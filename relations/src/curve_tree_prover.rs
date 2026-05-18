use bulletproofs::r1cs::*;

use crate::error::Error;
use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{CurveTree, CurveTreeNode, InnerNode, SelectAndRerandomizePath};

use crate::parameters::{SelRerandProofParameters, SingleLayerProofParameters};
use crate::select::multi_select_public_set_ext_challenge;
use ark_ec::{
    models::short_weierstrass::{Projective, SWCurveConfig},
    short_weierstrass::Affine,
    CurveGroup,
};
use ark_ff::PrimeField;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::string::ToString;
use ark_std::{
    fmt::{Debug, Formatter},
    vec,
    vec::Vec,
};
use bulletproofs::PedersenGens;
use core::ops::Mul;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use zeroize::{Zeroize, ZeroizeOnDrop};

impl<
        const L: usize,
        const M: usize,
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    > CurveTreeNode<L, M, P0, P1>
{
    /// Generate witness node for this node and add that witness to `current_level_witness_nodes` and
    /// then call this function for its immediate child as well. The witness is the `self`'s child on path
    /// from root to the leaf with index `leaf_index` and x-coordinates of all the children of `self`
    /// Recursively traverse from top to bottom
    pub fn generate_witness_node_for_this_and_children(
        &self,
        leaf_index: usize,
        tree_index: usize,
        current_level_witness_nodes: &mut Vec<WitnessNode<L, P0, P1>>,
        other_level_witness_nodes: &mut Vec<WitnessNode<L, P1, P0>>,
    ) -> Result<(), Error> {
        if let Self::InnerNode(inner_node) = &self {
            let child_node_index_to_rerandomize = self.child_index(leaf_index).unwrap();
            let child_node_to_rerandomize =
                inner_node.get_child(child_node_index_to_rerandomize)?;

            current_level_witness_nodes.push(WitnessNode {
                x_coord_children: inner_node.x_coord_children[tree_index],
                child_node_to_randomize: child_node_to_rerandomize.commitment(tree_index),
            });

            // recursively add the remaining path
            child_node_to_rerandomize.generate_witness_node_for_this_and_children(
                leaf_index,
                tree_index,
                other_level_witness_nodes,
                current_level_witness_nodes,
            )?;
        }
        Ok(())
    }
}

/// Implements prover operations on the Curve Tree
impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTree<L, M, P0, P1>
{
    /// Produce a witness of the path (root to leaf) to the commitment at `index` including siblings.
    /// The witness consists of "nodes" of the path where each "node" contains x-coordinates of the children (plus delta)
    /// and a non-hiding commitment to those x-coordinates as well.
    /// This does not randomize the commitments in the "node" but just fetches it.
    pub fn get_path_to_leaf_for_proof(
        &self,
        leaf_index: usize,
        tree_index: usize,
    ) -> Result<CurveTreeWitnessPath<L, P0, P1>, Error> {
        let mut even_internal_nodes: Vec<WitnessNode<L, P0, P1>> = Vec::new();
        let mut odd_internal_nodes: Vec<WitnessNode<L, P1, P0>> = Vec::new();

        match self {
            Self::Even(ct) => ct.generate_witness_node_for_this_and_children(
                leaf_index,
                tree_index,
                &mut even_internal_nodes,
                &mut odd_internal_nodes,
            )?,
            Self::Odd(ct) => ct.generate_witness_node_for_this_and_children(
                leaf_index,
                tree_index,
                &mut odd_internal_nodes,
                &mut even_internal_nodes,
            )?,
        }

        debug_assert_eq!(
            self.height(),
            even_internal_nodes.len() + odd_internal_nodes.len()
        );
        Ok(CurveTreeWitnessPath {
            even_internal_nodes,
            odd_internal_nodes,
        })
    }

    /// Produce witnesses for multiple paths that share the same root.
    /// This is optimized for batch operations, storing shared root children x-coordinates once.
    pub fn get_paths_to_leaves_for_proof(
        &self,
        leaf_indices: &[usize],
        tree_index: usize,
    ) -> Result<WitnessPathsWithSameRoot<L, P0, P1>, Error> {
        if leaf_indices.is_empty() {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }

        let num_leaves = leaf_indices.len();
        let mut even_internal_nodes = vec![vec![]; num_leaves];
        let mut odd_internal_nodes = vec![vec![]; num_leaves];

        match self {
            Self::Even(ct) => {
                if let CurveTreeNode::InnerNode(inner_node) = ct {
                    let child_nodes_to_randomize = Self::generate_paths(
                        leaf_indices,
                        tree_index,
                        &mut even_internal_nodes,
                        &mut odd_internal_nodes,
                        ct,
                        inner_node,
                    )?;
                    let root_children = RootChildren::Even {
                        x_coords: inner_node.x_coord_children[tree_index],
                        child_nodes_to_randomize,
                    };
                    Ok(WitnessPathsWithSameRoot {
                        root_children,
                        even_internal_nodes,
                        odd_internal_nodes,
                    })
                } else {
                    unreachable!()
                }
            }
            Self::Odd(ct) => {
                if let CurveTreeNode::InnerNode(inner_node) = ct {
                    let child_nodes_to_randomize = CurveTree::<L, M, P1, P0>::generate_paths(
                        leaf_indices,
                        tree_index,
                        &mut odd_internal_nodes,
                        &mut even_internal_nodes,
                        ct,
                        inner_node,
                    )?;
                    let root_children = RootChildren::Odd {
                        x_coords: inner_node.x_coord_children[tree_index],
                        child_nodes_to_randomize,
                    };
                    Ok(WitnessPathsWithSameRoot {
                        root_children,
                        even_internal_nodes,
                        odd_internal_nodes,
                    })
                } else {
                    unreachable!()
                }
            }
        }
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: CryptoRngCore>(
        &self,
        leaf_index: usize,
        tree_index: usize,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
        rng: &mut R,
    ) -> Result<(SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField), Error> {
        let witness = self.get_path_to_leaf_for_proof(leaf_index, tree_index)?;
        witness.select_and_rerandomize_prover_gadget(even_prover, odd_prover, parameters, rng)
    }

    fn generate_paths(
        leaf_indices: &[usize],
        tree_index: usize,
        even_internal_nodes: &mut Vec<Vec<WitnessNode<L, P0, P1>>>,
        odd_internal_nodes: &mut Vec<Vec<WitnessNode<L, P1, P0>>>,
        root_node: &CurveTreeNode<L, M, P0, P1>,
        inner_node: &InnerNode<L, M, P0, P1>,
    ) -> Result<Vec<Affine<P1>>, Error> {
        let num_leaves = leaf_indices.len();
        let mut child_nodes_to_randomize = Vec::with_capacity(num_leaves);
        let mut children = Vec::with_capacity(num_leaves);
        for leaf_index in leaf_indices {
            let child_node_index_to_rerandomize = root_node.child_index(*leaf_index).unwrap();
            let child_node_to_randomize = inner_node.get_child(child_node_index_to_rerandomize)?;
            child_nodes_to_randomize.push(child_node_to_randomize.commitment(tree_index));
            children.push((*leaf_index, child_node_to_randomize));
        }
        for (i, (leaf_index, child_node)) in children.into_iter().enumerate() {
            child_node.generate_witness_node_for_this_and_children(
                leaf_index,
                tree_index,
                &mut odd_internal_nodes[i],
                &mut even_internal_nodes[i],
            )?
        }
        Ok(child_nodes_to_randomize)
    }
}

/// A single node on the witness path.
/// Contains the information needed to prove the single level select and rerandomize relation.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct WitnessNode<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    /// x-coordinates of all children of this node, including `child_node_to_randomize`
    pub x_coord_children: [P0::ScalarField; L],
    /// The child node of this node that is on the path from root to the desired leaf.
    pub child_node_to_randomize: Affine<P1>,
}

impl<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> Debug
    for WitnessNode<L, P0, P1>
{
    // This is a dummy implementation to allow unwrapping the result of converting a vector into an array of the same size.
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "CurveTreeWitness")
    }
}

/// A witness of a Curve Tree path including siblings for all nodes on the path.
/// Contains all information needed to prove the select and rerandomize relation.
#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct CurveTreeWitnessPath<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
{
    /// list of witnesses of generated by taking children of even level internal nodes. The children are themselves odd level nodes.
    pub even_internal_nodes: Vec<WitnessNode<L, P0, P1>>,
    /// list of witnesses of generated by taking children of odd level internal nodes. The children are themselves even level nodes.
    pub odd_internal_nodes: Vec<WitnessNode<L, P1, P0>>,
}

/// Root children information including x-coordinates and selected child nodes for multiple paths
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub enum RootChildren<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    /// Root is an even-level node
    Even {
        /// x-coordinates of all children (odd level nodes) of the root (shared across all paths)
        x_coords: [P0::ScalarField; L],
        /// The child nodes selected by each path (one per path). These are odd level nodes
        child_nodes_to_randomize: Vec<Affine<P1>>,
    },
    /// Root is an odd-level node
    Odd {
        /// x-coordinates of all children (even level nodes) of the root (shared across all paths)
        x_coords: [P1::ScalarField; L],
        /// The child nodes selected by each path (one per path). These are even level nodes
        child_nodes_to_randomize: Vec<Affine<P0>>,
    },
}

/// Multiple witness paths that share the same root.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct WitnessPathsWithSameRoot<
    const L: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig + Copy,
> {
    /// Root's children (x-coords and selected children for all paths)
    pub root_children: RootChildren<L, P0, P1>,
    /// Witness nodes for each path, excluding root's children. The length of outer vector is the number of paths
    pub even_internal_nodes: Vec<Vec<WitnessNode<L, P0, P1>>>,
    /// Witness nodes for each path, excluding root's children. The length of outer vector is the number of paths
    pub odd_internal_nodes: Vec<Vec<WitnessNode<L, P1, P0>>>,
}

impl<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
    WitnessPathsWithSameRoot<L, P0, P1>
{
    /// Returns the number of paths in this witness
    pub fn num_paths(&self) -> usize {
        self.odd_internal_nodes.len()
    }

    /// Converts this batch witness structure into individual [`CurveTreeWitnessPath`] objects
    pub fn to_individual_paths(&self) -> Vec<CurveTreeWitnessPath<L, P0, P1>> {
        let num_paths = self.num_paths();
        let mut paths = Vec::with_capacity(num_paths);

        match &self.root_children {
            RootChildren::Even {
                x_coords,
                child_nodes_to_randomize,
            } => {
                for i in 0..num_paths {
                    let root_witness = WitnessNode {
                        x_coord_children: *x_coords,
                        child_node_to_randomize: child_nodes_to_randomize[i],
                    };

                    let mut even_internal_nodes = vec![root_witness];
                    even_internal_nodes.extend(self.even_internal_nodes[i].clone());

                    paths.push(CurveTreeWitnessPath {
                        even_internal_nodes,
                        odd_internal_nodes: self.odd_internal_nodes[i].clone(),
                    });
                }
            }
            RootChildren::Odd {
                x_coords,
                child_nodes_to_randomize,
            } => {
                for i in 0..num_paths {
                    let root_witness = WitnessNode {
                        x_coord_children: *x_coords,
                        child_node_to_randomize: child_nodes_to_randomize[i],
                    };

                    let mut odd_internal_nodes = vec![root_witness];
                    odd_internal_nodes.extend(self.odd_internal_nodes[i].clone());

                    paths.push(CurveTreeWitnessPath {
                        even_internal_nodes: self.even_internal_nodes[i].clone(),
                        odd_internal_nodes,
                    });
                }
            }
        }

        paths
    }
}

/// Variables allocated for the x-coordinates of the selected children of root
#[derive(Clone)]
pub enum RootChildrenCoordsVars<F0: PrimeField, F1: PrimeField> {
    Even(Vec<LinearCombination<F0>>),
    Odd(Vec<LinearCombination<F1>>),
}

/// Prove a single inclusion using a CurveTreeWitnessPath
impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessPath<L, P0, P1>
{
    pub fn root_is_even(&self) -> bool {
        // The leaf is even and included in the internal even nodes.
        // If the number of internal even and odd nodes is equal,
        // then the first odd node is the parent of the first even node and a child of the even root.
        let even = self.even_internal_nodes.len() == self.odd_internal_nodes.len();
        // Otherwise there must be an additional even node which has the odd root as parent.
        if !even {
            debug_assert_eq!(
                self.even_internal_nodes.len() + 1,
                self.odd_internal_nodes.len()
            )
        };
        even
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf
    /// and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: CryptoRngCore>(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
        rng: &mut R,
    ) -> Result<(SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField), Error> {
        let (
            even_rerandomized_nodes,
            odd_rerandomized_nodes,
            even_rerandomization_scalars,
            odd_rerandomization_scalars,
            re_randomization_of_leaf,
        ) = self.randomize_nodes(parameters.pc_gens(), rng);

        let root_is_even = self.root_is_even();

        // Select and rerandomize for root node. The set of children of root is public
        if root_is_even {
            self.even_internal_nodes[0].root_level_select_and_rerandomize_prover_gadget(
                even_prover,
                &parameters.odd_parameters,
                &odd_rerandomized_nodes[0],
                odd_rerandomization_scalars[0],
                &self.even_internal_nodes[0].x_coord_children,
            )?;
        } else {
            self.odd_internal_nodes[0].root_level_select_and_rerandomize_prover_gadget(
                odd_prover,
                &parameters.even_parameters,
                &even_rerandomized_nodes[0],
                even_rerandomization_scalars[0],
                &self.odd_internal_nodes[0].x_coord_children,
            )?;
        }

        // Select and rerandomize for non-root nodes
        self.select_and_rerandomize_prover_gadget_non_root_nodes(
            even_prover,
            odd_prover,
            root_is_even,
            &even_rerandomized_nodes,
            &odd_rerandomized_nodes,
            even_rerandomization_scalars,
            odd_rerandomization_scalars,
            parameters,
        )?;

        Ok((
            SelectAndRerandomizePath {
                even_commitments: even_rerandomized_nodes,
                odd_commitments: odd_rerandomized_nodes,
            },
            re_randomization_of_leaf, // This is the scalar applied to the selected leaf for rerandomization
        ))
    }

    // TODO: Use the optimized path
    pub fn select_and_rerandomize_prover_gadget_for_common_root<R: CryptoRngCore>(
        paths: &[Self],
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
        rng: &mut R,
    ) -> Result<
        (
            Vec<SelectAndRerandomizePath<L, P0, P1>>,
            Vec<P0::ScalarField>,
        ),
        Error,
    > {
        let is_root_even = paths[0].root_is_even();
        // Check all paths are consistent
        for path in &paths[1..] {
            let this_root_is_even = path.root_is_even();
            if is_root_even {
                if !this_root_is_even {
                    return Err(Error::RootTypeMismatch {
                        expected: "even".to_string(),
                        got: "odd".to_string(),
                    });
                }
            } else {
                if this_root_is_even {
                    return Err(Error::RootTypeMismatch {
                        expected: "odd".to_string(),
                        got: "even".to_string(),
                    });
                }
            }
        }

        let selected_children_x_coords = if is_root_even {
            // For each path get the child node of root
            let witness_nodes_of_root = paths
                .iter()
                .map(|p| &p.even_internal_nodes[0])
                .collect::<Vec<_>>();
            let delta = parameters.odd_parameters.sl_params.delta;
            let x_coords_selected_children =
                Self::process_root_nodes_for_given_paths_with_common_root(
                    witness_nodes_of_root,
                    even_prover,
                    delta,
                )?;
            RootChildrenCoordsVars::Even(x_coords_selected_children)
        } else {
            let witness_nodes_of_root = paths
                .iter()
                .map(|p| &p.odd_internal_nodes[0])
                .collect::<Vec<_>>();
            let delta = parameters.even_parameters.sl_params.delta;
            let x_coords_selected_children = CurveTreeWitnessPath::<L, P1, P0>::process_root_nodes_for_given_paths_with_common_root(
                witness_nodes_of_root,
                odd_prover,
                delta,
            )?;
            RootChildrenCoordsVars::Odd(x_coords_selected_children)
        };
        Self::process_non_root_nodes_for_given_paths_with_common_root(
            &paths,
            even_prover,
            odd_prover,
            selected_children_x_coords,
            parameters,
            rng,
        )
    }

    /// Used when proving for multiple paths with a common root. Called after process_root_nodes_for_given_paths_with_common_root.
    /// Returns the rerandomization scalars of leaves for each path.
    pub fn process_non_root_nodes_for_given_paths_with_common_root<R: CryptoRngCore>(
        paths: &[Self],
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        mut selected_root_children_x_coords: RootChildrenCoordsVars<F0, F1>,
        parameters: &SelRerandProofParameters<P0, P1>,
        rng: &mut R,
    ) -> Result<
        (
            Vec<SelectAndRerandomizePath<L, P0, P1>>,
            Vec<P0::ScalarField>,
        ),
        Error,
    > {
        if paths.is_empty() {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }
        let is_root_even = paths[0].root_is_even();

        let mut randomized_paths = Vec::with_capacity(paths.len());
        let mut re_randomization_of_leaves = Vec::with_capacity(paths.len());

        for path in paths {
            // Randomize nodes for this path
            let (
                even_rerandomized_nodes,
                odd_rerandomized_nodes,
                even_rerandomization_scalars,
                odd_rerandomization_scalars,
                re_randomization_of_leaf,
            ) = path.randomize_nodes(parameters.pc_gens(), rng);

            // Enforce re-randomization relation on child of root
            selected_root_children_x_coords.validate_and_re_randomize_child(
                even_prover,
                odd_prover,
                &even_rerandomized_nodes[0],
                &odd_rerandomized_nodes[0],
                Some(&path),
                Some(even_rerandomization_scalars[0]),
                Some(odd_rerandomization_scalars[0]),
                is_root_even,
                parameters,
            )?;

            // Process non-root nodes
            path.select_and_rerandomize_prover_gadget_non_root_nodes(
                even_prover,
                odd_prover,
                is_root_even,
                &even_rerandomized_nodes,
                &odd_rerandomized_nodes,
                even_rerandomization_scalars,
                odd_rerandomization_scalars,
                parameters,
            )?;

            randomized_paths.push(SelectAndRerandomizePath {
                odd_commitments: odd_rerandomized_nodes,
                even_commitments: even_rerandomized_nodes,
            });
            re_randomization_of_leaves.push(re_randomization_of_leaf);
        }

        Ok((randomized_paths, re_randomization_of_leaves))
    }

    /// Randomizes the nodes in the witness path and returns the randomized nodes and randomizers.
    /// Returns: (odd_rerandomized_nodes, even_rerandomized_nodes, even_rerandomization_scalars, odd_rerandomization_scalars, re_randomization_of_leaf)
    pub(crate) fn randomize_nodes<R: CryptoRngCore>(
        &self,
        (even_pc_gens, odd_pc_gens): (&PedersenGens<Affine<P0>>, &PedersenGens<Affine<P1>>),
        rng: &mut R,
    ) -> (
        Vec<Affine<P0>>,
        Vec<Affine<P1>>,
        Vec<P0::ScalarField>,
        Vec<P1::ScalarField>,
        P0::ScalarField,
    ) {
        // for each even internal node, there must be a rerandomization of a commitment in the odd curve
        let even_length = self.even_internal_nodes.len();
        let mut odd_rerandomization_scalars: Vec<P1::ScalarField> = Vec::with_capacity(even_length);
        let mut odd_rerandomized_nodes: Vec<Affine<P1>> = Vec::with_capacity(even_length);
        // and vice versa
        let odd_length = self.odd_internal_nodes.len();
        let mut even_rerandomization_scalars: Vec<P0::ScalarField> = Vec::with_capacity(odd_length);
        let mut even_rerandomized_nodes: Vec<Affine<P0>> = Vec::with_capacity(odd_length);

        // TODO: A small (since height is small) optimization is to compute the all blindings at once.

        // For each node on even levels in the witness path, randomize its child (odd level node) by adding `B_blinding * r_1`
        for even in &self.even_internal_nodes {
            let rerandomization = F1::rand(rng);
            let blinding = odd_pc_gens.B_blinding.mul(rerandomization).into_affine();
            odd_rerandomization_scalars.push(rerandomization);
            odd_rerandomized_nodes.push((even.child_node_to_randomize + blinding).into());
        }

        // For each node on odd levels in the witness path, randomize its child (even level node, including leaf)
        // by adding `B_blinding * r_1`
        let mut re_randomization_of_leaf = F0::default();
        for (i, odd) in self.odd_internal_nodes.iter().enumerate() {
            let rerandomization = F0::rand(rng);
            let blinding = even_pc_gens.B_blinding.mul(rerandomization).into_affine();
            let rerandomized = (odd.child_node_to_randomize + blinding).into();
            even_rerandomization_scalars.push(rerandomization);
            // Since leaf is always at even level, the parent of leaf is always at odd level. If
            // current node is the last (lowest) odd level node, then its `child_node_to_randomize` is the
            // leaf node whose proof if being created.
            even_rerandomized_nodes.push(rerandomized);
            if i == self.odd_internal_nodes.len() - 1 {
                // The lowest odd level node
                re_randomization_of_leaf = rerandomization;
            }
        }

        (
            even_rerandomized_nodes,
            odd_rerandomized_nodes,
            even_rerandomization_scalars,
            odd_rerandomization_scalars,
            re_randomization_of_leaf,
        )
    }

    /// Allocate x-coordinates of children of root and enforce set-membership constraint on the selected child of root.
    /// Returns x-coordinates of selected children of the root node.
    /// Used when proving for multiple paths with a common root
    fn process_root_nodes_for_given_paths_with_common_root(
        mut witness_nodes_of_root: Vec<&WitnessNode<L, P0, P1>>,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        delta: Affine<P1>,
    ) -> Result<Vec<LinearCombination<F0>>, Error> {
        let mut child_nodes_to_randomize = Vec::with_capacity(witness_nodes_of_root.len());

        let first_child = witness_nodes_of_root.remove(0);
        let all_x_coords_root_children = first_child.x_coord_children;

        // For children of root node, these might be same or different, add delta to them
        child_nodes_to_randomize.push(first_child.child_node_to_randomize + delta);

        for node in witness_nodes_of_root {
            if all_x_coords_root_children != node.x_coord_children {
                return Err(Error::MismatchedXCoordsChildren);
            }
            child_nodes_to_randomize.push(node.child_node_to_randomize + delta);
        }

        let child_nodes_to_randomize = Projective::normalize_batch(&child_nodes_to_randomize);
        allocate_children_of_root_and_enforce_membership(
            prover,
            child_nodes_to_randomize.len(),
            Some(child_nodes_to_randomize),
            &all_x_coords_root_children,
        )
    }

    /// Proves select and rerandomize for all non-root nodes in the witness path.
    fn select_and_rerandomize_prover_gadget_non_root_nodes(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        root_is_even: bool,
        even_rerandomized_nodes: &[Affine<P0>],
        odd_rerandomized_nodes: &[Affine<P1>],
        mut even_rerandomization_scalars: Vec<P0::ScalarField>,
        mut odd_rerandomization_scalars: Vec<P1::ScalarField>,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        let even_length = self.even_internal_nodes.len();
        let odd_length = self.odd_internal_nodes.len();

        let prove_even = |prover: &mut Prover<MerlinTranscript, Affine<P0>>| -> Result<(), Error> {
            for i in 0..even_length {
                // Because root is already processed in the function called before this
                let index = if root_is_even { i + 1 } else { i };
                if self.even_internal_nodes.len() == index {
                    continue;
                }
                self.even_internal_nodes[index].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.odd_parameters,
                    &even_rerandomized_nodes[i],
                    even_rerandomization_scalars[i],
                    &odd_rerandomized_nodes[index],
                    odd_rerandomization_scalars[index],
                )?;
            }
            Ok(())
        };

        let prove_odd = |prover: &mut Prover<MerlinTranscript, Affine<P1>>| -> Result<(), Error> {
            for i in 0..odd_length {
                // Because root is already processed in the function called before this
                let index = if !root_is_even { i + 1 } else { i };
                if self.odd_internal_nodes.len() == index {
                    continue;
                }
                self.odd_internal_nodes[index].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.even_parameters,
                    &odd_rerandomized_nodes[i],
                    odd_rerandomization_scalars[i],
                    &even_rerandomized_nodes[index],
                    even_rerandomization_scalars[index],
                )?;
            }
            Ok(())
        };

        #[cfg(not(feature = "parallel"))]
        let even_res = prove_even(even_prover);

        #[cfg(not(feature = "parallel"))]
        let odd_res = prove_odd(odd_prover);

        #[cfg(feature = "parallel")]
        let (even_res, odd_res) = rayon::join(|| prove_even(even_prover), || prove_odd(odd_prover));

        even_res?;
        odd_res?;

        Zeroize::zeroize(&mut odd_rerandomization_scalars);
        Zeroize::zeroize(&mut even_rerandomization_scalars);

        Ok(())
    }
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > WitnessNode<L, P0, P1>
{
    /// Allocates variables for the children and proves select and rerandomize for one.
    /// If the parent is the root, the variables are allocated directly, otherwise by allocating commitment to the parent.
    pub fn single_level_select_and_rerandomize_prover_gadget(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        child_level_parameters: &SingleLayerProofParameters<P1>,
        self_node_rerandomized: &Affine<P0>,
        self_rerandomization_scalar: P0::ScalarField,
        rerandomized_child: &Affine<P1>,
        child_rerandomization_scalar: P1::ScalarField,
    ) -> Result<(), Error> {
        // In this case this (`self`) is a non-root inner node and the children (and the scalar used for rerandomizing) are part of the witness.
        // Allocate variables for x-coordinates (which are committed in `self_node_rerandomized`) of child nodes with `self_rerandomization_scalar` as the blinding
        let children = prover
            .vars_for_committed_vec(
                self_node_rerandomized,
                &self.x_coord_children,
                self_rerandomization_scalar,
            )
            .iter()
            .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
            .collect();
        self.single_level_select_and_rerandomize_prover_gadget_helper(
            prover,
            child_level_parameters,
            rerandomized_child,
            child_rerandomization_scalar,
            children,
        )
    }

    /// Proves the select and rerandomize for one of the children represented by the variables.
    pub fn single_level_select_and_rerandomize_prover_gadget_helper(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        parameters: &SingleLayerProofParameters<P1>,
        rerandomized_child: &Affine<P1>,
        child_rerandomization_scalar: P1::ScalarField,
        all_children_vars: Vec<LinearCombination<<P0>::ScalarField>>,
    ) -> Result<(), Error> {
        let child_commitment = self.child_node_to_randomize;

        single_level_select_and_rerandomize(
            prover,
            parameters,
            rerandomized_child,
            all_children_vars,
            Some((child_commitment + parameters.sl_params.delta).into_affine()),
            Some(child_rerandomization_scalar),
        )?;

        Ok(())
    }

    /// Proves the select and rerandomize for children of the root node.
    pub fn root_level_select_and_rerandomize_prover_gadget(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        parameters: &SingleLayerProofParameters<P1>,
        rerandomized_child: &Affine<P1>,
        child_rerandomization_scalar: P1::ScalarField,
        children_of_root: &[P0::ScalarField],
    ) -> Result<(), Error> {
        let child_commitment = self.child_node_to_randomize;
        root_level_select_and_rerandomize(
            prover,
            parameters,
            rerandomized_child,
            children_of_root,
            Some((child_commitment + parameters.sl_params.delta).into_affine()),
            Some(child_rerandomization_scalar),
        )?;

        Ok(())
    }
}

pub(crate) fn allocate_children_of_root_and_enforce_membership<
    P: SWCurveConfig,
    Cs: ConstraintSystem<P::BaseField>,
>(
    cs: &mut Cs,
    num_selected_children: usize,
    child_nodes_to_randomize: Option<Vec<Affine<P>>>,
    all_x_coords_root_children: &[P::BaseField],
) -> Result<Vec<LinearCombination<P::BaseField>>, Error> {
    let x_coords_selected_children = match child_nodes_to_randomize {
        Some(child_nodes_to_randomize) => child_nodes_to_randomize
            .into_iter()
            .map(|c| cs.allocate(Some(c.x)).unwrap().into())
            .collect::<Vec<_>>(),
        _ => (0..num_selected_children)
            .map(|_| cs.allocate(None).unwrap().into())
            .collect::<Vec<_>>(),
    };
    let c = cs
        .transcript()
        .challenge_scalar(b"challenge-for-multi_select");
    multi_select_public_set_ext_challenge(
        cs,
        x_coords_selected_children.clone(),
        &all_x_coords_root_children,
        c,
    )?;
    Ok(x_coords_selected_children)
}

impl<F0: PrimeField, F1: PrimeField> RootChildrenCoordsVars<F0, F1> {
    pub fn validate_and_re_randomize_child<
        const L: usize,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
        Cs0: ConstraintSystem<F0>,
        Cs1: ConstraintSystem<F1>,
    >(
        &mut self,
        cs_even: &mut Cs0,
        cs_odd: &mut Cs1,
        even_rerandomized_child: &Affine<P0>,
        odd_rerandomized_child: &Affine<P1>,
        path: Option<&CurveTreeWitnessPath<L, P0, P1>>,
        even_child_rerandomization_scalar: Option<P0::ScalarField>,
        odd_child_rerandomization_scalar: Option<P1::ScalarField>,
        is_root_even: bool,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        match self {
            Self::Even(coords) => {
                if !is_root_even {
                    return Err(Error::RootTypeMismatch {
                        expected: "even".to_string(),
                        got: "odd".to_string(),
                    });
                }
                let rerandomized_child = odd_rerandomized_child;
                cs_even
                    .transcript()
                    .append(b"rerandomized_child", rerandomized_child);
                let x_var = coords.remove(0);
                let child_plus_delta = path.map(|p| {
                    (p.even_internal_nodes[0].child_node_to_randomize
                        + parameters.odd_parameters.sl_params.delta)
                        .into_affine()
                });
                validate_point_and_re_randomize(
                    cs_even,
                    &parameters.odd_parameters,
                    rerandomized_child,
                    x_var,
                    child_plus_delta,
                    odd_child_rerandomization_scalar,
                )?;
            }
            Self::Odd(coords) => {
                if is_root_even {
                    return Err(Error::RootTypeMismatch {
                        expected: "odd".to_string(),
                        got: "even".to_string(),
                    });
                }
                let rerandomized_child = even_rerandomized_child;
                cs_odd
                    .transcript()
                    .append(b"rerandomized_child", rerandomized_child);
                let x_var = coords.remove(0);
                let child_plus_delta = path.map(|p| {
                    (p.odd_internal_nodes[0].child_node_to_randomize
                        + parameters.even_parameters.sl_params.delta)
                        .into_affine()
                });
                validate_point_and_re_randomize(
                    cs_odd,
                    &parameters.even_parameters,
                    rerandomized_child,
                    x_var,
                    child_plus_delta,
                    even_child_rerandomization_scalar,
                )?;
            }
        }
        Ok(())
    }
}

impl<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> CanonicalSerialize
    for RootChildren<L, P0, P1>
{
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        match self {
            RootChildren::Even {
                x_coords,
                child_nodes_to_randomize,
            } => {
                0u8.serialize_with_mode(&mut writer, compress)?;
                x_coords.serialize_with_mode(&mut writer, compress)?;
                child_nodes_to_randomize.serialize_with_mode(&mut writer, compress)?;
            }
            RootChildren::Odd {
                x_coords,
                child_nodes_to_randomize,
            } => {
                1u8.serialize_with_mode(&mut writer, compress)?;
                x_coords.serialize_with_mode(&mut writer, compress)?;
                child_nodes_to_randomize.serialize_with_mode(&mut writer, compress)?;
            }
        }
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        1 + match self {
            RootChildren::Even {
                x_coords,
                child_nodes_to_randomize,
            } => {
                x_coords.serialized_size(compress)
                    + child_nodes_to_randomize.serialized_size(compress)
            }
            RootChildren::Odd {
                x_coords,
                child_nodes_to_randomize,
            } => {
                x_coords.serialized_size(compress)
                    + child_nodes_to_randomize.serialized_size(compress)
            }
        }
    }
}

impl<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> CanonicalDeserialize
    for RootChildren<L, P0, P1>
{
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let variant = u8::deserialize_with_mode(&mut reader, compress, validate)?;
        match variant {
            0 => {
                let x_coords =
                    <[P0::ScalarField; L]>::deserialize_with_mode(&mut reader, compress, validate)?;
                let child_nodes_to_randomize =
                    Vec::<Affine<P1>>::deserialize_with_mode(&mut reader, compress, validate)?;
                Ok(RootChildren::Even {
                    x_coords,
                    child_nodes_to_randomize,
                })
            }
            1 => {
                let x_coords =
                    <[P1::ScalarField; L]>::deserialize_with_mode(&mut reader, compress, validate)?;
                let child_nodes_to_randomize =
                    Vec::<Affine<P0>>::deserialize_with_mode(&mut reader, compress, validate)?;
                Ok(RootChildren::Odd {
                    x_coords,
                    child_nodes_to_randomize,
                })
            }
            _ => Err(SerializationError::InvalidData),
        }
    }
}

impl<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> Valid
    for RootChildren<L, P0, P1>
{
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}
