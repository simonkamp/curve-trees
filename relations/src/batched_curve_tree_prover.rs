use bulletproofs::r1cs::*;

use crate::curve_tree_prover::{CurveTreeWitnessPath, WitnessNode};
use crate::error::Error;
use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{CurveTree, CurveTreeNode, SelectAndRerandomizeMultiPath};
use crate::parameters::{SelRerandProofParameters, SingleLayerProofParameters};
use crate::select::multi_select_public_set_ext_challenge;
use ark_ec::{
    models::short_weierstrass::{Projective, SWCurveConfig},
    short_weierstrass::Affine,
    CurveGroup,
};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{string::ToString, vec, vec::Vec, Zero};
use bulletproofs::PedersenGens;
use core::ops::Mul;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use zeroize::{Zeroize, ZeroizeOnDrop};

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf
    /// and the rerandomization scalar of the selected leaf.
    pub fn batched_select_and_rerandomize_prover_gadget<R: CryptoRngCore>(
        &self,
        indices: &[u32],
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
        rng: &mut R,
    ) -> Result<
        (
            SelectAndRerandomizeMultiPath<L, M, P0, P1>,
            Vec<P0::ScalarField>,
        ),
        Error,
    > {
        let witness = self.get_paths_to_leaves(indices)?;

        witness.batched_select_and_rerandomize_prover_gadget(
            even_prover,
            odd_prover,
            parameters,
            rng,
        )
    }

    /// Produce a witness of the paths to the commitments indexed by `indices` including siblings.
    pub fn get_paths_to_leaves(
        &self,
        indices: &[u32],
    ) -> Result<CurveTreeWitnessMultiPath<L, M, P0, P1>, Error> {
        let num_indices = indices.len();
        if num_indices > M {
            return Err(Error::MoreIndicesThanSupportedBatchSize(
                num_indices as u32,
                M as u32,
            ));
        }

        // Get paths for each leaf index
        let mut independent_paths: Vec<CurveTreeWitnessPath<L, P0, P1>> =
            Vec::with_capacity(num_indices);
        for (tree_index, leaf_index) in indices.iter().enumerate() {
            independent_paths
                .push(self.get_path_to_leaf_for_proof(*leaf_index as usize, tree_index)?);
        }

        // Assumes that all paths have same number of even level nodes
        let num_even_internal_nodes = independent_paths[0].even_internal_nodes.len();
        // Assumes that all paths have same number of odd level nodes
        let num_odd_internal_nodes = independent_paths[0].odd_internal_nodes.len();

        let mut even_internal_nodes: Vec<Vec<WitnessNode<L, P0, P1>>> =
            Vec::with_capacity(num_even_internal_nodes);
        let mut odd_internal_nodes: Vec<Vec<WitnessNode<L, P1, P0>>> =
            Vec::with_capacity(num_odd_internal_nodes);

        for (i, mut path) in independent_paths.into_iter().enumerate() {
            if i == 0 {
                for _ in 0..num_even_internal_nodes {
                    even_internal_nodes.push(Vec::with_capacity(num_indices));
                }
                for _ in 0..num_odd_internal_nodes {
                    odd_internal_nodes.push(Vec::with_capacity(num_indices));
                }
            }
            // draining because can't move out due to Drop trait (ZeroizeOnDrop)
            for (j, node) in path.even_internal_nodes.drain(0..).enumerate() {
                even_internal_nodes[j].push(node)
            }
            for (j, node) in path.odd_internal_nodes.drain(0..).enumerate() {
                odd_internal_nodes[j].push(node)
            }
        }

        assert_eq!(
            self.height(),
            even_internal_nodes.len() + odd_internal_nodes.len()
        );
        Ok(CurveTreeWitnessMultiPath {
            even_internal_nodes,
            odd_internal_nodes,
        })
    }

    /// Produce optimized witnesses for multiple multi-paths sharing the same root.
    /// Takes a flat slice of leaf indices and chunks them into groups of M.
    pub fn get_optmz_paths_to_leaves(
        &self,
        indices: &[u32],
    ) -> Result<WitnessMultiPathForSameRoot<L, M, P0, P1>, Error> {
        if indices.is_empty() {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }

        let num_indices_per_path = M.min(indices.len());

        match self {
            Self::Even(ct) => {
                if let CurveTreeNode::InnerNode(inner_node) = ct {
                    let mut x_coords = Vec::with_capacity(num_indices_per_path);
                    for root_index in 0..num_indices_per_path {
                        x_coords.push(inner_node.x_coord_children[root_index]);
                    }

                    let mut child_nodes_to_randomize = Vec::with_capacity(indices.len());
                    let mut root_children_nodes = vec![];
                    for (i, leaf_index) in indices.into_iter().enumerate() {
                        let root_index = i % M;
                        let child_node_index = ct.child_index(*leaf_index as usize).unwrap();
                        let child_node = inner_node.get_child(child_node_index)?;
                        child_nodes_to_randomize.push(child_node.commitment(root_index));
                        root_children_nodes.push(child_node);
                    }

                    let root_children = RootChildrenForMultiPath::Even {
                        x_coords,
                        child_nodes_to_randomize,
                    };

                    let mut all_other_level_internal_nodes = vec![];
                    let mut all_current_level_internal_nodes = vec![];

                    for (chunk_indices, root_children_nodes) in
                        indices.chunks(M).zip(root_children_nodes.chunks(M))
                    {
                        let mut multi_path_current_level_nodes = Vec::new();
                        let mut multi_path_other_level_nodes = Vec::new();

                        for (root_index, (leaf_index, child_node)) in chunk_indices
                            .into_iter()
                            .zip(root_children_nodes.into_iter())
                            .enumerate()
                        {
                            let mut current_level_witness_nodes = Vec::new();
                            let mut other_level_witness_nodes = Vec::new();

                            child_node.generate_witness_node_for_this_and_children(
                                *leaf_index as usize,
                                root_index,
                                &mut current_level_witness_nodes,
                                &mut other_level_witness_nodes,
                            )?;

                            if root_index == 0 {
                                for _ in 0..other_level_witness_nodes.len() {
                                    multi_path_other_level_nodes
                                        .push(Vec::with_capacity(chunk_indices.len()));
                                }
                                for _ in 0..current_level_witness_nodes.len() {
                                    multi_path_current_level_nodes
                                        .push(Vec::with_capacity(chunk_indices.len()));
                                }
                            }

                            for (level, node) in other_level_witness_nodes.into_iter().enumerate() {
                                multi_path_other_level_nodes[level].push(node);
                            }
                            for (level, node) in current_level_witness_nodes.into_iter().enumerate()
                            {
                                multi_path_current_level_nodes[level].push(node);
                            }
                        }

                        all_other_level_internal_nodes.push(multi_path_other_level_nodes);
                        all_current_level_internal_nodes.push(multi_path_current_level_nodes);
                    }

                    Ok(WitnessMultiPathForSameRoot {
                        root_children,
                        even_internal_nodes: all_other_level_internal_nodes,
                        odd_internal_nodes: all_current_level_internal_nodes,
                    })
                } else {
                    unreachable!()
                }
            }
            Self::Odd(ct) => {
                if let CurveTreeNode::InnerNode(inner_node) = ct {
                    let mut x_coords = Vec::with_capacity(num_indices_per_path);
                    for root_index in 0..num_indices_per_path {
                        x_coords.push(inner_node.x_coord_children[root_index]);
                    }

                    let mut child_nodes_to_randomize = Vec::with_capacity(indices.len());
                    let mut root_children_nodes = vec![];
                    for (i, leaf_index) in indices.into_iter().enumerate() {
                        let root_index = i % M;
                        let child_node_index = ct.child_index(*leaf_index as usize).unwrap();
                        let child_node = inner_node.get_child(child_node_index)?;
                        child_nodes_to_randomize.push(child_node.commitment(root_index));
                        root_children_nodes.push(child_node);
                    }

                    let root_children = RootChildrenForMultiPath::Odd {
                        x_coords,
                        child_nodes_to_randomize,
                    };

                    let mut all_even_internal_nodes = vec![];
                    let mut all_odd_internal_nodes = vec![];

                    for (chunk_indices, root_children_nodes) in
                        indices.chunks(M).zip(root_children_nodes.chunks(M))
                    {
                        let mut multi_path_current_level_nodes = Vec::new();
                        let mut multi_path_other_level_nodes = Vec::new();

                        for (root_index, (leaf_index, child_node)) in chunk_indices
                            .into_iter()
                            .zip(root_children_nodes.into_iter())
                            .enumerate()
                        {
                            let mut current_level_witness_nodes = Vec::new();
                            let mut other_level_witness_nodes = Vec::new();

                            child_node.generate_witness_node_for_this_and_children(
                                *leaf_index as usize,
                                root_index,
                                &mut current_level_witness_nodes,
                                &mut other_level_witness_nodes,
                            )?;

                            if root_index == 0 {
                                for _ in 0..other_level_witness_nodes.len() {
                                    multi_path_other_level_nodes
                                        .push(Vec::with_capacity(chunk_indices.len()));
                                }
                                for _ in 0..current_level_witness_nodes.len() {
                                    multi_path_current_level_nodes
                                        .push(Vec::with_capacity(chunk_indices.len()));
                                }
                            }

                            for (level, node) in other_level_witness_nodes.into_iter().enumerate() {
                                multi_path_other_level_nodes[level].push(node);
                            }
                            for (level, node) in current_level_witness_nodes.into_iter().enumerate()
                            {
                                multi_path_current_level_nodes[level].push(node);
                            }
                        }

                        all_even_internal_nodes.push(multi_path_other_level_nodes);
                        all_odd_internal_nodes.push(multi_path_current_level_nodes);
                    }

                    Ok(WitnessMultiPathForSameRoot {
                        root_children,
                        even_internal_nodes: all_odd_internal_nodes,
                        odd_internal_nodes: all_even_internal_nodes,
                    })
                } else {
                    unreachable!()
                }
            }
        }
    }
}

#[derive(Clone)]
pub enum RootChildrenCoordsVars<F0: PrimeField, F1: PrimeField> {
    Even(Vec<Vec<LinearCombination<F0>>>),
    Odd(Vec<Vec<LinearCombination<F1>>>),
}

#[derive(Clone)]
pub enum RootChildrenSelected<
    F0: PrimeField,
    F1: PrimeField,
    P0: SWCurveConfig<BaseField = F1, ScalarField = F0>,
    P1: SWCurveConfig<BaseField = F0, ScalarField = F1>,
> {
    Even(Vec<Vec<Affine<P1>>>),
    Odd(Vec<Vec<Affine<P0>>>),
}

/// Root children data for batched multi-path witness with M trees
#[derive(Clone)]
pub enum RootChildrenForMultiPath<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig + Copy,
> {
    Even {
        /// x-coordinates of all L children for each tree (up to M trees)
        x_coords: Vec<[P0::ScalarField; L]>,
        /// Selected child nodes to randomize for each leaf index
        child_nodes_to_randomize: Vec<Affine<P1>>,
    },
    Odd {
        /// x-coordinates of all L children for each tree (up to M trees)
        x_coords: Vec<[P1::ScalarField; L]>,
        /// Selected child nodes to randomize for each leaf index
        child_nodes_to_randomize: Vec<Affine<P0>>,
    },
}

/// Optimized batch witness structure for multiple [`CurveTreeWitnessMultiPath`] objects sharing the same root.
/// Stores each root's children x-coordinates once instead of duplicating them for each path (on same root).
#[derive(Clone)]
pub struct WitnessMultiPathForSameRoot<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig + Copy,
> {
    /// Root children data (x-coords and selected children)
    pub root_children: RootChildrenForMultiPath<L, M, P0, P1>,
    /// Internal even level nodes for each multi-path (excluding root)
    pub even_internal_nodes: Vec<Vec<Vec<WitnessNode<L, P0, P1>>>>,
    /// Internal odd level nodes for each multi-path (excluding root)
    pub odd_internal_nodes: Vec<Vec<Vec<WitnessNode<L, P1, P0>>>>,
}

impl<const L: usize, const M: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
    WitnessMultiPathForSameRoot<L, M, P0, P1>
{
    /// Returns the number of multi-paths in this batch
    pub fn num_multi_paths(&self) -> usize {
        self.odd_internal_nodes.len()
    }

    /// Converts this batch structure into individual `CurveTreeWitnessMultiPath` objects
    pub fn to_individual_multi_paths(&self) -> Vec<CurveTreeWitnessMultiPath<L, M, P0, P1>> {
        let num_multi_paths = self.num_multi_paths();
        let mut multi_paths = Vec::with_capacity(num_multi_paths);

        match &self.root_children {
            RootChildrenForMultiPath::Even {
                x_coords,
                child_nodes_to_randomize,
            } => {
                for (path_idx, chunk) in child_nodes_to_randomize.chunks(M).enumerate() {
                    let mut even_internal_nodes = Vec::new();
                    let mut root_level_nodes = Vec::with_capacity(chunk.len());

                    for (root_idx, &child_node) in chunk.iter().enumerate() {
                        let root_witness = WitnessNode {
                            x_coord_children: x_coords[root_idx],
                            child_node_to_randomize: child_node,
                        };
                        root_level_nodes.push(root_witness);
                    }
                    even_internal_nodes.push(root_level_nodes);

                    for level in &self.even_internal_nodes[path_idx] {
                        even_internal_nodes.push(level.clone());
                    }

                    multi_paths.push(CurveTreeWitnessMultiPath {
                        even_internal_nodes,
                        odd_internal_nodes: self.odd_internal_nodes[path_idx].clone(),
                    });
                }
            }
            RootChildrenForMultiPath::Odd {
                x_coords,
                child_nodes_to_randomize,
            } => {
                for (path_idx, chunk) in child_nodes_to_randomize.chunks(M).enumerate() {
                    let mut odd_internal_nodes = Vec::new();
                    let mut root_level_nodes = Vec::with_capacity(chunk.len());

                    for (root_idx, &child_node) in chunk.iter().enumerate() {
                        let root_witness = WitnessNode {
                            x_coord_children: x_coords[root_idx],
                            child_node_to_randomize: child_node,
                        };
                        root_level_nodes.push(root_witness);
                    }
                    odd_internal_nodes.push(root_level_nodes);

                    for level in &self.odd_internal_nodes[path_idx] {
                        odd_internal_nodes.push(level.clone());
                    }

                    multi_paths.push(CurveTreeWitnessMultiPath {
                        even_internal_nodes: self.even_internal_nodes[path_idx].clone(),
                        odd_internal_nodes,
                    });
                }
            }
        }

        multi_paths
    }
}

/// A witness of at most M paths in M independently generated Curve Trees including siblings for all nodes on the paths.
/// Contains all information needed to prove M batched select and rerandomize relations.
#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct CurveTreeWitnessMultiPath<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig + Copy,
> {
    /// list of witness nodes corresponding to internal even level nodes. The inner vector contains witness
    /// nodes for each path at the same level
    pub even_internal_nodes: Vec<Vec<WitnessNode<L, P0, P1>>>,
    /// list of witness nodes corresponding to internal odd level nodes. The inner vector contains witness
    /// nodes for each path at the same level
    pub odd_internal_nodes: Vec<Vec<WitnessNode<L, P1, P0>>>,
}

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessMultiPath<L, M, P0, P1>
{
    pub fn root_is_even(&self) -> bool {
        if self.even_internal_nodes.len() == self.odd_internal_nodes.len() {
            return true;
        }
        if self.even_internal_nodes.len() + 1 == self.odd_internal_nodes.len() {
            return false;
        }
        panic!("Invalid witness path");
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf
    /// and the rerandomization scalar of the selected leaf.
    pub fn batched_select_and_rerandomize_prover_gadget<R: CryptoRngCore>(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
        rng: &mut R,
    ) -> Result<
        (
            SelectAndRerandomizeMultiPath<L, M, P0, P1>,
            Vec<P0::ScalarField>,
        ),
        Error,
    > {
        let num_indices = self.num_indices();
        if num_indices > M as u32 {
            return Err(Error::MoreIndicesThanSupportedBatchSize(
                self.num_indices(),
                M as u32,
            ));
        }

        let (
            even_rerandomized_sum_of_nodes,
            odd_rerandomized_sum_of_nodes,
            even_rerandomization_scalars,
            odd_rerandomization_scalars,
            rerandomizations_of_selected,
            rerandomization_scalars_of_selected,
        ) = self.randomize_nodes(parameters.pc_gens(), rng);

        let root_is_even = self.root_is_even();

        // Select and rerandomize for root node. The set of children of root is public
        if root_is_even {
            let mut children = Vec::with_capacity(L * num_indices as usize);
            for i in 0..num_indices as usize {
                children
                    .extend_from_slice(self.even_internal_nodes[0][i].x_coord_children.as_slice());
            }
            let mut selected_children_plus_delta = vec![Projective::zero(); num_indices as usize];
            for i in 0..num_indices as usize {
                // TODO: \sum{self.even_internal_nodes[0][i].child_node_to_randomize} is already created in `randomize_nodes`.
                selected_children_plus_delta[i] = self.even_internal_nodes[0][i]
                    .child_node_to_randomize
                    + parameters.odd_parameters.sl_params.delta;
            }
            let selected_children_plus_delta =
                Projective::normalize_batch(&selected_children_plus_delta);
            root_level_batched_select_and_rerandomize(
                even_prover,
                &parameters.odd_parameters,
                num_indices,
                &odd_rerandomized_sum_of_nodes[0],
                children,
                Some(&selected_children_plus_delta),
                Some(odd_rerandomization_scalars[0]),
            )?;
        } else {
            // Collect x-coordinates of all children of the root node
            let mut children = Vec::with_capacity(L * num_indices as usize);
            for i in 0..num_indices as usize {
                children
                    .extend_from_slice(self.odd_internal_nodes[0][i].x_coord_children.as_slice());
            }
            // Add delta to selected (to be randomized) children of the root node
            let mut selected_children_plus_delta = vec![Projective::zero(); num_indices as usize];
            for i in 0..num_indices as usize {
                selected_children_plus_delta[i] = self.odd_internal_nodes[0][i]
                    .child_node_to_randomize
                    + parameters.even_parameters.sl_params.delta;
            }
            let selected_children_plus_delta =
                Projective::normalize_batch(&selected_children_plus_delta);
            root_level_batched_select_and_rerandomize(
                odd_prover,
                &parameters.even_parameters,
                num_indices,
                &even_rerandomized_sum_of_nodes[0],
                children,
                Some(&selected_children_plus_delta),
                Some(even_rerandomization_scalars[0]),
            )?;
        }

        self.batched_select_and_rerandomize_prover_gadget_non_root_nodes(
            even_prover,
            odd_prover,
            root_is_even,
            &even_rerandomized_sum_of_nodes,
            &odd_rerandomized_sum_of_nodes,
            &even_rerandomization_scalars,
            &odd_rerandomization_scalars,
            &rerandomizations_of_selected,
            &rerandomization_scalars_of_selected,
            parameters,
        )?;

        Ok((
            SelectAndRerandomizeMultiPath {
                even_commitments: even_rerandomized_sum_of_nodes,
                odd_commitments: odd_rerandomized_sum_of_nodes,
                selected_commitments: rerandomizations_of_selected,
            },
            rerandomization_scalars_of_selected,
        ))
    }

    /// Commits to the root and rerandomizations of multiple paths with a common root
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments for all paths and the rerandomization scalars of the selected leaves.
    pub fn batched_select_and_rerandomize_prover_gadget_for_common_root<R: CryptoRngCore>(
        paths: &[Self],
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
        rng: &mut R,
    ) -> Result<
        (
            Vec<SelectAndRerandomizeMultiPath<L, M, P0, P1>>,
            Vec<Vec<P0::ScalarField>>,
        ),
        Error,
    > {
        if paths.is_empty() {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }

        let root_children = Self::process_root_nodes_for_given_multi_paths_with_common_root(
            paths,
            even_prover,
            odd_prover,
            parameters,
        )?;

        Self::process_non_root_nodes_for_given_multi_paths_with_common_root(
            paths,
            even_prover,
            odd_prover,
            root_children,
            parameters,
            rng,
        )
    }

    pub fn process_non_root_nodes_for_given_multi_paths_with_common_root<R: CryptoRngCore>(
        paths: &[Self],
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        root_children: (
            RootChildrenSelected<F0, F1, P0, P1>,
            RootChildrenCoordsVars<F0, F1>,
        ),
        parameters: &SelRerandProofParameters<P0, P1>,
        rng: &mut R,
    ) -> Result<
        (
            Vec<SelectAndRerandomizeMultiPath<L, M, P0, P1>>,
            Vec<Vec<P0::ScalarField>>,
        ),
        Error,
    > {
        if paths.is_empty() {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }

        let is_root_even = paths[0].root_is_even();

        let mut randomized_multi_paths = Vec::with_capacity(paths.len());
        let mut all_rerandomization_scalars = Vec::with_capacity(paths.len());

        let (mut root_children_selected, mut root_children_selected_coord_vars) = root_children;

        for path in paths {
            let num_indices = path.num_indices();
            if num_indices > M as u32 {
                return Err(Error::MoreIndicesThanSupportedBatchSize(
                    num_indices,
                    M as u32,
                ));
            }

            let (
                even_rerandomized_sum_of_nodes,
                odd_rerandomized_sum_of_nodes,
                even_rerandomization_scalars,
                odd_rerandomization_scalars,
                rerandomizations_of_selected,
                rerandomization_scalars_of_selected,
            ) = path.randomize_nodes(parameters.pc_gens(), rng);

            // Process root node for this multi-path
            root_children_selected_coord_vars.validate_and_re_randomize_children(
                Some(&mut root_children_selected),
                even_prover,
                odd_prover,
                &even_rerandomized_sum_of_nodes[0],
                &odd_rerandomized_sum_of_nodes[0],
                Some(even_rerandomization_scalars[0]),
                Some(odd_rerandomization_scalars[0]),
                num_indices,
                is_root_even,
                parameters,
            )?;

            // Process non-root nodes for this multi-path
            path.batched_select_and_rerandomize_prover_gadget_non_root_nodes(
                even_prover,
                odd_prover,
                is_root_even,
                &even_rerandomized_sum_of_nodes,
                &odd_rerandomized_sum_of_nodes,
                &even_rerandomization_scalars,
                &odd_rerandomization_scalars,
                &rerandomizations_of_selected,
                &rerandomization_scalars_of_selected,
                parameters,
            )?;

            randomized_multi_paths.push(SelectAndRerandomizeMultiPath {
                even_commitments: even_rerandomized_sum_of_nodes,
                odd_commitments: odd_rerandomized_sum_of_nodes,
                selected_commitments: rerandomizations_of_selected,
            });
            all_rerandomization_scalars.push(rerandomization_scalars_of_selected);
        }

        Ok((randomized_multi_paths, all_rerandomization_scalars))
    }

    pub fn batched_select_and_rerandomize_prover_gadget_non_root_nodes(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        root_is_even: bool,
        even_rerandomized_sum_of_nodes: &[Affine<P0>],
        odd_rerandomized_sum_of_nodes: &[Affine<P1>],
        even_rerandomization_scalars: &[P0::ScalarField],
        odd_rerandomization_scalars: &[P1::ScalarField],
        rerandomizations_of_selected: &[Affine<P0>],
        rerandomization_scalars_of_selected: &[P0::ScalarField],
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        let even_length = self.even_internal_nodes.len();
        let odd_length = self.odd_internal_nodes.len();

        let prove_even = |prover: &mut Prover<MerlinTranscript, Affine<P0>>| -> Result<(), Error> {
            for i in 0..even_length {
                // Since root's children are already processed
                let index = if root_is_even { i + 1 } else { i };
                if self.even_internal_nodes.len() == index {
                    continue;
                }
                WitnessNode::single_level_batched_select_and_rerandomize_prover_gadget(
                    &self.even_internal_nodes[index],
                    prover,
                    &parameters.odd_parameters,
                    &even_rerandomized_sum_of_nodes[i],
                    even_rerandomization_scalars[i],
                    &odd_rerandomized_sum_of_nodes[index],
                    odd_rerandomization_scalars[index],
                )?;
            }
            Ok(())
        };

        let prove_odd = |prover: &mut Prover<MerlinTranscript, Affine<P1>>| -> Result<(), Error> {
            for i in 0..odd_length {
                // Since root's children are already processed
                let index = if !root_is_even { i + 1 } else { i };
                if self.odd_internal_nodes.len() == index {
                    continue;
                }
                if index < (odd_length - 1) {
                    WitnessNode::single_level_batched_select_and_rerandomize_prover_gadget(
                        &self.odd_internal_nodes[index],
                        prover,
                        &parameters.even_parameters,
                        &odd_rerandomized_sum_of_nodes[i],
                        odd_rerandomization_scalars[i],
                        &even_rerandomized_sum_of_nodes[index],
                        even_rerandomization_scalars[index],
                    )?
                } else {
                    let num_indices = self.num_indices();
                    debug_assert_eq!(
                        rerandomizations_of_selected.len(),
                        rerandomization_scalars_of_selected.len()
                    );
                    debug_assert_eq!(rerandomizations_of_selected.len(), num_indices as usize);
                    // Commit to the last internal node to obtain variables for its children.
                    let children_vars = WitnessNode::allocate_multi_node_variables(
                        &self.odd_internal_nodes[index],
                        prover,
                        &odd_rerandomized_sum_of_nodes[i],
                        odd_rerandomization_scalars[i],
                    );

                    // The selected leaves are rerandomized individually, as we allow these commitments to use the same generators.
                    // Split the variables of the vector commitments into chunks corresponding to the M parents.
                    let chunks =
                        children_vars.chunks_exact(children_vars.len() / num_indices as usize);
                    for (inclusion_index, chunk) in chunks.enumerate() {
                        single_level_select_and_rerandomize(
                            prover,
                            &parameters.even_parameters,
                            &rerandomizations_of_selected[inclusion_index],
                            chunk.to_vec(),
                            Some(
                                (self.odd_internal_nodes[index][inclusion_index]
                                    .child_node_to_randomize
                                    + parameters.even_parameters.sl_params.delta)
                                    .into_affine(),
                            ),
                            Some(rerandomization_scalars_of_selected[inclusion_index]),
                        )?;
                    }
                }
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
        Ok(())
    }

    /// Number of leaf indices for which this multi-path was created. Assumes path was created honestly.
    pub fn num_indices(&self) -> u32 {
        self.odd_internal_nodes[0].len() as u32
    }

    fn process_root_nodes_for_given_multi_paths_with_common_root(
        paths: &[Self],
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<
        (
            RootChildrenSelected<F0, F1, P0, P1>,
            RootChildrenCoordsVars<F0, F1>,
        ),
        Error,
    > {
        // Check all paths are consistent and have the same root parity and count max indices in a path across all
        let is_root_even = paths[0].root_is_even();
        let mut max_num_indices = paths[0].num_indices();
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

            let num_indices = path.num_indices();

            if num_indices > M as u32 {
                return Err(Error::MoreIndicesThanSupportedBatchSize(
                    path.num_indices(),
                    M as u32,
                ));
            }

            if num_indices > max_num_indices {
                max_num_indices = num_indices;
            }
        }

        if is_root_even {
            let mut all_x_coords_root_children = Vec::with_capacity(L * max_num_indices as usize);
            let mut selected_children_plus_delta_grp_by_root_index =
                vec![vec![]; max_num_indices as usize];
            for path in paths.iter() {
                // Fill x-coordinates of all children of root and root is same for all paths and is not randomized
                if all_x_coords_root_children.len() == 0 && path.num_indices() == max_num_indices {
                    for j in 0..path.num_indices() as usize {
                        all_x_coords_root_children.extend_from_slice(
                            path.even_internal_nodes[0][j].x_coord_children.as_slice(),
                        );
                    }
                }
                for root_index in 0..path.num_indices() as usize {
                    selected_children_plus_delta_grp_by_root_index[root_index].push(
                        path.even_internal_nodes[0][root_index].child_node_to_randomize
                            + parameters.odd_parameters.sl_params.delta,
                    );
                }
            }
            let selected_children_plus_delta_grp_by_root_index =
                selected_children_plus_delta_grp_by_root_index
                    .into_iter()
                    .map(|s| Projective::normalize_batch(&s))
                    .collect::<Vec<_>>();

            let (selected_children_plus_delta, selected_children_of_root_xs) =
                Self::_process_root_nodes_for_given_multi_paths_with_common_root(
                    paths.len(),
                    max_num_indices,
                    all_x_coords_root_children,
                    selected_children_plus_delta_grp_by_root_index,
                    even_prover,
                )?;
            Ok((
                RootChildrenSelected::Even(selected_children_plus_delta),
                RootChildrenCoordsVars::Even(selected_children_of_root_xs),
            ))
        } else {
            let mut all_x_coords_root_children = Vec::with_capacity(L * max_num_indices as usize);
            let mut selected_children_plus_delta_grp_by_root_index =
                vec![vec![]; max_num_indices as usize];
            for path in paths.iter() {
                if all_x_coords_root_children.len() == 0 && path.num_indices() == max_num_indices {
                    for j in 0..path.num_indices() as usize {
                        all_x_coords_root_children.extend_from_slice(
                            path.odd_internal_nodes[0][j].x_coord_children.as_slice(),
                        );
                    }
                }
                for root_index in 0..path.num_indices() as usize {
                    selected_children_plus_delta_grp_by_root_index[root_index].push(
                        path.odd_internal_nodes[0][root_index].child_node_to_randomize
                            + parameters.even_parameters.sl_params.delta,
                    );
                }
            }
            let selected_children_plus_delta_grp_by_root_index =
                selected_children_plus_delta_grp_by_root_index
                    .into_iter()
                    .map(|s| Projective::normalize_batch(&s))
                    .collect::<Vec<_>>();

            let (selected_children_plus_delta, selected_children_of_root_xs) = CurveTreeWitnessMultiPath::<L, M, P1, P0>::_process_root_nodes_for_given_multi_paths_with_common_root(
                paths.len(),
                max_num_indices,
                all_x_coords_root_children,
                selected_children_plus_delta_grp_by_root_index,
                odd_prover,
            )?;
            Ok((
                RootChildrenSelected::Odd(selected_children_plus_delta),
                RootChildrenCoordsVars::Odd(selected_children_of_root_xs),
            ))
        }
    }

    fn _process_root_nodes_for_given_multi_paths_with_common_root(
        num_paths: usize,
        max_num_indices: u32,
        all_x_coords_root_children: Vec<F0>,
        mut selected_children_plus_delta_grp_by_root_index: Vec<Vec<Affine<P1>>>,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
    ) -> Result<(Vec<Vec<Affine<P1>>>, Vec<Vec<LinearCombination<F0>>>), Error> {
        let mut selected_children_plus_delta = vec![vec![]; num_paths];
        // Split the variables of the vector commitments into chunks corresponding to the `max_num_indices` roots.
        let chunks = all_x_coords_root_children
            .chunks_exact(all_x_coords_root_children.len() / max_num_indices as usize);
        let mut selected_children_of_root_xs = vec![vec![]; num_paths];
        for (root_index, chunk) in chunks.enumerate() {
            // Enforce set membership for the i-th root
            let xs = selected_children_plus_delta_grp_by_root_index[root_index]
                .iter()
                .map(|s| prover.allocate(Some(s.x)).unwrap().into())
                .collect::<Vec<_>>();
            let c = prover
                .transcript()
                .challenge_scalar(b"challenge-for-multi_select");
            multi_select_public_set_ext_challenge(prover, xs.clone(), chunk, c)?;
            for (j, x) in xs.into_iter().enumerate() {
                selected_children_of_root_xs[j].push(x);
            }
            for (j, child) in selected_children_plus_delta_grp_by_root_index[root_index]
                .drain(..)
                .into_iter()
                .enumerate()
            {
                selected_children_plus_delta[j].push(child);
            }
        }
        Ok((selected_children_plus_delta, selected_children_of_root_xs))
    }

    pub fn randomize_nodes<R: CryptoRngCore>(
        &self,
        (even_pc_gens, odd_pc_gens): (&PedersenGens<Affine<P0>>, &PedersenGens<Affine<P1>>),
        rng: &mut R,
    ) -> (
        Vec<Affine<P0>>,
        Vec<Affine<P1>>,
        Vec<P0::ScalarField>,
        Vec<P1::ScalarField>,
        Vec<Affine<P0>>,
        Vec<P0::ScalarField>,
    ) {
        let num_indices = self.num_indices();

        // for each even internal node, there must be a rerandomization of a commitment in the odd curve
        let even_length = self.even_internal_nodes.len();
        let mut odd_rerandomization_scalars: Vec<P1::ScalarField> = Vec::with_capacity(even_length);
        let mut odd_rerandomized_sum_of_nodes: Vec<Affine<P1>> = Vec::with_capacity(even_length);
        // and vice versa
        let odd_length = self.odd_internal_nodes.len();
        let mut even_rerandomization_scalars: Vec<P0::ScalarField> = Vec::with_capacity(odd_length);
        let mut even_rerandomized_sum_of_nodes: Vec<Affine<P0>> = Vec::with_capacity(odd_length);

        for even_multi_node in &self.even_internal_nodes {
            let mut sum_of_selected = Projective::<P1>::zero();
            for even_node in even_multi_node {
                sum_of_selected += even_node.child_node_to_randomize;
            }

            let rerandomization = F1::rand(rng);
            odd_rerandomization_scalars.push(rerandomization);
            let blinding = odd_pc_gens.B_blinding.mul(rerandomization).into_affine();
            odd_rerandomized_sum_of_nodes.push((sum_of_selected + blinding).into());
        }

        let mut rerandomization_scalars_of_selected = vec![F0::ZERO; num_indices as usize];
        let mut rerandomizations_of_selected = vec![Affine::<P0>::default(); num_indices as usize];
        for (index, odd_multi_node) in self.odd_internal_nodes.iter().enumerate() {
            if index < self.odd_internal_nodes.len() - 1 {
                let mut sum_of_selected = Projective::<P0>::zero();
                for odd_node in odd_multi_node {
                    sum_of_selected += odd_node.child_node_to_randomize;
                }

                let rerandomization: F0 = F0::rand(rng);
                even_rerandomization_scalars.push(rerandomization);
                let blinding = even_pc_gens.B_blinding.mul(rerandomization).into_affine();
                even_rerandomized_sum_of_nodes.push((sum_of_selected + blinding).into());
            } else {
                // multi_node is the parent of leaves
                for i in 0..num_indices as usize {
                    let rerandomization: F0 = F0::rand(rng);
                    rerandomization_scalars_of_selected[i] = rerandomization;
                    let blinding = even_pc_gens.B_blinding.mul(rerandomization).into_affine();
                    rerandomizations_of_selected[i] =
                        (odd_multi_node[i].child_node_to_randomize + blinding).into();
                }
            }
        }
        (
            even_rerandomized_sum_of_nodes,
            odd_rerandomized_sum_of_nodes,
            even_rerandomization_scalars,
            odd_rerandomization_scalars,
            rerandomizations_of_selected,
            rerandomization_scalars_of_selected,
        )
    }
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > WitnessNode<L, P0, P1>
{
    /// Prove a single level of the batched select and rerandomize relation.
    pub fn single_level_batched_select_and_rerandomize_prover_gadget(
        nodes: &[Self],
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        parameters: &SingleLayerProofParameters<P1>,
        parent_node: &Affine<P0>,
        parent_rerandomization_scalar: P0::ScalarField,
        rerandomized_sum_of_selected: &Affine<P1>,
        child_rerandomization_scalar: P1::ScalarField,
    ) -> Result<(), Error> {
        let num_indices = nodes.len();
        // `children_vars` is a vector of x-coordinates of all the `nodes`
        let children_vars = Self::allocate_multi_node_variables(
            nodes,
            prover,
            parent_node,
            parent_rerandomization_scalar,
        );

        let mut selected_children_plus_delta = vec![Projective::<P1>::zero(); num_indices];
        for i in 0..num_indices {
            selected_children_plus_delta[i] =
                nodes[i].child_node_to_randomize + parameters.sl_params.delta;
        }
        let selected_children_plus_delta =
            Projective::normalize_batch(&selected_children_plus_delta);

        single_level_batched_select_and_rerandomize(
            prover,
            parameters,
            num_indices as u32,
            rerandomized_sum_of_selected,
            children_vars,
            Some(&selected_children_plus_delta),
            Some(child_rerandomization_scalar),
        )?;

        Ok(())
    }

    /// Allocate variable for the children of a node in a multi path by committing to an internal node or using the children of the root as public input.
    pub fn allocate_multi_node_variables(
        nodes: &[Self],
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        parent_node: &Affine<P0>,
        parent_rerandomization_scalar: P0::ScalarField,
    ) -> Vec<LinearCombination<<P0>::ScalarField>> {
        // `children_vars` is a vector of x-coordinates of all the `nodes`
        let children_vars = if parent_rerandomization_scalar.is_zero() {
            let mut children_vars: Vec<LinearCombination<P0::ScalarField>> =
                Vec::with_capacity(L * nodes.len());
            for node in nodes {
                children_vars.append(&mut node.x_coord_children.map(constant).to_vec());
            }
            children_vars
        } else {
            let mut children: Vec<P0::ScalarField> = Vec::with_capacity(L * nodes.len());
            for node in nodes {
                children.append(&mut node.x_coord_children.to_vec());
            }
            let children_vars = prover.vars_for_committed_vec(
                parent_node,
                &children,
                parent_rerandomization_scalar,
            );
            children_vars
                .iter()
                .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
                .collect()
        };
        children_vars
    }
}

impl<F0: PrimeField, F1: PrimeField> RootChildrenCoordsVars<F0, F1> {
    pub fn validate_and_re_randomize_children<
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
        Cs0: ConstraintSystem<F0>,
        Cs1: ConstraintSystem<F1>,
    >(
        &mut self,
        selected_children_plus_delta: Option<&mut RootChildrenSelected<F0, F1, P0, P1>>,
        cs_even: &mut Cs0,
        cs_odd: &mut Cs1,
        even_rerandomized_sum_of_nodes: &Affine<P0>,
        odd_rerandomized_sum_of_nodes: &Affine<P1>,
        even_rerandomization_scalar: Option<P0::ScalarField>,
        odd_rerandomization_scalar: Option<P1::ScalarField>,
        num_indices: u32,
        is_root_even: bool,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        match self {
            Self::Even(children_x_coords) => {
                if !is_root_even {
                    return Err(Error::RootTypeMismatch {
                        expected: "even".to_string(),
                        got: "odd".to_string(),
                    });
                }
                let re_randomized_child_sum = &odd_rerandomized_sum_of_nodes;
                let children = selected_children_plus_delta.map(|s| match s {
                    RootChildrenSelected::Even(c) => c.remove(0),
                    _ => unreachable!(),
                });
                let children = children.as_ref().map(|c| c.as_slice());
                let x_coords = children_x_coords.remove(0);
                single_level_batched_validate_and_rerandomize_root_children(
                    cs_even,
                    &parameters.odd_parameters,
                    num_indices,
                    re_randomized_child_sum,
                    children,
                    x_coords,
                    odd_rerandomization_scalar,
                )
            }
            Self::Odd(children_x_coords) => {
                if is_root_even {
                    return Err(Error::RootTypeMismatch {
                        expected: "odd".to_string(),
                        got: "even".to_string(),
                    });
                }
                let re_randomized_child_sum = &even_rerandomized_sum_of_nodes;
                let children = selected_children_plus_delta.map(|s| match s {
                    RootChildrenSelected::Odd(c) => c.remove(0),
                    _ => unreachable!(),
                });
                let children = children.as_ref().map(|c| c.as_slice());
                let x_coords = children_x_coords.remove(0);
                single_level_batched_validate_and_rerandomize_root_children(
                    cs_odd,
                    &parameters.even_parameters,
                    num_indices,
                    re_randomized_child_sum,
                    children,
                    x_coords,
                    even_rerandomization_scalar,
                )
            }
        }
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
    CanonicalSerialize for RootChildrenForMultiPath<L, M, P0, P1>
{
    fn serialize_with_mode<W: ark_std::io::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        match self {
            RootChildrenForMultiPath::Even {
                x_coords,
                child_nodes_to_randomize,
            } => {
                0u8.serialize_with_mode(&mut writer, compress)?;
                x_coords.serialize_with_mode(&mut writer, compress)?;
                child_nodes_to_randomize.serialize_with_mode(&mut writer, compress)?;
            }
            RootChildrenForMultiPath::Odd {
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

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        1 + match self {
            RootChildrenForMultiPath::Even {
                x_coords,
                child_nodes_to_randomize,
            } => {
                x_coords.serialized_size(compress)
                    + child_nodes_to_randomize.serialized_size(compress)
            }
            RootChildrenForMultiPath::Odd {
                x_coords,
                child_nodes_to_randomize,
            } => {
                x_coords.serialized_size(compress)
                    + child_nodes_to_randomize.serialized_size(compress)
            }
        }
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
    CanonicalDeserialize for RootChildrenForMultiPath<L, M, P0, P1>
{
    fn deserialize_with_mode<R: ark_std::io::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let variant = u8::deserialize_with_mode(&mut reader, compress, validate)?;
        match variant {
            0 => {
                let x_coords = Vec::<[P0::ScalarField; L]>::deserialize_with_mode(
                    &mut reader,
                    compress,
                    validate,
                )?;
                let child_nodes_to_randomize =
                    Vec::<Affine<P1>>::deserialize_with_mode(&mut reader, compress, validate)?;
                Ok(RootChildrenForMultiPath::Even {
                    x_coords,
                    child_nodes_to_randomize,
                })
            }
            1 => {
                let x_coords = Vec::<[P1::ScalarField; L]>::deserialize_with_mode(
                    &mut reader,
                    compress,
                    validate,
                )?;
                let child_nodes_to_randomize =
                    Vec::<Affine<P0>>::deserialize_with_mode(&mut reader, compress, validate)?;
                Ok(RootChildrenForMultiPath::Odd {
                    x_coords,
                    child_nodes_to_randomize,
                })
            }
            _ => Err(ark_serialize::SerializationError::InvalidData),
        }
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
    ark_serialize::Valid for RootChildrenForMultiPath<L, M, P0, P1>
{
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        Ok(())
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
    CanonicalSerialize for WitnessMultiPathForSameRoot<L, M, P0, P1>
{
    fn serialize_with_mode<W: ark_std::io::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.root_children
            .serialize_with_mode(&mut writer, compress)?;
        self.even_internal_nodes
            .serialize_with_mode(&mut writer, compress)?;
        self.odd_internal_nodes
            .serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.root_children.serialized_size(compress)
            + self.even_internal_nodes.serialized_size(compress)
            + self.odd_internal_nodes.serialized_size(compress)
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
    CanonicalDeserialize for WitnessMultiPathForSameRoot<L, M, P0, P1>
{
    fn deserialize_with_mode<R: ark_std::io::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let root_children =
            RootChildrenForMultiPath::deserialize_with_mode(&mut reader, compress, validate)?;
        let even_internal_nodes = Vec::deserialize_with_mode(&mut reader, compress, validate)?;
        let odd_internal_nodes = Vec::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(WitnessMultiPathForSameRoot {
            root_children,
            even_internal_nodes,
            odd_internal_nodes,
        })
    }
}

impl<const L: usize, const M: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
    ark_serialize::Valid for WitnessMultiPathForSameRoot<L, M, P0, P1>
{
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        Ok(())
    }
}
