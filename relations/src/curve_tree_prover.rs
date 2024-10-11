use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{
    x_coordinates, CurveTree, CurveTreeNode, SelRerandParameters, SelectAndRerandomizePath,
};

use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, CurveGroup};
use ark_ff::PrimeField;
use ark_std::fmt::Debug;
use ark_std::fmt::Formatter;
use ark_std::Zero;
use merlin::Transcript;
use rand::Rng;
use std::ops::Mul;

impl<
        const L: usize,
        const M: usize,
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    > CurveTreeNode<L, M, P0, P1>
{
    pub fn select_and_rerandomize_prover_witness(
        &self,
        index: usize,
        tree_index: usize,
        even_nodes: &mut Vec<CurveTreeWitness<L, P0, P1>>,
        odd_nodes: &mut Vec<CurveTreeWitness<L, P1, P0>>,
        delta_even: &Affine<P0>,
        delta_odd: &Affine<P1>,
    ) {
        if let Self::Branch {
            parent_commitment: _,
            children,
            height: _,
            elements: _,
        } = &self
        {
            let child_index = self.child_index(index);
            let child = match &children[self.child_index(index)] {
                None => panic!(
                    "Child index out of bounds. Height: {}, Index: {}, Local index: {}",
                    self.height(),
                    index,
                    child_index
                ),
                Some(child) => child,
            };
            let siblings = x_coordinates(children, delta_odd, tree_index);

            even_nodes.push(CurveTreeWitness {
                siblings,
                child_witness: child.commitment(tree_index),
            });

            // recursively add the remaining path
            child.select_and_rerandomize_prover_witness(
                index, tree_index, odd_nodes, even_nodes, delta_odd, delta_even,
            );
        }
    }
}

// Implements prover operations on the Curve Tree
impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    /// Produce a witness of the path to the commitment at `index` including siblings.
    pub fn select_and_rerandomize_prover_witness(
        &self,
        index: usize,
        tree_index: usize,
        params: &SelRerandParameters<P0, P1>,
    ) -> CurveTreeWitnessPath<L, P0, P1> {
        let mut even_internal_nodes: Vec<CurveTreeWitness<L, P0, P1>> = Vec::new();
        let mut odd_internal_nodes: Vec<CurveTreeWitness<L, P1, P0>> = Vec::new();

        match self {
            Self::Even(ct) => ct.select_and_rerandomize_prover_witness(
                index,
                tree_index,
                &mut even_internal_nodes,
                &mut odd_internal_nodes,
                &params.even_parameters.delta,
                &params.odd_parameters.delta,
            ),
            Self::Odd(ct) => ct.select_and_rerandomize_prover_witness(
                index,
                tree_index,
                &mut odd_internal_nodes,
                &mut even_internal_nodes,
                &params.odd_parameters.delta,
                &params.even_parameters.delta,
            ),
        }

        assert_eq!(
            self.height(),
            even_internal_nodes.len() + odd_internal_nodes.len()
        );
        CurveTreeWitnessPath {
            even_internal_nodes,
            odd_internal_nodes,
        }
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        index: usize,
        tree_index: usize,
        even_prover: &mut Prover<Transcript, Affine<P0>>,
        odd_prover: &mut Prover<Transcript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField) {
        let witness = self.select_and_rerandomize_prover_witness(index, tree_index, parameters);
        witness.select_and_rerandomize_prover_gadget(even_prover, odd_prover, parameters, rng)
    }
}

/// A witness of a node on a Curve Tree path including siblings.
/// Contains the information needed to prove the single level select and rerandomize relation.
#[derive(Copy, Clone)]
pub struct CurveTreeWitness<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    pub siblings: [P0::ScalarField; L],
    pub child_witness: Affine<P1>,
}

impl<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> Debug
    for CurveTreeWitness<L, P0, P1>
{
    // This is a dummy implementation to allow unwrapping the result of converting a vector into an array of the same size.
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "CurveTreeWitness")
    }
}

/// A witness of a Curve Tree path including siblings for all nodes on the path.
/// Contains all information needed to prove the select and rerandomize relation.
#[derive(Clone, Default)]
pub struct CurveTreeWitnessPath<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
{
    // list of internal even nodes including the selected leaf.
    pub even_internal_nodes: Vec<CurveTreeWitness<L, P0, P1>>,
    // list of internal odd nodes
    pub odd_internal_nodes: Vec<CurveTreeWitness<L, P1, P0>>,
    // the root is not explicitly represented
}

// Prove a single inclusion using a CurveTreeWitnessPath
impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessPath<L, P0, P1>
{
    fn root_is_even(&self) -> bool {
        // The leaf is even and included in the internal even nodes.
        // If the number of internal even and odd nodes is equal,
        // then the first odd node is the parent of the first even node and a child of the even root.
        let even = self.even_internal_nodes.len() == self.odd_internal_nodes.len();
        // Otherwise there must be an additional even node which has the odd root as parent.
        if !even {
            assert!(self.even_internal_nodes.len() + 1 == self.odd_internal_nodes.len())
        };
        even
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf
    /// and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        even_prover: &mut Prover<Transcript, Affine<P0>>,
        odd_prover: &mut Prover<Transcript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField) {
        // for each even internal node, there must be a rerandomization of a commitment in the odd curve
        let even_length = self.even_internal_nodes.len();
        let mut odd_rerandomization_scalars: Vec<P1::ScalarField> = Vec::with_capacity(even_length);
        let mut odd_rerandomized_commitments: Vec<Affine<P1>> = Vec::with_capacity(even_length);
        // and vice versa
        let odd_length = self.odd_internal_nodes.len();
        let mut even_rerandomization_scalars: Vec<P0::ScalarField> = Vec::with_capacity(odd_length);
        let mut even_rerandomized_commitments: Vec<Affine<P0>> = Vec::with_capacity(odd_length);

        for even in &self.even_internal_nodes {
            let rerandomization = F1::rand(rng);
            odd_rerandomization_scalars.push(rerandomization);
            let blinding = parameters
                .odd_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            odd_rerandomized_commitments.push((even.child_witness + blinding).into());
        }

        let mut rerandomization_scalar_of_selected = F0::default();
        let mut rerandomization_of_selected = Affine::<P0>::default();
        for (i, odd) in self.odd_internal_nodes.iter().enumerate() {
            let rerandomization = F0::rand(rng);
            let blinding = parameters
                .even_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            let rerandomized = (odd.child_witness + blinding).into();
            if i < self.odd_internal_nodes.len() - 1 {
                even_rerandomization_scalars.push(rerandomization);
                even_rerandomized_commitments.push(rerandomized);
            } else {
                even_rerandomization_scalars.push(rerandomization); // todo quick fix
                rerandomization_scalar_of_selected = rerandomization;
                rerandomization_of_selected = rerandomized;
            }
        }

        let prove_even = |prover: &mut Prover<Transcript, Affine<P0>>| {
            for i in 0..even_length {
                let parent_rerandomization = if self.root_is_even() {
                    if i == 0 {
                        // the parent is the the root and thus not rerandomized
                        F0::zero()
                    } else {
                        even_rerandomization_scalars[i - 1]
                    }
                } else {
                    even_rerandomization_scalars[i]
                };
                self.even_internal_nodes[i].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.even_parameters,
                    &parameters.odd_parameters,
                    parent_rerandomization,
                    odd_rerandomization_scalars[i],
                );
            }
        };
        #[cfg(not(feature = "parallel"))]
        prove_even(even_prover);
        let prove_odd = |prover: &mut Prover<Transcript, Affine<P1>>| {
            for i in 0..odd_length {
                let parent_rerandomization = if !self.root_is_even() {
                    if i == 0 {
                        // the parent is the the root and thus not rerandomized
                        F1::zero()
                    } else {
                        odd_rerandomization_scalars[i - 1]
                    }
                } else {
                    odd_rerandomization_scalars[i]
                };
                self.odd_internal_nodes[i].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.odd_parameters,
                    &parameters.even_parameters,
                    parent_rerandomization,
                    even_rerandomization_scalars[i],
                );
            }
        };
        #[cfg(not(feature = "parallel"))]
        prove_odd(odd_prover);

        #[cfg(feature = "parallel")]
        rayon::join(|| prove_even(even_prover), || prove_odd(odd_prover));

        (
            SelectAndRerandomizePath {
                selected_commitment: rerandomization_of_selected,
                odd_commitments: odd_rerandomized_commitments,
                even_commitments: even_rerandomized_commitments,
            },
            rerandomization_scalar_of_selected, // This is the scalar applied to the selected leaf for rerandomization
        )
    }
}

/// A witness of M paths in M independently generated Curve Trees including siblings for all nodes on the paths.
/// Contains all information needed to prove M batched select and rerandomize relations.
#[derive(Clone)]
pub struct CurveTreeWitnessMultiPath<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig + Copy,
> {
    // list of internal even nodes including the selected leaves
    pub even_internal_nodes: Vec<[CurveTreeWitness<L, P0, P1>; M]>,
    // list of internal odd nodes
    pub odd_internal_nodes: Vec<[CurveTreeWitness<L, P1, P0>; M]>,
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > CurveTreeWitness<L, P0, P1>
{
    /// Allocates variables for the children and proves select and rerandomize for one.
    /// If the parent is the root, the variables are allocated directly, otherwise by committing to the parent.
    pub fn single_level_select_and_rerandomize_prover_gadget(
        &self,
        prover: &mut Prover<Transcript, Affine<P0>>,
        even_parameters: &SingleLayerParameters<P0>,
        odd_parameters: &SingleLayerParameters<P1>,
        parent_rerandomization_scalar: P0::ScalarField,
        child_rerandomization_scalar: P1::ScalarField,
    ) {
        let children_vars = if parent_rerandomization_scalar.is_zero() {
            // In this case the parent is the root and the children are treated as public input to the circuit.
            self.siblings.map(constant).to_vec()
        } else {
            // In this case the parent is a rerandomized commitment and the children (and the scalar used for rerandomizing) are part of the witness.
            let (_, children_vars) = prover.commit_vec(
                &self.siblings,
                parent_rerandomization_scalar,
                &even_parameters.bp_gens,
            );
            children_vars
                .iter()
                .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
                .collect()
        };
        self.single_level_select_and_rerandomize_prover_gadget_helper(
            prover,
            odd_parameters,
            child_rerandomization_scalar,
            children_vars,
        );
    }

    /// Proves the select and rerandomize for one of the children represented by the variables.
    pub fn single_level_select_and_rerandomize_prover_gadget_helper(
        &self,
        prover: &mut Prover<Transcript, Affine<P0>>,
        odd_parameters: &SingleLayerParameters<P1>,
        child_rerandomization_scalar: P1::ScalarField,
        children_vars: Vec<LinearCombination<<P0>::ScalarField>>,
    ) {
        let child_commitment = self.child_witness;
        let blinding = odd_parameters.pc_gens.B_blinding * child_rerandomization_scalar;
        let rerandomized_child = child_commitment + blinding.into_affine();

        single_level_select_and_rerandomize(
            prover,
            odd_parameters,
            &rerandomized_child.into(),
            children_vars,
            Some((child_commitment + odd_parameters.delta).into_affine()),
            Some(child_rerandomization_scalar),
        );
    }
}
