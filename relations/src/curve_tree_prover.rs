use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{
    x_coordinates, CurveTree, CurveTreeNode, SelRerandParameters, SelectAndRerandomizeMultiPath,
    SelectAndRerandomizePath,
};
use ark_ec::AffineRepr;
use ark_ec::{
    models::short_weierstrass::{Projective, SWCurveConfig},
    short_weierstrass::Affine,
    CurveGroup,
};
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
    fn select_and_rerandomize_prover_witness(
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
        // todo capacity
        let mut even_nodes: Vec<CurveTreeWitness<L, P0, P1>> = Vec::new();
        let mut odd_nodes: Vec<CurveTreeWitness<L, P1, P0>> = Vec::new();

        match self {
            Self::Even(ct) => ct.select_and_rerandomize_prover_witness(
                index,
                tree_index,
                &mut even_nodes,
                &mut odd_nodes,
                &params.even_parameters.delta,
                &params.odd_parameters.delta,
            ),
            Self::Odd(ct) => ct.select_and_rerandomize_prover_witness(
                index,
                tree_index,
                &mut odd_nodes,
                &mut even_nodes,
                &params.odd_parameters.delta,
                &params.even_parameters.delta,
            ),
        }

        CurveTreeWitnessPath {
            even_internal_nodes: even_nodes,
            odd_nodes,
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

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf and the rerandomization scalar of the selected leaf.
    pub fn batched_select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        indices: [usize; M],
        even_prover: &mut Prover<Transcript, Affine<P0>>,
        odd_prover: &mut Prover<Transcript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (
        SelectAndRerandomizeMultiPath<L, M, P0, P1>,
        [P0::ScalarField; M],
    ) {
        let witness = self.select_and_rerandomize_prover_multi_witness(indices, parameters);

        witness.batched_select_and_rerandomize_prover_gadget(
            even_prover,
            odd_prover,
            parameters,
            rng,
        )
    }

    /// Produce a witness of the paths to the commitments indexed by `indices` including siblings.
    pub fn select_and_rerandomize_prover_multi_witness(
        &self,
        indices: [usize; M],
        params: &SelRerandParameters<P0, P1>,
    ) -> CurveTreeWitnessMultiPath<L, M, P0, P1> {
        let mut single_witnesses: Vec<CurveTreeWitnessPath<L, P0, P1>> = Vec::with_capacity(M);
        for i in 0..M {
            single_witnesses
                .push(self.select_and_rerandomize_prover_witness(indices[i], i, params));
        }
        let mut even_nodes: Vec<[CurveTreeWitness<L, P0, P1>; M]> = Vec::new();
        for i in 0..single_witnesses[0].even_internal_nodes.len() - 1 {
            let witnesses: Vec<_> = single_witnesses
                .iter()
                .map(|w| w.even_internal_nodes[i])
                .collect();
            even_nodes.push(witnesses.try_into().unwrap());
        }

        let mut odd_nodes: Vec<[CurveTreeWitness<L, P1, P0>; M]> = Vec::new();
        for i in 0..single_witnesses[0].odd_nodes.len() - 1 {
            let witnesses: Vec<_> = single_witnesses.iter().map(|w| w.odd_nodes[i]).collect();
            odd_nodes.push(witnesses.try_into().unwrap());
        }
        CurveTreeWitnessMultiPath {
            even_nodes,
            odd_nodes,
        }
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
    pub odd_nodes: Vec<CurveTreeWitness<L, P1, P0>>,
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
        let even = self.even_internal_nodes.len() == self.odd_nodes.len();
        // Otherwise there must be an additional even node which has the odd root as parent.
        if !even {
            assert!(self.even_internal_nodes.len() + 1 == self.odd_nodes.len())
        };
        return even;
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
        let odd_length = self.odd_nodes.len();
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
        for (i, odd) in self.odd_nodes.iter().enumerate() {
            let rerandomization = F0::rand(rng);
            let blinding = parameters
                .even_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            let rerandomized = (odd.child_witness + blinding).into();
            if i < self.odd_nodes.len() - 1 {
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
                self.odd_nodes[i].single_level_select_and_rerandomize_prover_gadget(
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
    // list of internal even nodes
    pub even_nodes: Vec<[CurveTreeWitness<L, P0, P1>; M]>, // todo this includes the leaf node
    // list of internal odd nodes
    pub odd_nodes: Vec<[CurveTreeWitness<L, P1, P0>; M]>,
}

// Prove multiple inclusions using a CurveTreeWitnessPath
impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessMultiPath<L, M, P0, P1>
{
    fn root_is_even(&self) -> bool {
        if self.even_nodes.len() == self.odd_nodes.len() {
            return true;
        }
        if self.even_nodes.len() + 1 == self.odd_nodes.len() {
            return false;
        }
        panic!("Invalid witness path");
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf
    /// and the rerandomization scalar of the selected leaf.
    pub fn batched_select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        even_prover: &mut Prover<Transcript, Affine<P0>>,
        odd_prover: &mut Prover<Transcript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (
        SelectAndRerandomizeMultiPath<L, M, P0, P1>,
        [P0::ScalarField; M],
    ) {
        // for each even internal node, there must be a rerandomization of a commitment in the odd curve
        let even_length = self.even_nodes.len();
        let mut odd_rerandomization_scalars: Vec<P1::ScalarField> = Vec::with_capacity(even_length);
        let mut odd_rerandomized_commitments: Vec<Affine<P1>> = Vec::with_capacity(even_length);
        // and vice versa
        let odd_length = self.odd_nodes.len();
        let mut even_rerandomization_scalars: Vec<P0::ScalarField> = Vec::with_capacity(odd_length);
        let mut even_rerandomized_commitments: Vec<Affine<P0>> = Vec::with_capacity(odd_length);

        for even in &self.even_nodes {
            let mut sum_of_selected = Projective::<P1>::zero();
            for i in 0..M {
                sum_of_selected = sum_of_selected + even[i].child_witness; // todo: delta?
            }

            let rerandomization = F1::rand(rng);
            odd_rerandomization_scalars.push(rerandomization);
            let blinding = parameters
                .odd_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            odd_rerandomized_commitments.push((sum_of_selected + blinding).into());
        }

        let mut rerandomization_scalars_of_selected = [F0::ZERO; M];
        let mut rerandomizations_of_selected = [Affine::<P0>::default(); M];
        for (index, odd) in self.odd_nodes.iter().enumerate() {
            if index < self.odd_nodes.len() - 1 {
                let mut sum_of_selected = Projective::<P0>::zero();
                for i in 0..M {
                    sum_of_selected = sum_of_selected + odd[i].child_witness; // todo: I believe delta is accounted for?
                }

                let rerandomization: F0 = F0::rand(rng);
                even_rerandomization_scalars.push(rerandomization);
                let blinding = parameters
                    .even_parameters
                    .pc_gens
                    .B_blinding
                    .mul(rerandomization)
                    .into_affine();
                even_rerandomized_commitments.push((sum_of_selected + blinding).into());
            } else {
                for i in 0..M {
                    let rerandomization: F0 = F0::rand(rng);
                    rerandomization_scalars_of_selected[i] = rerandomization;
                    let blinding = parameters
                        .even_parameters
                        .pc_gens
                        .B_blinding
                        .mul(rerandomization)
                        .into_affine();
                    rerandomizations_of_selected[i] = (odd[i].child_witness + blinding).into();
                }
            }
        }

        // Todo: The leaf level needs separate select and rerandomize relations for soundness. Fix after implementing for the verifier and testing.
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
                CurveTreeWitness::single_level_batched_select_and_rerandomize_prover_gadget(
                    &self.even_nodes[i],
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
                if i < odd_length - 1 {
                    CurveTreeWitness::single_level_batched_select_and_rerandomize_prover_gadget(
                        &self.odd_nodes[i],
                        prover,
                        &parameters.odd_parameters,
                        &parameters.even_parameters,
                        parent_rerandomization,
                        even_rerandomization_scalars[i],
                    );
                } else {
                    // The selected leaves are rerandomized individually, as we allow these commitments to use the same generators.
                    for inclusion_index in 0..M {
                        // todo how do variables work here?
                        // self.odd_nodes[i][inclusion_index]
                        //     .single_level_select_and_rerandomize_prover_gadget(
                        //         prover,
                        //         &parameters.odd_parameters,
                        //         &parameters.even_parameters,
                        //         parent_rerandomization,
                        //         rerandomization_scalars_of_selected[inclusion_index],
                        //     )
                    }
                }
            }
        };
        #[cfg(not(feature = "parallel"))]
        prove_odd(odd_prover);

        #[cfg(feature = "parallel")]
        rayon::join(|| prove_even(even_prover), || prove_odd(odd_prover));

        (
            SelectAndRerandomizeMultiPath {
                even_commitments: even_rerandomized_commitments,
                odd_commitments: odd_rerandomized_commitments,
                selected_commitments: rerandomizations_of_selected,
            },
            rerandomization_scalars_of_selected,
        )
    }
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > CurveTreeWitness<L, P0, P1>
{
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

    // Prove a single level of the batched select and rerandomize relation.
    pub fn single_level_batched_select_and_rerandomize_prover_gadget<const M: usize>(
        nodes: &[Self; M],
        prover: &mut Prover<Transcript, Affine<P0>>,
        even_parameters: &SingleLayerParameters<P0>,
        odd_parameters: &SingleLayerParameters<P1>,
        parent_rerandomization_scalar: P0::ScalarField,
        child_rerandomization_scalar: P1::ScalarField,
    ) {
        let children_vars = if parent_rerandomization_scalar.is_zero() {
            let mut children_vars: Vec<LinearCombination<P0::ScalarField>> = Vec::new();
            for i in 0..M {
                children_vars.append(&mut nodes[i].siblings.map(constant).to_vec());
            }
            children_vars
        } else {
            // todo quick fix, clean up
            let mut children_vars: Vec<LinearCombination<P0::ScalarField>> = Vec::new();
            for i in 0..M {
                let (_, node_children_vars) = prover.commit_vec(
                    &nodes[i].siblings,
                    parent_rerandomization_scalar,
                    &even_parameters.bp_gens,
                );
                let mut node_children_lin_combs = node_children_vars
                    .iter()
                    .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
                    .collect();
                children_vars.append(&mut node_children_lin_combs);
            }
            children_vars
        };

        // Todo: The sum of selected was computed previously
        let (selected_children, sum_of_selected) = {
            let mut sum_of_selected = Projective::<P1>::zero();
            let mut children: [Affine<P1>; M] = [Affine::<P1>::zero(); M];
            for i in 0..M {
                sum_of_selected = sum_of_selected + nodes[i].child_witness; // todo: delta?
                children[i] = (nodes[i].child_witness + odd_parameters.delta).into_affine();
            }
            (children, sum_of_selected)
        };
        let blinding = odd_parameters.pc_gens.B_blinding * child_rerandomization_scalar;
        let rerandomized_sum_of_selected = (sum_of_selected + blinding).into_affine();

        single_level_batched_select_and_rerandomize(
            prover,
            odd_parameters,
            &rerandomized_sum_of_selected,
            children_vars,
            Some(&selected_children),
            Some(child_rerandomization_scalar),
        );
    }
}
