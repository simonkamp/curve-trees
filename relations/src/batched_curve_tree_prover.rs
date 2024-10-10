use bulletproofs::r1cs::*;

use crate::curve_tree_prover::{CurveTreeWitness, CurveTreeWitnessPath};
use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{CurveTree, SelRerandParameters, SelectAndRerandomizeMultiPath};
use ark_ec::AffineRepr;
use ark_ec::{
    models::short_weierstrass::{Projective, SWCurveConfig},
    short_weierstrass::Affine,
    CurveGroup,
};
use ark_ff::PrimeField;
use ark_std::Zero;
use merlin::Transcript;
use rand::Rng;
use std::ops::Mul;

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
        let mut even_internal_nodes: Vec<[CurveTreeWitness<L, P0, P1>; M]> = Vec::new();
        for i in 0..single_witnesses[0].even_internal_nodes.len() {
            let witnesses: Vec<_> = single_witnesses
                .iter()
                .map(|w| w.even_internal_nodes[i])
                .collect();
            even_internal_nodes.push(witnesses.try_into().unwrap());
        }

        let mut odd_internal_nodes: Vec<[CurveTreeWitness<L, P1, P0>; M]> = Vec::new();
        for i in 0..single_witnesses[0].odd_internal_nodes.len() {
            let witnesses: Vec<_> = single_witnesses
                .iter()
                .map(|w| w.odd_internal_nodes[i])
                .collect();
            odd_internal_nodes.push(witnesses.try_into().unwrap());
        }
        assert_eq!(
            self.height(),
            even_internal_nodes.len() + odd_internal_nodes.len()
        );
        CurveTreeWitnessMultiPath {
            even_internal_nodes,
            odd_internal_nodes,
        }
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
        let even_length = self.even_internal_nodes.len();
        let mut odd_rerandomization_scalars: Vec<P1::ScalarField> = Vec::with_capacity(even_length);
        let mut odd_rerandomized_commitments: Vec<Affine<P1>> = Vec::with_capacity(even_length);
        // and vice versa
        let odd_length = self.odd_internal_nodes.len();
        let mut even_rerandomization_scalars: Vec<P0::ScalarField> = Vec::with_capacity(odd_length);
        let mut even_rerandomized_commitments: Vec<Affine<P0>> = Vec::with_capacity(odd_length);

        for even in &self.even_internal_nodes {
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
        for (index, odd) in self.odd_internal_nodes.iter().enumerate() {
            if index < self.odd_internal_nodes.len() - 1 {
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
                    &self.even_internal_nodes[i],
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
                        &self.odd_internal_nodes[i],
                        prover,
                        &parameters.odd_parameters,
                        &parameters.even_parameters,
                        parent_rerandomization,
                        even_rerandomization_scalars[i],
                    );
                } else {
                    // self.odd_internal_nodes[i][0]
                    // .single_level_select_and_rerandomize_prover_gadget(
                    //     prover,
                    //     &parameters.odd_parameters,
                    //     &parameters.even_parameters,
                    //     parent_rerandomization,
                    //     rerandomization_scalars_of_selected[0],
                    // );
                    // todo, for now just show inclusion of the first leaf

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
            let mut children: Vec<P0::ScalarField> = Vec::new();
            for i in 0..M {
                children.append(&mut nodes[i].siblings.to_vec());
            }
            let (_, children_vars) = prover.commit_vec(
                &children,
                parent_rerandomization_scalar,
                &even_parameters.bp_gens,
            );
            children_vars
                .iter()
                .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
                .collect()
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
