use crate::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use crate::curve::{checked_curve_addition_helper, curve_check, PointRepresentation};
use crate::curve_tree::{
    SelectAndRerandomizeMultiPath, SelectAndRerandomizeMultiPathWithDivisorComms,
};
use crate::curve_tree_prover::WitnessNode;
use crate::error::{Error, Result};
use crate::prover::{constraints_for_dlogs, create_and_commit_divisor};
use crate::select::{select, select_public_set};
use ark_dlog_gadget::dlog::{DiscreteLogParameters, DivisorComms, PointWithDlog};

use crate::parameters::{SelRerandProofParametersRef, SingleLayerProofParametersNew};
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::DivisorCurve;
use ark_ff::{PrimeField, Zero};
use ark_std::marker::PhantomData;
use ark_std::vec;
use ark_std::{boxed::Box, vec::Vec};
use bulletproofs::r1cs::{constant, ConstraintSystem, LinearCombination, Prover, Variable};
use bulletproofs::BulletproofGens;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use zeroize::Zeroize;

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: DivisorCurve<BaseField = F1, ScalarField = F0> + Copy,
        P1: DivisorCurve<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessMultiPath<L, M, P0, P1>
{
    /// Divisor-based batched select and rerandomize prover gadget.
    /// Returns path commitments, leaf rerandomizations, and divisor commitments for root, non-root levels, and leaves.
    pub fn batched_select_and_rerandomize_prover_gadget_new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
        rng: &mut R,
    ) -> Result<(
        SelectAndRerandomizeMultiPathWithDivisorComms<L, M, P0, P1>,
        Vec<P0::ScalarField>,
    )> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

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
            mut even_rerandomization_scalars,
            mut odd_rerandomization_scalars,
            rerandomizations_of_selected,
            rerandomization_scalars_of_selected,
        ) = self.randomize_nodes((even_parameters.pc_gens(), odd_parameters.pc_gens()), rng);

        let root_is_even = self.root_is_even();

        let mut even_node_divisors = Vec::new();
        let mut even_node_comms = Vec::new();
        let mut odd_node_divisors = Vec::new();
        let mut odd_node_comms = Vec::new();

        if root_is_even {
            let (sum_x_var, sum_y_var, x, y, divisor_comms, p) =
                Self::select_and_commit_divisor_for_root::<_, Parameters0>(
                    rng,
                    even_prover,
                    num_indices,
                    &self.even_internal_nodes[0],
                    odd_rerandomized_sum_of_nodes[0],
                    odd_rerandomization_scalars[0],
                    odd_parameters,
                    &even_parameters.sl_params.bp_gens,
                )?;
            even_node_comms.push(divisor_comms);
            even_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
        } else {
            let (sum_x_var, sum_y_var, x, y, divisor_comms, p) =
                CurveTreeWitnessMultiPath::<L, M, P1, P0>::select_and_commit_divisor_for_root::<
                    _,
                    Parameters1,
                >(
                    rng,
                    odd_prover,
                    num_indices,
                    &self.odd_internal_nodes[0],
                    even_rerandomized_sum_of_nodes[0],
                    even_rerandomization_scalars[0],
                    even_parameters,
                    &odd_parameters.sl_params.bp_gens,
                )?;
            odd_node_comms.push(divisor_comms);
            odd_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
        }

        // Process even non-root nodes
        for i in 0..self.even_internal_nodes.len() {
            let index = if root_is_even { i + 1 } else { i };
            if self.even_internal_nodes.len() == index {
                continue;
            }

            let (sum_x_var, sum_y_var, x, y, divisor_comms, p) =
                Self::select_and_commit_divisor_for_non_root::<_, Parameters0>(
                    rng,
                    even_prover,
                    num_indices,
                    &self.even_internal_nodes[index],
                    odd_rerandomized_sum_of_nodes[index],
                    odd_rerandomization_scalars[index],
                    &even_rerandomized_sum_of_nodes[i],
                    even_rerandomization_scalars[i],
                    odd_parameters,
                    &even_parameters.sl_params.bp_gens,
                )?;
            even_node_comms.push(divisor_comms);
            even_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
        }

        // Process odd non-root nodes (except last level which has leaves)
        for i in 0..self.odd_internal_nodes.len() {
            let index = if !root_is_even { i + 1 } else { i };
            if self.odd_internal_nodes.len() == index {
                continue;
            }

            if index < (self.odd_internal_nodes.len() - 1) {
                let (sum_x_var, sum_y_var, x, y, divisor_comms, p) = CurveTreeWitnessMultiPath::<L, M, P1, P0>::select_and_commit_divisor_for_non_root::<_, Parameters1>(
                    rng,
                    odd_prover,
                    num_indices,
                    &self.odd_internal_nodes[index],
                    even_rerandomized_sum_of_nodes[index],
                    even_rerandomization_scalars[index],
                    &odd_rerandomized_sum_of_nodes[i],
                        odd_rerandomization_scalars[i],
                    even_parameters,
                    &odd_parameters.sl_params.bp_gens,
                )?;
                odd_node_comms.push(divisor_comms);
                odd_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
            }
        }

        // Process leaf level - individual divisor proofs for each leaf
        {
            let last_odd_index = self.odd_internal_nodes.len() - 1;
            let nodes = &self.odd_internal_nodes[last_odd_index];

            // Parent info for allocating variables
            let parent_index = if !root_is_even && last_odd_index > 0 {
                last_odd_index - 1
            } else {
                last_odd_index
            };
            let parent_scalar = if parent_index < odd_rerandomization_scalars.len() {
                odd_rerandomization_scalars[parent_index]
            } else {
                F1::zero()
            };

            // Allocate variables for all children x-coords
            let mut children_x_coords: Vec<F1> = Vec::with_capacity(L * num_indices as usize);
            for node in nodes {
                children_x_coords.extend_from_slice(node.x_coord_children.as_slice());
            }

            let children_vars: Vec<LinearCombination<F1>> = if parent_scalar.is_zero() {
                children_x_coords.iter().map(|x| constant(*x)).collect()
            } else {
                let parent_node = &odd_rerandomized_sum_of_nodes[parent_index];
                let vars = odd_prover.vars_for_committed_vec(
                    parent_node,
                    &children_x_coords,
                    parent_scalar,
                );
                vars.iter().map(|v| (*v).into()).collect()
            };

            // Split into chunks for each index
            let chunk_size = children_vars.len() / num_indices as usize;
            let chunks: Vec<_> = children_vars.chunks_exact(chunk_size).collect();

            for (i, chunk) in chunks.iter().enumerate() {
                let child_plus_delta = (nodes[i].child_node_to_randomize
                    + even_parameters.sl_params.delta)
                    .into_affine();

                // Allocate x, y variables on odd_prover (F1 constraint system for P0 base field)
                let x_var = odd_prover.allocate(Some(child_plus_delta.x)).unwrap();
                let y_var = odd_prover.allocate(Some(child_plus_delta.y)).unwrap();

                // Select on odd_prover
                select(odd_prover, x_var.into(), chunk.iter().cloned())?;

                // Add transcript entry for rerandomized leaf
                odd_prover
                    .transcript()
                    .append(b"rerandomized_child", &rerandomizations_of_selected[i]);

                let rerandomized_plus_delta = (rerandomizations_of_selected[i]
                    + even_parameters.sl_params.delta)
                    .into_affine();
                let (x, y) = rerandomized_plus_delta
                    .xy()
                    .ok_or_else(|| Error::PointCantBeZero)?;

                let (divisor_comms, p) = create_and_commit_divisor::<_, F1, F0, P1, P0, Parameters1>(
                    rng,
                    odd_prover,
                    rerandomization_scalars_of_selected[i],
                    &even_parameters.table_b_blinding,
                    &odd_parameters.sl_params.bp_gens,
                )?;

                odd_node_comms.push(divisor_comms);
                odd_node_divisors.push((x_var.into(), y_var.into(), x, y, p));
            }
        }

        constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_prover,
            odd_prover,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors,
            odd_node_divisors,
        )?;

        Zeroize::zeroize(&mut odd_rerandomization_scalars);
        Zeroize::zeroize(&mut even_rerandomization_scalars);

        Ok((
            SelectAndRerandomizeMultiPathWithDivisorComms {
                path: SelectAndRerandomizeMultiPath {
                    even_commitments: even_rerandomized_sum_of_nodes,
                    odd_commitments: odd_rerandomized_sum_of_nodes,
                    selected_commitments: rerandomizations_of_selected,
                },
                even_divisor_comms: even_node_comms,
                odd_divisor_comms: odd_node_comms,
            },
            rerandomization_scalars_of_selected,
        ))
    }

    fn select_and_commit_divisor_for_root<R: CryptoRngCore, Parameters0: DiscreteLogParameters>(
        rng: &mut R,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        num_indices: u32,
        witness_nodes: &[WitnessNode<L, P0, P1>],
        re_randomized_sum_of_children: Affine<P1>,
        child_re_randomization: F1,
        parameters: &SingleLayerProofParametersNew<P1, Parameters0>,
        bp_gens: &BulletproofGens<Affine<P0>>,
    ) -> Result<(
        LinearCombination<F0>,
        LinearCombination<F0>,
        F0,
        F0,
        DivisorComms<Affine<P0>>,
        Box<PointWithDlog<F0, Parameters0>>,
    )> {
        let mut all_children_x: Vec<F0> = Vec::with_capacity(L * num_indices as usize);
        let mut selected_children_plus_delta: Vec<Affine<P1>> =
            Vec::with_capacity(num_indices as usize);

        for i in 0..num_indices as usize {
            all_children_x.extend_from_slice(witness_nodes[i].x_coord_children.as_slice());
            selected_children_plus_delta.push(
                (witness_nodes[i].child_node_to_randomize + parameters.sl_params.delta)
                    .into_affine(),
            );
        }

        // Batched select and accumulate for root
        let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_root::<F0, P1, _>(
            prover,
            num_indices,
            &all_children_x,
            Some(&selected_children_plus_delta),
        )?;

        // Compute the target point for discrete log verification
        let shifted_rerandomized = (re_randomized_sum_of_children
            + (parameters.sl_params.delta * P1::ScalarField::from(num_indices as u64)))
        .into_affine();
        let (x, y) = shifted_rerandomized
            .xy()
            .ok_or_else(|| Error::PointCantBeZero)?;

        // Create single divisor proof for the sum
        let (divisor_comms, p) = create_and_commit_divisor::<_, F0, F1, P0, P1, Parameters0>(
            rng,
            prover,
            child_re_randomization,
            &parameters.table_b_blinding,
            bp_gens,
        )?;
        Ok((sum_x_var, sum_y_var, x, y, divisor_comms, p))
    }

    fn select_and_commit_divisor_for_non_root<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
    >(
        rng: &mut R,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        num_indices: u32,
        witness_nodes: &[WitnessNode<L, P0, P1>],
        re_randomized_sum_of_children: Affine<P1>,
        child_re_randomization: F1,
        parent_node: &Affine<P0>,
        parent_rerandomization_scalar: F0,
        parameters: &SingleLayerProofParametersNew<P1, Parameters0>,
        bp_gens: &BulletproofGens<Affine<P0>>,
    ) -> Result<(
        LinearCombination<F0>,
        LinearCombination<F0>,
        F0,
        F0,
        DivisorComms<Affine<P0>>,
        Box<PointWithDlog<F0, Parameters0>>,
    )> {
        let children_vars = WitnessNode::allocate_multi_node_variables(
            witness_nodes,
            prover,
            parent_node,
            parent_rerandomization_scalar,
        );

        let mut selected_children_plus_delta = vec![Projective::<P1>::zero(); num_indices as usize];
        for j in 0..num_indices as usize {
            selected_children_plus_delta[j] =
                witness_nodes[j].child_node_to_randomize + parameters.sl_params.delta;
        }
        let selected_children_plus_delta =
            Projective::normalize_batch(&selected_children_plus_delta);

        let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_non_root(
            prover,
            num_indices,
            children_vars,
            Some(&selected_children_plus_delta),
        )?;

        let shifted_rerandomized = (re_randomized_sum_of_children
            + (parameters.sl_params.delta * P1::ScalarField::from(num_indices)))
        .into_affine();
        let (x, y) = shifted_rerandomized
            .xy()
            .ok_or_else(|| Error::PointCantBeZero)?;

        let (divisor_comms, p) = create_and_commit_divisor::<_, F0, F1, P0, P1, Parameters0>(
            rng,
            prover,
            child_re_randomization,
            &parameters.table_b_blinding,
            bp_gens,
        )?;
        Ok((sum_x_var, sum_y_var, x, y, divisor_comms, p))
    }
}

pub fn batched_select_and_accumulate_root<
    F: PrimeField,
    C: SWCurveConfig<BaseField = F> + Copy,
    Cs: ConstraintSystem<F>,
>(
    cs: &mut Cs,
    num_indices: u32, // The number of parallel selections
    all_children_x_coords: &[F],
    selected_children_plus_delta: Option<&[Affine<C>]>,
) -> Result<(
    Option<Affine<C>>,
    LinearCombination<F>,
    LinearCombination<F>,
)> {
    // Initialize the accumulated sum of the selected children to dummy values.
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        point: None,
    };

    let chunk_size = all_children_x_coords.len() / (num_indices as usize);
    let chunks: Vec<_> = all_children_x_coords.chunks_exact(chunk_size).collect();

    for (i, chunk) in chunks.iter().enumerate() {
        let ith_selected_witness = selected_children_plus_delta.map(|xy| xy[i]);
        let x_var = cs.allocate(ith_selected_witness.map(|xy| xy.x)).unwrap();
        let y_var = cs.allocate(ith_selected_witness.map(|xy| xy.y)).unwrap();

        // Select from public set
        select_public_set(cs, x_var.into(), chunk)?;

        // Curve check
        curve_check(cs, x_var.into(), y_var.into(), C::COEFF_A, C::COEFF_B);

        let ith_selected = PointRepresentation {
            x: x_var.into(),
            y: y_var.into(),
            point: ith_selected_witness,
        };

        // Update the cumulated sum of selected children
        if i == 0 {
            // In the first iteration, the sum is the first selected child.
            sum_of_selected = ith_selected;
        } else {
            // In the consecutive iterations, add the ith selected child to the accumulated sum
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected)?;
        }
    }

    Ok((sum_of_selected.point, sum_of_selected.x, sum_of_selected.y))
}

pub fn batched_select_and_accumulate_non_root<
    F: PrimeField,
    C: SWCurveConfig<BaseField = F> + Copy,
    Cs: ConstraintSystem<F>,
>(
    cs: &mut Cs,
    num_indices: u32, // The number of parallel selections
    all_children_x_coords: Vec<LinearCombination<F>>,
    selected_children_plus_delta: Option<&[Affine<C>]>,
) -> Result<(
    Option<Affine<C>>,
    LinearCombination<F>,
    LinearCombination<F>,
)> {
    // Initialize the accumulated sum of the selected children to dummy values.
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        point: None,
    };

    let chunk_size = all_children_x_coords.len() / (num_indices as usize);
    let chunks: Vec<_> = all_children_x_coords.chunks_exact(chunk_size).collect();

    for (i, chunk) in chunks.iter().enumerate() {
        let ith_selected_witness = selected_children_plus_delta.map(|xy| xy[i]);
        let x_var = cs.allocate(ith_selected_witness.map(|xy| xy.x)).unwrap();
        let y_var = cs.allocate(ith_selected_witness.map(|xy| xy.y)).unwrap();

        // Select from public set
        select(cs, x_var.into(), chunk.iter().cloned())?;

        // Curve check
        curve_check(cs, x_var.into(), y_var.into(), C::COEFF_A, C::COEFF_B);

        let ith_selected = PointRepresentation {
            x: x_var.into(),
            y: y_var.into(),
            point: ith_selected_witness,
        };

        // Update the cumulated sum of selected children
        if i == 0 {
            // In the first iteration, the sum is the first selected child.
            sum_of_selected = ith_selected;
        } else {
            // In the consecutive iterations, add the ith selected child to the accumulated sum
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected)?;
        }
    }

    Ok((sum_of_selected.point, sum_of_selected.x, sum_of_selected.y))
}
