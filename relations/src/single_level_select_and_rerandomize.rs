use bulletproofs::r1cs::*;

use crate::curve::{checked_curve_addition_helper, curve_check, PointRepresentation};
use crate::error::Error;
use crate::rerandomize::*;
use crate::select::*;

use crate::parameters::SingleLayerProofParameters;
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_std::vec::Vec;
use core::marker::PhantomData;
use dock_crypto_utils::transcript::Transcript;

/// Circuit for the single level select and rerandomize relation.
pub fn single_level_select_and_rerandomize<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerProofParameters<C2>,
    rerandomized_child: &Affine<C2>, // The public rerandomization of the selected child without Delta
    all_children_plus_delta: Vec<LinearCombination<Fs>>, // Variables representing members of the (parent) vector commitment
    child_plus_delta: Option<Affine<C2>>,                // Witness of the selected child plus Delta
    child_rerandomization_scalar: Option<Fb>, // The scalar used for randomizing, i.e. child + Delta + child_rerandomization_scalar * H = rerandomized_child + Delta
) -> Result<(), Error> {
    // Add the re-randomised child to the transcript
    cs.transcript()
        .append(b"rerandomized_child", &rerandomized_child);

    // Show that child is part of `all_children` by showing that the child's x-coordinate is present in x-coordinates of the all children
    let x_var = cs.allocate(child_plus_delta.map(|xy| xy.x)).unwrap();
    let x_lc: LinearCombination<_> = x_var.into();
    select(cs, x_lc.clone(), all_children_plus_delta.iter().cloned())?;

    validate_point_and_re_randomize(
        cs,
        parameters,
        rerandomized_child,
        x_lc,
        child_plus_delta,
        child_rerandomization_scalar,
    )
}

/// Circuit for the root level node's select and rerandomize relation.
/// Similar to single_level_select_and_rerandomize but uses select_public_set instead of select since root's children are public.
pub fn root_level_select_and_rerandomize<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerProofParameters<C2>,
    rerandomized_child: &Affine<C2>, // The public rerandomization of the selected child without Delta
    all_children_plus_delta: &[Fs],  // Public set of x-coordinates of all children plus delta
    child_plus_delta: Option<Affine<C2>>, // Witness of the selected child plus Delta
    child_rerandomization_scalar: Option<Fb>, // The scalar used for randomizing, i.e. child + Delta + child_rerandomization_scalar * H = rerandomized_child + Delta
) -> Result<(), Error> {
    // Add the re-randomised child to the transcript
    cs.transcript()
        .append(b"rerandomized_child", &rerandomized_child);

    // Show that child is part of `all_children` by showing that the child's x-coordinate is present in x-coordinates of the all children
    let x_var = cs.allocate(child_plus_delta.map(|xy| xy.x)).unwrap();
    let x_lc: LinearCombination<_> = x_var.into();
    select_public_set(cs, x_lc.clone(), all_children_plus_delta)?;

    validate_point_and_re_randomize(
        cs,
        parameters,
        rerandomized_child,
        x_lc,
        child_plus_delta,
        child_rerandomization_scalar,
    )
}

/// Helper function to validate a point on the curve and prove rerandomization.
/// This function performs curve validation and rerandomization proof for a given point.
pub fn validate_point_and_re_randomize<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs,
    parameters: &SingleLayerProofParameters<C2>,
    rerandomized_child: &Affine<C2>,
    x_lc: LinearCombination<Fs>,
    child_plus_delta: Option<Affine<C2>>,
    child_rerandomization_scalar: Option<Fb>,
) -> Result<(), Error> {
    // Proof that the opened x coordinate with the witnessed y is a point on the curve
    // Note that empty branches are encoded as 0 which works because x=0 does not satisfy the curve equation for any of the curves used.
    let y_var = cs.allocate(child_plus_delta.map(|xy| xy.y)).unwrap();
    let y_lc: LinearCombination<_> = y_var.into();
    // TODO: Reconsider if this is needed since the x-coordinate has already been selected from the set of siblings.
    curve_check(cs, x_lc.clone(), y_lc.clone(), C2::COEFF_A, C2::COEFF_B);

    // Show that `rerandomized_child` is a rerandomization of the selected child
    let rerandomized_child_plus_delta =
        (*rerandomized_child + parameters.sl_params.delta).into_affine();
    re_randomize(
        cs,
        &parameters.tables,
        PointRepresentation {
            x: x_lc,
            y: y_lc,
            point: child_plus_delta,
        },
        constant(rerandomized_child_plus_delta.x),
        constant(rerandomized_child_plus_delta.y),
        child_rerandomization_scalar,
    )?;

    Ok(())
}

/// Circuit for the single level version of the batched select and rerandomize relation.
/// Facilitates showing M instances of the select and rerandomize relation with only a single rerandomization.
pub fn single_level_batched_select_and_rerandomize<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerProofParameters<C2>,
    num_indices: u32,                         // The number of parallel selections
    sum_of_rerandomized: &Affine<C2>, // The public rerandomization of the sum of selected children
    all_children: Vec<LinearCombination<Fs>>, // Variables representing members of the combined and rerandomized parent vector commitment (i.e. the rerandomized sum of num_indices parents)
    selected_children_plus_delta: Option<&[Affine<C2>]>, // Witnesses of the commitments being selected and rerandomized
    child_rerandomization_scalar: Option<Fb>, // The scalar used for randomizing, i.e. \sum selected_witnesses + child_rerandomization_scalar * H = sum_of_rerandomized + num_indices * Delta
) -> Result<(), Error> {
    single_level_batched_select_and_rerandomize_inner(
        cs,
        parameters,
        num_indices,
        sum_of_rerandomized,
        all_children,
        selected_children_plus_delta,
        child_rerandomization_scalar,
        |cs, x, chunk| select(cs, x, chunk.iter().cloned()),
    )
}

pub fn root_level_batched_select_and_rerandomize<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerProofParameters<C2>,
    num_indices: u32,                 // The number of parallel selections
    sum_of_rerandomized: &Affine<C2>, // The public rerandomization of the sum of selected children
    all_children: Vec<Fs>,            // x-coordinates of all children of root, combined.
    selected_children_plus_delta: Option<&[Affine<C2>]>, // Witnesses of the commitments being selected and rerandomized
    child_rerandomization_scalar: Option<Fb>, // The scalar used for randomizing, i.e. \sum selected_witnesses + child_rerandomization_scalar * H = sum_of_rerandomized + num_indices * Delta
) -> Result<(), Error> {
    single_level_batched_select_and_rerandomize_inner(
        cs,
        parameters,
        num_indices,
        sum_of_rerandomized,
        all_children,
        selected_children_plus_delta,
        child_rerandomization_scalar,
        |cs, x, chunk| select_public_set(cs, x, chunk),
    )
}

fn single_level_batched_select_and_rerandomize_inner<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
    C,
    F,
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerProofParameters<C2>,
    num_indices: u32,                 // The number of parallel selections
    sum_of_rerandomized: &Affine<C2>, // The public rerandomization of the sum of selected children
    all_children: Vec<C>,
    selected_children_plus_delta: Option<&[Affine<C2>]>, // Witnesses of the commitments being selected and rerandomized
    child_rerandomization_scalar: Option<Fb>, // The scalar used for randomizing, i.e. \sum selected_witnesses + child_rerandomization_scalar * H = sum_of_rerandomized + num_indices * Delta
    select_fn: F,
) -> Result<(), Error>
where
    F: Fn(&mut Cs, LinearCombination<Fs>, &[C]) -> Result<(), Error>,
{
    // Initialize the accumulated sum of the selected children to dummy values.
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        point: None,
    };
    // Split the variables of the vector commitments into chunks corresponding to the M parents.
    let chunks = all_children.chunks_exact(all_children.len() / num_indices as usize);
    for (i, chunk) in chunks.enumerate() {
        let ith_selected_witness = selected_children_plus_delta.map(|xy| xy[i]);
        let x_var = cs.allocate(ith_selected_witness.map(|xy| xy.x))?;
        let y_var = cs.allocate(ith_selected_witness.map(|xy| xy.y))?;
        let ith_selected = PointRepresentation {
            x: x_var.into(),
            y: y_var.into(),
            point: ith_selected_witness,
        };
        // Show that the parent is committed to the ith child's x-coordinate
        select_fn(cs, x_var.into(), chunk)?;

        // Proof that the opened x coordinate with the witnessed y is a point on the curve
        // Note that empty branches are encoded as 0 which works because x=0 does not satisfy the curve equation for any of the curves used.
        curve_check(cs, x_var.into(), y_var.into(), C2::COEFF_A, C2::COEFF_B);

        // Update the cumulated sum of selected children
        if i == 0 {
            // In the first iteration, the sum is the first selected child.
            sum_of_selected = ith_selected;
        } else {
            // In the consecutive iterations, add the ith selected child to the accumulated sum
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected)?;
        }
    }
    // Add num_indices*Delta to the public sum of the children
    let shifted_rerandomized = (*sum_of_rerandomized
        + (parameters.sl_params.delta * C2::ScalarField::from(num_indices)))
    .into_affine();
    // Show that `rerandomized`, is a rerandomization of sum of the selected children
    re_randomize(
        cs,
        &parameters.tables,
        sum_of_selected,
        constant(shifted_rerandomized.x),
        constant(shifted_rerandomized.y),
        child_rerandomization_scalar,
    )?;

    Ok(())
}

pub fn single_level_batched_validate_and_rerandomize_root_children<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerProofParameters<C2>,
    num_indices: u32,                 // The number of parallel selections
    sum_of_rerandomized: &Affine<C2>, // The public rerandomization of the sum of selected children
    selected_children_plus_delta: Option<&[Affine<C2>]>, // Witnesses of the commitments being selected and rerandomized
    selected_children_x_coords: Vec<LinearCombination<Fs>>,
    child_rerandomization_scalar: Option<Fb>, // The scalar used for randomizing, i.e. \sum selected_witnesses + child_rerandomization_scalar * H = sum_of_rerandomized + num_indices * Delta
) -> Result<(), Error> {
    // Initialize the accumulated sum of the selected children to dummy values.
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        point: None,
    };
    assert_eq!(num_indices as usize, selected_children_x_coords.len());
    for (i, x_var) in selected_children_x_coords.into_iter().enumerate() {
        let ith_selected_witness = selected_children_plus_delta.map(|xy| xy[i]);
        let y_var: LinearCombination<_> = cs.allocate(ith_selected_witness.map(|xy| xy.y))?.into();
        let ith_selected = PointRepresentation {
            x: x_var.clone(),
            y: y_var.clone(),
            point: ith_selected_witness,
        };

        // Proof that the opened x coordinate with the witnessed y is a point on the curve
        // Note that empty branches are encoded as 0 which works because x=0 does not satisfy the curve equation for any of the curves used.
        curve_check(cs, x_var.clone(), y_var.clone(), C2::COEFF_A, C2::COEFF_B);

        // Update the cumulated sum of selected children
        if i == 0 {
            // In the first iteration, the sum is the first selected child.
            sum_of_selected = ith_selected;
        } else {
            // In the consecutive iterations, add the ith selected child to the accumulated sum
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected)?;
        }
    }

    // Add num_indices*Delta to the public sum of the children
    let shifted_rerandomized = (*sum_of_rerandomized
        + (parameters.sl_params.delta * C2::ScalarField::from(num_indices)))
    .into_affine();
    // Show that `rerandomized`, is a rerandomization of sum of the selected children
    re_randomize(
        cs,
        &parameters.tables,
        sum_of_selected,
        constant(shifted_rerandomized.x),
        constant(shifted_rerandomized.y),
        child_rerandomization_scalar,
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::parameters::{SelRerandParameters, SelRerandProofParameters, SingleLayerParameters};
    use ark_pallas::PallasConfig;
    use core::iter;

    use super::*;

    use ark_std::UniformRand;
    use ark_vesta::VestaConfig;
    use dock_crypto_utils::transcript::MerlinTranscript;

    fn test_single_level_inner<
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    >(
        sr_params: &SelRerandParameters<P0, P1>,
    ) where
        Affine<P0>: UniformRand,
        P0::ScalarField: UniformRand,
        P1::ScalarField: UniformRand,
    {
        let mut rng = rand::thread_rng();
        // Test of selecting and rerandomizing a dummy commitment `child'
        let child = Affine::<P0>::rand(&mut rng);

        // Parent is a commitment to the x coordinate of the children where Delta is added to each child.
        let child_plus_delta = (child + sr_params.even_parameters.delta).into_affine();
        let child_plus_delta_x = child_plus_delta.x;
        let xs = vec![child_plus_delta_x];
        let blinding = P1::ScalarField::rand(&mut rng);
        let parent = sr_params.odd_parameters.commit(xs.as_slice(), blinding, 0);

        // Rerandomize the child
        let rerandomization = P0::ScalarField::rand(&mut rng);
        let rerandomized_child =
            child + (sr_params.even_parameters.pc_gens.B_blinding * rerandomization);

        let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

        let proof = {
            let mut transcript = MerlinTranscript::new(b"single_level_select_and_rerandomize");
            let mut prover: Prover<_, Affine<P1>> =
                Prover::new(&sr_params.odd_parameters.pc_gens, &mut transcript);

            let (xs_comm, xs_vars) =
                prover.commit_vec(xs.as_slice(), blinding, &sr_params.odd_parameters.bp_gens);
            assert_eq!(xs_comm, parent);

            single_level_select_and_rerandomize(
                &mut prover,
                &sr_proof_params.even_parameters,
                &rerandomized_child.into_affine(),
                xs_vars.into_iter().map(|x| x.into()).collect(),
                Some(child_plus_delta),
                Some(rerandomization),
            )
            .unwrap();
            let proof = prover.prove(&sr_params.odd_parameters.bp_gens).unwrap();
            proof
        };

        let mut transcript = MerlinTranscript::new(b"single_level_select_and_rerandomize");
        let mut verifier = Verifier::<_, Affine<P1>>::new(&mut transcript);
        let xs_vars = verifier.commit_vec(1, parent);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_proof_params.even_parameters,
            &rerandomized_child.into_affine(),
            xs_vars.into_iter().map(|x| x.into()).collect(),
            None,
            None,
        )
        .unwrap();

        verifier
            .verify(
                &proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            )
            .unwrap();
    }

    #[test]
    fn test_single_level() {
        let generators_length = 1 << 12;

        // Test with parameters created using new()
        let sr_params_new = SelRerandParameters::<PallasConfig, VestaConfig>::new(
            generators_length,
            generators_length,
        )
        .expect("Failed to create SelRerandParameters");
        test_single_level_inner(&sr_params_new);

        // Test with parameters created using new_using_label()
        let sr_params_label = SelRerandParameters {
            even_parameters: SingleLayerParameters::<PallasConfig>::new_using_label(
                b"test_single_level_even",
                generators_length,
            )
            .expect("Failed to create even parameters"),
            odd_parameters: SingleLayerParameters::<VestaConfig>::new_using_label(
                b"test_single_level_odd",
                generators_length,
            )
            .expect("Failed to create odd parameters"),
        };
        test_single_level_inner(&sr_params_label);

        // Test with reversed curves using new_using_label()
        let sr_params_label_reversed = SelRerandParameters {
            even_parameters: SingleLayerParameters::<VestaConfig>::new_using_label(
                b"test_single_level_even_rev",
                generators_length,
            )
            .expect("Failed to create even parameters"),
            odd_parameters: SingleLayerParameters::<PallasConfig>::new_using_label(
                b"test_single_level_odd_rev",
                generators_length,
            )
            .expect("Failed to create odd parameters"),
        };
        test_single_level_inner(&sr_params_label_reversed);
    }

    fn test_single_level_batched_inner<
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    >(
        sr_params: &SelRerandParameters<P0, P1>,
    ) where
        Affine<P0>: UniformRand,
        P0::ScalarField: UniformRand,
        P1::ScalarField: UniformRand,
    {
        let mut rng = rand::thread_rng();
        const M: usize = 2;
        let arity = 32;
        let children: Vec<_> = iter::from_fn(|| Some(Affine::<P0>::rand(&mut rng)))
            .take(M * arity)
            .collect();
        // Pick M children
        let child_index_1 = 3;
        let child_index_2 = arity + 7;
        assert_ne!(children[child_index_1], children[child_index_2]);

        let children_plus_delta: Vec<_> = children
            .iter()
            .map(|child| (*child + sr_params.even_parameters.delta).into_affine())
            .collect();
        let xs: Vec<_> = children_plus_delta
            .iter()
            .map(|child_plus_delta| child_plus_delta.x)
            .collect();
        let blinding = P1::ScalarField::rand(&mut rng);
        let parent = sr_params.odd_parameters.commit(xs.as_slice(), blinding, 0);

        // Rerandomize the selected children
        let rerandomization_1 = P0::ScalarField::rand(&mut rng);
        let rerandomized_child_1 = (children[child_index_1]
            + (sr_params.even_parameters.pc_gens.B_blinding * rerandomization_1))
            .into_affine();

        let rerandomization_2 = P0::ScalarField::rand(&mut rng);
        let rerandomized_child_2 = (children[child_index_2]
            + (sr_params.even_parameters.pc_gens.B_blinding * rerandomization_2))
            .into_affine();

        let rerandomized_sum = (rerandomized_child_1 + rerandomized_child_2).into_affine();

        let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

        let proof = {
            let mut transcript = MerlinTranscript::new(b"single_level_select_and_rerandomize");
            let mut prover: Prover<_, Affine<P1>> =
                Prover::new(&sr_params.odd_parameters.pc_gens, &mut transcript);

            let (xs_comm, xs_vars) =
                prover.commit_vec(xs.as_slice(), blinding, &sr_params.odd_parameters.bp_gens);
            assert_eq!(xs_comm, parent);

            single_level_batched_select_and_rerandomize(
                &mut prover,
                &sr_proof_params.even_parameters,
                M as u32,
                &rerandomized_sum,
                xs_vars.into_iter().map(|x| x.into()).collect(),
                Some(&[
                    children_plus_delta[child_index_1],
                    children_plus_delta[child_index_2],
                ]),
                Some(rerandomization_1 + rerandomization_2),
            )
            .expect("Failed to run single_level_batched_select_and_rerandomize");
            let proof = prover.prove(&sr_params.odd_parameters.bp_gens).unwrap();
            proof
        };

        let mut transcript = MerlinTranscript::new(b"single_level_select_and_rerandomize");
        let mut verifier = Verifier::<_, Affine<P1>>::new(&mut transcript);
        let xs_vars = verifier.commit_vec(M * arity, parent);
        single_level_batched_select_and_rerandomize(
            &mut verifier,
            &sr_proof_params.even_parameters,
            M as u32,
            &rerandomized_sum,
            xs_vars.into_iter().map(|x| x.into()).collect(),
            None,
            None,
        )
        .expect("Failed to run single_level_batched_select_and_rerandomize");

        verifier
            .verify(
                &proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            )
            .unwrap();
    }

    #[test]
    fn test_single_level_batched() {
        let generators_length = 1 << 12;

        // Test with parameters created using new()
        let sr_params_new = SelRerandParameters::<PallasConfig, VestaConfig>::new(
            generators_length,
            generators_length,
        )
        .expect("Failed to create SelRerandParameters");
        test_single_level_batched_inner(&sr_params_new);

        // Test with parameters created using new_using_label()
        let sr_params_label = SelRerandParameters {
            even_parameters: SingleLayerParameters::<PallasConfig>::new_using_label(
                b"test_batched_even",
                generators_length,
            )
            .expect("Failed to create even parameters"),
            odd_parameters: SingleLayerParameters::<VestaConfig>::new_using_label(
                b"test_batched_odd",
                generators_length,
            )
            .expect("Failed to create odd parameters"),
        };
        test_single_level_batched_inner(&sr_params_label);

        // Test with reversed curves using new_using_label()
        let sr_params_label_reversed = SelRerandParameters {
            even_parameters: SingleLayerParameters::<VestaConfig>::new_using_label(
                b"test_batched_even_rev",
                generators_length,
            )
            .expect("Failed to create even parameters"),
            odd_parameters: SingleLayerParameters::<PallasConfig>::new_using_label(
                b"test_batched_odd_rev",
                generators_length,
            )
            .expect("Failed to create odd parameters"),
        };
        test_single_level_batched_inner(&sr_params_label_reversed);
    }
}
