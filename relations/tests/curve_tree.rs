extern crate bulletproofs;
extern crate pasta;
extern crate relations;

use bulletproofs::r1cs::*;

use rand::thread_rng;
use relations::curve_tree::*;

use ark_ec::{models::short_weierstrass_jacobian::GroupAffine, ProjectiveCurve};
use ark_std::UniformRand;
use merlin::Transcript;

type PallasParameters = pasta::pallas::PallasParameters;
type VestaParameters = pasta::vesta::VestaParameters;
type PallasP = pasta::pallas::Projective;

#[test]
pub fn test_curve_tree_even_depth() {
    test_curve_tree_with_parameters::<32>(4, 11);
}

#[test]
pub fn test_curve_tree_odd_depth() {
    test_curve_tree_with_parameters::<32>(3, 11);
}

pub fn test_curve_tree_with_parameters<const L: usize>(
    depth: usize,
    generators_length_log_2: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
        generators_length,
        generators_length,
        &mut rng,
    );

    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, GroupAffine<PallasParameters>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, GroupAffine<VestaParameters>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let some_point = PallasP::rand(&mut rng).into_affine();
    let (permissible_point, _) = sr_params
        .even_parameters
        .uh
        .permissible_commitment(&some_point, &sr_params.even_parameters.pc_gens.B_blinding);
    let set = vec![permissible_point];
    let curve_tree =
        CurveTree::<L, PallasParameters, VestaParameters>::from_set(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let (path_commitments, _) = curve_tree.select_and_rerandomize_prover_gadget(
        0,
        &mut pallas_prover,
        &mut vesta_prover,
        &sr_params,
        &mut rng,
    );

    let pallas_proof = pallas_prover
        .prove(&sr_params.even_parameters.bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_params.odd_parameters.bp_gens)
        .unwrap();

    {
        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let _rerandomized_leaf = curve_tree.select_and_rerandomize_verifier_gadget(
            &mut pallas_verifier,
            &mut vesta_verifier,
            path_commitments,
            &sr_params,
        );
        let vesta_res = vesta_verifier.verify(
            &vesta_proof,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
        );
        let pallas_res = pallas_verifier.verify(
            &pallas_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
        );
        assert_eq!(vesta_res, pallas_res);
        assert_eq!(vesta_res, Ok(()));
    }
}

#[test]
pub fn test_curve_tree_batch_verification() {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << 12;

    let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
        generators_length,
        generators_length,
        &mut rng,
    );

    let some_point = PallasP::rand(&mut rng).into_affine();
    let (permissible_point, _) = sr_params
        .even_parameters
        .uh
        .permissible_commitment(&some_point, &sr_params.even_parameters.pc_gens.B_blinding);
    let set = vec![permissible_point];
    let curve_tree =
        CurveTree::<32, PallasParameters, VestaParameters>::from_set(&set, &sr_params, Some(4));
    assert_eq!(curve_tree.height(), 4);

    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, GroupAffine<PallasParameters>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, GroupAffine<VestaParameters>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let (path_commitments, _) = curve_tree.select_and_rerandomize_prover_gadget(
        0,
        &mut pallas_prover,
        &mut vesta_prover,
        &sr_params,
        &mut thread_rng(),
    );

    let pallas_proof = pallas_prover
        .prove(&sr_params.even_parameters.bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_params.odd_parameters.bp_gens)
        .unwrap();

    let (pvt1, vvt1) = {
        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let _rerandomized_leaf = curve_tree.select_and_rerandomize_verifier_gadget(
            &mut pallas_verifier,
            &mut vesta_verifier,
            path_commitments.clone(),
            &sr_params,
        );
        let vesta_verification_tuples = vesta_verifier
            .verification_scalars_and_points(&vesta_proof)
            .unwrap();
        let pallas_verification_tuples = pallas_verifier
            .verification_scalars_and_points(&pallas_proof)
            .unwrap();
        (pallas_verification_tuples, vesta_verification_tuples)
    };
    let (pvt2, vvt2) = {
        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let _rerandomized_leaf = curve_tree.select_and_rerandomize_verifier_gadget(
            &mut pallas_verifier,
            &mut vesta_verifier,
            path_commitments,
            &sr_params,
        );
        let vesta_verification_tuples = vesta_verifier
            .verification_scalars_and_points(&vesta_proof)
            .unwrap();
        let pallas_verification_tuples = pallas_verifier
            .verification_scalars_and_points(&pallas_proof)
            .unwrap();
        (pallas_verification_tuples, vesta_verification_tuples)
    };
    let pallas_res = batch_verify(
        vec![pvt1, pvt2],
        &sr_params.even_parameters.pc_gens,
        &sr_params.even_parameters.bp_gens,
    );
    let vesta_res = batch_verify(
        vec![vvt1, vvt2],
        &sr_params.odd_parameters.pc_gens,
        &sr_params.odd_parameters.bp_gens,
    );
    assert_eq!(pallas_res, vesta_res);
    assert_eq!(pallas_res, Ok(()));
}
