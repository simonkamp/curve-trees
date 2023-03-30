extern crate bulletproofs;
extern crate relations;

use ark_ff::PrimeField;
use bulletproofs::r1cs::*;

use rand::thread_rng;
use relations::curve_tree::*;

use ark_ec::{
    short_weierstrass::{Affine, SWCurveConfig},
    CurveGroup,
};
use ark_std::UniformRand;
use merlin::Transcript;

type PallasParameters = ark_pallas::PallasConfig;
type VestaParameters = ark_vesta::VestaConfig;
type PallasP = ark_pallas::Projective;

use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_vesta::VestaConfig;

use ark_secp256k1::{Config as SecpConfig, Fq as SecpBase};
use ark_secq256k1::Config as SecqConfig;

#[test]
pub fn test_curve_tree_even_depth() {
    test_curve_tree_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(4, 11);
    test_curve_tree_with_parameters::<32, SecpBase, SecpConfig, SecqConfig>(4, 11);
}

#[test]
pub fn test_curve_tree_odd_depth() {
    test_curve_tree_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(3, 11);
    test_curve_tree_with_parameters::<32, SecpBase, SecpConfig, SecqConfig>(3, 11);
}

pub fn test_curve_tree_with_parameters<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params =
        SelRerandParameters::<P0, P1>::new(generators_length, generators_length, &mut rng);

    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let some_point = Affine::<P0>::rand(&mut rng);
    let (permissible_point, _) = sr_params
        .even_parameters
        .uh
        .permissible_commitment(&some_point, &sr_params.even_parameters.pc_gens.B_blinding);
    let set = vec![permissible_point];
    let curve_tree = CurveTree::<L, P0, P1>::from_set(&set, &sr_params, Some(depth));
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
    let mut pallas_prover: Prover<_, Affine<PallasParameters>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<VestaParameters>> =
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
