mod common;

use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::{
    curves::{selene::SeleneParams, vesta::VestaParams},
    DivisorCurve,
};
use ark_ff::{PrimeField, Zero};
use ark_helios::{Fq as HeliosBase, Fr as SeleneBase, HeliosConfig};
use ark_pallas::{Fq as PallasBase, Fr as VestaBase, PallasConfig};
use ark_selene::SeleneConfig;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use bulletproofs::r1cs::{Prover, Verifier};
use common::prove;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::prelude::SliceRandom;
use relations::curve_tree::CurveTree;
use relations::error::Error;
use relations::parameters::{
    SelRerandParameters, SelRerandProofParameters, SingleLayerProofParametersNew,
};
use relations::ped_comm_group_elems::{
    prove as prove_new, prove_naive, verify as verify_new, verify_naive,
};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

#[test]
pub fn commitment_naive() {
    check_naive::<2, PallasBase, PallasConfig, VestaConfig>(Some(4), 13, 16, 1, 4);
    check_naive::<8, PallasBase, PallasConfig, VestaConfig>(Some(4), 14, 4096, 1, 8);
    check_naive::<8, PallasBase, PallasConfig, VestaConfig>(Some(4), 14, 4096, 1, 5);
    check_naive::<8, PallasBase, PallasConfig, VestaConfig>(Some(4), 14, 4096, 1, 3);
}

#[test]
pub fn commitment() {
    // Test different combinations of shared_dlog_indices

    let test_cases = vec![
        ("no shared dlog", vec![]),
        ("some indices have shared dlog", vec![1, 2]),
        ("all shared dlog", vec![0, 1, 2, 3]),
    ];

    for (desc, indices) in test_cases {
        let shared_indices: BTreeSet<usize> = indices.into_iter().collect();
        println!("Testing: {desc}");

        check::<2, VestaBase, PallasBase, PallasConfig, VestaConfig, VestaParams>(
            Some(4),
            13,
            16,
            1,
            4,
            shared_indices.clone(),
        );

        check::<2, SeleneBase, HeliosBase, HeliosConfig, SeleneConfig, SeleneParams>(
            Some(4),
            13,
            16,
            1,
            4,
            shared_indices,
        );
    }
}

pub fn check_naive<
    const L: usize,
    F0: PrimeField,
    P0: SWCurveConfig<BaseField = F0> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_proofs: usize,
    nesting_size: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

    let possible_proof_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();
    let mut proof_indices = BTreeMap::new();
    while proof_indices.len() < num_proofs {
        let nested = (0..nesting_size)
            .map(|_| Affine::<P1>::rand(&mut rng))
            .collect::<Vec<_>>();
        let x_coords = nested
            .iter()
            .map(|n| (*n + sr_params.odd_parameters.delta).into_affine().x)
            .collect::<Vec<_>>();
        let comm =
            sr_params
                .even_parameters
                .commit(x_coords.as_slice(), P0::ScalarField::zero(), 0);
        proof_indices.insert(
            possible_proof_indices.choose(&mut rng).unwrap(),
            (nested, comm),
        );
    }

    let mut set = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    for (i, (_, c)) in &proof_indices {
        set[**i] = *c;
    }

    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let root = curve_tree.root_node();

    let mut prover_time = Duration::default();
    let mut verifier_time = Duration::default();

    let mut proof_size_printed = false;

    for (leaf_index, (nested, comm)) in proof_indices {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let clock = Instant::now();
        let path = curve_tree
            .get_path_to_leaf_for_proof(*leaf_index, 0)
            .unwrap();
        let (path_commitments, re_randomization_of_leaf) = path
            .select_and_rerandomize_prover_gadget(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut rng,
            )
            .unwrap();

        let blindings_for_points = (0..nested.len())
            .map(|_| <P1::ScalarField>::rand(&mut rng))
            .collect::<Vec<_>>();
        let re_randomized_nested = prove_naive(
            &mut pallas_prover,
            nested,
            &path_commitments.get_rerandomized_leaf(),
            re_randomization_of_leaf,
            blindings_for_points,
            &sr_proof_params.odd_parameters,
        )
        .expect("Failed to prove naive");

        let nc1 = pallas_prover.constraints.len();
        let nc2 = vesta_prover.constraints.len();
        let (pallas_proof, vesta_proof) = prove(
            pallas_prover,
            vesta_prover,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng,
        )
        .unwrap();

        prover_time += clock.elapsed();

        assert_eq!(
            path_commitments.get_rerandomized_leaf(),
            comm + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
                .into_affine()
        );

        if !proof_size_printed {
            println!(
                "Proof size: {}, constraints ({nc1}, {nc2})",
                path_commitments.compressed_size()
                    + re_randomized_nested.compressed_size()
                    + pallas_proof.compressed_size()
                    + vesta_proof.compressed_size()
            );
            proof_size_printed = true;
        }

        {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let clock = Instant::now();

            path_commitments
                .select_and_rerandomize_verifier_gadget(
                    &root,
                    &mut pallas_verifier,
                    &mut vesta_verifier,
                    &sr_proof_params,
                )
                .unwrap();
            let rerandomized_leaf = path_commitments.get_rerandomized_leaf();

            verify_naive(
                &mut pallas_verifier,
                rerandomized_leaf,
                re_randomized_nested,
                &sr_proof_params.odd_parameters,
            )
            .expect("Failed to verify naive");

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
            verifier_time += clock.elapsed();

            assert!(vesta_res.is_ok());
            assert!(pallas_res.is_ok());
            assert_eq!(
                rerandomized_leaf.into_group(),
                curve_tree.get_leaf(*leaf_index).unwrap().into_group()
                    + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
            )
        }
    }

    println!("For tree with {num_leaves} leaves, nesting size {nesting_size}, {num_proofs} proofs took {:?} prover time and {:?} verifier time", prover_time, verifier_time);
}

pub fn check<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
    P1: DivisorCurve<BaseField = F0, ScalarField = F1> + Copy + Send + Sync,
    Params: DiscreteLogParameters,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_proofs: usize,
    nesting_size: usize,
    shared_dlog_indices: BTreeSet<usize>,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

    let odd_proof_params = SingleLayerProofParametersNew::<P1, Params>::from_single_layer_params(
        sr_params.odd_parameters.clone(),
    );

    let possible_proof_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();
    let mut proof_indices = BTreeMap::new();
    while proof_indices.len() < num_proofs {
        let nested = (0..nesting_size)
            .map(|_| Affine::<P1>::rand(&mut rng))
            .collect::<Vec<_>>();
        let x_coords = nested
            .iter()
            .map(|n| (*n + sr_params.odd_parameters.delta).into_affine().x)
            .collect::<Vec<_>>();
        let comm =
            sr_params
                .even_parameters
                .commit(x_coords.as_slice(), P0::ScalarField::zero(), 0);
        proof_indices.insert(
            possible_proof_indices.choose(&mut rng).unwrap(),
            (nested, comm),
        );
    }

    let mut set = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    for (i, (_, c)) in &proof_indices {
        set[**i] = *c;
    }

    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let root = curve_tree.root_node();

    let mut prover_time = Duration::default();
    let mut verifier_time = Duration::default();

    let mut proof_size_printed = false;

    for (leaf_index, (nested, comm)) in proof_indices {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let clock = Instant::now();
        let (path_commitments, re_randomization_of_leaf) = curve_tree
            .select_and_rerandomize_prover_gadget(
                *leaf_index,
                0,
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut rng,
            )
            .unwrap();

        assert_eq!(
            path_commitments.get_rerandomized_leaf(),
            comm + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
                .into_affine()
        );

        let blindings_for_points = (0..nested.len())
            .map(|_| <P1::ScalarField>::rand(&mut rng))
            .collect::<Vec<_>>();
        let (re_randomized_nested, comms) = prove_new::<_, _, _, P0, P1, Params>(
            &mut rng,
            &mut pallas_prover,
            nested.clone(),
            &path_commitments.get_rerandomized_leaf(),
            re_randomization_of_leaf,
            blindings_for_points.clone(),
            &odd_proof_params,
            &sr_params.even_parameters.bp_gens,
            shared_dlog_indices.clone(),
        )
        .expect("Failed to prove");

        let nc1 = pallas_prover.constraints.len();
        let nc2 = vesta_prover.constraints.len();
        let (pallas_proof, vesta_proof) = prove(
            pallas_prover,
            vesta_prover,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng,
        )
        .unwrap();

        prover_time += clock.elapsed();

        for i in 0..nesting_size {
            assert_eq!(
                re_randomized_nested.re_randomized_points[i].into_group(),
                nested[i]
                    + (odd_proof_params.sl_params.pc_gens.B_blinding * blindings_for_points[i])
            );
            if shared_dlog_indices.contains(&i) {
                assert_eq!(
                    re_randomized_nested.blindings_with_different_gen[&i].into_group(),
                    odd_proof_params.sl_params.pc_gens.B * blindings_for_points[i]
                );
            }
        }

        if !proof_size_printed {
            println!(
                "Proof size: {}, constraints ({nc1}, {nc2})",
                path_commitments.compressed_size()
                    + re_randomized_nested.compressed_size()
                    + comms.compressed_size()
                    + pallas_proof.compressed_size()
                    + vesta_proof.compressed_size()
            );
            proof_size_printed = true;
        }

        {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let clock = Instant::now();

            path_commitments
                .select_and_rerandomize_verifier_gadget(
                    &root,
                    &mut pallas_verifier,
                    &mut vesta_verifier,
                    &sr_proof_params,
                )
                .unwrap();
            let rerandomized_leaf = path_commitments.get_rerandomized_leaf();

            verify_new::<_, _, P0, P1, Params>(
                &mut pallas_verifier,
                rerandomized_leaf,
                re_randomized_nested,
                comms,
                &odd_proof_params,
                shared_dlog_indices.clone(),
            )
            .expect("Failed to verify");

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
            verifier_time += clock.elapsed();

            assert!(vesta_res.is_ok());
            assert!(pallas_res.is_ok());
            assert_eq!(
                rerandomized_leaf.into_group(),
                curve_tree.get_leaf(*leaf_index).unwrap().into_group()
                    + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
            )
        }
    }

    println!("For tree with {num_leaves} leaves, nesting size {nesting_size}, {num_proofs} proofs took {:?} prover time and {:?} verifier time", prover_time, verifier_time);
}

#[test]
pub fn verify_rejects_re_randomized_point_at_infinity() {
    // Verifier must reject when a malicious prover supplies `re_randomized_points[i] = -delta`,
    // which makes `re_randomized_plus_delta[i]` the point at infinity.

    let mut rng = rand::thread_rng();
    let generators_length = 1 << 13;
    let nesting_size = 2;

    let sr_params =
        SelRerandParameters::<PallasConfig, VestaConfig>::new(generators_length, generators_length)
            .expect("Failed to create SelRerandParameters");

    let odd_proof_params =
        SingleLayerProofParametersNew::<VestaConfig, VestaParams>::from_single_layer_params(
            sr_params.odd_parameters.clone(),
        );

    let nested: Vec<Affine<VestaConfig>> = (0..nesting_size)
        .map(|_| Affine::<VestaConfig>::rand(&mut rng))
        .collect();

    let x_coords: Vec<_> = nested
        .iter()
        .map(|n| (*n + sr_params.odd_parameters.delta).into_affine().x)
        .collect();
    let re_randomized_comm =
        sr_params
            .even_parameters
            .commit(x_coords.as_slice(), VestaBase::zero(), 0);

    let pallas_transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
    let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let blinding_of_comm = VestaBase::rand(&mut rng);
    let blindings_for_points: Vec<PallasBase> = (0..nesting_size)
        .map(|_| PallasBase::rand(&mut rng))
        .collect();

    let shared_dlog_indices: BTreeSet<usize> = BTreeSet::new();

    let (mut re_randomized_nested, comms) =
        prove_new::<_, _, _, PallasConfig, VestaConfig, VestaParams>(
            &mut rng,
            &mut pallas_prover,
            nested.clone(),
            &re_randomized_comm,
            blinding_of_comm,
            blindings_for_points.clone(),
            &odd_proof_params,
            &sr_params.even_parameters.bp_gens,
            shared_dlog_indices.clone(),
        )
        .expect("Failed to prove");

    // re_randomized_points[0] = -delta so that re_randomized_plus_delta[0] = O (infinity)
    let delta = odd_proof_params.sl_params.delta;
    re_randomized_nested.re_randomized_points[0] = (-delta.into_group()).into_affine();

    let pallas_transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
    let mut pallas_verifier = Verifier::new(pallas_transcript);

    let result = verify_new::<_, _, PallasConfig, VestaConfig, VestaParams>(
        &mut pallas_verifier,
        re_randomized_comm,
        re_randomized_nested,
        comms,
        &odd_proof_params,
        shared_dlog_indices,
    );

    assert!(
        matches!(result, Err(Error::PointCantBeZero)),
        "expected PointCantBeZero, got: {result:?}",
    );
}
