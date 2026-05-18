extern crate bulletproofs;
extern crate relations;
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::{
    short_weierstrass::{Affine, SWCurveConfig},
    AffineRepr, CurveGroup,
};
use ark_ec_divisors::{
    curves::{
        helios::HeliosParams, pallas::PallasParams, selene::SeleneParams, vesta::VestaParams,
    },
    DivisorCurve,
};
use ark_ff::PrimeField;
use ark_helios::{Fq as HeliosBase, HeliosConfig};
use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_secp256k1::{Config as SecpConfig, Fq as SecpBase};
use ark_secq256k1::Config as SecqConfig;
use ark_selene::SeleneConfig;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use ark_vesta::{Fq as VestaBase, VestaConfig};
use bulletproofs::r1cs::*;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::prelude::SliceRandom;
use rand::thread_rng;
use relations::curve_tree::*;
use std::collections::BTreeSet;
use std::time::{Duration, Instant};

mod common;
use common::prove;
use relations::curve_tree_prover::CurveTreeWitnessPath;
use relations::error::Error;
use relations::parameters::{
    SelRerandParameters, SelRerandParametersRef, SelRerandProofParameters,
    SelRerandProofParametersNew,
};
use relations::utils::verify;

type PallasParameters = PallasConfig;
type VestaParameters = VestaConfig;
type PallasP = ark_pallas::Projective;

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

#[test]
pub fn test_curve_tree_even_depth_new() {
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        8,
        3,
    );
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        4,
        3,
    );
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        16,
        5,
    );
}

#[test]
pub fn test_curve_tree_even_depth_large() {
    test_curve_tree_with_parameters_new::<256, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        13,
        64,
        15,
    );
    test_curve_tree_with_parameters_new::<256, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        13,
        128,
        15,
    );
    test_curve_tree_with_parameters_new::<256, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        13,
        256,
        15,
    );

    test_curve_tree_with_parameters_new::<256, PallasBase, PallasConfig, VestaConfig>(
        None, 13, 64, 15,
    );
    test_curve_tree_with_parameters_new::<256, PallasBase, PallasConfig, VestaConfig>(
        None, 13, 128, 15,
    );
    test_curve_tree_with_parameters_new::<256, PallasBase, PallasConfig, VestaConfig>(
        None, 13, 256, 15,
    );
}

#[test]
pub fn test_curve_tree_odd_depth_large() {
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(3),
        11,
        64,
        10,
    );
    test_curve_tree_with_parameters_new::<32, SecpBase, SecpConfig, SecqConfig>(
        Some(3),
        11,
        128,
        10,
    );
}

#[test]
pub fn test_curve_tree_small() {
    test_curve_tree_with_parameters_new::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 2, 2);
    test_curve_tree_with_parameters_new::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 4, 2);
    test_curve_tree_with_parameters_new::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 8, 2);
    test_curve_tree_with_parameters_new::<2, PallasBase, PallasConfig, VestaConfig>(
        None, 11, 16, 2,
    );
}

#[test]
pub fn curve_tree_get_update() {
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 2, 2);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 4, 2);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 8, 5);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 12, 16, 10);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 12, 32, 10);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 12, 64, 10);
}

#[test]
pub fn test_curve_tree_using_params_generated_by_hash_to_curve() {
    let generators_length = 1 << 11;

    // Test with Pallas as P0, Vesta as P1
    let sr_params_pallas = SelRerandParameters::<PallasConfig, VestaConfig>::new_using_label(
        b"curve_tree_test_pallas_p0",
        generators_length,
        generators_length,
    )
    .expect("Failed to create SelRerandParameters with Pallas as P0");

    test_curve_tree_inner::<32, PallasBase, PallasConfig, VestaConfig>(&sr_params_pallas, 4);

    // Test with Vesta as P0, Pallas as P1
    let sr_params_vesta = SelRerandParameters::<VestaConfig, PallasConfig>::new_using_label(
        b"curve_tree_test_vesta_p0",
        generators_length,
        generators_length,
    )
    .expect("Failed to create SelRerandParameters with Vesta as P0");

    test_curve_tree_inner::<32, VestaBase, VestaConfig, PallasConfig>(&sr_params_vesta, 4);
}

fn test_curve_tree_inner<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    sr_params: &SelRerandParameters<P0, P1>,
    depth: usize,
) where
    Affine<P0>: UniformRand,
{
    let mut rng = thread_rng();
    let even_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut even_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, even_transcript);

    let odd_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut odd_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, odd_transcript);

    let some_point = Affine::<P0>::rand(&mut rng);
    let set = vec![some_point];
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

    let path = curve_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let (path_commitments, re_randomization_of_leaf) = path
        .select_and_rerandomize_prover_gadget(
            &mut even_prover,
            &mut odd_prover,
            &sr_proof_params,
            &mut rng,
        )
        .unwrap();

    let (pallas_proof, vesta_proof) = prove(
        even_prover,
        odd_prover,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();

    let root = curve_tree.root_node();

    {
        let even_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut even_verifier = Verifier::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut odd_verifier = Verifier::new(odd_transcript);

        path_commitments
            .select_and_rerandomize_verifier_gadget(
                &root,
                &mut even_verifier,
                &mut odd_verifier,
                &sr_proof_params,
            )
            .unwrap();
        let rerandomized_leaf = path_commitments.get_rerandomized_leaf();
        odd_verifier
            .verify(
                &vesta_proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            )
            .unwrap();
        even_verifier
            .verify(
                &pallas_proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            )
            .unwrap();
        assert_eq!(
            rerandomized_leaf.into_group(),
            curve_tree.get_leaf(0).unwrap().into_group()
                + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
        )
    }
}

pub fn test_curve_tree_with_parameters<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
) where
    Affine<P0>: UniformRand,
{
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    test_curve_tree_inner::<L, F, P0, P1>(&sr_params, depth);
}

pub fn test_curve_tree_with_parameters_new<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_proofs: usize,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_proof_params =
        SelRerandProofParameters::<P0, P1>::new(generators_length, generators_length).unwrap();

    let set = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_proof_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let possible_proof_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();
    let mut proof_indices = BTreeSet::new();
    while proof_indices.len() < num_proofs {
        proof_indices.insert(possible_proof_indices.choose(&mut rng).unwrap());
    }

    let root = curve_tree.root_node();

    let mut prover_time = Duration::default();
    let mut verifier_time = Duration::default();

    let mut proof_size_printed = false;

    for leaf_index in proof_indices {
        let clock = Instant::now();

        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> = Prover::new(
            &sr_proof_params.even_parameters().pc_gens,
            pallas_transcript,
        );

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

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

        let nc1 = pallas_prover.constraints.len();
        let nc2 = vesta_prover.constraints.len();
        let (pallas_proof, vesta_proof) = prove(
            pallas_prover,
            vesta_prover,
            &sr_proof_params.even_parameters().bp_gens,
            &sr_proof_params.odd_parameters().bp_gens,
            &mut rng,
        )
        .unwrap();

        prover_time += clock.elapsed();

        if !proof_size_printed {
            println!(
                "Proof size for L={L}, height={}, constraints=({nc1}, {nc2}): {} bytes",
                curve_tree.height(),
                pallas_proof.compressed_size() + vesta_proof.compressed_size()
            );
            proof_size_printed = true;
        }

        {
            let clock = Instant::now();
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            path_commitments
                .select_and_rerandomize_verifier_gadget(
                    &root,
                    &mut pallas_verifier,
                    &mut vesta_verifier,
                    &sr_proof_params,
                )
                .unwrap();
            let rerandomized_leaf = path_commitments.get_rerandomized_leaf();
            verify(
                pallas_verifier,
                vesta_verifier,
                &pallas_proof,
                &vesta_proof,
                &sr_proof_params.even_parameters().pc_gens,
                &sr_proof_params.even_parameters().bp_gens,
                &sr_proof_params.odd_parameters().pc_gens,
                &sr_proof_params.odd_parameters().bp_gens,
                &mut rng,
            )
            .unwrap();
            verifier_time += clock.elapsed();
            assert_eq!(
                rerandomized_leaf.into_group(),
                curve_tree.get_leaf(*leaf_index).unwrap().into_group()
                    + (sr_proof_params.even_parameters().pc_gens.B_blinding
                        * re_randomization_of_leaf)
            )
        }
    }

    println!(
        "For tree with {} leaves, {} proofs took {:?} prover time and {:?} verifier time",
        num_leaves, num_proofs, prover_time, verifier_time
    );
}

pub fn test_curve_tree_get_update<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_updates: usize,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_proof_params =
        SelRerandProofParameters::<P0, P1>::new(generators_length, generators_length).unwrap();

    let leaves = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    let mut curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&leaves, &sr_proof_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let possible_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();

    let mut update_indices = BTreeSet::new();
    while update_indices.len() < num_updates {
        update_indices.insert(possible_indices.choose(&mut rng).unwrap());
    }

    /*// Keep `num_same` number of indices same, meaning their value isn't updated
    let num_same = if num_leaves > num_updates {if (num_leaves - num_updates) > 10 {10} else {num_leaves - num_updates}} else {0};
    let mut same_indices = BTreeSet::new();
    while same_indices.len() < num_same {
        let i = possible_indices.choose(&mut rng).unwrap();
        if !update_indices.contains(i) {
            same_indices.insert(i);
        }
    }*/

    for leaf_index in &possible_indices {
        if !update_indices.contains(leaf_index) {
            let leaf = curve_tree.get_leaf(*leaf_index).unwrap();
            assert_eq!(leaves[*leaf_index], leaf);
        }
    }

    for leaf_index in update_indices.clone() {
        let leaf = curve_tree.get_leaf(*leaf_index).unwrap();
        assert_eq!(leaves[*leaf_index], leaf);
        let new_leaf = Affine::<P0>::rand(&mut rng);
        curve_tree.update_leaf(*leaf_index, 0, new_leaf, &sr_proof_params);
        let leaf = curve_tree.get_leaf(*leaf_index).unwrap();
        assert_eq!(leaf, new_leaf);
    }

    let root = curve_tree.root_node();

    for leaf_index in update_indices.clone() {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> = Prover::new(
            &sr_proof_params.even_parameters().pc_gens,
            pallas_transcript,
        );

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

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

        let (pallas_proof, vesta_proof) = prove(
            pallas_prover,
            vesta_prover,
            &sr_proof_params.even_parameters().bp_gens,
            &sr_proof_params.odd_parameters().bp_gens,
            &mut rng,
        )
        .unwrap();

        {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            path_commitments
                .select_and_rerandomize_verifier_gadget(
                    &root,
                    &mut pallas_verifier,
                    &mut vesta_verifier,
                    &sr_proof_params,
                )
                .unwrap();
            let rerandomized_leaf = path_commitments.get_rerandomized_leaf();
            let vesta_res = vesta_verifier.verify(
                &vesta_proof,
                &sr_proof_params.odd_parameters().pc_gens,
                &sr_proof_params.odd_parameters().bp_gens,
            );
            let pallas_res = pallas_verifier.verify(
                &pallas_proof,
                &sr_proof_params.even_parameters().pc_gens,
                &sr_proof_params.even_parameters().bp_gens,
            );
            assert!(vesta_res.is_ok());
            assert!(pallas_res.is_ok());
            assert_eq!(
                rerandomized_leaf.into_group(),
                curve_tree.get_leaf(*leaf_index).unwrap().into_group()
                    + (sr_proof_params.even_parameters().pc_gens.B_blinding
                        * re_randomization_of_leaf)
            )
        }
    }
}

#[test]
pub fn test_curve_tree_batch_verification() {
    let mut rng = thread_rng();
    let generators_length = 1 << 12;

    let sr_proof_params = SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
        generators_length,
        generators_length,
    )
    .unwrap();

    let batch_size = 5;

    let set = (0..batch_size)
        .map(|_| PallasP::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();
    let curve_tree = CurveTree::<32, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &sr_proof_params,
        Some(4),
    );

    let labels = [
        b"select_and_rerandomize_1",
        b"select_and_rerandomize_2",
        b"select_and_rerandomize_3",
    ];

    println!("Batch size = {batch_size}");

    let mut path_commitments = Vec::with_capacity(batch_size);
    let mut pallas_proofs = Vec::with_capacity(batch_size);
    let mut vesta_proofs = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        // Choosing arbitrary labels
        let label = labels[i % labels.len()];
        let pallas_transcript = MerlinTranscript::new(label);
        let mut pallas_prover: Prover<_, Affine<PallasParameters>> = Prover::new(
            &sr_proof_params.even_parameters().pc_gens,
            pallas_transcript,
        );

        let vesta_transcript = MerlinTranscript::new(label);
        let mut vesta_prover: Prover<_, Affine<VestaParameters>> =
            Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

        let path = curve_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
        let (path_commitment, _) = path
            .select_and_rerandomize_prover_gadget(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut thread_rng(),
            )
            .unwrap();

        let pallas_proof = pallas_prover
            .prove(&sr_proof_params.even_parameters().bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&sr_proof_params.odd_parameters().bp_gens)
            .unwrap();
        path_commitments.push(path_commitment);
        pallas_proofs.push(pallas_proof);
        vesta_proofs.push(vesta_proof);
    }

    let start = Instant::now();
    let mut pallas_vt = Vec::with_capacity(batch_size);
    let mut vesta_vt = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        // Choosing same label as prover
        let label = labels[i % labels.len()];
        let pallas_transcript = MerlinTranscript::new(label);
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(label);
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        path_commitments[i]
            .select_and_rerandomize_verifier_gadget(
                &curve_tree.root_node(),
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();
        let pallas_verification_tuples = pallas_verifier
            .verification_scalars_and_points(&pallas_proofs[i])
            .unwrap();
        let vesta_verification_tuples = vesta_verifier
            .verification_scalars_and_points(&vesta_proofs[i])
            .unwrap();
        pallas_vt.push(pallas_verification_tuples);
        vesta_vt.push(vesta_verification_tuples);
    }

    let pallas_res = batch_verify(
        pallas_vt,
        &sr_proof_params.even_parameters().pc_gens,
        &sr_proof_params.even_parameters().bp_gens,
    );
    let vesta_res = batch_verify(
        vesta_vt,
        &sr_proof_params.odd_parameters().pc_gens,
        &sr_proof_params.odd_parameters().bp_gens,
    );

    assert_eq!(pallas_res, Ok(()));
    assert_eq!(vesta_res, Ok(()));

    println!("Batch verification took {:?}", start.elapsed());

    let start = Instant::now();
    for i in 0..batch_size {
        // Choosing same label as prover
        let label = labels[i % labels.len()];
        let pallas_transcript = MerlinTranscript::new(label);
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(label);
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        path_commitments[i]
            .select_and_rerandomize_verifier_gadget(
                &curve_tree.root_node(),
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();
        let vesta_res = vesta_verifier.verify(
            &vesta_proofs[i],
            &sr_proof_params.odd_parameters().pc_gens,
            &sr_proof_params.odd_parameters().bp_gens,
        );
        let pallas_res = pallas_verifier.verify(
            &pallas_proofs[i],
            &sr_proof_params.even_parameters().pc_gens,
            &sr_proof_params.even_parameters().bp_gens,
        );
        assert_eq!(pallas_res, Ok(()));
        assert_eq!(vesta_res, Ok(()));
    }
    println!("Regular verification took {:?}", start.elapsed());
}

#[test]
pub fn test_combined_vs_common_root_path_proofs() {
    check_combined_vs_common_root_proofs_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(
        4, 12, 2,
    );
    check_combined_vs_common_root_proofs_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(
        4, 13, 3,
    );
    check_combined_vs_common_root_proofs_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(
        4, 13, 4,
    );
    check_combined_vs_common_root_proofs_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(
        3, 13, 2,
    );
    check_combined_vs_common_root_proofs_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(
        3, 13, 3,
    );
    check_combined_vs_common_root_proofs_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(
        3, 13, 4,
    );
}

pub fn check_combined_vs_common_root_proofs_with_parameters<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
    num_paths: usize,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_proof_params =
        SelRerandProofParameters::<P0, P1>::new(generators_length, generators_length).unwrap();

    let mut set = Vec::<Affine<P0>>::new();
    for _ in 0..num_paths {
        set.push(Affine::<P0>::rand(&mut rng));
    }

    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_proof_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    println!("For {num_paths} leaves, width {L}, height {depth}");

    println!("Combined Proof");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> = Prover::new(
        &sr_proof_params.even_parameters().pc_gens,
        pallas_transcript,
    );

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

    let mut path_commitments_list: Vec<SelectAndRerandomizePath<L, P0, P1>> = vec![];
    let mut all_leaf_rerandomizations = vec![];
    for i in 0..num_paths {
        let path = curve_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
        let (path_commitments, rl) = path
            .select_and_rerandomize_prover_gadget(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut rng,
            )
            .unwrap();
        path_commitments_list.push(path_commitments);
        all_leaf_rerandomizations.push(rl);
    }

    let pallas_proof = pallas_prover
        .prove(&sr_proof_params.even_parameters().bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_proof_params.odd_parameters().bp_gens)
        .unwrap();

    let combined_proof_size = path_commitments_list.compressed_size()
        + pallas_proof.compressed_size()
        + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", combined_proof_size);

    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    let mut rerandomized_leaves = vec![];
    for path_commitments in &path_commitments_list {
        path_commitments
            .select_and_rerandomize_verifier_gadget(
                &curve_tree.root_node(),
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();
        rerandomized_leaves.push(path_commitments.get_rerandomized_leaf());
    }

    vesta_verifier
        .verify(
            &vesta_proof,
            &sr_proof_params.odd_parameters().pc_gens,
            &sr_proof_params.odd_parameters().bp_gens,
        )
        .unwrap();
    pallas_verifier
        .verify(
            &pallas_proof,
            &sr_proof_params.even_parameters().pc_gens,
            &sr_proof_params.even_parameters().bp_gens,
        )
        .unwrap();
    println!("Verification time: {:?}", clock.elapsed());

    for i in 0..num_paths {
        assert_eq!(
            rerandomized_leaves[i].into_group(),
            curve_tree.get_leaf(i).unwrap().into_group()
                + (sr_proof_params.even_parameters().pc_gens.B_blinding
                    * all_leaf_rerandomizations[i])
        )
    }

    println!("Common root proofs");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> = Prover::new(
        &sr_proof_params.even_parameters().pc_gens,
        pallas_transcript,
    );

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

    let mut paths = Vec::new();
    for i in 0..num_paths {
        let path = curve_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
        paths.push(path);
    }

    let (all_path_commitments, all_leaf_rerandomizations) =
        CurveTreeWitnessPath::select_and_rerandomize_prover_gadget_for_common_root(
            &paths,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            &mut rng,
        )
        .unwrap();

    let pallas_proof = pallas_prover
        .prove(&sr_proof_params.even_parameters().bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_proof_params.odd_parameters().bp_gens)
        .unwrap();

    let all_paths_proof_size = all_path_commitments.compressed_size()
        + pallas_proof.compressed_size()
        + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", all_paths_proof_size);

    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    SelectAndRerandomizePath::select_and_rerandomize_verifier_gadget_for_common_root(
        &all_path_commitments,
        &mut pallas_verifier,
        &mut vesta_verifier,
        &curve_tree.root_node(),
        &sr_proof_params,
    )
    .unwrap();
    let rerandomized_leaves: Vec<_> = all_path_commitments
        .iter()
        .map(|p| p.get_rerandomized_leaf())
        .collect();

    vesta_verifier
        .verify(
            &vesta_proof,
            &sr_proof_params.odd_parameters().pc_gens,
            &sr_proof_params.odd_parameters().bp_gens,
        )
        .unwrap();
    pallas_verifier
        .verify(
            &pallas_proof,
            &sr_proof_params.even_parameters().pc_gens,
            &sr_proof_params.even_parameters().bp_gens,
        )
        .unwrap();
    println!("Verification time: {:?}", clock.elapsed());

    for i in 0..num_paths {
        assert_eq!(
            rerandomized_leaves[i].into_group(),
            curve_tree.get_leaf(i).unwrap()
                + (sr_proof_params.even_parameters().pc_gens.B_blinding
                    * all_leaf_rerandomizations[i])
        )
    }
}

#[test]
pub fn test_common_root_paths() {
    check_common_root_paths::<8, PallasBase, PallasConfig, VestaConfig>(4, 12, 5);
    check_common_root_paths::<8, PallasBase, PallasConfig, VestaConfig>(3, 13, 5);
}

pub fn check_common_root_paths<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
    num_paths: usize,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let mut set = Vec::<Affine<P0>>::new();
    for _ in 0..num_paths {
        set.push(Affine::<P0>::rand(&mut rng));
    }

    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let leaf_indices: Vec<usize> = (0..num_paths).collect();

    let mut witness_paths = Vec::new();
    for &i in &leaf_indices {
        let path = curve_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
        witness_paths.push(path);
    }

    let witness_paths_with_same_root = curve_tree
        .get_paths_to_leaves_for_proof(&leaf_indices, 0)
        .unwrap();

    println!(
        "For L={L} and {num_paths} paths, size = {} and optimized size = {}",
        witness_paths.compressed_size(),
        witness_paths_with_same_root.compressed_size()
    );

    assert_eq!(witness_paths_with_same_root.num_paths(), num_paths);

    let reconstructed_paths = witness_paths_with_same_root.to_individual_paths();
    assert_eq!(reconstructed_paths.len(), num_paths);

    for (i, (original, reconstructed)) in witness_paths
        .iter()
        .zip(reconstructed_paths.iter())
        .enumerate()
    {
        assert_eq!(
            original.even_internal_nodes.len(),
            reconstructed.even_internal_nodes.len()
        );
        assert_eq!(
            original.odd_internal_nodes.len(),
            reconstructed.odd_internal_nodes.len()
        );

        for (j, (orig_node, recon_node)) in original
            .even_internal_nodes
            .iter()
            .zip(reconstructed.even_internal_nodes.iter())
            .enumerate()
        {
            assert_eq!(
                orig_node.x_coord_children, recon_node.x_coord_children,
                "Path {}, even node {}: x_coord_children mismatch",
                i, j
            );
            assert_eq!(
                orig_node.child_node_to_randomize, recon_node.child_node_to_randomize,
                "Path {}, even node {}: child_node_to_randomize mismatch",
                i, j
            );
        }

        for (j, (orig_node, recon_node)) in original
            .odd_internal_nodes
            .iter()
            .zip(reconstructed.odd_internal_nodes.iter())
            .enumerate()
        {
            assert_eq!(
                orig_node.x_coord_children, recon_node.x_coord_children,
                "Path {}, odd node {}: x_coord_children mismatch",
                i, j
            );
            assert_eq!(
                orig_node.child_node_to_randomize, recon_node.child_node_to_randomize,
                "Path {}, odd node {}: child_node_to_randomize mismatch",
                i, j
            );
        }
    }

    let root_is_even = witness_paths[0].root_is_even();

    for path in &witness_paths[1..] {
        assert_eq!(
            path.even_internal_nodes.len(),
            witness_paths[0].even_internal_nodes.len()
        );
        assert_eq!(
            path.odd_internal_nodes.len(),
            witness_paths[0].odd_internal_nodes.len()
        );
    }

    if root_is_even {
        let root_x_coords = &witness_paths[0].even_internal_nodes[0].x_coord_children;
        for path in &witness_paths[1..] {
            assert_eq!(&path.even_internal_nodes[0].x_coord_children, root_x_coords);
        }
    } else {
        let root_x_coords = &witness_paths[0].odd_internal_nodes[0].x_coord_children;
        for path in &witness_paths[1..] {
            assert_eq!(&path.odd_internal_nodes[0].x_coord_children, root_x_coords);
        }
    }
}

#[test]
pub fn test_curve_tree_odd_depth_divisor() {
    test_curve_tree_with_parameters_newer::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(3), 11, 8, 3);
    test_curve_tree_with_parameters_newer::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(3), 11, 4, 3);
    test_curve_tree_with_parameters_newer::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(3), 11, 16, 5);

    test_curve_tree_with_parameters_newer::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(3), 11, 8, 3);
    test_curve_tree_with_parameters_newer::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(3), 11, 4, 3);
    test_curve_tree_with_parameters_newer::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(3), 11, 16, 5);
}

#[test]
pub fn test_curve_tree_even_depth_divisor() {
    test_curve_tree_with_parameters_newer::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(4), 11, 4, 3);
    test_curve_tree_with_parameters_newer::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(6), 11, 8, 3);
    test_curve_tree_with_parameters_newer::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(4), 11, 16, 5);

    test_curve_tree_with_parameters_newer::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(4), 11, 4, 3);
    test_curve_tree_with_parameters_newer::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(6), 11, 8, 3);
    test_curve_tree_with_parameters_newer::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(4), 11, 16, 5);
}

#[test]
pub fn test_curve_tree_even_depth_large_divisor() {
    test_curve_tree_with_parameters_newer::<
        64,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(4), 13, 64, 15);
    test_curve_tree_with_parameters_newer::<
        64,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(4), 13, 128, 15);
    test_curve_tree_with_parameters_newer::<
        64,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(4), 13, 256, 15);

    test_curve_tree_with_parameters_newer::<
        256,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(None, 13, 64, 15);
    test_curve_tree_with_parameters_newer::<
        256,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(None, 13, 128, 15);
    test_curve_tree_with_parameters_newer::<
        256,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(None, 13, 256, 15);

    test_curve_tree_with_parameters_newer::<
        64,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(4), 13, 64, 15);
    test_curve_tree_with_parameters_newer::<
        64,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(4), 13, 128, 15);
    test_curve_tree_with_parameters_newer::<
        64,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(4), 13, 256, 15);

    test_curve_tree_with_parameters_newer::<
        256,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(None, 13, 64, 15);
    test_curve_tree_with_parameters_newer::<
        256,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(None, 13, 128, 15);
    test_curve_tree_with_parameters_newer::<
        256,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(None, 13, 256, 15);
}

#[test]
pub fn test_curve_tree_odd_depth_large_divisor() {
    test_curve_tree_with_parameters_newer::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(Some(3), 11, 64, 10);

    test_curve_tree_with_parameters_newer::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(Some(3), 11, 64, 10);
}

pub fn test_curve_tree_with_parameters_newer<
    const L: usize,
    F: PrimeField,
    P0: DivisorCurve<BaseField = F> + Copy,
    P1: DivisorCurve<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    Params0: DiscreteLogParameters,
    Params1: DiscreteLogParameters,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_proofs: usize,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_proof_params = SelRerandProofParametersNew::<P0, P1, Params0, Params1>::new(
        generators_length,
        generators_length,
    )
    .unwrap();

    let set = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_proof_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let possible_proof_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();
    let mut proof_indices = BTreeSet::new();
    while proof_indices.len() < num_proofs {
        proof_indices.insert(possible_proof_indices.choose(&mut rng).unwrap());
    }

    let root = curve_tree.root_node();

    let mut prover_time = Duration::default();
    let mut verifier_time = Duration::default();

    let mut proof_size_printed = false;

    for leaf_index in proof_indices {
        let clock = Instant::now();

        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> = Prover::new(
            &sr_proof_params.even_parameters().pc_gens,
            pallas_transcript,
        );

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

        let path = curve_tree
            .get_path_to_leaf_for_proof(*leaf_index, 0)
            .unwrap();
        let (path_commitments, re_randomization_of_leaf) = path
            .select_and_rerandomize_prover_gadget_new::<_, Params0, Params1>(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut rng,
            )
            .unwrap();

        let nc1 = pallas_prover.constraints.len();
        let nc2 = vesta_prover.constraints.len();
        let (pallas_proof, vesta_proof) = prove(
            pallas_prover,
            vesta_prover,
            &sr_proof_params.even_parameters().bp_gens,
            &sr_proof_params.odd_parameters().bp_gens,
            &mut rng,
        )
        .unwrap();

        prover_time += clock.elapsed();

        if !proof_size_printed {
            println!(
                "Proof size for L={L}, height={}, constraints=({nc1}, {nc2}): {} bytes",
                curve_tree.height(),
                pallas_proof.compressed_size()
                    + vesta_proof.compressed_size()
                    + path_commitments.odd_divisor_comms.compressed_size()
                    + path_commitments.even_divisor_comms.compressed_size()
            );
            proof_size_printed = true;
        }

        {
            let clock = Instant::now();
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            path_commitments
                .select_and_rerandomize_verifier_gadget(
                    &root,
                    &mut pallas_verifier,
                    &mut vesta_verifier,
                    &sr_proof_params,
                )
                .unwrap();

            let rerandomized_leaf = path_commitments.path.get_rerandomized_leaf();
            verify(
                pallas_verifier,
                vesta_verifier,
                &pallas_proof,
                &vesta_proof,
                &sr_proof_params.even_parameters().pc_gens,
                &sr_proof_params.even_parameters().bp_gens,
                &sr_proof_params.odd_parameters().pc_gens,
                &sr_proof_params.odd_parameters().bp_gens,
                &mut rng,
            )
            .unwrap();
            verifier_time += clock.elapsed();
            assert_eq!(
                rerandomized_leaf.into_group(),
                curve_tree.get_leaf(*leaf_index).unwrap()
                    + (sr_proof_params.even_parameters().pc_gens.B_blinding
                        * re_randomization_of_leaf)
            )
        }
    }

    println!(
        "For tree with {} leaves, {} proofs took {:?} prover time and {:?} verifier time",
        num_leaves, num_proofs, prover_time, verifier_time
    );
}

#[test]
pub fn test_combined_vs_common_root_path_proofs_divisor() {
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(4, 12, 2);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(4, 13, 3);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(4, 13, 4);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(3, 13, 2);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(3, 13, 3);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(3, 13, 4);

    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(4, 12, 2);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(4, 13, 3);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(4, 13, 4);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(3, 13, 2);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(3, 13, 3);
    check_combined_vs_common_root_proofs_with_parameters_divisor::<
        32,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(3, 13, 4);
}

pub fn check_combined_vs_common_root_proofs_with_parameters_divisor<
    const L: usize,
    F: PrimeField,
    P0: DivisorCurve<BaseField = F> + Copy,
    P1: DivisorCurve<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    Params0: DiscreteLogParameters,
    Params1: DiscreteLogParameters,
>(
    depth: usize,
    generators_length_log_2: usize,
    num_paths: usize,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_proof_params = SelRerandProofParametersNew::<P0, P1, Params0, Params1>::new(
        generators_length,
        generators_length,
    )
    .unwrap();

    let mut set = Vec::<Affine<P0>>::new();
    for _ in 0..num_paths {
        set.push(Affine::<P0>::rand(&mut rng));
    }

    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_proof_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let root = curve_tree.root_node();

    println!("For {num_paths} leaves, width {L}, height {depth}");

    println!("Combined Proof");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> = Prover::new(
        &sr_proof_params.even_parameters().pc_gens,
        pallas_transcript,
    );

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

    let mut path_commitments_list: Vec<SelectAndRerandomizePathWithDivisorComms<L, P0, P1>> =
        vec![];
    let mut all_leaf_rerandomizations = vec![];

    for i in 0..num_paths {
        let path = curve_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
        let (path_commitments, rl) = path
            .select_and_rerandomize_prover_gadget_new::<_, Params0, Params1>(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut rng,
            )
            .unwrap();
        path_commitments_list.push(path_commitments);
        all_leaf_rerandomizations.push(rl);
    }

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_proof_params.even_parameters().bp_gens,
        &sr_proof_params.odd_parameters().bp_gens,
        &mut rng,
    )
    .unwrap();

    println!("Proving time: {:?}", clock.elapsed());

    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    let mut rerandomized_leaves = vec![];
    for path_commitments in path_commitments_list.iter() {
        path_commitments
            .select_and_rerandomize_verifier_gadget::<Params0, Params1>(
                &root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();
        rerandomized_leaves.push(path_commitments.path.get_rerandomized_leaf());
    }

    verify(
        pallas_verifier,
        vesta_verifier,
        &pallas_proof,
        &vesta_proof,
        &sr_proof_params.even_parameters().pc_gens,
        &sr_proof_params.even_parameters().bp_gens,
        &sr_proof_params.odd_parameters().pc_gens,
        &sr_proof_params.odd_parameters().bp_gens,
        &mut rng,
    )
    .unwrap();
    println!("Verification time: {:?}", clock.elapsed());

    for i in 0..num_paths {
        assert_eq!(
            rerandomized_leaves[i].into_group(),
            curve_tree.get_leaf(i).unwrap()
                + (sr_proof_params.even_parameters().pc_gens.B_blinding
                    * all_leaf_rerandomizations[i])
        )
    }

    println!("Common root proofs");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> = Prover::new(
        &sr_proof_params.even_parameters().pc_gens,
        pallas_transcript,
    );

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

    let leaf_indices: Vec<usize> = (0..num_paths).collect();
    let witness_paths_with_same_root = curve_tree
        .get_paths_to_leaves_for_proof(&leaf_indices, 0)
        .unwrap();

    let (all_path_commitments, all_leaf_rerandomizations) = witness_paths_with_same_root
        .select_and_rerandomize_prover_gadget_new::<_, Params0, Params1>(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            &mut rng,
        )
        .unwrap();

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_proof_params.even_parameters().bp_gens,
        &sr_proof_params.odd_parameters().bp_gens,
        &mut rng,
    )
    .unwrap();

    println!("Proving time: {:?}", clock.elapsed());

    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    SelectAndRerandomizePathWithDivisorComms::<L, P0, P1>::select_and_rerandomize_verifier_gadget_multi::<
        Params0,
        Params1,
    >(
        &all_path_commitments,
        &root,
        &mut pallas_verifier,
        &mut vesta_verifier,
        &sr_proof_params,
    ).unwrap();
    let rerandomized_leaves: Vec<_> = all_path_commitments
        .iter()
        .map(|p| p.path.get_rerandomized_leaf())
        .collect();

    verify(
        pallas_verifier,
        vesta_verifier,
        &pallas_proof,
        &vesta_proof,
        &sr_proof_params.even_parameters().pc_gens,
        &sr_proof_params.even_parameters().bp_gens,
        &sr_proof_params.odd_parameters().pc_gens,
        &sr_proof_params.odd_parameters().bp_gens,
        &mut rng,
    )
    .unwrap();
    println!("Verification time: {:?}", clock.elapsed());

    for i in 0..num_paths {
        assert_eq!(
            rerandomized_leaves[i].into_group(),
            curve_tree.get_leaf(i).unwrap()
                + (sr_proof_params.even_parameters().pc_gens.B_blinding
                    * all_leaf_rerandomizations[i])
        )
    }
}

#[test]
pub fn test_single_path_divisor_malformed_proof_inputs() {
    let mut rng = thread_rng();
    let generators_length = 1 << 11;
    let sr_proof_params =
        SelRerandProofParametersNew::<PallasConfig, VestaConfig, PallasParams, VestaParams>::new(
            generators_length,
            generators_length,
        )
        .unwrap();

    let set = (0..8)
        .map(|_| Affine::<PallasConfig>::rand(&mut rng))
        .collect::<Vec<_>>();
    let curve_tree =
        CurveTree::<32, 1, PallasConfig, VestaConfig>::from_leaves(&set, &sr_proof_params, Some(4));
    let root = curve_tree.root_node();

    let pallas_transcript = MerlinTranscript::new(b"malformed-single-path");
    let mut pallas_prover: Prover<_, Affine<PallasConfig>> = Prover::new(
        &sr_proof_params.even_parameters().pc_gens,
        pallas_transcript,
    );
    let vesta_transcript = MerlinTranscript::new(b"malformed-single-path");
    let mut vesta_prover: Prover<_, Affine<VestaConfig>> =
        Prover::new(&sr_proof_params.odd_parameters().pc_gens, vesta_transcript);

    let path = curve_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let (valid_path_commitments, _) = path
        .select_and_rerandomize_prover_gadget_new::<_, PallasParams, VestaParams>(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            &mut rng,
        )
        .unwrap();

    let assert_malformed = |err: Error, expected: &str| match err {
        Error::MalformedProofInput(msg) => assert!(msg.contains(expected), "{msg}"),
        other => panic!("unexpected error variant: {other:?}"),
    };

    let mut missing_root_child = valid_path_commitments.clone();
    let expected_root_child_msg = match &root {
        Root::Even(_) => {
            missing_root_child.path.odd_commitments.clear();
            "missing root child in odd_commitments for even root"
        }
        Root::Odd(_) => {
            missing_root_child.path.even_commitments.clear();
            "missing root child in even_commitments for odd root"
        }
    };
    let pallas_transcript = MerlinTranscript::new(b"malformed-single-path-root-child");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"malformed-single-path-root-child");
    let mut vesta_verifier = Verifier::new(vesta_transcript);
    let err = missing_root_child
        .select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
            &root,
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_proof_params,
        )
        .unwrap_err();
    assert_malformed(err, expected_root_child_msg);

    let mut missing_root_divisor = valid_path_commitments.clone();
    let expected_root_divisor_msg = match &root {
        Root::Even(_) => {
            missing_root_divisor.even_divisor_comms.clear();
            "missing root divisor commitments for even side"
        }
        Root::Odd(_) => {
            missing_root_divisor.odd_divisor_comms.clear();
            "missing root divisor commitments for odd side"
        }
    };
    let pallas_transcript = MerlinTranscript::new(b"malformed-single-path-root-divisor");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"malformed-single-path-root-divisor");
    let mut vesta_verifier = Verifier::new(vesta_transcript);
    let err = missing_root_divisor
        .select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
            &root,
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_proof_params,
        )
        .unwrap_err();
    assert_malformed(err, expected_root_divisor_msg);

    let mut missing_even_non_root_chain = valid_path_commitments.clone();
    missing_even_non_root_chain.path.even_commitments.clear();
    let pallas_transcript = MerlinTranscript::new(b"malformed-single-path-even-chain");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"malformed-single-path-even-chain");
    let mut vesta_verifier = Verifier::new(vesta_transcript);
    let err = missing_even_non_root_chain
        .select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
            &root,
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_proof_params,
        )
        .unwrap_err();
    assert_malformed(err, "even_commitments must contain at least one element");
}
