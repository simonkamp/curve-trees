extern crate bulletproofs;
extern crate relations;

use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::AffineRepr;
use ark_ec_divisors::{
    curves::{
        helios::HeliosParams, pallas::PallasParams, selene::SeleneParams, vesta::VestaParams,
    },
    DivisorCurve,
};
use ark_ff::PrimeField;
use bulletproofs::r1cs::*;
use relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use relations::curve_tree::*;
use relations::error::Error as RelError;
use relations::utils::{prove, verify};
use std::time::Instant;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_std::UniformRand;

use ark_helios::{Fq as HeliosBase, Fr as HeliosFr, HeliosConfig};
use ark_pallas::{Fq as PallasBase, Fr as PallasFr, PallasConfig};
use ark_selene::SeleneConfig;
use ark_vesta::VestaConfig;

use ark_serialize::CanonicalSerialize;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::thread_rng;
use relations::parameters::{
    SelRerandParameters, SelRerandProofParameters, SelRerandProofParametersNew,
};

#[test]
pub fn test_batched_curve_tree_even_depth() {
    test_batched_curve_tree_with_parameters::<32, 2, PallasBase, PallasConfig, VestaConfig>(
        2, 12, 2,
    );
    test_batched_curve_tree_with_parameters::<32, 2, PallasBase, PallasConfig, VestaConfig>(
        4, 12, 2,
    );
    test_batched_curve_tree_with_parameters::<32, 2, PallasBase, PallasConfig, VestaConfig>(
        6, 12, 2,
    );
    // test_batched_curve_tree_with_parameters::<32, 2, SecpBase, SecpConfig, SecqConfig>(4, 12, 2);
}

#[test]
pub fn test_batched_curve_tree_odd_depth() {
    // TODO: Uncomment and support tree of height 1
    // test_batched_curve_tree_with_parameters::<32, 2, PallasBase, PallasConfig, VestaConfig>(1, 12, 2);
    test_batched_curve_tree_with_parameters::<32, 2, PallasBase, PallasConfig, VestaConfig>(
        3, 12, 2,
    );
    test_batched_curve_tree_with_parameters::<32, 2, PallasBase, PallasConfig, VestaConfig>(
        5, 12, 2,
    );
    // test_batched_curve_tree_with_parameters::<32, 2, SecpBase, SecpConfig, SecqConfig>(3, 12, 2);
}

#[test]
pub fn test_batched_curve_tree_less_than_batch() {
    test_batched_curve_tree_with_parameters::<256, 16, PallasBase, PallasConfig, VestaConfig>(
        3, 15, 1,
    );
    test_batched_curve_tree_with_parameters::<256, 16, PallasBase, PallasConfig, VestaConfig>(
        3, 15, 2,
    );
    test_batched_curve_tree_with_parameters::<256, 16, PallasBase, PallasConfig, VestaConfig>(
        3, 15, 3,
    );
    test_batched_curve_tree_with_parameters::<256, 16, PallasBase, PallasConfig, VestaConfig>(
        3, 15, 4,
    );
    test_batched_curve_tree_with_parameters::<256, 16, PallasBase, PallasConfig, VestaConfig>(
        3, 15, 5,
    );
    test_batched_curve_tree_with_parameters::<256, 16, PallasBase, PallasConfig, VestaConfig>(
        3, 15, 6,
    );
    test_batched_curve_tree_with_parameters::<256, 16, PallasBase, PallasConfig, VestaConfig>(
        3, 15, 16,
    );
}

#[test]
pub fn test_optimized_multi_paths() {
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(4, 12, 3);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(4, 12, 4);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(4, 12, 5);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(4, 12, 8);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(4, 12, 9);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(3, 13, 3);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(3, 13, 4);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(3, 13, 5);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(3, 13, 8);
    check_optimized_multi_paths::<8, 4, PallasBase, PallasConfig, VestaConfig>(3, 13, 9);
}

pub fn test_batched_curve_tree_with_parameters<
    const L: usize,
    const M: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
    num_indices_to_prove: u32,
) {
    assert!(num_indices_to_prove <= M as u32);

    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

    let mut set = Vec::<Affine<P0>>::new();
    let mut indices = vec![0u32; num_indices_to_prove as usize];
    for i in 0..num_indices_to_prove {
        set.push(Affine::<P0>::rand(&mut rng));
        indices[i as usize] = i;
    }
    let curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let paths = curve_tree.get_paths_to_leaves(indices.as_slice()).unwrap();

    println!(
        "For batch size {} (max {M}), width {L} and height {depth}",
        num_indices_to_prove
    );
    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);
    let (path_commitments, leaf_randomizations) = paths
        .batched_select_and_rerandomize_prover_gadget(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            &mut rng,
        )
        .expect("Failed to prove batched select and rerandomize");

    println!(
        "prover constraints {} {}",
        pallas_prover.constraints.len(),
        vesta_prover.constraints.len()
    );

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();
    println!("Proving time: {:?}", clock.elapsed());
    println!(
        "Proof size: {}",
        path_commitments.compressed_size()
            + pallas_proof.compressed_size()
            + vesta_proof.compressed_size()
    );

    {
        let root = curve_tree.root_node();

        let clock = Instant::now();

        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        path_commitments
            .batched_select_and_rerandomize_verifier_gadget(
                &root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();
        let rerandomized_leaves = path_commitments.get_rerandomized_leaves();

        println!(
            "verifier constraints {} {}",
            pallas_verifier.constraints.len(),
            vesta_verifier.constraints.len()
        );

        verify(
            pallas_verifier,
            vesta_verifier,
            &pallas_proof,
            &vesta_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng,
        )
        .unwrap();
        println!("Verifying time: {:?}", clock.elapsed());
        for i in 0..num_indices_to_prove as usize {
            assert_eq!(
                rerandomized_leaves[i].into_group(),
                set[i] + (sr_params.even_parameters.pc_gens.B_blinding * leaf_randomizations[i])
            );
        }
    }
}

#[test]
pub fn test_individual_vs_batched_proofs() {
    check_individual_vs_batched_proofs_with_parameters::<
        512,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(4, 14);
    check_individual_vs_batched_proofs_with_parameters::<
        512,
        3,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(4, 14);
}

pub fn check_individual_vs_batched_proofs_with_parameters<
    const L: usize,
    const M: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

    // Create leaves for both trees
    let mut set = Vec::<Affine<P0>>::new();
    for _ in 0..M {
        set.push(Affine::<P0>::rand(&mut rng));
    }

    // Create curve tree with batch support
    let batched_curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(batched_curve_tree.height(), depth);

    // For individual proofs and combined proof, using a non-batched curve tree
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    println!("For {M} leaves, width {L}, height {depth}");

    // Create individual proofs for each leaf
    println!("Individual Proofs");
    let mut individual_proofs = Vec::new();
    let mut total_individual_proof_size = 0;

    let clock = Instant::now();
    for i in 0..M {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let path = curve_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
        let (path_commitments, _) = path
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
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng,
        )
        .unwrap();

        total_individual_proof_size += path_commitments.compressed_size()
            + pallas_proof.compressed_size()
            + vesta_proof.compressed_size();
        individual_proofs.push((path_commitments, pallas_proof, vesta_proof));
    }

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", total_individual_proof_size);

    // Verify individual proofs
    let clock = Instant::now();
    for (path_commitments, pallas_proof, vesta_proof) in &individual_proofs {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        path_commitments
            .select_and_rerandomize_verifier_gadget(
                &curve_tree.root_node(),
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();

        verify(
            pallas_verifier,
            vesta_verifier,
            pallas_proof,
            vesta_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng,
        )
        .unwrap();
    }
    println!("Verification time: {:?}", clock.elapsed());

    // Create single combined proof (call select_and_rerandomize_prover_gadget for each leaf but prove() only once)
    println!("Combined Proof");

    let root = curve_tree.root_node();
    let mut paths = vec![];
    for i in 0..M {
        let path = curve_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
        paths.push(path);
    }
    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    // Call select_and_rerandomize_prover_gadget for each leaf to accumulate constraints
    let mut path_commitments_list: Vec<SelectAndRerandomizePath<L, P0, P1>> = Vec::new();
    for i in 0..M {
        let (path_commitments, _) = paths[i]
            .select_and_rerandomize_prover_gadget(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut rng,
            )
            .unwrap();
        path_commitments_list.push(path_commitments);
    }

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();

    let combined_proof_size = path_commitments_list.compressed_size()
        + pallas_proof.compressed_size()
        + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", combined_proof_size);

    // Verify combined proof
    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    // For verification, we need to call the verifier gadget for each leaf too
    for path_commitments in &path_commitments_list {
        path_commitments
            .select_and_rerandomize_verifier_gadget(
                &root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();
    }

    verify(
        pallas_verifier,
        vesta_verifier,
        &pallas_proof,
        &vesta_proof,
        &sr_params.even_parameters.pc_gens,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.pc_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();
    println!("Verification time: {:?}", clock.elapsed());

    // Create proper batched proof using batched_select_and_rerandomize_prover_gadget
    println!("Batched Proof");

    let mut indices = vec![0u32; M];
    for i in 0..M {
        indices[i] = i as u32;
    }
    let paths = batched_curve_tree
        .get_paths_to_leaves(indices.as_slice())
        .unwrap();
    let root = batched_curve_tree.root_node();

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let (path_commitments, leaf_randomizations) = paths
        .batched_select_and_rerandomize_prover_gadget(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            &mut rng,
        )
        .expect("Failed to prove batched select and rerandomize");

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();

    let batched_proof_size = path_commitments.compressed_size()
        + pallas_proof.compressed_size()
        + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", batched_proof_size);

    // Verify batched proof
    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    path_commitments
        .batched_select_and_rerandomize_verifier_gadget(
            &root,
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_proof_params,
        )
        .unwrap();
    let rerandomized_leaves = path_commitments.get_rerandomized_leaves();
    verify(
        pallas_verifier,
        vesta_verifier,
        &pallas_proof,
        &vesta_proof,
        &sr_params.even_parameters.pc_gens,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.pc_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();
    println!("Verification time: {:?}", clock.elapsed());
    for i in 0..M {
        assert_eq!(
            rerandomized_leaves[i].into_group(),
            set[i].into_group()
                + (sr_params.even_parameters.pc_gens.B_blinding * leaf_randomizations[i])
        );
    }
}

#[test]
pub fn test_batched_combined_vs_common_root_proofs() {
    check_batched_combined_vs_common_root_proofs_with_parameters::<
        32,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(4, 13, 3);
    check_batched_combined_vs_common_root_proofs_with_parameters::<
        32,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(4, 13, 4);
    check_batched_combined_vs_common_root_proofs_with_parameters::<
        32,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(4, 14, 5);
    check_batched_combined_vs_common_root_proofs_with_parameters::<
        32,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(3, 13, 3);
    check_batched_combined_vs_common_root_proofs_with_parameters::<
        32,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(3, 13, 4);
    check_batched_combined_vs_common_root_proofs_with_parameters::<
        32,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(3, 14, 5);

    check_batched_combined_vs_common_root_proofs_with_parameters::<
        512,
        4,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(4, 17, 40);
}

pub fn check_batched_combined_vs_common_root_proofs_with_parameters<
    const L: usize,
    const M: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
    num_leaves: u32,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

    let mut set = Vec::<Affine<P0>>::new();
    for _ in 0..num_leaves {
        set.push(Affine::<P0>::rand(&mut rng));
    }

    let curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    // ceil(num_leaves/M)
    let num_paths = (num_leaves as usize + M - 1) / M;
    let mut paths = vec![];
    for indices in (0..num_leaves).collect::<Vec<_>>().chunks(M) {
        paths.push(curve_tree.get_paths_to_leaves(&indices).unwrap());
    }
    assert_eq!(paths.len(), num_paths);

    println!("For {num_leaves} leaves with batch size {M}, width {L}, height {depth}");

    println!("Combined Proof (separate multi-paths)");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let mut path_commitments_list: Vec<SelectAndRerandomizeMultiPath<L, M, P0, P1>> = vec![];
    let mut all_leaf_rerandomizations = vec![];
    for p in &paths {
        let (path_commitments, leaf_rands) = p
            .batched_select_and_rerandomize_prover_gadget(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut rng,
            )
            .unwrap();
        path_commitments_list.push(path_commitments);
        all_leaf_rerandomizations.push(leaf_rands);
    }

    let mut expected_num_leaves = 0;
    for i in 0..num_paths {
        expected_num_leaves += path_commitments_list[i].num_indices();
    }
    assert_eq!(expected_num_leaves, num_leaves);

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();

    let combined_proof_size = pallas_proof.compressed_size() + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", combined_proof_size);

    let root = curve_tree.root_node();

    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    let mut rerandomized_leaves_list = vec![];
    for path_commitments in &path_commitments_list {
        path_commitments
            .batched_select_and_rerandomize_verifier_gadget(
                &root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();
        let rl = path_commitments.get_rerandomized_leaves();
        rerandomized_leaves_list.push(rl);
    }

    verify(
        pallas_verifier,
        vesta_verifier,
        &pallas_proof,
        &vesta_proof,
        &sr_params.even_parameters.pc_gens,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.pc_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();
    println!("Verification time: {:?}", clock.elapsed());

    for i in 0..num_paths {
        for j in 0..M {
            let leaf_idx = i * M + j;
            if leaf_idx < num_leaves as usize {
                assert_eq!(
                    rerandomized_leaves_list[i][j].into_group(),
                    curve_tree.get_leaf(leaf_idx).unwrap().into_group()
                        + (sr_params.even_parameters.pc_gens.B_blinding
                            * all_leaf_rerandomizations[i][j])
                )
            }
        }
    }

    println!("Common root proofs");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let (path_commitments_list, all_leaf_rerandomizations) =
        CurveTreeWitnessMultiPath::batched_select_and_rerandomize_prover_gadget_for_common_root(
            &paths,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            &mut rng,
        )
        .unwrap();

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();

    let all_paths_proof_size = pallas_proof.compressed_size() + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", all_paths_proof_size);

    let mut expected_num_leaves = 0;
    for i in 0..num_paths {
        expected_num_leaves += path_commitments_list[i].num_indices();
    }
    assert_eq!(expected_num_leaves, num_leaves);

    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    SelectAndRerandomizeMultiPath::batched_select_and_rerandomize_verifier_gadget_for_common_root(
        &path_commitments_list,
        &root,
        &mut pallas_verifier,
        &mut vesta_verifier,
        &sr_proof_params,
    )
    .unwrap();
    let rerandomized_leaves_list: Vec<_> = path_commitments_list
        .iter()
        .map(|p| p.get_rerandomized_leaves())
        .collect();

    verify(
        pallas_verifier,
        vesta_verifier,
        &pallas_proof,
        &vesta_proof,
        &sr_params.even_parameters.pc_gens,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.pc_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();
    println!("Verification time: {:?}", clock.elapsed());

    for i in 0..num_paths {
        for j in 0..M {
            let leaf_idx = i * M + j;
            if leaf_idx < num_leaves as usize {
                assert_eq!(
                    rerandomized_leaves_list[i][j].into_group(),
                    curve_tree.get_leaf(leaf_idx).unwrap()
                        + (sr_params.even_parameters.pc_gens.B_blinding
                            * all_leaf_rerandomizations[i][j])
                )
            }
        }
    }
}

pub fn check_optimized_multi_paths<
    const L: usize,
    const M: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
    num_leaves: usize,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let mut set = Vec::with_capacity(num_leaves);
    let mut leaf_indices = Vec::with_capacity(num_leaves);
    for i in 0..num_leaves {
        set.push(Affine::<P0>::rand(&mut rng));
        leaf_indices.push(i as u32)
    }

    let curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let mut multi_paths = Vec::new();
    for chunk in leaf_indices.chunks(M) {
        let multi_path = curve_tree.get_paths_to_leaves(chunk).unwrap();
        multi_paths.push(multi_path);
    }

    let optimized_multi_paths = curve_tree.get_optmz_paths_to_leaves(&leaf_indices).unwrap();

    let num_multi_paths = (num_leaves + M - 1) / M;

    assert_eq!(optimized_multi_paths.num_multi_paths(), multi_paths.len());

    println!(
        "For L={L}, M={M} and {num_multi_paths} paths, size = {} and optimized size = {}",
        multi_paths.compressed_size(),
        optimized_multi_paths.compressed_size()
    );

    let reconstructed_multi_paths = optimized_multi_paths.to_individual_multi_paths();
    assert_eq!(reconstructed_multi_paths.len(), num_multi_paths);

    for (i, (original, reconstructed)) in multi_paths
        .iter()
        .zip(reconstructed_multi_paths.iter())
        .enumerate()
    {
        assert_eq!(
            original.even_internal_nodes.len(),
            reconstructed.even_internal_nodes.len(),
            "Multi-path {}: even_internal_nodes length mismatch",
            i
        );
        assert_eq!(
            original.odd_internal_nodes.len(),
            reconstructed.odd_internal_nodes.len(),
            "Multi-path {}: odd_internal_nodes length mismatch",
            i
        );

        for (level, (orig_level, recon_level)) in original
            .even_internal_nodes
            .iter()
            .zip(reconstructed.even_internal_nodes.iter())
            .enumerate()
        {
            assert_eq!(
                orig_level.len(),
                recon_level.len(),
                "Multi-path {}, even level {}: nodes count mismatch",
                i,
                level
            );
            for (tree_idx, (orig_node, recon_node)) in
                orig_level.iter().zip(recon_level.iter()).enumerate()
            {
                assert_eq!(
                    orig_node.x_coord_children, recon_node.x_coord_children,
                    "Multi-path {}, even level {}, tree {}: x_coord_children mismatch",
                    i, level, tree_idx
                );
                assert_eq!(
                    orig_node.child_node_to_randomize, recon_node.child_node_to_randomize,
                    "Multi-path {}, even level {}, tree {}: child_node_to_randomize mismatch",
                    i, level, tree_idx
                );
            }
        }

        for (level, (orig_level, recon_level)) in original
            .odd_internal_nodes
            .iter()
            .zip(reconstructed.odd_internal_nodes.iter())
            .enumerate()
        {
            assert_eq!(
                orig_level.len(),
                recon_level.len(),
                "Multi-path {}, odd level {}: nodes count mismatch",
                i,
                level
            );
            for (tree_idx, (orig_node, recon_node)) in
                orig_level.iter().zip(recon_level.iter()).enumerate()
            {
                assert_eq!(
                    orig_node.x_coord_children, recon_node.x_coord_children,
                    "Multi-path {}, odd level {}, tree {}: x_coord_children mismatch",
                    i, level, tree_idx
                );
                assert_eq!(
                    orig_node.child_node_to_randomize, recon_node.child_node_to_randomize,
                    "Multi-path {}, odd level {}, tree {}: child_node_to_randomize mismatch",
                    i, level, tree_idx
                );
            }
        }
    }

    for multi_path in &multi_paths[1..] {
        assert_eq!(
            multi_path.even_internal_nodes.len(),
            multi_paths[0].even_internal_nodes.len()
        );
        assert_eq!(
            multi_path.odd_internal_nodes.len(),
            multi_paths[0].odd_internal_nodes.len()
        );
    }
}

#[test]
pub fn test_batched_curve_tree_even_depth_divisor() {
    test_batched_curve_tree_with_parameters_new::<
        32,
        2,
        PallasFr,   // F0 = P0::ScalarField
        PallasBase, // F1 = P0::BaseField
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(4, 12, 2);

    test_batched_curve_tree_with_parameters_new::<
        32,
        2,
        PallasFr,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(6, 13, 2);

    test_batched_curve_tree_with_parameters_new::<
        32,
        2,
        HeliosFr,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(4, 12, 2);

    test_batched_curve_tree_with_parameters_new::<
        32,
        2,
        HeliosFr,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(6, 13, 2);
}

#[test]
pub fn test_batched_curve_tree_odd_depth_divisor() {
    test_batched_curve_tree_with_parameters_new::<
        32,
        2,
        PallasFr,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(3, 12, 2);

    test_batched_curve_tree_with_parameters_new::<
        32,
        2,
        PallasFr,
        PallasBase,
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >(5, 12, 2);

    test_batched_curve_tree_with_parameters_new::<
        32,
        2,
        HeliosFr,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(3, 12, 2);

    test_batched_curve_tree_with_parameters_new::<
        32,
        2,
        HeliosFr,
        HeliosBase,
        HeliosConfig,
        SeleneConfig,
        HeliosParams,
        SeleneParams,
    >(5, 12, 2);
}

pub fn test_batched_curve_tree_with_parameters_new<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    P0: DivisorCurve<BaseField = F1, ScalarField = F0> + Copy,
    P1: DivisorCurve<BaseField = F0, ScalarField = F1> + Copy,
    Params0: DiscreteLogParameters,
    Params1: DiscreteLogParameters,
>(
    depth: usize,
    generators_length_log_2: usize,
    num_indices_to_prove: u32,
) {
    assert!(num_indices_to_prove <= M as u32);

    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let sr_proof_params =
        SelRerandProofParametersNew::<P0, P1, Params0, Params1>::from_sr_params(sr_params.clone());

    let mut set = Vec::<Affine<P0>>::new();
    let mut indices = vec![0u32; num_indices_to_prove as usize];
    for i in 0..num_indices_to_prove {
        set.push(Affine::<P0>::rand(&mut rng));
        indices[i as usize] = i;
    }
    let curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let paths = curve_tree.get_paths_to_leaves(indices.as_slice()).unwrap();

    println!(
        "For batch size {} (max {M}), width {L} and height {depth}",
        num_indices_to_prove
    );
    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let (path_commitments, leaf_randomizations) = paths
        .batched_select_and_rerandomize_prover_gadget_new::<_, Params0, Params1>(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            &mut rng,
        )
        .expect("Failed to prove batched select and rerandomize (divisor)");

    println!(
        "prover constraints {} {}",
        pallas_prover.constraints.len(),
        vesta_prover.constraints.len()
    );

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.bp_gens,
        &mut rng,
    )
    .unwrap();
    println!("Proving time: {:?}", clock.elapsed());
    println!(
        "Proof size: {}",
        path_commitments.compressed_size()
            + pallas_proof.compressed_size()
            + vesta_proof.compressed_size()
    );

    {
        let root = curve_tree.root_node();

        let clock = Instant::now();

        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        path_commitments
            .batched_select_and_rerandomize_verifier_gadget::<Params0, Params1>(
                &root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_proof_params,
            )
            .unwrap();
        let rerandomized_leaves = path_commitments.path.get_rerandomized_leaves();

        println!(
            "verifier constraints {} {}",
            pallas_verifier.constraints.len(),
            vesta_verifier.constraints.len()
        );

        verify(
            pallas_verifier,
            vesta_verifier,
            &pallas_proof,
            &vesta_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng,
        )
        .unwrap();
        println!("Verifying time: {:?}", clock.elapsed());
        for i in 0..num_indices_to_prove as usize {
            assert_eq!(
                rerandomized_leaves[i].into_group(),
                set[i] + (sr_params.even_parameters.pc_gens.B_blinding * leaf_randomizations[i])
            );
        }
    }
}

#[test]
pub fn test_batched_divisor_malformed_proof_inputs() {
    let mut rng = thread_rng();
    let generators_length = 1 << 12;
    let sr_params =
        SelRerandParameters::<PallasConfig, VestaConfig>::new(generators_length, generators_length)
            .unwrap();
    let sr_proof_params = SelRerandProofParametersNew::<
        PallasConfig,
        VestaConfig,
        PallasParams,
        VestaParams,
    >::from_sr_params(sr_params.clone());

    let set = (0..2)
        .map(|_| Affine::<PallasConfig>::rand(&mut rng))
        .collect::<Vec<_>>();
    let curve_tree =
        CurveTree::<32, 2, PallasConfig, VestaConfig>::from_leaves(&set, &sr_proof_params, Some(4));
    let root = curve_tree.root_node();
    let paths = curve_tree.get_paths_to_leaves(&[0, 1]).unwrap();

    let pallas_transcript = MerlinTranscript::new(b"malformed-batched-path");
    let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"malformed-batched-path");
    let mut vesta_prover: Prover<_, Affine<VestaConfig>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);
    let (valid_path_commitments, _) = paths
        .batched_select_and_rerandomize_prover_gadget_new::<_, PallasParams, VestaParams>(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            &mut rng,
        )
        .unwrap();

    let mut zero_selected = valid_path_commitments.clone();
    zero_selected.path.selected_commitments.clear();
    let pallas_transcript = MerlinTranscript::new(b"malformed-batched-empty-selected");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"malformed-batched-empty-selected");
    let mut vesta_verifier = Verifier::new(vesta_transcript);
    let err = zero_selected
        .batched_select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
            &root,
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_proof_params,
        )
        .unwrap_err();
    assert!(matches!(err, RelError::NeedNonZeroNumberOfIndices));

    let mut short_root = root.clone();
    let expected_root_msg = match &mut short_root {
        Root::Even(root_node) => {
            root_node.x_coord_children.truncate(1);
            "root x_coord_children shorter than selected indices for even root"
        }
        Root::Odd(root_node) => {
            root_node.x_coord_children.truncate(1);
            "root x_coord_children shorter than selected indices for odd root"
        }
    };
    let pallas_transcript = MerlinTranscript::new(b"malformed-batched-root-xcoords");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"malformed-batched-root-xcoords");
    let mut vesta_verifier = Verifier::new(vesta_transcript);
    let err = valid_path_commitments
        .clone()
        .batched_select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
            &short_root,
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_proof_params,
        )
        .unwrap_err();
    match err {
        RelError::MalformedProofInput(msg) => assert!(msg.contains(expected_root_msg), "{msg}"),
        other => panic!("unexpected error variant: {other:?}"),
    }

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
    let pallas_transcript = MerlinTranscript::new(b"malformed-batched-root-child");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"malformed-batched-root-child");
    let mut vesta_verifier = Verifier::new(vesta_transcript);
    let err = missing_root_child
        .batched_select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
            &root,
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_proof_params,
        )
        .unwrap_err();
    match err {
        RelError::MalformedProofInput(msg) => {
            assert!(msg.contains(expected_root_child_msg), "{msg}")
        }
        other => panic!("unexpected error variant: {other:?}"),
    }
}
