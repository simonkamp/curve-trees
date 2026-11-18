extern crate bulletproofs;
extern crate relations;

use ark_dlog_gadget::dlog::DivisorComms;
use ark_ec::short_weierstrass::Affine;
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_pallas::PallasConfig;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use bulletproofs::r1cs::{Prover, Verifier};
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::thread_rng;
use relations::curve_tree::{
    CurveTree, Root, SelectAndRerandomizeMultiPathWithDivisorComms,
    SelectAndRerandomizePathWithDivisorComms,
};
use relations::error::Error;
use relations::parameters::{SelRerandParametersRef, SelRerandProofParametersNew};
use relations::utils::{prove, verify};
use relations::verifier_common_root::RootChildrenPoly;

const L: usize = 8;
const M: usize = 2;
const MAX_HEIGHT: u8 = 5;
const NUM_LEAVES: usize = 4;
const GENS_LOG2: usize = 12;

type Params = SelRerandProofParametersNew<PallasConfig, VestaConfig, PallasParams, VestaParams>;
type SinglePath = SelectAndRerandomizePathWithDivisorComms<L, PallasConfig, VestaConfig>;
type MultiPath = SelectAndRerandomizeMultiPathWithDivisorComms<L, M, PallasConfig, VestaConfig>;

fn new_params() -> Params {
    Params::new(1 << GENS_LOG2, 1 << GENS_LOG2).unwrap()
}

fn new_verifiers() -> (
    Verifier<MerlinTranscript, Affine<PallasConfig>>,
    Verifier<MerlinTranscript, Affine<VestaConfig>>,
) {
    (
        Verifier::new(MerlinTranscript::new(b"path-height")),
        Verifier::new(MerlinTranscript::new(b"path-height")),
    )
}

fn new_provers(
    params: &Params,
) -> (
    Prover<'_, MerlinTranscript, Affine<PallasConfig>>,
    Prover<'_, MerlinTranscript, Affine<VestaConfig>>,
) {
    (
        Prover::new(
            &params.even_parameters().pc_gens,
            MerlinTranscript::new(b"path-height"),
        ),
        Prover::new(
            &params.odd_parameters().pc_gens,
            MerlinTranscript::new(b"path-height"),
        ),
    )
}

fn assert_path_length_mismatch(res: Result<(), Error>) {
    match res {
        Err(Error::PathLengthMismatch { .. }) => {}
        other => panic!("expected PathLengthMismatch, got {other:?}"),
    }
}

fn assert_invalid_root_height(res: Result<(), Error>) {
    match res {
        Err(Error::InvalidRootHeight { .. }) => {}
        other => panic!("expected InvalidRootHeight, got {other:?}"),
    }
}

/// Runs every single-path verifier gadget on `path` and returns their results.
fn single_path_gadget_results(
    path: &SinglePath,
    root: &Root<L, 1, PallasConfig, VestaConfig>,
    params: &Params,
) -> Vec<Result<(), Error>> {
    let (mut pv, mut vv) = new_verifiers();
    let single = path.select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
        root, &mut pv, &mut vv, params,
    );
    let (mut pv, mut vv) = new_verifiers();
    let multi = SinglePath::select_and_rerandomize_verifier_gadget_multi::<PallasParams, VestaParams>(
        core::slice::from_ref(path),
        root,
        &mut pv,
        &mut vv,
        params,
    );
    let (mut pv, mut vv) = new_verifiers();
    let common_root = RootChildrenPoly::from_root(root).and_then(|poly| {
        path.select_and_rerandomize_verifier_gadget_common_root::<PallasParams, VestaParams>(
            root, &poly, &mut pv, &mut vv, params,
        )
    });
    vec![single, multi, common_root]
}

/// Runs every batched verifier gadget on `path` and returns their results.
fn multi_path_gadget_results(
    path: &MultiPath,
    root: &Root<L, M, PallasConfig, VestaConfig>,
    params: &Params,
) -> Vec<Result<(), Error>> {
    let (mut pv, mut vv) = new_verifiers();
    let single = path.batched_select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
        root, &mut pv, &mut vv, params,
    );
    let (mut pv, mut vv) = new_verifiers();
    let multi = MultiPath::batched_select_and_rerandomize_verifier_gadget_multi::<
        PallasParams,
        VestaParams,
    >(core::slice::from_ref(path), root, &mut pv, &mut vv, params);
    vec![single, multi]
}

/// Copies of `path` with one element added to or removed from one of its vectors.
fn single_path_length_tamperings(path: &SinglePath) -> Vec<SinglePath> {
    let mut out = Vec::new();
    let mut p = path.clone();
    let extra = p.path.even_commitments[0];
    p.path.even_commitments.push(extra);
    out.push(p);
    let mut p = path.clone();
    p.path.even_commitments.pop();
    out.push(p);
    if let Some(extra) = path.path.odd_commitments.first() {
        let mut p = path.clone();
        p.path.odd_commitments.push(*extra);
        out.push(p);
        let mut p = path.clone();
        p.path.odd_commitments.pop();
        out.push(p);
    } else {
        let mut p = path.clone();
        p.path
            .odd_commitments
            .push(Affine::<VestaConfig>::rand(&mut thread_rng()));
        out.push(p);
    }
    if let Some(extra) = path.even_divisor_comms.first() {
        let mut p = path.clone();
        p.even_divisor_comms.push(extra.clone());
        out.push(p);
        let mut p = path.clone();
        p.even_divisor_comms.pop();
        out.push(p);
    } else {
        let mut p = path.clone();
        p.even_divisor_comms
            .push(DivisorComms(vec![Affine::<PallasConfig>::rand(
                &mut thread_rng(),
            )]));
        out.push(p);
    }
    let mut p = path.clone();
    let extra = p.odd_divisor_comms[0].clone();
    p.odd_divisor_comms.push(extra);
    out.push(p);
    let mut p = path.clone();
    p.odd_divisor_comms.pop();
    out.push(p);
    out
}

/// Copies of `path` with one element added to or removed from one of its vectors.
fn multi_path_length_tamperings(path: &MultiPath) -> Vec<MultiPath> {
    let mut out = Vec::new();
    if let Some(extra) = path.path.even_commitments.first() {
        let mut p = path.clone();
        p.path.even_commitments.push(*extra);
        out.push(p);
        let mut p = path.clone();
        p.path.even_commitments.pop();
        out.push(p);
    } else {
        let mut p = path.clone();
        p.path
            .even_commitments
            .push(Affine::<PallasConfig>::rand(&mut thread_rng()));
        out.push(p);
    }
    if let Some(extra) = path.path.odd_commitments.first() {
        let mut p = path.clone();
        p.path.odd_commitments.push(*extra);
        out.push(p);
        let mut p = path.clone();
        p.path.odd_commitments.pop();
        out.push(p);
    } else {
        let mut p = path.clone();
        p.path
            .odd_commitments
            .push(Affine::<VestaConfig>::rand(&mut thread_rng()));
        out.push(p);
    }
    if let Some(extra) = path.even_divisor_comms.first() {
        let mut p = path.clone();
        p.even_divisor_comms.push(extra.clone());
        out.push(p);
        let mut p = path.clone();
        p.even_divisor_comms.pop();
        out.push(p);
    } else {
        let mut p = path.clone();
        p.even_divisor_comms
            .push(DivisorComms(vec![Affine::<PallasConfig>::rand(
                &mut thread_rng(),
            )]));
        out.push(p);
    }
    let mut p = path.clone();
    let extra = p.odd_divisor_comms[0].clone();
    p.odd_divisor_comms.push(extra);
    out.push(p);
    let mut p = path.clone();
    p.odd_divisor_comms.pop();
    out.push(p);
    out
}

fn with_height<const N: usize>(
    root: &Root<L, N, PallasConfig, VestaConfig>,
    height: u8,
) -> Root<L, N, PallasConfig, VestaConfig> {
    let mut root = root.clone();
    match &mut root {
        Root::Even(n) => n.height = height,
        Root::Odd(n) => n.height = height,
    }
    root
}

#[test]
fn root_height_matches_tree_height() {
    let params = new_params();
    let mut rng = thread_rng();
    let set = (0..NUM_LEAVES)
        .map(|_| Affine::<PallasConfig>::rand(&mut rng))
        .collect::<Vec<_>>();
    for height in 1..=MAX_HEIGHT {
        let tree = CurveTree::<L, 1, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &params,
            Some(height as usize),
        );
        let root = tree.root_node();
        assert_eq!(root.height(), height);
        assert_eq!(root.is_even(), height % 2 == 0);
        root.check_height().unwrap();
    }
}

#[test]
fn root_with_invalid_height_is_rejected() {
    let params = new_params();
    let mut rng = thread_rng();
    let set = (0..NUM_LEAVES)
        .map(|_| Affine::<PallasConfig>::rand(&mut rng))
        .collect::<Vec<_>>();
    for height in 1..=MAX_HEIGHT {
        let tree = CurveTree::<L, 1, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &params,
            Some(height as usize),
        );
        let root = tree.root_node();

        let mut bytes = vec![];
        root.serialize_compressed(&mut bytes).unwrap();
        let decoded =
            Root::<L, 1, PallasConfig, VestaConfig>::deserialize_compressed(&bytes[..]).unwrap();
        assert_eq!(decoded, root);

        // Parity of the height differs from the root's level, or the height is 0.
        let mut bad_heights = vec![height + 1, 0];
        if height > 1 {
            bad_heights.push(height - 1);
        }
        for bad_height in bad_heights {
            let bad_root = with_height(&root, bad_height);
            assert_invalid_root_height(bad_root.check_height());

            let mut bytes = vec![];
            bad_root.serialize_compressed(&mut bytes).unwrap();
            assert!(
                Root::<L, 1, PallasConfig, VestaConfig>::deserialize_compressed(&bytes[..])
                    .is_err()
            );
        }
    }
}

#[test]
fn single_path_length_must_match_root_height() {
    let params = new_params();
    let mut rng = thread_rng();
    let set = (0..NUM_LEAVES)
        .map(|_| Affine::<PallasConfig>::rand(&mut rng))
        .collect::<Vec<_>>();

    for height in 1..=MAX_HEIGHT {
        let tree = CurveTree::<L, 1, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &params,
            Some(height as usize),
        );
        let root = tree.root_node();
        let witness = tree.get_path_to_leaf_for_proof(1, 0).unwrap();
        assert_eq!(witness.height(), height as usize);
        witness.check_height_for_root(&root).unwrap();

        let (mut pp, mut vp) = new_provers(&params);
        let (path, _) = witness
            .select_and_rerandomize_prover_gadget_new::<_, PallasParams, VestaParams>(
                &mut pp, &mut vp, &params, &mut rng, None,
            )
            .unwrap();
        let (even_proof, odd_proof) = prove(
            pp,
            vp,
            &params.even_parameters().bp_gens,
            &params.odd_parameters().bp_gens,
            &mut rng,
        )
        .unwrap();

        // Honest path verifies.
        path.check_lengths_for_root(&root).unwrap();
        let (mut pv, mut vv) = new_verifiers();
        path.select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
            &root, &mut pv, &mut vv, &params,
        )
        .unwrap();
        verify(
            pv,
            vv,
            &even_proof,
            &odd_proof,
            &params.even_parameters().pc_gens,
            &params.even_parameters().bp_gens,
            &params.odd_parameters().pc_gens,
            &params.odd_parameters().bp_gens,
            &mut rng,
        )
        .unwrap();

        // One element more or less in any path or divisor commitment vector.
        for tampered in single_path_length_tamperings(&path) {
            for res in single_path_gadget_results(&tampered, &root, &params) {
                assert_path_length_mismatch(res);
            }
        }

        // Same parity, different height.
        let taller_root = with_height(&root, height + 2);
        for res in single_path_gadget_results(&path, &taller_root, &params) {
            assert_path_length_mismatch(res);
        }
        assert!(matches!(
            witness.check_height_for_root(&taller_root),
            Err(Error::WitnessPathHeightMismatch { .. })
        ));
        if height > 2 {
            let shorter_root = with_height(&root, height - 2);
            for res in single_path_gadget_results(&path, &shorter_root, &params) {
                assert_path_length_mismatch(res);
            }
            assert!(matches!(
                witness.check_height_for_root(&shorter_root),
                Err(Error::WitnessPathHeightMismatch { .. })
            ));
        }

        // Height parity differs from the root's level.
        let bad_root = with_height(&root, height + 1);
        for res in single_path_gadget_results(&path, &bad_root, &params) {
            assert_invalid_root_height(res);
        }
        assert_invalid_root_height(witness.check_height_for_root(&bad_root));
    }
}

#[test]
fn multi_path_length_must_match_root_height() {
    let params = new_params();
    let mut rng = thread_rng();
    let set = (0..NUM_LEAVES)
        .map(|_| Affine::<PallasConfig>::rand(&mut rng))
        .collect::<Vec<_>>();

    for height in 1..=MAX_HEIGHT {
        let tree = CurveTree::<L, M, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &params,
            Some(height as usize),
        );
        let root = tree.root_node();
        let witness = tree.get_paths_to_leaves(&[0, 1]).unwrap();
        assert_eq!(witness.height(), height as usize);
        witness.check_height_for_root(&root).unwrap();

        let (mut pp, mut vp) = new_provers(&params);
        let (path, _) = witness
            .batched_select_and_rerandomize_prover_gadget_new::<_, PallasParams, VestaParams>(
                &mut pp, &mut vp, &params, &mut rng, None,
            )
            .unwrap();
        let (even_proof, odd_proof) = prove(
            pp,
            vp,
            &params.even_parameters().bp_gens,
            &params.odd_parameters().bp_gens,
            &mut rng,
        )
        .unwrap();

        // Honest path verifies.
        path.check_lengths_for_root_and_width_of_path(&root)
            .unwrap();
        let (mut pv, mut vv) = new_verifiers();
        path.batched_select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
            &root, &mut pv, &mut vv, &params,
        )
        .unwrap();
        verify(
            pv,
            vv,
            &even_proof,
            &odd_proof,
            &params.even_parameters().pc_gens,
            &params.even_parameters().bp_gens,
            &params.odd_parameters().pc_gens,
            &params.odd_parameters().bp_gens,
            &mut rng,
        )
        .unwrap();

        // One element more or less in any path or divisor commitment vector.
        for tampered in multi_path_length_tamperings(&path) {
            for res in multi_path_gadget_results(&tampered, &root, &params) {
                assert_path_length_mismatch(res);
            }
        }

        // More selected leaves than M.
        let mut too_many = path.clone();
        let extra = too_many.path.selected_commitments[0];
        too_many.path.selected_commitments.push(extra);
        let extra = too_many.odd_divisor_comms[0].clone();
        too_many.odd_divisor_comms.push(extra);
        for res in multi_path_gadget_results(&too_many, &root, &params) {
            assert!(matches!(
                res,
                Err(Error::MoreIndicesThanSupportedBatchSize(..))
            ));
        }

        // A path with no internal levels, as for a height-1 tree, against an odd root of height >= 3.
        if height >= 3 && height % 2 == 1 {
            let mut empty = path.clone();
            let num_indices = empty.path.selected_commitments.len();
            empty.path.even_commitments.clear();
            empty.path.odd_commitments.clear();
            empty.even_divisor_comms.clear();
            let leaf_divisors_start = empty.odd_divisor_comms.len() - num_indices;
            empty.odd_divisor_comms.drain(..leaf_divisors_start);
            for res in multi_path_gadget_results(&empty, &root, &params) {
                assert_path_length_mismatch(res);
            }
        }

        // Same parity, different height.
        let taller_root = with_height(&root, height + 2);
        for res in multi_path_gadget_results(&path, &taller_root, &params) {
            assert_path_length_mismatch(res);
        }
        assert!(matches!(
            witness.check_height_for_root(&taller_root),
            Err(Error::WitnessPathHeightMismatch { .. })
        ));

        // Height parity differs from the root's level.
        let bad_root = with_height(&root, height + 1);
        for res in multi_path_gadget_results(&path, &bad_root, &params) {
            assert_invalid_root_height(res);
        }
        assert_invalid_root_height(witness.check_height_for_root(&bad_root));
    }
}
