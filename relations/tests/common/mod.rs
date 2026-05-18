use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use bulletproofs::r1cs::{Prover, Verifier};
use dock_crypto_utils::transcript::MerlinTranscript;
use rand_core::CryptoRngCore;
use relations::curve_tree::Root;
use relations::curve_tree_prover::CurveTreeWitnessPath;
use relations::parameters::{SelRerandParameters, SelRerandProofParameters};
pub use relations::utils::{prove, verify};
use std::time::{Duration, Instant};

#[allow(dead_code)]
const PROOF_LABEL: &'static [u8; 22] = b"select_and_rerandomize";

#[allow(dead_code)]
pub fn check_proof<
    const L: usize,
    R: CryptoRngCore,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    rng: &mut R,
    leaf: Affine<P0>,
    path: CurveTreeWitnessPath<L, P0, P1>,
    root: &Root<L, 1, P0, P1>,
    sr_params: &SelRerandParameters<P0, P1>,
) -> (Duration, Duration) {
    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

    let start = Instant::now();
    let pallas_transcript = MerlinTranscript::new(PROOF_LABEL);
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(PROOF_LABEL);
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let (path_commitments, re_randomization_of_leaf) = path
        .select_and_rerandomize_prover_gadget(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_proof_params,
            rng,
        )
        .unwrap();

    let (pallas_proof, vesta_proof) = prove(
        pallas_prover,
        vesta_prover,
        &sr_params.even_parameters.bp_gens,
        &sr_params.odd_parameters.bp_gens,
        rng,
    )
    .unwrap();

    let proving_time = start.elapsed();

    let verifying_time = {
        let start = Instant::now();
        let pallas_transcript = MerlinTranscript::new(PROOF_LABEL);
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(PROOF_LABEL);
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
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
            rng,
        )
        .unwrap();

        assert_eq!(
            rerandomized_leaf.into_group(),
            leaf.into_group()
                + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
        );
        start.elapsed()
    };

    (proving_time, verifying_time)
}
