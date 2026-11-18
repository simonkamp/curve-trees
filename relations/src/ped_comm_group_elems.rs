//! Pedersen commitment to "curve points". Commits to elliptic curve points by committing to both their
//! coordinates. Then the knowledge of those committed points can be proved along with
//! generating a re-randomized version of each point.
//! Given points `P_i \in G` as `A = [P_0, P_1, ..., P_n]`. Commit to `A` in a Pedersen commitment of both
//! coordinates of each `P_i`, i.e. `C = PedCom(P_0.x, P_0.y, ..., P_n.x, P_n.y) = \sum_i{G_{2i}*P_i.x + G_{2i+1}*P_i.y}`
//! where `C \in H` where `G, H` are on 2 curves which form a 2-cycle (base field of one equals scalar
//! field of other).
//!
//! 1. Prover randomizes each `P_i` to get `A_r = [{P_r}_0, {P_r}_1, ..., {P_r}_n]` where `A_r[i] = {P_r}_i = P_i + r_i*B` where
//! `B \in G` and `r_i` is chosen randomly.
//! 2. Prover proves `\forall i, P_i \in G`, i.e. `P_i.x, P_i.y` are x and y coordinates of a point which lies in group `G`.
//! 3. Prover proves `\forall i, A_r[i] = A[i] + r_i*B = P_i + r_i*B`
//!
//! Both coordinates are committed, which pins `P_i`. Curve trees commit only `(P_i + delta).x`, leaving the
//! y-sign free so the prover can re-randomize `-(P_i + delta)` and output a re-randomization of
//! `-P_i - 2*delta`. The `delta` shift approach of the curve tree paper does not work for points where
//! prover does not need to know the opening of points. `P_i` being the identity is rejected as `(0, 0)`
//! is not on the curve.
//!
//! ## Selective Dual Re-Randomization
//!
//! The `prove` and `verify` functions support selective dual re-randomization via `shared_dlog_indices: &BTreeSet<usize>`:
//!
//! ### For indices in the set
//! - Produces 2 re-randomized points using same blinding with different generators:
//!   - Primary: `P_i + B_blinding * r_i`
//!   - Secondary: `P_i + B * r_i`
//! - Uses `discrete_log_blinding_and_dlog` (mixed proof with shared scalar)
//!
//! ### For indices not in the set
//! - Produces 1 re-randomized point: `P_i + B_blinding * r_i`
//! - Uses standard `discrete_log_blinding`
//!
//! ## Example Usage
//!
//! ```rust,ignore
//! // Mixed mode: indices 0 and 2 get dual points, others get single points
//! let shared_dlog_indices: BTreeSet<usize> = [0, 2].into_iter().collect();
//! let (re_randomized, comms) = prove(..., parameters, bp_gens, &shared_dlog_indices)?;
//!
//! // re_randomized.primary: Vec of primary points (always present, one per input)
//! // re_randomized.secondary: BTreeMap with secondary points only for indices {0, 2}
//!
//! verify(..., &re_randomized, &comms, parameters, &shared_dlog_indices)?;
//! ```

use crate::error::Error;
use crate::parameters::SingleLayerProofParametersNew;
use crate::prover::{estimate_divisor_chunk_len, ped_comm_estimated_mult_gates};
use ark_dlog_gadget::dlog::{
    commit_witness_chunks_given_chunk_len_verifier, commit_witness_chunks_prover,
    commit_witness_chunks_prover_multi_point, commit_witness_chunks_verifier_multi_point,
    create_divisor_and_decomposition, create_divisor_and_decomposition_multi_point,
    discrete_log_blinding_and_dlog_given_challenge, discrete_log_blinding_given_challenge,
    discrete_log_challenge, DiscreteLogParameters, DivisorComms,
};
use ark_dlog_gadget::utils::CurveSpec;
use ark_ec::scalar_mul::BatchMulPreprocessing;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    collections::{BTreeMap, BTreeSet},
    format,
    string::ToString,
    vec::Vec,
};
use bulletproofs::r1cs::constraint_system::constrain_lc_with_scalar;
use bulletproofs::r1cs::{ConstraintSystem, Prover, Variable, Verifier};
use bulletproofs::BulletproofGens;
use dock_crypto_utils::msm::multiply_field_elems_with_same_group_elem;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use zeroize::Zeroize;

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReRandomizedPoints<P: SWCurveConfig> {
    /// `points[i] + B_blinding * blindings[i]`
    pub re_randomized_points: Vec<Affine<P>>,
    /// `B * blindings[i]` for indices of the map
    pub blindings_with_different_gen: BTreeMap<u32, Affine<P>>,
}

impl<P: SWCurveConfig> ReRandomizedPoints<P> {
    pub fn len(&self) -> usize {
        self.re_randomized_points.len()
    }

    pub fn is_empty(&self) -> bool {
        self.re_randomized_points.is_empty()
    }
}

const RE_RANDOMIZED_POINTS: &'static [u8; 20] = b"re_randomized_points";
const PUBLIC_SUFFIX: &'static [u8; 13] = b"public_suffix";

/// Fewest scalars for which a `BatchMulPreprocessing` table beats one scalar multiplication each.
const MIN_SCALARS_FOR_FIXED_BASE_TABLE: usize = 32;

/// For indices in `shared_dlog_indices`, produces 2 re-randomized points using same blinding with different generators.
/// For other indices, produces 1 re-randomized point.
pub fn prove<
    R: CryptoRngCore,
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<ScalarField = Fs> + Copy,
    P1: DivisorCurve<BaseField = Fs, ScalarField = Fb> + Copy,
    Parameters: DiscreteLogParameters,
>(
    rng: &mut R,
    prover: &mut Prover<MerlinTranscript, Affine<P0>>,
    points: &[Affine<P1>],
    re_randomized_comm: &Affine<P0>,
    blinding_of_comm: P0::ScalarField,
    blindings_for_points: &[P1::ScalarField],
    parameters: &SingleLayerProofParametersNew<P1, Parameters>,
    bp_gens: &BulletproofGens<Affine<P0>>,
    shared_dlog_indices: &BTreeSet<usize>,
    a_l_estimate: Option<u16>,
) -> Result<(ReRandomizedPoints<P1>, Vec<DivisorComms<Affine<P0>>>), Error> {
    prove_given_public_suffix(
        rng,
        prover,
        points,
        re_randomized_comm,
        &[],
        blinding_of_comm,
        blindings_for_points,
        parameters,
        bp_gens,
        shared_dlog_indices,
        a_l_estimate,
    )
}

/// Same as [`prove`] but `re_randomized_comm` opens to `[points[0].x, points[0].y, ..., points[n].x, points[n].y] || public_suffix`
/// and each suffix coordinate is constrained to equal its public value. The opened dimension is `2 * points.len() + public_suffix.len()`.
/// `public_suffix` is added to the transcript.
pub fn prove_given_public_suffix<
    R: CryptoRngCore,
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<ScalarField = Fs> + Copy,
    P1: DivisorCurve<BaseField = Fs, ScalarField = Fb> + Copy,
    Parameters: DiscreteLogParameters,
>(
    rng: &mut R,
    prover: &mut Prover<MerlinTranscript, Affine<P0>>,
    points: &[Affine<P1>],
    re_randomized_comm: &Affine<P0>,
    public_suffix: &[Fs],
    blinding_of_comm: P0::ScalarField,
    blindings_for_points: &[P1::ScalarField],
    parameters: &SingleLayerProofParametersNew<P1, Parameters>,
    bp_gens: &BulletproofGens<Affine<P0>>,
    shared_dlog_indices: &BTreeSet<usize>,
    a_l_estimate: Option<u16>,
) -> Result<(ReRandomizedPoints<P1>, Vec<DivisorComms<Affine<P0>>>), Error> {
    let size = points.len();
    if blindings_for_points.len() != size {
        return Err(Error::MismatchedSize(blindings_for_points.len(), size));
    }
    let chunk_len = estimate_divisor_chunk_len::<Parameters>(a_l_estimate.map_or_else(
        || ped_comm_estimated_mult_gates(size, shared_dlog_indices.len()),
        |a| a as usize,
    ));

    // [points[0].x, points[0].y, ..., points[n].x, points[n].y] || public_suffix
    let mut coords = Vec::with_capacity(2 * size + public_suffix.len());
    for p in points {
        let (x, y) = p.xy().ok_or_else(|| Error::PointCantBeZero)?;
        coords.push(x);
        coords.push(y);
    }
    coords.extend_from_slice(public_suffix);

    let blinding_base = parameters.sl_params.pc_gens.B_blinding.into_group();
    let mut blinders_b_blinding =
        multiply_field_elems_with_same_group_elem(blinding_base, blindings_for_points);

    // `points[i] + B_blinding * blindings[i]`
    let mut re_randomized_points = Vec::with_capacity(size);
    for i in 0..size {
        re_randomized_points.push(points[i] + blinders_b_blinding[i]);
    }
    let re_randomized_points = Projective::normalize_batch(&re_randomized_points);

    Zeroize::zeroize(&mut blinders_b_blinding);

    // compute blindings using same blinding but different generator, `B * blindings[i]`
    let other_base = parameters.sl_params.pc_gens.B.into_group();
    // `i` -> `B * blindings[i]` for `i` in `shared_dlog_indices`
    let mut blinding_points = BTreeMap::new();

    let shared_blindings = if shared_dlog_indices.len() < MIN_SCALARS_FOR_FIXED_BASE_TABLE {
        shared_dlog_indices
            .iter()
            .map(|&idx| other_base * blindings_for_points[idx])
            .collect::<Vec<_>>()
    } else {
        let pre = BatchMulPreprocessing::new(other_base, shared_dlog_indices.len());
        shared_dlog_indices
            .iter()
            .map(|&idx| pre.windowed_mul(&blindings_for_points[idx]))
            .collect::<Vec<_>>()
    };
    let shared_blinding_points = Projective::normalize_batch(&shared_blindings);
    for (&idx, pt) in shared_dlog_indices.iter().zip(shared_blinding_points) {
        blinding_points.insert(idx as u32, pt);
    }

    let re_randomized_points = ReRandomizedPoints {
        re_randomized_points,
        blindings_with_different_gen: blinding_points,
    };

    let coord_vars = prover_commit(
        prover,
        re_randomized_comm,
        blinding_of_comm,
        &coords,
        &re_randomized_points,
    );
    prover.transcript().append(PUBLIC_SUFFIX, &public_suffix);

    constrain_public_suffix(prover, &coord_vars[2 * size..], public_suffix);

    let cs = CurveSpec {
        a: P1::COEFF_A,
        b: P1::COEFF_B,
    };

    // Commit all witnesses
    let mut all_comms = Vec::with_capacity(size);
    let mut blinds_single = BTreeMap::new();
    let mut blinds_multi = BTreeMap::new();

    let gen_table_refs = [&parameters.table_b_blinding, &parameters.table_b];

    for i in 0..size {
        if shared_dlog_indices.contains(&i) {
            let witness = create_divisor_and_decomposition_multi_point::<_, P1, Parameters>(
                &gen_table_refs,
                -blindings_for_points[i],
            )?;
            let (comm_divisor, _, blinds) =
                commit_witness_chunks_prover_multi_point::<_, _, _, Parameters>(
                    rng, prover, &witness, chunk_len, bp_gens,
                )?;
            all_comms.push(comm_divisor);
            blinds_multi.insert(i, blinds);
        } else {
            let witness = create_divisor_and_decomposition::<_, P1, Parameters>(
                &parameters.table_b_blinding,
                -blindings_for_points[i],
            )?;
            let (comm_divisor, _, blind) = commit_witness_chunks_prover::<_, _, _, Parameters>(
                rng, prover, &witness, chunk_len, bp_gens,
            )?;
            all_comms.push(comm_divisor);
            blinds_single.insert(i, blind);
        }
    }

    let (challenge, challenge_gen) = discrete_log_challenge(
        prover,
        &cs,
        &[&parameters.table_b_blinding, &parameters.table_b],
    )?;

    // Enforce constraints
    for i in 0..size {
        let x_var = coord_vars[2 * i];
        let y_var = coord_vars[2 * i + 1];

        let (re_rand_x_var, re_rand_y_var) = re_randomized_points.re_randomized_points[i]
            .xy()
            .ok_or_else(|| Error::PointCantBeZero)?;

        if shared_dlog_indices.contains(&i) {
            let (other_x_var, other_y_var) = re_randomized_points
                .blindings_with_different_gen
                .get(&(i as u32))
                .unwrap()
                .xy()
                .ok_or_else(|| Error::PointCantBeZero)?;
            discrete_log_blinding_and_dlog_given_challenge(
                prover,
                (x_var, y_var),
                blinds_multi.remove(&i).unwrap(),
                (re_rand_x_var, re_rand_y_var),
                (other_x_var, other_y_var),
                &cs,
                &challenge,
                &challenge_gen[0],
                &challenge_gen[1],
            )?;
        } else {
            discrete_log_blinding_given_challenge(
                prover,
                (x_var, y_var),
                *blinds_single.remove(&i).unwrap(),
                (re_rand_x_var, re_rand_y_var),
                &cs,
                &challenge,
                &challenge_gen[0],
            );
        }
    }

    Ok((re_randomized_points, all_comms))
}

pub fn verify<
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<ScalarField = Fs> + Copy,
    P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Parameters: DiscreteLogParameters,
>(
    verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
    re_randomized_comm: Affine<P0>,
    re_randomized_points: &ReRandomizedPoints<P1>,
    comms: &[DivisorComms<Affine<P0>>],
    parameters: &SingleLayerProofParametersNew<P1, Parameters>,
    shared_dlog_indices: &BTreeSet<usize>,
    a_l_estimate: Option<u16>,
) -> Result<(), Error> {
    verify_given_public_suffix(
        verifier,
        re_randomized_comm,
        &[],
        re_randomized_points,
        comms,
        parameters,
        shared_dlog_indices,
        a_l_estimate,
    )
}

/// Same as [`verify`] but `re_randomized_comm` is opened at dimension `2 * re_randomized_points.len() + public_suffix.len()`
/// and the coordinates after the points are constrained to equal `public_suffix`. `public_suffix` is added to the transcript.
pub fn verify_given_public_suffix<
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<ScalarField = Fs> + Copy,
    P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Parameters: DiscreteLogParameters,
>(
    verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
    re_randomized_comm: Affine<P0>,
    public_suffix: &[Fs],
    re_randomized_points: &ReRandomizedPoints<P1>,
    comms: &[DivisorComms<Affine<P0>>],
    parameters: &SingleLayerProofParametersNew<P1, Parameters>,
    shared_dlog_indices: &BTreeSet<usize>,
    a_l_estimate: Option<u16>,
) -> Result<(), Error> {
    let size = re_randomized_points.len();

    if comms.len() != size {
        return Err(Error::MismatchedSize(comms.len(), size));
    }

    // Defense in depth: Dont allow extra keys in re_randomized_points.blindings_with_different_gen as
    // verifier might (which it should since its prover controlled) use keys of re_randomized_points.blindings_with_different_gen
    // for other than verification
    if re_randomized_points.blindings_with_different_gen.len() != shared_dlog_indices.len()
        || !shared_dlog_indices.iter().all(|i| {
            re_randomized_points
                .blindings_with_different_gen
                .contains_key(&(*i as u32))
                && *i < size
        })
    {
        return Err(Error::MalformedProofInput(
            "blindings_with_different_gen keys must equal the keys of shared_dlog_indices"
                .to_string(),
        ));
    }

    let chunk_len = estimate_divisor_chunk_len::<Parameters>(a_l_estimate.map_or_else(
        || ped_comm_estimated_mult_gates(size, shared_dlog_indices.len()),
        |a| a as usize,
    ));

    // Commit to both coordinates of the original points and the public suffix
    let coord_vars = verifier.commit_vec(2 * size + public_suffix.len(), re_randomized_comm);

    verifier
        .transcript()
        .append(RE_RANDOMIZED_POINTS, re_randomized_points);
    verifier.transcript().append(PUBLIC_SUFFIX, &public_suffix);

    constrain_public_suffix(verifier, &coord_vars[2 * size..], public_suffix);

    let cs = CurveSpec {
        a: P1::COEFF_A,
        b: P1::COEFF_B,
    };

    let mut blinds_single = BTreeMap::new();
    let mut blinds_multi = BTreeMap::new();

    for (i, comm) in comms.iter().enumerate() {
        if shared_dlog_indices.contains(&i) {
            let blinds = commit_witness_chunks_verifier_multi_point::<_, _, Parameters>(
                verifier, comm, chunk_len, 2,
            )?;
            blinds_multi.insert(i, blinds);
        } else {
            let blind = commit_witness_chunks_given_chunk_len_verifier::<_, _, Parameters>(
                verifier, comm, chunk_len,
            )?;
            blinds_single.insert(i, blind);
        }
    }

    let (challenge, challenge_gen) = discrete_log_challenge(
        verifier,
        &cs,
        &[&parameters.table_b_blinding, &parameters.table_b],
    )?;

    // Enforce constraints
    for i in 0..size {
        let x_var = coord_vars[2 * i];
        let y_var = coord_vars[2 * i + 1];

        let (re_rand_x_var, re_rand_y_var) = re_randomized_points.re_randomized_points[i]
            .xy()
            .ok_or_else(|| Error::PointCantBeZero)?;

        // unwrap on blinds_multi is fine as its created in this function above
        if shared_dlog_indices.contains(&i) {
            let blinds = blinds_multi.remove(&i).unwrap();
            let (other_x_var, other_y_var) = re_randomized_points
                .blindings_with_different_gen
                .get(&(i as u32))
                .ok_or_else(|| Error::MalformedProofInput(format!("Missing point at index {i}")))?
                .xy()
                .ok_or_else(|| Error::PointCantBeZero)?;
            discrete_log_blinding_and_dlog_given_challenge(
                verifier,
                (x_var, y_var),
                blinds,
                (re_rand_x_var, re_rand_y_var),
                (other_x_var, other_y_var),
                &cs,
                &challenge,
                &challenge_gen[0],
                &challenge_gen[1],
            )?;
        } else {
            let blind = blinds_single.remove(&i).unwrap();
            discrete_log_blinding_given_challenge(
                verifier,
                (x_var, y_var),
                *blind,
                (re_rand_x_var, re_rand_y_var),
                &cs,
                &challenge,
                &challenge_gen[0],
            );
        }
    }

    Ok(())
}

/// Constrains each of `suffix_vars` to equal the corresponding element of `public_suffix`.
fn constrain_public_suffix<Fs: PrimeField, CS: ConstraintSystem<Fs>>(
    cs: &mut CS,
    suffix_vars: &[Variable<Fs>],
    public_suffix: &[Fs],
) {
    for (var, value) in suffix_vars.iter().zip(public_suffix) {
        constrain_lc_with_scalar(cs, (*var).into(), *value);
    }
}

/// This is just to allow mocking
#[cfg_attr(
    all(test, feature = "nightly_mocking_tests"),
    mocktopus::macros::mockable
)]
fn prover_commit<
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<ScalarField = Fs> + Copy,
    P1: DivisorCurve<BaseField = Fs, ScalarField = Fb> + Copy,
>(
    prover: &mut Prover<MerlinTranscript, Affine<P0>>,
    re_randomized_comm: &Affine<P0>,
    blinding_of_comm: P0::ScalarField,
    coords: &[Fs],
    re_randomized_points: &ReRandomizedPoints<P1>,
) -> Vec<Variable<Fs>> {
    // Allocate commitment to both coordinates of all points
    let coord_vars = prover.vars_for_committed_vec(re_randomized_comm, coords, blinding_of_comm);

    prover
        .transcript()
        .append(RE_RANDOMIZED_POINTS, re_randomized_points);
    coord_vars
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::Error;
    use crate::parameters::{SelRerandParameters, SingleLayerProofParametersNew};
    use ark_ec_divisors::curves::vesta::VestaParams;
    use ark_ff::Zero;
    use ark_pallas::{Fq as PallasBase, PallasConfig};
    use ark_std::UniformRand;
    use ark_vesta::{Fq as VestaBase, VestaConfig};
    use bulletproofs::r1cs::{Prover, Verifier};
    use dock_crypto_utils::transcript::MerlinTranscript;
    use std::collections::BTreeSet;

    #[test]
    fn negative_cases() {
        let mut rng = rand::thread_rng();

        let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(1 << 13, 1 << 13)
            .expect("Failed to create SelRerandParameters");

        let odd_proof_params =
            SingleLayerProofParametersNew::<VestaConfig, VestaParams>::from_single_layer_params(
                sr_params.odd_parameters.clone(),
            );

        let nesting_size = 2;
        let nested: Vec<Affine<VestaConfig>> = (0..nesting_size)
            .map(|_| Affine::<VestaConfig>::rand(&mut rng))
            .collect();
        let coords: Vec<VestaBase> = nested
            .iter()
            .flat_map(|n| {
                let (x, y) = n.xy().unwrap();
                [x, y]
            })
            .collect();
        let re_randomized_comm =
            sr_params
                .even_parameters
                .commit(coords.as_slice(), VestaBase::zero(), 0);
        let blinding_of_comm = VestaBase::rand(&mut rng);
        let blindings_for_points: Vec<PallasBase> = (0..nesting_size)
            .map(|_| PallasBase::rand(&mut rng))
            .collect();
        let shared_dlog_indices: BTreeSet<usize> = [0].into_iter().collect();

        let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
        let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
            Prover::new(&sr_params.even_parameters.pc_gens, transcript);

        let (mut re_randomized_nested, comms) =
            prove::<_, _, _, PallasConfig, VestaConfig, VestaParams>(
                &mut rng,
                &mut pallas_prover,
                &nested,
                &re_randomized_comm,
                blinding_of_comm,
                &blindings_for_points,
                &odd_proof_params,
                &sr_params.even_parameters.bp_gens,
                &shared_dlog_indices,
                None,
            )
            .expect("Failed to prove");

        // unexpected extra key in blindings_with_different_gen fails verification
        {
            let mut rr = re_randomized_nested.clone();
            rr.blindings_with_different_gen
                .insert(1, Affine::<VestaConfig>::rand(&mut rng));

            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_verifier: Verifier<_, Affine<PallasConfig>> = Verifier::new(transcript);

            let result = verify::<_, _, PallasConfig, VestaConfig, VestaParams>(
                &mut pallas_verifier,
                re_randomized_comm,
                &rr,
                &comms,
                &odd_proof_params,
                &shared_dlog_indices,
                None,
            );

            assert!(
                matches!(result, Err(Error::MalformedProofInput(_))),
                "expected MalformedProofInput for extra key, got: {result:?}",
            );
        }

        // point at infinity fails verification
        re_randomized_nested.re_randomized_points[0] = Affine::<VestaConfig>::identity();

        let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
        let mut pallas_verifier: Verifier<_, Affine<PallasConfig>> = Verifier::new(transcript);

        let result = verify::<_, _, PallasConfig, VestaConfig, VestaParams>(
            &mut pallas_verifier,
            re_randomized_comm,
            &re_randomized_nested,
            &comms,
            &odd_proof_params,
            &shared_dlog_indices,
            None,
        );

        assert!(
            matches!(result, Err(Error::PointCantBeZero)),
            "expected PointCantBeZero, got: {result:?}",
        );
    }

    #[test]
    fn negative_point_is_rejected() {
        // Using -P instead of P (since same x-coordinate) should get rejected.
        let mut rng = rand::thread_rng();

        let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(1 << 13, 1 << 13)
            .expect("Failed to create SelRerandParameters");

        let odd_proof_params =
            SingleLayerProofParametersNew::<VestaConfig, VestaParams>::from_single_layer_params(
                sr_params.odd_parameters.clone(),
            );

        let nesting_size = 2;
        let nested: Vec<Affine<VestaConfig>> = (0..nesting_size)
            .map(|_| Affine::<VestaConfig>::rand(&mut rng))
            .collect();
        let coords_of = |points: &[Affine<VestaConfig>]| -> Vec<VestaBase> {
            points
                .iter()
                .flat_map(|n| {
                    let (x, y) = n.xy().unwrap();
                    [x, y]
                })
                .collect()
        };
        let blinding_of_comm = VestaBase::rand(&mut rng);
        let re_randomized_comm =
            sr_params
                .even_parameters
                .commit(coords_of(&nested).as_slice(), blinding_of_comm, 0);

        let reflected: Vec<Affine<VestaConfig>> = nested.iter().map(|n| -*n).collect();
        for i in 0..nesting_size {
            assert_eq!(reflected[i].x, nested[i].x);
        }
        assert_ne!(
            sr_params.even_parameters.commit(
                coords_of(&reflected).as_slice(),
                VestaBase::zero(),
                0
            ),
            re_randomized_comm,
        );

        let blindings_for_points: Vec<PallasBase> = (0..nesting_size)
            .map(|_| PallasBase::rand(&mut rng))
            .collect();
        let shared_dlog_indices: BTreeSet<usize> = [0].into_iter().collect();

        let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
        let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
            Prover::new(&sr_params.even_parameters.pc_gens, transcript);

        // Prove for the reflected points against the commitment to the original ones
        let (re_randomized_nested, comms) =
            prove::<_, _, _, PallasConfig, VestaConfig, VestaParams>(
                &mut rng,
                &mut pallas_prover,
                &reflected,
                &re_randomized_comm,
                blinding_of_comm,
                &blindings_for_points,
                &odd_proof_params,
                &sr_params.even_parameters.bp_gens,
                &shared_dlog_indices,
                None,
            )
            .unwrap();

        let proof = pallas_prover
            .prove_with_rng(&sr_params.even_parameters.bp_gens, &mut rng)
            .unwrap();

        let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
        let mut pallas_verifier: Verifier<_, Affine<PallasConfig>> = Verifier::new(transcript);

        verify::<_, _, PallasConfig, VestaConfig, VestaParams>(
            &mut pallas_verifier,
            re_randomized_comm,
            &re_randomized_nested,
            &comms,
            &odd_proof_params,
            &shared_dlog_indices,
            None,
        )
        .unwrap();

        let result = pallas_verifier.verify(
            &proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
        );
        assert!(
            result.is_err(),
            "expected verify to reject the reflected point, got: {result:?}",
        );
    }

    #[test]
    fn public_suffix_is_constrained() {
        // The commitment holds the points' coordinates followed by a suffix. An invalid suffix is
        // rejected.
        let mut rng = rand::thread_rng();

        let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(1 << 13, 1 << 13)
            .expect("Failed to create SelRerandParameters");

        let odd_proof_params =
            SingleLayerProofParametersNew::<VestaConfig, VestaParams>::from_single_layer_params(
                sr_params.odd_parameters.clone(),
            );

        let nesting_size = 2;
        let nested: Vec<Affine<VestaConfig>> = (0..nesting_size)
            .map(|_| Affine::<VestaConfig>::rand(&mut rng))
            .collect();
        let real_suffix = [
            VestaBase::rand(&mut rng),
            VestaBase::rand(&mut rng),
            VestaBase::zero(),
            VestaBase::from(1u64),
        ];
        let mut coords: Vec<VestaBase> = nested
            .iter()
            .flat_map(|n| {
                let (x, y) = n.xy().unwrap();
                [x, y]
            })
            .collect();
        coords.extend_from_slice(&real_suffix);
        let blinding_of_comm = VestaBase::rand(&mut rng);
        let re_randomized_comm =
            sr_params
                .even_parameters
                .commit(coords.as_slice(), blinding_of_comm, 0);
        let shared_dlog_indices: BTreeSet<usize> = [0].into_iter().collect();

        let mut check = |expected_suffix: &[VestaBase]| {
            let blindings_for_points: Vec<PallasBase> = (0..nesting_size)
                .map(|_| PallasBase::rand(&mut rng))
                .collect();

            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
                Prover::new(&sr_params.even_parameters.pc_gens, transcript);
            let (re_randomized_nested, comms) =
                prove_given_public_suffix::<_, _, _, PallasConfig, VestaConfig, VestaParams>(
                    &mut rng,
                    &mut pallas_prover,
                    &nested,
                    &re_randomized_comm,
                    &real_suffix,
                    blinding_of_comm,
                    &blindings_for_points,
                    &odd_proof_params,
                    &sr_params.even_parameters.bp_gens,
                    &shared_dlog_indices,
                    None,
                )
                .unwrap();
            let proof = pallas_prover
                .prove_with_rng(&sr_params.even_parameters.bp_gens, &mut rng)
                .unwrap();

            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_verifier: Verifier<_, Affine<PallasConfig>> = Verifier::new(transcript);
            verify_given_public_suffix::<_, _, PallasConfig, VestaConfig, VestaParams>(
                &mut pallas_verifier,
                re_randomized_comm,
                expected_suffix,
                &re_randomized_nested,
                &comms,
                &odd_proof_params,
                &shared_dlog_indices,
                None,
            )
            .unwrap();
            pallas_verifier.verify(
                &proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            )
        };

        check(&real_suffix).unwrap();

        assert!(check(&[VestaBase::zero(); 4]).is_err());

        let mut wrong_suffix = real_suffix;
        wrong_suffix[3] = real_suffix[2].clone();
        assert!(check(&wrong_suffix).is_err());

        let short_suffix = real_suffix[..3].as_ref();
        assert!(check(short_suffix).is_err());
    }

    // Run as cargo +nightly nextest run --features nightly_mocking_tests mocking_tests

    #[cfg(feature = "nightly_mocking_tests")]
    mod mocking_tests {
        use mocktopus::mocking::{MockResult, Mockable};

        use super::*;

        fn clear_mocks() {
            prover_commit::<PallasBase, VestaBase, PallasConfig, VestaConfig>.clear_mock();
        }

        struct MockGuard;

        impl MockGuard {
            fn new() -> Self {
                Self
            }
        }

        impl Drop for MockGuard {
            fn drop(&mut self) {
                clear_mocks();
            }
        }

        fn honest_rerand(
            points: &[Affine<VestaConfig>],
            parameters: &SingleLayerProofParametersNew<VestaConfig, VestaParams>,
            blindings: &[PallasBase],
            shared: &BTreeSet<usize>,
        ) -> ReRandomizedPoints<VestaConfig> {
            let other_base = parameters.sl_params.pc_gens.B.into_group();
            let mut blinding_points = BTreeMap::new();
            for idx in shared.iter() {
                blinding_points.insert(*idx as u32, (other_base * blindings[*idx]).into_affine());
            }
            let blinding_base = parameters.sl_params.pc_gens.B_blinding.into_group();
            let blinders = multiply_field_elems_with_same_group_elem(blinding_base, blindings);
            let re_randomized_points = (0..blindings.len())
                .map(|i| points[i].into_group() + blinders[i])
                .collect::<Vec<_>>();
            let re_randomized_points = CurveGroup::normalize_batch(&re_randomized_points);
            ReRandomizedPoints {
                re_randomized_points,
                blindings_with_different_gen: blinding_points,
            }
        }

        #[test]
        fn wrong_re_randomized_points_fails() {
            let _guard = MockGuard::new();
            let mut rng = rand::thread_rng();

            let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(1 << 13, 1 << 13)
                .expect("Failed to create SelRerandParameters");

            let odd_proof_params =
                SingleLayerProofParametersNew::<VestaConfig, VestaParams>::from_single_layer_params(
                    sr_params.odd_parameters.clone(),
                );

            let shared_dlog_indices: BTreeSet<usize> = [0].into_iter().collect();

            // Honest data: points [A, B] that the prover internally works with
            let nested: Vec<Affine<VestaConfig>> = (0..2)
                .map(|_| Affine::<VestaConfig>::rand(&mut rng))
                .collect();
            let coords: Vec<VestaBase> = nested
                .iter()
                .flat_map(|n| {
                    let (x, y) = n.xy().unwrap();
                    [x, y]
                })
                .collect();
            let re_randomized_comm =
                sr_params
                    .even_parameters
                    .commit(coords.as_slice(), VestaBase::zero(), 0);
            let blinding_of_comm = VestaBase::rand(&mut rng);
            let blindings_for_points: Vec<PallasBase> =
                (0..2).map(|_| PallasBase::rand(&mut rng)).collect();

            // Malicious data: different points [C, D] used in transcript and verify
            let malicious_nested: Vec<Affine<VestaConfig>> = (0..2)
                .map(|_| Affine::<VestaConfig>::rand(&mut rng))
                .collect();
            let malicious_coords: Vec<VestaBase> = malicious_nested
                .iter()
                .flat_map(|n| {
                    let (x, y) = n.xy().unwrap();
                    [x, y]
                })
                .collect();
            let malicious_re_rand_comm =
                sr_params
                    .even_parameters
                    .commit(malicious_coords.as_slice(), VestaBase::zero(), 0);
            let malicious_blinding_of_comm = VestaBase::rand(&mut rng);
            let malicious_blindings: Vec<PallasBase> =
                (0..2).map(|_| PallasBase::rand(&mut rng)).collect();
            let malicious_rr = honest_rerand(
                &malicious_nested,
                &odd_proof_params,
                &malicious_blindings,
                &shared_dlog_indices,
            );

            // Mock: use the malicious data for `vars_for_committed_vec` and transcript,
            // ignoring the honest arguments that `prove` passes. This makes the prover's
            // transcript consistent with what the verifier will see, while the constraint
            // system is built for [A, B].
            prover_commit::<PallasBase, VestaBase, PallasConfig, VestaConfig>.mock_safe({
                let mal_rr = malicious_rr.clone();
                let mal_comm = malicious_re_rand_comm;
                let mal_coords = malicious_coords.clone();
                let mal_blinding = malicious_blinding_of_comm;
                move |prover, _comm, _blinding, _coords, _re_rand| {
                    let coord_vars =
                        prover.vars_for_committed_vec(&mal_comm, &mal_coords, mal_blinding);
                    prover.transcript().append(RE_RANDOMIZED_POINTS, &mal_rr);
                    MockResult::Return(coord_vars)
                }
            });

            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
                Prover::new(&sr_params.even_parameters.pc_gens, transcript);

            let (_re_randomized_nested, comms) =
                prove::<_, _, _, PallasConfig, VestaConfig, VestaParams>(
                    &mut rng,
                    &mut pallas_prover,
                    &nested,
                    &re_randomized_comm,
                    blinding_of_comm,
                    &blindings_for_points,
                    &odd_proof_params,
                    &sr_params.even_parameters.bp_gens,
                    &shared_dlog_indices,
                    None,
                )
                .expect("Failed to prove");

            let proof = pallas_prover
                .prove_with_rng(&sr_params.even_parameters.bp_gens, &mut rng)
                .unwrap();

            // Verify with the malicious data: commitment, rerandomized points, and
            // blindings-with-different-gen are all from [C, D]. The comms from `prove`
            // encode [A, B]'s blindings, so the constraint system is mismatched.
            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_verifier: Verifier<_, Affine<PallasConfig>> = Verifier::new(transcript);

            verify::<_, _, PallasConfig, VestaConfig, VestaParams>(
                &mut pallas_verifier,
                malicious_re_rand_comm,
                &malicious_rr,
                &comms,
                &odd_proof_params,
                &shared_dlog_indices,
                None,
            )
            .unwrap();

            let result = pallas_verifier.verify(
                &proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            );
            assert!(
                result.is_err(),
                "expected verify to reject wrong re_randomized_points, got: {result:?}",
            );
        }

        #[test]
        fn wrong_blindings_with_different_gen_fails() {
            let _guard = MockGuard::new();
            let mut rng = rand::thread_rng();

            let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(1 << 13, 1 << 13)
                .expect("Failed to create SelRerandParameters");

            let odd_proof_params =
                SingleLayerProofParametersNew::<VestaConfig, VestaParams>::from_single_layer_params(
                    sr_params.odd_parameters.clone(),
                );

            let shared_dlog_indices: BTreeSet<usize> = [0].into_iter().collect();

            // Honest data: points [A, B] that the prover internally works with
            let nested: Vec<Affine<VestaConfig>> = (0..2)
                .map(|_| Affine::<VestaConfig>::rand(&mut rng))
                .collect();
            let coords: Vec<VestaBase> = nested
                .iter()
                .flat_map(|n| {
                    let (x, y) = n.xy().unwrap();
                    [x, y]
                })
                .collect();
            let re_randomized_comm =
                sr_params
                    .even_parameters
                    .commit(coords.as_slice(), VestaBase::zero(), 0);
            let blinding_of_comm = VestaBase::rand(&mut rng);
            let blindings_for_points: Vec<PallasBase> =
                (0..2).map(|_| PallasBase::rand(&mut rng)).collect();

            // Malicious data: different points [C, D] used in transcript and verify
            let malicious_nested: Vec<Affine<VestaConfig>> = (0..2)
                .map(|_| Affine::<VestaConfig>::rand(&mut rng))
                .collect();
            let malicious_coords: Vec<VestaBase> = malicious_nested
                .iter()
                .flat_map(|n| {
                    let (x, y) = n.xy().unwrap();
                    [x, y]
                })
                .collect();
            let malicious_re_rand_comm =
                sr_params
                    .even_parameters
                    .commit(malicious_coords.as_slice(), VestaBase::zero(), 0);
            let malicious_blinding_of_comm = VestaBase::rand(&mut rng);
            let malicious_blindings: Vec<PallasBase> =
                (0..2).map(|_| PallasBase::rand(&mut rng)).collect();
            let malicious_rr = honest_rerand(
                &malicious_nested,
                &odd_proof_params,
                &malicious_blindings,
                &shared_dlog_indices,
            );

            prover_commit::<PallasBase, VestaBase, PallasConfig, VestaConfig>.mock_safe({
                let mal_rr = malicious_rr.clone();
                let mal_comm = malicious_re_rand_comm;
                let mal_coords = malicious_coords.clone();
                let mal_blinding = malicious_blinding_of_comm;
                move |prover, _comm, _blinding, _coords, _re_rand| {
                    let coord_vars =
                        prover.vars_for_committed_vec(&mal_comm, &mal_coords, mal_blinding);
                    prover.transcript().append(RE_RANDOMIZED_POINTS, &mal_rr);
                    MockResult::Return(coord_vars)
                }
            });

            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
                Prover::new(&sr_params.even_parameters.pc_gens, transcript);

            let (_re_randomized_nested, comms) =
                prove::<_, _, _, PallasConfig, VestaConfig, VestaParams>(
                    &mut rng,
                    &mut pallas_prover,
                    &nested,
                    &re_randomized_comm,
                    blinding_of_comm,
                    &blindings_for_points,
                    &odd_proof_params,
                    &sr_params.even_parameters.bp_gens,
                    &shared_dlog_indices,
                    None,
                )
                .expect("Failed to prove");

            let proof = pallas_prover
                .prove_with_rng(&sr_params.even_parameters.bp_gens, &mut rng)
                .unwrap();

            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_verifier: Verifier<_, Affine<PallasConfig>> = Verifier::new(transcript);

            verify::<_, _, PallasConfig, VestaConfig, VestaParams>(
                &mut pallas_verifier,
                malicious_re_rand_comm,
                &malicious_rr,
                &comms,
                &odd_proof_params,
                &shared_dlog_indices,
                None,
            )
            .unwrap();

            let result = pallas_verifier.verify(
                &proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            );
            assert!(
                result.is_err(),
                "expected verify to reject wrong blindings_with_different_gen, got: {result:?}",
            );
        }

        #[test]
        fn wrong_re_randomized_comm_fails() {
            let _guard = MockGuard::new();
            let mut rng = rand::thread_rng();

            let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(1 << 13, 1 << 13)
                .expect("Failed to create SelRerandParameters");

            let odd_proof_params =
                SingleLayerProofParametersNew::<VestaConfig, VestaParams>::from_single_layer_params(
                    sr_params.odd_parameters.clone(),
                );

            let shared_dlog_indices: BTreeSet<usize> = [0].into_iter().collect();

            // Honest data: points [A, B] that the prover internally works with
            let nested: Vec<Affine<VestaConfig>> = (0..2)
                .map(|_| Affine::<VestaConfig>::rand(&mut rng))
                .collect();
            let coords: Vec<VestaBase> = nested
                .iter()
                .flat_map(|n| {
                    let (x, y) = n.xy().unwrap();
                    [x, y]
                })
                .collect();
            let re_randomized_comm =
                sr_params
                    .even_parameters
                    .commit(coords.as_slice(), VestaBase::zero(), 0);
            let blinding_of_comm = VestaBase::rand(&mut rng);
            let blindings_for_points: Vec<PallasBase> =
                (0..2).map(|_| PallasBase::rand(&mut rng)).collect();

            // Malicious data: different points [C, D] used in transcript and verify
            let malicious_nested: Vec<Affine<VestaConfig>> = (0..2)
                .map(|_| Affine::<VestaConfig>::rand(&mut rng))
                .collect();
            let malicious_coords: Vec<VestaBase> = malicious_nested
                .iter()
                .flat_map(|n| {
                    let (x, y) = n.xy().unwrap();
                    [x, y]
                })
                .collect();
            let malicious_re_rand_comm =
                sr_params
                    .even_parameters
                    .commit(malicious_coords.as_slice(), VestaBase::zero(), 0);
            let malicious_blinding_of_comm = VestaBase::rand(&mut rng);
            let malicious_blindings: Vec<PallasBase> =
                (0..2).map(|_| PallasBase::rand(&mut rng)).collect();
            let malicious_rr = honest_rerand(
                &malicious_nested,
                &odd_proof_params,
                &malicious_blindings,
                &shared_dlog_indices,
            );

            prover_commit::<PallasBase, VestaBase, PallasConfig, VestaConfig>.mock_safe({
                let mal_rr = malicious_rr.clone();
                let mal_comm = malicious_re_rand_comm;
                let mal_coords = malicious_coords.clone();
                let mal_blinding = malicious_blinding_of_comm;
                move |prover, _comm, _blinding, _coords, _re_rand| {
                    let coord_vars =
                        prover.vars_for_committed_vec(&mal_comm, &mal_coords, mal_blinding);
                    prover.transcript().append(RE_RANDOMIZED_POINTS, &mal_rr);
                    MockResult::Return(coord_vars)
                }
            });

            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
                Prover::new(&sr_params.even_parameters.pc_gens, transcript);

            let (_re_randomized_nested, comms) =
                prove::<_, _, _, PallasConfig, VestaConfig, VestaParams>(
                    &mut rng,
                    &mut pallas_prover,
                    &nested,
                    &re_randomized_comm,
                    blinding_of_comm,
                    &blindings_for_points,
                    &odd_proof_params,
                    &sr_params.even_parameters.bp_gens,
                    &shared_dlog_indices,
                    None,
                )
                .expect("Failed to prove");

            let proof = pallas_prover
                .prove_with_rng(&sr_params.even_parameters.bp_gens, &mut rng)
                .unwrap();

            let transcript = MerlinTranscript::new(b"ped_comm_group_elems_test");
            let mut pallas_verifier: Verifier<_, Affine<PallasConfig>> = Verifier::new(transcript);

            verify::<_, _, PallasConfig, VestaConfig, VestaParams>(
                &mut pallas_verifier,
                malicious_re_rand_comm,
                &malicious_rr,
                &comms,
                &odd_proof_params,
                &shared_dlog_indices,
                None,
            )
            .unwrap();

            let result = pallas_verifier.verify(
                &proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            );
            assert!(
                result.is_err(),
                "expected verify to reject wrong re_randomized_comm, got: {result:?}",
            );
        }
    }
}
