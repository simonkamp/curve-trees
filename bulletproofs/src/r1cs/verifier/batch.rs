use crate::errors::R1CSError;
use crate::r1cs::verifier::{bases_and_scalars, msm_check};
use crate::r1cs::VerificationTuple;
use crate::{BulletproofGens, PedersenGens};
use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::{One, Zero};
use ark_std::UniformRand;
use ark_std::{vec, vec::Vec};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use rand_core::{CryptoRng, RngCore};

#[cfg(feature = "std")]
pub fn batch_verify<C: AffineRepr>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
) -> Result<(), R1CSError> {
    let mut rng = rand::thread_rng();
    batch_verify_with_rng(verification_tuples, pc_gens, bp_gens, &mut rng)
}

pub fn batch_verify_with_rng<C: AffineRepr, R: RngCore + CryptoRng>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    rng: &mut R,
) -> Result<(), R1CSError> {
    batch_verify_core(verification_tuples, pc_gens, bp_gens, |_| {
        C::ScalarField::rand(rng)
    })
}

pub fn batch_verify_with_given_randomness<C: AffineRepr>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    randomness: C::ScalarField,
) -> Result<(), R1CSError> {
    batch_verify_core(verification_tuples, pc_gens, bp_gens, |r| randomness * r)
}

pub fn batch_verify_core_different_sizes<C: AffineRepr, R>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    new_randomness_getter: R,
) -> Result<(), R1CSError>
where
    R: FnMut(C::ScalarField) -> C::ScalarField,
{
    let (b, s) =
        bases_and_scalars_for_batch(verification_tuples, pc_gens, bp_gens, new_randomness_getter)?;

    let mega_check = C::Group::msm_unchecked(&b, &s);
    if !mega_check.is_zero() {
        return Err(R1CSError::VerificationError);
    }
    Ok(())
}

pub fn bases_and_scalars_for_batch<C: AffineRepr, R>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    mut new_randomness_getter: R,
) -> Result<(Vec<C>, Vec<C::ScalarField>), R1CSError>
where
    R: FnMut(C::ScalarField) -> C::ScalarField,
{
    let mut max_padded_n = 0;
    let mut max_proof_dep_scalars = 0;
    for vt in &verification_tuples {
        let padded_n = vt.padded_n()?;
        if padded_n > max_padded_n {
            max_padded_n = padded_n
        }
        if vt.proof_dependent_scalars.len() > max_proof_dep_scalars {
            max_proof_dep_scalars = vt.proof_dependent_scalars.len();
        }
    }
    let max_padded_n = max_padded_n as usize;

    let mut proof_points = Vec::with_capacity(max_proof_dep_scalars * verification_tuples.len());
    let mut proof_dependent_scalars =
        Vec::with_capacity(max_proof_dep_scalars * verification_tuples.len());
    let mut linear_combination = vec![C::ScalarField::zero(); (2 * max_padded_n) + 2];

    let mut random_scalar = C::ScalarField::one();

    for mut vt in verification_tuples {
        let padded_n = vt.padded_n()? as usize;
        let proof_dep_scalars = vt.proof_dependent_scalars.len();

        // length of vt.proof_independent_scalars = 2 + 2*padded_n

        proof_points.append(&mut vt.proof_dependent_points);
        // Padding
        for _ in 0..(max_proof_dep_scalars - proof_dep_scalars) {
            proof_points.push(C::zero());
        }

        random_scalar = new_randomness_getter(random_scalar);

        // Multiply all scalars
        let ps = vt
            .proof_dependent_scalars
            .into_iter()
            .map(|s| s * random_scalar);
        proof_dependent_scalars.extend(ps);
        // Padding
        for _ in 0..(max_proof_dep_scalars - proof_dep_scalars) {
            proof_dependent_scalars.push(C::ScalarField::zero());
        }

        // For B and B_blinding
        linear_combination[0] += random_scalar * vt.proof_independent_scalars[0];
        linear_combination[1] += random_scalar * vt.proof_independent_scalars[1];

        // For G
        for i in 0..padded_n {
            linear_combination[2 + i] += random_scalar * vt.proof_independent_scalars[2 + i];
        }

        // For H
        for i in 0..padded_n {
            linear_combination[2 + max_padded_n + i] +=
                random_scalar * vt.proof_independent_scalars[2 + padded_n + i];
        }
    }

    bases_and_scalars(
        proof_points,
        proof_dependent_scalars,
        linear_combination,
        max_padded_n as u32,
        pc_gens,
        bp_gens,
    )
}

pub fn batch_verify_core_same_size<C: AffineRepr, F>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    mut new_randomness_getter: F,
) -> Result<(), R1CSError>
where
    F: FnMut(C::ScalarField) -> C::ScalarField,
{
    let mut ver_iter = verification_tuples.into_iter();
    let vt = ver_iter.next().ok_or(R1CSError::NoVerificationTuple)?;
    let padded_n = vt.padded_n()?;
    let (mut proof_points, mut proof_point_scalars, mut linear_combination) = (
        vt.proof_dependent_points,
        vt.proof_dependent_scalars,
        vt.proof_independent_scalars,
    );

    let mut random_scalar = C::ScalarField::one();

    for mut vt in ver_iter {
        let expected = vt.padded_n()?;
        if padded_n != expected {
            return Err(R1CSError::IncompatibleVerificationTuple(expected, padded_n));
        }
        proof_points.append(&mut vt.proof_dependent_points);

        random_scalar = new_randomness_getter(random_scalar);

        // Multiply all scalars
        let ps = vt
            .proof_dependent_scalars
            .into_iter()
            .map(|s| s * random_scalar);
        let fps = vt
            .proof_independent_scalars
            .into_iter()
            .map(|s| s * random_scalar);

        proof_point_scalars.extend(ps);
        linear_combination = linear_combination
            .iter()
            .zip(fps)
            .map(|(a, b)| *a + b)
            .collect()
    }

    msm_check(
        proof_points,
        proof_point_scalars,
        linear_combination,
        padded_n,
        pc_gens,
        bp_gens,
    )
}

pub fn batch_verify_core<C: AffineRepr, F>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    new_randomness_getter: F,
) -> Result<(), R1CSError>
where
    F: FnMut(C::ScalarField) -> C::ScalarField,
{
    let mut vt_iter = verification_tuples.iter();
    let vt = vt_iter.next().ok_or(R1CSError::NoVerificationTuple)?;
    let padded_n = vt.padded_n()?;
    let mut same_size = true;
    for vt in vt_iter {
        if padded_n != vt.padded_n()? {
            same_size = false;
            break;
        }
    }
    if same_size {
        // println!("Same size: {}", padded_n);
        batch_verify_core_same_size(verification_tuples, pc_gens, bp_gens, new_randomness_getter)
    } else {
        // println!("Different size: {}", padded_n);
        batch_verify_core_different_sizes(
            verification_tuples,
            pc_gens,
            bp_gens,
            new_randomness_getter,
        )
    }
}

pub fn add_verification_tuples_to_rmc_0<C: AffineRepr>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    rmc: &mut RandomizedMultChecker<C>,
) -> Result<(), R1CSError> {
    if verification_tuples.len() == 0 {
        return Err(R1CSError::NoVerificationTuple);
    }
    let mut max_padded_n = 0;
    let mut max_proof_dep_scalars = 0;
    for vt in &verification_tuples {
        let padded_n = vt.padded_n()?;
        if padded_n > max_padded_n {
            max_padded_n = padded_n
        }
        if vt.proof_dependent_scalars.len() > max_proof_dep_scalars {
            max_proof_dep_scalars = vt.proof_dependent_scalars.len();
        }
    }

    // We are performing a single-party circuit proof, so party index is 0.
    let gens = bp_gens.share(0);

    if bp_gens.gens_capacity < max_padded_n {
        return Err(R1CSError::InvalidGeneratorsLength(
            bp_gens.gens_capacity,
            max_padded_n,
        ));
    }

    use core::iter;
    let fixed_points = iter::once(pc_gens.B)
        .chain(iter::once(pc_gens.B_blinding))
        .chain(gens.G(max_padded_n).copied())
        .chain(gens.H(max_padded_n).copied())
        .collect::<Vec<_>>();

    for mut vt in verification_tuples {
        let padded_n = vt.padded_n()?;
        let proof_dep_scalars = vt.proof_dependent_scalars.len();

        // length of vt.proof_independent_scalars = 2 + 2*padded_n

        let b = vt
            .proof_dependent_points
            .into_iter()
            .chain(iter::repeat(C::zero()).take(max_proof_dep_scalars - proof_dep_scalars))
            .chain(fixed_points.clone())
            .collect::<Vec<_>>();

        let mut s = Vec::with_capacity(max_proof_dep_scalars + 2 * (max_padded_n as usize) + 2);
        s.append(&mut vt.proof_dependent_scalars);
        // Padding
        for _ in 0..(max_proof_dep_scalars - proof_dep_scalars) {
            s.push(C::ScalarField::zero());
        }

        // For B and B_blinding
        s.push(vt.proof_independent_scalars[0]);
        s.push(vt.proof_independent_scalars[1]);

        // For G
        for i in 0..padded_n as usize {
            s.push(vt.proof_independent_scalars[2 + i]);
        }
        // Padding for G
        for _ in 0..(max_padded_n - padded_n) {
            s.push(C::ScalarField::zero());
        }

        // For H
        for i in 0..padded_n {
            s.push(vt.proof_independent_scalars[(2 + padded_n + i) as usize]);
        }
        // Padding for H
        for _ in 0..(max_padded_n - padded_n) {
            s.push(C::ScalarField::zero());
        }

        debug_assert_eq!(b.len(), s.len());
        // debug_assert_eq!(vt.proof_independent_scalars.len(), 0);
        debug_assert_eq!(
            s.len(),
            max_proof_dep_scalars + 2 * (max_padded_n as usize) + 2
        );
        rmc.add_many(b, &s, C::zero());
    }
    Ok(())
}

/// Accumulate all scalar multiplication checks of Bulletproof verification so that they can be later done in
/// a single scalar multiplication
pub fn add_verification_tuples_to_rmc<C: AffineRepr>(
    verification_tuples: Vec<VerificationTuple<C>>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    rmc: &mut RandomizedMultChecker<C>,
) -> Result<(), R1CSError> {
    let (b, s) = bases_and_scalars_for_batch(verification_tuples, pc_gens, bp_gens, |_| {
        let random_scalar = rmc.current_random;
        rmc.update_random();
        random_scalar
    })?;

    for (b_i, s_i) in b.into_iter().zip(s.into_iter()) {
        rmc.add(b_i, s_i);
    }

    Ok(())
}
