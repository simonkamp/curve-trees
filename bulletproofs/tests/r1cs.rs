#![allow(non_snake_case)]

extern crate bulletproofs;
extern crate merlin;
extern crate rand;

use ark_ec::AffineRepr;
use ark_ff::Field;
use ark_std::UniformRand;

use ark_pallas::Affine;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use rand::seq::SliceRandom;

// Shuffle gadget (documented in markdown file)

/// A proof-of-shuffle.
struct ShuffleProof<C: AffineRepr>(R1CSProof<C>);

impl<C: AffineRepr> ShuffleProof<C> {
    fn gadget<CS: RandomizableConstraintSystem<C::ScalarField>>(
        cs: &mut CS,
        x: Vec<Variable<C::ScalarField>>,
        y: Vec<Variable<C::ScalarField>>,
    ) -> Result<(), R1CSError> {
        assert_eq!(x.len(), y.len());
        let k = x.len();

        if k == 1 {
            cs.constrain(y[0] - x[0]);
            return Ok(());
        }

        cs.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"shuffle challenge");

            // Make last x multiplier for i = k-1 and k-2
            let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);

            // Make multipliers for x from i == [0, k-3]
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
                let (_, _, o) = cs.multiply(prev_out.into(), x[i] - z);
                o
            });

            // Make last y multiplier for i = k-1 and k-2
            let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);

            // Make multipliers for y from i == [0, k-3]
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
                let (_, _, o) = cs.multiply(prev_out.into(), y[i] - z);
                o
            });

            // Constrain last x mul output and last y mul output to be equal
            cs.constrain(first_mulx_out - first_muly_out);

            Ok(())
        })
    }
}

impl<C: AffineRepr> ShuffleProof<C> {
    /// Attempt to construct a proof that `output` is a permutation of `input`.
    ///
    /// Returns a tuple `(proof, input_commitments || output_commitments)`.
    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens<C>,
        bp_gens: &'b BulletproofGens<C>,
        transcript: &'a mut Transcript,
        input: &[C::ScalarField],
        output: &[C::ScalarField],
    ) -> Result<(ShuffleProof<C>, Vec<C>, Vec<C>), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut prover: Prover<_, C> = Prover::new(&pc_gens, transcript);

        // Construct blinding factors using an RNG.
        // Note: a non-example implementation would want to operate on existing commitments.
        let mut blinding_rng = rand::thread_rng();

        let (input_commitments, input_vars): (Vec<C>, Vec<Variable<C::ScalarField>>) = input
            .into_iter()
            .map(|v| prover.commit(*v, C::ScalarField::rand(&mut blinding_rng)))
            .unzip();

        let (output_commitments, output_vars): (Vec<_>, Vec<_>) = output
            .into_iter()
            .map(|v| prover.commit(*v, C::ScalarField::rand(&mut blinding_rng)))
            .unzip();

        ShuffleProof::<C>::gadget(&mut prover, input_vars, output_vars)?;

        let proof = prover.prove(&bp_gens)?;

        Ok((ShuffleProof(proof), input_commitments, output_commitments))
    }
}

impl<C: AffineRepr> ShuffleProof<C> {
    /// Attempt to verify a `ShuffleProof`.
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens<C>,
        bp_gens: &'b BulletproofGens<C>,
        transcript: &'a mut Transcript,
        input_commitments: &Vec<C>,
        output_commitments: &Vec<C>,
    ) -> Result<(), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let k = input_commitments.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut verifier = Verifier::new(transcript);

        let input_vars: Vec<_> = input_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        let output_vars: Vec<_> = output_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        ShuffleProof::<C>::gadget(&mut verifier, input_vars, output_vars)?;

        verifier.verify(&self.0, &pc_gens, &bp_gens)?;
        Ok(())
    }
    pub fn verification_scalars_and_points<'a, 'b>(
        &self,
        transcript: &'a mut Transcript,
        input_commitments: &Vec<C>,
        output_commitments: &Vec<C>,
    ) -> Result<VerificationTuple<C>, R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let k = input_commitments.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut verifier = Verifier::new(transcript);

        let input_vars: Vec<_> = input_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        let output_vars: Vec<_> = output_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        ShuffleProof::<C>::gadget(&mut verifier, input_vars, output_vars)?;

        verifier.verification_scalars_and_points(&self.0)
    }
}

fn kshuffle_helper(k: usize) {
    use rand::Rng;
    type Scalar = <Affine as AffineRepr>::ScalarField;

    // Common code
    let pc_gens = PedersenGens::<Affine>::default();
    let bp_gens = BulletproofGens::<Affine>::new((2 * k).next_power_of_two(), 1);

    let (proof, input_commitments, output_commitments) = {
        // Randomly generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<Scalar> = (0..k)
            .map(|_| Scalar::from(rng.gen_range(min..max)))
            .collect();
        let mut output = input.clone();
        output.shuffle(&mut rand::thread_rng());

        let mut prover_transcript = Transcript::new(b"ShuffleProofTest");
        ShuffleProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output).unwrap()
    };

    {
        let mut verifier_transcript = Transcript::new(b"ShuffleProofTest");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
                &output_commitments
            )
            .is_ok());
    }
}

fn kshuffle_batch_helper(k: usize, n: usize) {
    use rand::Rng;
    type Scalar = <Affine as AffineRepr>::ScalarField;

    // Common code
    let pc_gens = PedersenGens::<Affine>::default();
    let bp_gens = BulletproofGens::<Affine>::new((2 * k).next_power_of_two(), 1);

    let mut proofs_and_commitments = Vec::with_capacity(n);
    for _ in 0..n {
        // Randomly generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<Scalar> = (0..k)
            .map(|_| Scalar::from(rng.gen_range(min..max)))
            .collect();
        let mut output = input.clone();
        output.shuffle(&mut rand::thread_rng());

        let mut prover_transcript = Transcript::new(b"ShuffleProofTest");
        proofs_and_commitments.push(
            ShuffleProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output)
                .unwrap(),
        );
    }

    let mut vsps = Vec::with_capacity(n);
    for i in 0..n {
        let mut verifier_transcript = Transcript::new(b"ShuffleProofTest");
        let (proof, input_commitments, output_commitments) = &proofs_and_commitments[i];
        vsps.push(
            proof
                .verification_scalars_and_points(
                    &mut verifier_transcript,
                    &input_commitments,
                    &output_commitments,
                )
                .unwrap(),
        );
    }

    assert!(batch_verify(vsps, &pc_gens, &bp_gens).is_ok());
}

#[test]
fn shuffle_gadget_test_1() {
    kshuffle_helper(1);
    kshuffle_batch_helper(1, 2);
}

#[test]
fn shuffle_gadget_test_2() {
    kshuffle_helper(2);
    kshuffle_batch_helper(2, 4);
}

#[test]
fn shuffle_gadget_test_3() {
    kshuffle_helper(3);
}

#[test]
fn shuffle_gadget_test_4() {
    kshuffle_helper(4);
}

#[test]
fn shuffle_gadget_test_5() {
    kshuffle_helper(5);
}

#[test]
fn shuffle_gadget_test_6() {
    kshuffle_helper(6);
}

#[test]
fn shuffle_gadget_test_7() {
    kshuffle_helper(7);
}

#[test]
fn shuffle_gadget_test_24() {
    kshuffle_helper(24);
}

#[test]
fn shuffle_gadget_test_42() {
    kshuffle_helper(42);
    // kshuffle_batch_helper(42, 42);
}

/// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
fn example_gadget<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a1: LinearCombination<F>,
    a2: LinearCombination<F>,
    b1: LinearCombination<F>,
    b2: LinearCombination<F>,
    c1: LinearCombination<F>,
    c2: LinearCombination<F>,
) {
    let (_, _, c_var) = cs.multiply(a1 + a2, b1 + b2);
    cs.constrain(c1 + c2 - c_var);
}

// Prover's scope
fn example_gadget_proof<C: AffineRepr>(
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(R1CSProof<C>, Vec<C>), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let mut rng = rand::thread_rng();
    let (commitments, vars): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
        .iter()
        .map(|x| prover.commit(C::ScalarField::from(*x), C::ScalarField::rand(&mut rng)))
        .unzip();

    // 3. Build a CS
    example_gadget(
        &mut prover,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        C::ScalarField::from(c2).into(),
    );

    // 4. Make a proof
    let proof = prover.prove(bp_gens)?;

    Ok((proof, commitments))
}

// Verifier logic
fn example_gadget_verify<C: AffineRepr>(
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    c2: u64,
    proof: R1CSProof<C>,
    commitments: Vec<C>,
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a verifier
    let mut verifier = Verifier::new(&mut transcript);

    // 2. Commit high-level variables
    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();

    // 3. Build a CS
    example_gadget(
        &mut verifier,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        C::ScalarField::from(c2).into(),
    );

    // 4. Verify the proof
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .map_err(|_| R1CSError::VerificationError)
}

fn example_gadget_roundtrip_helper<C: AffineRepr>(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::<C>::default();
    let bp_gens = BulletproofGens::<C>::new(128, 1);

    let (proof, commitments) =
        example_gadget_proof::<C>(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

    example_gadget_verify::<C>(&pc_gens, &bp_gens, c2, proof, commitments)
}

#[test]
fn example_gadget_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(example_gadget_roundtrip_helper::<Affine>(3, 4, 6, 1, 40, 9).is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(example_gadget_roundtrip_helper::<Affine>(3, 4, 6, 1, 40, 10).is_err());
}

// Range Proof gadget

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn range_proof<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut v: LinearCombination<F>,
    v_assignment: Option<u64>,
    n: usize,
) -> Result<(), R1CSError> {
    let mut exp_2 = F::one();
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate_multiplier(v_assignment.map(|q| {
            let bit: u64 = (q >> i) & 1;
            ((1 - bit).into(), bit.into())
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        // cs.constrain(a + (b - 1u64));
        cs.constrain(a + (b - constant(1u64)));

        // Add `-b_i*2^i` to the linear combination
        // in order to form the following constraint by the end of the loop:
        // v = Sum(b_i * 2^i, i = 0..n-1)
        v = v - b * exp_2;

        exp_2 = exp_2 + exp_2;
    }

    // Enforce that v = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(v);

    Ok(())
}

#[test]
fn range_proof_gadget() {
    use rand::thread_rng;
    use rand::Rng;

    let mut rng = thread_rng();
    let m = 3; // number of values to test per `n`

    for n in [2, 10, 32, 63].iter() {
        let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
        let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min..max)).collect();
        for v in values {
            assert!(range_proof_helper::<Affine>(v.into(), *n).is_ok());
        }
        assert!(range_proof_helper::<Affine>((max + 1).into(), *n).is_err());
    }
}

fn range_proof_helper<C: AffineRepr>(v_val: u64, n: usize) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::<C>::default();
    let bp_gens = BulletproofGens::<C>::new(128, 1);

    // Prover's scope
    let (proof, commitment) = {
        // Prover makes a `ConstraintSystem` instance representing a range proof gadget
        let mut prover_transcript = Transcript::new(b"RangeProofTest");
        let mut rng = rand::thread_rng();

        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (com, var) = prover.commit(v_val.into(), C::ScalarField::rand(&mut rng));
        assert!(range_proof(&mut prover, var.into(), Some(v_val), n).is_ok());

        let proof = prover.prove(&bp_gens)?;

        (proof, com)
    };

    // Verifier makes a `ConstraintSystem` instance representing a merge gadget
    let mut verifier_transcript = Transcript::new(b"RangeProofTest");
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let var = verifier.commit(commitment);

    // Verifier adds constraints to the constraint system
    assert!(range_proof(&mut verifier, var.into(), None, n).is_ok());

    // Verifier verifies proof
    verifier.verify(&proof, &pc_gens, &bp_gens)
}
