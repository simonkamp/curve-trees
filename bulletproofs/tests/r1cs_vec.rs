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

mod veccom_twice {
    use super::*;

    // Prover's scope
    fn gadget_proof<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
    ) -> Result<(R1CSProof<C>, C, C), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a prover
        let mut prover = Prover::new(pc_gens, &mut transcript);

        let mut rng = rand::thread_rng();

        // empty vector commitment
        let v = vec![];

        // 2. Commit to two empty vectors
        let (comm1, _) = prover.commit_vec(&v, C::ScalarField::rand(&mut rng), bp_gens);
        let (comm2, _) = prover.commit_vec(&v, C::ScalarField::rand(&mut rng), bp_gens);

        // 3. Prove
        let proof = prover.prove(bp_gens)?;

        Ok((proof, comm1, comm2))
    }

    // Verifier logic
    fn gadget_verify<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        proof: R1CSProof<C>,
        comm1: C,
        comm2: C,
    ) -> Result<(), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a verifier
        let mut verifier = Verifier::new(&mut transcript);

        let _: Vec<_> = verifier.commit_vec(0, comm1);
        let _: Vec<_> = verifier.commit_vec(0, comm2);

        verifier
            .verify(&proof, &pc_gens, &bp_gens)
            .map_err(|_| R1CSError::VerificationError)
    }

    fn gadget_roundtrip_helper<C: AffineRepr>() -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(128, 1);

        let (proof, comm1, comm2) = gadget_proof::<C>(&pc_gens, &bp_gens)?;

        gadget_verify::<C>(&pc_gens, &bp_gens, proof, comm1, comm2)
    }

    #[test]
    fn test() {
        assert!(gadget_roundtrip_helper::<Affine>().is_ok());
        // assert!(gadget_roundtrip_helper::<Affine>().is_err());
    }
}
mod veccom_empty {
    use super::*;

    /// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
    fn gadget<F: Field, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        c2: LinearCombination<F>,
        d1: LinearCombination<F>,
        d2: LinearCombination<F>,
    ) {
        /*
        let (_, _, c_var) = cs.multiply(a1 + a2, b1 + b2);
        cs.constrain(c1 + c2 - c_var);
        */

        cs.constrain(d1 - d2);
    }

    // Prover's scope
    fn gadget_proof<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        c2: u64,
        d1: u64,
        d2: u64,
    ) -> Result<(R1CSProof<C>, C, C, C), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a prover
        let mut prover = Prover::new(pc_gens, &mut transcript);

        let mut rng = rand::thread_rng();

        // empty vector commitment
        let v = vec![];

        let h = C::ScalarField::rand(&mut rng);
        let (d1_comm, d1) = prover.commit(C::ScalarField::from(d1), h);

        let h = C::ScalarField::rand(&mut rng);
        let (d2_comm, d2) = prover.commit(C::ScalarField::from(d2), h);

        let h = C::ScalarField::rand(&mut rng);
        let (comm, _) = prover.commit_vec(&v, h, bp_gens);

        // 3. Build a CS
        gadget(
            &mut prover,
            C::ScalarField::from(c2).into(),
            d1.into(),
            d2.into(),
        );

        // 4. Make a proof
        let proof = prover.prove(bp_gens)?;

        Ok((proof, d1_comm, d2_comm, comm))
    }

    // Verifier logic
    fn gadget_verify<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        c2: u64,
        proof: R1CSProof<C>,
        d1_comm: C,
        d2_comm: C,
        comm: C,
    ) -> Result<(), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a verifier
        let mut verifier = Verifier::new(&mut transcript);

        // 3. Regular commitments
        let d1 = verifier.commit(d1_comm);
        let d2 = verifier.commit(d2_comm);

        // 2. Commit high-level variables
        let _: Vec<_> = verifier.commit_vec(0, comm);

        // 3. Build a CS
        gadget(
            &mut verifier,
            C::ScalarField::from(c2).into(),
            d1.into(),
            d2.into(),
        );

        // 4. Verify the proof
        verifier
            .verify(&proof, &pc_gens, &bp_gens)
            .map_err(|_| R1CSError::VerificationError)
    }

    fn gadget_roundtrip_helper<C: AffineRepr>(c2: u64, d1: u64, d2: u64) -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(128, 1);

        let (proof, d1_comm, d2_comm, comm) = gadget_proof::<C>(&pc_gens, &bp_gens, c2, d1, d2)?;

        gadget_verify::<C>(&pc_gens, &bp_gens, c2, proof, d1_comm, d2_comm, comm)
    }

    #[test]
    fn test() {
        assert!(gadget_roundtrip_helper::<Affine>(9, 4, 4).is_ok());
        assert!(gadget_roundtrip_helper::<Affine>(10, 5, 4).is_err());
    }
}

mod veccom_non_empty_do_nothing {
    use super::*;

    fn gadget<F: Field, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a1: LinearCombination<F>,
        a2: LinearCombination<F>,
        a3: LinearCombination<F>,
        a4: LinearCombination<F>,
        a5: LinearCombination<F>,
        d1: LinearCombination<F>,
        d2: LinearCombination<F>,
    ) {
        cs.constrain(d1 - d2);
    }

    // Prover's scope
    fn gadget_proof<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
        d1: u64,
        d2: u64,
    ) -> Result<(R1CSProof<C>, C, C, C), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a prover
        let mut prover = Prover::new(pc_gens, &mut transcript);

        let mut rng = rand::thread_rng();

        // commit to all inputs in a single commitment
        let h = C::ScalarField::rand(&mut rng);
        let (d1_comm, d1) = prover.commit(C::ScalarField::from(d1), h);

        let h = C::ScalarField::rand(&mut rng);
        let (d2_comm, d2) = prover.commit(C::ScalarField::from(d2), h);

        let h = C::ScalarField::rand(&mut rng);
        let (comm, vars) = prover.commit_vec(
            &vec![
                C::ScalarField::from(a1),
                C::ScalarField::from(a2),
                C::ScalarField::from(a3),
                C::ScalarField::from(a4),
                C::ScalarField::from(a5),
            ],
            h,
            bp_gens,
        );

        // 3. Build a CS
        gadget(
            &mut prover,
            vars[0].into(),
            vars[1].into(),
            vars[2].into(),
            vars[3].into(),
            vars[4].into(),
            d1.into(),
            d2.into(),
        );

        // 4. Make a proof
        let proof = prover.prove(bp_gens)?;

        Ok((proof, d1_comm, d2_comm, comm))
    }

    // Verifier logic
    fn gadget_verify<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        proof: R1CSProof<C>,
        d1_comm: C,
        d2_comm: C,
        comm: C,
    ) -> Result<(), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a verifier
        let mut verifier = Verifier::new(&mut transcript);

        // 3. Regular commitments
        let d1 = verifier.commit(d1_comm);
        let d2 = verifier.commit(d2_comm);

        // 2. Commit high-level variables
        let vars: Vec<_> = verifier.commit_vec(5, comm);

        // 3. Build a CS
        gadget(
            &mut verifier,
            vars[0].into(),
            vars[1].into(),
            vars[2].into(),
            vars[3].into(),
            vars[4].into(),
            d1.into(),
            d2.into(),
        );

        // 4. Verify the proof
        verifier
            .verify(&proof, &pc_gens, &bp_gens)
            .map_err(|_| R1CSError::VerificationError)
    }

    fn gadget_roundtrip_helper<C: AffineRepr>(
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
        d1: u64,
        d2: u64,
    ) -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(128, 1);

        let (proof, d1_comm, d2_comm, comm) =
            gadget_proof::<C>(&pc_gens, &bp_gens, a1, a2, a3, a4, a5, d1, d2)?;

        gadget_verify::<C>(&pc_gens, &bp_gens, proof, d1_comm, d2_comm, comm)
    }

    #[test]
    fn test() {
        // (3 + 4) * (6 + 1) = (40 + 9)
        assert!(gadget_roundtrip_helper::<Affine>(1, 2, 3, 4, 5, 4, 4).is_ok());
        // (3 + 4) * (6 + 1) != (40 + 10)
        assert!(gadget_roundtrip_helper::<Affine>(1, 2, 3, 4, 5, 5, 4).is_err());
    }
}

mod veccom_non_trivial_linear {
    use super::*;

    /// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
    fn gadget<F: Field, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a1: LinearCombination<F>,
        a2: LinearCombination<F>,
        a3: LinearCombination<F>,
        a4: LinearCombination<F>,
        a5: LinearCombination<F>,
        d1: LinearCombination<F>,
        d2: LinearCombination<F>,
    ) {
        cs.constrain(a1.clone() - a2.clone());
        cs.constrain(a2.clone() - a3.clone());
        cs.constrain(a4.clone() - (a1.clone() + a2.clone() + a3.clone()));
        cs.constrain(d1.clone() - (a1 + a2 + a3 + a4 + a5));
        cs.constrain(d1 - d2);
    }

    // Prover's scope
    fn gadget_proof<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
        d1: u64,
        d2: u64,
    ) -> Result<(R1CSProof<C>, C, C, C), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a prover
        let mut prover = Prover::new(pc_gens, &mut transcript);

        let mut rng = rand::thread_rng();

        // commit to all inputs in a single commitment
        let h = C::ScalarField::rand(&mut rng);
        let (d1_comm, d1) = prover.commit(C::ScalarField::from(d1), h);

        let h = C::ScalarField::rand(&mut rng);
        let (d2_comm, d2) = prover.commit(C::ScalarField::from(d2), h);

        let h = C::ScalarField::rand(&mut rng);
        let (comm, vars) = prover.commit_vec(
            &vec![
                C::ScalarField::from(a1),
                C::ScalarField::from(a2),
                C::ScalarField::from(a3),
                C::ScalarField::from(a4),
                C::ScalarField::from(a5),
            ],
            h,
            bp_gens,
        );

        // 3. Build a CS
        gadget(
            &mut prover,
            vars[0].into(),
            vars[1].into(),
            vars[2].into(),
            vars[3].into(),
            vars[4].into(),
            d1.into(),
            d2.into(),
        );

        // 4. Make a proof
        let proof = prover.prove(bp_gens)?;

        Ok((proof, d1_comm, d2_comm, comm))
    }

    // Verifier logic
    fn gadget_verify<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        proof: R1CSProof<C>,
        d1_comm: C,
        d2_comm: C,
        comm: C,
    ) -> Result<(), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a verifier
        let mut verifier = Verifier::new(&mut transcript);

        // 3. Regular commitments
        let d1 = verifier.commit(d1_comm);
        let d2 = verifier.commit(d2_comm);

        // 2. Commit high-level variables
        let vars: Vec<_> = verifier.commit_vec(5, comm);

        // 3. Build a CS
        gadget(
            &mut verifier,
            vars[0].into(),
            vars[1].into(),
            vars[2].into(),
            vars[3].into(),
            vars[4].into(),
            d1.into(),
            d2.into(),
        );

        // 4. Verify the proof
        verifier
            .verify(&proof, &pc_gens, &bp_gens)
            .map_err(|_| R1CSError::VerificationError)
    }

    fn gadget_roundtrip_helper<C: AffineRepr>(
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
        d1: u64,
        d2: u64,
    ) -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(128, 1);

        let (proof, d1_comm, d2_comm, comm) =
            gadget_proof::<C>(&pc_gens, &bp_gens, a1, a2, a3, a4, a5, d1, d2)?;

        gadget_verify::<C>(&pc_gens, &bp_gens, proof, d1_comm, d2_comm, comm)
    }

    #[test]
    fn test() {
        // (3 + 4) * (6 + 1) = (40 + 9)
        assert!(gadget_roundtrip_helper::<Affine>(5, 5, 5, 15, 7, 37, 37).is_ok());
        // (3 + 4) * (6 + 1) != (40 + 10)
        assert!(gadget_roundtrip_helper::<Affine>(1, 2, 3, 4, 5, 5, 4).is_err());
    }
}

mod veccom_large_linear {
    use super::*;

    const DIM: usize = 0x100;

    /// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
    fn gadget<F: Field, CS: ConstraintSystem<F>>(cs: &mut CS, ax: Vec<LinearCombination<F>>) {
        cs.constrain(ax[0].clone() - F::one());
        cs.constrain(ax[1].clone() - F::one());
        for i in 2..DIM {
            cs.constrain(ax[i].clone() - (ax[i - 1].clone() + ax[i - 2].clone()));
        }
    }

    // Prover's scope
    fn gadget_proof<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
    ) -> Result<(R1CSProof<C>, C), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a prover
        let mut prover = Prover::new(pc_gens, &mut transcript);

        let mut rng = rand::thread_rng();

        // commit to all inputs in a single commitment
        let mut fib: Vec<C::ScalarField> = vec![C::ScalarField::from(0u8); DIM];

        fib[0] = C::ScalarField::from(1u8);
        fib[1] = C::ScalarField::from(1u8);
        for i in 2..fib.len() {
            fib[i] = fib[i - 1] + fib[i - 2];
        }

        let h = C::ScalarField::rand(&mut rng);
        let (comm, vars) = prover.commit_vec(&fib, h, bp_gens);

        // 3. Build a CS
        gadget(
            &mut prover,
            vars.into_iter().map(|v| v.into()).collect::<Vec<_>>(),
        );

        // 4. Make a proof
        let proof = prover.prove(bp_gens)?;

        Ok((proof, comm))
    }

    // Verifier logic
    fn gadget_verify<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        proof: R1CSProof<C>,
        comm: C,
    ) -> Result<(), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a verifier
        let mut verifier = Verifier::new(&mut transcript);

        // 2. Commit high-level variables
        let vars: Vec<_> = verifier.commit_vec(DIM, comm);

        // 3. Build a CS
        gadget(
            &mut verifier,
            vars.into_iter().map(|v| v.into()).collect::<Vec<_>>(),
        );

        // 4. Verify the proof
        verifier
            .verify(&proof, &pc_gens, &bp_gens)
            .map_err(|_| R1CSError::VerificationError)
    }

    fn gadget_roundtrip_helper<C: AffineRepr>() -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(DIM, 1);

        let (proof, comm) = gadget_proof::<C>(&pc_gens, &bp_gens)?;

        gadget_verify::<C>(&pc_gens, &bp_gens, proof, comm)
    }

    #[test]
    fn test() {
        assert!(gadget_roundtrip_helper::<Affine>().is_ok());
    }
}

mod veccom_mul_seperate {
    use super::*;

    const DIM: usize = 0;

    /// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
    fn gadget<F: Field, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: LinearCombination<F>,
        b: LinearCombination<F>,
        ab: LinearCombination<F>,
    ) {
    }

    // Prover's scope
    fn gadget_proof<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        a: C::ScalarField,
        b: C::ScalarField,
        ab: C::ScalarField,
    ) -> Result<(R1CSProof<C>, C), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a prover
        let mut prover = Prover::new(pc_gens, &mut transcript);

        let mut rng = rand::thread_rng();

        // commit to all inputs in a single commitment
        let abc: Vec<C::ScalarField> = vec![];

        let (a, b, c) = prover.allocate_multiplier(Some((a, b))).unwrap();

        // create a veccom
        let h = C::ScalarField::rand(&mut rng);

        let (comm, vars) = prover.commit_vec(&abc, h, bp_gens);

        assert_eq!(vars.len(), DIM);

        // 3. Build a CS
        gadget(&mut prover, a.into(), b.into(), c.into());

        // 4. Make a proof
        let proof = prover.prove(bp_gens)?;

        Ok((proof, comm))
    }

    // Verifier logic
    fn gadget_verify<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        proof: R1CSProof<C>,
        comm: C,
    ) -> Result<(), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a verifier
        let mut verifier = Verifier::new(&mut transcript);

        let (a, b, c) = verifier.allocate_multiplier(None).unwrap();

        // 2. Commit high-level variables
        let vars: Vec<_> = verifier.commit_vec(DIM, comm);

        assert_eq!(vars.len(), DIM);

        // 3. Build a CS
        gadget(&mut verifier, a.into(), b.into(), c.into());

        // 4. Verify the proof
        verifier
            .verify(&proof, &pc_gens, &bp_gens)
            .map_err(|_| R1CSError::VerificationError)
    }

    fn gadget_roundtrip_helper<C: AffineRepr>(
        a: C::ScalarField,
        b: C::ScalarField,
        ab: C::ScalarField,
    ) -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(20, 1);

        let (proof, comm) = gadget_proof::<C>(&pc_gens, &bp_gens, a, b, ab)?;

        gadget_verify::<C>(&pc_gens, &bp_gens, proof, comm)
    }

    #[test]
    fn test() {
        assert!(gadget_roundtrip_helper::<Affine>(0.into(), 0.into(), 0.into()).is_ok());
    }
}

mod veccom_mul {
    use super::*;

    /// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
    fn gadget<F: Field, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: LinearCombination<F>,
        b: LinearCombination<F>,
        ab: LinearCombination<F>,
    ) {
        let (va, vb, vab) = cs.multiply(a, b);
        cs.constrain(vab - ab)
    }

    // Prover's scope
    fn gadget_proof<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        a: C::ScalarField,
        b: C::ScalarField,
        ab: C::ScalarField,
    ) -> Result<(R1CSProof<C>, C), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a prover
        let mut prover = Prover::new(pc_gens, &mut transcript);

        let mut rng = rand::thread_rng();

        // commit to all inputs in a single commitment

        let abc: Vec<C::ScalarField> = vec![a, b, ab];

        let h = C::ScalarField::rand(&mut rng);
        let (comm, vars) = prover.commit_vec(&abc, h, bp_gens);

        // 3. Build a CS
        gadget(&mut prover, vars[0].into(), vars[1].into(), vars[2].into());

        // 4. Make a proof
        let proof = prover.prove(bp_gens)?;

        Ok((proof, comm))
    }

    // Verifier logic
    fn gadget_verify<C: AffineRepr>(
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
        proof: R1CSProof<C>,
        comm: C,
    ) -> Result<(), R1CSError> {
        let mut transcript = Transcript::new(b"R1CSExampleGadget");

        // 1. Create a verifier
        let mut verifier = Verifier::new(&mut transcript);

        // 2. Commit high-level variables
        let vars: Vec<_> = verifier.commit_vec(3, comm);

        // 3. Build a CS
        gadget(
            &mut verifier,
            vars[0].into(),
            vars[1].into(),
            vars[2].into(),
        );

        // 4. Verify the proof
        verifier
            .verify(&proof, &pc_gens, &bp_gens)
            .map_err(|_| R1CSError::VerificationError)
    }

    fn gadget_roundtrip_helper<C: AffineRepr>(
        a: C::ScalarField,
        b: C::ScalarField,
        ab: C::ScalarField,
    ) -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(20, 1);

        let (proof, comm) = gadget_proof::<C>(&pc_gens, &bp_gens, a, b, ab)?;

        gadget_verify::<C>(&pc_gens, &bp_gens, proof, comm)
    }

    #[test]
    fn test() {
        assert!(gadget_roundtrip_helper::<Affine>(5.into(), 5.into(), 25.into()).is_ok());
    }
}
