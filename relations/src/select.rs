#![allow(unused)] // todo
use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use crate::curve::*;
use crate::lookup::*;

use ark_ec::{
    models::short_weierstrass_jacobian::{GroupAffine, GroupProjective},
    AffineCurve, ModelParameters, ProjectiveCurve, SWModelParameters,
};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::{One, UniformRand, Zero};
use merlin::Transcript;
use std::{borrow::BorrowMut, iter, marker::PhantomData};

/// Prove that a commitment x is one of the values commited to in vector commitment xs.
/// The prover must provide the index of x in xs as witness.
pub fn select<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    x: LinearCombination<F>,
    xs: Vec<LinearCombination<F>>,
    index: Option<usize>,
) {
    assert!(xs.len() > 0);
    // allocate vector of index bits, and constrain them to be bits
    let mut is = Vec::with_capacity(xs.len());
    for i in 0..xs.len() {
        // Allocate variable for ith index.
        // If i == index witness prover allocates 1, otherwise 0.
        let ith_var = cs
            .allocate(index.map(|index| if index == i { F::one() } else { F::zero() }))
            .expect("Prover must have witness");
        // Constrain ith var to be a bit
        is_bit(cs, ith_var.into());

        is.push(ith_var);
    }

    // Constrain sum of the index bits to 1.
    let mut is_sum: LinearCombination<F> = is[0].into();
    for i in 1..is.len() {
        is_sum = is_sum + is[i];
    }
    cs.constrain(is_sum - F::one());

    // x = inner product of is and xs
    let mut inner_product: LinearCombination<F> = F::zero().into();
    for i in 0..is.len() {
        let (_, _, product) = cs.multiply(xs[i].clone(), is[i].into());
        inner_product = inner_product + product;
    }
    cs.constrain(inner_product - x);
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_std::UniformRand;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;

    use rand::thread_rng;
    use rand::Rng;

    use pasta;
    type PallasA = pasta::pallas::Affine;
    type PallasScalar = <PallasA as AffineCurve>::ScalarField;
    type PallasBase = <PallasA as AffineCurve>::BaseField;
    type VestaA = pasta::vesta::Affine;
    type VestaScalar = <VestaA as AffineCurve>::ScalarField;
    type VestaBase = <VestaA as AffineCurve>::BaseField;

    #[test]
    fn test_select() {
        let mut rng = rand::thread_rng();
        let pg = PedersenGens::default();
        let bpg = BulletproofGens::new(1024, 1);
        let (proof, xs_comms, x_comm) = {
            // have a prover commit to a vector of random elements in Pallas base field
            // (will be x-coordinates of permissible points in the end)
            let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                .take(256)
                .collect();
            let index = 42;
            let x = xs[index];

            let mut transcript = Transcript::new(b"select");
            let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
            let mut xs_comms = Vec::with_capacity(256);
            let mut xs_vars = Vec::with_capacity(256);
            for i in 0..256 {
                let (c, v) = prover.commit(xs[i], PallasBase::rand(&mut rng));
                xs_comms.push(c);
                xs_vars.push(v);
            }
            let (x_comm, x_var) = prover.commit(x, PallasBase::rand(&mut rng));

            select(
                &mut prover,
                x_var.into(),
                xs_vars.into_iter().map(|v| v.into()).collect(),
                Some(index),
            );

            let proof = prover.prove(&bpg).unwrap();
            (proof, xs_comms, x_comm)
        };

        let mut transcript = Transcript::new(b"select");
        let mut verifier = Verifier::new(&mut transcript);

        let mut xs_vars = Vec::with_capacity(256);
        for i in 0..256 {
            xs_vars.push(verifier.commit(xs_comms[i]));
        }
        let x_var = verifier.commit(x_comm);

        select(
            &mut verifier,
            x_var.into(),
            xs_vars.into_iter().map(|v| v.into()).collect(),
            None,
        );

        verifier.verify(&proof, &pg, &bpg).unwrap();
    }

    #[test]
    fn test_select_vec_commit() {
        let mut rng = rand::thread_rng();
        let pg = PedersenGens::default();
        let bpg = BulletproofGens::new(1024, 1);
        let (proof, xs_comm, x_comm) = {
            // have a prover commit to a vector of random elements in Pallas base field
            // (will be x-coordinates of permissible points in the end)
            let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                .take(256)
                .collect();
            let index = 42;
            let x = xs[index];

            let mut transcript = Transcript::new(b"select");
            let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
            let blinding_xs = PallasBase::rand(&mut rng);
            let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);
            let blinding_x = PallasBase::rand(&mut rng);
            let (x_comm, x_var) = prover.commit(x, blinding_x);

            select(
                &mut prover,
                x_var.into(),
                xs_vars.into_iter().map(|v| v.into()).collect(),
                Some(index),
            );

            let proof = prover.prove(&bpg).unwrap();
            (proof, xs_comm, x_comm)
        };

        let mut transcript = Transcript::new(b"select");
        let mut verifier = Verifier::new(&mut transcript);

        let xs_vars = verifier.commit_vec(256, xs_comm);
        let x_var = verifier.commit(x_comm);

        select(
            &mut verifier,
            x_var.into(),
            xs_vars.into_iter().map(|v| v.into()).collect(),
            None,
        );

        let res = verifier.verify(&proof, &pg, &bpg);
        // todo awaits vector commitment fix
        assert_eq!(res, Ok(()))
    }
}
