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

pub fn select<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    x: LinearCombination<F>,
    xs: Vec<LinearCombination<F>>,
    is: Vec<LinearCombination<F>>,
) {
    assert!(xs.len() > 0);
    assert!(xs.len() == is.len());
    // constrain is to bits
    is.iter().map(|i| is_bit(cs, i.clone()));

    // constrain sum of is to 1
    let mut is_sum = is[0].clone();
    for i in 1..is.len() {
        is_sum = is_sum + is[i].clone();
    }
    cs.constrain(is_sum - F::one());

    // x = inner product of is and xs
    let mut inner_product: LinearCombination<F> = F::zero().into();
    for i in 0..is.len() {
        let (_, _, product) = cs.multiply(xs[i].clone(), is[i].clone());
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
        let bpg = BulletproofGens::new(512, 1);
        let (proof, xs_comms, is_comms, x_comm) = {
            // have a prover commit to a vector of random elements in Pallas base field
            // (will be x-coordinates of permissible points in the end)
            let xs: Vec<_> = iter::repeat(PallasBase::rand(&mut rng)).take(256).collect();
            let mut is: Vec<_> = iter::repeat(PallasBase::zero()).take(256).collect();
            let index = 42;
            is[index] = PallasBase::one();
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
            let mut is_comms = Vec::with_capacity(256);
            let mut is_vars = Vec::with_capacity(256);
            for i in 0..256 {
                let (c, v) = prover.commit(is[i], PallasBase::rand(&mut rng));
                is_comms.push(c);
                is_vars.push(v);
            }
            let (x_comm, x_var) = prover.commit(x, PallasBase::rand(&mut rng));

            select(
                &mut prover,
                x_var.into(),
                xs_vars.into_iter().map(|v| v.into()).collect(),
                is_vars.into_iter().map(|v| v.into()).collect(),
            );

            let proof = prover.prove(&bpg).unwrap();
            (proof, xs_comms, is_comms, x_comm)
        };

        let mut transcript = Transcript::new(b"select");
        let mut verifier = Verifier::new(&mut transcript);

        let mut xs_vars = Vec::with_capacity(256);
        let mut is_vars = Vec::with_capacity(256);
        for i in 0..256 {
            xs_vars.push(verifier.commit(xs_comms[i]));
        }
        for i in 0..256 {
            is_vars.push(verifier.commit(is_comms[i]));
        }
        let x_var = verifier.commit(x_comm);

        select(
            &mut verifier,
            x_var.into(),
            xs_vars.into_iter().map(|v| v.into()).collect(),
            is_vars.into_iter().map(|v| v.into()).collect(),
        );

        verifier.verify(&proof, &pg, &bpg).unwrap();
    }

    #[test]
    fn test_select_vec_commit() {
        let mut rng = rand::thread_rng();
        let pg = PedersenGens::default();
        let bpg = BulletproofGens::new(512, 1);
        let (proof, xs_comm, is_comm, x_comm) = {
            // have a prover commit to a vector of random elements in Pallas base field
            // (will be x-coordinates of permissible points in the end)
            let xs: Vec<_> = iter::repeat(PallasBase::rand(&mut rng)).take(256).collect();
            let mut is: Vec<_> = iter::repeat(PallasBase::zero()).take(256).collect();
            let index = 42;
            is[index] = PallasBase::one();
            let x = xs[index];

            let mut transcript = Transcript::new(b"select");
            let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
            let blinding_xs = PallasBase::rand(&mut rng);
            let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);
            let blinding_is = PallasBase::rand(&mut rng);
            let (is_comm, is_vars) = prover.commit_vec(xs.as_slice(), blinding_is, &bpg);
            let blinding_x = PallasBase::rand(&mut rng);
            let (x_comm, x_var) = prover.commit(x, blinding_x);

            select(
                &mut prover,
                x_var.into(),
                xs_vars.into_iter().map(|v| v.into()).collect(),
                is_vars.into_iter().map(|v| v.into()).collect(),
            );

            let proof = prover.prove(&bpg).unwrap();
            (proof, xs_comm, is_comm, x_comm)
        };

        let mut transcript = Transcript::new(b"select");
        let mut verifier = Verifier::new(&mut transcript);

        let xs_vars = verifier.commit_vec(256, xs_comm);
        let is_vars = verifier.commit_vec(256, is_comm);
        let x_var = verifier.commit(x_comm);

        select(
            &mut verifier,
            x_var.into(),
            xs_vars.into_iter().map(|v| v.into()).collect(),
            is_vars.into_iter().map(|v| v.into()).collect(),
        );

        // todo awaits vector commitment fix
        // verifier.verify(&proof, &pg, &bpg).unwrap();
    }
}
