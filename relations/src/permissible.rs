#![allow(unused)] // todo
use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use crate::curve::*;
use crate::lookup::*;

use ark_ec::{
    models::short_weierstrass_jacobian::{GroupAffine, GroupProjective},
    AffineCurve, ModelParameters, ProjectiveCurve, SWModelParameters,
};
use ark_ff::{BigInteger, Field, PrimeField, SquareRootField};
use ark_std::{rand::Rng, One, UniformRand, Zero};
use merlin::Transcript;
use std::{borrow::BorrowMut, iter, marker::PhantomData};

#[derive(Clone, Copy, Debug)]
pub struct UniversalHash<F: SquareRootField> {
    alpha: F,
    beta: F,
    // coefficients in curve equation
    a: F,
    b: F,
}

impl<F: SquareRootField> UniversalHash<F> {
    pub fn new<R: Rng>(rng: &mut R, a: F, b: F) -> Self {
        Self {
            alpha: F::rand(rng),
            beta: F::rand(rng),
            a: a,
            b: b,
        }
    }
    /// Given a commitment c, blinded using h, returns c' and r s.t. c' = c+h*r and c' is a permissible point
    pub fn permissible_commitment<C: SWModelParameters<BaseField = F>>(
        &self,
        c: &GroupAffine<C>,
        h: &GroupAffine<C>,
    ) -> (GroupAffine<C>, C::ScalarField) {
        let mut r = 0u64;
        let mut c_prime = *c;
        while !self.is_permissible(c_prime) {
            c_prime += h;
            r += 1;
        }
        (c_prime, C::ScalarField::from(r))
    }

    pub fn witness(&self, y: F) -> F {
        self.universal_hash(y)
            .sqrt()
            .expect("point must be permissible")
    }

    pub fn is_permissible<C: SWModelParameters<BaseField = F>>(
        &self,
        point: GroupAffine<C>,
    ) -> bool {
        let hash_of_y_is_qr = self.universal_hash_to_bit(point.y);
        // todo is testing the first condition sufficient?
        let hash_of_neg_y_is_not_qr = !self.universal_hash_to_bit(-point.y);
        hash_of_y_is_qr && hash_of_neg_y_is_not_qr
    }

    /// returns true iff v*alpha+beta is a quadratic residue
    pub fn universal_hash_to_bit(&self, v: F) -> bool {
        self.universal_hash(v).legendre().is_qr()
    }

    fn universal_hash(&self, v: F) -> F {
        v * self.alpha + self.beta
    }

    pub fn permissible<Cs: ConstraintSystem<F>>(
        &self,
        cs: &mut Cs,
        x: LinearCombination<F>,
        y: Option<F>,
    ) {
        let y_var = cs.allocate(y).expect("Prover must supply witness");
        curve_check(cs, x, y_var.into(), self.a, self.b);
        let (_, _, w2) = cs
            .allocate_multiplier(y.map(|y| {
                let w = self.witness(y);
                (w, w)
            }))
            .expect("Prover must supply witness");
        let hash: LinearCombination<F> = y_var * self.alpha + self.beta;
        cs.constrain(w2 - hash);
    }
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
    type PallasP = pasta::pallas::Projective;
    type PallasScalar = <PallasA as AffineCurve>::ScalarField;
    type PallasBase = <PallasA as AffineCurve>::BaseField;
    type VestaA = pasta::vesta::Affine;
    type VestaScalar = <VestaA as AffineCurve>::ScalarField;
    type VestaBase = <VestaA as AffineCurve>::BaseField;

    #[test]
    fn test_permissible() {
        let mut rng = rand::thread_rng();
        let c = PallasP::rand(&mut rng).into_affine();
        let h = PallasP::rand(&mut rng).into_affine();
        let uh = UniversalHash::<PallasBase>::new(
            &mut rng,
            pasta::pallas::PallasParameters::COEFF_A,
            pasta::pallas::PallasParameters::COEFF_B,
        );
        let (c2, r) = uh.permissible_commitment(&c, &h);

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(8, 1);

        let (proof, x_comm) = {
            let mut transcript = Transcript::new(b"Permissible");
            let mut prover = Prover::new(&pc_gens, &mut transcript);
            let (x_comm, x_var) = prover.commit(c2.x, VestaScalar::rand(&mut rng));

            uh.permissible(&mut prover, x_var.into(), Some(c2.y));

            let proof = prover.prove(&bp_gens).unwrap();
            (proof, x_comm)
        };

        let mut transcript = Transcript::new(b"Permissible");
        let mut verifier = Verifier::new(&mut transcript);
        let x_var = verifier.commit(x_comm);

        uh.permissible(&mut verifier, x_var.into(), None);

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }
}
