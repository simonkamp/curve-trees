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
use ark_std::{One, UniformRand, Zero};
use merlin::Transcript;
use std::{borrow::BorrowMut, iter, marker::PhantomData};

struct UniversalHash<F: SquareRootField> {
    alpha: F,
    beta: F,
}

impl<F: SquareRootField> UniversalHash<F> {
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
        let u = v * self.alpha + self.beta;
        u.legendre().is_qr()
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
    type PallasScalar = <PallasA as AffineCurve>::ScalarField;
    type PallasBase = <PallasA as AffineCurve>::BaseField;
    type VestaA = pasta::vesta::Affine;
    type VestaScalar = <VestaA as AffineCurve>::ScalarField;
    type VestaBase = <VestaA as AffineCurve>::BaseField;

    #[test]
    fn test_permissible() {}
}
