use bulletproofs::r1cs::*;

use crate::curve::*;

use ark_ec::models::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::Field;
use ark_std::rand::Rng;

#[derive(Clone, Copy, Debug)]
pub struct UniversalHash<F: Field> {
    alpha: F,
    beta: F,
    // coefficients in curve equation
    a: F,
    b: F,
}

impl<F: Field> UniversalHash<F> {
    pub fn new<R: Rng>(rng: &mut R, a: F, b: F) -> Self {
        Self {
            alpha: F::rand(rng),
            beta: F::rand(rng),
            a,
            b,
        }
    }
    /// Given a commitment c, blinded using h, returns c' and r s.t. c' = c+h*r and c' is a permissible point
    pub fn permissible_commitment<S: Field, C: SWCurveConfig<BaseField = F, ScalarField = S>>(
        &self,
        c: &Affine<C>,
        h: &Affine<C>,
    ) -> (Affine<C>, C::ScalarField) {
        let mut r = 0u64;
        let mut c_prime = *c;
        while !self.is_permissible(c_prime) {
            c_prime = (c_prime + h).into();
            r += 1;
        }
        (c_prime, C::ScalarField::from(r))
    }

    pub fn witness(&self, y: F) -> F {
        self.universal_hash(y)
            .sqrt()
            .expect("point must be permissible")
    }

    pub fn is_permissible<C: SWCurveConfig<BaseField = F>>(&self, point: Affine<C>) -> bool {
        let hash_of_y_is_qr = self.universal_hash_to_bit(point.y);
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

    pub fn permissible_gadget<Cs: ConstraintSystem<F>>(
        &self,
        cs: &mut Cs,
        x: LinearCombination<F>,
        y: Option<F>,
        y_var: Variable<F>,
    ) {
        // prove that (x,y) is a point on the curve
        curve_check(cs, x, y_var.into(), self.a, self.b);
        // prove that the y coordinate hashes to a quadratic residue
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
    use ark_ec::AffineRepr;
    use ark_std::UniformRand;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;

    type PallasA = ark_pallas::Affine;
    type PallasP = ark_pallas::Projective;
    type PallasBase = <PallasA as AffineRepr>::BaseField;
    type VestaA = ark_vesta::Affine;
    type VestaScalar = <VestaA as AffineRepr>::ScalarField;

    #[test]
    fn test_permissible() {
        let mut rng = rand::thread_rng();
        let c = PallasA::rand(&mut rng);
        let h = PallasA::rand(&mut rng);
        let uh = UniversalHash::<PallasBase>::new(
            &mut rng,
            ark_pallas::PallasConfig::COEFF_A,
            ark_pallas::PallasConfig::COEFF_B,
        );
        let (c2, _) = uh.permissible_commitment(&c, &h);

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(8, 1);

        let (proof, x_comm) = {
            let mut transcript = Transcript::new(b"Permissible");
            let mut prover = Prover::new(&pc_gens, &mut transcript);
            let (x_comm, x_var) = prover.commit(c2.x, VestaScalar::rand(&mut rng));
            let y_var = prover.allocate(Some(c2.y)).unwrap();

            uh.permissible_gadget(&mut prover, x_var.into(), Some(c2.y), y_var);

            let proof = prover.prove(&bp_gens).unwrap();
            (proof, x_comm)
        };

        let mut transcript = Transcript::new(b"Permissible");
        let mut verifier = Verifier::new(&mut transcript);
        let x_var = verifier.commit(x_comm);
        let y_var = verifier.allocate(None).unwrap();

        uh.permissible_gadget(&mut verifier, x_var.into(), None, y_var);

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }
}
