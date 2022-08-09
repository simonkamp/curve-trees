#[allow(unused)]
#[allow(unused_imports)]
use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use crate::lookup::*;

use ark_ec::{
    models::short_weierstrass_jacobian::{GroupAffine, GroupProjective},
    AffineCurve, ModelParameters, SWModelParameters,
};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::{One, Zero};
use merlin::Transcript;
use std::{borrow::BorrowMut, marker::PhantomData};

pub fn curve_check<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    x: LinearCombination<F>,
    y: LinearCombination<F>,
    a: F, // 0 for pallas and vesta
    b: F, // 5 for pallas and vesta
) {
    let (_, _, x2) = cs.multiply(x.clone(), x.clone());
    let (_, _, x3) = cs.multiply(x, x2.into());
    let (_, _, y2) = cs.multiply(y.clone(), y);

    // x^3 + A*x^2 + B - y^2 = 0
    cs.constrain(
        LinearCombination::<F>::from(x3) + LinearCombination::<F>::from(x2).scalar_mul(a) + b - y2,
    )
}

#[derive(Clone, Debug)]
pub struct curve_addition_prms<F: Field> {
    x1: LinearCombination<F>,
    y1: LinearCombination<F>,
    x2: LinearCombination<F>,
    y2: LinearCombination<F>,
    x3: LinearCombination<F>,
    y3: LinearCombination<F>,
    delta: LinearCombination<F>,
}

/// Enforce points over C::ScalarField: (x_3, y_3) = (x_1, y_1) + (x_2, y_2)
/// Takes the slope (delta) as input
pub fn incomplete_curve_addition<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    prms: &curve_addition_prms<F>,
) {
    // delta * (x_2 - x_1) = y_2 - y_1
    let (_, _, delta_x2_x1) = cs.multiply(prms.delta.clone(), prms.x2.clone() - prms.x1.clone()); // todo make borrow parameters?
    cs.constrain(LinearCombination::<F>::from(delta_x2_x1) - (prms.y2.clone() - prms.y1.clone()));

    // delta * (x_3 - x_1) = - y_3 - y_1
    let (_, _, delta_x3_x1) = cs.multiply(prms.delta.clone(), prms.x3.clone() - prms.x1.clone());
    cs.constrain(LinearCombination::<F>::from(delta_x3_x1) - (-prms.y3.clone() - prms.y1.clone()));

    // delta * delta = x_3 + x_2 + x_1
    let (_, _, delta2) = cs.multiply(prms.delta.clone(), prms.delta.clone());
    cs.constrain(
        prms.x3.clone() + prms.x2.clone() + prms.x1.clone() - LinearCombination::<F>::from(delta2),
    );
}

/// Enforce ()
pub fn checked_curve_addition<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    prms: &curve_addition_prms<F>,
    x1_minus_x2_inv: LinearCombination<F>,
) {
    not_zero(cs, prms.x1.clone() - prms.x2.clone(), x1_minus_x2_inv);
    incomplete_curve_addition(cs, prms);
}

/// Enforce v != 0
/// Takes v and its modular inverse (v_inv) as input
fn not_zero<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    v: LinearCombination<F>,
    v_inv: LinearCombination<F>,
) {
    // v * v_inv = one
    let (_, _, one) = cs.multiply(v, v_inv);
    // one = 1
    cs.constrain(one - Variable::One(PhantomData));
}

pub fn re_randomize<F: Field, C: SWModelParameters<BaseField = F>, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    h: GroupAffine<C>,
    commitment_x: F,
    commitment_y: F,
    commitment_x_tilde: F,
    commitment_y_tilde: F,
    randomness: Option<C::ScalarField>, // Witness provided by the prover
) {
    let lambda = <C::ScalarField as PrimeField>::size_in_bits();
    let m = lambda / 3 + 1;

    let r_bits = match randomness {
        None => None,
        Some(r) => {
            let r: <C::ScalarField as PrimeField>::BigInt = r.into();
            Some(r.to_bits_le())
        }
    };

    // Define tables T_1 .. T_m
    let mut m_th_other_term = C::ScalarField::zero();
    for i in 1..m + 1 {
        let mut table = Lookup3Bit::<2, F> {
            elems: [[F::one(); WINDOW_ELEMS]; 2],
        };
        // 2^(3*i)
        let j_term = C::ScalarField::from(2u8).pow(&[3u64 * i as u64]);
        let other_term = if i < m {
            // add j term to the sum in the mth iteration other term
            m_th_other_term += j_term;
            // 2^(3*(i+1))
            C::ScalarField::from(2u8).pow(&[3u64 * (i + 1) as u64])
        } else {
            // sum for i = 1..m-1 { 2^(3* i) }
            m_th_other_term
        };
        for j in 0..WINDOW_ELEMS {
            // s = j * 2^(3*i) + other_term
            let s = (C::ScalarField::from(j as u64) * j_term) - other_term;
            // Multiply blinding by s
            let hs = h.mul(s);
            table.elems[0][j] = hs.x;
            table.elems[1][j] = hs.y;
        }

        let index = match &r_bits {
            None => None,
            Some(random_bits) => {
                let bi = (i - 1) * 3;
                let mut index = if random_bits[bi] { 1usize } else { 0 };
                if random_bits[bi + 1] {
                    index += 2
                };
                if random_bits[bi + 2] {
                    index += 4
                };
                Some(index)
            }
        };

        let [x_table, y_table] = lookup(cs, &table, index).unwrap();
    }
}

pub fn prove_addition<
    T: BorrowMut<Transcript>,
    C: AffineCurve,
    C2: SWModelParameters<BaseField = C::ScalarField>,
>(
    prover: &mut Prover<T, C>,
    p: C2,
    q: C2,
) {
    prover.transcript().append_message(b"", b"");
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_ec::ProjectiveCurve;
    use ark_std::UniformRand;
    use pasta::{
        pallas::Affine as PallasA, pallas::Projective as PallasP, vesta::Affine as VestaA,
        vesta::Projective as VestaP, Fp, Fq,
    };
    type PallasScalar = <PallasA as AffineCurve>::ScalarField;
    type VestaScalar = <VestaA as AffineCurve>::ScalarField;

    #[test]
    fn add() {
        let mut rng = rand::thread_rng();
        let p = <PallasP as UniformRand>::rand(&mut rng);
        let pa = p.into_affine();
        let x1: VestaScalar = (pa as PallasA).x;
        let y1: VestaScalar = (pa as PallasA).y;

        let q = <PallasP as UniformRand>::rand(&mut rng);
        let qa = q.into_affine();
        let x2: VestaScalar = (qa as PallasA).x;
        let y2: VestaScalar = (qa as PallasA).y;

        assert!(x1 != x2); // sanity check, should not happen except with negl. prob.

        let p_plus_q = p + q;
        let p_plus_qa = p_plus_q.into_affine();
        let x3: VestaScalar = (p_plus_qa as PallasA).x;
        let y3: VestaScalar = (p_plus_qa as PallasA).y;

        // sanity checks
        let delta = (y2 - y1) / (x2 - x1);
        assert_eq!(delta * (x2 - x1), y2 - y1);
        assert_eq!(delta * (x3 - x1), -y3 - y1);
        assert_eq!(delta * delta, x1 + x2 + x3);

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(128, 1); // todo size

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut prover = Prover::new(&pc_gens, &mut transcript);
        let (x1_comm, x1_var) = prover.commit(x1, VestaScalar::rand(&mut rng));
        let (y1_comm, y1_var) = prover.commit(y1, VestaScalar::rand(&mut rng));
        let (x2_comm, x2_var) = prover.commit(x2, VestaScalar::rand(&mut rng));
        let (y2_comm, y2_var) = prover.commit(y2, VestaScalar::rand(&mut rng));
        let (x3_comm, x3_var) = prover.commit(x3, VestaScalar::rand(&mut rng));
        let (y3_comm, y3_var) = prover.commit(y3, VestaScalar::rand(&mut rng));
        let (delta_comm, delta_var) = prover.commit(delta, VestaScalar::rand(&mut rng));
        let (x1_minus_x2_inv_comm, x1_minus_x2_inv_var) = prover.commit(
            VestaScalar::from(1) / (x1 - x2),
            VestaScalar::rand(&mut rng),
        );

        let add_prms = curve_addition_prms {
            x1: x1_var.into(),
            y1: y1_var.into(),
            x2: x2_var.into(),
            y2: y2_var.into(),
            x3: x3_var.into(),
            y3: y3_var.into(),
            delta: delta_var.into(),
        };

        checked_curve_addition(&mut prover, &add_prms, x1_minus_x2_inv_var.into());

        let proof = prover.prove(&bp_gens).unwrap();

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut verifier = Verifier::new(&mut transcript);

        let x1_var = verifier.commit(x1_comm);
        let y1_var = verifier.commit(y1_comm);
        let x2_var = verifier.commit(x2_comm);
        let y2_var = verifier.commit(y2_comm);
        let x3_var = verifier.commit(x3_comm);
        let y3_var = verifier.commit(y3_comm);
        let delta_var = verifier.commit(delta_comm);
        let x1_minus_x2_inv_var = verifier.commit(x1_minus_x2_inv_comm);

        let add_prms = curve_addition_prms {
            x1: x1_var.into(),
            y1: y1_var.into(),
            x2: x2_var.into(),
            y2: y2_var.into(),
            x3: x3_var.into(),
            y3: y3_var.into(),
            delta: delta_var.into(),
        };

        checked_curve_addition(&mut verifier, &add_prms, x1_minus_x2_inv_var.into());

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }
}
