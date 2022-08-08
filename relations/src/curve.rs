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
use std::marker::PhantomData;

pub fn curve_check<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    x: LinearCombination<C::ScalarField>,
    y: LinearCombination<C::ScalarField>,
    a: C::ScalarField, // 0 for pallas and vesta
    b: C::ScalarField, // 5 for pallas and vesta
) {
    let (_, _, x2) = cs.multiply(x.clone(), x.clone());
    let (_, _, x3) = cs.multiply(x.clone(), x2.into());
    let (_, _, y2) = cs.multiply(y.clone(), y.clone());

    // x^3 + A*x^2 + B - y^2 = 0
    cs.constrain(
        LinearCombination::<C::ScalarField>::from(x3)
            + LinearCombination::<C::ScalarField>::from(x2).scalar_mul(a)
            + b
            - y2,
    )
}

/// Enforce points over C::ScalarField: (x_3, y_3) = (x_1, y_1) + (x_2, y_2)
/// Takes the slope (delta) as input
pub fn incomplete_curve_addition<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    x1: LinearCombination<C::ScalarField>,
    y1: LinearCombination<C::ScalarField>,
    x2: LinearCombination<C::ScalarField>,
    y2: LinearCombination<C::ScalarField>,
    x3: LinearCombination<C::ScalarField>,
    y3: LinearCombination<C::ScalarField>,
    delta: LinearCombination<C::ScalarField>,
) {
    // delta * (x_2 - x_1) = y_2 - y_1
    let (_, _, delta_x2_x1) = cs.multiply(delta.clone(), x2.clone() - x1.clone());
    cs.constrain(LinearCombination::<C::ScalarField>::from(delta_x2_x1) - (y2 - y1.clone()));

    // delta * (x_3 - x_1) = - y_3 - y_1
    let (_, _, delta_x3_x1) = cs.multiply(delta.clone(), x3.clone() - x1.clone());
    cs.constrain(LinearCombination::<C::ScalarField>::from(delta_x3_x1) - (-y3 - y1));

    // delta * delta = x_3 + x_2 + x_1
    let (_, _, delta2) = cs.multiply(delta.clone(), delta.clone());
    cs.constrain(x3 + x2 + x1 - LinearCombination::<C::ScalarField>::from(delta2));
}

/// Enforce ()
pub fn checked_curve_addition<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    x1: LinearCombination<C::ScalarField>,
    y1: LinearCombination<C::ScalarField>,
    x2: LinearCombination<C::ScalarField>,
    y2: LinearCombination<C::ScalarField>,
    x3: LinearCombination<C::ScalarField>,
    y3: LinearCombination<C::ScalarField>,
    delta: LinearCombination<C::ScalarField>,
    x1_minus_x2_inv: LinearCombination<C::ScalarField>,
) {
    not_zero(cs, x1.clone() - x2.clone(), x1_minus_x2_inv);
    incomplete_curve_addition(cs, x1, y1, x2, y2, x3, y3, delta);
}

/// Enforce v != 0
/// Takes v and its modular inverse (v_inv) as input
fn not_zero<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    v: LinearCombination<C::ScalarField>,
    v_inv: LinearCombination<C::ScalarField>,
) {
    // v * v_inv = one
    let (_, _, one) = cs.multiply(v, v_inv);
    // one = 1
    cs.constrain(LinearCombination::<C::ScalarField>::from(
        one - Variable::One(PhantomData),
    ));
}

pub fn re_randomize<
    C: AffineCurve,
    C2: SWModelParameters<BaseField = C::ScalarField>,
    Cs: ConstraintSystem<C>,
>(
    cs: &mut Cs,
    h: GroupAffine<C2>,
    commitment_x: C::ScalarField,
    commitment_y: C::ScalarField,
    commitment_x_tilde: C::ScalarField,
    commitment_y_tilde: C::ScalarField,
    randomness: Option<C2::ScalarField>, // Witness provided by the prover
) {
    let lambda = <C2::ScalarField as PrimeField>::size_in_bits();
    let m = lambda / 3 + 1;

    let r_bits = match randomness {
        None => None,
        Some(r) => {
            let r: <C2::ScalarField as PrimeField>::BigInt = r.into();
            Some(r.to_bits_le())
        }
    };

    // Define tables T_1 .. T_m
    let mut m_th_other_term = C2::ScalarField::zero();
    for i in 1..m + 1 {
        let mut table = Lookup3Bit::<2, C::ScalarField> {
            elems: [[C::ScalarField::one(); WINDOW_ELEMS]; 2],
        };
        // 2^(3*i)
        let j_term = C2::ScalarField::from(2u8).pow(&[3u64 * i as u64]);
        let other_term = if i < m {
            // add j term to the sum in the mth iteration other term
            m_th_other_term = m_th_other_term + j_term;
            // 2^(3*(i+1))
            C2::ScalarField::from(2u8).pow(&[3u64 * (i + 1) as u64])
        } else {
            // sum for i = 1..m-1 { 2^(3* i) }
            m_th_other_term
        };
        for j in 0..WINDOW_ELEMS {
            // s = j * 2^(3*i) + other_term
            let s = (C2::ScalarField::from(j as u64) * j_term) - other_term;
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

        checked_curve_addition(
            &mut prover,
            x1_var.into(),
            y1_var.into(),
            x2_var.into(),
            y2_var.into(),
            x3_var.into(),
            y3_var.into(),
            delta_var.into(),
            x1_minus_x2_inv_var.into(),
        );

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

        checked_curve_addition(
            &mut verifier,
            x1_var.into(),
            y1_var.into(),
            x2_var.into(),
            y2_var.into(),
            x3_var.into(),
            y3_var.into(),
            delta_var.into(),
            x1_minus_x2_inv_var.into(),
        );

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }
}
