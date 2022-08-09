#![allow(unused)] // todo
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
    let (_, _, x_r) = cs.multiply(x.clone(), x.clone());
    let (_, _, x_o) = cs.multiply(x, x_r.into());
    let (_, _, y_r) = cs.multiply(y.clone(), y);

    // x^3 + A*x^2 + B - y^2 = 0
    cs.constrain(
        LinearCombination::<F>::from(x_o) + LinearCombination::<F>::from(x_r).scalar_mul(a) + b
            - y_r,
    )
}

#[derive(Clone, Debug)]
pub struct CurveAddition<F: Field> {
    x_l: LinearCombination<F>,
    y_l: LinearCombination<F>,
    x_r: LinearCombination<F>,
    y_r: LinearCombination<F>,
    x_o: LinearCombination<F>,
    y_o: LinearCombination<F>,
    delta: Option<F>,
}

/// Enforce points over C::ScalarField: (x_o, y_o) = (x_l, y_l) + (x_r, y_r)
/// Takes the slope (delta) as input
pub fn incomplete_curve_addition<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    prms: &CurveAddition<F>,
) {
    let delta_lc: LinearCombination<F> = cs.allocate(prms.delta).unwrap().into();
    // delta * (x_r - x_l) = y_r - y_l
    let (_, _, delta_x_r_x_l) = cs.multiply(delta_lc.clone(), prms.x_r.clone() - prms.x_l.clone()); // todo make borrow parameters?
    cs.constrain(
        LinearCombination::<F>::from(delta_x_r_x_l) - (prms.y_r.clone() - prms.y_l.clone()),
    );

    // delta * (x_o - x_l) = - y_o - y_l
    let (_, _, delta_x_o_x_l) = cs.multiply(delta_lc.clone(), prms.x_o.clone() - prms.x_l.clone());
    cs.constrain(
        LinearCombination::<F>::from(delta_x_o_x_l) - (-prms.y_o.clone() - prms.y_l.clone()),
    );

    // delta * delta = x_o + x_r + x_l
    let (_, _, delta2) = cs.multiply(delta_lc.clone(), delta_lc.clone());
    cs.constrain(
        prms.x_o.clone() + prms.x_r.clone() + prms.x_l.clone()
            - LinearCombination::<F>::from(delta2),
    );
}

/// Enforce ()
pub fn checked_curve_addition<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    prms: &CurveAddition<F>,
    x_l_minus_x_r_inv: Option<F>,
) {
    let x_l_minus_x_r_inv_lc: LinearCombination<F> = cs.allocate(x_l_minus_x_r_inv).unwrap().into();
    not_zero(
        cs,
        prms.x_l.clone() - prms.x_r.clone(),
        x_l_minus_x_r_inv_lc,
    );
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
    h: GroupAffine<C>, // Constant
    commitment_x: LinearCombination<F>,
    commitment_y: LinearCombination<F>,
    commitment_x_tilde: LinearCombination<F>,
    commitment_y_tilde: LinearCombination<F>,
    commitment: Option<GroupAffine<C>>, // Witness provided by the prover
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

    let mut blinding_accumulator = GroupAffine::<C>::zero();
    let mut m_th_other_term = C::ScalarField::zero();
    let mut acc_i_minus_1_x_lc: LinearCombination<F> = Variable::One(PhantomData).into();
    let mut acc_i_minus_1_y_lc: LinearCombination<F> = Variable::One(PhantomData).into();
    // Define tables T_1 .. T_m, and witnesses
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

        let (index, x_l_minus_x_r_inv, delta, acc_i_x, acc_i_y) = match &r_bits {
            None => (None, None, None, None, None),
            Some(random_bits) => {
                let bi = (i - 1) * 3;
                let mut index = if bi < lambda && random_bits[bi] {
                    1usize
                } else {
                    0
                };
                if bi + 1 < lambda && random_bits[bi + 1] {
                    index += 2
                };
                if bi + 2 < lambda && random_bits[bi + 2] {
                    index += 4
                };
                let x_i_lookup = table.elems[0][index];
                let y_i_lookup = table.elems[1][index];
                let x_left = blinding_accumulator.x; // read before updating blinding accumulator
                let y_left = blinding_accumulator.y; // read before updating blinding accumulator
                let x_right = x_i_lookup;
                let y_right = y_i_lookup;
                // compute slope delta
                let delta = Some((y_right - y_left) / (x_right - x_left));
                let x_left_minus_x_right_inv = if i == m {
                    // compute x_l-x_r inverse for checked addition
                    Some(F::one() / (x_left - x_right))
                } else {
                    None
                };
                blinding_accumulator =
                    blinding_accumulator + GroupAffine::<C>::new(x_i_lookup, y_i_lookup, false);

                (
                    Some(index),
                    x_left_minus_x_right_inv,
                    delta,
                    Some(blinding_accumulator.x),
                    Some(blinding_accumulator.y),
                )
            }
        };

        let [x_table, y_table] = lookup(cs, &table, index).unwrap();

        // Allocate coordinated for the accumulated witness
        let acc_i_x_lc: LinearCombination<F> = cs.allocate(acc_i_x).unwrap().into();
        let acc_i_y_lc: LinearCombination<F> = cs.allocate(acc_i_y).unwrap().into();
        if i > 1 {
            // Enforce addition constraint:
            // R_i = R_i-1 + (x_i, y_i)
            let prms = CurveAddition {
                x_l: acc_i_minus_1_x_lc.clone(),
                y_l: acc_i_minus_1_y_lc.clone(),
                x_r: x_table,
                y_r: y_table,
                x_o: acc_i_x_lc.clone(),
                y_o: acc_i_y_lc.clone(),
                delta: delta,
            };
            if i == m {
                // enforce checked curve addition
                checked_curve_addition(cs, &prms, x_l_minus_x_r_inv);
            } else {
                // enforce incomplete curve addition
                incomplete_curve_addition(cs, &prms);
            }
        }
        acc_i_minus_1_x_lc = acc_i_x_lc;
        acc_i_minus_1_y_lc = acc_i_y_lc;
    }

    // constrain (x_tilde, y_tilde) = (x, y) + (R_m) - with checked addition
    let (delta, x_l_minus_x_r_inv) = match commitment {
        Some(commitment) => {
            let x_left = commitment.x;
            let y_left = commitment.y;
            let x_right = blinding_accumulator.x;
            let y_right = blinding_accumulator.y;
            let delta = (y_right - y_left) / (x_right - x_left);
            (Some(delta), Some(F::one() / (x_left - x_right)))
        }
        _ => (None, None),
    };
    let prms = CurveAddition {
        x_l: commitment_x,
        y_l: commitment_y,
        x_r: acc_i_minus_1_x_lc,
        y_r: acc_i_minus_1_y_lc,
        x_o: commitment_x_tilde,
        y_o: commitment_y_tilde,
        delta: delta,
    };
    checked_curve_addition(cs, &prms, x_l_minus_x_r_inv);
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
    type PallasScalar = <PallasP as ProjectiveCurve>::ScalarField;
    type VestaScalar = <VestaP as ProjectiveCurve>::ScalarField;

    #[test]
    fn add() {
        let mut rng = rand::thread_rng();
        let p = <PallasP as UniformRand>::rand(&mut rng);
        let pa = p.into_affine();
        let x_l: VestaScalar = (pa as PallasA).x;
        let y_l: VestaScalar = (pa as PallasA).y;

        let q = <PallasP as UniformRand>::rand(&mut rng);
        let qa = q.into_affine();
        let x_r: VestaScalar = (qa as PallasA).x;
        let y_r: VestaScalar = (qa as PallasA).y;

        assert!(x_l != x_r); // sanity check, should not happen except with negl. prob.

        let p_plus_q = p + q;
        let p_plus_qa = p_plus_q.into_affine();
        let x_o: VestaScalar = (p_plus_qa as PallasA).x;
        let y_o: VestaScalar = (p_plus_qa as PallasA).y;

        // sanity checks
        let delta = (y_r - y_l) / (x_r - x_l);
        assert_eq!(delta * (x_r - x_l), y_r - y_l);
        assert_eq!(delta * (x_o - x_l), -y_o - y_l);
        assert_eq!(delta * delta, x_l + x_r + x_o);

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(128, 1); // todo size

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut prover = Prover::new(&pc_gens, &mut transcript);
        let (x_l_comm, x_l_var) = prover.commit(x_l, VestaScalar::rand(&mut rng));
        let (y_l_comm, y_l_var) = prover.commit(y_l, VestaScalar::rand(&mut rng));
        let (x_r_comm, x_r_var) = prover.commit(x_r, VestaScalar::rand(&mut rng));
        let (y_r_comm, y_r_var) = prover.commit(y_r, VestaScalar::rand(&mut rng));
        let (x_o_comm, x_o_var) = prover.commit(x_o, VestaScalar::rand(&mut rng));
        let (y_o_comm, y_o_var) = prover.commit(y_o, VestaScalar::rand(&mut rng));
        let x_l_minus_x_r_inv = VestaScalar::from(1) / (x_l - x_r);

        let add_prms = CurveAddition {
            x_l: x_l_var.into(),
            y_l: y_l_var.into(),
            x_r: x_r_var.into(),
            y_r: y_r_var.into(),
            x_o: x_o_var.into(),
            y_o: y_o_var.into(),
            delta: Some(delta),
        };

        checked_curve_addition(&mut prover, &add_prms, Some(x_l_minus_x_r_inv));

        let proof = prover.prove(&bp_gens).unwrap();

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut verifier = Verifier::new(&mut transcript);

        let x_l_var = verifier.commit(x_l_comm);
        let y_l_var = verifier.commit(y_l_comm);
        let x_r_var = verifier.commit(x_r_comm);
        let y_r_var = verifier.commit(y_r_comm);
        let x_o_var = verifier.commit(x_o_comm);
        let y_o_var = verifier.commit(y_o_comm);

        let add_prms = CurveAddition {
            x_l: x_l_var.into(),
            y_l: y_l_var.into(),
            x_r: x_r_var.into(),
            y_r: y_r_var.into(),
            x_o: x_o_var.into(),
            y_o: y_o_var.into(),
            delta: None,
        };

        checked_curve_addition(&mut verifier, &add_prms, None);

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }

    #[test]
    fn test_re_randomize() {
        let mut rng = rand::thread_rng();
        let h = <PallasP as UniformRand>::rand(&mut rng).into_affine();
        let c = <PallasP as UniformRand>::rand(&mut rng).into_affine();
        let r: PallasScalar = <PallasA as AffineCurve>::ScalarField::rand(&mut rng);
        let blinding = h.mul(r).into_affine();
        let c_tilde = c + h;

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(1024, 1);

        let (proof, commitments) = {
            let mut transcript = Transcript::new(b"RerandGadget");
            let mut prover = Prover::new(&pc_gens, &mut transcript);
            let (c_x_comm, c_x_lc) = prover.commit(c.x, VestaScalar::rand(&mut rng));
            let (c_y_comm, c_y_lc) = prover.commit(c.y, VestaScalar::rand(&mut rng));
            let (c_tilde_x_comm, c_tilde_x_lc) =
                prover.commit(c_tilde.x, VestaScalar::rand(&mut rng));
            let (c_tilde_y_comm, c_tilde_y_lc) =
                prover.commit(c_tilde.y, VestaScalar::rand(&mut rng));

            re_randomize(
                &mut prover,
                h,
                c_x_lc.into(),
                c_y_lc.into(),
                c_tilde_x_lc.into(),
                c_tilde_y_lc.into(),
                Some(c),
                Some(r),
            );

            let proof = prover.prove(&bp_gens).unwrap();
            (proof, [c_x_comm, c_y_comm, c_tilde_x_comm, c_tilde_y_comm])
        };

        let mut transcript = Transcript::new(b"RerandGadget");
        let mut verifier = Verifier::new(&mut transcript);
        let vars = commitments.map(|c| verifier.commit(c));

        re_randomize(
            &mut verifier,
            h,
            vars[0].into(),
            vars[1].into(),
            vars[2].into(),
            vars[3].into(),
            None,
            None,
        );

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }
}
