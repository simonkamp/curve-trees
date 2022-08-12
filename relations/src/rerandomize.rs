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
use ark_std::{One, Zero};
use merlin::Transcript;
use std::{borrow::BorrowMut, marker::PhantomData};

pub fn build_simple_tables<C: SWModelParameters>(
    h: GroupAffine<C>,
) -> Vec<Lookup3Bit<2, C::BaseField>> {
    // build tables as in zcash spec
    let lambda = <C::ScalarField as PrimeField>::size_in_bits();
    let m = lambda / 3 + 1;

    // Define tables T_1 .. T_m, and witnesses
    let mut tables = Vec::with_capacity(m);
    let mut m_th_right_term = C::ScalarField::zero();
    for i in 1..m + 1 {
        let mut table = Lookup3Bit::<2, C::BaseField> {
            elems: [[C::BaseField::one(); WINDOW_ELEMS]; 2],
        };
        for j in 0..WINDOW_ELEMS {
            let s = C::ScalarField::from(j as u64)
                * C::ScalarField::from(2u64).pow(&[3u64 * (i - 1) as u64]);
            // Multiply blinding by s
            let hs = h.mul(s).into_affine();
            table.elems[0][j] = hs.x;
            table.elems[1][j] = hs.y;
        }
        tables.push(table);
    }
    tables
}

pub fn build_tables<C: SWModelParameters>(h: GroupAffine<C>) -> Vec<Lookup3Bit<2, C::BaseField>> {
    let lambda = <C::ScalarField as PrimeField>::size_in_bits();
    let m = lambda / 3 + 1;

    // Define tables T_1 .. T_m, and witnesses
    let mut tables = Vec::with_capacity(m);
    let mut m_th_right_term = C::ScalarField::zero();
    for i in 1..m + 1 {
        let mut table = Lookup3Bit::<2, C::BaseField> {
            elems: [[C::BaseField::one(); WINDOW_ELEMS]; 2],
        };
        // 2^(3*(i - 1))
        let j_term = C::ScalarField::from(2u64).pow(&[3u64 * (i - 1) as u64]);
        let right_term = if i < m {
            // 2^(3*i)
            let right_term = C::ScalarField::from(2u64).pow(&[3u64 * i as u64]);
            // add right term to the sum in the mth iteration right term
            m_th_right_term += right_term;
            right_term
        } else {
            // subtract sum of all previous right terms: for i = 1..m-1 { 2^(3* i) }
            -m_th_right_term
        };
        for j in 0..WINDOW_ELEMS {
            // s = j * 2^(3*i) + right_term
            let s = (C::ScalarField::from(j as u64) * j_term) + right_term;
            // Multiply blinding by s
            let hs = h.mul(s).into_affine();
            // todo account for hs = 0 or make sure that it can never happen.
            table.elems[0][j] = hs.x;
            table.elems[1][j] = hs.y;
        }
        tables.push(table);
    }
    tables
}

pub fn re_randomize<F: Field, C: SWModelParameters<BaseField = F>, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    tables: &Vec<Lookup3Bit<2, F>>,
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
    let mut acc_i_minus_1_x_lc: LinearCombination<F> = Variable::One(PhantomData).into();
    let mut acc_i_minus_1_y_lc: LinearCombination<F> = Variable::One(PhantomData).into();
    // Define tables T_1 .. T_m, and witnesses
    for i in 1..m + 1 {
        let mut table = tables[i - 1];

        let (index, x_l_minus_x_r_inv, delta, acc_i_x, acc_i_y) = match &r_bits {
            None => (None, None, None, None, None),
            Some(random_bits) => {
                let bi = (i - 1) * 3;
                let mut index: usize = if bi < lambda && random_bits[bi] { 1 } else { 0 };
                if bi + 1 < lambda && random_bits[bi + 1] {
                    index += 2;
                };
                if bi + 2 < lambda && random_bits[bi + 2] {
                    index += 4;
                };
                let x_i_lookup = table.elems[0][index];
                let y_i_lookup = table.elems[1][index];
                let x_left = blinding_accumulator.x; // read before updating blinding accumulator
                let y_left = blinding_accumulator.y; // read before updating blinding accumulator
                let x_right = x_i_lookup;
                let y_right = y_i_lookup;
                // compute slope delta
                let delta = if i != 1 {
                    Some((y_right - y_left) / (x_right - x_left))
                } else {
                    None
                };
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

        // Allocate coordinates for the accumulated witness
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
    fn test_re_randomize() {
        let mut rng = rand::thread_rng();
        let h = PallasP::rand(&mut rng).into_affine();
        let c = PallasP::rand(&mut rng).into_affine();
        let r: PallasScalar = <PallasA as AffineCurve>::ScalarField::rand(&mut rng);
        let blinding = h.mul(r).into_affine();
        let c_tilde = c + blinding;

        let tables = build_tables(h);

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(1024, 1);

        let proof = {
            let mut transcript = Transcript::new(b"RerandGadget");
            let mut prover = Prover::new(&pc_gens, &mut transcript);
            let c_x_var = prover.allocate(Some(c.x)).unwrap();
            let c_y_var = prover.allocate(Some(c.y)).unwrap();
            let c_x_tilde_var = prover.allocate(Some(c_tilde.x)).unwrap();
            let c_y_tilde_var = prover.allocate(Some(c_tilde.y)).unwrap();

            re_randomize(
                &mut prover,
                &tables,
                c_x_var.into(),
                c_y_var.into(),
                c_x_tilde_var.into(),
                c_y_tilde_var.into(),
                Some(c),
                Some(r),
            );

            let proof = prover.prove(&bp_gens).unwrap();
            proof
        };

        let mut transcript = Transcript::new(b"RerandGadget");
        let mut verifier: Verifier<_, VestaA> = Verifier::new(&mut transcript);
        let c_x_var = verifier.allocate(None).unwrap();
        let c_y_var = verifier.allocate(None).unwrap();
        let c_x_tilde_var = verifier.allocate(None).unwrap();
        let c_y_tilde_var = verifier.allocate(None).unwrap();

        re_randomize::<_, pasta::pallas::PallasParameters, _>(
            &mut verifier,
            &tables,
            c_x_var.into(),
            c_y_var.into(),
            c_x_tilde_var.into(),
            c_y_tilde_var.into(),
            None,
            None,
        );

        // todo final msm fails
        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }

    #[test]
    fn test_simple_tables() {
        // testing a simplified fixed base table multiplication using the 3bit tables described in Zcash spec
        let mut rng = rand::thread_rng();
        let h = PallasP::rand(&mut rng).into_affine();
        let r: PallasScalar = <PallasA as AffineCurve>::ScalarField::rand(&mut rng);
        let h_r = h.mul(r).into_affine();

        let tables = build_simple_tables(h);
        let lambda = <PallasScalar as PrimeField>::size_in_bits();
        let m = lambda / 3 + 1;
        let r_bigint: <PallasScalar as PrimeField>::BigInt = r.into();
        let random_bits = r_bigint.to_bits_le();
        let mut h_r_acc = PallasA::zero();
        let mut r_acc = PallasScalar::zero();
        for i in 1..m + 1 {
            // n.b. i is 0 indexed
            let mut table = tables[i - 1];
            let bi = (i - 1) * 3;
            let mut index = if bi < lambda && random_bits[bi] {
                1usize
            } else {
                0
            };
            if bi + 1 < lambda && random_bits[bi + 1] {
                index += 2;
            };
            if bi + 2 < lambda && random_bits[bi + 2] {
                index += 4;
            };
            let t_i = if index == 0 {
                // handle the infinity point explicitly
                PallasA::zero()
            } else {
                // otherwise the field elements in the table form a point
                let x_i = table.elems[0][index];
                let y_i = table.elems[1][index];
                PallasA::new(x_i, y_i, false)
            };
            h_r_acc += &t_i;

            r_acc = r_acc
                + PallasScalar::from(2u8).pow(&[3u64 * (i - 1) as u64])
                    * PallasScalar::from(index as u64);
        }
        assert_eq!(r, r_acc.into(), "Bit decomposition.");
        assert_eq!(h_r, h_r_acc, "Table multiplication.");
    }

    #[test]
    fn test_tables() {
        let mut rng = rand::thread_rng();
        let h = PallasP::rand(&mut rng).into_affine();
        let r: PallasScalar = <PallasA as AffineCurve>::ScalarField::rand(&mut rng);
        // let r = PallasScalar::from(1u8);
        let h_r = h.mul(r).into_affine();

        let tables = build_tables(h);
        let lambda = <PallasScalar as PrimeField>::size_in_bits();
        let m = lambda / 3 + 1;
        let r_bigint: <PallasScalar as PrimeField>::BigInt = r.into();
        let random_bits = r_bigint.to_bits_le();
        let mut h_r_acc = PallasA::zero();
        for i in 1..m + 1 {
            // n.b. i is 0 indexed
            let mut table = tables[i - 1];
            let bi = (i - 1) * 3;
            let mut index = if bi < lambda && random_bits[bi] {
                1usize
            } else {
                0
            };
            if bi + 1 < lambda && random_bits[bi + 1] {
                index += 2;
            };
            if bi + 2 < lambda && random_bits[bi + 2] {
                index += 4;
            };
            let x_i = table.elems[0][index];
            let y_i = table.elems[1][index];
            let t_i = PallasA::new(x_i, y_i, false);
            h_r_acc += &t_i;
        }
        assert_eq!(h_r, h_r_acc);
    }
}
