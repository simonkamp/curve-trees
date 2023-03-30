use bulletproofs::r1cs::*;

use crate::curve::*;
use crate::lookup::*;

use ark_ec::{
    models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, AffineRepr, CurveGroup,
};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::{One, Zero};
use std::marker::PhantomData;

pub fn build_tables<C: AffineRepr>(h: C) -> Vec<Lookup3Bit<2, C::BaseField>> {
    let lambda = <C::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize;
    let m = lambda / 3 + 1;

    // Define tables T_1 .. T_m, and witnesses
    let mut tables = Vec::with_capacity(m);
    let mut m_th_right_term = C::ScalarField::zero();
    for i in 1..m + 1 {
        let mut table = Lookup3Bit::<2, C::BaseField> {
            elems: [[C::BaseField::one(); WINDOW_ELEMS]; 2],
        };
        // 2^(3*(i - 1))
        let j_term = C::ScalarField::from(2u64).pow([3u64 * (i - 1) as u64]);
        let right_term = if i < m {
            // 2^(3*i)
            let right_term = C::ScalarField::from(2u64).pow([3u64 * i as u64]);
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
            table.elems[0][j] = *hs.x().unwrap();
            table.elems[1][j] = *hs.y().unwrap();
        }
        tables.push(table);
    }
    tables
}

pub fn re_randomize<
    F: Field,
    S: PrimeField,
    P: SWCurveConfig<BaseField = F, ScalarField = S>,
    Cs: ConstraintSystem<F>,
>(
    cs: &mut Cs,
    tables: &[Lookup3Bit<2, F>],
    commitment: PointRepresentation<F, Affine<P>>,
    commitment_x_tilde: LinearCombination<F>,
    commitment_y_tilde: LinearCombination<F>,
    randomness: Option<S>, // Witness provided by the prover
) {
    let lambda = S::MODULUS_BIT_SIZE as usize;
    let m = lambda / 3 + 1;

    let r_bits = match randomness {
        None => None,
        Some(r) => {
            let r: S::BigInt = r.into();
            Some(r.to_bits_le())
        }
    };

    let mut blinding_accumulator = Affine::<P>::zero();
    let mut acc_i_minus_1_x_lc: LinearCombination<F> = Variable::One(PhantomData).into();
    let mut acc_i_minus_1_y_lc: LinearCombination<F> = Variable::One(PhantomData).into();
    // Define tables T_1 .. T_m, and witnesses
    for i in 1..m + 1 {
        let table = tables[i - 1];

        let (index, x_l_minus_x_r_inv, delta, acc_i_x, acc_i_y) = match &r_bits {
            None => (None, None, None, None, None),
            Some(random_bits) => {
                let bi = (i - 1) * 3;
                let mut index: usize = usize::from(bi < lambda && random_bits[bi]);
                if bi + 1 < lambda && random_bits[bi + 1] {
                    index += 2;
                };
                if bi + 2 < lambda && random_bits[bi + 2] {
                    index += 4;
                };
                let x_i_lookup = table.elems[0][index];
                let y_i_lookup = table.elems[1][index];
                let x_left = if i == 1 {
                    F::zero()
                } else {
                    *blinding_accumulator.x().unwrap()
                }; // read before updating blinding accumulator
                let y_left = if i == 1 {
                    F::zero()
                } else {
                    *blinding_accumulator.y().unwrap()
                }; // read before updating blinding accumulator
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
                    (blinding_accumulator + Affine::<P>::new(x_i_lookup, y_i_lookup)).into();

                (
                    Some(index),
                    x_left_minus_x_right_inv,
                    delta,
                    Some(*blinding_accumulator.x().unwrap()),
                    Some(*blinding_accumulator.y().unwrap()),
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
                delta,
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
    let (delta, x_l_minus_x_r_inv) = match commitment.witness {
        Some(commitment) => {
            let x_left = commitment.x().unwrap();
            let y_left = commitment.y().unwrap();
            let x_right = blinding_accumulator.x().unwrap();
            let y_right = blinding_accumulator.y().unwrap();
            let delta = (*y_right - y_left) / (*x_right - x_left);
            (Some(delta), Some(F::one() / (*x_left - x_right)))
        }
        _ => (None, None),
    };
    let prms = CurveAddition {
        x_l: commitment.x,
        y_l: commitment.y,
        x_r: acc_i_minus_1_x_lc,
        y_r: acc_i_minus_1_y_lc,
        x_o: commitment_x_tilde,
        y_o: commitment_y_tilde,
        delta,
    };
    checked_curve_addition(cs, &prms, x_l_minus_x_r_inv);
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::PallasConfig;
    use bulletproofs::{BulletproofGens, PedersenGens};

    use ark_ec::CurveGroup;
    use ark_pallas::Affine as PallasA;
    use ark_std::UniformRand;
    use ark_vesta::Affine as VestaA;
    use merlin::Transcript;
    type PallasScalar = <PallasA as AffineRepr>::ScalarField;

    #[test]
    fn test_re_randomize() {
        let mut rng = rand::thread_rng();
        let h = PallasA::rand(&mut rng);
        let c = PallasA::rand(&mut rng);
        let r: PallasScalar = <PallasA as AffineRepr>::ScalarField::rand(&mut rng);
        let blinding = h * r;
        let c_tilde = (c + blinding).into_affine();

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
                PointRepresentation {
                    x: c_x_var.into(),
                    y: c_y_var.into(),
                    witness: Some(c),
                },
                c_x_tilde_var.into(),
                c_y_tilde_var.into(),
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

        re_randomize::<_, _, PallasConfig, _>(
            &mut verifier,
            &tables,
            PointRepresentation {
                x: c_x_var.into(),
                y: c_y_var.into(),
                witness: None,
            },
            c_x_tilde_var.into(),
            c_y_tilde_var.into(),
            None,
        );

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }

    #[test]
    fn test_tables() {
        let mut rng = rand::thread_rng();
        let h = PallasA::rand(&mut rng);
        let r: PallasScalar = <PallasA as AffineRepr>::ScalarField::rand(&mut rng);
        let h_r = h * r;

        let tables = build_tables(h);
        let lambda = <PallasScalar as PrimeField>::MODULUS_BIT_SIZE as usize;
        let m = lambda / 3 + 1;
        let r_bigint: <PallasScalar as PrimeField>::BigInt = r.into();
        let random_bits = r_bigint.to_bits_le();
        let mut h_r_acc = PallasA::zero();
        for i in 1..m + 1 {
            // n.b. i is 0 indexed
            let table = tables[i - 1];
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
            let t_i = PallasA::new(x_i, y_i);
            h_r_acc = (h_r_acc + &t_i).into();
        }
        assert_eq!(h_r, h_r_acc);
    }
}
