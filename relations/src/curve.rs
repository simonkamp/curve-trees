use ark_ec::{short_weierstrass_jacobian::GroupAffine, AffineCurve, SWModelParameters};
use ark_ff::Field;
use bulletproofs::r1cs::*;
use std::marker::PhantomData;

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
    // todo can anything be optimized by checking for a = 0?
}

/// A point represented by variables corresponding to its affine coordinates and optionally the value of those,
/// which must be known by the prover.
pub struct PointRepresentation<F: Field, C: AffineCurve<BaseField = F>> {
    pub x: LinearCombination<F>,
    pub y: LinearCombination<F>,
    pub witness: Option<C>, // Some(x,y) for the prover, otherwise None
}

/// Given variables representing the coordinates of two points returns two variables representing the sum.
/// The prover must additionally provide the two summands as input and gets the sum as output.
pub fn incomplete_curve_addition_helper<
    F: Field,
    Cs: ConstraintSystem<F>,
    P: SWModelParameters<BaseField = F>,
>(
    cs: &mut Cs,
    left: PointRepresentation<F, GroupAffine<P>>,
    right: PointRepresentation<F, GroupAffine<P>>,
) -> PointRepresentation<F, GroupAffine<P>> {
    let (out_witness, delta) = match (left.witness, right.witness) {
        (Some(left), Some(right)) => {
            let out = left + right;
            let delta = (right.y - left.y) / (right.x - left.x);
            (Some(out), Some(delta))
        }
        _ => (None, None),
    };
    let x_out = cs.allocate(out_witness.map(|o| o.x)).unwrap();
    let y_out = cs.allocate(out_witness.map(|o| o.y)).unwrap();
    incomplete_curve_addition(
        cs,
        &CurveAddition {
            x_l: left.x,
            y_l: left.y,
            x_r: right.x,
            y_r: right.y,
            x_o: x_out.into(),
            y_o: y_out.into(),
            delta: delta,
        },
    );
    PointRepresentation {
        x: x_out.into(),
        y: y_out.into(),
        witness: out_witness,
    }
}

/// Given variables representing the coordinates of two points returns two variables representing the sum
/// and checks that the result is not point at inf.
/// The prover must additionally provide the two summands as input and gets the sum as output.
pub fn checked_curve_addition_helper<
    F: Field,
    Cs: ConstraintSystem<F>,
    P: SWModelParameters<BaseField = F>,
>(
    cs: &mut Cs,
    left: PointRepresentation<F, GroupAffine<P>>,
    right: PointRepresentation<F, GroupAffine<P>>,
) -> PointRepresentation<F, GroupAffine<P>> {
    let (out_witness, delta, x_l_minus_x_r_inv) = match (left.witness, right.witness) {
        (Some(left), Some(right)) => {
            let out = left + right;
            let delta = (right.y - left.y) / (right.x - left.x);
            assert_ne!(left.x, right.x);
            let x_l_minus_x_r_inv = F::one() / (left.x - right.x);
            (Some(out), Some(delta), Some(x_l_minus_x_r_inv))
        }
        _ => (None, None, None),
    };
    let x_out = cs.allocate(out_witness.map(|o| o.x)).unwrap();
    let y_out = cs.allocate(out_witness.map(|o| o.y)).unwrap();
    checked_curve_addition(
        cs,
        &CurveAddition {
            x_l: left.x,
            y_l: left.y,
            x_r: right.x,
            y_r: right.y,
            x_o: x_out.into(),
            y_o: y_out.into(),
            delta: delta,
        },
        x_l_minus_x_r_inv,
    );
    PointRepresentation {
        x: x_out.into(),
        y: y_out.into(),
        witness: out_witness,
    }
}

#[derive(Clone, Debug)]
pub struct CurveAddition<F: Field> {
    pub x_l: LinearCombination<F>,
    pub y_l: LinearCombination<F>,
    pub x_r: LinearCombination<F>,
    pub y_r: LinearCombination<F>,
    pub x_o: LinearCombination<F>,
    pub y_o: LinearCombination<F>,
    pub delta: Option<F>,
}

/// Enforce points over C::ScalarField: (x_o, y_o) = (x_l, y_l) + (x_r, y_r)
/// Takes the slope (delta) as input from the prover
pub fn incomplete_curve_addition<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    prms: &CurveAddition<F>,
) {
    let delta_lc: LinearCombination<F> = cs.allocate(prms.delta).unwrap().into();
    // delta * (x_r - x_l) = y_r - y_l
    let (_, _, delta_x_r_x_l) = cs.multiply(delta_lc.clone(), prms.x_r.clone() - prms.x_l.clone());
    cs.constrain(
        LinearCombination::<F>::from(delta_x_r_x_l) - (prms.y_r.clone() - prms.y_l.clone()),
    );

    // delta * (x_o - x_l) = - y_o - y_l
    let (_, _, delta_x_o_x_l) = cs.multiply(delta_lc.clone(), prms.x_o.clone() - prms.x_l.clone());
    cs.constrain(
        LinearCombination::<F>::from(delta_x_o_x_l) - (-prms.y_o.clone() - prms.y_l.clone()),
    );

    // delta * delta = x_o + x_r + x_l
    let (_, _, delta2) = cs.multiply(delta_lc.clone(), delta_lc);
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
    // todo check on curve?
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

#[cfg(test)]
mod tests {
    use super::*;

    use ark_ec::ProjectiveCurve;
    use ark_std::{One, UniformRand, Zero};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use pasta::{
        pallas::Affine as PallasA, pallas::Projective as PallasP, vesta::Affine as VestaA,
        vesta::Projective as VestaP,
    };
    type VestaScalar = <VestaP as ProjectiveCurve>::ScalarField;
    use merlin::Transcript;

    #[test]
    fn test_curve_addition() {
        let mut rng = rand::thread_rng();
        let p = <PallasP as UniformRand>::rand(&mut rng);
        let pa = p.into_affine();
        let x_l: VestaScalar = (pa as PallasA).x;
        let y_l: VestaScalar = (pa as PallasA).y;

        let q = <PallasP as UniformRand>::rand(&mut rng);
        let qa = q.into_affine();
        let x_r: VestaScalar = (qa as PallasA).x;
        let y_r: VestaScalar = (qa as PallasA).y;

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
        let bp_gens = BulletproofGens::<VestaA>::new(8, 1);

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut prover = Prover::new(&pc_gens, &mut transcript);
        let (x_l_comm, x_l_var) = prover.commit(x_l, VestaScalar::rand(&mut rng));
        let (y_l_comm, y_l_var) = prover.commit(y_l, VestaScalar::rand(&mut rng));
        let (x_r_comm, x_r_var) = prover.commit(x_r, VestaScalar::rand(&mut rng));
        let (y_r_comm, y_r_var) = prover.commit(y_r, VestaScalar::rand(&mut rng));
        let (x_o_comm, x_o_var) = prover.commit(x_o, VestaScalar::rand(&mut rng));
        let (y_o_comm, y_o_var) = prover.commit(y_o, VestaScalar::rand(&mut rng));
        let x_l_minus_x_r_inv = VestaScalar::one() / (x_l - x_r);

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
    fn test_curve_addition_helper() {
        let mut rng = rand::thread_rng();
        let p = <PallasP as UniformRand>::rand(&mut rng);
        let pa = p.into_affine();
        let x_l: VestaScalar = (pa as PallasA).x;
        let y_l: VestaScalar = (pa as PallasA).y;

        let q = <PallasP as UniformRand>::rand(&mut rng);
        let qa = q.into_affine();
        let x_r: VestaScalar = (qa as PallasA).x;
        let y_r: VestaScalar = (qa as PallasA).y;

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(8, 1);

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut prover = Prover::new(&pc_gens, &mut transcript);
        let (x_l_comm, x_l_var) = prover.commit(x_l, VestaScalar::rand(&mut rng));
        let (y_l_comm, y_l_var) = prover.commit(y_l, VestaScalar::rand(&mut rng));
        let (x_r_comm, x_r_var) = prover.commit(x_r, VestaScalar::rand(&mut rng));
        let (y_r_comm, y_r_var) = prover.commit(y_r, VestaScalar::rand(&mut rng));

        let addition_result = incomplete_curve_addition_helper(
            &mut prover,
            PointRepresentation {
                x: x_l_var.into(),
                y: y_l_var.into(),
                witness: Some(pa),
            },
            PointRepresentation {
                x: x_r_var.into(),
                y: y_r_var.into(),
                witness: Some(qa),
            },
        );
        assert_eq!(
            addition_result.witness.map(|out| out == (p + q)),
            Some(true)
        );

        let proof = prover.prove(&bp_gens).unwrap();

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut verifier = Verifier::new(&mut transcript);

        let x_l_var = verifier.commit(x_l_comm);
        let y_l_var = verifier.commit(y_l_comm);
        let x_r_var = verifier.commit(x_r_comm);
        let y_r_var = verifier.commit(y_r_comm);
        incomplete_curve_addition_helper::<_, _, pasta::pallas::PallasParameters>(
            &mut verifier,
            PointRepresentation {
                x: x_l_var.into(),
                y: y_l_var.into(),
                witness: None,
            },
            PointRepresentation {
                x: x_r_var.into(),
                y: y_r_var.into(),
                witness: None,
            },
        );

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }

    #[test]
    fn test_checked_curve_addition_helper() {
        let mut rng = rand::thread_rng();
        let p = <PallasP as UniformRand>::rand(&mut rng);
        let pa = p.into_affine();
        let x_l: VestaScalar = (pa as PallasA).x;
        let y_l: VestaScalar = (pa as PallasA).y;

        let q = <PallasP as UniformRand>::rand(&mut rng);
        let qa = q.into_affine();
        let x_r: VestaScalar = (qa as PallasA).x;
        let y_r: VestaScalar = (qa as PallasA).y;

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(8, 1);

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut prover = Prover::new(&pc_gens, &mut transcript);
        let (x_l_comm, x_l_var) = prover.commit(x_l, VestaScalar::rand(&mut rng));
        let (y_l_comm, y_l_var) = prover.commit(y_l, VestaScalar::rand(&mut rng));
        let (x_r_comm, x_r_var) = prover.commit(x_r, VestaScalar::rand(&mut rng));
        let (y_r_comm, y_r_var) = prover.commit(y_r, VestaScalar::rand(&mut rng));

        let addition_result = checked_curve_addition_helper(
            &mut prover,
            PointRepresentation {
                x: x_l_var.into(),
                y: y_l_var.into(),
                witness: Some(pa),
            },
            PointRepresentation {
                x: x_r_var.into(),
                y: y_r_var.into(),
                witness: Some(qa),
            },
        );
        assert_eq!(
            addition_result
                .witness
                .map(|out| out == (p + q) && out != PallasA::zero()),
            Some(true)
        );

        let proof = prover.prove(&bp_gens).unwrap();

        let mut transcript = Transcript::new(b"CurveAdditionGadget");
        let mut verifier = Verifier::new(&mut transcript);

        let x_l_var = verifier.commit(x_l_comm);
        let y_l_var = verifier.commit(y_l_comm);
        let x_r_var = verifier.commit(x_r_comm);
        let y_r_var = verifier.commit(y_r_comm);
        checked_curve_addition_helper::<_, _, pasta::pallas::PallasParameters>(
            &mut verifier,
            PointRepresentation {
                x: x_l_var.into(),
                y: y_l_var.into(),
                witness: None,
            },
            PointRepresentation {
                x: x_r_var.into(),
                y: y_r_var.into(),
                witness: None,
            },
        );

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }
}
