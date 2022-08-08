#[allow(unused)] // todo
use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use ark_ec::AffineCurve;
use merlin::Transcript;
use std::marker::PhantomData;

fn curve_check<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    x: LinearCombination<C::ScalarField>,
    y: LinearCombination<C::ScalarField>,
    a: C::ScalarField,
    b: C::ScalarField,
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
fn incomplete_curve_addition<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    // todo pass points as structs (or single struct with delta?) with conversion from the other curve
    x1: LinearCombination<C::ScalarField>,
    y1: LinearCombination<C::ScalarField>,
    x2: LinearCombination<C::ScalarField>,
    y2: LinearCombination<C::ScalarField>,
    x3: LinearCombination<C::ScalarField>,
    y3: LinearCombination<C::ScalarField>,
    delta: LinearCombination<C::ScalarField>, // free variable
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
fn checked_curve_addition<C: AffineCurve, Cs: ConstraintSystem<C>>(
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

// todo why are other implementations much more complex? Am I missing something?
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
