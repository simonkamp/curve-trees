use bulletproofs::r1cs::*;

use ark_ec::AffineCurve;
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

    // x^3 + A*X^2 + B - y^2 = 0
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
    delta: LinearCombination<C::ScalarField>, // free variable
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
