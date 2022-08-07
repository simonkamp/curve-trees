use bulletproofs::r1cs::*;

use ark_ec::AffineCurve;

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

fn curve_addition<C: AffineCurve, Cs: ConstraintSystem<C>>(cs: &mut Cs) {}
