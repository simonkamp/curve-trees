use ark_ff::fields::Field;
use bulletproofs::r1cs::*;

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn range_proof<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut v: LinearCombination<F>,
    v_assignment: Option<u64>,
    n: usize,
) -> Result<(), R1CSError> {
    let mut exp_2 = F::one();
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate_multiplier(v_assignment.map(|q| {
            let bit: u64 = (q >> i) & 1;
            ((1 - bit).into(), bit.into())
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - constant(1u64)));

        // Add `-b_i*2^i` to the linear combination
        // in order to form the following constraint by the end of the loop:
        // v = Sum(b_i * 2^i, i = 0..n-1)
        v = v - b * exp_2;

        exp_2 = exp_2 + exp_2;
    }

    // Enforce that v = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(v);

    Ok(())
}
