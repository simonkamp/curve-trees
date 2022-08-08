#[allow(unused)]
#[allow(unused_imports)]

use bulletproofs::r1cs::*;

use ark_ec::AffineCurve;
use ark_ff::{Field, One, Zero};

const WINDOW_SIZE: usize = 3;
pub const WINDOW_ELEMS: usize = 1 << WINDOW_SIZE;

pub struct Lookup3Bit<const N: usize, F: Field> {
    pub elems: [[F; WINDOW_ELEMS]; N],
}

fn b2f<F: Field>(v: bool) -> F {
    if v {
        F::one()
    } else {
        F::zero()
    }
}

fn is_bit<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    var: LinearCombination<C::ScalarField>,
) {
    let (_, _, zero) = cs.multiply(var.clone(), var - C::ScalarField::one());
    cs.constrain(zero.into());
}

fn bit<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    val: Option<bool>,
) -> Result<Variable<C::ScalarField>, R1CSError> {
    // compute assignment (if witness is provided)
    let assignment = val.map(|b| {
        let s = if b {
            C::ScalarField::one()
        } else {
            C::ScalarField::zero()
        };
        (s, s - C::ScalarField::one())
    });

    // alloc multiplication
    let (bit, bit_inv, zero) = cs.allocate_multiplier(assignment)?;

    // check bit_inv and bit relation
    cs.constrain(bit_inv - (bit - C::ScalarField::one()));

    // check that product is zero
    cs.constrain(zero.into());

    Ok(bit)
}

fn single_membership<C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    u: &[C::ScalarField; WINDOW_ELEMS],
    sa: LinearCombination<C::ScalarField>, // product
    s0: LinearCombination<C::ScalarField>, // bit
    s1: LinearCombination<C::ScalarField>, // bit
    s2: LinearCombination<C::ScalarField>, // bit
) -> LinearCombination<C::ScalarField> {
    // left side
    let (_, _, left): (
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
    ) = cs.multiply(s0.clone(), {
        let f = -(sa.clone() * u[0]) + (s2.clone() * u[0]) + (s1.clone() * u[0]) - u[0]
            + (sa.clone() * u[2]);
        let f = f - (s1.clone() * u[2]) + (sa.clone() * u[4])
            - (s2.clone() * u[4])
            - (sa.clone() * u[6]);
        let f = f + (sa.clone() * u[1]) - (s2.clone() * u[1]) - (s1.clone() * u[1]) + u[1]
            - (sa.clone() * u[3]);
        let f = f + (s1.clone() * u[3]) - (sa.clone() * u[5])
            + (s2.clone() * u[5])
            + (sa.clone() * u[7]);
        f
    });

    // right size
    let right = -(sa.clone() * u[0]) + (s2.clone() * u[0]) + (s1.clone() * u[0]) - u[0]
        + (sa.clone() * u[2]);
    let right = right - (s1.clone() * u[2]) + (sa.clone() * u[4])
        - (s2.clone() * u[4])
        - (sa.clone() * u[6]);

    // sum is the element
    left - right
}

impl<const N: usize, F: Field> Lookup3Bit<N, F> {
    fn lookup(&self, index: usize) -> [F; N] {
        assert!(index < WINDOW_ELEMS);
        let val: Vec<_> = (0..N).map(|i| self.elems[i][index].clone()).collect();
        val.try_into().unwrap()
    }
}

// The witness (provided when proving/None when verifying) is the secret index
pub fn lookup<const N: usize, C: AffineCurve, Cs: ConstraintSystem<C>>(
    cs: &mut Cs,
    table: &Lookup3Bit<N, C::ScalarField>,
    index: Option<usize>,
) -> Result<[LinearCombination<C::ScalarField>; N], R1CSError> {
    // compute multiplication of higher bits
    let (b1, b2, ba) =
        cs.allocate_multiplier(index.map(|i| (b2f((i >> 1) & 1 == 1), b2f((i >> 2) & 1 == 1))))?;

    // enforce bits
    let b0 = bit::<C, Cs>(cs, index.map(|i| (i & 1) == 1))?;
    is_bit(cs, b1.into());
    is_bit(cs, b2.into());

    // enforce membership
    let mut res: Vec<LinearCombination<_>> = Vec::with_capacity(N);
    for i in 0..N {
        res.push(single_membership(
            cs,
            &table.elems[i],
            ba.into(),
            b0.into(),
            b1.into(),
            b2.into(),
        ));
    }

    Ok(res.try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;

    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;

    use rand::thread_rng;
    use rand::Rng;

    use pasta;

    /*
    #[test]
    fn test_lookup() {


        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let mut rng = thread_rng();

        let u: [F; 8] = [
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
        ];

        let b0: bool = rng.gen();
        let b1: bool = rng.gen();
        let b2: bool = rng.gen();

    }
    */
}
