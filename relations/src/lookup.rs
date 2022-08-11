#![allow(unused)]
use bulletproofs::r1cs::*;

use ark_ec::AffineCurve;
use ark_ff::{Field, One, Zero};

const WINDOW_SIZE: usize = 3;
pub const WINDOW_ELEMS: usize = 1 << WINDOW_SIZE;

#[derive(Copy, Clone, Debug)]
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

pub fn is_bit<F: Field, Cs: ConstraintSystem<F>>(cs: &mut Cs, var: LinearCombination<F>) {
    let (_, _, zero) = cs.multiply(var.clone(), var - F::one());
    cs.constrain(zero.into());
}

fn bit<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    val: Option<bool>,
) -> Result<Variable<F>, R1CSError> {
    // compute assignment (if witness is provided)
    let assignment = val.map(|b| {
        let s = if b { F::one() } else { F::zero() };
        (s, s - F::one())
    });

    // alloc multiplication
    let (bit, bit_inv, zero) = cs.allocate_multiplier(assignment)?;

    // check bit_inv and bit relation
    cs.constrain(bit_inv - (bit - F::one()));

    // check that product is zero
    cs.constrain(zero.into());

    Ok(bit)
}

fn single_membership<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    u: &[F; WINDOW_ELEMS],
    sa: LinearCombination<F>, // product
    s0: LinearCombination<F>, // bit
    s1: LinearCombination<F>, // bit
    s2: LinearCombination<F>, // bit
) -> LinearCombination<F> {
    // left side
    let (_, _, left): (Variable<F>, Variable<F>, Variable<F>) = cs.multiply(s0, {
        let f = -(sa.clone() * u[0]) + (s2.clone() * u[0]) + (s1.clone() * u[0]) - u[0]
            + (sa.clone() * u[2]);
        let f = f - (s1.clone() * u[2]) + (sa.clone() * u[4])
            - (s2.clone() * u[4])
            - (sa.clone() * u[6]);
        let f = f + (sa.clone() * u[1]) - (s2.clone() * u[1]) - (s1.clone() * u[1]) + u[1]
            - (sa.clone() * u[3]);
        f + (s1.clone() * u[3]) - (sa.clone() * u[5]) + (s2.clone() * u[5]) + (sa.clone() * u[7])
    });

    // right side
    let right = -(sa.clone() * u[0]) + (s2.clone() * u[0]) + (s1.clone() * u[0]) - u[0]
        + (sa.clone() * u[2]);
    let right = right - (s1 * u[2]) + (sa.clone() * u[4]) - (s2 * u[4]) - (sa * u[6]);

    // sum is the element
    left - right
}

impl<const N: usize, F: Field> Lookup3Bit<N, F> {
    fn lookup(&self, index: usize) -> [F; N] {
        assert!(index < WINDOW_ELEMS);
        let val: Vec<_> = (0..N).map(|i| self.elems[i][index]).collect();
        val.try_into().unwrap()
    }
}

// The witness (provided when proving/None when verifying) is the secret index
pub fn lookup<const N: usize, F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    table: &Lookup3Bit<N, F>,
    index: Option<usize>,
) -> Result<[LinearCombination<F>; N], R1CSError> {
    // compute multiplication of higher bits
    let (b1, b2, ba) =
        cs.allocate_multiplier(index.map(|i| (b2f((i >> 1) & 1 == 1), b2f((i >> 2) & 1 == 1))))?;

    // enforce bits
    let b0 = bit::<F, Cs>(cs, index.map(|i| (i & 1) == 1))?;
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

    use ark_std::UniformRand;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;

    use rand::thread_rng;
    use rand::Rng;

    use pasta;
    type C = pasta::pallas::Affine;
    type C2 = pasta::vesta::Affine;
    type F = <C as AffineCurve>::ScalarField;

    #[test]
    fn test_lookup() {
        let mut rng = thread_rng();

        let u: [F; 8] = [
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
        ];
        let v: [F; 8] = [
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
        ];

        let l3b = Lookup3Bit { elems: [u, v] };

        assert_eq!(l3b.lookup(0), [u[0], v[0]]);
        assert_eq!(l3b.lookup(1), [u[1], v[1]]);
        assert_eq!(l3b.lookup(7), [u[7], v[7]]);

        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(1024, 1);

        let proof = {
            let mut transcript = Transcript::new(b"Lookup");
            let mut prover = Prover::new(&pc_gens, &mut transcript);

            let index = 7;
            let [x, y] = l3b.lookup(index);
            let x_var = prover.allocate(Some(x)).unwrap();
            let y_var = prover.allocate(Some(y)).unwrap();
            let [x_lookup_lc, y_lookup_lc] = lookup(&mut prover, &l3b, Some(index)).unwrap();
            prover.constrain(x_lookup_lc - x_var);
            prover.constrain(y_lookup_lc - y_var);

            prover.prove(&bp_gens).unwrap()
        };

        let mut transcript = Transcript::new(b"Lookup");
        let mut verifier = Verifier::new(&mut transcript);

        let x_var = verifier.allocate(None).unwrap();
        let y_var = verifier.allocate(None).unwrap();
        let [x_lookup_lc, y_lookup_lc] = lookup(&mut verifier, &l3b, None).unwrap();
        verifier.constrain(x_lookup_lc - x_var);
        verifier.constrain(y_lookup_lc - y_var);
        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap()
    }
}
