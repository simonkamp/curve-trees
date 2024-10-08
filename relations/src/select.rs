use bulletproofs::r1cs::*;

use ark_ff::Field;

/// Prove that a commitment x is one of the values committed to in vector commitment xs.
pub fn select<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    x: LinearCombination<F>,
    mut xs: impl Iterator<Item = LinearCombination<F>>,
) {
    // (x_1 - x) * (x_2 - x) * ... * (x_n - x) = 0
    let first_term: LinearCombination<F> =
        xs.next().expect("Cannot select from empty list.") - x.clone();
    let mut product: LinearCombination<F> = first_term;
    for xi in xs {
        let (_, _, next_product) = cs.multiply(product, xi.clone() - x.clone());
        product = next_product.into();
    }
    cs.constrain(product);
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_ec::AffineRepr;
    use ark_std::UniformRand;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;
    use std::iter;

    type PallasA = ark_pallas::Affine;
    type PallasBase = <PallasA as AffineRepr>::BaseField;
    type VestaA = ark_vesta::Affine;
    type VestaScalar = <VestaA as AffineRepr>::ScalarField;

    #[test]
    fn test_select() {
        let mut rng = rand::thread_rng();
        let pg = PedersenGens::default();
        let bpg = BulletproofGens::new(1024, 1);
        let (proof, xs_comm, x_comm) = {
            // have a prover commit to a vector of random elements in Pallas base field
            let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                .take(256)
                .collect();
            let index = 42;
            let x = xs[index];

            let mut transcript = Transcript::new(b"select");
            let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
            let blinding_xs = PallasBase::rand(&mut rng);
            let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);
            let blinding_x = PallasBase::rand(&mut rng);
            let (x_comm, x_var) = prover.commit(x, blinding_x);

            select(
                &mut prover,
                x_var.into(),
                xs_vars.into_iter().map(|v| v.into()),
            );

            let proof = prover.prove(&bpg).unwrap();
            (proof, xs_comm, x_comm)
        };

        let mut transcript = Transcript::new(b"select");
        let mut verifier = Verifier::new(&mut transcript);

        let xs_vars = verifier.commit_vec(256, xs_comm);
        let x_var = verifier.commit(x_comm);

        select(
            &mut verifier,
            x_var.into(),
            xs_vars.into_iter().map(|v| v.into()),
        );

        let res = verifier.verify(&proof, &pg, &bpg);
        assert_eq!(res, Ok(()))
    }
}
