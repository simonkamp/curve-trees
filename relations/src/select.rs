use crate::error::{Error, Result};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_std::vec::Vec;
use bulletproofs::r1cs::*;
use dock_crypto_utils::ff::powers;
use dock_crypto_utils::poly::poly_from_roots;

/// Prove that a commitment x is one of the values committed to in vector commitment xs.
pub fn select<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    x: LinearCombination<F>,
    mut xs: impl Iterator<Item = LinearCombination<F>>,
) -> Result<()> {
    // (x_1 - x) * (x_2 - x) * ... * (x_n - x) = 0
    let first_factor: LinearCombination<F> =
        xs.next().ok_or(Error::NeedNonZeroSetSize)? - x.clone();
    let mut product: LinearCombination<F> = first_factor;
    for xi in xs {
        let (_, _, next_product) = cs.multiply(product, xi.clone() - x.clone());
        product = next_product.into();
    }
    cs.constrain(product);
    Ok(())
}

/// Prove that a commitments in `xs` are subset of the values committed to in vector commitment `ys`.
pub fn multi_select<F: Field, Cs: RandomizableConstraintSystem<F>>(
    cs: &mut Cs,
    xs: Vec<LinearCombination<F>>,
    ys: Vec<LinearCombination<F>>,
) -> Result<()> {
    if xs.is_empty() {
        return Err(Error::NeedNonZeroNumberOfIndices);
    }
    if ys.is_empty() {
        return Err(Error::NeedNonZeroSetSize);
    }
    Ok(cs.specify_randomized_constraints(move |cs| {
        let challenge = cs.challenge_scalar(b"challenge");
        construct_random_linear_combination_product(cs, xs.as_slice(), ys.as_slice(), challenge);
        Ok(())
    })?)
}

/// Prove that the commitments in `xs` are subset of the values committed to in vector commitment `ys`.
pub fn multi_select_ext_challenge<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    xs: Vec<LinearCombination<F>>,
    ys: Vec<LinearCombination<F>>,
    challenge: F,
) -> Result<()> {
    if xs.is_empty() {
        return Err(Error::NeedNonZeroNumberOfIndices);
    }
    if ys.is_empty() {
        return Err(Error::NeedNonZeroSetSize);
    }

    construct_random_linear_combination_product(cs, xs.as_slice(), ys.as_slice(), challenge);
    Ok(())
}

fn construct_random_linear_combination_product<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    xs: &[LinearCombination<F>],
    ys: &[LinearCombination<F>],
    challenge: F,
) {
    // Need to enforce
    // (y_1 - x_1) * (y_2 - x_1) * ... * (y_n - x_1) = 0
    // (y_1 - x_2) * (y_2 - x_2) * ... * (y_n - x_2) = 0
    // ...
    // Enforce a single random linear combination of the above equations.
    let mut r = F::ONE;
    let mut product = LinearCombination::default();
    for x_i in xs {
        let mut product_i: LinearCombination<F> = ys[0].clone() - x_i.clone();
        for y_i in &ys[1..] {
            let (_, _, next_product) = cs.multiply(product_i.clone(), y_i.clone() - x_i.clone());
            product_i = next_product.into();
        }
        product = product + product_i * r;
        r *= challenge;
    }

    cs.constrain(product);
}

/// Naive implementation of [`multi_select`] that calls [`select`] in a loop for each x_i in `xs`.
pub fn multi_select_naive<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    xs: Vec<LinearCombination<F>>,
    ys: Vec<LinearCombination<F>>,
) {
    assert!(xs.len() > 0);
    assert!(ys.len() > 0);

    for x in xs {
        select(cs, x, ys.clone().into_iter()).unwrap();
    }
}

/// Prove that a commitment `x` is one of the values in public set `xs`.
pub fn select_public_set<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    x: LinearCombination<F>,
    xs: &[F],
) -> Result<()> {
    if xs.is_empty() {
        return Err(Error::NeedNonZeroSetSize);
    }

    let poly = poly_from_roots::<F>(xs);
    let mut eval: LinearCombination<F> = poly.coeffs[0].into();
    let mut x_power = x.clone();
    for i in 1..poly.coeffs.len() {
        eval = eval + (x_power.clone() * poly.coeffs[i].clone());
        let (_, _, o) = cs.multiply(x_power, x.clone());
        x_power = o.into();
    }

    cs.constrain(eval);
    Ok(())
}

/// Prove that the commitments in `xs` are subset of the values `ys`
pub fn multi_select_public_set<F: Field, Cs: RandomizableConstraintSystem<F>>(
    cs: &mut Cs,
    xs: Vec<LinearCombination<F>>,
    ys: &[F],
) -> Result<()> {
    if xs.is_empty() {
        return Err(Error::NeedNonZeroNumberOfIndices);
    }
    if ys.is_empty() {
        return Err(Error::NeedNonZeroSetSize);
    }

    // Same idea as multi_select_public_set_ext_challenge

    let poly = poly_from_roots::<F>(ys);
    Ok(cs.specify_randomized_constraints(move |cs| {
        let challenge = cs.challenge_scalar(b"challenge");
        construct_eval_random_linear_combination_poly(cs, xs, challenge, poly);
        Ok(())
    })?)
}

/// Prove that the commitments in `xs` are subset of the values `ys`
pub fn multi_select_public_set_ext_challenge<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    xs: Vec<LinearCombination<F>>,
    ys: &[F],
    challenge: F,
) -> Result<()> {
    if xs.is_empty() {
        return Err(Error::NeedNonZeroNumberOfIndices);
    }
    if ys.is_empty() {
        return Err(Error::NeedNonZeroSetSize);
    }

    // If xs is subset of ys, then a polynomial with roots as elements of ys will evaluate to 0 at
    // all elements of xs. Rather than evaluating polynomial once on each of xs, evaluate the
    // single polynomial formed from random linear combination of each polynomial

    // p(y) = (y-y_1)(y-y_2)... for each y_i in ys
    // Enforce p(x_1) + c.p(x_2) + c^2.p(x_3) + ... = 0 for each x_i in xs and c is the challenge

    let poly = poly_from_roots::<F>(ys);
    construct_eval_random_linear_combination_poly(cs, xs, challenge, poly);
    Ok(())
}

fn construct_eval_random_linear_combination_poly<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    xs: Vec<LinearCombination<F>>,
    challenge: F,
    poly: DensePolynomial<F>,
) {
    let challenge_powers = powers(&challenge, xs.len() as u32);
    // Sum of the constant term of random linear combination polynomial
    let mut eval: LinearCombination<F> =
        (poly.coeffs[0] * challenge_powers.iter().sum::<F>()).into();
    // Evaluate the polynomial by adding terms of single degree in each iteration
    let mut xs_powers = xs.clone();
    for i in 1..poly.coeffs.len() {
        let mut eval_i = xs_powers[0].clone();
        for j in 1..challenge_powers.len() {
            eval_i = eval_i + (xs_powers[j].clone() * challenge_powers[j]);
        }
        eval = eval + (eval_i * poly.coeffs[i]);
        // Calculate the next power of each x_i for next degree term evaluation
        for j in 0..challenge_powers.len() {
            let (_, _, o) = cs.multiply(xs_powers[j].clone(), xs[j].clone());
            xs_powers[j] = o.into();
        }
    }
    cs.constrain(eval);
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_ec::AffineRepr;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use core::iter;
    use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
    use rand::{prelude::SliceRandom, Rng};
    use std::time::Instant;

    type PallasA = ark_pallas::Affine;
    type PallasBase = <PallasA as AffineRepr>::BaseField;
    type VestaA = ark_vesta::Affine;
    type VestaScalar = <VestaA as AffineRepr>::ScalarField;

    fn sample_subset(
        ys: &[VestaScalar],
        subset_size: usize,
        valid_subset: bool,
        rng: &mut impl Rng,
    ) -> Vec<VestaScalar> {
        assert!(subset_size > 0);
        let mut xs = ys
            .choose_multiple(rng, subset_size)
            .cloned()
            .collect::<Vec<_>>();
        if !valid_subset {
            xs[subset_size - 1] = sample_non_member(ys, rng);
        }
        xs
    }

    fn sample_non_member(ys: &[VestaScalar], rng: &mut impl Rng) -> VestaScalar {
        loop {
            let candidate = VestaScalar::rand(rng);
            if !ys.contains(&candidate) {
                return candidate;
            }
        }
    }

    fn check_multi_select_private(
        set_size: usize,
        subset_size: usize,
        valid_subset: bool,
        external_challenge: bool,
        pg: &PedersenGens<VestaA>,
        bpg: &BulletproofGens<VestaA>,
    ) {
        let mut rng = rand::thread_rng();
        let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
            .take(set_size)
            .collect();
        let xs = sample_subset(ys.as_slice(), subset_size, valid_subset, &mut rng);

        let (proof_result, ys_comm, xs_comm) = {
            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
            let blinding_ys = PallasBase::rand(&mut rng);
            let (ys_comm, ys_vars) = prover.commit_vec(ys.as_slice(), blinding_ys, &bpg);
            let blinding_xs = PallasBase::rand(&mut rng);
            let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

            if external_challenge {
                let challenge = prover.transcript().challenge_scalar(b"challenge");
                multi_select_ext_challenge(
                    &mut prover,
                    xs_vars.into_iter().map(|v| v.into()).collect(),
                    ys_vars.into_iter().map(|v| v.into()).collect(),
                    challenge,
                )
                .unwrap();
            } else {
                multi_select(
                    &mut prover,
                    xs_vars.into_iter().map(|v| v.into()).collect(),
                    ys_vars.into_iter().map(|v| v.into()).collect(),
                )
                .unwrap();
            }

            let proof_result = prover.prove(&bpg);
            if let Ok(proof) = &proof_result {
                println!("For set size = {set_size}, subset size = {subset_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());
            }

            (proof_result, ys_comm, xs_comm)
        };

        let proof = match proof_result {
            Ok(proof) => proof,
            Err(_) => {
                assert!(!valid_subset);
                return;
            }
        };

        let start = Instant::now();
        let mut transcript = MerlinTranscript::new(b"select");
        let mut verifier = Verifier::new(&mut transcript);

        let ys_vars = verifier.commit_vec(set_size, ys_comm);
        let xs_vars = verifier.commit_vec(subset_size, xs_comm);

        if external_challenge {
            let challenge = verifier.transcript().challenge_scalar(b"challenge");
            multi_select_ext_challenge(
                &mut verifier,
                xs_vars.into_iter().map(|v| v.into()).collect(),
                ys_vars.into_iter().map(|v| v.into()).collect(),
                challenge,
            )
            .unwrap();
        } else {
            multi_select(
                &mut verifier,
                xs_vars.into_iter().map(|v| v.into()).collect(),
                ys_vars.into_iter().map(|v| v.into()).collect(),
            )
            .unwrap();
        }

        let verify_result = verifier.verify(&proof, pg, bpg);
        if valid_subset {
            verify_result.unwrap();
            println!("Verifier time {:?}", start.elapsed());
        } else {
            assert!(verify_result.is_err());
        }
    }

    fn check_multi_select_public(
        set_size: usize,
        subset_size: usize,
        valid_subset: bool,
        external_challenge: bool,
        pg: &PedersenGens<VestaA>,
        bpg: &BulletproofGens<VestaA>,
    ) {
        let mut rng = rand::thread_rng();
        let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
            .take(set_size)
            .collect();
        let xs = sample_subset(ys.as_slice(), subset_size, valid_subset, &mut rng);

        let (proof_result, xs_comm) = {
            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);

            let blinding_xs = PallasBase::rand(&mut rng);
            let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

            if external_challenge {
                let challenge = prover.transcript().challenge_scalar(b"challenge");
                multi_select_public_set_ext_challenge(
                    &mut prover,
                    xs_vars.into_iter().map(|v| v.into()).collect(),
                    ys.as_slice(),
                    challenge,
                )
                .unwrap();
            } else {
                multi_select_public_set(
                    &mut prover,
                    xs_vars.into_iter().map(|v| v.into()).collect(),
                    ys.as_slice(),
                )
                .unwrap();
            }

            let proof_result = prover.prove(&bpg);
            if let Ok(proof) = &proof_result {
                println!("For set size = {set_size}, subset size = {subset_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());
            }

            (proof_result, xs_comm)
        };

        let proof = match proof_result {
            Ok(proof) => proof,
            Err(_) => {
                assert!(!valid_subset);
                return;
            }
        };

        let start = Instant::now();
        let mut transcript = MerlinTranscript::new(b"select");
        let mut verifier = Verifier::new(&mut transcript);

        let xs_vars = verifier.commit_vec(subset_size, xs_comm);

        if external_challenge {
            let challenge = verifier.transcript().challenge_scalar(b"challenge");
            multi_select_public_set_ext_challenge(
                &mut verifier,
                xs_vars.into_iter().map(|v| v.into()).collect(),
                ys.as_slice(),
                challenge,
            )
            .unwrap();
        } else {
            multi_select_public_set(
                &mut verifier,
                xs_vars.into_iter().map(|v| v.into()).collect(),
                ys.as_slice(),
            )
            .unwrap();
        }

        let verify_result = verifier.verify(&proof, pg, bpg);
        if valid_subset {
            verify_result.unwrap();
            println!("Verifier time {:?}", start.elapsed());
        } else {
            assert!(verify_result.is_err());
        }
    }

    #[test]
    fn test_select() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(set_size: usize, pg: &PedersenGens<VestaA>, bpg: &BulletproofGens<VestaA>) {
            let mut rng = rand::thread_rng();
            let (proof, xs_comm, x_comm) = {
                // have a prover commit to a vector of random elements in Pallas base field
                let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                    .take(set_size)
                    .collect();
                let index = 42;
                let x = xs[index];

                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
                let blinding_xs = PallasBase::rand(&mut rng);
                let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);
                let blinding_x = PallasBase::rand(&mut rng);
                let (x_comm, x_var) = prover.commit(x, blinding_x);

                select(
                    &mut prover,
                    x_var.into(),
                    xs_vars.into_iter().map(|v| v.into()),
                )
                .unwrap();

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, xs_comm, x_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let xs_vars = verifier.commit_vec(set_size, xs_comm);
            let x_var = verifier.commit(x_comm);

            select(
                &mut verifier,
                x_var.into(),
                xs_vars.into_iter().map(|v| v.into()),
            )
            .unwrap();

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, &pg, &bpg);
        check(1000, &pg, &bpg);
        check(2000, &pg, &bpg);

        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"select-empty");
        let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
        let x_var: LinearCombination<_> = prover
            .allocate(Some(VestaScalar::rand(&mut rng)))
            .unwrap()
            .into();
        assert!(matches!(
            select(
                &mut prover,
                x_var,
                iter::empty::<LinearCombination<VestaScalar>>(),
            ),
            Err(Error::NeedNonZeroSetSize)
        ));
    }

    #[test]
    fn test_select_public_set() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(set_size: usize, pg: &PedersenGens<VestaA>, bpg: &BulletproofGens<VestaA>) {
            let mut rng = rand::thread_rng();

            // Generate a public set of random elements
            let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                .take(set_size)
                .collect();
            let index = 42;
            let x = xs[index];

            let (proof, x_comm) = {
                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);

                // Only commit to x, not to xs (public set)
                let blinding_x = PallasBase::rand(&mut rng);
                let (x_comm, x_var) = prover.commit(x, blinding_x);

                select_public_set(&mut prover, x_var.into(), xs.as_slice()).unwrap();

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, x_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let x_var = verifier.commit(x_comm);

            // Verifier uses the same public set xs
            select_public_set(&mut verifier, x_var.into(), xs.as_slice()).unwrap();

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, &pg, &bpg);
        check(1000, &pg, &bpg);
        check(2000, &pg, &bpg);

        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"select-public-empty");
        let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
        let x_var: LinearCombination<_> = prover
            .allocate(Some(VestaScalar::rand(&mut rng)))
            .unwrap()
            .into();
        assert!(matches!(
            select_public_set(&mut prover, x_var, &[]),
            Err(Error::NeedNonZeroSetSize)
        ));
    }

    #[test]
    fn test_multi_select_naive() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(
            set_size: usize,
            subset_size: usize,
            pg: &PedersenGens<VestaA>,
            bpg: &BulletproofGens<VestaA>,
        ) {
            let mut rng = rand::thread_rng();
            let (proof, ys_comm, xs_comm) = {
                let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                    .take(set_size)
                    .collect();
                let xs = ys
                    .choose_multiple(&mut rng, subset_size)
                    .cloned()
                    .collect::<Vec<_>>();

                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
                let blinding_ys = PallasBase::rand(&mut rng);
                let (ys_comm, ys_vars) = prover.commit_vec(ys.as_slice(), blinding_ys, &bpg);
                let blinding_xs = PallasBase::rand(&mut rng);
                let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

                multi_select_naive(
                    &mut prover,
                    xs_vars.clone().into_iter().map(|v| v.into()).collect(),
                    ys_vars.clone().into_iter().map(|v| v.into()).collect(),
                );

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}, subset size = {subset_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, ys_comm, xs_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let ys_vars = verifier.commit_vec(set_size, ys_comm);
            let xs_vars = verifier.commit_vec(subset_size, xs_comm);

            multi_select_naive(
                &mut verifier,
                xs_vars.clone().into_iter().map(|v| v.into()).collect(),
                ys_vars.clone().into_iter().map(|v| v.into()).collect(),
            );

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, 2, &pg, &bpg);
        check(512, 3, &pg, &bpg);
        check(512, 4, &pg, &bpg);

        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"multi-select-empty");
        let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
        let x_var: LinearCombination<_> = prover
            .allocate(Some(VestaScalar::rand(&mut rng)))
            .unwrap()
            .into();
        let y_var: LinearCombination<_> = prover
            .allocate(Some(VestaScalar::rand(&mut rng)))
            .unwrap()
            .into();
        assert!(matches!(
            multi_select(&mut prover, Vec::new(), vec![y_var]),
            Err(Error::NeedNonZeroNumberOfIndices)
        ));
        assert!(matches!(
            multi_select(&mut prover, vec![x_var], Vec::new()),
            Err(Error::NeedNonZeroSetSize)
        ));
    }

    #[test]
    fn test_multi_select() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        for subset_size in [2usize, 3, 4] {
            check_multi_select_private(512, subset_size, true, false, &pg, &bpg);
        }
        check_multi_select_private(128, 4, false, false, &pg, &bpg);
    }

    #[test]
    fn test_multi_select_ext_challenge() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        for subset_size in [2usize, 3, 4] {
            check_multi_select_private(512, subset_size, true, true, &pg, &bpg);
        }
        check_multi_select_private(128, 4, false, true, &pg, &bpg);

        let mut rng = rand::thread_rng();
        let challenge = VestaScalar::rand(&mut rng);
        let mut transcript = MerlinTranscript::new(b"multi-select-ext-empty");
        let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
        let x_var: LinearCombination<_> = prover
            .allocate(Some(VestaScalar::rand(&mut rng)))
            .unwrap()
            .into();
        let y_var: LinearCombination<_> = prover
            .allocate(Some(VestaScalar::rand(&mut rng)))
            .unwrap()
            .into();
        assert!(matches!(
            multi_select_ext_challenge(&mut prover, Vec::new(), vec![y_var], challenge),
            Err(Error::NeedNonZeroNumberOfIndices)
        ));
        assert!(matches!(
            multi_select_ext_challenge(&mut prover, vec![x_var], Vec::new(), challenge),
            Err(Error::NeedNonZeroSetSize)
        ));
    }

    #[test]
    fn test_multi_select_public_set() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        for subset_size in [2usize, 3, 4] {
            check_multi_select_public(512, subset_size, true, false, &pg, &bpg);
        }
        check_multi_select_public(128, 4, false, false, &pg, &bpg);

        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"multi-select-public-empty");
        let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
        let x_var: LinearCombination<_> = prover
            .allocate(Some(VestaScalar::rand(&mut rng)))
            .unwrap()
            .into();
        assert!(matches!(
            multi_select_public_set(&mut prover, Vec::new(), &[VestaScalar::from(1u64)]),
            Err(Error::NeedNonZeroNumberOfIndices)
        ));
        assert!(matches!(
            multi_select_public_set(&mut prover, vec![x_var], &[]),
            Err(Error::NeedNonZeroSetSize)
        ));
    }

    #[test]
    fn test_multi_select_public_set_ext_challenge() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        for subset_size in [2usize, 3, 4] {
            check_multi_select_public(512, subset_size, true, true, &pg, &bpg);
        }
        check_multi_select_public(128, 4, false, true, &pg, &bpg);

        let mut rng = rand::thread_rng();
        let challenge = VestaScalar::rand(&mut rng);
        let mut transcript = MerlinTranscript::new(b"multi-select-public-empty");
        let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
        let x_var: LinearCombination<_> = prover
            .allocate(Some(VestaScalar::rand(&mut rng)))
            .unwrap()
            .into();
        assert!(matches!(
            multi_select_public_set_ext_challenge(
                &mut prover,
                Vec::new(),
                &[VestaScalar::from(1u64)],
                challenge,
            ),
            Err(Error::NeedNonZeroNumberOfIndices)
        ));
        assert!(matches!(
            multi_select_public_set_ext_challenge(&mut prover, vec![x_var], &[], challenge),
            Err(Error::NeedNonZeroSetSize)
        ));
    }
}
