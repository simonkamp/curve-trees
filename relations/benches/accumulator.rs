#[macro_use]
extern crate criterion;
use ark_ff::PrimeField;
use criterion::{BenchmarkId, Criterion};

extern crate bulletproofs;
use bulletproofs::r1cs::{batch_verify, LinearCombination, Prover, Verifier};

extern crate relations;
use relations::{curve_tree::*, select::*};

use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_vesta::VestaConfig;

use ark_secp256k1::{Config as SecpConfig, Fq as SecpBase};
use ark_secq256k1::Config as SecqConfig;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::{UniformRand, Zero};

use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[cfg(feature = "usenix")]
fn bench_accumulator(c: &mut Criterion) {
    #[cfg(feature = "table2")]
    {
        println!("Table 2\n");
        println!("Benchmark accumulator over the pasta cycle, |S|=2^30\n");
        bench_accumulator_with_parameters::<256, PallasBase, PallasConfig, VestaConfig>(
            c, 3, 64, 11, 12, "pasta",
        );
        println!("Benchmark accumulator over the secp256k1 / secq256k1 cycle, |S|=2^30\n");
        bench_accumulator_with_parameters::<256, SecpBase, SecpConfig, SecqConfig>(
            c, 3, 64, 11, 12, "secp&q",
        );
    }
}

#[cfg(not(feature = "usenix"))]
fn bench_accumulator(c: &mut Criterion) {
    bench_accumulator_with_parameters::<256, PallasBase, PallasConfig, VestaConfig>(
        c, 3, 64, 11, 12, "pasta",
    );
    bench_accumulator_with_parameters::<256, SecpBase, SecpConfig, SecqConfig>(
        c, 3, 64, 11, 12, "secp&q",
    );
}

// `L` is the branching factor of the curve tree
fn bench_accumulator_with_parameters<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    c: &mut Criterion,
    depth: usize,                        // the depth of the curve tree
    leaf_width: usize, // the maximum number of field elements stored in a curve tree leaf
    even_generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
    odd_generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
    curves: &str,
) {
    let prefix_string = format!("Acc_Curves:{curves}_L:{L}_D:{depth}_LeafWidth:{leaf_width}");
    let mut rng = rand::thread_rng();
    let even_generators_length = 1 << even_generators_length_log_2;
    let odd_generators_length = 1 << odd_generators_length_log_2;

    let sr_params =
        SelRerandParameters::<P0, P1>::new(even_generators_length, odd_generators_length);

    let leaf_elements: Vec<_> = (0..leaf_width)
        .map(|_| P0::ScalarField::rand(&mut rng))
        .collect();
    let element = leaf_elements[0];
    // Unless all leafs of the curve tree are occupied, it would always be possible to open to zero by using an empty leaf.
    assert_ne!(element, P0::ScalarField::zero());
    let leaf_commitment =
        sr_params
            .even_parameters
            .commit(&leaf_elements, P0::ScalarField::zero(), 0);

    let set = vec![leaf_commitment];
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_set(&set, &sr_params, Some(depth));

    let prove = |print| {
        let pallas_transcript = Transcript::new(b"acc");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"acc");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let (path, rerandomization) = curve_tree.select_and_rerandomize_prover_gadget(
            0,
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rand::thread_rng(),
        );

        let (leaf_commitment, leaf_vars) = pallas_prover.commit_vec(
            &leaf_elements,
            rerandomization,
            &sr_params.even_parameters.bp_gens,
        );
        assert_eq!(leaf_commitment, path.get_rerandomized_leaf()); // sanity check

        select(
            &mut pallas_prover,
            LinearCombination::from(element),
            leaf_vars.iter().map(|var| LinearCombination::from(*var)),
        );

        if print {
            println!(
                "{prefix_string}_Constraints: {}",
                pallas_prover.number_of_constraints() + vesta_prover.number_of_constraints()
            );
        }
        #[cfg(not(feature = "parallel"))]
        let (pallas_proof, vesta_proof) = (
            pallas_prover
                .prove(&sr_params.even_parameters.bp_gens)
                .unwrap(),
            vesta_prover
                .prove(&sr_params.odd_parameters.bp_gens)
                .unwrap(),
        );
        #[cfg(feature = "parallel")]
        let (pallas_proof, vesta_proof) = rayon::join(
            || {
                pallas_prover
                    .prove(&sr_params.even_parameters.bp_gens)
                    .unwrap()
            },
            || {
                vesta_prover
                    .prove(&sr_params.odd_parameters.bp_gens)
                    .unwrap()
            },
        );
        (path, pallas_proof, vesta_proof)
    };
    let (path, pallas_proof, vesta_proof) = prove(true);

    println!(
        "{}_ProofSize: {} bytes\n",
        &prefix_string,
        path.serialized_size(Compress::Yes)
            + pallas_proof.serialized_size(Compress::Yes)
            + vesta_proof.serialized_size(Compress::Yes)
    );

    #[cfg(feature = "bench_prover")]
    {
        let mut group = c.benchmark_group(&prefix_string);
        group.bench_function("prover", |b| b.iter(|| prove(false)));
    }

    let group_name = format!("{}_batch_verification", &prefix_string);
    let mut group = c.benchmark_group(group_name);
    use std::iter;

    for n in [1, 100] {
        group.bench_with_input(
            BenchmarkId::from_parameter(n),
            &iter::repeat(path.clone()).take(n).collect::<Vec<_>>(),
            |b, proofs| {
                b.iter(|| {
                    #[cfg(feature = "parallel")]
                    {
                        let srvs = proofs.par_iter().map(|path| {
                            let mut path = path.clone();
                            curve_tree.select_and_rerandomize_verification_commitments(&mut path);
                            path
                        });
                        let srvs_clone = srvs.clone();
                        rayon::join(
                            || {
                                let pallas_verification_scalars_and_points: Vec<_> = srvs
                                    .map(|srv| {
                                        let pallas_transcript = Transcript::new(b"acc");
                                        let mut pallas_verifier = Verifier::new(pallas_transcript);
                                        srv.even_verifier_gadget(
                                            &mut pallas_verifier,
                                            &sr_params,
                                            &curve_tree,
                                        );
                                        let leaf_vars = pallas_verifier
                                            .commit_vec(leaf_width, path.get_rerandomized_leaf());
                                        select(
                                            &mut pallas_verifier,
                                            LinearCombination::from(element),
                                            leaf_vars
                                                .iter()
                                                .map(|var| LinearCombination::from(*var)),
                                        );
                                        let pallas_vt = pallas_verifier
                                            .verification_scalars_and_points(&pallas_proof)
                                            .unwrap();
                                        pallas_vt
                                    })
                                    .collect();
                                batch_verify(
                                    pallas_verification_scalars_and_points,
                                    &sr_params.even_parameters.pc_gens,
                                    &sr_params.even_parameters.bp_gens,
                                )
                                .unwrap()
                            },
                            || {
                                let vesta_verification_scalars_and_points: Vec<_> = srvs_clone
                                    .map(|srv| {
                                        let vesta_transcript = Transcript::new(b"acc");
                                        let mut vesta_verifier = Verifier::new(vesta_transcript);
                                        srv.odd_verifier_gadget(
                                            &mut vesta_verifier,
                                            &sr_params,
                                            &curve_tree,
                                        );

                                        let vesta_vt = vesta_verifier
                                            .verification_scalars_and_points(&vesta_proof)
                                            .unwrap();
                                        vesta_vt
                                    })
                                    .collect();
                                batch_verify(
                                    vesta_verification_scalars_and_points,
                                    &sr_params.odd_parameters.pc_gens,
                                    &sr_params.odd_parameters.bp_gens,
                                )
                                .unwrap()
                            },
                        )
                    };
                    #[cfg(not(feature = "parallel"))]
                    {
                        let srvs = proofs.iter().map(|path| {
                            let mut path = path.clone();
                            curve_tree.select_and_rerandomize_verification_commitments(&mut path);
                            path
                        });
                        let srvs_clone = srvs.clone();
                        {
                            let pallas_verification_scalars_and_points: Vec<_> = srvs
                                .map(|srv| {
                                    let pallas_transcript = Transcript::new(b"acc");
                                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                                    srv.even_verifier_gadget(
                                        &mut pallas_verifier,
                                        &sr_params,
                                        &curve_tree,
                                    );
                                    let leaf_vars = pallas_verifier
                                        .commit_vec(leaf_width, path.get_rerandomized_leaf());
                                    select(
                                        &mut pallas_verifier,
                                        LinearCombination::from(element),
                                        leaf_vars.iter().map(|var| LinearCombination::from(*var)),
                                    );
                                    let pallas_vt = pallas_verifier
                                        .verification_scalars_and_points(&pallas_proof)
                                        .unwrap();
                                    pallas_vt
                                })
                                .collect();
                            batch_verify(
                                pallas_verification_scalars_and_points,
                                &sr_params.even_parameters.pc_gens,
                                &sr_params.even_parameters.bp_gens,
                            )
                            .unwrap()
                        };
                        {
                            let vesta_verification_scalars_and_points: Vec<_> = srvs_clone
                                .map(|srv| {
                                    let vesta_transcript = Transcript::new(b"acc");
                                    let mut vesta_verifier = Verifier::new(vesta_transcript);
                                    srv.odd_verifier_gadget(
                                        &mut vesta_verifier,
                                        &sr_params,
                                        &curve_tree,
                                    );

                                    let vesta_vt = vesta_verifier
                                        .verification_scalars_and_points(&vesta_proof)
                                        .unwrap();
                                    vesta_vt
                                })
                                .collect();
                            batch_verify(
                                vesta_verification_scalars_and_points,
                                &sr_params.odd_parameters.pc_gens,
                                &sr_params.odd_parameters.bp_gens,
                            )
                            .unwrap()
                        };
                    }
                })
            },
        );
    }
}

criterion_group! {
    name = accumulator;
    config = Criterion::default().sample_size(50);
    targets =
    bench_accumulator,
}

criterion_main!(accumulator);
