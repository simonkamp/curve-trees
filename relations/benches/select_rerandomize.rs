#[macro_use]
extern crate criterion;
use ark_ff::PrimeField;
use criterion::{BenchmarkId, Criterion};

extern crate bulletproofs;
use bulletproofs::r1cs::{batch_verify, Prover, Verifier};

extern crate relations;
use relations::curve_tree::*;

use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_vesta::VestaConfig;

use ark_secp256k1::{Config as SecpConfig, Fq as SecpBase};
use ark_secq256k1::Config as SecqConfig;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::UniformRand;

use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[cfg(feature = "usenix")]
fn bench_select_and_rerandomize(c: &mut Criterion) {
    #[cfg(feature = "table1")]
    {
        println!("Table 1\n");
        let threaded = "";
        let curves = "pasta";
        println!("Benchmark Select and rerandomize over the pasta cycle, |S|=2^20\n");
        bench_select_and_rerandomize_with_parameters::<1024, PallasBase, PallasConfig, VestaConfig>(
            c, 2, 11, threaded, curves,
        );
        println!("Benchmark Select and rerandomize over the pasta cycle, |S|=2^32\n");
        bench_select_and_rerandomize_with_parameters::<256, PallasBase, PallasConfig, VestaConfig>(
            c, 4, 12, threaded, curves,
        );
        println!("Benchmark Select and rerandomize over the pasta cycle, |S|=2^40\n");
        bench_select_and_rerandomize_with_parameters::<1024, PallasBase, PallasConfig, VestaConfig>(
            c, 4, 12, threaded, curves,
        );
        let curves = "secp&secq";
        println!(
            "Benchmark Select and rerandomize over the secp256k1 / seqp256k1 cycle, |S|=2^20\n"
        );
        bench_select_and_rerandomize_with_parameters::<1024, SecpBase, SecpConfig, SecqConfig>(
            c, 2, 11, threaded, curves,
        );
        println!(
            "Benchmark Select and rerandomize over the secp256k1 / seqp256k1 cycle, |S|=2^32\n"
        );
        bench_select_and_rerandomize_with_parameters::<256, SecpBase, SecpConfig, SecqConfig>(
            c, 4, 12, threaded, curves,
        );
        println!(
            "Benchmark Select and rerandomize over the secp256k1 / seqp256k1 cycle, |S|=2^40\n"
        );
        bench_select_and_rerandomize_with_parameters::<1024, SecpBase, SecpConfig, SecqConfig>(
            c, 4, 12, threaded, curves,
        );
    }
}

#[cfg(not(feature = "usenix"))]
fn bench_select_and_rerandomize(c: &mut Criterion) {
    let threaded = {
        #[cfg(feature = "parallel")]
        {
            "Multi_threaded"
        }
        #[cfg(not(feature = "parallel"))]
        {
            "Single_threaded"
        }
    };
    let curves = "pasta";
    bench_select_and_rerandomize_with_parameters::<1024, PallasBase, PallasConfig, VestaConfig>(
        c, 2, 11, threaded, curves,
    );
    bench_select_and_rerandomize_with_parameters::<256, PallasBase, PallasConfig, VestaConfig>(
        c, 4, 12, threaded, curves,
    );
    bench_select_and_rerandomize_with_parameters::<1024, PallasBase, PallasConfig, VestaConfig>(
        c, 4, 12, threaded, curves,
    );
    let curves = "secp&secq";
    bench_select_and_rerandomize_with_parameters::<1024, SecpBase, SecpConfig, SecqConfig>(
        c, 2, 11, threaded, curves,
    );
    bench_select_and_rerandomize_with_parameters::<256, SecpBase, SecpConfig, SecqConfig>(
        c, 4, 12, threaded, curves,
    );
    bench_select_and_rerandomize_with_parameters::<1024, SecpBase, SecpConfig, SecqConfig>(
        c, 4, 12, threaded, curves,
    );
}

// `L` is the branching factor of the curve tree
fn bench_select_and_rerandomize_with_parameters<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    c: &mut Criterion,
    depth: usize,                   // the depth of the curve tree
    generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
    threaded: &str,
    curves: &str,
) {
    let prefix_string = format!("{threaded}SelRand_Curves:{curves}_L:{L}_D:{depth}");
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params =
        SelRerandParameters::<P0, P1>::new(generators_length, generators_length, &mut rng);

    let some_point = Affine::<P0>::rand(&mut rng);
    let set = vec![some_point];
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_set(&set, &sr_params, Some(depth));

    let prove = |print| {
        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let (path, _) = curve_tree.select_and_rerandomize_prover_gadget(
            0,
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rand::thread_rng(),
        );
        if print {
            println!(
                "{}_Constraints: {}",
                &prefix_string,
                2 * pallas_prover.number_of_constraints()
            );
        }
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
        #[cfg(not(feature = "parallel"))]
        let (pallas_proof, vesta_proof) = (
            pallas_prover
                .prove(&sr_params.even_parameters.bp_gens)
                .unwrap(),
            vesta_prover
                .prove(&sr_params.odd_parameters.bp_gens)
                .unwrap(),
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

    {
        let mut group = c.benchmark_group(&prefix_string);

        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("prover_gadget", |b| {
            b.iter(|| {
                let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                let mut pallas_prover: Prover<_, Affine<P0>> =
                    Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

                let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                let mut vesta_prover: Prover<_, Affine<P1>> =
                    Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

                let (_path, _) = curve_tree.select_and_rerandomize_prover_gadget(
                    0,
                    &mut pallas_prover,
                    &mut vesta_prover,
                    &sr_params,
                    &mut rng,
                );
            })
        });

        #[cfg(feature = "bench_prover")]
        group.bench_function("prover", |b| b.iter(|| prove(false)));

        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("verification_gadget", |b| {
            b.iter(|| {
                // Common part
                let srv = curve_tree.select_and_rerandomize_verification_commitments(path.clone());

                let even_verification_gadget = || {
                    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    srv.even_verifier_gadget(&mut pallas_verifier, &sr_params, &curve_tree);
                };

                let odd_verification_gadget = || {
                    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut vesta_verifier = Verifier::new(vesta_transcript);
                    srv.odd_verifier_gadget(&mut vesta_verifier, &sr_params, &curve_tree);
                };

                #[cfg(not(feature = "parallel"))]
                {
                    even_verification_gadget();
                    odd_verification_gadget()
                }
                #[cfg(feature = "parallel")]
                {
                    rayon::join(even_verification_gadget, odd_verification_gadget);
                }
            })
        });

        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("verification_tuples", |b| {
            b.iter(|| {
                // Common part
                let srv = curve_tree.select_and_rerandomize_verification_commitments(path.clone());

                let even_verification_gadget = || {
                    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    srv.even_verifier_gadget(&mut pallas_verifier, &sr_params, &curve_tree);
                    let _ = pallas_verifier
                        .verification_scalars_and_points(&pallas_proof)
                        .unwrap();
                };

                let odd_verification_gadget = || {
                    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut vesta_verifier = Verifier::new(vesta_transcript);
                    srv.odd_verifier_gadget(&mut vesta_verifier, &sr_params, &curve_tree);
                    let _ = vesta_verifier
                        .verification_scalars_and_points(&vesta_proof)
                        .unwrap();
                };

                #[cfg(not(feature = "parallel"))]
                {
                    even_verification_gadget();
                    odd_verification_gadget()
                }
                #[cfg(feature = "parallel")]
                {
                    rayon::join(even_verification_gadget, odd_verification_gadget);
                }
            })
        });
        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("verify_single", |b| {
            b.iter(|| {
                // Common part
                let srv = curve_tree.select_and_rerandomize_verification_commitments(path.clone());

                let even_verification_gadget = || {
                    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    srv.even_verifier_gadget(&mut pallas_verifier, &sr_params, &curve_tree);
                    let pallas_vt = pallas_verifier
                        .verification_scalars_and_points(&pallas_proof)
                        .unwrap();

                    let res = batch_verify(
                        vec![pallas_vt],
                        &sr_params.even_parameters.pc_gens,
                        &sr_params.even_parameters.bp_gens,
                    );
                    assert_eq!(res, Ok(()))
                };

                let odd_verification_gadget = || {
                    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut vesta_verifier = Verifier::new(vesta_transcript);
                    srv.odd_verifier_gadget(&mut vesta_verifier, &sr_params, &curve_tree);

                    let vesta_vt = vesta_verifier
                        .verification_scalars_and_points(&vesta_proof)
                        .unwrap();

                    let res = batch_verify(
                        vec![vesta_vt],
                        &sr_params.odd_parameters.pc_gens,
                        &sr_params.odd_parameters.bp_gens,
                    );
                    assert_eq!(res, Ok(()))
                };

                #[cfg(not(feature = "parallel"))]
                {
                    even_verification_gadget();
                    odd_verification_gadget()
                }
                #[cfg(feature = "parallel")]
                {
                    rayon::join(even_verification_gadget, odd_verification_gadget);
                }
            })
        });
    }

    let group_name = format!("{}_batch_verification", &prefix_string);
    let mut group = c.benchmark_group(group_name);
    use std::iter;

    // for n in [1, 2, 10, 50, 100] {
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
                                        let pallas_transcript =
                                            Transcript::new(b"select_and_rerandomize");
                                        let mut pallas_verifier = Verifier::new(pallas_transcript);
                                        srv.even_verifier_gadget(
                                            &mut pallas_verifier,
                                            &sr_params,
                                            &curve_tree,
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
                                        let vesta_transcript =
                                            Transcript::new(b"select_and_rerandomize");
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
                    }
                    #[cfg(not(feature = "parallel"))]
                    {
                        let mut pallas_verification_scalars_and_points =
                            Vec::with_capacity(proofs.len());
                        let mut vesta_verification_scalars_and_points =
                            Vec::with_capacity(proofs.len());
                        for path in proofs {
                            let mut srv = path.clone();
                            curve_tree.select_and_rerandomize_verification_commitments(&mut srv);
                            {
                                let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                                let mut pallas_verifier = Verifier::new(pallas_transcript);
                                srv.even_verifier_gadget(
                                    &mut pallas_verifier,
                                    &sr_params,
                                    &curve_tree,
                                );
                                let pallas_vt = pallas_verifier
                                    .verification_scalars_and_points(&pallas_proof)
                                    .unwrap();
                                pallas_verification_scalars_and_points.push(pallas_vt);
                            }

                            {
                                let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                                let mut vesta_verifier = Verifier::new(vesta_transcript);
                                srv.odd_verifier_gadget(
                                    &mut vesta_verifier,
                                    &sr_params,
                                    &curve_tree,
                                );

                                let vesta_vt = vesta_verifier
                                    .verification_scalars_and_points(&vesta_proof)
                                    .unwrap();
                                vesta_verification_scalars_and_points.push(vesta_vt);
                            }
                        }
                        batch_verify(
                            pallas_verification_scalars_and_points,
                            &sr_params.even_parameters.pc_gens,
                            &sr_params.even_parameters.bp_gens,
                        )
                        .unwrap();
                        batch_verify(
                            vesta_verification_scalars_and_points,
                            &sr_params.odd_parameters.pc_gens,
                            &sr_params.odd_parameters.bp_gens,
                        )
                        .unwrap()
                    }
                })
            },
        );
    }
}

criterion_group! {
    name = select_and_rerandomize;
    config = Criterion::default().sample_size(50);
    targets =
    bench_select_and_rerandomize,
}

criterion_main!(select_and_rerandomize);
