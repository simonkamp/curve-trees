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

fn bench_select_and_rerandomize_batches(c: &mut Criterion) {
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
    bench_naive_batch_select_and_rerandomize_with_parameters::<
        1024,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 2, 12, threaded, curves);

    bench_grafted_batch_select_and_rerandomize_with_parameters::<
        1024,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 2, 12, 12, threaded, curves);

    bench_naive_batch_select_and_rerandomize_with_parameters::<
        256,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 13, threaded, curves);

    bench_grafted_batch_select_and_rerandomize_with_parameters::<
        256,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 12, 12, threaded, curves);

    bench_naive_batch_select_and_rerandomize_with_parameters::<
        256,
        4,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 14, threaded, curves);

    bench_grafted_batch_select_and_rerandomize_with_parameters::<
        256,
        4,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 12, 13, threaded, curves);

    bench_naive_batch_select_and_rerandomize_with_parameters::<
        256,
        8,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 15, threaded, curves);

    bench_grafted_batch_select_and_rerandomize_with_parameters::<
        256,
        8,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 13, 14, threaded, curves);

    bench_naive_batch_select_and_rerandomize_with_parameters::<
        1024,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 14, threaded, curves);

    bench_grafted_batch_select_and_rerandomize_with_parameters::<
        1024,
        2,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 13, 13, threaded, curves);

    let curves = "secp&secq";
    bench_naive_batch_select_and_rerandomize_with_parameters::<
        1024,
        2,
        SecpBase,
        SecpConfig,
        SecqConfig,
    >(c, 2, 12, threaded, curves);
    bench_naive_batch_select_and_rerandomize_with_parameters::<
        256,
        2,
        SecpBase,
        SecpConfig,
        SecqConfig,
    >(c, 4, 13, threaded, curves);
    bench_naive_batch_select_and_rerandomize_with_parameters::<
        1024,
        2,
        SecpBase,
        SecpConfig,
        SecqConfig,
    >(c, 4, 14, threaded, curves);
}

fn bench_naive_batch_select_and_rerandomize_with_parameters<
    const L: usize, // branching factor
    const M: usize, // batch size
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
    let prefix_string = format!("{threaded}NaiveBatchSelRand_Curves:{curves}_L:{L}_D:{depth}_M{M}");
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params =
        SelRerandParameters::<P0, P1>::new(generators_length, generators_length, &mut rng);

    let commitments_to_select: Vec<_> = (0..M).map(|_| Affine::<P0>::rand(&mut rng)).collect();
    let indices: [usize; M] = (0..M).collect::<Vec<usize>>().try_into().unwrap();
    let curve_tree =
        CurveTree::<L, M, P0, P1>::from_set(&commitments_to_select, &sr_params, Some(depth));

    let prove = |print| {
        let even_transcript = Transcript::new(b"select_and_rerandomize");
        let mut even_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, even_transcript);

        let odd_transcript = Transcript::new(b"select_and_rerandomize");
        let mut odd_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, odd_transcript);

        // We use the naive approach of selecting an rerandomizing twice.
        let mut paths = Vec::new();
        for i in indices {
            let (path, _) = curve_tree.select_and_rerandomize_prover_gadget(
                0,
                0,
                &mut even_prover,
                &mut odd_prover,
                &sr_params,
                &mut rand::thread_rng(),
            );
            paths.push(path)
        }
        if print {
            println!(
                "{}_Constraints: {}",
                &prefix_string,
                even_prover.number_of_constraints() + odd_prover.number_of_constraints()
            );
        }
        #[cfg(feature = "parallel")]
        let (even_proof, odd_proof) = rayon::join(
            || {
                even_prover
                    .prove(&sr_params.even_parameters.bp_gens)
                    .unwrap()
            },
            || odd_prover.prove(&sr_params.odd_parameters.bp_gens).unwrap(),
        );
        #[cfg(not(feature = "parallel"))]
        let (even_proof, odd_proof) = (
            even_prover
                .prove(&sr_params.even_parameters.bp_gens)
                .unwrap(),
            odd_prover.prove(&sr_params.odd_parameters.bp_gens).unwrap(),
        );
        (paths, even_proof, odd_proof)
    };
    let (paths, even_proof, odd_proof) = prove(true);

    println!(
        "{}_ProofSize: {} bytes\n",
        &prefix_string,
        paths.serialized_size(Compress::Yes)
            + even_proof.serialized_size(Compress::Yes)
            + odd_proof.serialized_size(Compress::Yes)
    );

    {
        let mut group = c.benchmark_group(&prefix_string);

        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("prover_gadget", |b| {
            b.iter(|| {
                let even_transcript = Transcript::new(b"select_and_rerandomize");
                let mut even_prover: Prover<_, Affine<P0>> =
                    Prover::new(&sr_params.even_parameters.pc_gens, even_transcript);

                let odd_transcript = Transcript::new(b"select_and_rerandomize");
                let mut odd_prover: Prover<_, Affine<P1>> =
                    Prover::new(&sr_params.odd_parameters.pc_gens, odd_transcript);

                let (_path, _) = curve_tree.select_and_rerandomize_prover_gadget(
                    0,
                    &mut even_prover,
                    &mut odd_prover,
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
                    let even_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut even_verifier = Verifier::new(even_transcript);
                    srv.even_verifier_gadget(&mut even_verifier, &sr_params, &curve_tree);
                };

                let odd_verification_gadget = || {
                    let odd_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut odd_verifier = Verifier::new(odd_transcript);
                    srv.odd_verifier_gadget(&mut odd_verifier, &sr_params, &curve_tree);
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
                    let even_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut even_verifier = Verifier::new(even_transcript);
                    srv.even_verifier_gadget(&mut even_verifier, &sr_params, &curve_tree);
                    let _ = even_verifier
                        .verification_scalars_and_points(&even_proof)
                        .unwrap();
                };

                let odd_verification_gadget = || {
                    let odd_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut odd_verifier = Verifier::new(odd_transcript);
                    srv.odd_verifier_gadget(&mut odd_verifier, &sr_params, &curve_tree);
                    let _ = odd_verifier
                        .verification_scalars_and_points(&odd_proof)
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
                    let even_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut even_verifier = Verifier::new(even_transcript);
                    srv.even_verifier_gadget(&mut even_verifier, &sr_params, &curve_tree);
                    let even_vt = even_verifier
                        .verification_scalars_and_points(&even_proof)
                        .unwrap();

                    let res = batch_verify(
                        vec![even_vt],
                        &sr_params.even_parameters.pc_gens,
                        &sr_params.even_parameters.bp_gens,
                    );
                    assert_eq!(res, Ok(()))
                };

                let odd_verification_gadget = || {
                    let odd_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut odd_verifier = Verifier::new(odd_transcript);
                    srv.odd_verifier_gadget(&mut odd_verifier, &sr_params, &curve_tree);

                    let odd_vt = odd_verifier
                        .verification_scalars_and_points(&odd_proof)
                        .unwrap();

                    let res = batch_verify(
                        vec![odd_vt],
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
            &iter::repeat(paths.clone()).take(n).collect::<Vec<_>>(),
            |b, proofs| {
                b.iter(|| {
                    #[cfg(feature = "parallel")]
                    {
                        let srvs = proofs.par_iter().map(|paths| {
                            let mut paths_with_root = Vec::new();
                            for i in 0..M {
                                let mut path = paths[i].clone();
                                curve_tree
                                    .select_and_rerandomize_verification_commitments(&mut path);
                                paths_with_root.push(path);
                            }
                            paths_with_root
                        });
                        let srvs_clone = srvs.clone();
                        rayon::join(
                            || {
                                let even_verification_scalars_and_points: Vec<_> = srvs
                                    .map(|srv| {
                                        let even_transcript =
                                            Transcript::new(b"select_and_rerandomize");
                                        let mut even_verifier = Verifier::new(even_transcript);
                                        for i in 0..M {
                                            srv[i].even_verifier_gadget(
                                                &mut even_verifier,
                                                &sr_params,
                                                &curve_tree,
                                            );
                                        }
                                        let even_vt = even_verifier
                                            .verification_scalars_and_points(&even_proof)
                                            .unwrap();
                                        even_vt
                                    })
                                    .collect();
                                batch_verify(
                                    even_verification_scalars_and_points,
                                    &sr_params.even_parameters.pc_gens,
                                    &sr_params.even_parameters.bp_gens,
                                )
                                .unwrap()
                            },
                            || {
                                let odd_verification_scalars_and_points: Vec<_> = srvs_clone
                                    .map(|srv| {
                                        let odd_transcript =
                                            Transcript::new(b"select_and_rerandomize");
                                        let mut odd_verifier = Verifier::new(odd_transcript);
                                        for i in 0..M {
                                            srv[i].odd_verifier_gadget(
                                                &mut odd_verifier,
                                                &sr_params,
                                                &curve_tree,
                                            );
                                        }

                                        let odd_vt = odd_verifier
                                            .verification_scalars_and_points(&odd_proof)
                                            .unwrap();
                                        odd_vt
                                    })
                                    .collect();
                                batch_verify(
                                    odd_verification_scalars_and_points,
                                    &sr_params.odd_parameters.pc_gens,
                                    &sr_params.odd_parameters.bp_gens,
                                )
                                .unwrap()
                            },
                        )
                    }
                    #[cfg(not(feature = "parallel"))]
                    {
                        let mut even_verification_scalars_and_points =
                            Vec::with_capacity(proofs.len());
                        let mut odd_verification_scalars_and_points =
                            Vec::with_capacity(proofs.len());
                        for path in proofs {
                            let mut srv = path.clone();
                            curve_tree.select_and_rerandomize_verification_commitments(&mut srv);
                            {
                                let even_transcript = Transcript::new(b"select_and_rerandomize");
                                let mut even_verifier = Verifier::new(even_transcript);
                                srv.even_verifier_gadget(
                                    &mut even_verifier,
                                    &sr_params,
                                    &curve_tree,
                                );
                                let even_vt = even_verifier
                                    .verification_scalars_and_points(&even_proof)
                                    .unwrap();
                                even_verification_scalars_and_points.push(even_vt);
                            }

                            {
                                let odd_transcript = Transcript::new(b"select_and_rerandomize");
                                let mut odd_verifier = Verifier::new(odd_transcript);
                                srv.odd_verifier_gadget(&mut odd_verifier, &sr_params, &curve_tree);

                                let odd_vt = odd_verifier
                                    .verification_scalars_and_points(&odd_proof)
                                    .unwrap();
                                odd_verification_scalars_and_points.push(odd_vt);
                            }
                        }
                        batch_verify(
                            even_verification_scalars_and_points,
                            &sr_params.even_parameters.pc_gens,
                            &sr_params.even_parameters.bp_gens,
                        )
                        .unwrap();
                        batch_verify(
                            odd_verification_scalars_and_points,
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

fn bench_grafted_batch_select_and_rerandomize_with_parameters<
    const L: usize,
    const M: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    c: &mut Criterion,
    depth: usize,                        // the depth of the curve tree
    even_generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
    odd_generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
    threaded: &str,
    curves: &str,
) {
    let prefix_string =
        format!("{threaded}GraftedBatchSelRand_Curves:{curves}_L:{L}_D:{depth}_M{M}");
    let mut rng = rand::thread_rng();
    let even_generators_length = 1 << even_generators_length_log_2;
    let odd_generators_length = 1 << odd_generators_length_log_2;

    let sr_params =
        SelRerandParameters::<P0, P1>::new(even_generators_length, odd_generators_length, &mut rng);

    let commitments_to_select: Vec<_> = (0..M).map(|_| Affine::<P0>::rand(&mut rng)).collect();
    let indices: [usize; M] = (0..M).collect::<Vec<usize>>().try_into().unwrap();
    let curve_tree =
        CurveTree::<L, M, P0, P1>::from_set(&commitments_to_select, &sr_params, Some(depth));

    let prove = |print| {
        let even_transcript = Transcript::new(b"select_and_rerandomize");
        let mut even_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, even_transcript);

        let odd_transcript = Transcript::new(b"select_and_rerandomize");
        let mut odd_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, odd_transcript);

        let (multi_path, _) = curve_tree.batched_select_and_rerandomize_prover_gadget(
            indices,
            &mut even_prover,
            &mut odd_prover,
            &sr_params,
            &mut rand::thread_rng(),
        );
        if print {
            println!(
                "{}_Constraints: {}",
                &prefix_string,
                even_prover.number_of_constraints() + odd_prover.number_of_constraints()
            );
            println!(
                "EvenConstraints: {}, OddConstraints: {}",
                even_prover.number_of_constraints(),
                odd_prover.number_of_constraints()
            );
        }
        #[cfg(feature = "parallel")]
        let (even_proof, odd_proof) = rayon::join(
            || {
                even_prover
                    .prove(&sr_params.even_parameters.bp_gens)
                    .unwrap()
            },
            || odd_prover.prove(&sr_params.odd_parameters.bp_gens).unwrap(),
        );
        #[cfg(not(feature = "parallel"))]
        let (even_proof, odd_proof) = (
            even_prover
                .prove(&sr_params.even_parameters.bp_gens)
                .unwrap(),
            odd_prover.prove(&sr_params.odd_parameters.bp_gens).unwrap(),
        );
        (multi_path, even_proof, odd_proof)
    };
    let (multi_path, even_proof, odd_proof) = prove(true);

    println!(
        "{}_ProofSize: {} bytes\n",
        &prefix_string,
        multi_path.serialized_size(Compress::Yes)
            + even_proof.serialized_size(Compress::Yes)
            + odd_proof.serialized_size(Compress::Yes)
    );

    {
        let mut group = c.benchmark_group(&prefix_string);

        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("prover_gadget", |b| {
            b.iter(|| {
                let even_transcript = Transcript::new(b"select_and_rerandomize");
                let mut even_prover: Prover<_, Affine<P0>> =
                    Prover::new(&sr_params.even_parameters.pc_gens, even_transcript);

                let odd_transcript = Transcript::new(b"select_and_rerandomize");
                let mut odd_prover: Prover<_, Affine<P1>> =
                    Prover::new(&sr_params.odd_parameters.pc_gens, odd_transcript);

                let (_path, _) = curve_tree.select_and_rerandomize_prover_gadget(
                    0,
                    &mut even_prover,
                    &mut odd_prover,
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
                    let even_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut even_verifier = Verifier::new(even_transcript);
                    srv.even_verifier_gadget(&mut even_verifier, &sr_params, &curve_tree);
                };

                let odd_verification_gadget = || {
                    let odd_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut odd_verifier = Verifier::new(odd_transcript);
                    srv.odd_verifier_gadget(&mut odd_verifier, &sr_params, &curve_tree);
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
                    let even_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut even_verifier = Verifier::new(even_transcript);
                    srv.even_verifier_gadget(&mut even_verifier, &sr_params, &curve_tree);
                    let _ = even_verifier
                        .verification_scalars_and_points(&even_proof)
                        .unwrap();
                };

                let odd_verification_gadget = || {
                    let odd_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut odd_verifier = Verifier::new(odd_transcript);
                    srv.odd_verifier_gadget(&mut odd_verifier, &sr_params, &curve_tree);
                    let _ = odd_verifier
                        .verification_scalars_and_points(&odd_proof)
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
                    let even_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut even_verifier = Verifier::new(even_transcript);
                    srv.even_verifier_gadget(&mut even_verifier, &sr_params, &curve_tree);
                    let even_vt = even_verifier
                        .verification_scalars_and_points(&even_proof)
                        .unwrap();

                    let res = batch_verify(
                        vec![even_vt],
                        &sr_params.even_parameters.pc_gens,
                        &sr_params.even_parameters.bp_gens,
                    );
                    assert_eq!(res, Ok(()))
                };

                let odd_verification_gadget = || {
                    let odd_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut odd_verifier = Verifier::new(odd_transcript);
                    srv.odd_verifier_gadget(&mut odd_verifier, &sr_params, &curve_tree);

                    let odd_vt = odd_verifier
                        .verification_scalars_and_points(&odd_proof)
                        .unwrap();

                    let res = batch_verify(
                        vec![odd_vt],
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
            &iter::repeat(multi_path.clone()).take(n).collect::<Vec<_>>(),
            |b, proofs| {
                b.iter(|| {
                    #[cfg(feature = "parallel")]
                    {
                        let srvs = proofs.par_iter().map(|paths| {
                            let mut path_with_root = multi_path.clone();
                            curve_tree.batched_select_and_rerandomize_verification_commitments(
                                &mut path_with_root,
                            );
                            path_with_root
                        });
                        let srvs_clone = srvs.clone();
                        rayon::join(
                            || {
                                let even_verification_scalars_and_points: Vec<_> = srvs
                                    .map(|srv| {
                                        let even_transcript =
                                            Transcript::new(b"select_and_rerandomize");
                                        let mut even_verifier = Verifier::new(even_transcript);

                                        srv.even_verifier_gadget(
                                            &mut even_verifier,
                                            &sr_params,
                                            &curve_tree,
                                        );

                                        let even_vt = even_verifier
                                            .verification_scalars_and_points(&even_proof)
                                            .unwrap();
                                        even_vt
                                    })
                                    .collect();
                                batch_verify(
                                    even_verification_scalars_and_points,
                                    &sr_params.even_parameters.pc_gens,
                                    &sr_params.even_parameters.bp_gens,
                                )
                                .unwrap()
                            },
                            || {
                                let odd_verification_scalars_and_points: Vec<_> = srvs_clone
                                    .map(|srv| {
                                        let odd_transcript =
                                            Transcript::new(b"select_and_rerandomize");
                                        let mut odd_verifier = Verifier::new(odd_transcript);

                                        srv.odd_verifier_gadget(
                                            &mut odd_verifier,
                                            &sr_params,
                                            &curve_tree,
                                        );

                                        let odd_vt = odd_verifier
                                            .verification_scalars_and_points(&odd_proof)
                                            .unwrap();
                                        odd_vt
                                    })
                                    .collect();
                                batch_verify(
                                    odd_verification_scalars_and_points,
                                    &sr_params.odd_parameters.pc_gens,
                                    &sr_params.odd_parameters.bp_gens,
                                )
                                .unwrap()
                            },
                        )
                    }
                    #[cfg(not(feature = "parallel"))]
                    {
                        let mut even_verification_scalars_and_points =
                            Vec::with_capacity(proofs.len());
                        let mut odd_verification_scalars_and_points =
                            Vec::with_capacity(proofs.len());
                        for path in proofs {
                            let mut srv = path.clone();
                            curve_tree.select_and_rerandomize_verification_commitments(&mut srv);
                            {
                                let even_transcript = Transcript::new(b"select_and_rerandomize");
                                let mut even_verifier = Verifier::new(even_transcript);
                                srv.even_verifier_gadget(
                                    &mut even_verifier,
                                    &sr_params,
                                    &curve_tree,
                                );
                                let even_vt = even_verifier
                                    .verification_scalars_and_points(&even_proof)
                                    .unwrap();
                                even_verification_scalars_and_points.push(even_vt);
                            }

                            {
                                let odd_transcript = Transcript::new(b"select_and_rerandomize");
                                let mut odd_verifier = Verifier::new(odd_transcript);
                                srv.odd_verifier_gadget(&mut odd_verifier, &sr_params, &curve_tree);

                                let odd_vt = odd_verifier
                                    .verification_scalars_and_points(&odd_proof)
                                    .unwrap();
                                odd_verification_scalars_and_points.push(odd_vt);
                            }
                        }
                        batch_verify(
                            even_verification_scalars_and_points,
                            &sr_params.even_parameters.pc_gens,
                            &sr_params.even_parameters.bp_gens,
                        )
                        .unwrap();
                        batch_verify(
                            odd_verification_scalars_and_points,
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
    name = select_and_rerandomize_batches;
    config = Criterion::default().sample_size(10);
    targets =
    bench_select_and_rerandomize_batches,
}

criterion_main!(select_and_rerandomize_batches);
