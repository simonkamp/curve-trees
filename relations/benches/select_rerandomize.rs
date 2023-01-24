#[macro_use]
extern crate criterion;
use criterion::{BenchmarkId, Criterion};

extern crate bulletproofs;
use bulletproofs::r1cs::{batch_verify, Prover, Verifier};

extern crate relations;
use relations::curve_tree::*;

use ark_pallas::{PallasConfig, Projective as PallasP};
use ark_vesta::VestaConfig;

use ark_ec::{
    models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, AffineRepr, CurveGroup,
};
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::UniformRand;

use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

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
    bench_select_and_rerandomize_with_parameters::<1024>(c, 2, 11, threaded);
    bench_select_and_rerandomize_with_parameters::<256>(c, 4, 12, threaded);
    bench_select_and_rerandomize_with_parameters::<1024>(c, 4, 12, threaded);
}

// `L` is the branching factor of the curve tree
fn bench_select_and_rerandomize_with_parameters<const L: usize>(
    c: &mut Criterion,
    depth: usize,                   // the depth of the curve tree
    generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
    threaded: &str,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(
        generators_length,
        generators_length,
        &mut rng,
    );

    let some_point = PallasP::rand(&mut rng).into_affine();
    let (permissible_point, _) = sr_params
        .even_parameters
        .uh
        .permissible_commitment(&some_point, &sr_params.even_parameters.pc_gens.B_blinding);
    let set = vec![permissible_point];
    let curve_tree =
        CurveTree::<L, PallasConfig, VestaConfig>::from_set(&set, &sr_params, Some(depth));

    let prove = |print| {
        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<VestaConfig>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let (path, _) = curve_tree.select_and_rerandomize_prover_gadget(
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rand::thread_rng(),
        );
        if print {
            println!(
                "Number of constraints: {}",
                pallas_prover.number_of_constraints()
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
        "Proof size in bytes: {}",
        path.serialized_size(Compress::Yes)
            + pallas_proof.serialized_size(Compress::Yes)
            + vesta_proof.serialized_size(Compress::Yes)
    );

    {
        let group_name = format!("{}_Select&Rerandomize.L={},d={}.", threaded, L, depth);
        let mut group = c.benchmark_group(group_name);

        group.bench_function("prover_gadget", |b| {
            b.iter(|| {
                let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
                    Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

                let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                let mut vesta_prover: Prover<_, Affine<VestaConfig>> =
                    Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

                let (path, _) = curve_tree.select_and_rerandomize_prover_gadget(
                    0,
                    &mut pallas_prover,
                    &mut vesta_prover,
                    &sr_params,
                    &mut rng,
                );
            })
        });

        // #[cfg(feature = "bench_prover")]
        group.bench_function("prover", |b| b.iter(|| prove(false)));

        group.bench_function("verification_gadget", |b| {
            b.iter(|| {
                // Common part
                let srv = curve_tree.select_and_rerandomize_verification_commitments(path.clone());

                let even_verification_gadget = || {
                    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    srv.even_verifier_gadget(&mut pallas_verifier, &sr_params);
                };

                let odd_verification_gadget = || {
                    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut vesta_verifier = Verifier::new(vesta_transcript);
                    srv.odd_verifier_gadget(&mut vesta_verifier, &sr_params);
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

        group.bench_function("verification_tuples", |b| {
            b.iter(|| {
                // Common part
                let srv = curve_tree.select_and_rerandomize_verification_commitments(path.clone());

                let even_verification_gadget = || {
                    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    srv.even_verifier_gadget(&mut pallas_verifier, &sr_params);
                    let _ = pallas_verifier
                        .verification_scalars_and_points(&pallas_proof)
                        .unwrap();
                };

                let odd_verification_gadget = || {
                    let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut vesta_verifier = Verifier::new(vesta_transcript);
                    srv.odd_verifier_gadget(&mut vesta_verifier, &sr_params);
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
        group.bench_function("verify_single", |b| {
            b.iter(|| {
                // Common part
                let srv = curve_tree.select_and_rerandomize_verification_commitments(path.clone());

                let even_verification_gadget = || {
                    let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    srv.even_verifier_gadget(&mut pallas_verifier, &sr_params);
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
                    srv.odd_verifier_gadget(&mut vesta_verifier, &sr_params);

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

    let group_name = format!(
        "{}_select&rerandomize_batch_verification.L={},d={}.",
        threaded, L, depth
    );
    let mut group = c.benchmark_group(group_name);
    use std::iter;

    for n in [1, 2, 10, 50, 100, 150, 200] {
        group.bench_with_input(
            BenchmarkId::from_parameter(n),
            &iter::repeat(path.clone()).take(n).collect::<Vec<_>>(),
            |b, proofs| {
                b.iter(|| {
                    #[cfg(feature = "parallel")]
                    {
                        let srvs = proofs.par_iter().map(|path| {
                            curve_tree.select_and_rerandomize_verification_commitments(path.clone())
                        });
                        let srvs_clone = srvs.clone();
                        rayon::join(
                            || {
                                let pallas_verification_scalars_and_points: Vec<_> = srvs
                                    .map(|srv| {
                                        let pallas_transcript =
                                            Transcript::new(b"select_and_rerandomize");
                                        let mut pallas_verifier = Verifier::new(pallas_transcript);
                                        srv.even_verifier_gadget(&mut pallas_verifier, &sr_params);
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
                                        srv.odd_verifier_gadget(&mut vesta_verifier, &sr_params);

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
                            let srv = curve_tree
                                .select_and_rerandomize_verification_commitments(path.clone());
                            {
                                let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                                let mut pallas_verifier = Verifier::new(pallas_transcript);
                                srv.even_verifier_gadget(&mut pallas_verifier, &sr_params);
                                let pallas_vt = pallas_verifier
                                    .verification_scalars_and_points(&pallas_proof)
                                    .unwrap();
                                pallas_verification_scalars_and_points.push(pallas_vt);
                            }

                            {
                                let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                                let mut vesta_verifier = Verifier::new(vesta_transcript);
                                srv.odd_verifier_gadget(&mut vesta_verifier, &sr_params);

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
