#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use ark_ec::short_weierstrass::Projective;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_serialize::Compress;
use criterion::BenchmarkId;
use criterion::Criterion;

extern crate bulletproofs;
use bulletproofs::r1cs::{batch_verify, Prover};

extern crate relations;
use merlin::Transcript;
use relations::coin::*;
use relations::curve_tree::*;

use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_vesta::VestaConfig;

use ark_secp256k1::{Config as SecpConfig, Fq as SecpBase};
use ark_secq256k1::Config as SecqConfig;

use ark_crypto_primitives::{signature::schnorr::Schnorr, signature::SignatureScheme};
use ark_ec::short_weierstrass::Affine;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use blake2::Blake2s256 as Blake2s;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[cfg(feature = "usenix")]
fn bench_pour(c: &mut Criterion) {
    #[cfg(feature = "table3")]
    {
        let threaded = "";

        let curves = "pasta";
        println!("Table 3\n");
        println!("Benchmark Pour over the pasta cycle, |S|=2^20\n");
        bench_pour_with_parameters::<1024, PallasBase, PallasConfig, VestaConfig>(
            c, 2, 12, threaded, curves,
        );
        println!("Benchmark Pour over the pasta cycle, |S|=2^32\n");
        bench_pour_with_parameters::<256, PallasBase, PallasConfig, VestaConfig>(
            c, 4, 13, threaded, curves,
        );
        println!("Benchmark Pour over the pasta cycle, |S|=2^40\n");
        bench_pour_with_parameters::<1024, PallasBase, PallasConfig, VestaConfig>(
            c, 4, 13, threaded, curves,
        );
        let curves = "secp&q";
        println!("Benchmark Pour over the secp256k1 / seqp256k1 cycle, |S|=2^20\n");
        bench_pour_with_parameters::<1024, SecpBase, SecpConfig, SecqConfig>(
            c, 2, 12, threaded, curves,
        );
        println!("Benchmark Pour over the secp256k1 / seqp256k1 cycle, |S|=2^32\n");
        bench_pour_with_parameters::<256, SecpBase, SecpConfig, SecqConfig>(
            c, 4, 13, threaded, curves,
        );

        println!("Benchmark Pour over the secp256k1 / seqp256k1 cycle, |S|=2^40\n");
        bench_pour_with_parameters::<1024, SecpBase, SecpConfig, SecqConfig>(
            c, 4, 13, threaded, curves,
        );
    }
}

#[cfg(not(feature = "usenix"))]
fn bench_pour(c: &mut Criterion) {
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
    bench_pour_with_parameters::<1024, PallasBase, PallasConfig, VestaConfig>(
        c, 2, 12, threaded, curves,
    );
    bench_pour_with_parameters::<256, PallasBase, PallasConfig, VestaConfig>(
        c, 4, 13, threaded, curves,
    );
    bench_pour_with_parameters::<1024, PallasBase, PallasConfig, VestaConfig>(
        c, 4, 13, threaded, curves,
    );
    let curves = "secp&q";
    bench_pour_with_parameters::<1024, SecpBase, SecpConfig, SecqConfig>(
        c, 2, 12, threaded, curves,
    );
    bench_pour_with_parameters::<256, SecpBase, SecpConfig, SecqConfig>(c, 4, 13, threaded, curves);
    bench_pour_with_parameters::<1024, SecpBase, SecpConfig, SecqConfig>(
        c, 4, 13, threaded, curves,
    );
}

fn bench_pour_with_parameters<
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
    let prefix_string = format!("{threaded}Pour_Curves:{curves}_L:{L}_D:{depth}");
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2; // minimum sufficient power of 2

    let sr_params =
        SelRerandParameters::<P0, P1>::new(generators_length, generators_length, &mut rng);

    let schnorr_parameters = Schnorr::<Projective<P0>, Blake2s>::setup(&mut rng).unwrap();
    let (pk, sk) = Schnorr::keygen(&schnorr_parameters, &mut rng).unwrap();

    let (coin_aux_0, coin_0) = Coin::<P0, Projective<P0>>::new(
        19,
        &pk,
        &schnorr_parameters,
        &sr_params.even_parameters,
        &mut rng,
    );
    let (coin_aux_1, coin_1) = Coin::<P0, Projective<P0>>::new(
        23,
        &pk,
        &schnorr_parameters,
        &sr_params.even_parameters,
        &mut rng,
    );
    // Curve tree with two coins
    let set = vec![coin_0, coin_1];
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_set(&set, &sr_params, Some(depth));

    let randomized_pk_0 = Coin::<P0, Projective<P0>>::rerandomized_pk(
        &pk,
        &coin_aux_0.pk_randomness,
        &schnorr_parameters,
    );
    let input0 = SpendingInfo {
        coin_aux: coin_aux_0,
        index: 0,
        randomized_pk: randomized_pk_0,
        sk: sk.clone(),
    };
    let randomized_pk_1 = Coin::<P0, Projective<P0>>::rerandomized_pk(
        &pk,
        &coin_aux_1.pk_randomness,
        &schnorr_parameters,
    );
    let input1 = SpendingInfo {
        coin_aux: coin_aux_1,
        index: 1,
        randomized_pk: randomized_pk_1,
        sk: sk,
    };
    let prove = || {
        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let receiver_pk_0 = pk;
        let receiver_pk_1 = pk;

        prove_pour(
            pallas_prover,
            vesta_prover,
            &sr_params,
            &curve_tree,
            &input0,
            &input1,
            11,
            receiver_pk_0,
            31,
            receiver_pk_1,
            &schnorr_parameters,
            &mut rand::thread_rng(),
        )
    };
    let tx = prove();
    let pour_proof =
        Pour::<L, P0, P1, Projective<P0>>::deserialize_compressed(&tx.pour_bytes[..]).unwrap();

    println!(
        "{}_ProofSize: {} bytes",
        &prefix_string,
        tx.serialized_size(Compress::Yes)
    );

    {
        let mut group = c.benchmark_group(&prefix_string);

        #[cfg(feature = "bench_prover")]
        group.bench_function("prove", |b| b.iter(|| prove()));

        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("verification_gadget", |b| {
            b.iter(|| {
                tx.clone().verification_gadget(
                    b"select_and_rerandomize",
                    &sr_params,
                    &curve_tree,
                    &schnorr_parameters,
                );
            })
        });
        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("deserialize", |b| {
            b.iter(|| {
                let _pour =
                    Pour::<L, P0, P1, Projective<P0>>::deserialize_compressed(&tx.pour_bytes[..])
                        .unwrap();
            })
        });
        #[cfg(feature = "detailed_benchmarks")]
        group.bench_function("verify_single_with_deserialization", |b| {
            b.iter(|| {
                let (pallas_vt, vesta_vt) = tx.clone().verification_gadget(
                    b"select_and_rerandomize",
                    &sr_params,
                    &curve_tree,
                    &schnorr_parameters,
                );

                batch_verify(
                    vec![pallas_vt],
                    &sr_params.even_parameters.pc_gens,
                    &sr_params.even_parameters.bp_gens,
                )
                .unwrap();
                batch_verify(
                    vec![vesta_vt],
                    &sr_params.odd_parameters.pc_gens,
                    &sr_params.odd_parameters.bp_gens,
                )
                .unwrap();
            })
        });
    }

    use std::iter;
    let group_name = format!("{}_batch_verification", &prefix_string);
    let mut group = c.benchmark_group(group_name);
    for n in [1, 100] {
        group.bench_with_input(
            BenchmarkId::from_parameter(n),
            &iter::repeat(pour_proof.clone()).take(n).collect::<Vec<_>>(),
            |b, proofs| {
                b.iter(|| {
                    #[cfg(not(feature = "parallel"))]
                    {
                        let mut pallas_verification_scalars_and_points =
                            Vec::with_capacity(proofs.len());
                        let mut vesta_verification_scalars_and_points =
                            Vec::with_capacity(proofs.len());
                        for proof in proofs {
                            let p = proof.clone();
                            let (pallas_vt, vesta_vt) = p.verification_gadget(
                                b"select_and_rerandomize",
                                &sr_params,
                                &curve_tree,
                            );

                            pallas_verification_scalars_and_points.push(pallas_vt);
                            vesta_verification_scalars_and_points.push(vesta_vt);
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
                        .unwrap();
                    }
                    #[cfg(feature = "parallel")]
                    {
                        let proofs_and_commitment_paths = proofs.par_iter().map(|proof| {
                            let cp0 = curve_tree.select_and_rerandomize_verification_commitments(
                                proof.clone().randomized_path_0.clone(),
                            );
                            let cp1 = curve_tree.select_and_rerandomize_verification_commitments(
                                proof.clone().randomized_path_1.clone(),
                            );
                            (proof, cp0, cp1)
                        });
                        let proofs_and_commitment_paths_clone = proofs_and_commitment_paths.clone();
                        rayon::join(
                            || {
                                // even verification tuples
                                let event_vts: Vec<_> = proofs_and_commitment_paths
                                    .map(|(proof, path0, path1)| {
                                        proof.even_verification_gadget(
                                            b"select_and_rerandomize",
                                            &sr_params,
                                            &path0,
                                            &path1,
                                            &curve_tree,
                                        )
                                    })
                                    .collect();
                                batch_verify(
                                    event_vts,
                                    &sr_params.even_parameters.pc_gens,
                                    &sr_params.even_parameters.bp_gens,
                                )
                                .unwrap();
                            },
                            || {
                                // odd verification tuples
                                let odd_vts: Vec<_> = proofs_and_commitment_paths_clone
                                    .map(|(proof, path0, path1)| {
                                        proof.odd_verification_gadget(
                                            b"select_and_rerandomize",
                                            &sr_params,
                                            &path0,
                                            &path1,
                                            &curve_tree,
                                        )
                                    })
                                    .collect();
                                batch_verify(
                                    odd_vts,
                                    &sr_params.odd_parameters.pc_gens,
                                    &sr_params.odd_parameters.bp_gens,
                                )
                                .unwrap();
                            },
                        )
                    }
                })
            },
        );
    }
}

criterion_group! {
    name = pour;
    config = Criterion::default().sample_size(50);
    targets =
    bench_pour,
}

criterion_main!(pour);
