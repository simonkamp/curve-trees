#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use ark_serialize::Compress;
use criterion::BenchmarkId;
use criterion::Criterion;

extern crate bulletproofs;
use bulletproofs::r1cs::{batch_verify, Prover};

extern crate relations;
use merlin::Transcript;
use relations::coin::*;
use relations::curve_tree::*;

use ark_pallas::{PallasConfig, Projective as PallasP};
use ark_vesta::VestaConfig;

use ark_crypto_primitives::{signature::schnorr::Schnorr, signature::SignatureScheme};
use ark_ec::{
    models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, AffineRepr, CurveGroup,
};

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use blake2::Blake2s256 as Blake2s;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

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
    bench_pour_with_parameters::<1024>(c, 2, 12, threaded);
    bench_pour_with_parameters::<256>(c, 4, 13, threaded);
    bench_pour_with_parameters::<1024>(c, 4, 13, threaded);
}

fn bench_pour_with_parameters<const L: usize>(
    c: &mut Criterion,
    depth: usize,                   // the depth of the curve tree
    generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
    threaded: &str,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2; // minimum sufficient power of 2

    let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(
        generators_length,
        generators_length,
        &mut rng,
    );

    let schnorr_parameters = Schnorr::<PallasP, Blake2s>::setup(&mut rng).unwrap();
    let (pk, sk) = Schnorr::keygen(&schnorr_parameters, &mut rng).unwrap();

    let (coin_aux_0, coin_0) = Coin::<PallasConfig, PallasP>::new(
        19,
        &pk,
        &schnorr_parameters,
        &sr_params.even_parameters,
        &mut rng,
    );
    let (coin_aux_1, coin_1) = Coin::<PallasConfig, PallasP>::new(
        23,
        &pk,
        &schnorr_parameters,
        &sr_params.even_parameters,
        &mut rng,
    );
    // Curve tree with two coins
    let set = vec![coin_0, coin_1];
    let curve_tree =
        CurveTree::<L, PallasConfig, VestaConfig>::from_set(&set, &sr_params, Some(depth));

    let randomized_pk_0 = Coin::<PallasConfig, PallasP>::rerandomized_pk(
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
    let randomized_pk_1 = Coin::<PallasConfig, PallasP>::rerandomized_pk(
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
        let pallas_prover: Prover<_, Affine<PallasConfig>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let vesta_prover: Prover<_, Affine<VestaConfig>> =
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
        Pour::<PallasConfig, VestaConfig, PallasP>::deserialize_compressed(&tx.pour_bytes[..])
            .unwrap();

    println!("Proof size in bytes {}", tx.serialized_size(Compress::Yes));

    {
        let group_name = format!("{}_pour.L={},d={}.", threaded, L, depth);
        let mut group = c.benchmark_group(group_name);

        #[cfg(feature = "bench_prover")]
        group.bench_function("prove", |b| b.iter(|| prove()));

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
        group.bench_function("deserialize", |b| {
            b.iter(|| {
                let pour = Pour::<PallasConfig, VestaConfig, PallasP>::deserialize_compressed(
                    &tx.pour_bytes[..],
                )
                .unwrap();
            })
        });
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
    let group_name = format!("{}_pour_batch_verification.L={},d={}.", threaded, L, depth);
    let mut group = c.benchmark_group(group_name);
    for n in [1, 2, 10, 50, 100, 150, 200] {
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
