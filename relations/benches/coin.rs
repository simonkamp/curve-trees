#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate bulletproofs;
use bulletproofs::r1cs::{batch_verify, Prover, Verifier};

extern crate relations;
use merlin::Transcript;
use relations::coin::*;
use relations::select_and_rerandomize::*;

extern crate pasta;
use pasta::{
    pallas::{PallasParameters, Projective as PallasP},
    vesta::VestaParameters,
};

use ark_crypto_primitives::{signature::schnorr::Schnorr, SignatureScheme};
use ark_ec::models::short_weierstrass_jacobian::GroupAffine;
use ark_serialize::CanonicalSerialize;
use blake2::Blake2s;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

fn bench_pour(c: &mut Criterion) {
    let mut group = c.benchmark_group("Pour");

    let mut rng = rand::thread_rng();
    let generators_length = 1 << 13; // minimum sufficient power of 2

    let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
        generators_length,
        generators_length,
        &mut rng,
    );

    let schnorr_parameters = Schnorr::<PallasP, Blake2s>::setup(&mut rng).unwrap();
    let (pk, sk) = Schnorr::keygen(&schnorr_parameters, &mut rng).unwrap();

    let (coin_aux_0, coin_0) = Coin::<PallasParameters, PallasP>::new(
        19,
        &pk,
        &schnorr_parameters,
        &sr_params.c0_parameters,
        &mut rng,
    );
    let (coin_aux_1, coin_1) = Coin::<PallasParameters, PallasP>::new(
        23,
        &pk,
        &schnorr_parameters,
        &sr_params.c0_parameters,
        &mut rng,
    );
    // Curve tree with two coins
    let set = vec![coin_0, coin_1];
    let curve_tree =
        CurveTree::<256, PallasParameters, VestaParameters>::from_set(&set, &sr_params, Some(4));

    let randomized_pk_0 = Coin::<PallasParameters, PallasP>::rerandomized_pk(
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
    let randomized_pk_1 = Coin::<PallasParameters, PallasP>::rerandomized_pk(
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
    let proof = {
        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let pallas_prover: Prover<_, GroupAffine<PallasParameters>> =
            Prover::new(&sr_params.c0_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let vesta_prover: Prover<_, GroupAffine<VestaParameters>> =
            Prover::new(&sr_params.c1_parameters.pc_gens, vesta_transcript);

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
            &mut rng,
        )
    };

    println!("Proof size in bytes {}", proof.serialized_size());

    group.bench_function("verification_gadget", |b| {
        b.iter(|| {
            proof
                .clone()
                .verification_gadget(b"select_and_rerandomize", &sr_params, &curve_tree);
        })
    });
    group.bench_function("verify_single", |b| {
        b.iter(|| {
            let (pallas_vt, vesta_vt) = proof.clone().verification_gadget(
                b"select_and_rerandomize",
                &sr_params,
                &curve_tree,
            );

            // todo benchmark gadget vs msm time
            batch_verify(
                vec![pallas_vt],
                &sr_params.c0_parameters.pc_gens,
                &sr_params.c0_parameters.bp_gens,
            )
            .unwrap();
            batch_verify(
                vec![vesta_vt],
                &sr_params.c1_parameters.pc_gens,
                &sr_params.c1_parameters.bp_gens,
            )
            .unwrap();
        })
    });

    use std::iter;

    for n in [2, 10, 50, 100, 150, 200] {
        group.bench_with_input(
            format!("batch{}", n),
            &iter::repeat(proof.clone()).take(n).collect::<Vec<_>>(),
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
                            &sr_params.c0_parameters.pc_gens,
                            &sr_params.c0_parameters.bp_gens,
                        )
                        .unwrap();
                        batch_verify(
                            vesta_verification_scalars_and_points,
                            &sr_params.c1_parameters.pc_gens,
                            &sr_params.c1_parameters.bp_gens,
                        )
                        .unwrap();
                    }
                    #[cfg(feature = "parallel")]
                    {
                        let proofs_and_commitment_paths = proofs.par_iter().map(|proof| {
                            let cp0 = curve_tree.select_and_rerandomize_verification_commitments(
                                proof.randomized_path_0.clone(),
                            );
                            let cp1 = curve_tree.select_and_rerandomize_verification_commitments(
                                proof.randomized_path_1.clone(),
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
                                    &sr_params.c0_parameters.pc_gens,
                                    &sr_params.c0_parameters.bp_gens,
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
                                    &sr_params.c1_parameters.pc_gens,
                                    &sr_params.c1_parameters.bp_gens,
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
