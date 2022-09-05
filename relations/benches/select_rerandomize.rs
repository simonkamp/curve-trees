#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate bulletproofs;
use bulletproofs::r1cs::batch_verify;

extern crate relations;
use relations::select_rerandomize::*;

extern crate pasta;
use pasta::{
    pallas::{Affine as PallasAffine, PallasParameters},
    vesta::{Affine as VestaAffine, VestaParameters},
};

use ark_ec::AffineCurve;
use ark_serialize::CanonicalSerialize;

type PallasScalar = <PallasAffine as AffineCurve>::ScalarField;
type PallasBase = <PallasAffine as AffineCurve>::BaseField;
type VestaScalar = <VestaAffine as AffineCurve>::ScalarField;
type VestaBase = <VestaAffine as AffineCurve>::BaseField;

fn bench_select_and_rerandomize_prove(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << 12; // minimum sufficient power of 2

    let sr_params =
        SelRerandParameters::<PallasParameters, VestaParameters>::new(generators_length, &mut rng);

    c.bench_function("prove", |b| {
        b.iter(|| {
            let sr_proof = prove_from_mock_curve_tree(&sr_params);
        })
    });
}

criterion_group! {
    name = select_and_rerandomize_prove;
    config = Criterion::default().sample_size(10);
    targets =
    bench_select_and_rerandomize_prove,
}

fn bench_select_and_rerandomize_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("Verification of select and randomize proofs");

    let mut rng = rand::thread_rng();
    let generators_length = 1 << 12; // minimum sufficient power of 2

    let sr_params =
        SelRerandParameters::<PallasParameters, VestaParameters>::new(generators_length, &mut rng);
    let sr_proof = prove_from_mock_curve_tree(&sr_params);

    println!("Proof size in bytes {}", sr_proof.serialized_size());

    group.bench_function("verify_single", |b| {
        b.iter(|| {
            // benchmarks all of the verification steps, except:
            // 1) checking if both msms return zero
            // 2) that the root of the curve is consistent with the known curve tree
            let (pallas_verifier, vesta_verifier) = verification_circuit(&sr_params, &sr_proof);
            let p_res = pallas_verifier.verify(
                &sr_proof.pallas_proof,
                &sr_params.c1_parameters.pc_gens,
                &sr_params.c1_parameters.bp_gens,
            );
            let v_res = vesta_verifier.verify(
                &sr_proof.vesta_proof,
                &sr_params.c2_parameters.pc_gens,
                &sr_params.c2_parameters.bp_gens,
            );
        })
    });

    use std::iter;

    for n in [1, 10, 50, 99, 100, 199, 200] {
        group.bench_with_input(
            format!("Batch verification of {} proofs.", n),
            &iter::repeat(&sr_proof).take(n).collect::<Vec<_>>(),
            |b, proofs| {
                b.iter(|| {
                    // proofs.map(|sr_proof| verification_circuit(&sr_params, sr_proof));
                    let mut pallas_verification_scalars_and_points =
                        Vec::with_capacity(proofs.len());
                    let mut vesta_verification_scalars_and_points =
                        Vec::with_capacity(proofs.len());
                    for sr_proof in proofs {
                        let (pallas_verifier, vesta_verifier) =
                            verification_circuit(&sr_params, &sr_proof);
                        pallas_verification_scalars_and_points.push(
                            pallas_verifier
                                .verification_scalars_and_points(&sr_proof.pallas_proof)
                                .unwrap(),
                        );
                        vesta_verification_scalars_and_points.push(
                            vesta_verifier
                                .verification_scalars_and_points(&sr_proof.vesta_proof)
                                .unwrap(),
                        );
                    }
                    let p_res = batch_verify(
                        pallas_verification_scalars_and_points,
                        &sr_params.c1_parameters.pc_gens,
                        &sr_params.c1_parameters.bp_gens,
                    );
                    let v_res = batch_verify(
                        vesta_verification_scalars_and_points,
                        &sr_params.c2_parameters.pc_gens,
                        &sr_params.c2_parameters.bp_gens,
                    );
                    // should assert that the result is Ok
                })
            },
        );
    }
}

criterion_group! {
    name = select_and_rerandomize_verify;
    config = Criterion::default();
    targets =
    bench_select_and_rerandomize_verify,
}

// The benckmark for prove is ignored as it is very slow.
criterion_main!(select_and_rerandomize_verify);
