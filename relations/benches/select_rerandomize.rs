#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate relations;
use relations::select_rerandomize::*;

extern crate pasta;
use pasta::{
    pallas::{Affine as PallasAffine, PallasParameters},
    vesta::{Affine as VestaAffine, VestaParameters},
};

use ark_ec::AffineCurve;

type PallasScalar = <PallasAffine as AffineCurve>::ScalarField;
type PallasBase = <PallasAffine as AffineCurve>::BaseField;
type VestaScalar = <VestaAffine as AffineCurve>::ScalarField;
type VestaBase = <VestaAffine as AffineCurve>::BaseField;

fn bench_select_and_rerandomize_verify_single(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let generators_length = 2 << 11; // minimum sufficient power of 2

    let sr_params =
        SelRerandParameters::<PallasParameters, VestaParameters>::new(generators_length, &mut rng);
    let sr_proof = prove_from_mock_curve_tree(&sr_params);

    c.bench_function("verify_single", |b| {
        b.iter(|| {
            // benchmarks all of the verification steps, except:
            // 1) checking if both msms return zero
            // 2) that the root of the curve is consistent with the known curve tree
            let (pallas_verifier, vesta_verifier) = verification_circuit(&sr_params, &sr_proof);
            let p_res = pallas_verifier.verify(
                &sr_proof.pallas_proof,
                &sr_params.c1_pc_gens,
                &sr_params.c1_bp_gens,
            );
            let v_res = vesta_verifier.verify(
                &sr_proof.vesta_proof,
                &sr_params.c2_pc_gens,
                &sr_params.c2_bp_gens,
            );
        })
    });
}

criterion_group! {
    name = select_and_rerandomize_verify_single;
    config = Criterion::default();
    targets =
    bench_select_and_rerandomize_verify_single,
}

criterion_main!(select_and_rerandomize_verify_single);
