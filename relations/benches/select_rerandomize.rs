#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate bulletproofs;
use bulletproofs::r1cs::{batch_verify, Prover, Verifier};

extern crate relations;
use relations::select_and_rerandomize::*;

extern crate pasta;
use pasta::{
    pallas::{PallasParameters, Projective as PallasP},
    vesta::VestaParameters,
};

use ark_ec::{short_weierstrass_jacobian::GroupAffine, ProjectiveCurve};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;

use merlin::Transcript;

fn bench_select_and_rerandomize_verify(c: &mut Criterion) {
    bench_select_and_rerandomize_with_parameters::<256>(c, 4, 12);
    bench_select_and_rerandomize_with_parameters::<32>(c, 4, 11);
    bench_select_and_rerandomize_with_parameters::<1024>(c, 2, 11);
}

fn bench_select_and_rerandomize_with_parameters<const L: usize>(
    // `L` is the branching factor of the curve tree
    c: &mut Criterion,
    depth: usize,                   // the depth of the curve tree
    generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
) {
    let group_name = format!("Select&Rerandomize. Branching: {}, Depth: {}.", L, depth);
    let mut group = c.benchmark_group(group_name);

    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
        generators_length,
        generators_length,
        &mut rng,
    );

    let some_point = PallasP::rand(&mut rng).into_affine();
    let (permissible_point, _) = sr_params
        .c0_parameters
        .uh
        .permissible_commitment(&some_point, &sr_params.c0_parameters.pc_gens.B_blinding);
    let set = vec![permissible_point];
    let curve_tree =
        CurveTree::<L, PallasParameters, VestaParameters>::from_set(&set, &sr_params, Some(depth));

    let (path, pallas_proof, vesta_proof) = {
        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, GroupAffine<PallasParameters>> =
            Prover::new(&sr_params.c0_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, GroupAffine<VestaParameters>> =
            Prover::new(&sr_params.c1_parameters.pc_gens, vesta_transcript);

        let (path, _) = curve_tree.select_and_rerandomize_prover_gadget(
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
        );
        println!(
            "Number of constraints: {}",
            pallas_prover.number_of_constraints()
        );
        let pallas_proof = pallas_prover
            .prove(&sr_params.c0_parameters.bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&sr_params.c1_parameters.bp_gens)
            .unwrap();
        (path, pallas_proof, vesta_proof)
    };

    println!(
        "Proof size in bytes: {}",
        path.serialized_size() + pallas_proof.serialized_size() + vesta_proof.serialized_size()
    );

    group.bench_function("verification_gadget", |b| {
        b.iter(|| {
            let pallas_transcript = Transcript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = Transcript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let _ = curve_tree.select_and_rerandomize_verifier_gadget(
                &mut pallas_verifier,
                &mut vesta_verifier,
                path.clone(),
                &sr_params,
                L,
            );
        })
    });
    group.bench_function("verification_tuples", |b| {
        b.iter(|| {
            let pallas_transcript = Transcript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = Transcript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let _ = curve_tree.select_and_rerandomize_verifier_gadget(
                &mut pallas_verifier,
                &mut vesta_verifier,
                path.clone(),
                &sr_params,
                L,
            );

            let _ = pallas_verifier
                .verification_scalars_and_points(&pallas_proof)
                .unwrap();
            let _ = vesta_verifier
                .verification_scalars_and_points(&vesta_proof)
                .unwrap();
        })
    });
    group.bench_function("verify_single", |b| {
        b.iter(|| {
            let pallas_transcript = Transcript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = Transcript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let _ = curve_tree.select_and_rerandomize_verifier_gadget(
                &mut pallas_verifier,
                &mut vesta_verifier,
                path.clone(),
                &sr_params,
                L,
            );

            let pallas_vt = pallas_verifier
                .verification_scalars_and_points(&pallas_proof)
                .unwrap();
            let vesta_vt = vesta_verifier
                .verification_scalars_and_points(&vesta_proof)
                .unwrap();

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
            format!("Batch verify {} proofs.", n),
            &iter::repeat(path.clone()).take(n).collect::<Vec<_>>(),
            |b, proofs| {
                b.iter(|| {
                    let mut pallas_verification_scalars_and_points =
                        Vec::with_capacity(proofs.len());
                    let mut vesta_verification_scalars_and_points =
                        Vec::with_capacity(proofs.len());
                    for path in proofs {
                        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
                        let mut pallas_verifier = Verifier::new(pallas_transcript);
                        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
                        let mut vesta_verifier = Verifier::new(vesta_transcript);

                        let _ = curve_tree.select_and_rerandomize_verifier_gadget(
                            &mut pallas_verifier,
                            &mut vesta_verifier,
                            path.clone(),
                            &sr_params,
                            L,
                        );

                        let pallas_vt = pallas_verifier
                            .verification_scalars_and_points(&pallas_proof)
                            .unwrap();
                        let vesta_vt = vesta_verifier
                            .verification_scalars_and_points(&vesta_proof)
                            .unwrap();

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
                })
            },
        );
    }
}

criterion_group! {
    name = select_and_rerandomize_verify;
    config = Criterion::default().sample_size(20);
    targets =
    bench_select_and_rerandomize_verify,
}

// The benckmark for prove is ignored as it is very slow.
criterion_main!(select_and_rerandomize_verify);
