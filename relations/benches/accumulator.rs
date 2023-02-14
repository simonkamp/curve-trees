#[macro_use]
extern crate criterion;
use criterion::{BenchmarkId, Criterion};

extern crate bulletproofs;
use bulletproofs::r1cs::{batch_verify, LinearCombination, Prover, Verifier};

extern crate relations;
use relations::{curve_tree::*, select::*};

use ark_pallas::{Fr as PallasScalar, PallasConfig};
use ark_vesta::VestaConfig;

use ark_ec::short_weierstrass::Affine;
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::{UniformRand, Zero};

use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

fn bench_accumulator(c: &mut Criterion) {
    bench_accumulator_with_parameters::<256>(c, 3, 64, 11, 12);
    // bench_accumulator_with_parameters::<512>(c, 3, 8, 11, 12);
    // bench_accumulator_with_parameters::<1024>(c, 2, 1024, 12, 11);
}

// `L` is the branching factor of the curve tree
fn bench_accumulator_with_parameters<const L: usize>(
    c: &mut Criterion,
    depth: usize,                        // the depth of the curve tree
    leaf_width: usize, // the maximum number of field elements stored in a curve tree leaf
    even_generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
    odd_generators_length_log_2: usize, // should be minimal but larger than the number of constraints.
) {
    let mut rng = rand::thread_rng();
    let even_generators_length = 1 << even_generators_length_log_2;
    let odd_generators_length = 1 << odd_generators_length_log_2;

    let sr_params = SelRerandParameters::<PallasConfig, VestaConfig>::new(
        even_generators_length,
        odd_generators_length,
        &mut rng,
    );

    let leaf_elements: Vec<_> = (0..leaf_width)
        .map(|_| PallasScalar::rand(&mut rng))
        .collect();
    let element = leaf_elements[0];
    // Unless all leafs of the curve tree are occupied, it would always be possible to open to zero by using an empty leaf.
    assert_ne!(element, PallasScalar::zero());
    let leaf_commitment = sr_params
        .even_parameters
        .commit(&leaf_elements, PallasScalar::zero(), 0);

    let (permissible_point, permissible_randomness) =
        sr_params.even_parameters.uh.permissible_commitment(
            &leaf_commitment,
            &sr_params.even_parameters.pc_gens.B_blinding,
        );
    let set = vec![permissible_point];
    let curve_tree =
        CurveTree::<L, PallasConfig, VestaConfig>::from_set(&set, &sr_params, Some(depth));

    let prove = |print| {
        let pallas_transcript = Transcript::new(b"acc");
        let mut pallas_prover: Prover<_, Affine<PallasConfig>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"acc");
        let mut vesta_prover: Prover<_, Affine<VestaConfig>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let (path, rerandomization) = curve_tree.select_and_rerandomize_prover_gadget(
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rand::thread_rng(),
        );

        let (leaf_commitment, leaf_vars) = pallas_prover.commit_vec(
            &leaf_elements,
            permissible_randomness + rerandomization,
            &sr_params.even_parameters.bp_gens,
        );
        assert_eq!(leaf_commitment, path.get_rerandomized_leaf()); // sanity check

        select(
            &mut pallas_prover,
            LinearCombination::from(element),
            leaf_vars
                .iter()
                .map(|var| LinearCombination::from(*var))
                .collect(),
        );

        if print {
            println!(
                "Number of constraints pallas: {}",
                pallas_prover.number_of_constraints()
            );
            println!(
                "Number of constraints vesta: {}",
                vesta_prover.number_of_constraints()
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
        "Proof size in bytes: {}",
        path.serialized_size(Compress::Yes)
            + pallas_proof.serialized_size(Compress::Yes)
            + vesta_proof.serialized_size(Compress::Yes)
    );

    
    #[cfg(feature = "bench_prover")]
    {
        let group_name = format!("acc.L={},d={}.", L, depth);
        let mut group = c.benchmark_group(group_name);
        group.bench_function("prover", |b| b.iter(|| prove(false)));
    }

    let group_name = format!("acc_batch_verification.L={},d={}.", L, depth);
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
                            curve_tree.select_and_rerandomize_verification_commitments(path.clone())
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
                                                .map(|var| LinearCombination::from(*var))
                                                .collect(),
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
                            curve_tree.select_and_rerandomize_verification_commitments(path.clone())
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
                                        leaf_vars
                                            .iter()
                                            .map(|var| LinearCombination::from(*var))
                                            .collect(),
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
