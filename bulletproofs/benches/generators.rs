use pasta::pallas::Affine;

use bulletproofs::{BulletproofGens, PedersenGens};

#[macro_use]
extern crate criterion;
use criterion::Criterion;

fn pc_gens(c: &mut Criterion) {
    let mut group = c.benchmark_group("PedersenGens");
    group.bench_function("PedersenGens::default", |b| {
        b.iter(|| PedersenGens::<Affine>::default())
    });

    for i in 0..10 {
        group.bench_with_input(
            format!("PedersenGens::new, size = {}", i),
            &(2 << i),
            |b, size| b.iter(|| PedersenGens::<Affine>::new(*size)),
        );
    }
    group.finish()
}

fn bp_gens(c: &mut Criterion) {
    let mut group = c.benchmark_group("BulletproofGens");
    for i in 0..10 {
        group.bench_with_input(
            format!("BulletproofGens::new, size = {}", i),
            &(2 << i),
            |b, size| b.iter(|| BulletproofGens::<Affine>::new(*size, 1)),
        );
    }
    group.finish()
}

criterion_group! {
    name = bp;
    config = Criterion::default().sample_size(10);
    targets =
        bp_gens,
        pc_gens,
}

criterion_main!(bp);
