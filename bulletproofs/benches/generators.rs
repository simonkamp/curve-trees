use ark_pallas::Affine;

use bulletproofs::BulletproofGens;

#[macro_use]
extern crate criterion;
use criterion::Criterion;

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
        bp_gens
}

criterion_main!(bp);
