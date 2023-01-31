# Curve Trees

This is a benchmarking implementation for [Curve Trees](https://eprint.iacr.org/2022/756). It is not for production purposes.

This repository contains:
- A modified version of [dalek bulletproofs](https://github.com/dalek/bulletproofs), 
which is adapted to support curves implemented using the [arkworks algebra library](https://github.com/arkworks-rs/algebra)
in addition to batch verification and vector commitments.
- Bulletproof constraints to show that a commitment is a rerandomization of a member of the set represented by a curve tree. I.e. the select and rerandomize relation.
- Benchmarks for the VCash anonymous payment system.

## Running Benchmarks

To replicate the benchmarks in the [Curve Trees](https://eprint.iacr.org/2022/756) paper run: `cargo bench --features bench_prover`.

To get single core benchmarks disable default features: `cargo bench --features bench_prover --no-default-features`.

## Acknowledgements

The bulletproofs implementation is based on [dalek bulletproofs](https://github.com/dalek/bulletproofs) and the [arkworks algebra library](https://github.com/arkworks-rs/algebra).

## LICENSE

This code is released under the MIT License.
