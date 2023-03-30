# Curve Trees

This is a benchmarking implementation for Curve Trees. It is not for production purposes.

This repository contains:
- A modified version of [dalek bulletproofs](https://github.com/dalek/bulletproofs), 
which is adapted to support any curve implemented using the [arkworks algebra library](https://github.com/arkworks-rs/algebra)
in addition to batch verification and vector commitments.
- Bulletproof constraints to show that a commitment is a rerandomization of a member of the set represented by a curve tree. I.e. the select and rerandomize relation.
- Benchmarks for the VCash anonymous payment system.
- Benchmarks for an accumulator based on opening a commitment extracted using the select and rerandomize relation.

## Running Benchmarks

To replicate the benchmarks in the Curve Trees paper run: 
```
cargo bench --features bench_prover
```

To get single core benchmarks disable default features: 
```
cargo bench --features bench_prover --no-default-features
```

## Acknowledgements

The bulletproofs implementation is based on [dalek bulletproofs](https://github.com/dalek/bulletproofs) and the [arkworks algebra library](https://github.com/arkworks-rs/algebra).

## LICENSE

This code is released under the MIT License.
