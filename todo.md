# To do

## Benchmarks
- Select and rerandomize
    - [] 2ˆ20ish, with ???^4
    - [] 2ˆ24, with 256ˆ3?
    - [x] 2ˆ32, with 256ˆ4
    - [] 2ˆ64, with 256ˆ8?
- Pour
    - [x] 2-2, 2ˆ32
    - [] 2-2, 2ˆ24?
    - [] 2-2, 2ˆ16?
- Pour PRF 
    - [] 2-2, 2ˆ32
- Stacked trees?
- Stacked layers?
    - branching factor 2?

## Features
1. Implement the "Full security through PRF" scheme.

## Performance improvements
1. Experiment with flags, features, and nightly performance.
2. Multithreaded performance.
    * Dual core: Split between even and odd curve.
    * Multithreaded: Threadpool handling the non-batched parts.
3. Proofs about the coins in r1cs or alternatives?
3. Stacking 2 curve trees to halve the number of rerandomizations.
4. Stacking the layers of curve trees?
5. If above does not increase the number of commitments, decrease branching factor to 2.
6. RUSTFLAGS="-C target-cpu=native"
