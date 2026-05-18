#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
pub use verifier::batch::add_verification_tuples_to_rmc;
pub use verifier::batch::add_verification_tuples_to_rmc_0;

pub mod constraint_system;
pub mod linear_combination;
mod metrics;
mod proof;
mod prover;
pub mod verifier;

pub use self::constraint_system::{
    ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem,
};
pub use self::linear_combination::{constant, LinearCombination, Variable};
pub use self::metrics::Metrics;
pub use self::proof::R1CSProof;
pub use self::prover::Prover;
pub use self::verifier::{
    add_verification_tuple_to_rmc, verify_given_verification_tuple, VerificationTuple, Verifier,
};
#[cfg(feature = "std")]
pub use verifier::batch::batch_verify;
pub use verifier::batch::batch_verify_with_rng;

pub use crate::errors::R1CSError;

fn op_splits(op_deg: usize) -> Vec<(usize, usize)> {
    debug_assert_eq!(op_deg % 2, 0);
    let mid = op_deg / 2;

    // the first two are set to match dalek's implementation exactly
    let mut op_splits = Vec::with_capacity(op_deg);
    // for `a_L` and `a_R`
    op_splits.push((mid, mid));
    // for `a_O`
    op_splits.push((op_deg, 0));

    // all other deg splits, start from 1 since `a_O` is at 0
    for r_deg in 1..op_deg + 1 {
        if r_deg == mid {
            // already taken
            continue;
        }
        let l_deg = op_deg - r_deg;
        op_splits.push((l_deg, r_deg));
    }

    op_splits
}

fn degree(ncomm: usize) -> usize {
    // Table 1 of the fixed generalized Bulletproofs draft uses n' = 2 * ncomm + 2.
    2 + 2 * ncomm
}

fn t_poly_degree(op_degree: usize) -> usize {
    2 * (op_degree + 1)
}

fn transmitted_t_degree_indices(op_degree: usize) -> Vec<usize> {
    let mid = op_degree / 2;
    let t_poly_deg = t_poly_degree(op_degree);

    let mut degrees = Vec::with_capacity(t_poly_deg - mid);
    for d in mid..t_poly_deg + 1 {
        if d != op_degree {
            degrees.push(d);
        }
    }
    degrees
}
