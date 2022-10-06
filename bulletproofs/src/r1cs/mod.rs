mod constraint_system;
mod linear_combination;
mod metrics;
mod proof;
mod prover;
mod verifier;

pub use self::constraint_system::{
    ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem,
};
pub use self::linear_combination::{constant, LinearCombination, Variable};
pub use self::metrics::Metrics;
pub use self::proof::R1CSProof;
pub use self::prover::Prover;
pub use self::verifier::{batch_verify, VerificationTuple, Verifier};

pub use crate::errors::R1CSError;

fn op_splits(op_deg: usize) -> Vec<(usize, usize)> {
    debug_assert_eq!(op_deg % 2, 0);
    let mid = op_deg / 2;

    // the first two are special
    let mut op_splits = Vec::with_capacity(op_deg);
    op_splits.push((mid, mid));
    op_splits.push((op_deg, 0));

    // all other deg splits
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
