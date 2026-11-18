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
pub use verifier::batch::combine_verification_tuples;

pub use crate::errors::R1CSError;

#[cfg(feature = "nightly_mocking_tests")]
pub use self::prover::{committed_vec_dimension, committed_vec_opening};

/// Returns
/// - degrees of polynomials l(x) and r(x) which will potentially contain terms involving a_L, a_R, a_O,
///   etc except the blinding terms s_L and s_R
/// - degree of the term of the product polynomial where inner product of "interest" (a_L, a_R, etc)
///   will live
fn degrees(num_vec_comms: usize) -> (Vec<(usize, usize)>, usize) {
    // Table 1 of the fixed generalized Bulletproofs draft uses n' = 2 * ncomm + 2.
    let d = 2 + 2 * num_vec_comms;
    let mid = num_vec_comms + 1; // mid = d / 2

    // the first two are set to match dalek's implementation exactly
    let mut l_r_degrees = Vec::with_capacity(d);
    // for `a_L` and `a_R`
    l_r_degrees.push((mid, mid));
    // for `a_O`
    l_r_degrees.push((d, 0));

    // all other deg splits, start from 1 since `a_O` is at 0
    for r_deg in 1..d + 1 {
        if r_deg == mid {
            // already taken
            continue;
        }
        let l_deg = d - r_deg;
        l_r_degrees.push((l_deg, r_deg));
        if l_r_degrees.len() == (num_vec_comms + 2) {
            // We have degrees for each vector commitment as well as (`a_L`, `a_R`) term and `a_O` term
            break;
        }
    }
    (l_r_degrees, d)
}

fn t_poly_degree(inner_product_degree: usize) -> usize {
    2 * (inner_product_degree + 1)
}

/// The degrees of product polynomial t(x) for which a commitment is created. The degree of t(x) below
/// inner_product_degree/2 have 0 coefficients since l(x) has 0 coefficients for those degrees
fn committed_t_degrees(inner_product_degree: usize) -> Vec<usize> {
    let mid = inner_product_degree / 2;
    let t_poly_deg = t_poly_degree(inner_product_degree);

    let mut degrees = Vec::with_capacity(t_poly_deg - mid);
    for d in mid..t_poly_deg + 1 {
        if d != inner_product_degree {
            degrees.push(d);
        }
    }
    degrees
}
