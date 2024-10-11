// 3-bit lookups
pub mod lookup;

// Curve operations
pub mod curve;

// Rerandomize commitments
pub mod rerandomize;

// Show that a value is in a set of variables
pub mod select;

// Given a set of committed variables (vars) and a public commitment (C)
// prove that vars contain an x-coordinate that expands a commitment (C')
// s.t. C is a rerandomization of C'
pub mod single_level_select_and_rerandomize;

// Curve Tree data structure and functionality supporting membership proofs through multi-level select and rerandomize:
// Prove that a commitment is a rerandomization of a commitment contained in a Curve Tree
pub mod curve_tree;

// Prover logic for membership proofs
pub mod batched_curve_tree_prover;
pub mod curve_tree_prover;

// Verifier logic for membership proofs
pub mod batched_curve_tree_verifier;
pub mod curve_tree_verifier;

// Prove that a committed variable is in the range [0, 2^k)
pub mod range_proof;

// Anonymous payments using Curve Trees and rerandomizable signatures
pub mod coin;
