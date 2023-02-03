// 3-bit lookups
pub mod lookup;

// Curve operations
pub mod curve;

// Rerandomize commitments
pub mod rerandomize;

// Show that a value is in a set of variables
pub mod select;

// Prove that a commitment to x defines a canonical point (x,y)
pub mod permissible;

// Given a set of committed variables (vars) and a public commitment (C)
// prove that vars contain an x-coordinate that expands a commitment (C')
// s.t. C is a rerandomization of C'
pub mod single_level_select_and_rerandomize;

// Multi-level select and rerandomize:
// Prove that a commitment is a rerandomization of a commitment contained in a Curve Tree
pub mod curve_tree;

// Prove that a committed variable is in the range [0, 2^k)
pub mod range_proof;

// Anonymous payments using Curve Trees and rerandomizable signatures
pub mod coin;
