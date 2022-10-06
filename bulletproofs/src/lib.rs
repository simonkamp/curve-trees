extern crate alloc;

mod util;

mod errors;
mod generators;
mod inner_product_proof;
mod transcript;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};

#[cfg(feature = "std")]
pub mod r1cs;
