#![allow(non_snake_case)]
//! Definition of the proof struct.

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress};

use crate::errors::R1CSError;
use crate::inner_product_proof::InnerProductProof;

/// A proof of some statement specified by a
/// [`ConstraintSystem`](::r1cs::ConstraintSystem).
///
/// Statements are specified by writing gadget functions which add
/// constraints to a [`ConstraintSystem`](::r1cs::ConstraintSystem)
/// implementation.  To construct an [`R1CSProof`], a prover constructs
/// a [`ProverCS`](::r1cs::ProverCS), then passes it to gadget
/// functions to build the constraint system, then consumes the
/// constraint system using
/// [`ProverCS::prove`](::r1cs::ProverCS::prove) to produce an
/// [`R1CSProof`].  To verify an [`R1CSProof`], a verifier constructs a
/// [`VerifierCS`](::r1cs::VerifierCS), then passes it to the same
/// gadget functions to (re)build the constraint system, then consumes
/// the constraint system using
/// [`VerifierCS::verify`](::r1cs::VerifierCS::verify) to verify the
/// proof.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
#[allow(non_snake_case)]
pub struct R1CSProof<C: AffineRepr> {
    /// Commitment to the values of input wires in the first phase.
    pub(super) A_I1: C,
    /// Commitment to the values of output wires in the first phase.
    pub(super) A_O1: C,
    /// Commitment to the blinding factors in the first phase.
    pub(super) S1: C,
    /// Commitment to the (A_I2, A_O2, S2) tuple if the second phase
    pub(super) second_phase: Option<(C, C, C)>,
    /// Commitments to the transmitted coefficients of \(t(X)\), in increasing degree order.
    pub(super) T: Vec<C>,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(super) t_x: C::ScalarField,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(super) t_x_blinding: C::ScalarField,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    pub(super) e_blinding: C::ScalarField,
    /// Proof data for the inner-product argument.
    pub(super) ipp_proof: InnerProductProof<C>,
}

impl<C: AffineRepr> R1CSProof<C> {
    pub fn second_phase_commitments(&self) -> (C, C, C) {
        self.second_phase
            .unwrap_or((C::zero(), C::zero(), C::zero()))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size(Compress::Yes));
        if let Err(e) = self.serialize_compressed(&mut buf) {
            panic!("{}", e)
        }
        buf
    }

    pub fn from_bytes(slice: &[u8]) -> Result<R1CSProof<C>, R1CSError> {
        Self::deserialize_compressed(slice).map_err(|_| R1CSError::FormatError)
    }
}
