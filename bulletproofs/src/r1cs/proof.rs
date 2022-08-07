#![allow(non_snake_case)]
//! Definition of the proof struct.

use ark_ec::AffineCurve;
use ark_std::Zero;

use crate::errors::R1CSError;
use crate::inner_product_proof::InnerProductProof;

const ONE_PHASE_COMMITMENTS: u8 = 0;
const TWO_PHASE_COMMITMENTS: u8 = 1;

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
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct R1CSProof<C: AffineCurve> {
    /// Commitment to the values of input wires in the first phase.
    pub(super) A_I1: C,
    /// Commitment to the values of output wires in the first phase.
    pub(super) A_O1: C,
    /// Commitment to the blinding factors in the first phase.
    pub(super) S1: C,
    /// Commitment to the values of input wires in the second phase.
    pub(super) A_I2: C,
    /// Commitment to the values of output wires in the second phase.
    pub(super) A_O2: C,
    /// Commitment to the blinding factors in the second phase.
    pub(super) S2: C,
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

impl<C: AffineCurve> R1CSProof<C> {
    /// Returns the size in bytes required to serialize the `R1CSProof`.
    pub fn serialized_size(&self) -> usize {
        // version tag + (11 or 14) elements + the ipp
        let elements = if self.missing_phase2_commitments() {
            11
        } else {
            14
        };
        1 + elements * 32 + self.ipp_proof.serialized_size()
    }

    fn missing_phase2_commitments(&self) -> bool {
        self.A_I2.is_zero() && self.A_O2.is_zero() && self.S2.is_zero()
    }
}
