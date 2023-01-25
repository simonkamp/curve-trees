#![allow(non_snake_case)]
//! Definition of the proof struct.

use ark_ec::AffineRepr;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Write,
};

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
pub struct R1CSProof<C: AffineRepr> {
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

impl<C: AffineRepr> R1CSProof<C> {
    fn missing_phase2_commitments(&self) -> bool {
        self.A_I2.is_zero() && self.A_O2.is_zero() && self.S2.is_zero()
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

impl<C: AffineRepr> CanonicalSerialize for R1CSProof<C> {
    /// Returns the size in bytes required to serialize the `R1CSProof`.
    fn serialized_size(&self, compress: Compress) -> usize {
        let number_of_points = if self.missing_phase2_commitments() {
            3
        } else {
            6
        };
        // allocate space for the 6 points
        let points_size = number_of_points * self.A_I1.serialized_size(compress);
        // allocate space for the T vector
        let t_size = self.T.serialized_size(compress);
        // size of 3 scalars
        let scalars_size = 3 * self.t_x.serialized_size(compress);
        // size of the inner product proof
        let ipp_size = self.ipp_proof.serialized_size(compress);
        points_size + t_size + scalars_size + ipp_size + 1
    }

    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        // serialize first phase commitments.
        self.A_I1.serialize_with_mode(&mut writer, compress)?;
        self.A_O1.serialize_with_mode(&mut writer, compress)?;
        self.S1.serialize_with_mode(&mut writer, compress)?;

        // serialize second phase commitments, if present.
        if self.missing_phase2_commitments() {
            ONE_PHASE_COMMITMENTS.serialize_with_mode(&mut writer, compress)?;
        } else {
            TWO_PHASE_COMMITMENTS.serialize_with_mode(&mut writer, compress)?;
            self.A_I2.serialize_with_mode(&mut writer, compress)?;
            self.A_O2.serialize_with_mode(&mut writer, compress)?;
            self.S2.serialize_with_mode(&mut writer, compress)?;
        }

        // Serialize T
        self.T.serialize_with_mode(&mut writer, compress)?;
        // serialize scalars
        self.t_x.serialize_with_mode(&mut writer, compress)?;
        self.t_x_blinding
            .serialize_with_mode(&mut writer, compress)?;
        self.e_blinding.serialize_with_mode(&mut writer, compress)?;
        // serialize inner product argument
        self.ipp_proof.serialize_with_mode(&mut writer, compress)?;

        Ok(())
    }
}

impl<C: AffineRepr> Valid for R1CSProof<C> {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}
impl<C: AffineRepr> CanonicalDeserialize for R1CSProof<C> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, SerializationError> {
        let A_I1 = C::deserialize_with_mode(&mut reader, compress, validate)?;
        let A_O1 = C::deserialize_with_mode(&mut reader, compress, validate)?;
        let S1 = C::deserialize_with_mode(&mut reader, compress, validate)?;
        let flag = u8::deserialize_with_mode(&mut reader, compress, validate)?;
        let (A_I2, A_O2, S2) = if flag == TWO_PHASE_COMMITMENTS {
            (
                C::deserialize_with_mode(&mut reader, compress, validate)?,
                C::deserialize_with_mode(&mut reader, compress, validate)?,
                C::deserialize_with_mode(&mut reader, compress, validate)?,
            )
        } else {
            (C::zero(), C::zero(), C::zero())
        };
        Ok(Self {
            A_I1,
            A_O1,
            S1,
            A_I2,
            A_O2,
            S2,
            T: Vec::<C>::deserialize_with_mode(&mut reader, compress, validate)?,
            t_x: C::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?,
            t_x_blinding: C::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?,
            e_blinding: C::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?,
            ipp_proof: InnerProductProof::<C>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
        })
    }
}
