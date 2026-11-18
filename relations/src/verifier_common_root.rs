//! Common-root verifier.
//! When many curve-tree proofs are verified against the same root, the root's set-membership
//! check [`select_public_set`](crate::select::select_public_set)) rebuilds the same degree-`L`
//! vanishing polynomial of the root's public child x-coordinates for every proof.
//! That polynomial depends only on the (fixed) root, so it can be built once and reused.

use crate::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use crate::error::{Error, Result};
use crate::parameters::SelRerandProofParametersRef;
use crate::prover::{constraints_for_dlogs, select_root_given_poly, DlogItem};
use crate::verifier::commit_dlog_and_divisor;
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_dlog_gadget::dlog::DivisorComms;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::{Field, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_std::string::ToString;
use ark_std::vec;
use bulletproofs::r1cs::Verifier;
use dock_crypto_utils::poly::poly_from_roots;
use dock_crypto_utils::transcript::MerlinTranscript;

/// Precomputed vanishing polynomial of a curve-tree root's public child x-coordinates, built once
/// and reused across many proofs against that root.
pub enum RootChildrenPoly<F0: Field, F1: Field> {
    Even(DensePolynomial<F0>),
    Odd(DensePolynomial<F1>),
}

impl<F0: Field, F1: Field> RootChildrenPoly<F0, F1> {
    /// Build the polynomial from a fixed root. Compute this once and pass it to every proof's
    /// [`select_and_rerandomize_verifier_gadget_common_root`] call.
    ///
    /// [`select_and_rerandomize_verifier_gadget_common_root`]:
    /// SelectAndRerandomizePathWithDivisorComms::select_and_rerandomize_verifier_gadget_common_root
    pub fn from_root<const L: usize, P0, P1>(root: &Root<L, 1, P0, P1>) -> Result<Self>
    where
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    {
        match root {
            Root::Even(node) => {
                let xs = node.x_coord_children.first().ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root x-coordinates of children for even root".to_string(),
                    )
                })?;
                Ok(Self::Even(poly_from_roots::<F0>(xs)))
            }
            Root::Odd(node) => {
                let xs = node.x_coord_children.first().ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root x-coordinates of children for odd root".to_string(),
                    )
                })?;
                Ok(Self::Odd(poly_from_roots::<F1>(xs)))
            }
        }
    }
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > SelectAndRerandomizePathWithDivisorComms<L, P0, P1>
{
    /// Drop-in alternative to [`select_and_rerandomize_verifier_gadget`] that consumes a
    /// precomputed [`RootChildrenPoly`] for the root, skipping the per-proof O(L^2) reconstruction
    /// of the root's set-membership polynomial. Produces identical constraints, so a proof verifies
    /// the same way either gadget is used. Intended for verifying many proofs against one root.
    ///
    /// [`select_and_rerandomize_verifier_gadget`]:
    /// SelectAndRerandomizePathWithDivisorComms::select_and_rerandomize_verifier_gadget
    pub fn select_and_rerandomize_verifier_gadget_common_root<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        root: &Root<L, 1, P0, P1>,
        root_poly: &RootChildrenPoly<F0, F1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
    ) -> Result<()> {
        self.check_lengths_for_root(root)?;

        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let mut even_node_divisors = vec![];
        let mut odd_node_divisors = vec![];

        let root_is_even = match (root, root_poly) {
            (Root::Even(_), RootChildrenPoly::Even(poly)) => {
                let item = Self::verify_root_given_poly::<Parameters0>(
                    even_verifier,
                    &odd_parameters.sl_params.delta,
                    poly,
                    &self.path.odd_commitments,
                    &self.even_divisor_comms,
                )?;
                even_node_divisors.push(item);
                true
            }
            (Root::Odd(_), RootChildrenPoly::Odd(poly)) => {
                let item =
                    SelectAndRerandomizePathWithDivisorComms::<L, P1, P0>::verify_root_given_poly::<
                        Parameters1,
                    >(
                        odd_verifier,
                        &even_parameters.sl_params.delta,
                        poly,
                        &self.path.even_commitments,
                        &self.odd_divisor_comms,
                    )?;
                odd_node_divisors.push(item);
                false
            }
            // Root parity and supplied polynomial parity disagree.
            _ => {
                return Err(Error::MalformedProofInput(
                    "root_poly parity does not match root parity".to_string(),
                ))
            }
        };

        let mut commit_even = || -> Result<()> {
            // Last item of self.path.even_commitments is the leaf, which has no children.
            let even_non_root_len =
                self.path
                    .even_commitments
                    .len()
                    .checked_sub(1)
                    .ok_or_else(|| {
                        Error::MalformedProofInput(
                            "even_commitments must contain at least one element".to_string(),
                        )
                    })?;
            let items = Self::verify_non_root_levels_on_curve::<Parameters0>(
                even_verifier,
                root_is_even,
                even_non_root_len,
                &self.path.even_commitments,
                &self.path.odd_commitments,
                &self.even_divisor_comms,
                &odd_parameters.sl_params.delta,
            )?;
            even_node_divisors.extend(items);
            Ok(())
        };

        let mut commit_odd = || -> Result<()> {
            let odd_len = self.path.odd_commitments.len();
            let items =
                SelectAndRerandomizePathWithDivisorComms::<L, P1, P0>::verify_non_root_levels_on_curve::<
                    Parameters1,
                >(
                    odd_verifier,
                    !root_is_even,
                    odd_len,
                    &self.path.odd_commitments,
                    &self.path.even_commitments,
                    &self.odd_divisor_comms,
                    &even_parameters.sl_params.delta,
                )?;
            odd_node_divisors.extend(items);
            Ok(())
        };

        #[cfg(not(feature = "parallel"))]
        {
            commit_even()?;
            commit_odd()?;
        }

        #[cfg(feature = "parallel")]
        {
            let (even_res, odd_res) = rayon::join(|| commit_even(), || commit_odd());
            even_res?;
            odd_res?;
        }

        constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_verifier,
            odd_verifier,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors,
            odd_node_divisors,
        )?;
        Ok(())
    }

    /// Like [`verify_root`](super::verifier) but takes the precomputed root vanishing polynomial.
    fn verify_root_given_poly<Parameters: DiscreteLogParameters>(
        verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        delta: &Affine<P1>,
        root_poly: &DensePolynomial<F0>,
        child_commitments: &[Affine<P1>],
        divisor_comms: &[DivisorComms<Affine<P0>>],
    ) -> Result<DlogItem<F0, Parameters>> {
        let child = child_commitments.first().ok_or_else(|| {
            Error::MalformedProofInput("missing root child commitment".to_string())
        })?;
        let (x_var, y_var, x, y) = select_root_given_poly(verifier, delta, child, root_poly, None)?;
        let divisor = divisor_comms.first().ok_or_else(|| {
            Error::MalformedProofInput("missing root divisor commitment".to_string())
        })?;
        let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, divisor)?;
        Ok((x_var.into(), y_var.into(), x, y, p))
    }
}
