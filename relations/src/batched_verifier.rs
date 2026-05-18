use crate::batched_prover::{
    batched_select_and_accumulate_non_root, batched_select_and_accumulate_root,
};
use crate::curve_tree::{Root, SelectAndRerandomizeMultiPathWithDivisorComms};
use crate::error::{Error, Result};
use crate::parameters::SelRerandProofParametersRef;
use crate::prover::constraints_for_dlogs;
use crate::select::select;
use crate::verifier::commit_dlog_and_divisor;
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_std::{string::ToString, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Variable, Verifier};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > SelectAndRerandomizeMultiPathWithDivisorComms<L, M, P0, P1>
{
    /// Divisor-based batched select and rerandomize verifier gadget.
    pub fn batched_select_and_rerandomize_verifier_gadget<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        root: &Root<L, M, P0, P1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
    ) -> Result<()> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let num_indices_usize = self.path.selected_commitments.len();
        if num_indices_usize == 0 {
            return Err(Error::NeedNonZeroNumberOfIndices);
        }
        let num_indices = num_indices_usize as u32;
        // assert_eq!(leaf_comms.len(), num_indices as usize);

        let mut even_node_divisors = Vec::new();
        let mut odd_node_divisors = Vec::new();

        // Process root level and learn if it's even or odd
        let root_is_even = match root {
            Root::Even(root_node) => {
                let mut all_x_coords: Vec<F0> = Vec::with_capacity(L * num_indices as usize);
                for i in 0..num_indices as usize {
                    let x_coords = root_node.x_coord_children.get(i).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "root x_coord_children shorter than selected indices for even root"
                                .to_string(),
                        )
                    })?;
                    all_x_coords.extend_from_slice(x_coords.as_slice());
                }

                let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_root::<F0, P1, _>(
                    even_verifier,
                    num_indices,
                    &all_x_coords,
                    None,
                )?;

                let root_child = self.path.odd_commitments.get(0).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root child in odd_commitments for even root".to_string(),
                    )
                })?;
                let shifted_rerandomized = (*root_child
                    + (odd_parameters.sl_params.delta * P1::ScalarField::from(num_indices)))
                .into_affine();
                let (x, y) = shifted_rerandomized.xy().ok_or(Error::PointCantBeZero)?;

                let p = commit_dlog_and_divisor::<_, _, Parameters0>(
                    even_verifier,
                    self.even_divisor_comms.get(0).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing root divisor commitments for even side".to_string(),
                        )
                    })?,
                )?;
                even_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
                true
            }
            Root::Odd(root_node) => {
                let mut all_x_coords: Vec<F1> = Vec::with_capacity(L * num_indices as usize);
                for i in 0..num_indices as usize {
                    let x_coords = root_node.x_coord_children.get(i).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "root x_coord_children shorter than selected indices for odd root"
                                .to_string(),
                        )
                    })?;
                    all_x_coords.extend_from_slice(x_coords.as_slice());
                }

                let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_root::<F1, P0, _>(
                    odd_verifier,
                    num_indices,
                    &all_x_coords,
                    None,
                )?;

                let root_child = self.path.even_commitments.get(0).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root child in even_commitments for odd root".to_string(),
                    )
                })?;
                let shifted_rerandomized = (*root_child
                    + (even_parameters.sl_params.delta * P0::ScalarField::from(num_indices)))
                .into_affine();
                let (x, y) = shifted_rerandomized.xy().ok_or(Error::PointCantBeZero)?;

                let p = commit_dlog_and_divisor::<_, _, Parameters1>(
                    odd_verifier,
                    self.odd_divisor_comms.get(0).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing root divisor commitments for odd side".to_string(),
                        )
                    })?,
                )?;
                odd_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
                false
            }
        };

        // Process non-root nodes using closures (similar to verifier.rs pattern)
        let mut commit_even = || -> Result<()> {
            let even_length = self.path.even_commitments.len();
            for parent_index in 0..even_length {
                let child_index = if root_is_even {
                    parent_index.checked_add(1).ok_or_else(|| {
                        Error::MalformedProofInput("child index overflow on even side".to_string())
                    })?
                } else {
                    parent_index
                };

                let parent_commitment =
                    self.path
                        .even_commitments
                        .get(parent_index)
                        .ok_or_else(|| {
                            Error::MalformedProofInput(
                                "even_commitments shorter than required for even-side traversal"
                                    .to_string(),
                            )
                        })?;
                let child_commitment =
                    self.path.odd_commitments.get(child_index).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "odd_commitments shorter than required for even-side traversal"
                                .to_string(),
                        )
                    })?;
                let divisor_comms = self.even_divisor_comms.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "even_divisor_comms shorter than required for even-side traversal"
                            .to_string(),
                    )
                })?;

                let children_vars: Vec<Variable<F0>> =
                    even_verifier.commit_vec(L * num_indices as usize, *parent_commitment);
                let children_vars: Vec<LinearCombination<F0>> =
                    children_vars.into_iter().map(|v| v.into()).collect();
                let (_, sum_x_var, sum_y_var) = batched_select_and_accumulate_non_root::<F0, P1, _>(
                    even_verifier,
                    num_indices,
                    children_vars,
                    None,
                )?;

                let shifted_rerandomized = (*child_commitment
                    + (odd_parameters.sl_params.delta * P1::ScalarField::from(num_indices)))
                .into_affine();
                let (x, y) = shifted_rerandomized.xy().ok_or(Error::PointCantBeZero)?;

                let p = commit_dlog_and_divisor::<_, _, Parameters0>(even_verifier, divisor_comms)?;
                even_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
            }
            Ok(())
        };

        commit_even()?;

        let mut commit_odd = || -> Result<()> {
            let odd_length = self.path.odd_commitments.len();
            for parent_index in 0..odd_length {
                let child_index = if !root_is_even {
                    parent_index.checked_add(1).ok_or_else(|| {
                        Error::MalformedProofInput("child index overflow on odd side".to_string())
                    })?
                } else {
                    parent_index
                };

                // Skip the last level - that's leaves, handled separately
                if parent_index < (odd_length - 1) {
                    let parent_commitment =
                        self.path.odd_commitments.get(parent_index).ok_or_else(|| {
                            Error::MalformedProofInput(
                                "odd_commitments shorter than required for odd-side traversal"
                                    .to_string(),
                            )
                        })?;
                    let child_commitment =
                        self.path.even_commitments.get(child_index).ok_or_else(|| {
                            Error::MalformedProofInput(
                                "even_commitments shorter than required for odd-side traversal"
                                    .to_string(),
                            )
                        })?;
                    let divisor_comms =
                        self.odd_divisor_comms.get(child_index).ok_or_else(|| {
                            Error::MalformedProofInput(
                                "odd_divisor_comms shorter than required for odd-side traversal"
                                    .to_string(),
                            )
                        })?;

                    let children_vars: Vec<Variable<F1>> =
                        odd_verifier.commit_vec(L * num_indices as usize, *parent_commitment);
                    let children_vars: Vec<LinearCombination<F1>> =
                        children_vars.into_iter().map(|v| v.into()).collect();
                    let (_, sum_x_var, sum_y_var) =
                        batched_select_and_accumulate_non_root::<F1, P0, _>(
                            odd_verifier,
                            num_indices,
                            children_vars,
                            None,
                        )?;

                    let shifted_rerandomized = (*child_commitment
                        + (even_parameters.sl_params.delta * P0::ScalarField::from(num_indices)))
                    .into_affine();
                    let (x, y) = shifted_rerandomized.xy().ok_or(Error::PointCantBeZero)?;

                    let p =
                        commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, divisor_comms)?;
                    odd_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
                }
            }
            Ok(())
        };

        commit_odd()?;

        // Process leaf level - individual verification for each leaf
        {
            let odd_length = self.path.odd_commitments.len();
            let parent_index = odd_length.checked_sub(1).ok_or_else(|| {
                Error::MalformedProofInput(
                    "odd_commitments must contain at least one element for leaf verification"
                        .to_string(),
                )
            })?;

            // Commit to parent to get variables

            let parent_commitment =
                self.path.odd_commitments.get(parent_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "odd_commitments shorter than required for leaf verification".to_string(),
                    )
                })?;
            let children_vars: Vec<Variable<F1>> =
                odd_verifier.commit_vec(L * num_indices as usize, *parent_commitment);
            if children_vars.len() % num_indices_usize != 0 {
                return Err(Error::MalformedProofInput(
                    "leaf parent commitment does not split evenly across selected indices"
                        .to_string(),
                ));
            }
            let chunk_size = children_vars.len() / num_indices_usize;
            if chunk_size == 0 {
                return Err(Error::MalformedProofInput(
                    "leaf parent commitment produced empty chunks".to_string(),
                ));
            }
            let chunks: Vec<_> = children_vars.chunks_exact(chunk_size).collect();

            let leaf_divisor_start = self
                .odd_divisor_comms
                .len()
                .checked_sub(num_indices_usize)
                .ok_or_else(|| {
                    Error::MalformedProofInput(
                        "odd_divisor_comms shorter than selected indices for leaf verification"
                            .to_string(),
                    )
                })?;

            for (i, chunk) in chunks.iter().enumerate() {
                let x_var: LinearCombination<F1> = odd_verifier.allocate(None)?.into();
                let y_var = odd_verifier.allocate(None)?.into();

                // Select
                let children_lc: Vec<LinearCombination<F1>> =
                    chunk.iter().map(|v| (*v).into()).collect();
                select(odd_verifier, x_var.clone(), children_lc.into_iter())?;

                // Add transcript entry for rerandomized leaf
                let selected_commitment =
                    self.path.selected_commitments.get(i).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "selected_commitments shorter than inferred leaf chunks".to_string(),
                        )
                    })?;
                odd_verifier
                    .transcript()
                    .append(b"rerandomized_child", selected_commitment);

                let rerandomized_plus_delta =
                    (*selected_commitment + even_parameters.sl_params.delta).into_affine();
                let (x, y) = rerandomized_plus_delta.xy().ok_or(Error::PointCantBeZero)?;

                let leaf_divisor = self
                    .odd_divisor_comms
                    .get(leaf_divisor_start + i)
                    .ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing leaf divisor commitment for selected index".to_string(),
                        )
                    })?;
                let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, leaf_divisor)?;
                odd_node_divisors.push((x_var, y_var, x, y, p));
            }
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
}
