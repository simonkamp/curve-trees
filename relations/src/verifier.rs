use crate::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use crate::error::{Error, Result};
use crate::parameters::SelRerandProofParametersRef;
use crate::prover::{constraints_for_dlogs, select_non_root, select_root, DlogItem};
use crate::select::multi_select_public_set;
use ark_dlog_gadget::dlog::{
    commit_witness_chunks_verifier, DiscreteLogParameters, DivisorComms, PointWithDlog,
};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_std::vec;
use ark_std::{boxed::Box, format, string::ToString, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Verifier};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};

// NOTE: The verifier gadgets reject a path whose commitment or divisor commitment lengths don't match
// the root's height before touching the transcript or constraint system.

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > SelectAndRerandomizePathWithDivisorComms<L, P0, P1>
{
    pub fn select_and_rerandomize_verifier_gadget<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        root: &Root<L, 1, P0, P1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
    ) -> Result<()> {
        self.check_lengths_for_root(root)?;

        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let mut even_node_divisors = vec![];
        let mut odd_node_divisors = vec![];

        // The root's child lives on the other curve; the two arms are mirror images, so the odd
        // root reuses the same helper via the curve-swapped `<P1, P0>` instance.
        let root_is_even = match root {
            Root::Even(root) => {
                let item = Self::verify_root::<Parameters0>(
                    even_verifier,
                    &odd_parameters.sl_params.delta,
                    &root.x_coord_children,
                    &self.path.odd_commitments,
                    &self.even_divisor_comms,
                )?;
                even_node_divisors.push(item);
                true
            }
            Root::Odd(root) => {
                let item = SelectAndRerandomizePathWithDivisorComms::<L, P1, P0>::verify_root::<
                    Parameters1,
                >(
                    odd_verifier,
                    &even_parameters.sl_params.delta,
                    &root.x_coord_children,
                    &self.path.even_commitments,
                    &self.odd_divisor_comms,
                )?;
                odd_node_divisors.push(item);
                false
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

    pub fn select_and_rerandomize_verifier_gadget_multi<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        paths: &[Self],
        root: &Root<L, 1, P0, P1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
    ) -> Result<()> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let num_paths = paths.len();
        if num_paths == 0 {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }
        for path in paths {
            path.check_lengths_for_root(root)?;
        }

        let mut even_node_divisors = Vec::with_capacity(num_paths);
        let mut odd_node_divisors = Vec::with_capacity(num_paths);

        let root_is_even = match root {
            Root::Even(root_node) => {
                let delta = odd_parameters.sl_params.delta;
                let all_x_coords = root_node.x_coord_children.get(0).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root x_coord_children for even root".to_string(),
                    )
                })?;

                let mut re_randomized_children = Vec::with_capacity(num_paths);
                let mut even_node_comms = Vec::with_capacity(num_paths);
                for path in paths {
                    let child = *path.path.odd_commitments.get(0).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing root child in odd_commitments for even root".to_string(),
                        )
                    })?;
                    let root_divisor_comms = path.even_divisor_comms.first().ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing root divisor commitments for even side".to_string(),
                        )
                    })?;
                    re_randomized_children.push(child);
                    even_node_comms.push(root_divisor_comms);
                }

                Self::process_root_for_all::<Parameters0>(
                    even_verifier,
                    re_randomized_children,
                    all_x_coords,
                    delta,
                    &mut even_node_divisors,
                    &even_node_comms,
                )?;
                true
            }
            Root::Odd(root_node) => {
                let delta = even_parameters.sl_params.delta;
                let all_x_coords = root_node.x_coord_children.get(0).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root x_coord_children for odd root".to_string(),
                    )
                })?;

                let mut re_randomized_children = Vec::with_capacity(num_paths);
                let mut odd_node_comms = Vec::with_capacity(num_paths);
                for path in paths {
                    let child = *path.path.even_commitments.get(0).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing root child in even_commitments for odd root".to_string(),
                        )
                    })?;
                    let root_divisor_comms = path.odd_divisor_comms.first().ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing root divisor commitments for odd side".to_string(),
                        )
                    })?;
                    re_randomized_children.push(child);
                    odd_node_comms.push(root_divisor_comms);
                }

                SelectAndRerandomizePathWithDivisorComms::<L, P1, P0>::process_root_for_all::<
                    Parameters1,
                >(
                    odd_verifier,
                    re_randomized_children,
                    all_x_coords,
                    delta,
                    &mut odd_node_divisors,
                    &odd_node_comms,
                )?;
                false
            }
        };

        for path_idx in 0..num_paths {
            let path = &paths[path_idx];
            let path_even_comms = &path.even_divisor_comms;
            let path_odd_comms = &path.odd_divisor_comms;

            if even_node_divisors.len() <= path_idx {
                even_node_divisors.push(vec![]);
            }
            if odd_node_divisors.len() <= path_idx {
                odd_node_divisors.push(vec![]);
            }

            // Process even non-root nodes. Last item of path.path.even_commitments is the
            // leaf, which has no children.
            let even_non_root_len =
                path.path
                    .even_commitments
                    .len()
                    .checked_sub(1)
                    .ok_or_else(|| {
                        Error::MalformedProofInput(
                            "even_commitments must contain at least one element per path"
                                .to_string(),
                        )
                    })?;
            let even_items = Self::verify_non_root_levels_on_curve::<Parameters0>(
                even_verifier,
                root_is_even,
                even_non_root_len,
                &path.path.even_commitments,
                &path.path.odd_commitments,
                path_even_comms,
                &odd_parameters.sl_params.delta,
            )?;
            even_node_divisors[path_idx].extend(even_items);

            // Process odd non-root nodes
            let odd_len = path.path.odd_commitments.len();
            let odd_items =
                SelectAndRerandomizePathWithDivisorComms::<L, P1, P0>::verify_non_root_levels_on_curve::<
                    Parameters1,
                >(
                    odd_verifier,
                    !root_is_even,
                    odd_len,
                    &path.path.odd_commitments,
                    &path.path.even_commitments,
                    path_odd_comms,
                    &even_parameters.sl_params.delta,
                )?;
            odd_node_divisors[path_idx].extend(odd_items);
        }

        constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_verifier,
            odd_verifier,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors.into_iter().flatten(),
            odd_node_divisors.into_iter().flatten(),
        )?;
        Ok(())
    }

    fn process_root_for_all<Parameters: DiscreteLogParameters>(
        verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        re_randomized_children: Vec<Affine<P1>>,
        all_x_coords: &[F0],
        delta: Affine<P1>,
        node_divisors: &mut Vec<
            Vec<(
                LinearCombination<F0>,
                LinearCombination<F0>,
                F0,
                F0,
                Box<PointWithDlog<F0, Parameters>>,
            )>,
        >,
        node_comms: &[&DivisorComms<Affine<P0>>],
    ) -> Result<()> {
        let num_paths = re_randomized_children.len();
        if node_comms.len() != num_paths {
            return Err(Error::MismatchedSize(node_comms.len(), num_paths));
        }

        // Allocate x-coordinates for all selected children
        let mut x_vars: Vec<LinearCombination<F0>> = Vec::with_capacity(num_paths);
        for _ in 0..num_paths {
            x_vars.push(verifier.allocate(None)?.into());
        }

        // Enforce multi-select on public set
        multi_select_public_set(verifier, x_vars.clone(), all_x_coords)?;

        // For each path, process its selected child of root
        for (path_idx, (x_var, rerandomized_child)) in x_vars
            .into_iter()
            .zip(re_randomized_children.into_iter())
            .enumerate()
        {
            // Add rerandomized child to transcript
            verifier
                .transcript()
                .append(b"rerandomized_child", &rerandomized_child);

            let y_var = verifier.allocate(None)?.into();
            let (x, y) = (rerandomized_child + delta)
                .into_affine()
                .xy()
                .ok_or(Error::PointCantBeZero)?;

            let path_divisor_comms = *node_comms.get(path_idx).ok_or_else(|| {
                Error::MalformedProofInput(
                    "missing root divisor commitments for a path".to_string(),
                )
            })?;

            let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, path_divisor_comms)?;

            node_divisors.push(vec![(x_var, y_var, x, y, p)]);
        }

        Ok(())
    }

    /// Verify the root level of a single path. The root's child
    /// lives on the other parity, so it is selected from the root's public x-coords
    fn verify_root<Parameters: DiscreteLogParameters>(
        verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        delta: &Affine<P1>,
        root_x_coords: &[[F0; L]],
        child_commitments: &[Affine<P1>],
        divisor_comms: &[DivisorComms<Affine<P0>>],
    ) -> Result<DlogItem<F0, Parameters>> {
        let child = child_commitments.first().ok_or_else(|| {
            Error::MalformedProofInput("missing root child commitment".to_string())
        })?;
        let all_x_coords = root_x_coords.first().ok_or_else(|| {
            Error::MalformedProofInput("missing root x-coordinates of children".to_string())
        })?;
        let (x_var, y_var, x, y) = select_root(verifier, delta, child, all_x_coords, None)?;
        let divisor = divisor_comms.first().ok_or_else(|| {
            Error::MalformedProofInput("missing root divisor commitment".to_string())
        })?;
        let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, divisor)?;
        Ok((x_var.into(), y_var.into(), x, y, p))
    }

    /// Verify the non-root levels of a single path, returning per-level dlog items. `skip_root` is
    /// true when the root lives on this parity (even/odd). `num_parent_levels` excludes the leaf on the even level.
    pub(crate) fn verify_non_root_levels_on_curve<Parameters: DiscreteLogParameters>(
        verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        skip_root: bool,
        num_parent_levels: usize,
        parent_commitments: &[Affine<P0>],
        child_commitments: &[Affine<P1>],
        divisor_comms_list: &[DivisorComms<Affine<P0>>],
        delta: &Affine<P1>,
    ) -> Result<Vec<DlogItem<F0, Parameters>>> {
        let mut items = Vec::with_capacity(num_parent_levels);
        for parent_index in 0..num_parent_levels {
            // If the root is on this level, its child is the first commitment on the other
            // level and has already been processed during root handling.
            let child_index = if skip_root {
                parent_index + 1
            } else {
                parent_index
            };

            let child = child_commitments.get(child_index).ok_or_else(|| {
                Error::MalformedProofInput(format!(
                    "child commitments shorter than required for traversal (index {child_index}, len {})",
                    child_commitments.len()
                ))
            })?;
            let parent_commitment = parent_commitments.get(parent_index).ok_or_else(|| {
                Error::MalformedProofInput(format!(
                    "parent commitments shorter than required for traversal (index {parent_index}, len {})",
                    parent_commitments.len()
                ))
            })?;
            let variables = verifier
                .commit_vec(L, *parent_commitment)
                .iter()
                .map(|v| LinearCombination::<F0>::from(*v))
                .collect();
            let (x_var, y_var, x, y) = select_non_root(verifier, delta, child, variables, None)?;
            let divisor_comms = divisor_comms_list.get(child_index).ok_or_else(|| {
                Error::MalformedProofInput(format!(
                    "divisor commitments shorter than required for traversal (index {child_index}, len {})",
                    divisor_comms_list.len()
                ))
            })?;
            let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, divisor_comms)?;
            items.push((x_var.into(), y_var.into(), x, y, p));
        }
        Ok(items)
    }
}

pub fn commit_dlog_and_divisor<
    F: PrimeField,
    C: AffineRepr<ScalarField = F>,
    Parameters: DiscreteLogParameters,
>(
    verifier: &mut Verifier<MerlinTranscript, C>,
    divisor_commitments: &DivisorComms<C>,
) -> Result<Box<PointWithDlog<F, Parameters>>> {
    commit_witness_chunks_verifier(verifier, divisor_commitments).map_err(Into::into)
}
