use crate::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use crate::error::{Error, Result};
use crate::parameters::SelRerandProofParametersRef;
use crate::prover::{constraints_for_dlogs, select_non_root, select_root, VC_LEN};
use crate::select::multi_select_public_set_ext_challenge;
use ark_dlog_gadget::dlog::{
    commit_witness_chunks_verifier, DiscreteLogParameters, DivisorComms, PointWithDlog,
};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_std::vec;
use ark_std::{boxed::Box, string::ToString, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Verifier};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};

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
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let mut even_node_divisors = vec![];
        let mut odd_node_divisors = vec![];

        let root_is_even = match root {
            Root::Even(root) => {
                let child = self.path.odd_commitments.get(0).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root child in odd_commitments for even root".to_string(),
                    )
                })?;
                let all_x_coords = root.x_coord_children.get(0).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root x_coord_children for even root".to_string(),
                    )
                })?;
                let (x_var, y_var, x, y) = select_root(
                    even_verifier,
                    &odd_parameters.sl_params.delta,
                    child,
                    all_x_coords,
                    None,
                )?;
                let p = commit_dlog_and_divisor::<_, _, Parameters0>(
                    even_verifier,
                    self.even_divisor_comms.get(0).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing root divisor commitments for even side".to_string(),
                        )
                    })?,
                )?;
                even_node_divisors.push((x_var.into(), y_var.into(), x, y, p));
                true
            }
            Root::Odd(root) => {
                let child = self.path.even_commitments.get(0).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root child in even_commitments for odd root".to_string(),
                    )
                })?;
                let all_x_coords = root.x_coord_children.get(0).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root x_coord_children for odd root".to_string(),
                    )
                })?;
                let (x_var, y_var, x, y) = select_root(
                    odd_verifier,
                    &even_parameters.sl_params.delta,
                    child,
                    all_x_coords,
                    None,
                )?;
                let p = commit_dlog_and_divisor::<_, _, Parameters1>(
                    odd_verifier,
                    self.odd_divisor_comms.get(0).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "missing root divisor commitments for odd side".to_string(),
                        )
                    })?,
                )?;
                odd_node_divisors.push((x_var.into(), y_var.into(), x, y, p));
                false
            }
        };

        let mut commit_even = || -> Result<()> {
            // Last item of self.path.even_commitments.len() is for leaf
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
            for parent_index in 0..even_non_root_len {
                // If the root is at even level, then the first element in self.path.odd_commitments will be child
                // of the root and its already processed in `root_level_select_and_rerandomize`
                let child_index = if root_is_even {
                    parent_index.checked_add(1).ok_or_else(|| {
                        Error::MalformedProofInput("child index overflow on even side".to_string())
                    })?
                } else {
                    parent_index
                };

                let child = self.path.odd_commitments.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "odd_commitments shorter than required for even-side traversal".to_string(),
                    )
                })?;
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
                let variables = even_verifier
                    .commit_vec(L, *parent_commitment)
                    .iter()
                    .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                    .collect();
                let (x_var, y_var, x, y) = select_non_root(
                    even_verifier,
                    &odd_parameters.sl_params.delta,
                    child,
                    variables,
                    None,
                )?;
                let divisor_comms = self.even_divisor_comms.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "even_divisor_comms shorter than required for even-side traversal"
                            .to_string(),
                    )
                })?;
                let p = commit_dlog_and_divisor::<_, _, Parameters0>(even_verifier, divisor_comms)?;
                even_node_divisors.push((x_var.into(), y_var.into(), x, y, p));
            }
            Ok(())
        };

        let mut commit_odd = || -> Result<()> {
            for parent_index in 0..self.path.odd_commitments.len() {
                // If the root is at odd level, then the first element in self.path.even_commitments will be child
                // of the root and its already processed in `root_level_select_and_rerandomize`
                let child_index = if !root_is_even {
                    parent_index.checked_add(1).ok_or_else(|| {
                        Error::MalformedProofInput("child index overflow on odd side".to_string())
                    })?
                } else {
                    parent_index
                };

                let child = self.path.even_commitments.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "even_commitments shorter than required for odd-side traversal".to_string(),
                    )
                })?;
                let parent_commitment =
                    self.path.odd_commitments.get(parent_index).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "odd_commitments shorter than required for odd-side traversal"
                                .to_string(),
                        )
                    })?;
                let variables = odd_verifier
                    .commit_vec(L, *parent_commitment)
                    .iter()
                    .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                    .collect();
                let (x_var, y_var, x, y) = select_non_root(
                    odd_verifier,
                    &even_parameters.sl_params.delta,
                    child,
                    variables,
                    None,
                )?;
                let divisor_comms = self.odd_divisor_comms.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "odd_divisor_comms shorter than required for odd-side traversal"
                            .to_string(),
                    )
                })?;
                let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, divisor_comms)?;
                odd_node_divisors.push((x_var.into(), y_var.into(), x, y, p));
            }
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
                    if path.even_divisor_comms.is_empty() {
                        return Err(Error::MalformedProofInput(
                            "missing root divisor commitments for even side".to_string(),
                        ));
                    }
                    re_randomized_children.push(child);
                    even_node_comms.push(path.even_divisor_comms.clone());
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
                    if path.odd_divisor_comms.is_empty() {
                        return Err(Error::MalformedProofInput(
                            "missing root divisor commitments for odd side".to_string(),
                        ));
                    }
                    re_randomized_children.push(child);
                    odd_node_comms.push(path.odd_divisor_comms.clone());
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

            // Process even non-root nodes
            // Last item of path.path.even_commitments is for leaf
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
            for parent_index in 0..even_non_root_len {
                let child_index = if root_is_even {
                    parent_index.checked_add(1).ok_or_else(|| {
                        Error::MalformedProofInput("child index overflow on even side".to_string())
                    })?
                } else {
                    parent_index
                };

                let child = path.path.odd_commitments.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "odd_commitments shorter than required for even-side traversal".to_string(),
                    )
                })?;
                let parent_commitment =
                    path.path
                        .even_commitments
                        .get(parent_index)
                        .ok_or_else(|| {
                            Error::MalformedProofInput(
                                "even_commitments shorter than required for even-side traversal"
                                    .to_string(),
                            )
                        })?;
                let variables: Vec<LinearCombination<F0>> = even_verifier
                    .commit_vec(L, *parent_commitment)
                    .iter()
                    .map(|v| (*v).into())
                    .collect();

                let (x_var, y_var, x, y) = select_non_root(
                    even_verifier,
                    &odd_parameters.sl_params.delta,
                    child,
                    variables,
                    None,
                )?;

                let divisor_comms = path_even_comms.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "even_divisor_comms shorter than required for even-side traversal"
                            .to_string(),
                    )
                })?;
                let p = commit_dlog_and_divisor::<_, _, Parameters0>(even_verifier, divisor_comms)?;
                even_node_divisors[path_idx].push((x_var.into(), y_var.into(), x, y, p));
            }

            // Process odd non-root nodes
            for parent_index in 0..path.path.odd_commitments.len() {
                let child_index = if !root_is_even {
                    parent_index.checked_add(1).ok_or_else(|| {
                        Error::MalformedProofInput("child index overflow on odd side".to_string())
                    })?
                } else {
                    parent_index
                };

                let child = path.path.even_commitments.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "even_commitments shorter than required for odd-side traversal".to_string(),
                    )
                })?;
                let parent_commitment =
                    path.path.odd_commitments.get(parent_index).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "odd_commitments shorter than required for odd-side traversal"
                                .to_string(),
                        )
                    })?;
                let variables: Vec<LinearCombination<F1>> = odd_verifier
                    .commit_vec(L, *parent_commitment)
                    .iter()
                    .map(|v| (*v).into())
                    .collect();

                let (x_var, y_var, x, y) = select_non_root(
                    odd_verifier,
                    &even_parameters.sl_params.delta,
                    child,
                    variables,
                    None,
                )?;

                let divisor_comms = path_odd_comms.get(child_index).ok_or_else(|| {
                    Error::MalformedProofInput(
                        "odd_divisor_comms shorter than required for odd-side traversal"
                            .to_string(),
                    )
                })?;
                let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, divisor_comms)?;
                odd_node_divisors[path_idx].push((x_var.into(), y_var.into(), x, y, p));
            }
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
        node_comms: &[Vec<DivisorComms<Affine<P0>>>],
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

        // Get challenge and enforce multi-select on public set
        let challenge = verifier
            .transcript()
            .challenge_scalar(b"challenge-for-multi_select");
        multi_select_public_set_ext_challenge(verifier, x_vars.clone(), all_x_coords, challenge)?;

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

            let path_divisor_comms = node_comms
                .get(path_idx)
                .and_then(|comms| comms.get(0))
                .ok_or_else(|| {
                    Error::MalformedProofInput(
                        "missing root divisor commitments for a path".to_string(),
                    )
                })?;

            let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, path_divisor_comms)?;

            node_divisors.push(vec![(x_var, y_var, x, y, p)]);
        }

        Ok(())
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
    commit_witness_chunks_verifier(verifier, divisor_commitments, VC_LEN as usize)
        .map_err(Into::into)
}
