use ark_ec::short_weierstrass::Projective;
use ark_ec::CurveGroup;
use bulletproofs::r1cs::*;

use crate::error::Error;
use crate::single_level_select_and_rerandomize::*;

use crate::batched_curve_tree_prover::RootChildrenCoordsVars;
use crate::curve_tree::{CurveTree, Root, RootNode, SelectAndRerandomizeMultiPath};
use crate::parameters::{SelRerandProofParameters, SingleLayerProofParameters};
use crate::select::multi_select_public_set_ext_challenge;
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::{PrimeField, Zero};
use ark_std::{string::ToString, vec, vec::Vec};
use core::borrow::BorrowMut;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    /// Adds the root to a randomized multi path provided by the prover
    pub fn batched_select_and_rerandomize_verification_commitments(
        &self,
        randomized_path: &mut SelectAndRerandomizeMultiPath<L, M, P0, P1>,
    ) -> Result<(), Error> {
        let num_indices = randomized_path.num_indices();
        if num_indices > M as u32 {
            return Err(Error::MoreIndicesThanSupportedBatchSize(
                num_indices,
                M as u32,
            ));
        }

        match self {
            Self::Odd(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len()
                );
                let mut sum_of_roots = Projective::<P1>::zero();
                for i in 0..num_indices {
                    sum_of_roots += ct.commitment(i as usize)
                }
                let mut odd_commitments_with_root = vec![sum_of_roots.into_affine()];
                odd_commitments_with_root.append(&mut randomized_path.odd_commitments);
                randomized_path.odd_commitments = odd_commitments_with_root;
            }
            Self::Even(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len() + 1,
                    randomized_path.odd_commitments.len()
                );
                let mut sum_of_roots = Projective::<P0>::zero();
                for i in 0..num_indices {
                    sum_of_roots += ct.commitment(i as usize)
                }
                let mut even_commitments_with_root = vec![sum_of_roots.into_affine()];
                even_commitments_with_root.append(&mut randomized_path.even_commitments);
                randomized_path.even_commitments = even_commitments_with_root;
            }
        };
        Ok(())
    }
}

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > SelectAndRerandomizeMultiPath<L, M, P0, P1>
{
    /// Get the public rerandomization of the selected commitments
    pub fn get_rerandomized_leaves(&self) -> Vec<Affine<P0>> {
        self.selected_commitments.clone()
    }

    pub fn batched_select_and_rerandomize_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root: &Root<L, M, P0, P1>,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        let num_indices = self.ensure_acceptable_num_indices()?;

        let root_is_even = match root {
            Root::Even(root) => {
                let mut children = Vec::with_capacity(L * num_indices as usize);
                for i in 0..num_indices {
                    children.extend_from_slice(root.x_coord_children[i as usize].as_slice());
                }
                root_level_batched_select_and_rerandomize(
                    even_verifier,
                    &parameters.odd_parameters,
                    num_indices,
                    &self.odd_commitments[0],
                    children,
                    None,
                    None,
                )?;
                true
            }
            Root::Odd(root) => {
                let mut children = Vec::with_capacity(L * num_indices as usize);
                for i in 0..num_indices {
                    children.extend_from_slice(root.x_coord_children[i as usize].as_slice());
                }
                root_level_batched_select_and_rerandomize(
                    odd_verifier,
                    &parameters.even_parameters,
                    num_indices,
                    &self.even_commitments[0],
                    children,
                    None,
                    None,
                )?;
                false
            }
        };

        self.process_non_root_nodes(even_verifier, odd_verifier, root_is_even, parameters)?;
        Ok(())
    }

    /// Verify multiple multi-paths with a common root
    pub fn batched_select_and_rerandomize_verifier_gadget_for_common_root<
        T: BorrowMut<MerlinTranscript>,
    >(
        paths: &[Self],
        root: &Root<L, M, P0, P1>,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        if paths.is_empty() {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }

        let is_root_even = root.is_even();
        let mut max_num_indices = paths[0].ensure_acceptable_num_indices()?;

        for path in paths {
            let this_root_is_even = path.root_is_even()?;
            if is_root_even {
                if !this_root_is_even {
                    return Err(Error::RootTypeMismatch {
                        expected: "even".to_string(),
                        got: "odd".to_string(),
                    });
                }
            } else {
                if this_root_is_even {
                    return Err(Error::RootTypeMismatch {
                        expected: "odd".to_string(),
                        got: "even".to_string(),
                    });
                }
            }
            let num_indices = path.ensure_acceptable_num_indices()?;
            if num_indices > max_num_indices {
                max_num_indices = num_indices;
            }
        }

        let mut selected_children_count_grp_by_root_index = vec![0; max_num_indices as usize];
        for path in paths {
            for root_index in 0..path.num_indices() as usize {
                selected_children_count_grp_by_root_index[root_index] += 1;
            }
        }
        let mut root_children_selected_coord_vars = match root {
            Root::Even(node) => {
                RootChildrenCoordsVars::Even(Self::process_root_nodes_for_given_multi_paths_with_common_root(node, max_num_indices, selected_children_count_grp_by_root_index, paths.len(), even_verifier)?)
            }
            Root::Odd(node) => {
                RootChildrenCoordsVars::Odd(SelectAndRerandomizeMultiPath::<L, M, P1, P0>::process_root_nodes_for_given_multi_paths_with_common_root(node, max_num_indices, selected_children_count_grp_by_root_index, paths.len(), odd_verifier)?)
            }
        };

        for path in paths {
            let num_indices = path.num_indices();

            root_children_selected_coord_vars.validate_and_re_randomize_children(
                None,
                even_verifier,
                odd_verifier,
                &path.even_commitments[0],
                &path.odd_commitments[0],
                None,
                None,
                num_indices,
                is_root_even,
                parameters,
            )?;

            path.process_non_root_nodes(even_verifier, odd_verifier, is_root_even, parameters)?;
        }

        Ok(())
    }

    fn process_root_nodes_for_given_multi_paths_with_common_root<T: BorrowMut<MerlinTranscript>>(
        root_node: &RootNode<L, M, P0, P1>,
        max_num_indices: u32,
        selected_children_count_grp_by_root_index: Vec<u32>,
        num_paths: usize,
        verifier: &mut Verifier<T, Affine<P0>>,
    ) -> Result<Vec<Vec<LinearCombination<P0::ScalarField>>>, Error> {
        let mut selected_children_of_root_xs = vec![vec![]; num_paths];
        for root_index in 0..max_num_indices as usize {
            let children_of_root = root_node.x_coord_children[root_index].as_slice();
            // Enforce set membership for the i-th root
            let xs = (0..selected_children_count_grp_by_root_index[root_index])
                .map(|_| verifier.allocate(None).unwrap().into())
                .collect::<Vec<_>>();
            let c = verifier
                .transcript()
                .challenge_scalar(b"challenge-for-multi_select");
            multi_select_public_set_ext_challenge(verifier, xs.clone(), children_of_root, c)?;
            for (j, x) in xs.into_iter().enumerate() {
                selected_children_of_root_xs[j].push(x);
            }
        }
        Ok(selected_children_of_root_xs)
    }

    pub fn process_non_root_nodes<T: BorrowMut<MerlinTranscript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        is_root_even: bool,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        let verify_even = |even_verifier: &mut Verifier<T, Affine<P0>>| {
            self.even_verifier_gadget(is_root_even, even_verifier, &parameters.odd_parameters)
        };

        let verify_odd = |odd_verifier: &mut Verifier<T, Affine<P1>>| {
            self.odd_verifier_gadget(is_root_even, odd_verifier, &parameters.even_parameters)
        };

        #[cfg(not(feature = "parallel"))]
        let res_even = verify_even(even_verifier);

        #[cfg(not(feature = "parallel"))]
        let res_odd = verify_odd(odd_verifier);

        #[cfg(feature = "parallel")]
        let (res_even, res_odd) =
            rayon::join(|| verify_even(even_verifier), || verify_odd(odd_verifier));

        res_even?;
        res_odd?;

        Ok(())
    }

    pub fn even_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root_is_even: bool,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_parameters: &SingleLayerProofParameters<P1>,
    ) -> Result<(), Error> {
        let num_indices = self.num_indices();
        for parent_index in 0..self.even_commitments.len() {
            // If the root is at even level, then the first element in self.odd_commitments will be child
            // of the root and its already processed in `root_level_select_and_rerandomize`
            let child_index = if root_is_even {
                parent_index + 1
            } else {
                parent_index
            };
            let variables = even_verifier
                .commit_vec(
                    L * num_indices as usize,
                    self.even_commitments[parent_index],
                )
                .into_iter()
                .map(|v| LinearCombination::<P0::ScalarField>::from(v))
                .collect();
            single_level_batched_select_and_rerandomize(
                even_verifier,
                odd_parameters,
                num_indices,
                &self.odd_commitments[child_index],
                variables,
                None,
                None,
            )?;
        }
        Ok(())
    }

    pub fn odd_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root_is_even: bool,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        even_parameters: &SingleLayerProofParameters<P0>,
    ) -> Result<(), Error> {
        let num_indices = self.num_indices();
        for parent_index in 0..self.odd_commitments.len() {
            // If the root is at odd level, then the first element in self.even_commitments will be child
            // of the root and its already processed in `root_level_select_and_rerandomize`
            let child_index = if !root_is_even {
                parent_index + 1
            } else {
                parent_index
            };
            let variables = odd_verifier
                .commit_vec(L * num_indices as usize, self.odd_commitments[parent_index])
                .into_iter()
                .map(|v| LinearCombination::<P1::ScalarField>::from(v))
                .collect();
            if parent_index < self.odd_commitments.len() - 1 {
                single_level_batched_select_and_rerandomize(
                    odd_verifier,
                    even_parameters,
                    num_indices,
                    &self.even_commitments[child_index],
                    variables,
                    None,
                    None,
                )?;
            } else {
                // Split the variables of the vector commitments into chunks corresponding to the `num_indices` parents.
                let chunks = variables.chunks_exact(variables.len() / num_indices as usize);
                for (i, chunk) in chunks.enumerate() {
                    single_level_select_and_rerandomize(
                        odd_verifier,
                        even_parameters,
                        &self.selected_commitments[i],
                        chunk.to_vec(),
                        None,
                        None,
                    )?;
                }
            }
        }
        Ok(())
    }

    /// Number of leaf indices for which this multi-path was created.
    pub fn num_indices(&self) -> u32 {
        self.selected_commitments.len() as u32
    }

    fn ensure_acceptable_num_indices(&self) -> Result<u32, Error> {
        let num_indices = self.num_indices();
        if num_indices as usize > M {
            Err(Error::MoreIndicesThanSupportedBatchSize(
                num_indices,
                M as u32,
            ))
        } else {
            Ok(num_indices)
        }
    }

    fn root_is_even(&self) -> Result<bool, Error> {
        if self.even_commitments.len() == self.odd_commitments.len() {
            Ok(false)
        } else if (self.even_commitments.len() + 1) == self.odd_commitments.len() {
            Ok(true)
        } else {
            Err(Error::InvalidRootTypeForPath)
        }
    }
}
