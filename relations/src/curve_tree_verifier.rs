use bulletproofs::r1cs::*;

use crate::curve_tree::{Root, SelectAndRerandomizePath};
use crate::curve_tree_prover::{
    allocate_children_of_root_and_enforce_membership, CurveTreeWitnessPath, RootChildrenCoordsVars,
};
use crate::error::Error;
use crate::parameters::{SelRerandProofParameters, SingleLayerProofParameters};
use crate::single_level_select_and_rerandomize::*;
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::PrimeField;
use core::borrow::BorrowMut;
use dock_crypto_utils::transcript::MerlinTranscript;

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > SelectAndRerandomizePath<L, P0, P1>
{
    pub fn select_and_rerandomize_verifier_gadget<T: BorrowMut<MerlinTranscript>>(
        &self,
        root: &Root<L, 1, P0, P1>,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        let root_is_even = match root {
            Root::Even(root) => {
                let child = &self.odd_commitments[0];
                root_level_select_and_rerandomize(
                    even_verifier,
                    &parameters.odd_parameters,
                    &child,
                    &root.x_coord_children[0],
                    None,
                    None,
                )?;
                true
            }
            Root::Odd(root) => {
                let child = &self.even_commitments[0];
                root_level_select_and_rerandomize(
                    odd_verifier,
                    &parameters.even_parameters,
                    &child,
                    &root.x_coord_children[0],
                    None,
                    None,
                )?;
                false
            }
        };

        self.process_non_root_nodes(even_verifier, odd_verifier, root_is_even, parameters)?;
        Ok(())
    }

    pub fn select_and_rerandomize_verifier_gadget_for_common_root<
        T: BorrowMut<MerlinTranscript>,
    >(
        paths: &[Self],
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        root: &Root<L, 1, P0, P1>,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        // First, process the root node as its common
        let root_children_coords = Self::process_root_nodes_for_given_paths_with_common_root(
            paths,
            even_verifier,
            odd_verifier,
            root,
        )?;

        // Then, process the non-root nodes
        Self::process_non_root_nodes_for_given_paths_with_common_root(
            paths,
            even_verifier,
            odd_verifier,
            parameters,
            root_children_coords,
            root,
        )?;
        Ok(())
    }

    /// Used after calling [`root_level_select_and_rerandomize`]
    pub fn even_verifier_gadget_for_non_root_nodes<T: BorrowMut<MerlinTranscript>>(
        &self,
        root_is_even: bool,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_parameters: &SingleLayerProofParameters<P1>,
    ) -> Result<(), Error> {
        // Last item of self.even_commitments.len() is for leaf
        for parent_index in 0..(self.even_commitments.len() - 1) {
            // If the root is at even level, then the first element in self.odd_commitments will be child
            // of the root and its already processed in `root_level_select_and_rerandomize`
            let child_index = if root_is_even {
                parent_index + 1
            } else {
                parent_index
            };

            let child = &self.odd_commitments[child_index];
            let variables = even_verifier
                .commit_vec(L, self.even_commitments[parent_index])
                .iter()
                .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                .collect();
            single_level_select_and_rerandomize(
                even_verifier,
                odd_parameters,
                child,
                variables,
                None,
                None,
            )?;
        }

        Ok(())
    }

    /// Used after calling [`root_level_select_and_rerandomize`]
    pub fn odd_verifier_gadget_for_non_root_nodes<T: BorrowMut<MerlinTranscript>>(
        &self,
        root_is_even: bool,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        even_parameters: &SingleLayerProofParameters<P0>,
    ) -> Result<(), Error> {
        for parent_index in 0..self.odd_commitments.len() {
            // If the root is at odd level, then the first element in self.even_commitments will be child
            // of the root and its already processed in `root_level_select_and_rerandomize`
            let child_index = if !root_is_even {
                parent_index + 1
            } else {
                parent_index
            };

            let child = self.even_commitments[child_index];
            let variables = odd_verifier
                .commit_vec(L, self.odd_commitments[parent_index])
                .iter()
                .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                .collect();
            single_level_select_and_rerandomize(
                odd_verifier,
                even_parameters,
                &child,
                variables,
                None,
                None,
            )?;
        }

        Ok(())
    }

    pub fn process_root_nodes_for_given_paths_with_common_root<T: BorrowMut<MerlinTranscript>>(
        paths: &[Self],
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        root: &Root<L, 1, P0, P1>,
    ) -> Result<RootChildrenCoordsVars<P0::ScalarField, P1::ScalarField>, Error> {
        match root {
            Root::Even(root_node) => {
                let x_coords_children = allocate_children_of_root_and_enforce_membership::<P1, _>(
                    even_verifier,
                    paths.len(),
                    None,
                    &root_node.x_coord_children[0],
                )?;

                Ok(RootChildrenCoordsVars::Even(x_coords_children))
            }
            Root::Odd(root_node) => {
                let x_coords_children = allocate_children_of_root_and_enforce_membership::<P0, _>(
                    odd_verifier,
                    paths.len(),
                    None,
                    &root_node.x_coord_children[0],
                )?;
                Ok(RootChildrenCoordsVars::Odd(x_coords_children))
            }
        }
    }

    pub fn process_non_root_nodes_for_given_paths_with_common_root<
        T: BorrowMut<MerlinTranscript>,
    >(
        paths: &[Self],
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandProofParameters<P0, P1>,
        mut root_children_coords: RootChildrenCoordsVars<P0::ScalarField, P1::ScalarField>,
        root: &Root<L, 1, P0, P1>,
    ) -> Result<(), Error> {
        if paths.is_empty() {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }
        let is_root_even = root.is_even();

        for path in paths {
            root_children_coords.validate_and_re_randomize_child(
                even_verifier,
                odd_verifier,
                &path.even_commitments[0],
                &path.odd_commitments[0],
                None::<&CurveTreeWitnessPath<L, P0, P1>>,
                None,
                None,
                is_root_even,
                parameters,
            )?;

            // Process non-root nodes
            path.process_non_root_nodes(even_verifier, odd_verifier, is_root_even, parameters)?;
        }

        Ok(())
    }

    pub fn process_non_root_nodes<T: BorrowMut<MerlinTranscript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        root_is_even: bool,
        parameters: &SelRerandProofParameters<P0, P1>,
    ) -> Result<(), Error> {
        let verify_even = |even_verifier: &mut Verifier<T, Affine<P0>>| {
            self.even_verifier_gadget_for_non_root_nodes(
                root_is_even,
                even_verifier,
                &parameters.odd_parameters,
            )
        };

        let verify_odd = |odd_verifier: &mut Verifier<T, Affine<P1>>| {
            self.odd_verifier_gadget_for_non_root_nodes(
                root_is_even,
                odd_verifier,
                &parameters.even_parameters,
            )
        };

        #[cfg(not(feature = "parallel"))]
        let even_res = verify_even(even_verifier);

        #[cfg(not(feature = "parallel"))]
        let odd_res = verify_odd(odd_verifier);

        #[cfg(feature = "parallel")]
        let (even_res, odd_res) =
            rayon::join(|| verify_even(even_verifier), || verify_odd(odd_verifier));

        even_res?;
        odd_res?;

        Ok(())
    }

    /// Get the public rerandomization of the selected (leaf) commitment
    pub fn get_rerandomized_leaf(&self) -> Affine<P0> {
        self.even_commitments.last().unwrap().clone()
    }
}
