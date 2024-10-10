use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{
    x_coordinates, CurveTree, CurveTreeNode, SelRerandParameters, SelectAndRerandomizeMultiPath,
    SelectAndRerandomizePath,
};
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::PrimeField;
use merlin::Transcript;
use std::borrow::BorrowMut;

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    // Adds the root to a randomized path provided by the prover
    pub fn select_and_rerandomize_verification_commitments(
        &self,
        randomized_path: &mut SelectAndRerandomizePath<L, P0, P1>,
    ) {
        match self {
            Self::Odd(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len()
                );
                let mut odd_commitments_with_root = vec![ct.commitment(0)]; // todo index
                odd_commitments_with_root.append(&mut randomized_path.odd_commitments);
                randomized_path.odd_commitments = odd_commitments_with_root;
            }
            Self::Even(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len() + 1,
                    randomized_path.odd_commitments.len()
                );
                let mut even_commitments_with_root = vec![ct.commitment(0)]; // todo index
                even_commitments_with_root.append(&mut randomized_path.even_commitments);
                randomized_path.even_commitments = even_commitments_with_root;
            }
        };
    }

    // Adds the root to a randomized multi path provided by the prover
    pub fn batched_select_and_rerandomize_verification_commitments(
        &self,
        randomized_path: &mut SelectAndRerandomizeMultiPath<L, M, P0, P1>,
    ) {
        match self {
            Self::Odd(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len()
                );
                let mut odd_commitments_with_root = vec![ct.commitment(0)]; // todo index
                odd_commitments_with_root.append(&mut randomized_path.odd_commitments);
                randomized_path.odd_commitments = odd_commitments_with_root;
            }
            Self::Even(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len() + 1,
                    randomized_path.odd_commitments.len()
                );
                let mut even_commitments_with_root = vec![ct.commitment(0)]; // todo index
                even_commitments_with_root.append(&mut randomized_path.even_commitments);
                randomized_path.even_commitments = even_commitments_with_root;
            }
        };
    }
}

// todo merge with above to support any batch size, maybe start implementing for M = 2
impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    pub fn select_and_rerandomize_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        mut randomized_path: SelectAndRerandomizePath<L, P0, P1>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Affine<P0> {
        self.select_and_rerandomize_verification_commitments(&mut randomized_path);

        randomized_path.even_verifier_gadget(even_verifier, parameters, self);
        randomized_path.odd_verifier_gadget(odd_verifier, parameters, self);

        randomized_path.get_rerandomized_leaf()
    }

    pub fn batched_select_and_rerandomize_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        mut randomized_path: SelectAndRerandomizeMultiPath<L, M, P0, P1>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> [Affine<P0>; M] {
        self.batched_select_and_rerandomize_verification_commitments(&mut randomized_path);

        randomized_path.even_verifier_gadget(even_verifier, parameters, self);
        randomized_path.odd_verifier_gadget(odd_verifier, parameters, self);

        randomized_path.get_rerandomized_leaves()
    }
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy + Send,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy + Send,
    > SelectAndRerandomizePath<L, P0, P1>
{
    /// Get the public rerandomization of the selected commitment
    pub fn get_rerandomized_leaf(&self) -> Affine<P0> {
        self.selected_commitment
    }

    pub fn even_verifier_gadget<const M: usize, T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, M, P0, P1>,
    ) {
        // Determine the parity of the root:
        let root_is_odd = self.even_commitments.len() + 1 == self.odd_commitments.len();
        if !root_is_odd {
            assert!(self.even_commitments.len() == self.odd_commitments.len());
        }

        for parent_index in 0..self.even_commitments.len() {
            let odd_index = if root_is_odd {
                parent_index + 1
            } else {
                parent_index
            };
            let variables = if parent_index == 0 && !root_is_odd {
                let children = match &ct {
                    CurveTree::Even(root) => {
                        if let CurveTreeNode::Branch {
                            parent_commitment: _,
                            children,
                            height: _,
                            elements: _,
                        } = root
                        {
                            x_coordinates(children, &parameters.odd_parameters.delta, 0)
                        } else {
                            panic!()
                        }
                    }
                    _ => panic!(),
                };
                children.map(constant).to_vec()
            } else {
                let variables = even_verifier.commit_vec(L, self.even_commitments[parent_index]);
                variables
                    .iter()
                    .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                    .collect()
            };
            single_level_select_and_rerandomize(
                even_verifier,
                &parameters.odd_parameters,
                &self.odd_commitments[odd_index],
                variables,
                None,
                None,
            );
        }
    }

    pub fn odd_verifier_gadget<const M: usize, T: BorrowMut<Transcript>>(
        &self,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, M, P0, P1>,
    ) {
        // Determine the parity of the root:
        let root_is_odd = self.even_commitments.len() + 1 == self.odd_commitments.len();
        if !root_is_odd {
            assert!(self.even_commitments.len() == self.odd_commitments.len());
        }
        for parent_index in 0..self.odd_commitments.len() {
            let even_index = if root_is_odd {
                parent_index
            } else {
                parent_index + 1
            };
            let child = if parent_index < self.odd_commitments.len() - 1 {
                self.even_commitments[even_index]
            } else {
                self.selected_commitment
            };
            let variables = if parent_index == 0 && root_is_odd {
                let children = match &ct {
                    CurveTree::Odd(root) => {
                        if let CurveTreeNode::Branch {
                            parent_commitment: _,
                            children,
                            height: _,
                            elements: _,
                        } = root
                        {
                            x_coordinates(children, &parameters.even_parameters.delta, 0)
                        } else {
                            panic!()
                        }
                    }
                    _ => panic!(),
                };
                children.map(|c| constant(c)).to_vec()
            } else {
                let variables = odd_verifier.commit_vec(L, self.odd_commitments[parent_index]);
                variables
                    .iter()
                    .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                    .collect()
            };
            single_level_select_and_rerandomize(
                odd_verifier,
                &parameters.even_parameters,
                &child,
                variables,
                None,
                None,
            );
        }
    }
}

impl<
        const L: usize,
        const M: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy + Send,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy + Send,
    > SelectAndRerandomizeMultiPath<L, M, P0, P1>
{
    /// Get the public rerandomization of the selected commitments
    pub fn get_rerandomized_leaves(&self) -> [Affine<P0>; M] {
        self.selected_commitments
    }

    pub fn even_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, M, P0, P1>,
    ) {
        // Determine the parity of the root:
        let root_is_odd = self.even_commitments.len() + 1 == self.odd_commitments.len();
        if !root_is_odd {
            assert!(self.even_commitments.len() == self.odd_commitments.len());
        }

        for parent_index in 0..self.even_commitments.len() {
            let odd_index = if root_is_odd {
                parent_index + 1
            } else {
                parent_index
            };
            let variables = if parent_index == 0 && !root_is_odd {
                let children = match &ct {
                    CurveTree::Even(root) => {
                        if let CurveTreeNode::Branch {
                            parent_commitment: _,
                            children,
                            height: _,
                            elements: _,
                        } = root
                        {
                            x_coordinates(children, &parameters.odd_parameters.delta, 0)
                        } else {
                            panic!()
                        }
                    }
                    _ => panic!(),
                };
                children.map(constant).to_vec()
            } else {
                let variables = even_verifier.commit_vec(L, self.even_commitments[parent_index]);
                variables
                    .iter()
                    .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                    .collect()
            };
            single_level_select_and_rerandomize(
                even_verifier,
                &parameters.odd_parameters,
                &self.odd_commitments[odd_index],
                variables,
                None,
                None,
            );
        }
    }

    pub fn odd_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, M, P0, P1>,
    ) {
        // Determine the parity of the root:
        let root_is_odd = self.even_commitments.len() + 1 == self.odd_commitments.len();
        if !root_is_odd {
            assert!(self.even_commitments.len() == self.odd_commitments.len());
        }
        for parent_index in 0..self.odd_commitments.len() {
            let even_index = if root_is_odd {
                parent_index
            } else {
                parent_index + 1
            };

            let variables = if parent_index == 0 && root_is_odd {
                let children = match &ct {
                    CurveTree::Odd(root) => {
                        if let CurveTreeNode::Branch {
                            parent_commitment: _,
                            children,
                            height: _,
                            elements: _,
                        } = root
                        {
                            x_coordinates(children, &parameters.even_parameters.delta, 0)
                        } else {
                            panic!()
                        }
                    }
                    _ => panic!(),
                };
                children.map(|c| constant(c)).to_vec()
            } else {
                let variables = odd_verifier.commit_vec(L, self.odd_commitments[parent_index]);
                variables
                    .iter()
                    .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                    .collect()
            };
            if parent_index < self.odd_commitments.len() - 1 {
                single_level_batched_select_and_rerandomize(
                    // todo batched
                    odd_verifier,
                    &parameters.even_parameters,
                    &self.even_commitments[even_index],
                    variables,
                    None::<&[Affine<P0>; M]>,
                    None,
                );
            } else {
                for i in 0..M {
                    // single_level_select_and_rerandomize(
                    //     odd_verifier,
                    //     &parameters.even_parameters,
                    //     &self.selected_commitments[i],
                    //     variables.clone(), // todo these are all the variables, should we not split them into chunks?
                    //     None,
                    //     None,
                    // );
                }
            };
        }
    }
}
