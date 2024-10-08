use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{
    x_coordinates, CurveTree, CurveTreeNode, SelRerandParameters, SelectAndRerandomizePath,
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
        mut randomized_path: SelectAndRerandomizePath<L, P0, P1>,
    ) -> SelectAndRerandomizePath<L, P0, P1> {
        let (even_commitments, odd_commitments) = match self {
            Self::Odd(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len() + 1
                );
                let mut odd_commitments_with_root = vec![ct.commitment(0)]; // todo index
                odd_commitments_with_root.append(&mut randomized_path.odd_commitments);
                (randomized_path.even_commitments, odd_commitments_with_root)
            }
            Self::Even(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len()
                );
                let mut even_commitments_with_root = vec![ct.commitment(0)]; // todo index
                even_commitments_with_root.append(&mut randomized_path.even_commitments);
                (even_commitments_with_root, randomized_path.odd_commitments)
            }
        };

        SelectAndRerandomizePath {
            even_commitments,
            odd_commitments,
        }
    }
}

// todo merge with above to support any batch size, maybe start implementing for M = 2
impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, 1, P0, P1>
{
    pub fn select_and_rerandomize_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        randomized_path: SelectAndRerandomizePath<L, P0, P1>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Affine<P0> {
        let commitments = self.select_and_rerandomize_verification_commitments(randomized_path);

        commitments.even_verifier_gadget(even_verifier, parameters, self);
        commitments.odd_verifier_gadget(odd_verifier, parameters, self);

        commitments.get_rerandomized_leaf()
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
        *self.even_commitments.last().unwrap()
    }

    pub fn even_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        parameters: &SelRerandParameters<P0, P1>,
        ct: &CurveTree<L, 1, P0, P1>,
    ) {
        // Determine the parity of the root:
        let root_is_odd = self.even_commitments.len() == self.odd_commitments.len();
        if !root_is_odd {
            assert!(self.even_commitments.len() == self.odd_commitments.len() + 1);
        }

        // The last even commitment is skipped as it is the leaf and as such not a parent in the select and rerandomize relation.
        for parent_index in 0..self.even_commitments.len() - 1 {
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
        ct: &CurveTree<L, 1, P0, P1>,
    ) {
        // Determine the parity of the root:
        let root_is_odd = self.even_commitments.len() == self.odd_commitments.len();
        if !root_is_odd {
            assert!(self.even_commitments.len() == self.odd_commitments.len() + 1);
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
            single_level_select_and_rerandomize(
                odd_verifier,
                &parameters.even_parameters,
                &self.even_commitments[even_index],
                variables,
                None,
                None,
            );
        }
    }
}
