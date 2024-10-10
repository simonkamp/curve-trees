use ark_ec::short_weierstrass::Projective;
use ark_ec::CurveGroup;
use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{
    x_coordinates, CurveTree, CurveTreeNode, SelRerandParameters, SelectAndRerandomizeMultiPath,
};
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::{PrimeField, Zero};
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
                let mut sum_of_roots = Projective::<P1>::zero();
                for i in 0..M {
                    sum_of_roots = sum_of_roots + ct.commitment(i)
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
                for i in 0..M {
                    sum_of_roots = sum_of_roots + ct.commitment(i)
                }
                let mut even_commitments_with_root = vec![sum_of_roots.into_affine()];
                even_commitments_with_root.append(&mut randomized_path.even_commitments);
                randomized_path.even_commitments = even_commitments_with_root;
            }
        };
    }
}

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    pub fn batched_select_and_rerandomize_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, Affine<P0>>,
        odd_verifier: &mut Verifier<T, Affine<P1>>,
        mut randomized_path: SelectAndRerandomizeMultiPath<L, M, P0, P1>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> [Affine<P0>; M] {
        self.batched_select_and_rerandomize_verification_commitments(&mut randomized_path);
        // The even and odd commitments do not include the selected leaves, their sum should equal the height of the tree.
        debug_assert_eq!(
            self.height(),
            randomized_path.even_commitments.len() + randomized_path.odd_commitments.len()
        );

        randomized_path.even_verifier_gadget(even_verifier, parameters, self);
        randomized_path.odd_verifier_gadget(odd_verifier, parameters, self);

        randomized_path.get_rerandomized_leaves()
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
            let variables: Vec<LinearCombination<P0::ScalarField>> =
                if parent_index == 0 && !root_is_odd {
                    let children = match &ct {
                        CurveTree::Even(root) => {
                            // todo why not branch on this to determine if the root is even and if so extract the children, otherwise commit to get first set of vars
                            if let CurveTreeNode::Branch {
                                parent_commitment: _,
                                children,
                                height: _,
                                elements: _,
                            } = root
                            {
                                let mut children_xs = Vec::new();
                                for i in 0..M {
                                    children_xs.append(
                                        &mut x_coordinates(
                                            children,
                                            &parameters.odd_parameters.delta,
                                            i,
                                        )
                                        .to_vec(),
                                    )
                                }
                                println!("verifier used even root without committing");
                                children_xs
                            } else {
                                panic!()
                            }
                        }
                        _ => panic!(),
                    };
                    children.into_iter().map(constant).collect()
                } else {
                    println!("commit verifier even");
                    let variables =
                        even_verifier.commit_vec(L * M, self.even_commitments[parent_index]);
                    variables
                        .iter()
                        .map(|v| LinearCombination::<P0::ScalarField>::from(*v))
                        .collect()
                };
            assert_eq!(variables.len(), M * L);
            single_level_batched_select_and_rerandomize(
                even_verifier,
                &parameters.odd_parameters,
                &self.odd_commitments[odd_index],
                variables,
                None::<&[Affine<P1>; M]>,
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

            let variables: Vec<LinearCombination<P1::ScalarField>> = if parent_index == 0
                && root_is_odd
            {
                let children = match &ct {
                    CurveTree::Odd(root) => {
                        if let CurveTreeNode::Branch {
                            parent_commitment: _,
                            children,
                            height: _,
                            elements: _,
                        } = root
                        {
                            let mut children_xs = Vec::new();
                            for i in 0..M {
                                children_xs.append(
                                    &mut x_coordinates(
                                        children,
                                        &parameters.even_parameters.delta,
                                        i,
                                    )
                                    .to_vec(),
                                )
                            }
                            children_xs
                        } else {
                            panic!()
                        }
                    }
                    _ => panic!(),
                };
                // children.map(|c| constant(c)).to_vec()
                println!("verifier used odd root without committing");
                children.into_iter().map(constant).collect()
            } else {
                println!("commit verifier odd");
                let variables = odd_verifier.commit_vec(L * M, self.odd_commitments[parent_index]);
                variables
                    .iter()
                    .map(|v| LinearCombination::<P1::ScalarField>::from(*v))
                    .collect()
            };
            assert_eq!(variables.len(), M * L);

            if parent_index < self.odd_commitments.len() - 1 {
                println!("Odd verifier iteration {}", parent_index);
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
                // Split the variables of the vector commitments into chunks corresponding to the M parents.
                let chunks = variables.chunks_exact(variables.len() / M);
                for (i, chunk) in chunks.enumerate() {
                    // for i in 0..M {
                    single_level_select_and_rerandomize(
                        odd_verifier,
                        &parameters.even_parameters,
                        &self.selected_commitments[i],
                        chunk.to_vec(), // todo these are all the variables, should we not split them into chunks?
                        None,
                        None,
                    );
                    break;
                }
            };
        }
    }
}
