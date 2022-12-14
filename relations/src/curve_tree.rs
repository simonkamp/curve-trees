use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use ark_ec::{
    models::short_weierstrass_jacobian::GroupAffine, AffineCurve, ProjectiveCurve,
    SWModelParameters,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::{UniformRand, Zero};
use merlin::Transcript;
use rand::Rng;
use std::borrow::BorrowMut;

pub enum CurveTree<const L: usize, P0: SWModelParameters, P1: SWModelParameters> {
    Even(CurveTreeNode<L, P0, P1>),
    Odd(CurveTreeNode<L, P1, P0>),
}

impl<
        const L: usize,
        P0: SWModelParameters + Clone + Send,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone + Send,
    > CurveTree<L, P0, P1>
{
    /// Build a curve tree from a set of commitments assumed to be permissible
    pub fn from_set(
        set: &[GroupAffine<P0>],
        parameters: &SelRerandParameters<P0, P1>,
        height: Option<usize>, // resulting curve tree will have height at least `height`
    ) -> Self {
        if set.is_empty() {
            panic!("The curve tree must have at least one leaf.")
        }
        // Convert each commitment to a leaf.
        let mut forest_length = set.len();
        let mut next_forest_length = (forest_length + L - 1) / L;
        let mut even_forest = Vec::with_capacity(forest_length);
        for leaf in set {
            even_forest.push(CurveTreeNode::<L, P0, P1>::leaf(*leaf));
        }
        while forest_length > 1 {
            // Combine forest of trees with even roots, into a forest of trees with odd roots.
            let mut odd_forest = Vec::with_capacity(next_forest_length);
            for i in 0..next_forest_length {
                let mut chunk = Vec::new();
                for j in i * L..(i + 1) * L {
                    if j >= forest_length {
                        break;
                    }
                    chunk.push(even_forest[j].clone());
                }
                odd_forest.push(CurveTreeNode::<L, P1, P0>::combine(
                    chunk,
                    &parameters.odd_parameters,
                ));
            }
            forest_length = next_forest_length;
            next_forest_length = (next_forest_length + L - 1) / L;

            if forest_length == 1 {
                return Self::Odd(odd_forest[0].clone()).increase_height(height, parameters);
            }

            // Combine forest of trees with odd roots, into a forest of trees with even roots.
            even_forest = Vec::with_capacity(next_forest_length);
            for i in 0..next_forest_length {
                let mut chunk = Vec::new();
                for j in i * L..(i + 1) * L {
                    if j >= forest_length {
                        break;
                    }
                    chunk.push(odd_forest[j].clone());
                }
                even_forest.push(CurveTreeNode::<L, P0, P1>::combine(
                    chunk,
                    &parameters.even_parameters,
                ));
            }
            forest_length = next_forest_length;
            next_forest_length = (next_forest_length + L - 1) / L;
        }
        Self::Even(even_forest[0].clone()).increase_height(height, parameters)
    }

    pub fn increase_height(
        self,
        height: Option<usize>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Self {
        match height {
            None => self,
            Some(height) => {
                let mut res = self;
                while res.height() < height {
                    match res {
                        Self::Even(ct) => {
                            res = Self::Odd(CurveTreeNode::<L, P1, P0>::combine(
                                vec![ct],
                                &parameters.odd_parameters,
                            ));
                        }
                        Self::Odd(ct) => {
                            res = Self::Even(CurveTreeNode::<L, P0, P1>::combine(
                                vec![ct],
                                &parameters.even_parameters,
                            ));
                        }
                    }
                }
                res
            }
        }
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected??leaf and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget(
        &self,
        index: usize,
        even_prover: &mut Prover<Transcript, GroupAffine<P0>>,
        odd_prover: &mut Prover<Transcript, GroupAffine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> (SelectAndRerandomizePath<P0, P1>, P0::ScalarField) {
        let mut rng = rand::thread_rng();

        let mut even_commitments = Vec::new();
        let mut odd_commitments = Vec::new();
        let (mut even_internal_node, mut rerandomization_scalar) = match self {
            Self::Odd(ct) => ct.single_level_select_and_rerandomize_prover_gadget(
                index,
                odd_prover,
                &mut even_commitments,
                &parameters.odd_parameters,
                &parameters.even_parameters,
                P1::ScalarField::zero(),
                &mut rng,
            ),
            Self::Even(ct) => (ct, P0::ScalarField::zero()),
        };
        // While the current node is internal, do two iterations of the proof.
        while even_internal_node.children.is_some() {
            // Do two iterations of the proof and advance `even_internal_node`to a grandchild.
            let (child, child_rerandomization_scalar) = even_internal_node
                .single_level_select_and_rerandomize_prover_gadget(
                    index,
                    even_prover,
                    &mut odd_commitments,
                    &parameters.even_parameters,
                    &parameters.odd_parameters,
                    rerandomization_scalar,
                    &mut rng,
                );

            // Assumes the leaf layer is even. Todo make this part of the type
            (even_internal_node, rerandomization_scalar) = child
                .single_level_select_and_rerandomize_prover_gadget(
                    index,
                    odd_prover,
                    &mut even_commitments,
                    &parameters.odd_parameters,
                    &parameters.even_parameters,
                    child_rerandomization_scalar,
                    &mut rng,
                );
        }

        // return the commitments and the rerandomization scalar of the leaf.
        (
            SelectAndRerandomizePath {
                even_commitments,
                odd_commitments,
            },
            rerandomization_scalar,
        )
    }

    pub fn select_and_rerandomize_verification_commitments(
        &self,
        mut randomized_path: SelectAndRerandomizePath<P0, P1>,
    ) -> SRVerificationCommitments<P0, P1> {
        let (even_commitments, odd_commitments) = match self {
            // todo we are committing to public values in the first iteration.
            // could allocate variables for each entry instead of using the vector commitment machinery needed for the next levels
            Self::Odd(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len() + 1
                );
                let mut odd_commitments_with_root = vec![ct.commitment];
                odd_commitments_with_root.append(&mut randomized_path.odd_commitments);
                (randomized_path.even_commitments, odd_commitments_with_root)
            }
            Self::Even(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len()
                );
                let mut even_commitments_with_root = vec![ct.commitment];
                even_commitments_with_root.append(&mut randomized_path.even_commitments);
                (even_commitments_with_root, randomized_path.odd_commitments)
            }
        };

        SRVerificationCommitments {
            leaf: even_commitments[even_commitments.len() - 1],
            even_commitments,
            odd_commitments,
            branching_factor: L,
        }
    }

    pub fn select_and_rerandomize_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, GroupAffine<P0>>,
        odd_verifier: &mut Verifier<T, GroupAffine<P1>>,
        randomized_path: SelectAndRerandomizePath<P0, P1>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> GroupAffine<P0> {
        let commitments = self.select_and_rerandomize_verification_commitments(randomized_path);

        commitments.even_verifier_gadget(even_verifier, parameters);
        commitments.odd_verifier_gadget(odd_verifier, parameters);

        commitments.leaf
    }

    pub fn height(&self) -> usize {
        match self {
            Self::Even(ct) => ct.height,
            Self::Odd(ct) => ct.height,
        }
    }

    //todo add a function to add a single/several commitments
}

pub struct SRVerificationCommitments<P0: SWModelParameters, P1: SWModelParameters> {
    pub even_commitments: Vec<GroupAffine<P0>>,
    pub odd_commitments: Vec<GroupAffine<P1>>,
    pub leaf: GroupAffine<P0>,
    pub branching_factor: usize,
}

impl<
        P0: SWModelParameters + Clone + Send,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone + Send,
    > SRVerificationCommitments<P0, P1>
{
    pub fn even_verifier_gadget<T: BorrowMut<Transcript>>(
        &self,
        even_verifier: &mut Verifier<T, GroupAffine<P0>>,
        parameters: &SelRerandParameters<P0, P1>,
    ) {
        // The last even commitment is a leaf.
        for i in 0..self.even_commitments.len() - 1 {
            let odd_index = if self.even_commitments.len() == self.odd_commitments.len() {
                i + 1
            } else {
                i
            };
            let variables =
                even_verifier.commit_vec(self.branching_factor, self.even_commitments[i]);
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
        odd_verifier: &mut Verifier<T, GroupAffine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
    ) {
        for i in 0..self.odd_commitments.len() {
            let even_index = if self.even_commitments.len() == self.odd_commitments.len() {
                i
            } else {
                i + 1
            };
            let variables = odd_verifier.commit_vec(self.branching_factor, self.odd_commitments[i]);
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

#[derive(Clone)]
pub struct SelectAndRerandomizePath<P0: SWModelParameters, P1: SWModelParameters> {
    pub even_commitments: Vec<GroupAffine<P0>>,
    pub odd_commitments: Vec<GroupAffine<P1>>,
}

impl<P0: SWModelParameters, P1: SWModelParameters> CanonicalSerialize
    for SelectAndRerandomizePath<P0, P1>
{
    fn serialized_size(&self) -> usize {
        self.even_commitments.serialized_size() + self.odd_commitments.serialized_size()
    }

    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        self.even_commitments.serialize(&mut writer)?;
        self.odd_commitments.serialize(&mut writer)?;
        Ok(())
    }
}

impl<P0: SWModelParameters, P1: SWModelParameters> CanonicalDeserialize
    for SelectAndRerandomizePath<P0, P1>
{
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        Ok(Self {
            even_commitments: Vec::<GroupAffine<P0>>::deserialize(&mut reader)?,
            odd_commitments: Vec::<GroupAffine<P1>>::deserialize(&mut reader)?,
        })
    }
}

#[derive(Clone)]
pub struct CurveTreeNode<const L: usize, P0: SWModelParameters, P1: SWModelParameters> {
    commitment: GroupAffine<P0>,
    randomness: <GroupAffine<P0> as AffineCurve>::ScalarField,
    children: Option<Box<[Option<CurveTreeNode<L, P1, P0>>; L]>>,
    height: usize,
    elements: usize,
}

impl<const L: usize, P0: SWModelParameters, P1: SWModelParameters> std::fmt::Debug
    for CurveTreeNode<L, P0, P1>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "")
    }
}

impl<
        const L: usize,
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    > CurveTreeNode<L, P0, P1>
{
    // The commitment is assumed to be permissible
    pub fn leaf(commitment: GroupAffine<P0>) -> Self {
        Self {
            commitment,
            randomness: P0::ScalarField::zero(),
            children: None,
            height: 0,
            elements: 1,
        }
    }

    pub fn capacity(&self) -> usize {
        L.pow(self.height as u32)
    }

    pub fn child_index(&self, index: usize) -> usize {
        let capacity = L.pow(self.height as u32);
        let child_capacity = L.pow((self.height - 1) as u32);
        (index % capacity) / child_capacity
    }

    pub fn single_level_select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        index: usize,
        prover: &mut Prover<Transcript, GroupAffine<P0>>,
        commitments: &mut Vec<GroupAffine<P1>>,
        even_parameters: &SingleLayerParameters<P0>,
        odd_parameters: &SingleLayerParameters<P1>,
        rerandomization_scalar: P0::ScalarField,
        rng: &mut R,
    ) -> (&CurveTreeNode<L, P1, P0>, P1::ScalarField) {
        let child_rerandomization_scalar = P1::ScalarField::rand(rng);

        let (child, rerandomized_child, children_vars) = match &self.children {
            None => panic!("The node is assumed to be internal."),
            Some(children) => {
                let child = match &children[self.child_index(index)] {
                    None => panic!(
                        "Child index out of bounds. Height: {}, Index: {}",
                        self.height, index
                    ),
                    Some(child) => child,
                };
                let (_, children_vars) = prover.commit_vec(
                    children
                        .iter()
                        .map(|opt| match opt {
                            None => P0::ScalarField::zero(),
                            Some(child) => child.commitment.x,
                        })
                        .collect::<Vec<_>>()
                        .as_slice(),
                    self.randomness + rerandomization_scalar,
                    &even_parameters.bp_gens,
                );
                let child_commitment = child.commitment;
                let mut blinding_base = odd_parameters.pc_gens.B_blinding.into_projective();
                blinding_base *= child_rerandomization_scalar;
                let rerandomized_child = child_commitment + blinding_base.into_affine();
                commitments.push(rerandomized_child);
                (child, rerandomized_child, children_vars)
            }
        };

        single_level_select_and_rerandomize(
            prover,
            odd_parameters,
            &rerandomized_child,
            children_vars,
            Some(child.commitment),
            Some(child_rerandomization_scalar),
        );

        (child, child_rerandomization_scalar)
    }

    // Combine up to L nodes of level d into a single level d+1 node.
    // The children are assumed to be of appropriate identical height.
    // All but the last should be full.
    fn combine(
        children: Vec<CurveTreeNode<L, P1, P0>>,
        parameters: &SingleLayerParameters<P0>,
    ) -> Self {
        if children.len() > L {
            panic!(
                "Cannot combine more than the branching factor: {} into one node.",
                L
            )
        };

        let mut elements = 0;
        let mut cs: Vec<Option<CurveTreeNode<L, P1, P0>>> = Vec::with_capacity(L);
        for c in children {
            elements += c.elements;
            cs.push(Some(c));
        }
        // Let the rest of the children be dummy elements.
        while cs.len() < L {
            cs.push(None)
        }
        let children: [Option<CurveTreeNode<L, P1, P0>>; L] = cs.try_into().unwrap();
        let height = if let Some(c) = &children[0] {
            c.height + 1
        } else {
            1
        };
        // commit to the childrens x-coordinates with randomness zero, then increment randomness to find permissible point.
        let children_commitments = children
            .iter()
            .map(|c| {
                if let Some(c) = c {
                    c.commitment.x
                } else {
                    P1::BaseField::zero()
                }
            })
            .collect::<Vec<_>>();
        let (c, r) = parameters
            .permissible_commitment(children_commitments.as_slice(), P0::ScalarField::zero());

        Self {
            commitment: c,
            randomness: r,
            children: Some(Box::new(children)),
            height,
            elements,
        }
    }
}

pub struct SelRerandParameters<P0: SWModelParameters, P1: SWModelParameters> {
    pub even_parameters: SingleLayerParameters<P0>,
    pub odd_parameters: SingleLayerParameters<P1>,
}

impl<P0: SWModelParameters, P1: SWModelParameters> SelRerandParameters<P0, P1> {
    pub fn new<R: Rng>(
        even_generators_length: usize,
        odd_generators_length: usize,
        rng: &mut R,
    ) -> Self {
        SelRerandParameters {
            even_parameters: SingleLayerParameters::<P0>::new::<_, P1>(even_generators_length, rng),
            odd_parameters: SingleLayerParameters::<P1>::new::<_, P0>(odd_generators_length, rng),
        }
    }
}
