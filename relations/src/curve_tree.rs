use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Valid, Write,
};
use ark_std::Zero;
use merlin::Transcript;
use rand::Rng;
use std::{borrow::BorrowMut, ops::Mul};

pub enum CurveTree<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    Even(CurveTreeNode<L, P0, P1>),
    Odd(CurveTreeNode<L, P1, P0>),
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, P0, P1>
{
    /// Build a curve tree from a set of commitments assumed to be permissible
    pub fn from_set(
        set: &[Affine<P0>],
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
                for (j, tree) in even_forest.iter().enumerate().take((i + 1) * L).skip(i * L) {
                    if j >= forest_length {
                        break;
                    }
                    chunk.push(tree.clone());
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
                for (j, tree) in odd_forest.iter().enumerate().take((i + 1) * L).skip(i * L) {
                    if j >= forest_length {
                        break;
                    }
                    chunk.push(tree.clone());
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

    /// Produce a witness of the path to the commitment at `index` including siblings and randomness.
    pub fn select_and_rerandomize_prover_witness(
        &self,
        index: usize,
    ) -> CurveTreeWitnessPath<L, P0, P1> {
        // todo capacity
        let mut even_nodes: Vec<CurveTreeWitness<L, P0, P1>> = Vec::new();
        let mut odd_nodes: Vec<CurveTreeWitness<L, P1, P0>> = Vec::new();

        match self {
            Self::Even(ct) => {
                ct.select_and_rerandomize_prover_witness(index, &mut even_nodes, &mut odd_nodes)
            }
            Self::Odd(ct) => {
                ct.select_and_rerandomize_prover_witness(index, &mut odd_nodes, &mut even_nodes)
            }
        }

        CurveTreeWitnessPath {
            even_nodes,
            odd_nodes,
        }
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        index: usize,
        even_prover: &mut Prover<Transcript, Affine<P0>>,
        odd_prover: &mut Prover<Transcript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField) {
        let witness = self.select_and_rerandomize_prover_witness(index);
        witness.select_and_rerandomize_prover_gadget(even_prover, odd_prover, parameters, rng)
    }

    pub fn select_and_rerandomize_verification_commitments(
        &self,
        mut randomized_path: SelectAndRerandomizePath<L, P0, P1>,
    ) -> SelectAndRerandomizePath<L, P0, P1> {
        let (even_commitments, odd_commitments) = match self {
            // todo we are committing to public values in the first iteration.
            // could allocate variables for each entry instead of using the vector commitment machinery needed for the next levels
            Self::Odd(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len() + 1
                );
                let mut odd_commitments_with_root = vec![ct.parent_commitment];
                odd_commitments_with_root.append(&mut randomized_path.odd_commitments);
                (randomized_path.even_commitments, odd_commitments_with_root)
            }
            Self::Even(ct) => {
                assert_eq!(
                    randomized_path.even_commitments.len(),
                    randomized_path.odd_commitments.len()
                );
                let mut even_commitments_with_root = vec![ct.parent_commitment];
                even_commitments_with_root.append(&mut randomized_path.even_commitments);
                (even_commitments_with_root, randomized_path.odd_commitments)
            }
        };

        SelectAndRerandomizePath {
            even_commitments,
            odd_commitments,
        }
    }

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

    pub fn height(&self) -> usize {
        match self {
            Self::Even(ct) => ct.height,
            Self::Odd(ct) => ct.height,
        }
    }

    //todo add a function to add a single/several commitments
}

// todo don't include the root
#[derive(Clone)]
pub struct SelectAndRerandomizePath<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    pub even_commitments: Vec<Affine<P0>>,
    pub odd_commitments: Vec<Affine<P1>>,
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
        ct: &CurveTree<L, P0, P1>,
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
                        if let Some(children) = &root.children {
                            x_coordinates(children)
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
        ct: &CurveTree<L, P0, P1>,
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
                        if let Some(children) = &root.children {
                            x_coordinates(children)
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

impl<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> CanonicalSerialize
    for SelectAndRerandomizePath<L, P0, P1>
{
    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.even_commitments.serialized_size(compress)
            + self.odd_commitments.serialized_size(compress)
    }

    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), SerializationError> {
        self.even_commitments
            .serialize_with_mode(&mut writer, compress)?;
        self.odd_commitments
            .serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }
}

impl<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> Valid
    for SelectAndRerandomizePath<L, P0, P1>
{
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}
impl<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> CanonicalDeserialize
    for SelectAndRerandomizePath<L, P0, P1>
{
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, SerializationError> {
        Ok(Self {
            even_commitments: Vec::<Affine<P0>>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            odd_commitments: Vec::<Affine<P1>>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
        })
    }
}

/// A witness of a Curve Tree path including siblings of randomness.
/// Contains all the information needed to prove the select and rerandomize relation.
#[derive(Clone)]
pub struct CurveTreeWitnessPath<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
{
    // list of internal even nodes
    pub even_nodes: Vec<CurveTreeWitness<L, P0, P1>>,
    // list of internal odd nodes
    pub odd_nodes: Vec<CurveTreeWitness<L, P1, P0>>,
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessPath<L, P0, P1>
{
    fn root_is_even(&self) -> bool {
        if self.even_nodes.len() == self.odd_nodes.len() {
            return true;
        }
        if self.even_nodes.len() + 1 == self.odd_nodes.len() {
            return false;
        }
        panic!("Invalid witness path");
    }
    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf
    /// and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        even_prover: &mut Prover<Transcript, Affine<P0>>,
        odd_prover: &mut Prover<Transcript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField) {
        // for each even internal node, there must be a rerandomization of a commitment in the odd curve
        let even_length = self.even_nodes.len();
        let mut odd_rerandomization_scalars: Vec<P1::ScalarField> = Vec::with_capacity(even_length);
        let mut odd_rerandomized_commitments: Vec<Affine<P1>> = Vec::with_capacity(even_length);
        // and vice versa
        let odd_length = self.odd_nodes.len();
        let mut even_rerandomization_scalars: Vec<P0::ScalarField> = Vec::with_capacity(odd_length);
        let mut even_rerandomized_commitments: Vec<Affine<P0>> = Vec::with_capacity(odd_length);

        for even in &self.even_nodes {
            let rerandomization = F1::rand(rng);
            odd_rerandomization_scalars.push(rerandomization);
            let blinding = parameters
                .odd_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            odd_rerandomized_commitments.push((even.child_witness + blinding).into());
        }

        for odd in &self.odd_nodes {
            let rerandomization = F0::rand(rng);
            even_rerandomization_scalars.push(rerandomization);
            let blinding = parameters
                .even_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            even_rerandomized_commitments.push((odd.child_witness + blinding).into());
        }

        let prove_even = |prover: &mut Prover<Transcript, Affine<P0>>| {
            for i in 0..even_length {
                let parent_rerandomization = if self.root_is_even() {
                    if i == 0 {
                        // the parent is the the root and thus not rerandomized
                        F0::zero()
                    } else {
                        even_rerandomization_scalars[i - 1]
                    }
                } else {
                    even_rerandomization_scalars[i]
                };
                self.even_nodes[i].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.even_parameters,
                    &parameters.odd_parameters,
                    parent_rerandomization,
                    odd_rerandomization_scalars[i],
                );
            }
        };
        #[cfg(not(feature = "parallel"))]
        prove_even(even_prover);
        let prove_odd = |prover: &mut Prover<Transcript, Affine<P1>>| {
            for i in 0..odd_length {
                let parent_rerandomization = if !self.root_is_even() {
                    if i == 0 {
                        // the parent is the the root and thus not rerandomized
                        F1::zero()
                    } else {
                        odd_rerandomization_scalars[i - 1]
                    }
                } else {
                    odd_rerandomization_scalars[i]
                };
                self.odd_nodes[i].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.odd_parameters,
                    &parameters.even_parameters,
                    parent_rerandomization,
                    even_rerandomization_scalars[i],
                );
            }
        };
        #[cfg(not(feature = "parallel"))]
        prove_odd(odd_prover);

        #[cfg(feature = "parallel")]
        rayon::join(|| prove_even(even_prover), || prove_odd(odd_prover));

        (
            SelectAndRerandomizePath {
                even_commitments: even_rerandomized_commitments,
                odd_commitments: odd_rerandomized_commitments,
            },
            *even_rerandomization_scalars.last().unwrap(),
        )
    }
}

/// A witness of a Curve Tree path including siblings of randomness.
/// Contains the information needed to prove the single level select and rerandomize relation.
#[derive(Copy, Clone)]
pub struct CurveTreeWitness<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    randomness: P0::ScalarField,
    siblings: [P0::ScalarField; L],
    child_witness: Affine<P1>,
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > CurveTreeWitness<L, P0, P1>
{
    pub fn single_level_select_and_rerandomize_prover_gadget(
        &self,
        prover: &mut Prover<Transcript, Affine<P0>>,
        even_parameters: &SingleLayerParameters<P0>,
        odd_parameters: &SingleLayerParameters<P1>,
        parent_rerandomization_scalar: P0::ScalarField,
        child_rerandomization_scalar: P1::ScalarField,
    ) {
        let children_vars = if parent_rerandomization_scalar.is_zero() {
            self.siblings.map(constant).to_vec()
        } else {
            let (_, children_vars) = prover.commit_vec(
                &self.siblings,
                self.randomness + parent_rerandomization_scalar,
                &even_parameters.bp_gens,
            );
            children_vars
                .iter()
                .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
                .collect()
        };
        let child_commitment = self.child_witness;
        let blinding = odd_parameters.pc_gens.B_blinding * child_rerandomization_scalar;
        let rerandomized_child = child_commitment + blinding.into_affine();

        single_level_select_and_rerandomize(
            prover,
            odd_parameters,
            &rerandomized_child.into(),
            children_vars,
            Some(child_commitment),
            Some(child_rerandomization_scalar),
        );
    }
}

type Children<const L: usize, P0, P1> = [Option<CurveTreeNode<L, P1, P0>>; L];

// map L children to their x-coordinate with 0 representing the empty node.
fn x_coordinates<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig>(
    children: &Children<L, P0, P1>,
) -> [P1::BaseField; L] {
    children
        .iter()
        .map(|opt| match opt {
            None => P1::BaseField::zero(),
            Some(child) => child.parent_commitment.x,
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

#[derive(Clone)]
pub struct CurveTreeNode<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    parent_commitment: Affine<P0>,
    randomness: P0::ScalarField,
    children: Option<Box<Children<L, P0, P1>>>,
    height: usize,
    elements: usize,
}

impl<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> std::fmt::Debug
    for CurveTreeNode<L, P0, P1>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "")
    }
}

impl<
        const L: usize,
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    > CurveTreeNode<L, P0, P1>
{
    // The commitment is assumed to be permissible
    fn leaf(commitment: Affine<P0>) -> Self {
        Self {
            parent_commitment: commitment,
            randomness: P0::ScalarField::zero(),
            children: None,
            height: 0,
            elements: 1,
        }
    }

    fn child_index(&self, index: usize) -> usize {
        let capacity = L.pow(self.height as u32);
        let child_capacity = L.pow((self.height - 1) as u32);
        (index % capacity) / child_capacity
    }

    fn select_and_rerandomize_prover_witness(
        &self,
        index: usize,
        even_nodes: &mut Vec<CurveTreeWitness<L, P0, P1>>,
        odd_nodes: &mut Vec<CurveTreeWitness<L, P1, P0>>,
    ) {
        if let Some(children) = &self.children {
            let child_index = self.child_index(index);
            let child = match &children[self.child_index(index)] {
                None => panic!(
                    "Child index out of bounds. Height: {}, Index: {}, Local index: {}",
                    self.height, index, child_index
                ),
                Some(child) => child,
            };
            let siblings = x_coordinates(children);

            even_nodes.push(CurveTreeWitness {
                randomness: self.randomness,
                siblings,
                child_witness: child.parent_commitment,
            });

            // recursively add the remaining path
            child.select_and_rerandomize_prover_witness(index, odd_nodes, even_nodes);
        }
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
        // commit to the children's x-coordinates with randomness zero, then increment randomness to find permissible point.
        let (c, r) = parameters.permissible_commitment(
            &x_coordinates(&children),
            P0::ScalarField::zero(),
            0,
        ); // todo index
        Self {
            parent_commitment: c,
            randomness: r,
            children: Some(Box::new(children)),
            height,
            elements,
        }
    }
}

pub struct SelRerandParameters<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    pub even_parameters: SingleLayerParameters<P0>,
    pub odd_parameters: SingleLayerParameters<P1>,
}

impl<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> SelRerandParameters<P0, P1> {
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
