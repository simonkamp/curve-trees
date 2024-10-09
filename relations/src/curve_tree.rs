use crate::single_level_select_and_rerandomize::*;

use ark_ec::AffineRepr;
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Valid, Write,
};
use ark_std::Zero;
use rand::Rng;

// Parameters for multi level select and rerandomize over a 2-cycle of curves
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

pub enum CurveTree<
    const L: usize, // L is te branching factor, i.e. the number of children per branch
    const M: usize, // M the maximal batch size for which efficient parallel membership proofs are supported.
    P0: SWCurveConfig,
    P1: SWCurveConfig,
> {
    Even(CurveTreeNode<L, M, P0, P1>),
    Odd(CurveTreeNode<L, M, P1, P0>),
}

// Implements functionality for creating the Curve Tree
impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    /// Build a curve tree from a set of commitments
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
            even_forest.push(CurveTreeNode::<L, M, P0, P1>::Leaf(*leaf));
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
                odd_forest.push(CurveTreeNode::<L, M, P1, P0>::combine(
                    chunk,
                    &parameters.odd_parameters,
                    &parameters.even_parameters.delta,
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
                even_forest.push(CurveTreeNode::<L, M, P0, P1>::combine(
                    chunk,
                    &parameters.even_parameters,
                    &parameters.odd_parameters.delta,
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
                            res = Self::Odd(CurveTreeNode::<L, M, P1, P0>::combine(
                                vec![ct],
                                &parameters.odd_parameters,
                                &parameters.even_parameters.delta,
                            ));
                        }
                        Self::Odd(ct) => {
                            res = Self::Even(CurveTreeNode::<L, M, P0, P1>::combine(
                                vec![ct],
                                &parameters.even_parameters,
                                &parameters.odd_parameters.delta,
                            ));
                        }
                    }
                }
                res
            }
        }
    }

    //todo add a function to add a single/several commitments

    pub fn height(&self) -> usize {
        match self {
            Self::Even(ct) => ct.height(),
            Self::Odd(ct) => ct.height(),
        }
    }
}

impl<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> CanonicalSerialize
    for SelectAndRerandomizePath<L, P0, P1>
{
    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.selected_commitment.serialized_size(compress)
            + self.odd_commitments.serialized_size(compress)
            + self.even_commitments.serialized_size(compress)
    }

    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), SerializationError> {
        self.selected_commitment
            .serialize_with_mode(&mut writer, compress)?;
        self.odd_commitments
            .serialize_with_mode(&mut writer, compress)?;
        self.even_commitments
            .serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }
}

#[derive(Clone)]
/// A rerandomized path in the tree.
/// The `selected_commitment` is the selected and rerandomized commitment.
/// The last element in `odd_commitments` is the rerandomized parent of the selected leaf.
/// The last element in `even_commitments` is the rerandomized parent of the last element in `odd_commitments`, etc.
pub struct SelectAndRerandomizePath<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    pub selected_commitment: Affine<P0>,
    pub odd_commitments: Vec<Affine<P1>>,
    pub even_commitments: Vec<Affine<P0>>,
}

#[derive(Clone)]
/// A rerandomized multi path in the tree.
/// The elements in `selected_commitments` are the selected and rerandomized commitments.
/// The last element in `odd_commitments` is the rerandomized parent of the selected leaves.
/// The last element in `even_commitments` is the rerandomized parent of the last element in `odd_commitments`, etc.
pub struct SelectAndRerandomizeMultiPath<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig,
    P1: SWCurveConfig,
> {
    pub selected_commitments: [Affine<P0>; M],
    pub odd_commitments: Vec<Affine<P1>>,
    pub even_commitments: Vec<Affine<P0>>,
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
            selected_commitment: Affine::<P0>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            odd_commitments: Vec::<Affine<P1>>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            even_commitments: Vec::<Affine<P0>>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
        })
    }
}

type Children<const L: usize, const M: usize, P0, P1> = [Option<CurveTreeNode<L, M, P1, P0>>; L];

// map L children to their x-coordinate with 0 representing the empty node.
pub fn x_coordinates<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    children: &Children<L, M, P0, P1>,
    delta: &Affine<P1>,
    tree_index: usize,
) -> [P1::BaseField; L] {
    children
        .iter()
        .map(|opt| match opt {
            None => P1::BaseField::zero(),
            Some(child) => (child.commitment(tree_index) + delta).into_affine().x,
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

#[derive(Clone)]
pub enum CurveTreeNode<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    Branch {
        parent_commitment: [Affine<P0>; M],
        children: Box<Children<L, M, P0, P1>>,
        height: usize,
        elements: usize,
    },
    Leaf(Affine<P0>),
}

impl<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> std::fmt::Debug
    for CurveTreeNode<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "")
    }
}

impl<
        const L: usize,
        const M: usize,
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    > CurveTreeNode<L, M, P0, P1>
{
    pub fn commitment(&self, tree_index: usize) -> Affine<P0> {
        match self {
            Self::Branch {
                parent_commitment,
                children: _,
                height: _,
                elements: _,
            } => parent_commitment[tree_index],
            Self::Leaf(c) => *c,
        }
    }

    pub fn height(&self) -> usize {
        match self {
            Self::Branch {
                parent_commitment: _,
                children: _,
                height,
                elements: _,
            } => *height,
            Self::Leaf(_) => 0,
        }
    }

    pub fn elements(&self) -> usize {
        match self {
            Self::Branch {
                parent_commitment: _,
                children: _,
                height: _,
                elements,
            } => *elements,
            Self::Leaf(_) => 1,
        }
    }

    pub fn child_index(&self, index: usize) -> usize {
        let capacity = L.pow(self.height() as u32);
        let child_capacity = L.pow((self.height() - 1) as u32);
        (index % capacity) / child_capacity
    }

    // Combine up to L child nodes of level d into a single level d+1 node.
    // The children are assumed to be of appropriate identical height.
    // All but the last should be full.
    fn combine(
        children: Vec<CurveTreeNode<L, M, P1, P0>>,
        parameters: &SingleLayerParameters<P0>,
        delta: &Affine<P1>,
    ) -> Self {
        if children.len() > L {
            panic!(
                "Cannot combine more than the branching factor: {} into one node.",
                L
            )
        };

        let mut elements = 0;
        let mut cs: Vec<Option<CurveTreeNode<L, M, P1, P0>>> = Vec::with_capacity(L);
        for c in children {
            elements += c.elements();
            cs.push(Some(c));
        }
        // Let the rest of the children be dummy elements.
        while cs.len() < L {
            cs.push(None)
        }
        let children: [Option<CurveTreeNode<L, M, P1, P0>>; L] = cs.try_into().unwrap();
        let height = if let Some(c) = &children[0] {
            c.height() + 1
        } else {
            1
        };
        // For each set of generators commit to the children's x-coordinates with randomness zero.
        let mut commitments = [Affine::<P0>::zero(); M];
        for (tree_index, c) in commitments.iter_mut().enumerate() {
            *c = parameters.commit(
                &x_coordinates(&children, delta, tree_index),
                P0::ScalarField::zero(),
                tree_index,
            );
        }
        Self::Branch {
            parent_commitment: commitments,
            children: Box::new(children),
            height,
            elements,
        }
    }
}
