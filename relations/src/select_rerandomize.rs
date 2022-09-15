#![allow(unused)] // todo
use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use crate::curve::*;
use crate::lookup::*;
use crate::permissible::*;
use crate::rerandomize::*;
use crate::select::*;

use ark_ec::{
    models::short_weierstrass_jacobian::{GroupAffine, GroupProjective},
    msm::VariableBaseMSM,
    AffineCurve, ModelParameters, ProjectiveCurve, SWModelParameters,
};
use ark_ff::{BigInteger, Field, PrimeField, SquareRootField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::{One, UniformRand, Zero};
use merlin::Transcript;
use rand::Rng;
use std::{borrow::BorrowMut, iter, marker::PhantomData};

pub struct SingleLayerParameters<P: SWModelParameters> {
    pub bp_gens: BulletproofGens<GroupAffine<P>>,
    pub pc_gens: PedersenGens<GroupAffine<P>>,
    pub uh: UniversalHash<P::BaseField>,
    pub tables: Vec<Lookup3Bit<2, P::BaseField>>,
}

pub enum CurveTree<const L: usize, P0: SWModelParameters, P1: SWModelParameters> {
    Even(CurveTreeNode<L, P0, P1>),
    Odd(CurveTreeNode<L, P1, P0>),
}

impl<
        const L: usize,
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    > CurveTree<L, P0, P1>
{
    /// Build a curve tree from a set of commitments assumed to be permissible
    pub fn from_set(
        set: &[GroupAffine<P0>],
        parameters: &SelRerandParameters<P0, P1>,
        height: Option<usize>, // resulting curve tree will have height at least `height`
    ) -> Self {
        if set.len() == 0 {
            panic!("The curve tree must have at least one leaf.")
        }
        // Convert each commitment to a leaf.
        let mut even_forest: Vec<_> = set
            .iter()
            .map(|comm| CurveTreeNode::<L, P0, P1>::leaf(*comm))
            .collect();
        let mut current_height = 0;
        // todo should it be depth instead of height? Leaf has depth 0, but what height?
        while even_forest.len() > 1 || height.map_or(false, |h| current_height < h) {
            current_height += 1;
            // Combine forest of trees with even roots, into a forest of trees with odd roots.
            let odd_forest: Vec<_> = even_forest
                .chunks(L)
                .map(|chunk| CurveTreeNode::<L, P1, P0>::combine(chunk, &parameters.c1_parameters))
                .collect();

            if odd_forest.len() == 1 && height.map_or(true, |h| current_height >= h) {
                return Self::Odd(odd_forest[0].clone());
            }

            current_height += 1;
            // Combine forest of trees with odd roots, into a forest of trees with even roots.
            even_forest = odd_forest
                .chunks(L)
                .map(|chunk| CurveTreeNode::<L, P0, P1>::combine(chunk, &parameters.c0_parameters))
                .collect();
        }
        Self::Even(even_forest[0].clone())
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the commitments and the rerandomization scalar of the selected commitment.
    pub fn select_and_rerandomize_gadget(
        &self,
        index: usize,
        even_prover: &mut Prover<Transcript, GroupAffine<P0>>,
        odd_prover: &mut Prover<Transcript, GroupAffine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> (Vec<GroupAffine<P0>>, Vec<GroupAffine<P1>>, P0::ScalarField) {
        let mut rng = rand::thread_rng();

        // let mut level_index = 0; // todo for now lets always access the first child
        let mut even_commitments = Vec::new();
        let mut odd_commitments = Vec::new();
        let (mut even_internal_node, mut rerandomization_scalar) = match self {
            Self::Odd(ct) => ct.single_level_select_and_rerandomize_prover_gadget(
                index,
                odd_prover,
                &mut odd_commitments,
                &parameters.c1_parameters,
                &parameters.c0_parameters,
                P1::ScalarField::zero(),
                &mut rng,
            ),
            Self::Even(ct) => (ct, P0::ScalarField::zero()),
        };
        // While the current node is internal, do two iterations of the proof.
        while let Some(_) = &even_internal_node.children {
            // Do two iterations of the proof and advance `even_internal_node`to a grandchild.
            let (child, child_rerandomization_scalar) = even_internal_node
                .single_level_select_and_rerandomize_prover_gadget(
                    index,
                    even_prover,
                    &mut even_commitments,
                    &parameters.c0_parameters,
                    &parameters.c1_parameters,
                    rerandomization_scalar,
                    &mut rng,
                );

            // Assumes the leaf layer is even. Todo make this part of the type
            (even_internal_node, rerandomization_scalar) = child
                .single_level_select_and_rerandomize_prover_gadget(
                    index,
                    odd_prover,
                    &mut odd_commitments,
                    &parameters.c1_parameters,
                    &parameters.c0_parameters,
                    child_rerandomization_scalar,
                    &mut rng,
                );
        }

        // return the commitments and the rerandomization scalar of the leaf.
        (even_commitments, odd_commitments, rerandomization_scalar)
    }

    pub fn height(&self) -> usize {
        match self {
            Self::Even(ct) => ct.height,
            Self::Odd(ct) => ct.height,
        }
    }

    // todo add a function to increase capacity/height

    //todo add a function to add a single/several commitments
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
            commitment: commitment,
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
        commitments: &mut Vec<GroupAffine<P0>>,
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
                    None => panic!("Child index out of bounds."),
                    Some(child) => child,
                };
                let (rerandomized_commitment, children_vars) = prover.commit_vec(
                    &children
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
                commitments.push(rerandomized_commitment);
                let child_commitment = child.commitment;
                let mut blinding_base = odd_parameters.pc_gens.B_blinding.into_projective();
                blinding_base *= child_rerandomization_scalar;
                let rerandomized_child = child_commitment + blinding_base.into_affine();
                (child, rerandomized_child, children_vars)
            }
        };

        single_level_select_and_rerandomize(
            prover,
            &odd_parameters,
            &rerandomized_child,
            children_vars,
            Some(child.commitment),
            Some(child_rerandomization_scalar),
        );

        // todo would be prettier to call it recursively, but the return type would need to be known
        (child, child_rerandomization_scalar)
    }

    // Combine up to L nodes of level d into a single level d+1 node.
    // The children are assumed to be of appropriate identical height.
    // All but the last should be full.
    fn combine(
        children: &[CurveTreeNode<L, P1, P0>],
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
            cs.push(Some(c.clone()));
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
        let c_init = vector_commitment(
            children_commitments.as_slice(),
            P0::ScalarField::zero(),
            &parameters.bp_gens,
            &parameters.pc_gens,
        );
        let (c, r) = parameters
            .uh
            .permissible_commitment(&c_init, &parameters.pc_gens.B_blinding);

        Self {
            commitment: c,
            randomness: r,
            children: Some(Box::new(children)),
            height: height,
            elements: elements,
        }
    }
}

fn single_level_select_and_rerandomize<
    Fb: SquareRootField,
    Fs: SquareRootField,
    C2: SWModelParameters<BaseField = Fs, ScalarField = Fb>,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs,
    parameters: &SingleLayerParameters<C2>,
    rerandomized: &GroupAffine<C2>, // the public rerandomization of witness
    c0_vars: Vec<Variable<Fs>>,     // variables representing members of the vector commitment
    xy_witness: Option<GroupAffine<C2>>, // witness of the commitment we wish to select and rerandomize
    randomness_offset: Option<Fb>,       // the scalar used for randomizing
) {
    let x_var = cs.allocate(xy_witness.map(|xy| xy.x)).unwrap();
    // show that leaf is in c0
    select(
        cs,
        x_var.into(),
        c0_vars.into_iter().map(|v| v.into()).collect(),
    );
    // proof that l0 is a permissible
    parameters
        .uh
        .permissible(cs, x_var.into(), xy_witness.map(|xy| xy.y)); // todo this allocates a variable for y in addition to the one below
                                                                   // show that leaf_rerand, is a rerandomization of leaf
    let leaf_y = cs.allocate(xy_witness.map(|xy| xy.y)).unwrap();
    re_randomize(
        cs,
        &parameters.tables,
        x_var.into(),
        leaf_y.into(),
        constant(rerandomized.x),
        constant(rerandomized.y),
        xy_witness,
        randomness_offset,
    );
}

pub struct SelRerandProof<P0: SWModelParameters, P1: SWModelParameters> {
    pub result: GroupAffine<P0>,
    pub pallas_proof: R1CSProof<GroupAffine<P0>>,
    pub pallas_commitments: Vec<GroupAffine<P0>>,
    pub vesta_proof: R1CSProof<GroupAffine<P1>>,
    pub vesta_commitments: Vec<GroupAffine<P1>>,
}

impl<P0: SWModelParameters, P1: SWModelParameters> CanonicalSerialize for SelRerandProof<P0, P1> {
    fn serialized_size(&self) -> usize {
        let r1cs_proofs_size =
            self.pallas_proof.serialized_size() + self.vesta_proof.serialized_size();
        let commitments_size = self.result.serialized_size()
            + self.pallas_commitments.serialized_size()
            + self.vesta_commitments.serialized_size();
        r1cs_proofs_size + commitments_size
    }

    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // This serialization uses 8 bytes to encode the length of each vector.
        // There are three point vectors in each proof, and two commitment vectors.
        // I.e. 64 superfluous bytes for the entire proof.
        self.result.serialize(&mut writer)?;
        self.pallas_proof.serialize(&mut writer)?;
        self.pallas_commitments.serialize(&mut writer)?;
        self.vesta_proof.serialize(&mut writer)?;
        self.vesta_commitments.serialize(&mut writer)?;
        Ok(())
    }
}

impl<P0: SWModelParameters, P1: SWModelParameters> CanonicalDeserialize for SelRerandProof<P0, P1> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        Ok(Self {
            result: GroupAffine::<P0>::deserialize(&mut reader)?,
            pallas_proof: R1CSProof::<GroupAffine<P0>>::deserialize(&mut reader)?,
            pallas_commitments: Vec::<GroupAffine<P0>>::deserialize(&mut reader)?,
            vesta_proof: R1CSProof::<GroupAffine<P1>>::deserialize(&mut reader)?,
            vesta_commitments: Vec::<GroupAffine<P1>>::deserialize(&mut reader)?,
        })
    }
}

fn vector_commitment<C: AffineCurve>(
    v: &[C::ScalarField],
    v_blinding: C::ScalarField,
    bp_gens: &BulletproofGens<C>,
    pc_gens: &PedersenGens<C>,
) -> C {
    use std::iter;

    let gens = bp_gens.share(0);

    let generators: Vec<_> = iter::once(&pc_gens.B_blinding)
        .chain(gens.G(v.len()))
        .cloned()
        .collect::<Vec<_>>();

    let scalars: Vec<<C::ScalarField as PrimeField>::BigInt> = iter::once(&v_blinding)
        .chain(v.iter())
        .map(|s| {
            let s: <C::ScalarField as PrimeField>::BigInt = s.clone().into();
            s
        })
        .collect();

    assert_eq!(generators.len(), scalars.len());

    let comm = VariableBaseMSM::multi_scalar_mul(generators.as_slice(), scalars.as_slice());
    comm.into_affine()
}

pub struct SelRerandParameters<P0: SWModelParameters, P1: SWModelParameters> {
    pub c0_parameters: SingleLayerParameters<P0>,
    pub c1_parameters: SingleLayerParameters<P1>,
}

impl<P0: SWModelParameters, P1: SWModelParameters> SelRerandParameters<P0, P1> {
    pub fn new<R: Rng>(generators_length: usize, rng: &mut R) -> Self {
        // todo clean up naming and dead code
        let c0_pc_gens = PedersenGens::<GroupAffine<P0>>::default();
        let c0_bp_gens = BulletproofGens::<GroupAffine<P0>>::new(generators_length, 1);
        let c0_uh = UniversalHash::new(rng, P0::COEFF_A, P0::COEFF_B);
        let c0_scalar_tables = build_tables(c0_pc_gens.B_blinding);
        let c2_pc_gens = PedersenGens::<GroupAffine<P1>>::default();
        let c2_bp_gens = BulletproofGens::<GroupAffine<P1>>::new(generators_length, 1);
        let c2_uh = UniversalHash::new(rng, P1::COEFF_A, P1::COEFF_B);

        let c1_scalar_tables = build_tables(c2_pc_gens.B_blinding);
        let c0_parameters = SingleLayerParameters {
            bp_gens: BulletproofGens::<GroupAffine<P0>>::new(generators_length, 1),
            pc_gens: PedersenGens::<GroupAffine<P0>>::default(),
            uh: UniversalHash::new(rng, P0::COEFF_A, P0::COEFF_B),
            tables: c0_scalar_tables,
        };
        let c1_parameters = SingleLayerParameters {
            bp_gens: BulletproofGens::<GroupAffine<P1>>::new(generators_length, 1),
            pc_gens: PedersenGens::<GroupAffine<P1>>::default(),
            uh: UniversalHash::new(rng, P1::COEFF_A, P1::COEFF_B),
            tables: c1_scalar_tables,
        };
        SelRerandParameters {
            c0_parameters: c0_parameters,
            c1_parameters: c1_parameters,
        }
    }
}

pub fn prove_from_mock_curve_tree<
    P0: SWModelParameters,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField>,
>(
    srp: &SelRerandParameters<P0, P1>,
) -> (SelRerandProof<P0, P1>) {
    let mut rng = rand::thread_rng();

    let mut pallas_transcript = Transcript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, GroupAffine<P0>> =
        Prover::new(&srp.c0_parameters.pc_gens, &mut pallas_transcript);

    let mut vesta_transcript = Transcript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, GroupAffine<P1>> =
        Prover::new(&srp.c1_parameters.pc_gens, &mut vesta_transcript);

    let (leaf, leaf_rerand, leaf_rerandomization_offset) = {
        // Let leaf be a random dummy commitment for which we want to prove the select and randomize relation.
        let leaf_val = P0::ScalarField::rand(&mut rng);
        let leaf_randomness = P0::ScalarField::rand(&mut rng);
        let leaf = srp.c0_parameters.pc_gens.commit(leaf_val, leaf_randomness);
        let (leaf, r) = srp
            .c0_parameters
            .uh
            .permissible_commitment(&leaf, &srp.c0_parameters.pc_gens.B_blinding);
        let leaf_randomness = leaf_randomness + r;
        assert_eq!(
            leaf,
            srp.c0_parameters.pc_gens.commit(leaf_val, leaf_randomness)
        );
        let leaf_rerandomization_offset = P0::ScalarField::rand(&mut rng);
        // The rerandomization of the commitment to leaf is public.
        let leaf_rerand = srp
            .c0_parameters
            .pc_gens
            .commit(leaf_val, leaf_randomness + leaf_rerandomization_offset);
        (leaf, leaf_rerand, leaf_rerandomization_offset)
    };

    let (c0, c0_rerand, c0_rerandomization_offset, c0_rerand_vars) = {
        // Make a bunch of dummy commitments (random points) for the remaining leafs.
        let leaves: Vec<_> = iter::once(leaf.x)
            .chain(iter::from_fn(|| Some(P1::ScalarField::rand(&mut rng))).take(255))
            .collect();
        // Build the first internal node: a vector commitment to the leaves.
        let c0_r = P1::ScalarField::rand(&mut rng);
        let c0 = vector_commitment(
            leaves.as_slice(),
            c0_r,
            &srp.c1_parameters.bp_gens,
            &srp.c1_parameters.pc_gens,
        );
        // The internal node must also be a permissible commitment.
        let (c0, r) = srp
            .c1_parameters
            .uh
            .permissible_commitment(&c0, &srp.c1_parameters.pc_gens.B_blinding);
        let c0_r = c0_r + r;
        let c0_rerandomization_offset = P1::ScalarField::rand(&mut rng);
        let (c0_rerand, c0_rerand_vars) = vesta_prover.commit_vec(
            leaves.as_slice(),
            c0_r + c0_rerandomization_offset,
            &srp.c1_parameters.bp_gens,
        );

        (c0, c0_rerand, c0_rerandomization_offset, c0_rerand_vars)
    };
    single_level_select_and_rerandomize(
        &mut vesta_prover,
        &srp.c0_parameters,
        &leaf_rerand,
        c0_rerand_vars,
        Some(leaf),
        Some(leaf_rerandomization_offset),
    );
    let (c1, c1_rerand, c1_rerandomization_offset, c1_rerand_vars) = {
        // Make a bunch of dummy commitments (random points) for the remaining children.
        let rt1: Vec<_> = iter::once(c0.x)
            .chain(iter::from_fn(|| Some(P0::ScalarField::rand(&mut rng))).take(255))
            .collect();
        // Build the internal node: a vector commitment to the children.
        let c1_init_randomness = P0::ScalarField::rand(&mut rng);
        let c1 = vector_commitment(
            rt1.as_slice(),
            c1_init_randomness,
            &srp.c0_parameters.bp_gens,
            &srp.c0_parameters.pc_gens,
        );
        // Rerandomize the internal node to get a permissible point.
        let (c1, r) = srp
            .c0_parameters
            .uh
            .permissible_commitment(&c1, &srp.c0_parameters.pc_gens.B_blinding);
        let c1_permissible_randomness = c1_init_randomness + r;
        // Rerandomize the commitment so we can show membership without revealing the branch we are in.
        let c1_rerandomization_offset = P0::ScalarField::rand(&mut rng);
        let (c1_rerand, c1_rerand_vars) = pallas_prover.commit_vec(
            rt1.as_slice(),
            c1_permissible_randomness + c1_rerandomization_offset,
            &srp.c0_parameters.bp_gens,
        );
        (c1, c1_rerand, c1_rerandomization_offset, c1_rerand_vars)
    };
    single_level_select_and_rerandomize(
        &mut pallas_prover,
        &srp.c1_parameters,
        &c0_rerand,
        c1_rerand_vars,
        Some(c0),
        Some(c0_rerandomization_offset),
    );
    let (c2, c2_rerand, c2_rerandomization_offset, c2_rerand_vars) = {
        // Make a bunch of dummy commitments (random points) for the remaining children.
        let rt2: Vec<_> = iter::once(c1.x)
            .chain(iter::from_fn(|| Some(P1::ScalarField::rand(&mut rng))).take(255))
            .collect();
        // Build the internal node: a vector commitment to the children.
        let c2_init_randomness = P1::ScalarField::rand(&mut rng);
        let c2 = vector_commitment(
            rt2.as_slice(),
            c2_init_randomness,
            &srp.c1_parameters.bp_gens,
            &srp.c1_parameters.pc_gens,
        );
        // Rerandomize the internal node to get a permissible point.
        let (c2, r) = srp
            .c1_parameters
            .uh
            .permissible_commitment(&c2, &srp.c1_parameters.pc_gens.B_blinding);
        let c2_permissible_randomness = c2_init_randomness + r;
        // Rerandomize the commitment so we can show membership without revealing the branch we are in.
        let c2_rerandomization_offset = P1::ScalarField::rand(&mut rng);
        let (c2_rerand, c2_rerand_vars) = vesta_prover.commit_vec(
            rt2.as_slice(),
            c2_permissible_randomness + c2_rerandomization_offset,
            &srp.c1_parameters.bp_gens,
        );
        (c2, c2_rerand, c2_rerandomization_offset, c2_rerand_vars)
    };
    single_level_select_and_rerandomize(
        &mut vesta_prover,
        &srp.c0_parameters,
        &c1_rerand,
        c2_rerand_vars,
        Some(c1),
        Some(c1_rerandomization_offset),
    );

    let (c3, c3_vars) = {
        // Make a bunch of dummy commitments (random points) for the remaining children.
        let rt3: Vec<_> = iter::once(c2.x)
            .chain(iter::from_fn(|| Some(P0::ScalarField::rand(&mut rng))).take(255))
            .collect();
        // Build the internal node: a vector commitment to the children.
        let c3_init_randomness = P0::ScalarField::rand(&mut rng);
        let c3 = vector_commitment(
            rt3.as_slice(),
            c3_init_randomness,
            &srp.c0_parameters.bp_gens,
            &srp.c0_parameters.pc_gens,
        );
        // Rerandomize the internal node to get a permissible point.
        let (c3, r) = srp
            .c0_parameters
            .uh
            .permissible_commitment(&c3, &srp.c0_parameters.pc_gens.B_blinding);
        let c3_permissible_randomness = c3_init_randomness + r;
        // c3 is the root, and does not need to be hidden.
        let (c3_r, c3_vars) = pallas_prover.commit_vec(
            rt3.as_slice(),
            c3_permissible_randomness,
            &srp.c0_parameters.bp_gens,
        );
        // assert_eq!(c3, c3_r);
        (c3, c3_vars)
    };
    single_level_select_and_rerandomize(
        &mut pallas_prover,
        &srp.c1_parameters,
        &c2_rerand,
        c3_vars,
        Some(c2),
        Some(c2_rerandomization_offset),
    );
    SelRerandProof {
        result: leaf_rerand,
        pallas_proof: pallas_prover.prove(&srp.c0_parameters.bp_gens).unwrap(),
        pallas_commitments: vec![c1_rerand, c3],
        vesta_proof: vesta_prover.prove(&srp.c1_parameters.bp_gens).unwrap(),
        vesta_commitments: vec![c0_rerand, c2_rerand],
    }
}

pub fn verification_circuit<
    P0: SWModelParameters,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField>,
>(
    sr_params: &SelRerandParameters<P0, P1>,
    sr_proof: &SelRerandProof<P0, P1>,
) -> (
    Verifier<Transcript, GroupAffine<P0>>,
    Verifier<Transcript, GroupAffine<P1>>,
) {
    let vesta_verifier = {
        // Verify the vesta proof
        let mut transcript = Transcript::new(b"select_and_rerandomize");
        let mut verifier = Verifier::new(transcript);
        let c0_rerand_vars = verifier.commit_vec(256, sr_proof.vesta_commitments[0]);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_params.c0_parameters,
            &sr_proof.result,
            c0_rerand_vars,
            None,
            None,
        );
        let c2_rerand_vars = verifier.commit_vec(256, sr_proof.vesta_commitments[1]);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_params.c0_parameters,
            &sr_proof.pallas_commitments[0],
            c2_rerand_vars,
            None,
            None,
        );
        verifier
    };
    let pallas_verifier = {
        let mut transcript = Transcript::new(b"select_and_rerandomize");
        let mut verifier = Verifier::new(transcript);
        let c1_rerand_vars = verifier.commit_vec(256, sr_proof.pallas_commitments[0]);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_params.c1_parameters,
            &sr_proof.vesta_commitments[0],
            c1_rerand_vars,
            None,
            None,
        );
        let c3_vars = verifier.commit_vec(256, sr_proof.pallas_commitments[1]);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_params.c1_parameters,
            &sr_proof.vesta_commitments[1],
            c3_vars,
            None,
            None,
        );
        verifier
    };
    (pallas_verifier, vesta_verifier)
}

fn select_and_rerandomize_verification_gadget<
    P0: SWModelParameters,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField>,
    T: BorrowMut<Transcript>,
>(
    even_commitments: &Vec<GroupAffine<P0>>,
    odd_commitments: &Vec<GroupAffine<P1>>,
    even_verifier: &mut Verifier<T, GroupAffine<P0>>,
    odd_verifier: &mut Verifier<T, GroupAffine<P1>>,
    parameters: &SelRerandParameters<P0, P1>,
) {
    // todo split into two functions for parallelizability?
    // todo benchmark time of building circuit vs final verification to estimate gain of parallelizing one or both.
    assert!(even_commitments.len() >= odd_commitments.len());
    assert!(even_commitments.len() <= odd_commitments.len() + 1);

    // The last even commitment is a leaf.
    for i in 0..even_commitments.len() - 1 {
        let odd_index = if even_commitments.len() == odd_commitments.len() {
            i + 1
        } else {
            i
        };
        let variables = even_verifier.commit_vec(256, even_commitments[i]);
        single_level_select_and_rerandomize(
            even_verifier,
            &parameters.c1_parameters,
            &odd_commitments[odd_index],
            variables,
            None,
            None,
        );
    }

    for i in 0..odd_commitments.len() {
        let even_index = if even_commitments.len() == odd_commitments.len() {
            i
        } else {
            i + 1
        };
        let variables = odd_verifier.commit_vec(256, odd_commitments[i]);
        single_level_select_and_rerandomize(
            odd_verifier,
            &parameters.c0_parameters,
            &even_commitments[even_index],
            variables,
            None,
            None,
        );
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    use ark_std::UniformRand;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;

    use rand::thread_rng;

    use pasta;
    type PallasParameters = pasta::pallas::PallasParameters;
    type VestaParameters = pasta::vesta::VestaParameters;
    type PallasA = pasta::pallas::Affine;
    type PallasP = pasta::pallas::Projective;
    type PallasScalar = <PallasA as AffineCurve>::ScalarField;
    type PallasBase = <PallasA as AffineCurve>::BaseField;
    type VestaA = pasta::vesta::Affine;
    type VestaScalar = <VestaA as AffineCurve>::ScalarField;
    type VestaBase = <VestaA as AffineCurve>::BaseField;

    #[test]
    fn test_select_and_rerandomize_single() {
        let mut rng = rand::thread_rng();
        let generators_length = 1 << 12; // minimum sufficient power of 2

        let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            &mut rng,
        );

        // test single verification:
        let sr_proof = prove_from_mock_curve_tree(&sr_params);
        let (pallas_verifier, vesta_verifier) = verification_circuit(&sr_params, &sr_proof);
        let p_res = pallas_verifier.verify(
            &sr_proof.pallas_proof,
            &sr_params.c0_parameters.pc_gens,
            &sr_params.c0_parameters.bp_gens,
        );
        let v_res = vesta_verifier.verify(
            &sr_proof.vesta_proof,
            &sr_params.c1_parameters.pc_gens,
            &sr_params.c1_parameters.bp_gens,
        );
        assert_eq!(p_res, Ok(()));
        assert_eq!(v_res, Ok(()));
    }

    #[test]
    fn test_select_and_rerandomize_batched() {
        let mut rng = rand::thread_rng();
        let generators_length = 1 << 12; // minimum sufficient power of 2

        let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            &mut rng,
        );

        // test batched verifications:
        let sr_proof = prove_from_mock_curve_tree(&sr_params);
        let (pallas_verifier, vesta_verifier) = verification_circuit(&sr_params, &sr_proof);
        let sr_proof2 = prove_from_mock_curve_tree(&sr_params);
        let vesta_verification_scalars_and_points = vesta_verifier
            .verification_scalars_and_points(&sr_proof.vesta_proof)
            .unwrap();
        let pallas_verification_scalars_and_points = pallas_verifier
            .verification_scalars_and_points(&sr_proof.pallas_proof)
            .unwrap();

        let (pallas_verifier, vesta_verifier) = verification_circuit(&sr_params, &sr_proof2);
        let vesta_verification_scalars_and_points2 = vesta_verifier
            .verification_scalars_and_points(&sr_proof.vesta_proof)
            .unwrap();
        let pallas_verification_scalars_and_points2 = pallas_verifier
            .verification_scalars_and_points(&sr_proof.pallas_proof)
            .unwrap();

        let p_res = batch_verify(
            vec![
                pallas_verification_scalars_and_points,
                pallas_verification_scalars_and_points2,
            ],
            &sr_params.c0_parameters.pc_gens,
            &sr_params.c0_parameters.bp_gens,
        );
        let v_res = batch_verify(
            vec![
                vesta_verification_scalars_and_points,
                vesta_verification_scalars_and_points2,
            ],
            &sr_params.c1_parameters.pc_gens,
            &sr_params.c1_parameters.bp_gens,
        );
        assert_eq!(p_res, Ok(()));
        assert_eq!(v_res, Ok(()));
    }

    #[test]
    pub fn curve_tree() {
        let mut rng = rand::thread_rng();
        let generators_length = 1 << 12; // minimum sufficient power of 2

        let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            &mut rng,
        );

        let mut pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, GroupAffine<PallasParameters>> =
            Prover::new(&sr_params.c0_parameters.pc_gens, pallas_transcript);

        let mut vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, GroupAffine<VestaParameters>> =
            Prover::new(&sr_params.c1_parameters.pc_gens, vesta_transcript);

        let some_point = PallasP::rand(&mut rng).into_affine();
        let (permissible_point, _) = sr_params
            .c0_parameters
            .uh
            .permissible_commitment(&some_point, &sr_params.c0_parameters.pc_gens.B_blinding);
        let set = vec![permissible_point];
        let curve_tree = CurveTree::<256, PallasParameters, VestaParameters>::from_set(
            &set,
            &sr_params,
            Some(4),
        );
        assert_eq!(curve_tree.height(), 4);

        let (pallas_commitments, vesta_commitments, rerandomization_scalar) = curve_tree
            .select_and_rerandomize_gadget(0, &mut pallas_prover, &mut vesta_prover, &sr_params);

        let pallas_proof = pallas_prover
            .prove(&sr_params.c0_parameters.bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&sr_params.c1_parameters.bp_gens)
            .unwrap();

        {
            let mut pallas_transcript = Transcript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let mut vesta_transcript = Transcript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            select_and_rerandomize_verification_gadget(
                &pallas_commitments,
                &vesta_commitments,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_params,
            );

            pallas_verifier.verify(
                &pallas_proof,
                &sr_params.c0_parameters.pc_gens,
                &sr_params.c0_parameters.bp_gens,
            );
            vesta_verifier.verify(
                &vesta_proof,
                &sr_params.c1_parameters.pc_gens,
                &sr_params.c1_parameters.bp_gens,
            );
        }
    }

    // todo could add a test with branching factor 1 to test correctness w.o. vector commitments.
}
