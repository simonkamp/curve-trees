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
    pub fn from_Set(
        set: &[GroupAffine<P0>],
        even_parameters: &SingleLayerParameters<P0>,
        odd_parameters: &SingleLayerParameters<P1>,
    ) -> Self {
        if set.len() == 0 {
            panic!("")
        }
        // Convert each commitment to a leaf.
        let mut even_forest: Vec<_> = set
            .iter()
            .map(|comm| CurveTreeNode::<L, P0, P1>::leaf(*comm))
            .collect();
        let mut number_of_trees = even_forest.len();
        while number_of_trees > 1 {
            // Combine forest of trees with even roots, into a forest of trees with odd roots.
            let odd_forest: Vec<_> = even_forest
                .chunks(L)
                .map(|chunk| CurveTreeNode::<L, P1, P0>::combine(chunk, odd_parameters))
                .collect();

            if odd_forest.len() == 1 {
                return Self::Odd(odd_forest[0].clone());
            }

            // Combine forest of trees with odd roots, into a forest of trees with even roots.
            even_forest = odd_forest
                .chunks(L)
                .map(|chunk| CurveTreeNode::<L, P0, P1>::combine(chunk, even_parameters))
                .collect();
        }
        Self::Even(even_forest[0].clone())
    }

    pub fn get_path(
        &self,
        index: usize,
    ) -> (Vec<SingleLayerWitness<P0>>, Vec<SingleLayerWitness<P1>>) {
        match self {
            Self::Even(ct) => ct.get_path(index),
            Self::Odd(ct) => {
                let (odd_commitments, even_commitments) = ct.get_path(index);
                (even_commitments, odd_commitments)
            }
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

pub struct SingleLayerWitness<P: SWModelParameters> {
    commitment: GroupAffine<P>,
    randomness: P::ScalarField,
    index: usize,
}

impl<
        const L: usize,
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField> + Clone,
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

    // Gets the commitments on the path from the root to the leaf
    pub fn get_path(
        &self,
        leaf_index: usize,
    ) -> (Vec<SingleLayerWitness<P0>>, Vec<SingleLayerWitness<P1>>) {
        if leaf_index > self.capacity() {
            panic!("Out of bounds")
        };

        // path_indeces contain at index i the index of the height i node in the set of children of the height i+1 node.
        let mut path_indeces = Vec::with_capacity(self.height);
        let mut leafs_per_d_layer_node = L;
        for d in 0..self.height {
            let layer_d_index = leaf_index / leafs_per_d_layer_node;
            path_indeces.push(layer_d_index);
            leafs_per_d_layer_node *= L;
        }

        let mut self_commitments = Vec::new();
        let mut other_commitments = Vec::new();
        self_commitments.push(SingleLayerWitness {
            commitment: self.commitment,
            randomness: self.randomness,
            index: 0, // the root does not have a meaningful index
        });
        let mut tree = self;
        let mut d = self.height;
        while d > 0 {
            d -= 1; // d is at least 0

            let child = if let Some(children) = &tree.children {
                if let Some(child) = &children[path_indeces[d]] {
                    child
                } else {
                    panic!("Out of bounds")
                }
            } else {
                panic!("Out of bounds")
            };
            other_commitments.push(SingleLayerWitness {
                commitment: child.commitment,
                randomness: child.randomness,
                index: path_indeces[d],
            });

            if d == 0 {
                break;
            }
            d -= 1; // d is at least 0
            let grandchild = if let Some(children) = &child.children {
                if let Some(gc) = &children[path_indeces[d]] {
                    gc
                } else {
                    panic!("Out of bounds")
                }
            } else {
                panic!("Out of bounds")
            };
            self_commitments.push(SingleLayerWitness {
                commitment: grandchild.commitment,
                randomness: grandchild.randomness,
                index: path_indeces[d],
            });
            tree = grandchild;
        }
        (self_commitments, other_commitments)
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
    uh: &UniversalHash<Fs>,
    tables: &Vec<Lookup3Bit<2, Fs>>,
    rerandomized: GroupAffine<C2>, // the public rerandomization of witness
    c0_vars: Vec<Variable<Fs>>,    // variables representing members of the vector commitment
    index: Option<usize>,          // then index of witness in the vector commitment
    xy_witness: Option<GroupAffine<C2>>, // witness of the commitment we wish to select and rerandomize
    randomness_offset: Option<Fb>,       // the scalar used for randomizing
) {
    let x_var = cs.allocate(xy_witness.map(|xy| xy.x)).unwrap();
    // show that leaf is in c0
    select(
        cs,
        x_var.into(),
        c0_vars.into_iter().map(|v| v.into()).collect(),
        index,
    );
    // proof that l0 is a permissible
    uh.permissible(cs, x_var.into(), xy_witness.map(|xy| xy.y)); // todo this allocates a variable for y in addition to the one below
                                                                 // show that leaf_rerand, is a rerandomization of leaf
    let leaf_y = cs.allocate(xy_witness.map(|xy| xy.y)).unwrap();
    re_randomize(
        cs,
        tables,
        x_var.into(),
        leaf_y.into(),
        constant(rerandomized.x),
        constant(rerandomized.y),
        xy_witness,
        randomness_offset,
    );
}

pub struct SelRerandProof<P1: SWModelParameters, P2: SWModelParameters> {
    pub result: GroupAffine<P1>,
    pub pallas_proof: R1CSProof<GroupAffine<P1>>,
    pub pallas_commitments: Vec<GroupAffine<P1>>,
    pub vesta_proof: R1CSProof<GroupAffine<P2>>,
    pub vesta_commitments: Vec<GroupAffine<P2>>,
}

impl<P1: SWModelParameters, P2: SWModelParameters> CanonicalSerialize for SelRerandProof<P1, P2> {
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
        // There are two point vectors in each proof, and two commitment vectors.
        // I.e. 48 superfluous bytes for the entire proof.
        self.result.serialize(&mut writer)?;
        self.pallas_proof.serialize(&mut writer)?;
        self.pallas_commitments.serialize(&mut writer)?;
        self.vesta_proof.serialize(&mut writer)?;
        self.vesta_commitments.serialize(&mut writer)?;
        Ok(())
    }
}

impl<P1: SWModelParameters, P2: SWModelParameters> CanonicalDeserialize for SelRerandProof<P1, P2> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        Ok(Self {
            result: GroupAffine::<P1>::deserialize(&mut reader)?,
            pallas_proof: R1CSProof::<GroupAffine<P1>>::deserialize(&mut reader)?,
            pallas_commitments: Vec::<GroupAffine<P1>>::deserialize(&mut reader)?,
            vesta_proof: R1CSProof::<GroupAffine<P2>>::deserialize(&mut reader)?,
            vesta_commitments: Vec::<GroupAffine<P2>>::deserialize(&mut reader)?,
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

pub struct SelRerandParameters<P1: SWModelParameters, P2: SWModelParameters> {
    // pub c1_pc_gens: PedersenGens<GroupAffine<P1>>,
    // pub c1_bp_gens: BulletproofGens<GroupAffine<P1>>,
    // pub c1_uh: UniversalHash<P1::BaseField>,
    // pub c1_blinding: GroupAffine<P1>, // todo is in pc_gens
    pub c1_tables: Vec<Lookup3Bit<2, P1::BaseField>>,
    pub c1_parameters: SingleLayerParameters<P1>,
    // pub c2_pc_gens: PedersenGens<GroupAffine<P2>>,
    // pub c2_bp_gens: BulletproofGens<GroupAffine<P2>>,
    // pub c2_uh: UniversalHash<P2::BaseField>,
    // pub c2_blinding: GroupAffine<P2>, // todo is in pc_gens
    pub c2_tables: Vec<Lookup3Bit<2, P2::BaseField>>,
    pub c2_parameters: SingleLayerParameters<P2>,
}

impl<P1: SWModelParameters, P2: SWModelParameters> SelRerandParameters<P1, P2> {
    pub fn new<R: Rng>(generators_length: usize, rng: &mut R) -> Self {
        let c1_pc_gens = PedersenGens::<GroupAffine<P1>>::default();
        let c1_bp_gens = BulletproofGens::<GroupAffine<P1>>::new(generators_length, 1);
        let c1_uh = UniversalHash::new(rng, P1::COEFF_A, P1::COEFF_B);
        let c1_parameters = SingleLayerParameters {
            bp_gens: BulletproofGens::<GroupAffine<P1>>::new(generators_length, 1),
            pc_gens: PedersenGens::<GroupAffine<P1>>::default(),
            uh: UniversalHash::new(rng, P1::COEFF_A, P1::COEFF_B),
        };
        let c2_parameters = SingleLayerParameters {
            bp_gens: BulletproofGens::<GroupAffine<P2>>::new(generators_length, 1),
            pc_gens: PedersenGens::<GroupAffine<P2>>::default(),
            uh: UniversalHash::new(rng, P2::COEFF_A, P2::COEFF_B),
        };
        let c1_blinding = c1_pc_gens.B_blinding;
        let c1_scalar_tables = build_tables(c1_blinding);
        let c2_pc_gens = PedersenGens::<GroupAffine<P2>>::default();
        let c2_bp_gens = BulletproofGens::<GroupAffine<P2>>::new(generators_length, 1);
        let c2_uh = UniversalHash::new(rng, P2::COEFF_A, P2::COEFF_B);
        let c2_blinding = c2_pc_gens.B_blinding;
        let c2_scalar_tables = build_tables(c2_blinding);
        SelRerandParameters {
            // c1_pc_gens: c1_pc_gens,
            // c1_bp_gens: c1_bp_gens,
            // c1_uh: c1_uh,
            c1_parameters: c1_parameters,
            // c1_blinding: c1_blinding,
            c1_tables: c1_scalar_tables,
            // c2_pc_gens: c2_pc_gens,
            // c2_bp_gens: c2_bp_gens,
            // c2_uh: c2_uh,
            c2_parameters: c2_parameters,
            // c2_blinding: c2_blinding,
            c2_tables: c2_scalar_tables,
        }
    }
}

// todo should only compile for benchmarks and tests
pub fn prove_from_mock_curve_tree<
    P1: SWModelParameters,
    P2: SWModelParameters<BaseField = P1::ScalarField, ScalarField = P1::BaseField>,
>(
    srp: &SelRerandParameters<P1, P2>,
) -> (SelRerandProof<P1, P2>) {
    let mut rng = rand::thread_rng();

    let pallas_pc_gens = &srp.c1_parameters.pc_gens;
    let pallas_bp_gens = &srp.c1_parameters.bp_gens;
    let pallas_uh = srp.c1_parameters.uh;
    let pallas_blinding = srp.c1_parameters.pc_gens.B_blinding;
    let pallas_scalar_tables = &srp.c1_tables;

    let vesta_pc_gens = &srp.c2_parameters.pc_gens;
    let vesta_bp_gens = &srp.c2_parameters.bp_gens;
    let vesta_uh = srp.c2_parameters.uh;
    let vesta_blinding = srp.c2_parameters.pc_gens.B_blinding;
    let vesta_scalar_tables = &srp.c2_tables;

    let mut pallas_transcript = Transcript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, GroupAffine<P1>> =
        Prover::new(pallas_pc_gens, &mut pallas_transcript);

    let mut vesta_transcript = Transcript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, GroupAffine<P2>> =
        Prover::new(vesta_pc_gens, &mut vesta_transcript);
    let (leaf, leaf_rerand, leaf_rerandomization_offset) = {
        // Let leaf be a random dummy commitment for which we want to prove the select and randomize relation.
        let leaf_val = P1::ScalarField::rand(&mut rng);
        let leaf_randomness = P1::ScalarField::rand(&mut rng);
        let leaf = pallas_pc_gens.commit(leaf_val, leaf_randomness);
        let (leaf, r) = pallas_uh.permissible_commitment(&leaf, &pallas_blinding);
        let leaf_randomness = leaf_randomness + r;
        assert_eq!(leaf, pallas_pc_gens.commit(leaf_val, leaf_randomness));
        let leaf_rerandomization_offset = P1::ScalarField::rand(&mut rng);
        // The rerandomization of the commitment to leaf is public.
        let leaf_rerand =
            pallas_pc_gens.commit(leaf_val, leaf_randomness + leaf_rerandomization_offset);
        (leaf, leaf_rerand, leaf_rerandomization_offset)
    };

    let (c0, c0_rerand, c0_rerandomization_offset, c0_rerand_vars) = {
        // Make a bunch of dummy commitments (random points) for the remaining leafs.
        let leaves: Vec<_> = iter::once(leaf.x)
            .chain(iter::from_fn(|| Some(P2::ScalarField::rand(&mut rng))).take(255))
            .collect();
        // Build the first internal node: a vector commitment to the leaves.
        let c0_r = P2::ScalarField::rand(&mut rng);
        let c0 = vector_commitment(leaves.as_slice(), c0_r, &vesta_bp_gens, &vesta_pc_gens);
        // The internal node must also be a permissable commitment.
        let (c0, r) = vesta_uh.permissible_commitment(&c0, &vesta_blinding);
        let c0_r = c0_r + r;
        let c0_rerandomization_offset = P2::ScalarField::rand(&mut rng);
        let (c0_rerand, c0_rerand_vars) = vesta_prover.commit_vec(
            leaves.as_slice(),
            c0_r + c0_rerandomization_offset,
            &vesta_bp_gens,
        );

        (c0, c0_rerand, c0_rerandomization_offset, c0_rerand_vars)
    };
    single_level_select_and_rerandomize(
        &mut vesta_prover,
        &pallas_uh,
        &pallas_scalar_tables,
        leaf_rerand,
        c0_rerand_vars,
        Some(0),
        Some(leaf),
        Some(leaf_rerandomization_offset),
    );
    let (c1, c1_rerand, c1_rerandomization_offset, c1_rerand_vars) = {
        // Make a bunch of dummy commitments (random points) for the remaining children.
        let rt1: Vec<_> = iter::once(c0.x)
            .chain(iter::from_fn(|| Some(P1::ScalarField::rand(&mut rng))).take(255))
            .collect();
        // Build the internal node: a vector commitment to the children.
        let c1_init_randomness = P1::ScalarField::rand(&mut rng);
        let c1 = vector_commitment(
            rt1.as_slice(),
            c1_init_randomness,
            &pallas_bp_gens,
            &pallas_pc_gens,
        );
        // Rerandomize the internal node to get a permissable point.
        let (c1, r) = pallas_uh.permissible_commitment(&c1, &pallas_blinding);
        let c1_permissable_randomness = c1_init_randomness + r;
        // Rerandomize the commitment so we can show membership without revealing the branch we are in.
        let c1_rerandomization_offset = P1::ScalarField::rand(&mut rng);
        let (c1_rerand, c1_rerand_vars) = pallas_prover.commit_vec(
            rt1.as_slice(),
            c1_permissable_randomness + c1_rerandomization_offset,
            &pallas_bp_gens,
        );
        (c1, c1_rerand, c1_rerandomization_offset, c1_rerand_vars)
    };
    single_level_select_and_rerandomize(
        &mut pallas_prover,
        &vesta_uh,
        &vesta_scalar_tables,
        c0_rerand,
        c1_rerand_vars,
        Some(0),
        Some(c0),
        Some(c0_rerandomization_offset),
    );
    let (c2, c2_rerand, c2_rerandomization_offset, c2_rerand_vars) = {
        // Make a bunch of dummy commitments (random points) for the remaining children.
        let rt2: Vec<_> = iter::once(c1.x)
            .chain(iter::from_fn(|| Some(P2::ScalarField::rand(&mut rng))).take(255))
            .collect();
        // Build the internal node: a vector commitment to the children.
        let c2_init_randomness = P2::ScalarField::rand(&mut rng);
        let c2 = vector_commitment(
            rt2.as_slice(),
            c2_init_randomness,
            &vesta_bp_gens,
            &vesta_pc_gens,
        );
        // Rerandomize the internal node to get a permissable point.
        let (c2, r) = vesta_uh.permissible_commitment(&c2, &vesta_blinding);
        let c2_permissable_randomness = c2_init_randomness + r;
        // Rerandomize the commitment so we can show membership without revealing the branch we are in.
        let c2_rerandomization_offset = P2::ScalarField::rand(&mut rng);
        let (c2_rerand, c2_rerand_vars) = vesta_prover.commit_vec(
            rt2.as_slice(),
            c2_permissable_randomness + c2_rerandomization_offset,
            &vesta_bp_gens,
        );
        (c2, c2_rerand, c2_rerandomization_offset, c2_rerand_vars)
    };
    single_level_select_and_rerandomize(
        &mut vesta_prover,
        &pallas_uh,
        &pallas_scalar_tables,
        c1_rerand,
        c2_rerand_vars,
        Some(0),
        Some(c1),
        Some(c1_rerandomization_offset),
    );

    let (c3, c3_vars) = {
        // Make a bunch of dummy commitments (random points) for the remaining children.
        let rt3: Vec<_> = iter::once(c2.x)
            .chain(iter::from_fn(|| Some(P1::ScalarField::rand(&mut rng))).take(255))
            .collect();
        // Build the internal node: a vector commitment to the children.
        let c3_init_randomness = P1::ScalarField::rand(&mut rng);
        let c3 = vector_commitment(
            rt3.as_slice(),
            c3_init_randomness,
            &pallas_bp_gens,
            &pallas_pc_gens,
        );
        // Rerandomize the internal node to get a permissable point.
        let (c3, r) = pallas_uh.permissible_commitment(&c3, &pallas_blinding);
        let c3_permissable_randomness = c3_init_randomness + r;
        // c3 is the root, and does not need to be hidden.
        let (c3_r, c3_vars) =
            pallas_prover.commit_vec(rt3.as_slice(), c3_permissable_randomness, &pallas_bp_gens);
        assert_eq!(c3, c3_r);
        (c3, c3_vars)
    };
    single_level_select_and_rerandomize(
        &mut pallas_prover,
        &vesta_uh,
        &vesta_scalar_tables,
        c2_rerand,
        c3_vars,
        Some(0),
        Some(c2),
        Some(c2_rerandomization_offset),
    );
    SelRerandProof {
        result: leaf_rerand,
        pallas_proof: pallas_prover.prove(&pallas_bp_gens).unwrap(),
        pallas_commitments: vec![c1_rerand, c3],
        vesta_proof: vesta_prover.prove(&vesta_bp_gens).unwrap(),
        vesta_commitments: vec![c0_rerand, c2_rerand],
    }
}

pub fn verification_circuit<
    P1: SWModelParameters,
    P2: SWModelParameters<BaseField = P1::ScalarField, ScalarField = P1::BaseField>,
>(
    sr_params: &SelRerandParameters<P1, P2>,
    sr_proof: &SelRerandProof<P1, P2>,
) -> (
    Verifier<Transcript, GroupAffine<P1>>,
    Verifier<Transcript, GroupAffine<P2>>,
) {
    let vesta_verifier = {
        // Verify the vesta proof
        let mut transcript = Transcript::new(b"select_and_rerandomize");
        let mut verifier = Verifier::new(transcript);
        let c0_rerand_vars = verifier.commit_vec(256, sr_proof.vesta_commitments[0]);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_params.c1_parameters.uh,
            &sr_params.c1_tables,
            sr_proof.result,
            c0_rerand_vars,
            None,
            None,
            None,
        );
        let c2_rerand_vars = verifier.commit_vec(256, sr_proof.vesta_commitments[1]);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_params.c1_parameters.uh,
            &sr_params.c1_tables,
            sr_proof.pallas_commitments[0],
            c2_rerand_vars,
            None,
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
            &sr_params.c2_parameters.uh,
            &sr_params.c2_tables,
            sr_proof.vesta_commitments[0],
            c1_rerand_vars,
            None,
            None,
            None,
        );
        let c3_vars = verifier.commit_vec(256, sr_proof.pallas_commitments[1]);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_params.c2_parameters.uh,
            &sr_params.c2_tables,
            sr_proof.vesta_commitments[1],
            c3_vars,
            None,
            None,
            None,
        );
        verifier
    };
    (pallas_verifier, vesta_verifier)
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
            &sr_params.c1_parameters.pc_gens,
            &sr_params.c1_parameters.bp_gens,
        );
        let v_res = vesta_verifier.verify(
            &sr_proof.vesta_proof,
            &sr_params.c2_parameters.pc_gens,
            &sr_params.c2_parameters.bp_gens,
        );
        assert_eq!(p_res, Ok(()));
        assert_eq!(v_res, Ok(()));
    }

    #[test]
    fn test_select_and_rerandomize_batched() {
        let mut rng = rand::thread_rng();
        let generators_length = 2 << 11; // minimum sufficient power of 2

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
            &sr_params.c1_parameters.pc_gens,
            &sr_params.c1_parameters.bp_gens,
        );
        let v_res = batch_verify(
            vec![
                vesta_verification_scalars_and_points,
                vesta_verification_scalars_and_points2,
            ],
            &sr_params.c2_parameters.pc_gens,
            &sr_params.c2_parameters.bp_gens,
        );
        assert_eq!(p_res, Ok(()));
        assert_eq!(v_res, Ok(()));
    }

    // todo could add a test with branching facter 1 to test correctness w.o. vector commitments.
}
