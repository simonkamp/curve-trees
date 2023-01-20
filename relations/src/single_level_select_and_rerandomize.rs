use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use crate::curve::{checked_curve_addition_helper, PointRepresentation};
use crate::lookup::*;
use crate::permissible::*;
use crate::rerandomize::*;
use crate::select::*;

use ark_ec::{
    models::short_weierstrass_jacobian::GroupAffine, msm::VariableBaseMSM, ProjectiveCurve,
    SWModelParameters,
};
use ark_ff::{PrimeField, SquareRootField};
use ark_std::Zero;
use rand::Rng;
use std::iter;
use std::marker::PhantomData;

pub struct SingleLayerParameters<P: SWModelParameters> {
    pub bp_gens: BulletproofGens<GroupAffine<P>>,
    pub pc_gens: PedersenGens<GroupAffine<P>>,
    pub uh: UniversalHash<P::BaseField>,
    pub tables: Vec<Lookup3Bit<2, P::BaseField>>,
}

impl<P: SWModelParameters> SingleLayerParameters<P> {
    pub fn new<R: Rng, P1: SWModelParameters>(generators_length: usize, rng: &mut R) -> Self {
        let pc_gens = PedersenGens::<GroupAffine<P>>::default();
        let tables = build_tables(pc_gens.B_blinding);

        SingleLayerParameters {
            bp_gens: BulletproofGens::<GroupAffine<P>>::new(generators_length, 1),
            pc_gens,
            uh: UniversalHash::new(rng, P::COEFF_A, P::COEFF_B),
            tables,
        }
    }

    // todo refactor with bases as parameter for stackable curve trees (independent generators)
    pub fn commit(&self, v: &[P::ScalarField], v_blinding: P::ScalarField) -> GroupAffine<P> {
        let gens = self.bp_gens.share(0);

        let generators: Vec<_> = iter::once(&self.pc_gens.B_blinding)
            .chain(gens.G(v.len()))
            .cloned()
            .collect::<Vec<_>>();

        let scalars: Vec<<P::ScalarField as PrimeField>::BigInt> = iter::once(&v_blinding)
            .chain(v.iter())
            .map(|s| {
                let s: <P::ScalarField as PrimeField>::BigInt = (*s).into();
                s
            })
            .collect();

        assert_eq!(generators.len(), scalars.len());

        let comm = VariableBaseMSM::multi_scalar_mul(generators.as_slice(), scalars.as_slice());
        comm.into_affine()
    }

    pub fn permissible_commitment(
        &self,
        v: &[P::ScalarField],
        v_blinding: P::ScalarField,
    ) -> (GroupAffine<P>, P::ScalarField) {
        let commitment = self.commit(v, v_blinding);
        let (permissible_commitment, offset) = self
            .uh
            .permissible_commitment(&commitment, &self.pc_gens.B_blinding);
        (permissible_commitment, v_blinding + offset)
    }
}

/// Circuit for the single level version of the select and rerandomize relation.
pub fn single_level_select_and_rerandomize<
    Fb: SquareRootField,
    Fs: SquareRootField,
    C2: SWModelParameters<BaseField = Fs, ScalarField = Fb>,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerParameters<C2>,
    rerandomized: &GroupAffine<C2>, // The public rerandomization of the selected child
    c0_vars: Vec<Variable<Fs>>, // Variables representing members of the (parent) vector commitment
    selected_witness: Option<GroupAffine<C2>>, // Witness of the commitment being selected and rerandomized
    randomness_offset: Option<Fb>, // The scalar used for randomizing, i.e. selected_witness * randomness_offset = rerandomized
) {
    let x_var = cs.allocate(selected_witness.map(|xy| xy.x)).unwrap();
    let y_var = cs.allocate(selected_witness.map(|xy| xy.y)).unwrap();
    // Show that the parent is committed to the child's x-coordinate
    select(
        cs,
        x_var.into(),
        c0_vars.into_iter().map(|v| v.into()).collect(),
    );
    // Proof that the child is a permissible point
    parameters
        .uh
        .permissible_gadget(cs, x_var.into(), selected_witness.map(|xy| xy.y), y_var);
    // Show that `rerandomized` is a rerandomization of the selected child
    re_randomize(
        cs,
        &parameters.tables,
        x_var.into(),
        y_var.into(),
        constant(rerandomized.x),
        constant(rerandomized.y),
        selected_witness,
        randomness_offset,
    );
}

/// Circuit for the single level version of the batched select and rerandomize relation.
/// Facilitates showing M instances of the select and rerandomize relation with only a single rerandomization.
pub fn single_level_batched_select_and_rerandomize<
    Fb: SquareRootField,
    Fs: SquareRootField,
    C2: SWModelParameters<BaseField = Fs, ScalarField = Fb>,
    Cs: ConstraintSystem<Fs>,
    const M: usize, // The number of parallel selections
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerParameters<C2>,
    rerandomized: GroupAffine<C2>, // The public rerandomization of the sum of selected children
    c0_vars: Vec<Variable<Fs>>, // Variables representing members of the vector commitment (i.e. the sum of M parents)
    selected_witnesses: Option<[&GroupAffine<C2>; M]>, // Witnesses of the commitments being selected and rerandomized
    randomness_offset: Option<Fb>, // The scalar used for randomizing, i.e. \sum selected_witnesses * randomness_offset = rerandomized
) {
    // Initialize the accumulated sum of the selected children to dummy values.
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        witness: selected_witnesses.map(|_| (GroupAffine::<C2>::zero())),
    };
    // Split the variables of the vector commitments into section corresponding to the M parents.
    let chunks = c0_vars.chunks_exact(c0_vars.len() / M);
    let mut i = 0;
    for chunk in chunks {
        let ith_selected_witness = selected_witnesses.map(|xy| *xy[i]);
        let x_var = cs.allocate(ith_selected_witness.map(|xy| xy.x)).unwrap();
        let y_var = cs.allocate(ith_selected_witness.map(|xy| xy.y)).unwrap();
        let ith_selected = PointRepresentation {
            x: x_var.into(),
            y: y_var.into(),
            witness: ith_selected_witness,
        };
        // Show that the parent is committed to the ith child's x-coordinate
        select(
            cs,
            x_var.into(),
            chunk
                .into_iter()
                .map(|v| LinearCombination::<Fs>::from(*v))
                .collect(),
        );
        // Proof that the child is a permissible point
        parameters.uh.permissible_gadget(
            cs,
            x_var.into(),
            selected_witnesses.map(|xy| xy[i].y),
            y_var,
        );

        if i == 0 {
            // In the first iteration, the sum is the single selected child.
            sum_of_selected = ith_selected;
        } else {
            // Add the extracted point to the accumulated sum
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected);
        }
        i += 1;
    }
    // Show that `rerandomized`, is a rerandomization of sum of the selected children
    re_randomize(
        cs,
        &parameters.tables,
        sum_of_selected.x,
        sum_of_selected.y,
        constant(rerandomized.x),
        constant(rerandomized.y),
        sum_of_selected.witness,
        randomness_offset,
    );
}
