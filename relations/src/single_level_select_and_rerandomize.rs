use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use crate::lookup::*;
use crate::permissible::*;
use crate::rerandomize::*;
use crate::select::*;

use ark_ec::{
    models::short_weierstrass_jacobian::GroupAffine, msm::VariableBaseMSM, ProjectiveCurve,
    SWModelParameters,
};
use ark_ff::{PrimeField, SquareRootField};
use rand::Rng;
use std::iter;

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

pub fn single_level_select_and_rerandomize<
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
    let y_var = cs.allocate(xy_witness.map(|xy| xy.y)).unwrap();
    // show that leaf is in c0
    select(
        cs,
        x_var.into(),
        c0_vars.into_iter().map(|v| v.into()).collect(),
    );
    // proof that l0 is a permissible
    parameters
        .uh
        .permissible_gadget(cs, x_var.into(), xy_witness.map(|xy| xy.y), y_var);
    // show that leaf_rerand, is a rerandomization of leaf
    re_randomize(
        cs,
        &parameters.tables,
        x_var.into(),
        y_var.into(),
        constant(rerandomized.x),
        constant(rerandomized.y),
        xy_witness,
        randomness_offset,
    );
}
