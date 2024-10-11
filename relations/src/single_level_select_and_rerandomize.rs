use ark_serialize::CanonicalSerialize;
use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use crate::curve::{checked_curve_addition_helper, curve_check, PointRepresentation};
use crate::lookup::*;
use crate::rerandomize::*;
use crate::select::*;

use ark_ec::{
    models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, AffineRepr, CurveGroup,
    VariableBaseMSM,
};
use ark_ff::{Field, PrimeField, UniformRand};
use rand::Rng;
use std::iter;
use std::marker::PhantomData;

pub struct SingleLayerParameters<P: SWCurveConfig + Copy> {
    pub bp_gens: BulletproofGens<Affine<P>>,
    pub pc_gens: PedersenGens<Affine<P>>,
    pub delta: Affine<P>,
    pub coeff_a: P::BaseField,
    pub coeff_b: P::BaseField,
    pub tables: Vec<Lookup3Bit<2, P::BaseField>>,
}

impl<P: SWCurveConfig + Copy> SingleLayerParameters<P> {
    pub fn new<R: Rng, P1: SWCurveConfig>(generators_length: usize, rng: &mut R) -> Self {
        let pc_gens = PedersenGens::<Affine<P>>::default();
        let tables = build_tables(pc_gens.B_blinding);

        SingleLayerParameters {
            bp_gens: BulletproofGens::<Affine<P>>::new(generators_length, 1),
            pc_gens,
            delta: Affine::<P>::rand(rng), // todo choose as a hash to be convincingly independent from all generators in the commitment
            coeff_a: P::COEFF_A,
            coeff_b: P::COEFF_B,
            tables,
        }
    }

    pub fn commit(
        &self,
        v: &[P::ScalarField],
        v_blinding: P::ScalarField,
        generator_set_index: usize,
    ) -> Affine<P> {
        let gens = self
            .bp_gens
            .share(0)
            .G(v.len() * (generator_set_index + 1))
            .skip(v.len() * generator_set_index);

        let generators: Vec<_> = iter::once(&self.pc_gens.B_blinding)
            .chain(gens)
            .copied()
            .collect::<Vec<_>>();

        let scalars: Vec<P::ScalarField> = iter::once(&v_blinding)
            .chain(v.iter())
            .map(|s| {
                let s: P::ScalarField = *s;
                s
            })
            .collect();

        let comm = <Affine<P> as AffineRepr>::Group::msm(generators.as_slice(), scalars.as_slice());
        comm.unwrap().into_affine()
    }
}

/// Circuit for the single level select and rerandomize relation.
pub fn single_level_select_and_rerandomize<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerParameters<C2>,
    rerandomized_child: &Affine<C2>, // The public rerandomization of the selected child without Delta
    children: Vec<LinearCombination<Fs>>, // Variables representing members of the (parent) vector commitment
    child_plus_delta: Option<Affine<C2>>, // Witness of the selected child plus Delta
    randomness_offset: Option<Fb>, // The scalar used for randomizing, i.e. child + randomness_offset * H = rerandomized_child + Delta
) {
    // Add the rerandomised child to the transcript
    {
        // TODO: clean this up. The transcript in CS should be restricted restricted to `ProtocolTranscript'
        let mut bytes = Vec::new();
        if let Err(e) = rerandomized_child.serialize_compressed(&mut bytes) {
            panic!("{}", e)
        }
        cs.transcript()
            .append_message(b"rerandomized_child", &bytes);
    }

    // Show that the parent is committed to the witnessed child's x-coordinate
    let x_var = cs.allocate(child_plus_delta.map(|xy| xy.x)).unwrap();
    select(cs, x_var.into(), children.iter().cloned());

    // Proof that the opened x coordinate with the witnessed y is a point on the curve
    // Note that empty branches are encoded as 0 which works because x=0 does not satisfy the curve equation for any of the curves used.
    let y_var = cs.allocate(child_plus_delta.map(|xy| xy.y)).unwrap();
    curve_check(
        cs,
        x_var.into(),
        y_var.into(),
        parameters.coeff_a,
        parameters.coeff_b,
    );

    // Show that `rerandomized_child` is a rerandomization of the selected child
    let rerandomized_child_plus_delta = (*rerandomized_child + parameters.delta).into_affine();
    re_randomize(
        cs,
        &parameters.tables,
        PointRepresentation {
            x: x_var.into(),
            y: y_var.into(),
            witness: child_plus_delta,
        },
        constant(rerandomized_child_plus_delta.x),
        constant(rerandomized_child_plus_delta.y),
        randomness_offset,
    );
}

/// Circuit for the single level version of the batched select and rerandomize relation.
/// Facilitates showing M instances of the select and rerandomize relation with only a single rerandomization.
pub fn single_level_batched_select_and_rerandomize<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
    const M: usize, // The number of parallel selections
>(
    cs: &mut Cs, // Prover or verifier
    parameters: &SingleLayerParameters<C2>,
    sum_of_rerandomized: &Affine<C2>, // The public rerandomization of the sum of selected children
    children: Vec<LinearCombination<Fs>>, // Variables representing members of the combined and rerandomized parent vector commitment (i.e. the rerandomized sum of M parents)
    children_plus_delta: Option<&[Affine<C2>; M]>, // Witnesses of the commitments being selected and rerandomized
    randomness_offset: Option<Fb>, // The scalar used for randomizing, i.e. \sum selected_witnesses + randomness_offset * H = sum_of_rerandomized + M * Delta
) {
    // Initialize the accumulated sum of the selected children to dummy values.
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        witness: children_plus_delta.map(|_| (Affine::<C2>::zero())),
    };
    // Split the variables of the vector commitments into chunks corresponding to the M parents.
    let chunks = children.chunks_exact(children.len() / M);
    for (i, chunk) in chunks.enumerate() {
        let ith_selected_witness = children_plus_delta.map(|xy| xy[i]);
        let x_var = cs.allocate(ith_selected_witness.map(|xy| xy.x)).unwrap();
        let y_var = cs.allocate(ith_selected_witness.map(|xy| xy.y)).unwrap();
        let ith_selected = PointRepresentation {
            x: x_var.into(),
            y: y_var.into(),
            witness: ith_selected_witness,
        };
        // Show that the parent is committed to the ith child's x-coordinate
        select(cs, x_var.into(), chunk.iter().cloned());

        // Proof that the opened x coordinate with the witnessed y is a point on the curve
        // Note that empty branches are encoded as 0 which works because x=0 does not satisfy the curve equation for any of the curves used.
        curve_check(
            cs,
            x_var.into(),
            y_var.into(),
            parameters.coeff_a,
            parameters.coeff_b,
        );

        // Update the cumulated sum of selected children
        if i == 0 {
            // In the first iteration, the sum is the first selected child.
            sum_of_selected = ith_selected;
        } else {
            // In the consecutive iterations, add the ith selected child to the accumulated sum
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected);
        }
    }
    // Add M*Delta to the public sum of the children
    let shifted_rerandomized =
        (*sum_of_rerandomized + (parameters.delta * C2::ScalarField::from(M as u32))).into_affine();
    // Show that `rerandomized`, is a rerandomization of sum of the selected children
    re_randomize(
        cs,
        &parameters.tables,
        sum_of_selected,
        constant(shifted_rerandomized.x),
        constant(shifted_rerandomized.y),
        randomness_offset,
    );
}

#[cfg(test)]
mod tests {
    use crate::curve_tree::SelRerandParameters;

    use super::*;

    use ark_ec::AffineRepr;
    use ark_std::UniformRand;
    use merlin::Transcript;

    type PallasA = ark_pallas::Affine;
    type PallasScalar = <PallasA as AffineRepr>::ScalarField;
    type VestaA = ark_vesta::Affine;
    type VestaScalar = <VestaA as AffineRepr>::ScalarField;

    #[test]
    fn test_single_level() {
        let mut rng = rand::thread_rng();
        let generators_length = 1 << 12;

        let sr_params =
            SelRerandParameters::<ark_pallas::PallasConfig, ark_vesta::VestaConfig>::new(
                generators_length,
                generators_length,
                &mut rng,
            );

        // Test of selecting and rerandomizing a dummy commitment `child'
        let child = ark_pallas::Affine::rand(&mut rng);

        // Parent is a commitment to the x coordinate of the children where Delta is added to each child.
        let child_plus_delta = (child + sr_params.even_parameters.delta).into_affine();
        let child_plus_delta_x = *child_plus_delta.x().unwrap();
        let xs = vec![child_plus_delta_x];
        let blinding = VestaScalar::rand(&mut rng);
        let parent = sr_params.odd_parameters.commit(xs.as_slice(), blinding, 0);

        // Rerandomize the child
        let rerandomization = PallasScalar::rand(&mut rng);
        let rerandomized_child =
            child + (sr_params.even_parameters.pc_gens.B_blinding * rerandomization);

        let proof = {
            let mut transcript: Transcript =
                Transcript::new(b"single_level_select_and_rerandomize");
            let mut prover: Prover<_, VestaA> =
                Prover::new(&sr_params.odd_parameters.pc_gens, &mut transcript);

            let (xs_comm, xs_vars) =
                prover.commit_vec(xs.as_slice(), blinding, &sr_params.odd_parameters.bp_gens);
            assert_eq!(xs_comm, parent);

            single_level_select_and_rerandomize(
                &mut prover,
                &sr_params.even_parameters,
                &rerandomized_child.into_affine(),
                xs_vars.into_iter().map(|x| x.into()).collect(),
                Some(child_plus_delta),
                Some(rerandomization),
            );
            let proof = prover.prove(&sr_params.odd_parameters.bp_gens).unwrap();
            proof
        };

        let mut transcript: Transcript = Transcript::new(b"single_level_select_and_rerandomize");
        let mut verifier = Verifier::<_, VestaA>::new(&mut transcript);
        let xs_vars = verifier.commit_vec(1, parent);
        single_level_select_and_rerandomize(
            &mut verifier,
            &sr_params.even_parameters,
            &rerandomized_child.into_affine(),
            xs_vars.into_iter().map(|x| x.into()).collect(),
            None,
            None,
        );

        let res = verifier.verify(
            &proof,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
        );
        assert_eq!(res, Ok(()))
    }

    #[test]
    fn test_single_level_batched() {
        let mut rng = rand::thread_rng();
        let generators_length = 1 << 12;

        let sr_params =
            SelRerandParameters::<ark_pallas::PallasConfig, ark_vesta::VestaConfig>::new(
                generators_length,
                generators_length,
                &mut rng,
            );

        const M: usize = 2;
        let arity = 32;
        let children: Vec<_> = iter::from_fn(|| Some(PallasA::rand(&mut rng)))
            .take(M * arity)
            .collect();
        // Pick M children
        let child_index_1 = 3;
        let child_index_2 = arity + 7;
        assert_ne!(children[child_index_1], children[child_index_2]);

        let children_plus_delta: Vec<_> = children
            .iter()
            .map(|child| (*child + sr_params.even_parameters.delta).into_affine())
            .collect();
        let xs: Vec<_> = children_plus_delta
            .iter()
            .map(|child_plus_delta| *child_plus_delta.x().unwrap())
            .collect();
        let blinding = VestaScalar::rand(&mut rng);
        let parent = sr_params.odd_parameters.commit(xs.as_slice(), blinding, 0);

        // Rerandomize the selected children
        let rerandomization_1 = PallasScalar::rand(&mut rng);
        let rerandomized_child_1 = (children[child_index_1]
            + (sr_params.even_parameters.pc_gens.B_blinding * rerandomization_1))
            .into_affine();

        let rerandomization_2 = PallasScalar::rand(&mut rng);
        let rerandomized_child_2 = (children[child_index_2]
            + (sr_params.even_parameters.pc_gens.B_blinding * rerandomization_2))
            .into_affine();

        let rerandomized_sum = (rerandomized_child_1 + rerandomized_child_2).into_affine();

        let proof = {
            let mut transcript: Transcript =
                Transcript::new(b"single_level_select_and_rerandomize");
            let mut prover: Prover<_, VestaA> =
                Prover::new(&sr_params.odd_parameters.pc_gens, &mut transcript);

            let (xs_comm, xs_vars) =
                prover.commit_vec(xs.as_slice(), blinding, &sr_params.odd_parameters.bp_gens);
            assert_eq!(xs_comm, parent);

            single_level_batched_select_and_rerandomize(
                &mut prover,
                &sr_params.even_parameters,
                &rerandomized_sum,
                xs_vars.into_iter().map(|x| x.into()).collect(),
                Some(&[
                    children_plus_delta[child_index_1],
                    children_plus_delta[child_index_2],
                ]),
                Some(rerandomization_1 + rerandomization_2),
            );
            let proof = prover.prove(&sr_params.odd_parameters.bp_gens).unwrap();
            proof
        };

        let mut transcript: Transcript = Transcript::new(b"single_level_select_and_rerandomize");
        let mut verifier = Verifier::<_, VestaA>::new(&mut transcript);
        let xs_vars = verifier.commit_vec(M * arity, parent);
        single_level_batched_select_and_rerandomize(
            &mut verifier,
            &sr_params.even_parameters,
            &rerandomized_sum,
            xs_vars.into_iter().map(|x| x.into()).collect(),
            None::<&[PallasA; M]>,
            None,
        );

        let res = verifier.verify(
            &proof,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
        );
        assert_eq!(res, Ok(()))
    }
}
