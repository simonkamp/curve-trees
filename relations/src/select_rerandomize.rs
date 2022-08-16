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
use ark_std::{One, UniformRand, Zero};
use merlin::Transcript;
use std::{borrow::BorrowMut, iter, marker::PhantomData};

pub struct SelectAndRerandomizeParameters<Fs: SquareRootField> {
    uh: UniversalHash<Fs>,
    tables: Vec<Lookup3Bit<2, Fs>>,
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

#[cfg(test)]
mod tests {
    use super::*;

    use ark_std::UniformRand;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;

    use rand::thread_rng;
    use rand::Rng;

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
        pub c1_pc_gens: PedersenGens<GroupAffine<P1>>,
        pub c1_bp_gens: BulletproofGens<GroupAffine<P1>>,
        pub c1_uh: UniversalHash<P1::BaseField>,
        pub c1_blinding: GroupAffine<P1>, // todo is in pc_gens
        pub c1_tables: Vec<Lookup3Bit<2, P1::BaseField>>,
        pub c2_pc_gens: PedersenGens<GroupAffine<P2>>,
        pub c2_bp_gens: BulletproofGens<GroupAffine<P2>>,
        pub c2_uh: UniversalHash<P2::BaseField>,
        pub c2_blinding: GroupAffine<P2>, // todo is in pc_gens
        pub c2_tables: Vec<Lookup3Bit<2, P2::BaseField>>,
    }

    impl<P1: SWModelParameters, P2: SWModelParameters> SelRerandParameters<P1, P2> {
        pub fn new<R: Rng>(generators_length: usize, rng: &mut R) -> Self {
            let c1_pc_gens = PedersenGens::<GroupAffine<P1>>::default();
            let c1_bp_gens = BulletproofGens::<GroupAffine<P1>>::new(generators_length, 1);
            let c1_uh = UniversalHash::new(rng, P1::COEFF_A, P1::COEFF_B);
            let c1_blinding = c1_pc_gens.B_blinding;
            let c1_scalar_tables = build_tables(c1_blinding);
            let c2_pc_gens = PedersenGens::<GroupAffine<P2>>::default();
            let c2_bp_gens = BulletproofGens::<GroupAffine<P2>>::new(generators_length, 1);
            let c2_uh = UniversalHash::new(rng, P2::COEFF_A, P2::COEFF_B);
            let c2_blinding = c2_pc_gens.B_blinding;
            let c2_scalar_tables = build_tables(c2_blinding);
            SelRerandParameters {
                c1_pc_gens: c1_pc_gens,
                c1_bp_gens: c1_bp_gens,
                c1_uh: c1_uh,
                c1_blinding: c1_blinding,
                c1_tables: c1_scalar_tables,
                c2_pc_gens: c2_pc_gens,
                c2_bp_gens: c2_bp_gens,
                c2_uh: c2_uh,
                c2_blinding: c2_blinding,
                c2_tables: c2_scalar_tables,
            }
        }
    }

    fn prove(
        srp: &SelRerandParameters<PallasParameters, VestaParameters>,
    ) -> (SelRerandProof<PallasParameters, VestaParameters>) {
        let mut rng = rand::thread_rng();

        let pallas_pc_gens = &srp.c1_pc_gens;
        let pallas_bp_gens = &srp.c1_bp_gens;
        let pallas_uh = srp.c1_uh;
        let pallas_blinding = srp.c1_blinding;
        let pallas_scalar_tables = &srp.c1_tables;

        let vesta_pc_gens = &srp.c2_pc_gens;
        let vesta_bp_gens = &srp.c2_bp_gens;
        let vesta_uh = srp.c2_uh;
        let vesta_blinding = srp.c2_blinding;
        let vesta_scalar_tables = &srp.c2_tables;

        let mut pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, PallasA> =
            Prover::new(&pallas_pc_gens, &mut pallas_transcript);

        let mut vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, VestaA> =
            Prover::new(&vesta_pc_gens, &mut vesta_transcript);
        let (leaf, leaf_rerand, leaf_rerandomization_offset) = {
            // Let leaf be a random dummy commitment for which we want to prove the select and randomize relation.
            let leaf_val = PallasScalar::rand(&mut rng);
            let leaf_randomness = PallasScalar::rand(&mut rng);
            let leaf = pallas_pc_gens.commit(leaf_val, leaf_randomness);
            let (leaf, r) = pallas_uh.permissible_commitment(&leaf, &pallas_blinding);
            let leaf_randomness = leaf_randomness + r;
            assert_eq!(leaf, pallas_pc_gens.commit(leaf_val, leaf_randomness));
            let leaf_rerandomization_offset = PallasScalar::rand(&mut rng);
            // The rerandomization of the commitment to leaf is public.
            let leaf_rerand =
                pallas_pc_gens.commit(leaf_val, leaf_randomness + leaf_rerandomization_offset);
            (leaf, leaf_rerand, leaf_rerandomization_offset)
        };

        let (c0, c0_rerand, c0_rerandomization_offset, c0_rerand_vars) = {
            // Make a bunch of dummy commitments (random points) for the remaining leafs.
            let leaves: Vec<_> = iter::once(leaf.x)
                .chain(iter::from_fn(|| Some(VestaScalar::rand(&mut rng))).take(255))
                .collect();
            // Build the first internal node: a vector commitment to the leaves.
            let c0_r = VestaScalar::rand(&mut rng);
            let c0 = vector_commitment(leaves.as_slice(), c0_r, &vesta_bp_gens, &vesta_pc_gens);
            // The internal node must also be a permissable commitment.
            let (c0, r) = vesta_uh.permissible_commitment(&c0, &vesta_blinding);
            let c0_r = c0_r + r;
            let c0_rerandomization_offset = VestaScalar::rand(&mut rng);
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
                .chain(iter::from_fn(|| Some(PallasScalar::rand(&mut rng))).take(255))
                .collect();
            // Build the internal node: a vector commitment to the children.
            let c1_init_randomness = PallasScalar::rand(&mut rng);
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
            let c1_rerandomization_offset = PallasScalar::rand(&mut rng);
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
                .chain(iter::from_fn(|| Some(VestaScalar::rand(&mut rng))).take(255))
                .collect();
            // Build the internal node: a vector commitment to the children.
            let c2_init_randomness = VestaScalar::rand(&mut rng);
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
            let c2_rerandomization_offset = VestaScalar::rand(&mut rng);
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
                .chain(iter::from_fn(|| Some(PallasScalar::rand(&mut rng))).take(255))
                .collect();
            // Build the internal node: a vector commitment to the children.
            let c3_init_randomness = PallasScalar::rand(&mut rng);
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
            let (c3_r, c3_vars) = pallas_prover.commit_vec(
                rt3.as_slice(),
                c3_permissable_randomness,
                &pallas_bp_gens,
            );
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
            pallas_commitments: [c1_rerand, c3],
            vesta_proof: vesta_prover.prove(&vesta_bp_gens).unwrap(),
            vesta_commitments: [c0_rerand, c2_rerand],
        }
    }

    pub struct SelRerandProof<P1: SWModelParameters, P2: SWModelParameters> {
        pub result: GroupAffine<P1>,
        pub pallas_proof: R1CSProof<GroupAffine<P1>>,
        pub pallas_commitments: [GroupAffine<P1>; 2],
        pub vesta_proof: R1CSProof<GroupAffine<P2>>,
        pub vesta_commitments: [GroupAffine<P2>; 2],
    }

    fn verification_circuit(
        sr_params: &SelRerandParameters<PallasParameters, VestaParameters>,
        sr_proof: &SelRerandProof<PallasParameters, VestaParameters>,
    ) -> (Verifier<Transcript, PallasA>, Verifier<Transcript, VestaA>) {
        let vesta_verifier = {
            // Verify the vesta proof
            let mut transcript = Transcript::new(b"select_and_rerandomize");
            let mut verifier = Verifier::new(transcript);
            let c0_rerand_vars = verifier.commit_vec(256, sr_proof.vesta_commitments[0]);
            single_level_select_and_rerandomize(
                &mut verifier,
                &sr_params.c1_uh,
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
                &sr_params.c1_uh,
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
                &sr_params.c2_uh,
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
                &sr_params.c2_uh,
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

    #[test]
    fn test_select_and_rerandomize_single() {
        let mut rng = rand::thread_rng();
        let generators_length = 2 << 11; // minimum sufficient power of 2

        let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            &mut rng,
        );

        // test single verification:
        let sr_proof = prove(&sr_params);
        let (pallas_verifier, vesta_verifier) = verification_circuit(&sr_params, &sr_proof);
        let p_res = pallas_verifier.verify(
            &sr_proof.pallas_proof,
            &sr_params.c1_pc_gens,
            &sr_params.c1_bp_gens,
        );
        let v_res = vesta_verifier.verify(
            &sr_proof.vesta_proof,
            &sr_params.c2_pc_gens,
            &sr_params.c2_bp_gens,
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
        let sr_proof = prove(&sr_params);
        let (pallas_verifier, vesta_verifier) = verification_circuit(&sr_params, &sr_proof);
        let sr_proof2 = prove(&sr_params);
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
            &sr_params.c1_pc_gens,
            &sr_params.c1_bp_gens,
        );
        let v_res = batch_verify(
            vec![
                vesta_verification_scalars_and_points,
                vesta_verification_scalars_and_points2,
            ],
            &sr_params.c2_pc_gens,
            &sr_params.c2_bp_gens,
        );
        assert_eq!(p_res, Ok(()));
        assert_eq!(v_res, Ok(()));
    }

    // todo could add a test with branching facter 1 to test correctness w.o. vector commitments.
}
