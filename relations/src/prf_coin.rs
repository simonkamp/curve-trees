use std::ops::Mul;

use bulletproofs::r1cs::*;
use digest::generic_array::typenum::Gr;
use merlin::Transcript;
use rand::Rng;

use crate::{coin, select_and_rerandomize::*};

use ark_ec::{
    models::short_weierstrass_jacobian::GroupAffine, AffineCurve, ProjectiveCurve,
    SWModelParameters,
};
use ark_ff::{Field, PrimeField, ToBytes};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::{UniformRand, Zero};

/// A public key is a rerandomizable commitment to a secret prf key
#[derive(Clone, Copy)]
pub struct PublicKey<P: SWModelParameters>(pub GroupAffine<P>);

/// A secret key consists of the secret scalar
#[derive(Clone, Copy)]
pub struct SecretKey<P: SWModelParameters> {
    pub prf_key: P::ScalarField,
    pub randomness: P::ScalarField, // could this just be zero?
}

pub struct Coin<
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField> + Clone,
> {
    pub value: u64,
    pub value_randomness: P0::ScalarField, // the randomness used to commit to the value of the coin (before combining the value and pk)
    pub pk_randomness: P1::ScalarField, // the randomness used to randomize the public key, needed for the receivers signature
}

impl<P0, P1> Coin<P0, P1>
where
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    P0::BaseField: PrimeField,
{
    pub fn mint<R: Rng>(
        value: u64,
        pk: &PublicKey<P1>,
        sr_parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
        prover: &mut Prover<Transcript, GroupAffine<P0>>,
    ) -> (
        Coin<P0, P1>,
        GroupAffine<P0>,
        GroupAffine<P1>,
        Variable<P0::ScalarField>,
    ) {
        let (coin, _, rerandomized_pk) = Self::new(value, pk, sr_parameters, rng);

        let (value_commitment, variables) = prover.commit_vec(
            &[P0::ScalarField::from(value)],
            coin.value_randomness,
            &sr_parameters.c0_parameters.bp_gens,
        );
        range_proof(prover, variables[0].into(), Some(value), 64).unwrap(); // todo what range do we want to enforce? Table of benchmarks for different powers?

        (coin, value_commitment, rerandomized_pk, variables[0])
    }

    pub fn new<R: Rng>(
        value: u64,
        pk: &PublicKey<P1>,
        sr_parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (Coin<P0, P1>, GroupAffine<P0>, GroupAffine<P1>) {
        let pk_rerandomization = P1::ScalarField::rand(rng);
        let randomized_pk = Self::rerandomized_pk(pk, &pk_rerandomization, sr_parameters);

        let value_randomness = P0::ScalarField::rand(rng);
        let value_commitment = sr_parameters
            .c0_parameters
            .commit(&[P0::ScalarField::from(value)], value_randomness);

        (
            Coin {
                value,
                value_randomness,
                pk_randomness: pk_rerandomization,
            },
            value_commitment,
            randomized_pk.0,
        )
    }

    /// Used to hash the commitment to the value of the coin into the scalarfield of the `odd curve`
    /// in order to homomorphically add it to the commitment to the PRF key, i.e. the public key.
    fn hash_of_value_commitment(value_commitment: GroupAffine<P0>) -> P1::ScalarField {
        let mut bytes = Vec::new();
        value_commitment.write(&mut bytes).unwrap();
        element_from_bytes_stat::<P1::ScalarField>(&bytes)
    }

    pub fn rerandomized_pk(
        pk: &PublicKey<P1>,
        rerandomization: &P1::ScalarField,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> PublicKey<P1> {
        PublicKey(
            pk.0 + parameters
                .c1_parameters
                .pc_gens
                .B_blinding
                .mul(*rerandomization)
                .into_affine(),
        )
    }

    pub fn combine_into_permissible(
        rerandomized_pk: GroupAffine<P1>,
        value_commitment: GroupAffine<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> PermissibleCoinFromTxAndPK<P0, P1> {
        let hash_of_value_commitments = Self::hash_of_value_commitment(value_commitment);
        // the secret key uses the generator for single value commitments
        let g_to_hash = parameters
            .c1_parameters
            .pc_gens
            .B
            .mul(hash_of_value_commitments);
        let pre_permissible_pk = rerandomized_pk + g_to_hash.into_affine();
        let (permissible_pk, r_permissible_pk) =
            parameters.c1_parameters.uh.permissible_commitment(
                &pre_permissible_pk,
                &parameters.c1_parameters.pc_gens.B_blinding,
            );
        let pk_x = permissible_pk.x;
        // the prf component uses the second generator of a vector commitment
        let prf_generator = parameters
            .c0_parameters
            .bp_gens
            .share(0)
            .G(2)
            .collect::<Vec<_>>()[1]; // todo: not this unreadable garbage
        let per_permissible_coin = value_commitment + prf_generator.mul(pk_x).into();
        let (permissible_coin, r_permissible_coin) =
            parameters.c0_parameters.uh.permissible_commitment(
                &per_permissible_coin,
                &parameters.c0_parameters.pc_gens.B_blinding,
            );
        PermissibleCoinFromTxAndPK {
            permissible_pk,
            r_permissible_pk,
            permissible_coin,
            r_permissible_coin,
        } // todo only permissible_coin is needed for verifier
    }
}

pub struct PermissibleCoinFromTxAndPK<P0: SWModelParameters, P1: SWModelParameters> {
    pub permissible_pk: GroupAffine<P1>,
    pub r_permissible_pk: P1::ScalarField,
    pub permissible_coin: GroupAffine<P0>,
    pub r_permissible_coin: P0::ScalarField,
}

pub fn verify_mint<P: SWModelParameters>(
    verifier: &mut Verifier<Transcript, GroupAffine<P>>,
    commitment: GroupAffine<P>,
) -> Variable<P::ScalarField> {
    let variables = verifier.commit_vec(2, commitment);
    range_proof(verifier, variables[0].into(), None, 64).unwrap(); // todo range?
    variables[0]
}

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn range_proof<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut v: LinearCombination<F>,
    v_assignment: Option<u64>,
    n: usize,
) -> Result<(), R1CSError> {
    let mut exp_2 = F::one();
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate_multiplier(v_assignment.map(|q| {
            let bit: u64 = (q >> i) & 1;
            ((1 - bit).into(), bit.into())
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - constant(1u64)));

        // Add `-b_i*2^i` to the linear combination
        // in order to form the following constraint by the end of the loop:
        // v = Sum(b_i * 2^i, i = 0..n-1)
        v = v - b * exp_2;

        exp_2 = exp_2 + exp_2;
    }

    // Enforce that v = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(v);

    Ok(())
}

pub fn element_from_bytes_stat<F: PrimeField>(bytes: &[u8]) -> F {
    // for the purpose of hashing to a 256 bit prime field, provides statistical security of ... todo
    extern crate crypto;
    use crypto::digest::Digest;
    use crypto::sha3::Sha3;

    let mut sha = Sha3::sha3_512();
    sha.input(bytes);
    let mut buf = [0u8; 32];
    sha.result(&mut buf);
    F::from_le_bytes_mod_order(&buf)
}

pub struct SpendingInfo<P0, P1>
where
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    P0::BaseField: PrimeField,
{
    pub index: usize,
    pub coin_aux: Coin<P0, P1>,
    pub combined_coin: PermissibleCoinFromTxAndPK<P0, P1>,
    pub randomized_pk: PublicKey<P1>,
    pub sk: SecretKey<P1>,
}

impl<P0, P1> SpendingInfo<P0, P1>
where
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    P0::BaseField: PrimeField,
{
    pub fn prove_spend<const L: usize, R: Rng>(
        &self,
        even_prover: &mut Prover<Transcript, GroupAffine<P0>>,
        odd_prover: &mut Prover<Transcript, GroupAffine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, P0, P1>,
        rng: &mut R,
    ) -> (SelectAndRerandomizePath<P0, P1>, Variable<P0::ScalarField>) {
        let (path, rerandomization) = curve_tree.select_and_rerandomize_prover_gadget(
            self.index,
            even_prover,
            odd_prover,
            parameters,
        );

        let (rerandomized_point, coin_variables) = even_prover.commit_vec(
            &[
                P0::ScalarField::from(self.coin_aux.value),
                self.combined_coin.permissible_pk.x,
            ],
            self.coin_aux.value_randomness
                + self.combined_coin.r_permissible_coin
                + rerandomization,
            &parameters.c0_parameters.bp_gens,
        );
        assert_eq!(path.even_commitments.len(), 2);
        assert_eq!(path.even_commitments[1], rerandomized_point);

        // even_prover.constrain(variables[1] - self.tag);
        // todo extract rerandomization of the public key + h(tx) thing, and show opening and tag stuff
        let fresh_pk_randomness = P1::ScalarField::rand(rng);
        let permissible_pk = self.combined_coin.permissible_pk;
        let rerandomized_public_key = permissible_pk.mul(fresh_pk_randomness).into_affine();
        single_level_select_and_rerandomize(
            even_prover,
            &parameters.c1_parameters,
            &rerandomized_public_key,
            vec![coin_variables[1]],
            Some(permissible_pk),
            Some(fresh_pk_randomness),
        );

        // let x = self.sk;
        // let _ = odd_prover.commit(
        //     x,
        //     parameters.c1_parameters.pc_gens.B_blinding
        // );

        // the first entry of the coin variables is the value of the coin.
        (path, coin_variables[0])
    }
}
