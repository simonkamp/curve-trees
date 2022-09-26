#![allow(unused)]
use ark_crypto_primitives::commitment::blake2s;
use ark_crypto_primitives::signature::schnorr::Signature;
use ark_ec::CurveCycle;
// todo
use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use digest::Digest;
use merlin::{Transcript, TranscriptRng};
// use digest::Digest;
use rand::Rng;

use crate::curve::{self, *};
use crate::permissible::*;
use crate::select_and_rerandomize::*;

use ark_crypto_primitives::{
    signature::schnorr::{Parameters, PublicKey, Schnorr},
    SignatureScheme,
};
use ark_ec::{
    models::short_weierstrass_jacobian::{GroupAffine, GroupProjective},
    msm::VariableBaseMSM,
    AffineCurve, ModelParameters, ProjectiveCurve, SWModelParameters,
};
use ark_ff::{BigInteger, Field, PrimeField, SquareRootField, ToBytes};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::{One, UniformRand, Zero};
use blake2::Blake2s;

pub struct Coin<P0: SWModelParameters + Clone, C: ProjectiveCurve> {
    pub value: u64,
    pub tag: P0::ScalarField, // spending tag derived from the rerandomized public key
    pub permissible_randomness: P0::ScalarField, // hiding and permissible randomness used to commit to `tag` and `value`
    pub pk_randomness: C::ScalarField, // the randomness used to randomize the public key, needed for the receivers signature
}

impl<P0: SWModelParameters + Clone, C: ProjectiveCurve> Coin<P0, C> {
    pub fn mint<R: Rng>(
        value: u64,
        pk: &PublicKey<C>,
        parameters: &Parameters<C, Blake2s>,
        sr_parameters: &SingleLayerParameters<P0>,
        rng: &mut R,
        prover: &mut Prover<Transcript, GroupAffine<P0>>,
    ) -> (Coin<P0, C>, GroupAffine<P0>, Variable<P0::ScalarField>) {
        let random_scalar = C::ScalarField::rand(rng);
        let mut randomness = Vec::new();
        random_scalar.write(&mut randomness);
        let randomized_pk = Schnorr::randomize_public_key(parameters, pk, &randomness).unwrap();
        // let mut pk_bytes = Vec::new();
        // randomized_pk.write(&mut pk_bytes);
        // let output_tag = element_from_bytes_stat::<P0::ScalarField>(&pk_bytes);
        let output_tag = Self::pk_to_scalar(&randomized_pk);
        let (_coin, permissible_randomness) = sr_parameters.permissible_commitment(
            &[P0::ScalarField::from(value), output_tag],
            P0::ScalarField::rand(rng),
        );

        let (coin_commitment, variables) = prover.commit_vec(
            &[P0::ScalarField::from(value), output_tag],
            permissible_randomness,
            &sr_parameters.bp_gens,
        );
        range_proof(prover, variables[0].into(), Some(value), 64); // todo what range do we want to enforce? Table of benchmarks for different powers?

        (
            Coin {
                value: value,
                tag: output_tag,
                permissible_randomness: permissible_randomness,
                pk_randomness: random_scalar,
            },
            coin_commitment,
            variables[0],
        )
    }

    fn pk_to_scalar(pk: &PublicKey<C>) -> P0::ScalarField {
        let mut pk_bytes = Vec::new();
        pk.write(&mut pk_bytes);
        element_from_bytes_stat::<P0::ScalarField>(&pk_bytes)
    }

    pub fn prove_spend<
        const L: usize,
        // P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        // C: ProjectiveCurve,
    >(
        &self,
        index: usize,
        // coin_aux: Coin<P0, C>,
        even_prover: &mut Prover<Transcript, GroupAffine<P0>>,
        odd_prover: &mut Prover<Transcript, GroupAffine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, P0, P1>,
    ) -> (SelectAndRerandomizePath<P0, P1>, Variable<P0::ScalarField>) {
        let (path, rerandomization) = curve_tree.select_and_rerandomize_prover_gadget(
            index,
            even_prover,
            odd_prover,
            parameters,
        );

        let (_, variables) = even_prover.commit_vec(
            &[P0::ScalarField::from(self.value), self.tag],
            self.permissible_randomness + rerandomization,
            &parameters.c0_parameters.bp_gens,
        );

        // todo we could explicitly remove the tag from the commitment by subtracting G_t * tag, but it would still add a vector commitment to the proof, because we are using separate generators.
        even_prover.constrain(variables[1] - self.tag);

        (path, variables[0])
    }
}

pub fn verify_mint<P: SWModelParameters>(
    verifier: &mut Verifier<Transcript, GroupAffine<P>>,
    commitment: GroupAffine<P>,
    parameters: &SingleLayerParameters<P>,
) -> Variable<P::ScalarField> {
    let (variables) = verifier.commit_vec(2, commitment);
    range_proof(verifier, variables[0].into(), None, 64); // todo range?
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

pub fn prove_pour<
    const L: usize,
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    C: ProjectiveCurve,
    R: Rng,
>(
    mut even_prover: Prover<Transcript, GroupAffine<P0>>,
    mut odd_prover: Prover<Transcript, GroupAffine<P1>>,
    sr_parameters: &SelRerandParameters<P0, P1>,
    curve_tree: &CurveTree<L, P0, P1>,
    index_0: usize,
    coin_aux_0: Coin<P0, C>,
    index_1: usize,
    coin_aux_1: Coin<P0, C>,
    receiver_value_0: u64,
    receiver_pk_0: PublicKey<C>,
    receiver_value_1: u64,
    receiver_pk_1: PublicKey<C>,
    sig_parameters: &Parameters<C, Blake2s>,
    rng: &mut R,
) -> Pour<P0, P1, C> {
    // mint coins
    let (coin_opening_0, minted_coin_commitment_0, minted_amount_var_0) = Coin::<P0, C>::mint(
        receiver_value_0,
        &receiver_pk_0,
        sig_parameters,
        &sr_parameters.c0_parameters,
        rng,
        &mut even_prover,
    );
    let (coin_opening_1, minted_coin_commitment_1, minted_amount_var_1) = Coin::<P0, C>::mint(
        receiver_value_1,
        &receiver_pk_1,
        sig_parameters,
        &sr_parameters.c0_parameters,
        rng,
        &mut even_prover,
    );

    // spend coins
    let (path_0, spent_amount_var_0) = coin_aux_0.prove_spend(
        index_0,
        &mut even_prover,
        &mut odd_prover,
        sr_parameters,
        curve_tree,
    );
    let (path_1, spent_amount_var_1) = coin_aux_1.prove_spend(
        index_1,
        &mut even_prover,
        &mut odd_prover,
        sr_parameters,
        curve_tree,
    );

    // enforce equal amount spent and minted
    even_prover.constrain(
        minted_amount_var_0 + minted_amount_var_1 - spent_amount_var_0 - spent_amount_var_1,
    );

    // prove
    let even_proof = even_prover
        .prove(&sr_parameters.c0_parameters.bp_gens)
        .unwrap();
    let odd_proof = odd_prover
        .prove(&sr_parameters.c1_parameters.bp_gens)
        .unwrap();

    // todo serialize tx's and sign using both of the secret keys
    Pour {
        even_proof: even_proof,
        odd_proof: odd_proof,
        randomized_path_0: path_0,
        randomized_path_1: path_1,
        pk0: receiver_pk_0,
        pk1: receiver_pk_1,
        minted_coin_commitment_0: minted_coin_commitment_0,
        minted_coin_commitment_1: minted_coin_commitment_1,
    }
}

// todo do an n to m pour with arrays?
pub struct Pour<
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    C: ProjectiveCurve,
> {
    pub even_proof: R1CSProof<GroupAffine<P0>>,
    pub odd_proof: R1CSProof<GroupAffine<P1>>,
    pub randomized_path_0: SelectAndRerandomizePath<P0, P1>,
    pub randomized_path_1: SelectAndRerandomizePath<P0, P1>,
    pub pk0: PublicKey<C>,
    pub pk1: PublicKey<C>,
    pub minted_coin_commitment_0: GroupAffine<P0>,
    pub minted_coin_commitment_1: GroupAffine<P0>,
}

impl<
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: ProjectiveCurve,
    > CanonicalSerialize for Pour<P0, P1, C>
{
    fn serialized_size(&self) -> usize {
        self.even_proof.serialized_size()
            + self.odd_proof.serialized_size()
            + self.randomized_path_0.serialized_size()
            + self.randomized_path_1.serialized_size()
            + self.pk0.serialized_size()
            + self.pk1.serialized_size()
            + self.minted_coin_commitment_0.serialized_size()
            + self.minted_coin_commitment_1.serialized_size()
    }

    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        self.even_proof.serialize(&mut writer)?;
        self.odd_proof.serialize(&mut writer)?;
        self.randomized_path_0.serialize(&mut writer)?;
        self.randomized_path_1.serialize(&mut writer)?;
        self.pk0.serialize(&mut writer)?;
        self.pk1.serialize(&mut writer)?;
        self.minted_coin_commitment_0.serialize(&mut writer)?;
        self.minted_coin_commitment_1.serialize(&mut writer)?;
        Ok(())
    }
}

impl<
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: ProjectiveCurve,
    > CanonicalDeserialize for Pour<P0, P1, C>
{
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        Ok(Self {
            even_proof: R1CSProof::<GroupAffine<P0>>::deserialize(&mut reader)?,
            odd_proof: R1CSProof::<GroupAffine<P1>>::deserialize(&mut reader)?,
            randomized_path_0: SelectAndRerandomizePath::<P0, P1>::deserialize(&mut reader)?,
            randomized_path_1: SelectAndRerandomizePath::<P0, P1>::deserialize(&mut reader)?,
            pk0: PublicKey::<C>::deserialize(&mut reader)?,
            pk1: PublicKey::<C>::deserialize(&mut reader)?,
            minted_coin_commitment_0: GroupAffine::<P0>::deserialize(&mut reader)?,
            minted_coin_commitment_1: GroupAffine::<P0>::deserialize(&mut reader)?,
        })
    }
}

impl<
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: ProjectiveCurve,
    > Pour<P0, P1, C>
{
    // verification
    pub fn verification_gadget<const L: usize>(
        self,
        even_verifier: &mut Verifier<Transcript, GroupAffine<P0>>,
        odd_verifier: &mut Verifier<Transcript, GroupAffine<P1>>,
        sr_parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, P0, P1>,
    ) {
        // mint
        let minted_amount_var_0 = verify_mint(
            even_verifier,
            self.minted_coin_commitment_0,
            &sr_parameters.c0_parameters,
        );
        let minted_amount_var_1 = verify_mint(
            even_verifier,
            self.minted_coin_commitment_1,
            &sr_parameters.c0_parameters,
        );

        // spend
        let spent_amount_var_0 = Self::verify_spend(
            self.randomized_path_0,
            even_verifier,
            odd_verifier,
            sr_parameters,
            curve_tree,
            &self.pk0,
        );
        let spent_amount_var_1 = Self::verify_spend(
            self.randomized_path_1,
            even_verifier,
            odd_verifier,
            sr_parameters,
            curve_tree,
            &self.pk1,
        );

        // balance
        even_verifier.constrain(
            minted_amount_var_0 + minted_amount_var_1 - spent_amount_var_0 - spent_amount_var_1,
        );

        //check signatures
    }

    fn verify_spend<const L: usize>(
        randomized_path: SelectAndRerandomizePath<P0, P1>,
        even_verifier: &mut Verifier<Transcript, GroupAffine<P0>>,
        odd_verifier: &mut Verifier<Transcript, GroupAffine<P1>>,
        sr_parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, P0, P1>,
        pk: &PublicKey<C>,
    ) -> Variable<P0::ScalarField> {
        let rerandomized_coin = curve_tree.select_and_rerandomize_verifier_gadget(
            even_verifier,
            odd_verifier,
            randomized_path,
            sr_parameters,
        );
        let vars = even_verifier.commit_vec(L, rerandomized_coin);

        // enforce equality of tag with hash of public key
        even_verifier.constrain(vars[1] - Coin::<P0, C>::pk_to_scalar(pk));

        // return value to constrain spending balance
        vars[0]
    }
}

pub struct SignedTx<
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    C: ProjectiveCurve,
> {
    pub pour: Pour<P0, P1, C>,
    pub signature_prover_response_0: C::ScalarField,
    pub signature_verifier_challenge_0: C::ScalarField,
    pub signature_prover_response_1: C::ScalarField,
    pub signature_verifier_challenge_1: C::ScalarField,
}

impl<
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: ProjectiveCurve,
    > CanonicalSerialize for SignedTx<P0, P1, C>
{
    fn serialized_size(&self) -> usize {
        self.pour.serialized_size()
            + self.signature_prover_response_0.serialized_size()
            + self.signature_verifier_challenge_0.serialized_size()
            + self.signature_prover_response_1.serialized_size()
            + self.signature_verifier_challenge_1.serialized_size()
    }

    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        self.pour.serialize(&mut writer)?;
        self.signature_prover_response_0.serialize(&mut writer)?;
        self.signature_verifier_challenge_0.serialize(&mut writer)?;
        self.signature_prover_response_1.serialize(&mut writer)?;
        self.signature_verifier_challenge_1.serialize(&mut writer)?;
        Ok(())
    }
}

impl<
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: ProjectiveCurve,
    > CanonicalDeserialize for SignedTx<P0, P1, C>
{
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        Ok(Self {
            pour: Pour::<P0, P1, C>::deserialize(&mut reader)?,
            signature_prover_response_0: C::ScalarField::deserialize(&mut reader)?,
            signature_verifier_challenge_0: C::ScalarField::deserialize(&mut reader)?,
            signature_prover_response_1: C::ScalarField::deserialize(&mut reader)?,
            signature_verifier_challenge_1: C::ScalarField::deserialize(&mut reader)?,
        })
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
    fn test_schnorr() {
        let mut rng = rand::thread_rng();
        let parameters = Schnorr::<PallasP, Blake2s>::setup(&mut rng).unwrap();
        let (pk, sk) = Schnorr::keygen(&parameters, &mut rng).unwrap();
        let msg = b"msg";
        let signature = Schnorr::sign(&parameters, &sk, msg.as_slice(), &mut rng).unwrap();
        let randomness = [42u8];
        let randomized_sig =
            Schnorr::randomize_signature(&parameters, &signature, &randomness).unwrap();
        let randomized_pk = Schnorr::randomize_public_key(&parameters, &pk, &randomness).unwrap();
        let res = Schnorr::verify(&parameters, &randomized_pk, msg, &randomized_sig).unwrap();
        assert_eq!(res, true);
    }
}
