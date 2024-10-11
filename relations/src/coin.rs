use ark_serialize::Compress;
use ark_serialize::Valid;
use bulletproofs::r1cs::*;
use merlin::Transcript;
use rand::Rng;

use crate::curve_tree::*;
use crate::range_proof::*;
use crate::single_level_select_and_rerandomize::*;

use ark_crypto_primitives::{
    signature::schnorr::{Parameters, PublicKey, Schnorr, SecretKey, Signature},
    signature::*,
};
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::UniformRand;
use blake2::Blake2s256 as Blake2s;
use std::marker::PhantomData;

pub struct Coin<P0: SWCurveConfig + Clone, C: CurveGroup> {
    pub value: u64,
    pub tag: P0::ScalarField, // spending tag derived from the rerandomized public key
    pub blinding: P0::ScalarField, // randomness used to commit to `tag` and `value`
    pub pk_randomness: C::ScalarField, // randomness used to randomize the public key, needed for the receivers signature
}

impl<
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        C: CurveGroup,
    > Coin<P0, C>
{
    pub fn mint<R: Rng>(
        value: u64,
        pk: &PublicKey<C>,
        parameters: &Parameters<C, Blake2s>,
        sr_parameters: &SingleLayerParameters<P0>,
        rng: &mut R,
        prover: &mut Prover<Transcript, Affine<P0>>,
    ) -> (Coin<P0, C>, Affine<P0>, Variable<P0::ScalarField>) {
        let (coin, _) = Self::new(value, pk, parameters, sr_parameters, rng);

        let (coin_commitment, variables) = prover.commit_vec(
            &[P0::ScalarField::from(value), coin.tag],
            coin.blinding,
            &sr_parameters.bp_gens,
        );
        range_proof(prover, variables[0].into(), Some(value), 64).unwrap(); // todo what range do we want to enforce? Table of benchmarks for different powers?

        (coin, coin_commitment, variables[0])
    }

    pub fn new<R: Rng>(
        value: u64,
        pk: &PublicKey<C>,
        parameters: &Parameters<C, Blake2s>,
        sr_parameters: &SingleLayerParameters<P0>,
        rng: &mut R,
    ) -> (Coin<P0, C>, Affine<P0>) {
        let pk_rerandomization = C::ScalarField::rand(rng);
        let randomized_pk = Self::rerandomized_pk(pk, &pk_rerandomization, parameters);
        let output_tag = Self::pk_to_scalar(&randomized_pk);

        let blinding = P0::ScalarField::rand(rng);
        let coin_commitment =
            sr_parameters.commit(&[P0::ScalarField::from(value), output_tag], blinding, 0);

        (
            Coin {
                value,
                tag: output_tag,
                blinding,
                pk_randomness: pk_rerandomization,
            },
            coin_commitment,
        )
    }

    fn pk_to_scalar(pk: &PublicKey<C>) -> P0::ScalarField {
        let mut pk_bytes = Vec::new();
        pk.serialize_compressed(&mut pk_bytes).unwrap();
        element_from_bytes_stat::<P0::ScalarField>(&pk_bytes)
    }

    pub fn rerandomized_pk(
        pk: &PublicKey<C>,
        rerandomization: &C::ScalarField,
        parameters: &Parameters<C, Blake2s>,
    ) -> PublicKey<C> {
        let mut randomness = Vec::new();
        rerandomization
            .serialize_compressed(&mut randomness)
            .unwrap();
        Schnorr::randomize_public_key(parameters, pk, &randomness).unwrap()
    }

    pub fn prove_spend<
        const L: usize,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    >(
        &self,
        index: usize,
        even_prover: &mut Prover<Transcript, Affine<P0>>,
        odd_prover: &mut Prover<Transcript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, 1, P0, P1>,
    ) -> (
        SelectAndRerandomizePath<L, P0, P1>,
        Variable<P0::ScalarField>,
    ) {
        // TODO: Use batching technique.
        let (path, rerandomization) = curve_tree.select_and_rerandomize_prover_gadget(
            index,
            0,
            even_prover,
            odd_prover,
            parameters,
            &mut rand::thread_rng(),
        );

        // Todo: Avoid using vector commitment for efficiency. Can just subtract tag*G_tag from the coin outside the circuit. But we will need to change the generator of the value as well. To do that we need to prove knowledge of opening when minting using e.g. sigma protocols.
        let (rerandomized_point, variables) = even_prover.commit_vec(
            &[P0::ScalarField::from(self.value), self.tag],
            self.blinding + rerandomization,
            &parameters.even_parameters.bp_gens,
        );
        assert_eq!(path.selected_commitment, rerandomized_point);

        even_prover.constrain(variables[1] - self.tag);

        (path, variables[0])
    }
}

pub fn verify_mint<P: SWCurveConfig>(
    verifier: &mut Verifier<Transcript, Affine<P>>,
    commitment: Affine<P>,
) -> Variable<P::ScalarField> {
    let variables = verifier.commit_vec(2, commitment);
    range_proof(verifier, variables[0].into(), None, 64).unwrap(); // todo range?
    variables[0]
}

pub fn element_from_bytes_stat<F: PrimeField>(bytes: &[u8]) -> F {
    // for the purpose of hashing to a 256 bit prime field F_p, reducing 512 bits mod p is statistically close to uniform.
    use sha3::{Digest, Sha3_512};

    let mut sha = Sha3_512::new();
    sha.update(bytes);
    let result = sha.finalize();
    F::from_le_bytes_mod_order(result.as_slice())
}

pub struct SpendingInfo<P: SWCurveConfig + Clone, C: CurveGroup> {
    pub index: usize,
    pub coin_aux: Coin<P, C>,
    pub randomized_pk: PublicKey<C>,
    pub sk: SecretKey<C>,
}

pub fn prove_pour<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
    P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    C: CurveGroup,
    R: Rng,
>(
    mut even_prover: Prover<Transcript, Affine<P0>>,
    mut odd_prover: Prover<Transcript, Affine<P1>>,
    sr_parameters: &SelRerandParameters<P0, P1>,
    curve_tree: &CurveTree<L, 1, P0, P1>,
    input_0: &SpendingInfo<P0, C>,
    input_1: &SpendingInfo<P0, C>,
    receiver_value_0: u64,
    receiver_pk_0: PublicKey<C>,
    receiver_value_1: u64,
    receiver_pk_1: PublicKey<C>,
    sig_parameters: &Parameters<C, Blake2s>,
    rng: &mut R,
) -> SignedTx<P0, P1, C> {
    // mint coins
    let (_, minted_coin_commitment_0, minted_amount_var_0) = Coin::<P0, C>::mint(
        receiver_value_0,
        &receiver_pk_0,
        sig_parameters,
        &sr_parameters.even_parameters,
        rng,
        &mut even_prover,
    );
    let (_, minted_coin_commitment_1, minted_amount_var_1) = Coin::<P0, C>::mint(
        receiver_value_1,
        &receiver_pk_1,
        sig_parameters,
        &sr_parameters.even_parameters,
        rng,
        &mut even_prover,
    );

    // spend coins
    let (path_0, spent_amount_var_0) = input_0.coin_aux.prove_spend(
        input_0.index,
        &mut even_prover,
        &mut odd_prover,
        sr_parameters,
        curve_tree,
    );
    let (path_1, spent_amount_var_1) = input_1.coin_aux.prove_spend(
        input_1.index,
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
    #[cfg(not(feature = "parallel"))]
    let (even_proof, odd_proof) = (
        even_prover
            .prove(&sr_parameters.even_parameters.bp_gens)
            .unwrap(),
        odd_prover
            .prove(&sr_parameters.odd_parameters.bp_gens)
            .unwrap(),
    );
    #[cfg(feature = "parallel")]
    let (even_proof, odd_proof) = rayon::join(
        || {
            even_prover
                .prove(&sr_parameters.even_parameters.bp_gens)
                .unwrap()
        },
        || {
            odd_prover
                .prove(&sr_parameters.odd_parameters.bp_gens)
                .unwrap()
        },
    );

    let proof = Pour::<L, P0, P1, C> {
        even_proof,
        odd_proof,
        randomized_path_0: path_0,
        randomized_path_1: path_1,
        pk0: input_0.randomized_pk,
        pk1: input_1.randomized_pk,
        minted_coin_commitment_0,
        minted_coin_commitment_1,
    };
    // double sign
    let mut proof_bytes = Vec::with_capacity(proof.serialized_size(Compress::Yes));
    proof.serialize_compressed(&mut proof_bytes).unwrap();
    let sig_0 = Schnorr::sign(sig_parameters, &input_0.sk, proof_bytes.as_slice(), rng).unwrap();
    let mut randomization_bytes = Vec::new();
    input_0
        .coin_aux
        .pk_randomness
        .serialize_compressed(&mut randomization_bytes)
        .unwrap();
    let sig_0 =
        Schnorr::randomize_signature(sig_parameters, &sig_0, randomization_bytes.as_slice())
            .unwrap();

    let sig_1 = Schnorr::sign(sig_parameters, &input_1.sk, proof_bytes.as_slice(), rng).unwrap();
    let mut randomization_bytes = Vec::new();
    input_1
        .coin_aux
        .pk_randomness
        .serialize_compressed(&mut randomization_bytes)
        .unwrap();
    let sig_1 =
        Schnorr::randomize_signature(sig_parameters, &sig_1, randomization_bytes.as_slice())
            .unwrap();

    SignedTx::<P0, P1, _> {
        signature_prover_response_0: sig_0.prover_response,
        signature_verifier_challenge_0: sig_0.verifier_challenge,
        signature_prover_response_1: sig_1.prover_response,
        signature_verifier_challenge_1: sig_1.verifier_challenge,
        pour_bytes: proof_bytes,
        _pour_type: PhantomData,
    }
}

// todo do an n to m pour with arrays?
#[derive(Clone)]
pub struct Pour<
    const L: usize,
    P0: SWCurveConfig + Clone,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    C: CurveGroup,
> {
    pub even_proof: R1CSProof<Affine<P0>>,
    pub odd_proof: R1CSProof<Affine<P1>>,
    pub randomized_path_0: SelectAndRerandomizePath<L, P0, P1>,
    pub randomized_path_1: SelectAndRerandomizePath<L, P0, P1>,
    pub pk0: PublicKey<C>,
    pub pk1: PublicKey<C>,
    pub minted_coin_commitment_0: Affine<P0>,
    pub minted_coin_commitment_1: Affine<P0>,
}

impl<
        const L: usize,
        P0: SWCurveConfig + Clone,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: CurveGroup,
    > CanonicalSerialize for Pour<L, P0, P1, C>
{
    fn serialized_size(&self, compress: Compress) -> usize {
        self.even_proof.serialized_size(compress)
            + self.odd_proof.serialized_size(compress)
            + self.randomized_path_0.serialized_size(compress)
            + self.randomized_path_1.serialized_size(compress)
            + self.pk0.serialized_size(compress)
            + self.pk1.serialized_size(compress)
            + self.minted_coin_commitment_0.serialized_size(compress)
            + self.minted_coin_commitment_1.serialized_size(compress)
    }

    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.even_proof.serialize_with_mode(&mut writer, compress)?;
        self.odd_proof.serialize_with_mode(&mut writer, compress)?;
        self.randomized_path_0
            .serialize_with_mode(&mut writer, compress)?;
        self.randomized_path_1
            .serialize_with_mode(&mut writer, compress)?;
        self.pk0.serialize_with_mode(&mut writer, compress)?;
        self.pk1.serialize_with_mode(&mut writer, compress)?;
        self.minted_coin_commitment_0
            .serialize_with_mode(&mut writer, compress)?;
        self.minted_coin_commitment_1
            .serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }
}

impl<
        const L: usize,
        P0: SWCurveConfig + Clone,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: CurveGroup,
    > Valid for Pour<L, P0, P1, C>
{
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}
impl<
        const L: usize,
        P0: SWCurveConfig + Clone,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: CurveGroup,
    > CanonicalDeserialize for Pour<L, P0, P1, C>
{
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, SerializationError> {
        Ok(Self {
            even_proof: R1CSProof::<Affine<P0>>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            odd_proof: R1CSProof::<Affine<P1>>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            randomized_path_0: SelectAndRerandomizePath::<L, P0, P1>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            randomized_path_1: SelectAndRerandomizePath::<L, P0, P1>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            pk0: PublicKey::<C>::deserialize_with_mode(&mut reader, compress, validate)?,
            pk1: PublicKey::<C>::deserialize_with_mode(&mut reader, compress, validate)?,
            minted_coin_commitment_0: Affine::<P0>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            minted_coin_commitment_1: Affine::<P0>::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
        })
    }
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        C: CurveGroup,
    > Pour<L, P0, P1, C>
{
    // verification
    pub fn even_verification_gadget(
        &self,
        ro_domain: &'static [u8],
        sr_parameters: &SelRerandParameters<P0, P1>,
        spend_commitments_0: &SelectAndRerandomizePath<L, P0, P1>,
        spend_commitments_1: &SelectAndRerandomizePath<L, P0, P1>,
        curve_tree: &CurveTree<L, 1, P0, P1>,
    ) -> VerificationTuple<Affine<P0>> {
        let mut even_verifier = Verifier::new(Transcript::new(ro_domain));
        // mint
        let minted_amount_var_0 = verify_mint(&mut even_verifier, self.minted_coin_commitment_0);
        let minted_amount_var_1 = verify_mint(&mut even_verifier, self.minted_coin_commitment_1);

        // spend
        let spent_amount_var_0 = verify_spend_even::<L, _, _, _, _, C>(
            &mut even_verifier,
            spend_commitments_0,
            sr_parameters,
            &self.pk0,
            curve_tree,
        );
        let spent_amount_var_1 = verify_spend_even::<L, _, _, _, _, C>(
            &mut even_verifier,
            spend_commitments_1,
            sr_parameters,
            &self.pk1,
            curve_tree,
        );

        // balance
        even_verifier.constrain(
            minted_amount_var_0 + minted_amount_var_1 - spent_amount_var_0 - spent_amount_var_1,
        );

        even_verifier
            .verification_scalars_and_points(&self.even_proof)
            .unwrap()
    }

    // verification
    pub fn odd_verification_gadget(
        &self,
        ro_domain: &'static [u8],
        sr_parameters: &SelRerandParameters<P0, P1>,
        spend_commitments_0: &SelectAndRerandomizePath<L, P0, P1>,
        spend_commitments_1: &SelectAndRerandomizePath<L, P0, P1>,
        curve_tree: &CurveTree<L, 1, P0, P1>,
    ) -> VerificationTuple<Affine<P1>> {
        let mut odd_verifier = Verifier::new(Transcript::new(ro_domain));
        // spend
        verify_spend_odd(
            &mut odd_verifier,
            spend_commitments_0,
            sr_parameters,
            curve_tree,
        );
        verify_spend_odd(
            &mut odd_verifier,
            spend_commitments_1,
            sr_parameters,
            curve_tree,
        );

        odd_verifier
            .verification_scalars_and_points(&self.odd_proof)
            .unwrap()
    }

    // verification
    pub fn verification_gadget(
        self,
        ro_domain: &'static [u8],
        sr_parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, 1, P0, P1>,
    ) -> (VerificationTuple<Affine<P0>>, VerificationTuple<Affine<P1>>) {
        #[cfg(feature = "parallel")]
        let (spend_commitments_0, spend_commitments_1) = {
            // todo this might not be worth the overhead
            rayon::join(
                || {
                    let mut path = self.randomized_path_0.clone();
                    curve_tree.select_and_rerandomize_verification_commitments(&mut path);
                    path
                },
                || {
                    let mut path = self.randomized_path_1.clone();
                    curve_tree.select_and_rerandomize_verification_commitments(&mut path);
                    path
                },
            )
        };
        #[cfg(not(feature = "parallel"))]
        let (spend_commitments_0, spend_commitments_1) = {
            (
                {
                    let mut path = self.randomized_path_0.clone();
                    curve_tree.select_and_rerandomize_verification_commitments(&mut path);
                    path
                },
                {
                    let mut path = self.randomized_path_1.clone();
                    curve_tree.select_and_rerandomize_verification_commitments(&mut path);
                    path
                },
            )
        };

        #[cfg(feature = "parallel")]
        let (even_vt, odd_vt) = {
            rayon::join(
                || {
                    self.even_verification_gadget(
                        ro_domain,
                        sr_parameters,
                        &spend_commitments_0,
                        &spend_commitments_1,
                        curve_tree,
                    )
                },
                || {
                    self.odd_verification_gadget(
                        ro_domain,
                        sr_parameters,
                        &spend_commitments_0,
                        &spend_commitments_1,
                        curve_tree,
                    )
                },
            )
        };
        #[cfg(not(feature = "parallel"))]
        let (even_vt, odd_vt) = {
            (
                self.even_verification_gadget(
                    ro_domain,
                    sr_parameters,
                    &spend_commitments_0,
                    &spend_commitments_1,
                    curve_tree,
                ),
                self.odd_verification_gadget(
                    ro_domain,
                    sr_parameters,
                    &spend_commitments_0,
                    &spend_commitments_1,
                    curve_tree,
                ),
            )
        };

        // todo check signatures

        (even_vt, odd_vt)
    }
}

fn verify_spend_even<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
    P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    C: CurveGroup,
>(
    even_verifier: &mut Verifier<Transcript, Affine<P0>>,
    commitments: &SelectAndRerandomizePath<L, P0, P1>,
    sr_parameters: &SelRerandParameters<P0, P1>,
    pk: &PublicKey<C>,
    curve_tree: &CurveTree<L, 1, P0, P1>,
) -> Variable<P0::ScalarField> {
    commitments.even_verifier_gadget(even_verifier, sr_parameters, curve_tree);
    let vars = even_verifier.commit_vec(L, commitments.get_rerandomized_leaf());

    // enforce equality of tag with hash of public key
    even_verifier.constrain(vars[1] - Coin::<P0, C>::pk_to_scalar(pk));

    // return value to constrain spending balance
    vars[0]
}

fn verify_spend_odd<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
>(
    odd_verifier: &mut Verifier<Transcript, Affine<P1>>,
    commitments: &SelectAndRerandomizePath<L, P0, P1>,
    sr_parameters: &SelRerandParameters<P0, P1>,
    curve_tree: &CurveTree<L, 1, P0, P1>,
) {
    commitments.odd_verifier_gadget(odd_verifier, sr_parameters, curve_tree);
}

#[derive(Clone)]
pub struct SignedTx<
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    C: CurveGroup,
> {
    pub signature_prover_response_0: C::ScalarField,
    pub signature_verifier_challenge_0: C::ScalarField,
    pub signature_prover_response_1: C::ScalarField,
    pub signature_verifier_challenge_1: C::ScalarField,
    pub pour_bytes: Vec<u8>,
    _pour_type: PhantomData<(P0, P1)>,
}

impl<
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
        C: CurveGroup,
    > SignedTx<P0, P1, C>
{
    pub fn verification_gadget<const L: usize>(
        self,
        ro_domain: &'static [u8],
        sr_parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, 1, P0, P1>,
        sig_parameters: &Parameters<C, Blake2s>,
    ) -> (VerificationTuple<Affine<P0>>, VerificationTuple<Affine<P1>>) {
        let pour =
            Pour::<L, P0, P1, C>::deserialize_compressed(self.pour_bytes.as_slice()).unwrap();
        let pk0 = pour.pk0;
        let pk1 = pour.pk1;
        #[cfg(feature = "parallel")]
        let (_, vts) = rayon::join(
            || self.verify_signatures(sig_parameters, &pk0, &pk1),
            || pour.verification_gadget(ro_domain, sr_parameters, curve_tree),
        );
        #[cfg(not(feature = "parallel"))]
        let vts = {
            self.verify_signatures(sig_parameters, &pk0, &pk1);
            pour.verification_gadget(ro_domain, sr_parameters, curve_tree)
        };
        vts
    }

    pub fn verify_signatures(
        &self,
        sig_parameters: &Parameters<C, Blake2s>,
        pk0: &PublicKey<C>,
        pk1: &PublicKey<C>,
    ) {
        Schnorr::verify(
            sig_parameters,
            pk0,
            self.pour_bytes.as_slice(),
            &Signature {
                verifier_challenge: self.signature_verifier_challenge_0,
                prover_response: self.signature_prover_response_0,
            },
        )
        .unwrap();
        Schnorr::verify(
            sig_parameters,
            pk1,
            self.pour_bytes.as_slice(),
            &Signature {
                verifier_challenge: self.signature_verifier_challenge_1,
                prover_response: self.signature_prover_response_1,
            },
        )
        .unwrap();
    }
}

impl<
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
        C: CurveGroup,
    > CanonicalSerialize for SignedTx<P0, P1, C>
{
    fn serialized_size(&self, mode: Compress) -> usize {
        self.pour_bytes.serialized_size(mode)
            + self.signature_prover_response_0.serialized_size(mode)
            + self.signature_verifier_challenge_0.serialized_size(mode)
            + self.signature_prover_response_1.serialized_size(mode)
            + self.signature_verifier_challenge_1.serialized_size(mode)
    }

    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), SerializationError> {
        self.signature_prover_response_0
            .serialize_with_mode(&mut writer, compress)?;
        self.signature_verifier_challenge_0
            .serialize_with_mode(&mut writer, compress)?;
        self.signature_prover_response_1
            .serialize_with_mode(&mut writer, compress)?;
        self.signature_verifier_challenge_1
            .serialize_with_mode(&mut writer, compress)?;
        self.pour_bytes.serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }
}

impl<
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
        C: CurveGroup,
    > Valid for SignedTx<P0, P1, C>
{
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}
impl<
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
        C: CurveGroup,
    > CanonicalDeserialize for SignedTx<P0, P1, C>
{
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, SerializationError> {
        Ok(Self {
            signature_prover_response_0: C::ScalarField::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            signature_verifier_challenge_0: C::ScalarField::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            signature_prover_response_1: C::ScalarField::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            signature_verifier_challenge_1: C::ScalarField::deserialize_with_mode(
                &mut reader,
                compress,
                validate,
            )?,
            pour_bytes: Vec::<u8>::deserialize_with_mode(&mut reader, compress, validate)?,
            _pour_type: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasP = ark_pallas::Projective;

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

    #[test]
    pub fn test_spend() {
        let mut rng = rand::thread_rng();
        let generators_length = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)

        let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            generators_length,
        );

        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<PallasParameters>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<VestaParameters>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let schnorr_parameters = Schnorr::<PallasP, Blake2s>::setup(&mut rng).unwrap();
        let (pk, _sk) = Schnorr::keygen(&schnorr_parameters, &mut rng).unwrap();

        let (coin_aux, coin) = Coin::<PallasParameters, PallasP>::new(
            19,
            &pk,
            &schnorr_parameters,
            &sr_params.even_parameters,
            &mut rng,
        );
        let rerandomized_pk = Coin::<PallasParameters, PallasP>::rerandomized_pk(
            &pk,
            &coin_aux.pk_randomness,
            &schnorr_parameters,
        );
        // Curve tree with two coins
        let set = vec![coin];
        let curve_tree = CurveTree::<256, 1, PallasParameters, VestaParameters>::from_set(
            &set,
            &sr_params,
            Some(4),
        );

        let (mut path, _) = coin_aux.prove_spend(
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &curve_tree,
        );

        let pallas_proof = pallas_prover
            .prove(&sr_params.even_parameters.bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&sr_params.odd_parameters.bp_gens)
            .unwrap();

        {
            let pallas_transcript = Transcript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = Transcript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            curve_tree.select_and_rerandomize_verification_commitments(&mut path);
            let commitments = path;
            verify_spend_odd(&mut vesta_verifier, &commitments, &sr_params, &curve_tree);
            verify_spend_even::<256, _, _, _, _, PallasP>(
                &mut pallas_verifier,
                &commitments,
                &sr_params,
                &rerandomized_pk,
                &curve_tree,
            );

            vesta_verifier
                .verify(
                    &vesta_proof,
                    &sr_params.odd_parameters.pc_gens,
                    &sr_params.odd_parameters.bp_gens,
                )
                .unwrap();
            pallas_verifier
                .verify(
                    &pallas_proof,
                    &sr_params.even_parameters.pc_gens,
                    &sr_params.even_parameters.bp_gens,
                )
                .unwrap();
        }
    }

    #[test]
    pub fn test_pour() {
        let mut rng = rand::thread_rng();
        let generators_length = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)

        let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            generators_length,
        );

        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let pallas_prover: Prover<_, Affine<PallasParameters>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let vesta_prover: Prover<_, Affine<VestaParameters>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let schnorr_parameters = Schnorr::<PallasP, Blake2s>::setup(&mut rng).unwrap();
        let (pk, sk) = Schnorr::keygen(&schnorr_parameters, &mut rng).unwrap();

        let (coin_aux_0, coin_0) = Coin::<PallasParameters, PallasP>::new(
            19,
            &pk,
            &schnorr_parameters,
            &sr_params.even_parameters,
            &mut rng,
        );
        let (coin_aux_1, coin_1) = Coin::<PallasParameters, PallasP>::new(
            23,
            &pk,
            &schnorr_parameters,
            &sr_params.even_parameters,
            &mut rng,
        );
        // Curve tree with two coins
        let set = vec![coin_0, coin_1];
        let curve_tree = CurveTree::<256, 1, PallasParameters, VestaParameters>::from_set(
            &set,
            &sr_params,
            Some(4),
        );
        let randomized_pk_0 = Coin::<PallasParameters, PallasP>::rerandomized_pk(
            &pk,
            &coin_aux_0.pk_randomness,
            &schnorr_parameters,
        );
        let input0 = SpendingInfo {
            coin_aux: coin_aux_0,
            index: 0,
            randomized_pk: randomized_pk_0,
            sk: sk.clone(),
        };
        let randomized_pk_1 = Coin::<PallasParameters, PallasP>::rerandomized_pk(
            &pk,
            &coin_aux_1.pk_randomness,
            &schnorr_parameters,
        );
        let input1 = SpendingInfo {
            coin_aux: coin_aux_1,
            index: 1,
            randomized_pk: randomized_pk_1,
            sk: sk,
        };

        let receiver_pk_0 = pk;
        let receiver_pk_1 = pk;

        let proof = prove_pour(
            pallas_prover,
            vesta_prover,
            &sr_params,
            &curve_tree,
            &input0,
            &input1,
            11,
            receiver_pk_0,
            31,
            receiver_pk_1,
            &schnorr_parameters,
            &mut rng,
        );

        {
            let (pallas_vt, vesta_vt) = proof.verification_gadget(
                b"select_and_rerandomize",
                &sr_params,
                &curve_tree,
                &schnorr_parameters,
            );

            batch_verify(
                vec![pallas_vt],
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            )
            .unwrap();
            batch_verify(
                vec![vesta_vt],
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            )
            .unwrap();
        }
    }
}
