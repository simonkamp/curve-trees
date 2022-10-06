use bulletproofs::r1cs::*;
use merlin::Transcript;
use rand::Rng;

use crate::range_proof::*;
use crate::select_and_rerandomize::*;

use ark_crypto_primitives::{
    signature::schnorr::{Parameters, PublicKey, Schnorr, SecretKey, Signature},
    SignatureScheme,
};
use ark_ec::{models::short_weierstrass_jacobian::GroupAffine, ProjectiveCurve, SWModelParameters};
use ark_ff::{PrimeField, ToBytes};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::UniformRand;
use blake2::Blake2s;
use std::marker::PhantomData;

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
        let (coin, _) = Self::new(value, pk, parameters, sr_parameters, rng);

        let (coin_commitment, variables) = prover.commit_vec(
            &[P0::ScalarField::from(value), coin.tag],
            coin.permissible_randomness,
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
    ) -> (Coin<P0, C>, GroupAffine<P0>) {
        let pk_rerandomization = C::ScalarField::rand(rng);
        let randomized_pk = Self::rerandomized_pk(pk, &pk_rerandomization, parameters);
        let output_tag = Self::pk_to_scalar(&randomized_pk);

        let (coin_commitment, permissible_randomness) = sr_parameters.permissible_commitment(
            &[P0::ScalarField::from(value), output_tag],
            P0::ScalarField::rand(rng),
        );

        (
            Coin {
                value,
                tag: output_tag,
                permissible_randomness,
                pk_randomness: pk_rerandomization,
            },
            coin_commitment,
        )
    }

    fn pk_to_scalar(pk: &PublicKey<C>) -> P0::ScalarField {
        let mut pk_bytes = Vec::new();
        pk.write(&mut pk_bytes).unwrap();
        element_from_bytes_stat::<P0::ScalarField>(&pk_bytes)
    }

    pub fn rerandomized_pk(
        pk: &PublicKey<C>,
        rerandomization: &C::ScalarField,
        parameters: &Parameters<C, Blake2s>,
    ) -> PublicKey<C> {
        let mut randomness = Vec::new();
        rerandomization.write(&mut randomness).unwrap();
        Schnorr::randomize_public_key(parameters, pk, &randomness).unwrap()
    }

    pub fn prove_spend<
        const L: usize,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    >(
        &self,
        index: usize,
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

        let (rerandomized_point, variables) = even_prover.commit_vec(
            &[P0::ScalarField::from(self.value), self.tag],
            self.permissible_randomness + rerandomization,
            &parameters.c0_parameters.bp_gens,
        );
        assert_eq!(
            path.even_commitments[path.even_commitments.len() - 1],
            rerandomized_point
        );

        even_prover.constrain(variables[1] - self.tag);

        (path, variables[0])
    }
}

pub fn verify_mint<P: SWModelParameters>(
    verifier: &mut Verifier<Transcript, GroupAffine<P>>,
    commitment: GroupAffine<P>,
) -> Variable<P::ScalarField> {
    let variables = verifier.commit_vec(2, commitment);
    range_proof(verifier, variables[0].into(), None, 64).unwrap(); // todo range?
    variables[0]
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

pub struct SpendingInfo<P: SWModelParameters + Clone, C: ProjectiveCurve> {
    pub index: usize,
    pub coin_aux: Coin<P, C>,
    pub randomized_pk: PublicKey<C>,
    pub sk: SecretKey<C>,
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
    input_0: &SpendingInfo<P0, C>,
    input_1: &SpendingInfo<P0, C>,
    receiver_value_0: u64,
    receiver_pk_0: PublicKey<C>,
    receiver_value_1: u64,
    receiver_pk_1: PublicKey<C>,
    sig_parameters: &Parameters<C, Blake2s>,
    rng: &mut R, // todo input spending pks
) -> SignedTx<P0, P1, C> {
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
    let even_proof = even_prover
        .prove(&sr_parameters.c0_parameters.bp_gens)
        .unwrap();
    let odd_proof = odd_prover
        .prove(&sr_parameters.c1_parameters.bp_gens)
        .unwrap();

    // todo serialize tx's and sign using both of the secret keys
    let proof = Pour::<P0, P1, C> {
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
    let mut proof_bytes = Vec::with_capacity(proof.serialized_size());
    proof.serialize(&mut proof_bytes).unwrap();
    let sig_0 = Schnorr::sign(sig_parameters, &input_0.sk, proof_bytes.as_slice(), rng).unwrap();
    let mut randomization_bytes = Vec::new();
    input_0
        .coin_aux
        .pk_randomness
        .write(&mut randomization_bytes)
        .unwrap();
    let sig_0 =
        Schnorr::randomize_signature(sig_parameters, &sig_0, randomization_bytes.as_slice())
            .unwrap();

    let sig_1 = Schnorr::sign(sig_parameters, &input_1.sk, proof_bytes.as_slice(), rng).unwrap();
    let mut randomization_bytes = Vec::new();
    input_1
        .coin_aux
        .pk_randomness
        .write(&mut randomization_bytes)
        .unwrap();
    let sig_1 =
        Schnorr::randomize_signature(sig_parameters, &sig_1, randomization_bytes.as_slice())
            .unwrap();

    let signed_pour = SignedTx::<P0, P1, _> {
        signature_prover_response_0: sig_0.prover_response,
        signature_verifier_challenge_0: sig_0.verifier_challenge,
        signature_prover_response_1: sig_1.prover_response,
        signature_verifier_challenge_1: sig_1.verifier_challenge,
        pour_bytes: proof_bytes,
        _pour_type: PhantomData,
    };

    signed_pour
}

// todo do an n to m pour with arrays?
#[derive(Clone)]
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
    pub fn even_verification_gadget(
        &self,
        ro_domain: &'static [u8],
        sr_parameters: &SelRerandParameters<P0, P1>,
        spend_commitments_0: &SRVerificationCommitments<P0, P1>,
        spend_commitments_1: &SRVerificationCommitments<P0, P1>,
    ) -> VerificationTuple<GroupAffine<P0>> {
        let mut even_verifier = Verifier::new(Transcript::new(ro_domain));
        // mint
        let minted_amount_var_0 = verify_mint(&mut even_verifier, self.minted_coin_commitment_0);
        let minted_amount_var_1 = verify_mint(&mut even_verifier, self.minted_coin_commitment_1);

        // spend
        let spent_amount_var_0 = verify_spend_even::<_, _, C>(
            &mut even_verifier,
            spend_commitments_0,
            sr_parameters,
            &self.pk0,
        );
        let spent_amount_var_1 = verify_spend_even::<_, _, C>(
            &mut even_verifier,
            spend_commitments_1,
            sr_parameters,
            &self.pk1,
        );

        // balance
        even_verifier.constrain(
            minted_amount_var_0 + minted_amount_var_1 - spent_amount_var_0 - spent_amount_var_1,
        );

        let even_vt = even_verifier
            .verification_scalars_and_points(&self.even_proof)
            .unwrap();
        even_vt
    }

    // verification
    pub fn odd_verification_gadget(
        &self,
        ro_domain: &'static [u8],
        sr_parameters: &SelRerandParameters<P0, P1>,
        spend_commitments_0: &SRVerificationCommitments<P0, P1>,
        spend_commitments_1: &SRVerificationCommitments<P0, P1>,
    ) -> VerificationTuple<GroupAffine<P1>> {
        let mut odd_verifier = Verifier::new(Transcript::new(ro_domain));
        // spend
        verify_spend_odd(&mut odd_verifier, spend_commitments_0, sr_parameters);
        verify_spend_odd(&mut odd_verifier, spend_commitments_1, sr_parameters);

        let odd_vt = odd_verifier
            .verification_scalars_and_points(&self.odd_proof)
            .unwrap();
        odd_vt
    }

    // verification
    pub fn verification_gadget<const L: usize>(
        self,
        ro_domain: &'static [u8],
        sr_parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, P0, P1>,
    ) -> (
        VerificationTuple<GroupAffine<P0>>,
        VerificationTuple<GroupAffine<P1>>,
    ) {
        #[cfg(feature = "parallel")]
        let (spend_commitments_0, spend_commitments_1) = {
            // todo this might not be worth the overhead
            rayon::join(
                || {
                    curve_tree.select_and_rerandomize_verification_commitments(
                        self.randomized_path_0.clone(),
                    )
                },
                || {
                    curve_tree.select_and_rerandomize_verification_commitments(
                        self.randomized_path_1.clone(),
                    )
                },
            )
        };
        #[cfg(not(feature = "parallel"))]
        let (spend_commitments_0, spend_commitments_1) = {
            (
                curve_tree.select_and_rerandomize_verification_commitments(
                    self.randomized_path_0.clone(),
                ),
                curve_tree.select_and_rerandomize_verification_commitments(
                    self.randomized_path_1.clone(),
                ),
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
                    )
                },
                || {
                    self.odd_verification_gadget(
                        ro_domain,
                        sr_parameters,
                        &spend_commitments_0,
                        &spend_commitments_1,
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
                ),
                self.odd_verification_gadget(
                    ro_domain,
                    sr_parameters,
                    &spend_commitments_0,
                    &spend_commitments_1,
                ),
            )
        };

        // todo check signatures

        (even_vt, odd_vt)
    }
}

fn verify_spend_even<
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    C: ProjectiveCurve,
>(
    even_verifier: &mut Verifier<Transcript, GroupAffine<P0>>,
    commitments: &SRVerificationCommitments<P0, P1>,
    sr_parameters: &SelRerandParameters<P0, P1>,
    pk: &PublicKey<C>,
) -> Variable<P0::ScalarField> {
    commitments.even_verifier_gadget(even_verifier, sr_parameters);
    let vars = even_verifier.commit_vec(commitments.branching_factor, commitments.leaf);

    // enforce equality of tag with hash of public key
    even_verifier.constrain(vars[1] - Coin::<P0, C>::pk_to_scalar(pk));

    // return value to constrain spending balance
    vars[0]
}

fn verify_spend_odd<
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
>(
    odd_verifier: &mut Verifier<Transcript, GroupAffine<P1>>,
    commitments: &SRVerificationCommitments<P0, P1>,
    sr_parameters: &SelRerandParameters<P0, P1>,
) {
    commitments.odd_verifier_gadget(odd_verifier, sr_parameters);
}

fn verify_spend<
    const L: usize,
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    C: ProjectiveCurve,
>(
    randomized_path: SelectAndRerandomizePath<P0, P1>,
    even_verifier: &mut Verifier<Transcript, GroupAffine<P0>>,
    odd_verifier: &mut Verifier<Transcript, GroupAffine<P1>>,
    sr_parameters: &SelRerandParameters<P0, P1>,
    curve_tree: &CurveTree<L, P0, P1>,
    pk: &PublicKey<C>,
) -> Variable<P0::ScalarField> {
    let commitments = curve_tree.select_and_rerandomize_verification_commitments(randomized_path);
    verify_spend_odd(odd_verifier, &commitments, sr_parameters);
    verify_spend_even::<_, _, C>(even_verifier, &commitments, sr_parameters, pk)
}

#[derive(Clone)]
pub struct SignedTx<
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    C: ProjectiveCurve,
> {
    pub signature_prover_response_0: C::ScalarField,
    pub signature_verifier_challenge_0: C::ScalarField,
    pub signature_prover_response_1: C::ScalarField,
    pub signature_verifier_challenge_1: C::ScalarField,
    pub pour_bytes: Vec<u8>,
    _pour_type: PhantomData<(P0, P1)>,
}

impl<
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: ProjectiveCurve,
    > SignedTx<P0, P1, C>
{
    pub fn verification_gadget<const L: usize>(
        self,
        ro_domain: &'static [u8],
        sr_parameters: &SelRerandParameters<P0, P1>,
        curve_tree: &CurveTree<L, P0, P1>,
        sig_parameters: &Parameters<C, Blake2s>,
    ) -> (
        VerificationTuple<GroupAffine<P0>>,
        VerificationTuple<GroupAffine<P1>>,
    ) {
        let pour = self.verify_signature_and_deserialize(sig_parameters);
        pour.verification_gadget(ro_domain, sr_parameters, curve_tree)
    }

    pub fn verify_signature_and_deserialize(
        &self,
        sig_parameters: &Parameters<C, Blake2s>,
    ) -> Pour<P0, P1, C> {
        let pour = Pour::<P0, P1, C>::deserialize(self.pour_bytes.as_slice()).unwrap();

        Schnorr::verify(
            sig_parameters,
            &pour.pk0,
            self.pour_bytes.as_slice(),
            &Signature {
                verifier_challenge: self.signature_verifier_challenge_0,
                prover_response: self.signature_prover_response_0,
            },
        )
        .unwrap();
        Schnorr::verify(
            sig_parameters,
            &pour.pk1,
            self.pour_bytes.as_slice(),
            &Signature {
                verifier_challenge: self.signature_verifier_challenge_1,
                prover_response: self.signature_prover_response_1,
            },
        )
        .unwrap();
        pour
    }
}

impl<
        P0: SWModelParameters + Clone,
        P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
        C: ProjectiveCurve,
    > CanonicalSerialize for SignedTx<P0, P1, C>
{
    fn serialized_size(&self) -> usize {
        self.pour_bytes.serialized_size()
            + self.signature_prover_response_0.serialized_size()
            + self.signature_verifier_challenge_0.serialized_size()
            + self.signature_prover_response_1.serialized_size()
            + self.signature_verifier_challenge_1.serialized_size()
    }

    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        self.signature_prover_response_0.serialize(&mut writer)?;
        self.signature_verifier_challenge_0.serialize(&mut writer)?;
        self.signature_prover_response_1.serialize(&mut writer)?;
        self.signature_verifier_challenge_1.serialize(&mut writer)?;
        self.pour_bytes.serialize(&mut writer)?;
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
            signature_prover_response_0: C::ScalarField::deserialize(&mut reader)?,
            signature_verifier_challenge_0: C::ScalarField::deserialize(&mut reader)?,
            signature_prover_response_1: C::ScalarField::deserialize(&mut reader)?,
            signature_verifier_challenge_1: C::ScalarField::deserialize(&mut reader)?,
            pour_bytes: Vec::<u8>::deserialize(&mut reader)?,
            _pour_type: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use pasta;
    type PallasParameters = pasta::pallas::PallasParameters;
    type VestaParameters = pasta::vesta::VestaParameters;
    type PallasP = pasta::pallas::Projective;

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
            &mut rng,
        );

        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, GroupAffine<PallasParameters>> =
            Prover::new(&sr_params.c0_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, GroupAffine<VestaParameters>> =
            Prover::new(&sr_params.c1_parameters.pc_gens, vesta_transcript);

        let schnorr_parameters = Schnorr::<PallasP, Blake2s>::setup(&mut rng).unwrap();
        let (pk, sk) = Schnorr::keygen(&schnorr_parameters, &mut rng).unwrap();

        let (coin_aux, coin) = Coin::<PallasParameters, PallasP>::new(
            19,
            &pk,
            &schnorr_parameters,
            &sr_params.c0_parameters,
            &mut rng,
        );
        let rerandomized_pk = Coin::<PallasParameters, PallasP>::rerandomized_pk(
            &pk,
            &coin_aux.pk_randomness,
            &schnorr_parameters,
        );
        // Curve tree with two coins
        let set = vec![coin];
        let curve_tree = CurveTree::<256, PallasParameters, VestaParameters>::from_set(
            &set,
            &sr_params,
            Some(4),
        );

        let (path, _) = coin_aux.prove_spend(
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &curve_tree,
        );

        let pallas_proof = pallas_prover
            .prove(&sr_params.c0_parameters.bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&sr_params.c1_parameters.bp_gens)
            .unwrap();

        {
            let pallas_transcript = Transcript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = Transcript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let _ = verify_spend::<256, _, _, PallasP>(
                path,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_params,
                &curve_tree,
                &rerandomized_pk,
            );

            vesta_verifier
                .verify(
                    &vesta_proof,
                    &sr_params.c1_parameters.pc_gens,
                    &sr_params.c1_parameters.bp_gens,
                )
                .unwrap();
            pallas_verifier
                .verify(
                    &pallas_proof,
                    &sr_params.c0_parameters.pc_gens,
                    &sr_params.c0_parameters.bp_gens,
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
            &mut rng,
        );

        let pallas_transcript = Transcript::new(b"select_and_rerandomize");
        let pallas_prover: Prover<_, GroupAffine<PallasParameters>> =
            Prover::new(&sr_params.c0_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = Transcript::new(b"select_and_rerandomize");
        let vesta_prover: Prover<_, GroupAffine<VestaParameters>> =
            Prover::new(&sr_params.c1_parameters.pc_gens, vesta_transcript);

        let schnorr_parameters = Schnorr::<PallasP, Blake2s>::setup(&mut rng).unwrap();
        let (pk, sk) = Schnorr::keygen(&schnorr_parameters, &mut rng).unwrap();

        let (coin_aux_0, coin_0) = Coin::<PallasParameters, PallasP>::new(
            19,
            &pk,
            &schnorr_parameters,
            &sr_params.c0_parameters,
            &mut rng,
        );
        let (coin_aux_1, coin_1) = Coin::<PallasParameters, PallasP>::new(
            23,
            &pk,
            &schnorr_parameters,
            &sr_params.c0_parameters,
            &mut rng,
        );
        // Curve tree with two coins
        let set = vec![coin_0, coin_1];
        let curve_tree = CurveTree::<256, PallasParameters, VestaParameters>::from_set(
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
                &sr_params.c0_parameters.pc_gens,
                &sr_params.c0_parameters.bp_gens,
            )
            .unwrap();
            batch_verify(
                vec![vesta_vt],
                &sr_params.c1_parameters.pc_gens,
                &sr_params.c1_parameters.bp_gens,
            )
            .unwrap();
        }
    }
}
