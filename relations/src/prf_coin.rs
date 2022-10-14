use bulletproofs::{r1cs::*, PedersenGens};
use merlin::Transcript;
use rand::Rng;

use crate::{curve_tree::*, range_proof::range_proof, single_level_select_and_rerandomize::*};

use ark_ec::{
    models::short_weierstrass_jacobian::GroupAffine, AffineCurve, ProjectiveCurve,
    SWModelParameters,
};
use ark_ff::{Field, PrimeField, ToBytes};
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

impl<P: SWModelParameters> SecretKey<P> {
    pub fn new<R: Rng>(rng: &mut R) -> Self {
        Self {
            prf_key: P::ScalarField::rand(rng),
            randomness: P::ScalarField::rand(rng),
        }
    }

    pub fn public_key(&self, pc_gens: &PedersenGens<GroupAffine<P>>) -> PublicKey<P> {
        PublicKey(pc_gens.commit(self.prf_key, self.randomness))
    }
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
        MintingOutput<P0, P1>,
        Variable<P0::ScalarField>,
    ) {
        let (coin, minting_output) = Self::new(value, pk, sr_parameters, rng);

        let (_, variables) = prover.commit_vec(
            &[P0::ScalarField::from(value)],
            coin.value_randomness,
            &sr_parameters.even_parameters.bp_gens,
        );
        range_proof(prover, variables[0].into(), Some(value), 64).unwrap(); // todo what range do we want to enforce? Table of benchmarks for different powers?

        (coin, minting_output, variables[0])
    }

    pub fn new<R: Rng>(
        value: u64,
        pk: &PublicKey<P1>,
        sr_parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (Coin<P0, P1>, MintingOutput<P0, P1>) {
        // pick a random scalar and rerandomize the public key
        let pk_rerandomization = P1::ScalarField::rand(rng);
        let randomized_pk = Self::rerandomized_pk(pk, &pk_rerandomization, sr_parameters);

        // pick a random scalar to hide the coin value.
        let value_randomness = P0::ScalarField::rand(rng);
        let value_commitment = sr_parameters
            .even_parameters
            .commit(&[P0::ScalarField::from(value)], value_randomness);

        (
            Coin {
                value,
                value_randomness,
                pk_randomness: pk_rerandomization,
            },
            MintingOutput {
                value_commitment,
                public_key: randomized_pk,
            },
        )
    }

    pub fn rerandomized_pk(
        pk: &PublicKey<P1>,
        rerandomization: &P1::ScalarField,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> PublicKey<P1> {
        PublicKey(
            pk.0 + parameters
                .odd_parameters
                .pc_gens
                .B_blinding
                .mul(*rerandomization)
                .into_affine(),
        )
    }
}

#[derive(Clone, Copy)]
pub struct MintingOutput<P0: SWModelParameters, P1: SWModelParameters> {
    pub value_commitment: GroupAffine<P0>,
    pub public_key: PublicKey<P1>,
}

impl<P0, P1> MintingOutput<P0, P1>
where
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    P0::BaseField: PrimeField,
{
    /// Used to hash the commitment to the value of the coin into the scalarfield of the `odd curve`
    /// in order to homomorphically add it to the commitment to the PRF key, i.e. the public key.
    fn hash_of_value_commitment(&self) -> P1::ScalarField {
        let mut bytes = Vec::new();
        self.value_commitment.write(&mut bytes).unwrap();
        element_from_bytes_stat::<P1::ScalarField>(&bytes)
    }

    pub fn combine_into_permissible(
        &self,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> PermissibleCoin<P0, P1> {
        let hash_of_value_commitments = self.hash_of_value_commitment();
        // the secret key uses the generator for single value commitments
        let g_to_hash = parameters
            .odd_parameters
            .pc_gens
            .B
            .mul(hash_of_value_commitments);
        let pre_permissible_pk = self.public_key.0 + g_to_hash.into_affine();
        let (permissible_pk, r_permissible_pk) =
            parameters.odd_parameters.uh.permissible_commitment(
                &pre_permissible_pk,
                &parameters.odd_parameters.pc_gens.B_blinding,
            );
        let pk_x = permissible_pk.x;
        // the prf component uses the second generator of a vector commitment
        let prf_generator = parameters
            .even_parameters
            .bp_gens
            .share(0)
            .G(2)
            .collect::<Vec<_>>()[1]; // todo: not this unreadable garbage
        let per_permissible_coin = self.value_commitment + prf_generator.mul(pk_x).into();
        let (permissible_coin, r_permissible_coin) =
            parameters.even_parameters.uh.permissible_commitment(
                &per_permissible_coin,
                &parameters.even_parameters.pc_gens.B_blinding,
            );
        PermissibleCoin {
            permissible_pk,
            r_permissible_pk,
            permissible_coin,
            r_permissible_coin,
        } // todo only permissible_coin is needed for verifier
    }
}

// todo naming. Keeps track of all the randomness offsets when combining the output of mint into a permissible coin
// only the `permissible_coin` field is relevant unless you need to spend the coin.
pub struct PermissibleCoin<P0: SWModelParameters, P1: SWModelParameters> {
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
    pub minting_output: MintingOutput<P0, P1>,
    pub combined_coin: PermissibleCoin<P0, P1>,
    // pub randomized_pk: PublicKey<P1>,
    pub sk: SecretKey<P1>,
}

impl<P0, P1> SpendingInfo<P0, P1>
where
    P0: SWModelParameters + Clone,
    P1: SWModelParameters<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Clone,
    P0::BaseField: PrimeField,
{
    pub fn prove_spend<const L: usize, R: Rng>(
        self,
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
            &parameters.even_parameters.bp_gens,
        );
        assert_eq!(path.even_commitments[path.even_commitments.len() - 1], rerandomized_point);

        let fresh_pk_randomness = P1::ScalarField::rand(rng);
        let permissible_pk = self.combined_coin.permissible_pk;
        let rerandomized_public_key = permissible_pk.mul(fresh_pk_randomness).into_affine();
        single_level_select_and_rerandomize(
            even_prover,
            &parameters.odd_parameters,
            &rerandomized_public_key,
            vec![coin_variables[1]],
            Some(permissible_pk),
            Some(fresh_pk_randomness),
        );

        //show opening of rerandomized public key to x = prf_key + H(tx)
        let x = self.sk.prf_key + self.minting_output.hash_of_value_commitment();
        let (rerandomized_pk_alt, x_var) = odd_prover.commit(
            x,
            self.sk.randomness // initial randomness of commitment to the PRF key
                + self.coin_aux.pk_randomness // rerandomization done by the sender
                + self.combined_coin.r_permissible_pk // rerandomization done the network (to get a permissible point)
                + fresh_pk_randomness, // randomness from select and rerandomize
        );
        assert_eq!(rerandomized_public_key, rerandomized_pk_alt);
        let x_inverse = x.inverse().unwrap();
        //prove that t = [x^-1] * G
        let (spending_tag, x_inverse_var) = odd_prover.commit(x_inverse, P1::ScalarField::zero());

        // the first entry of the coin variables is the value of the coin.
        (path, coin_variables[0])
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use merlin::Transcript;
    use pasta::{self, pallas};
    type PallasParameters = pasta::pallas::PallasParameters;
    type VestaParameters = pasta::vesta::VestaParameters;
    type PallasP = pasta::pallas::Projective;

    #[test]
    fn test_spend() {
        let domain_string = b"prf_coin";
        let mut rng = rand::thread_rng();
        let generators_length = 1 << 13;


        let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            generators_length,
            &mut rng,
        );
        let mut pallas_prover: Prover<_, GroupAffine<PallasParameters>> =
            Prover::new(&sr_params.even_parameters.pc_gens, Transcript::new(domain_string));
        let mut vesta_prover: Prover<_, GroupAffine<VestaParameters>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, Transcript::new(domain_string));

        let sk = SecretKey::<VestaParameters>::new(&mut rng);
        let pk = sk.public_key(&sr_params.odd_parameters.pc_gens);
        
        let (coin_aux_0, mint_output_0) = Coin::<PallasParameters, VestaParameters>::new(2, &pk, &sr_params, &mut rng);
        let permissible_coin_0 = mint_output_0.combine_into_permissible(&sr_params);
        let (coin_aux_1, mint_output_1) = Coin::<PallasParameters, VestaParameters>::new(2, &pk, &sr_params, &mut rng);
        let permissible_coin_1 = mint_output_1.combine_into_permissible(&sr_params);


        let set = vec![permissible_coin_0.permissible_coin, permissible_coin_1.permissible_coin];
        let curve_tree = CurveTree::<256, PallasParameters, VestaParameters>::from_set(&set, &sr_params, Some(2));

        let spending_info_0 = SpendingInfo::<PallasParameters, VestaParameters> {
            index: 0,
            coin_aux: coin_aux_0,
            minting_output: mint_output_0,
            combined_coin: permissible_coin_0,
            sk: sk,
        };

        let (path, _val_var) = spending_info_0.prove_spend(&mut pallas_prover, &mut vesta_prover, &sr_params, &curve_tree, &mut rng);
        let pallas_proof = pallas_prover.prove(&sr_params.even_parameters.bp_gens).unwrap();
        let vesta_proof = vesta_prover.prove(&sr_params.odd_parameters.bp_gens).unwrap();


    }
}
