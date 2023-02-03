#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc(include = "../docs/inner-product-protocol.md"))]

extern crate alloc;

use alloc::borrow::Borrow;
use alloc::vec::Vec;

use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::{fields::batch_inversion, Field};
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Write,
};
use ark_std::One;
use core::iter;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::transcript::TranscriptProtocol;

#[derive(Clone, Debug)]
pub struct InnerProductProof<C: AffineRepr> {
    pub(crate) L_vec: Vec<C>,
    pub(crate) R_vec: Vec<C>,
    pub(crate) a: C::ScalarField,
    pub(crate) b: C::ScalarField,
}

impl<C: AffineRepr> InnerProductProof<C> {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut Transcript,
        Q: &C,
        G_factors: &[C::ScalarField],
        H_factors: &[C::ScalarField],
        mut G_vec: Vec<C>,
        mut H_vec: Vec<C>,
        mut a_vec: Vec<C::ScalarField>,
        mut b_vec: Vec<C::ScalarField>,
    ) -> InnerProductProof<C> {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        if n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            let l_scalars: Vec<C::ScalarField> = a_L
                .iter()
                .zip(G_factors[n..2 * n].iter())
                .map(|(a_L_i, g)| *a_L_i * g)
                .chain(
                    b_R.iter()
                        .zip(H_factors[0..n].iter())
                        .map(|(b_R_i, h)| *b_R_i * h),
                )
                .chain(iter::once(c_L))
                .collect();
            let l_points: Vec<C> = G_R
                .iter()
                .chain(H_L.iter())
                .chain(iter::once(Q))
                .copied()
                .collect();
            let L = C::Group::msm_unchecked(l_points.as_slice(), l_scalars.as_slice()).into();

            let r_scalars: Vec<C::ScalarField> = a_R
                .iter()
                .zip(G_factors[0..n].iter())
                .map(|(a_R_i, g)| *a_R_i * g)
                .chain(
                    b_L.iter()
                        .zip(H_factors[n..2 * n].iter())
                        .map(|(b_L_i, h)| *b_L_i * h),
                )
                .chain(iter::once(c_R))
                .collect();
            let r_points: Vec<C> = G_L
                .iter()
                .chain(H_R.iter())
                .chain(iter::once(Q))
                .copied()
                .collect();
            let R = C::Group::msm_unchecked(r_points.as_slice(), r_scalars.as_slice()).into();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = transcript.challenge_scalar::<C>(b"u");
            let u_inv = if let Some(res) = u.inverse() {
                res
            } else {
                panic!("u challenge is zero");
            };

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = C::Group::msm_unchecked(
                    &[G_L[i], G_R[i]],
                    &[(u_inv * G_factors[i]), (u * G_factors[n + i])],
                )
                .into();
                H_L[i] = C::Group::msm_unchecked(
                    &[H_L[i], H_R[i]],
                    &[(u * H_factors[i]), (u_inv * H_factors[n + i])],
                )
                .into();
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        while n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            let L = C::Group::msm_unchecked(
                G_R.iter()
                    .chain(H_L.iter())
                    .chain(iter::once(Q))
                    .copied()
                    .collect::<Vec<C>>()
                    .as_slice(),
                a_L.iter()
                    .chain(b_R.iter())
                    .chain(iter::once(&c_L))
                    .copied()
                    .collect::<Vec<C::ScalarField>>()
                    .as_slice(),
            )
            .into();

            let R = C::Group::msm_unchecked(
                G_L.iter()
                    .chain(H_R.iter())
                    .chain(iter::once(Q))
                    .copied()
                    .collect::<Vec<C>>()
                    .as_slice(),
                a_R.iter()
                    .chain(b_L.iter())
                    .chain(iter::once(&c_R))
                    .copied()
                    .collect::<Vec<C::ScalarField>>()
                    .as_slice(),
            )
            .into();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = transcript.challenge_scalar::<C>(b"u");
            let u_inv = if let Some(res) = u.inverse() {
                res
            } else {
                panic!("u challenge is zero");
            };

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = C::Group::msm_unchecked(&[G_L[i], G_R[i]], &[u_inv, u]).into();
                H_L[i] = C::Group::msm_unchecked(&[H_L[i], H_R[i]], &[u, u_inv]).into();
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
            // todo collapse iteration one and rest?
        }

        InnerProductProof {
            L_vec,
            R_vec,
            a: a[0],
            b: b[0],
        }
    }

    /// Computes three vectors of verification scalars \\([u\_{i}^{2}]\\), \\([u\_{i}^{-2}]\\) and \\([s\_{i}]\\) for combined multiscalar multiplication
    /// in a parent protocol. See [inner product protocol notes](index.html#verification-equation) for details.
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation within the inner product proof.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<
        (
            Vec<C::ScalarField>,
            Vec<C::ScalarField>,
            Vec<C::ScalarField>,
        ),
        ProofError,
    > {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }

        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript

        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges.push(transcript.challenge_scalar::<C>(b"u"));
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1

        let mut challenges_inv = challenges.clone();
        batch_inversion(&mut challenges_inv);
        // allinv should be product of all inverses
        let mut allinv: C::ScalarField = One::one();

        // 3. Compute u_i^2 and (1/u_i)^2

        for i in 0..lg_n {
            // update allinv
            allinv *= challenges_inv[i];
            challenges[i].square_in_place();
            challenges_inv[i].square_in_place();
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;

        // 4. Compute s values inductively.

        let mut s = Vec::with_capacity(n);
        s.push(allinv);
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            s.push(s[i - k] * u_lg_i_sq);
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

    /// This method is for testing that proof generation work,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify<IG, IH>(
        &self,
        n: usize,
        transcript: &mut Transcript,
        G_factors: IG,
        H_factors: IH,
        P: &C,
        Q: &C,
        G: &[C],
        H: &[C],
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<C::ScalarField>,
        IH: IntoIterator,
        IH::Item: Borrow<C::ScalarField>,
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| (self.a * s_i) * g_i.borrow())
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| (self.b * s_i_inv) * h_i.borrow());

        let neg_u_sq = u_sq.iter().map(|ui| -(*ui));
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| -(*ui));

        let expect_P = C::Group::msm_unchecked(
            iter::once(Q)
                .chain(G.iter())
                .chain(H.iter())
                .chain(self.L_vec.iter())
                .chain(self.R_vec.iter())
                .copied()
                .collect::<Vec<C>>()
                .as_slice(),
            iter::once(self.a * self.b)
                .chain(g_times_a_times_s)
                .chain(h_times_b_div_s)
                .chain(neg_u_sq)
                .chain(neg_u_inv_sq)
                .collect::<Vec<C::ScalarField>>()
                .as_slice(),
        );

        if expect_P.into() == *P {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    pub fn serialized_size(&self, compress: Compress) -> usize {
        // size of the two scalars
        let scalars_size = self.a.serialized_size(compress) * 2;
        // size of the 2 point vectors (should be equal)
        let l_and_r_size = self.L_vec.serialized_size(compress) * 2;
        scalars_size + l_and_r_size
    }
}

impl<C: AffineRepr> Valid for InnerProductProof<C> {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}
impl<C: AffineRepr> CanonicalDeserialize for InnerProductProof<C> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, SerializationError> {
        Ok(Self {
            L_vec: Vec::<C>::deserialize_with_mode(&mut reader, compress, validate)?,
            R_vec: Vec::<C>::deserialize_with_mode(&mut reader, compress, validate)?,
            a: C::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?,
            b: C::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?,
        })
    }
}

impl<C: AffineRepr> CanonicalSerialize for InnerProductProof<C> {
    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    ///
    /// For vectors of length `n` the proof size is
    /// \\(32 \cdot (2\lg n+2)\\) bytes.
    fn serialized_size(&self, mode: Compress) -> usize {
        // size of the two scalars
        let scalars_size = self.a.serialized_size(mode) * 2;
        // size of the 2 point vectors (should be equal)
        let l_and_r_size = self.L_vec.serialized_size(mode) * 2;
        scalars_size + l_and_r_size
    }

    /// Serializes the proof into a byte array of \\(2n+2\\) 32-byte elements.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.L_vec.serialize_with_mode(&mut writer, compress)?;
        self.R_vec.serialize_with_mode(&mut writer, compress)?;
        self.a.serialize_with_mode(&mut writer, compress)?;
        self.b.serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product<S: Field>(a: &[S], b: &[S]) -> S {
    let mut out = S::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_pallas::Affine;
    use ark_std::UniformRand;

    type F = <Affine as AffineRepr>::ScalarField;

    use crate::util;

    fn test_helper_create(n: usize) {
        use ark_std::rand::{prelude::StdRng, Rng, SeedableRng};
        let seed = [
            1, 0, 0, 0, 23, 0, 0, 0, 200, 1, 0, 0, 210, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0,
        ];
        let mut rng = StdRng::from_seed(seed);

        use crate::generators::BulletproofGens;
        let bp_gens = BulletproofGens::<Affine>::new(n, 1);
        let G: Vec<_> = bp_gens.share(0).G(n).copied().collect();
        let H: Vec<_> = bp_gens.share(0).H(n).copied().collect();

        // Q would be determined upstream in the protocol, so we pick a random one.
        let Q = util::affine_from_bytes_tai::<Affine>(b"test point");

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let b: Vec<_> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let c = inner_product(&a, &b);

        let G_factors: Vec<_> = iter::repeat(<Affine as AffineRepr>::ScalarField::one())
            .take(n)
            .collect();

        // y_inv is (the inverse of) a random challenge
        let y_inv: F = rng.gen();
        let H_factors: Vec<F> = util::exp_iter(y_inv).take(n).collect();

        // P would be determined upstream, but we need a correct P to check the proof.
        //
        // To generate P = <a,G> + <b,H'> + <a,b> Q, compute
        //             P = <a,G> + <b',H> + <a,b> Q,
        // where b' = b \circ y^(-n)
        let b_prime = b.iter().zip(util::exp_iter(y_inv)).map(|(bi, yi)| *bi * yi);
        // a.iter() has Item=&Scalar, need Item=Scalar to chain with b_prime
        let a_prime = a.iter().copied();

        let P = <Affine as AffineRepr>::Group::msm_unchecked(
            G.iter()
                .chain(H.iter())
                .chain(iter::once(&Q))
                .copied()
                .collect::<Vec<_>>()
                .as_slice(),
            a_prime
                .chain(b_prime)
                .chain(iter::once(c))
                .map(|s| s.into())
                .collect::<Vec<_>>()
                .as_slice(),
        )
        .into();

        let mut verifier = Transcript::new(b"innerproducttest");
        let proof = InnerProductProof::create(
            &mut verifier,
            &Q,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        );

        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                n,
                &mut verifier,
                iter::repeat(F::one()).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &Q,
                &G,
                &H
            )
            .is_ok());

        let mut buf = Vec::with_capacity(proof.serialized_size(Compress::Yes));
        proof.serialize_compressed(&mut buf).unwrap();
        let proof = InnerProductProof::deserialize_compressed(&buf[..]).unwrap();
        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                n,
                &mut verifier,
                iter::repeat(F::one()).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &Q,
                &G,
                &H
            )
            .is_ok());
    }

    #[test]
    fn make_ipp_1() {
        test_helper_create(1);
    }

    #[test]
    fn make_ipp_2() {
        test_helper_create(2);
    }

    #[test]
    fn make_ipp_4() {
        test_helper_create(4);
    }

    #[test]
    fn make_ipp_32() {
        test_helper_create(32);
    }

    #[test]
    fn make_ipp_64() {
        test_helper_create(64);
    }

    #[test]
    fn test_inner_product() {
        let a = vec![F::from(1u64), F::from(2u64), F::from(3u64), F::from(4u64)];
        let b = vec![F::from(2u64), F::from(3u64), F::from(4u64), F::from(5u64)];
        assert_eq!(F::from(40u64), inner_product(&a, &b));
    }
}
