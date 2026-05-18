use crate::util::GeneratorMultiplesSource;
use crate::{DivisorCurve, DivisorPoly, error::Error, new_divisor};
use ark_ec::AdditiveGroup;
use ark_ec::short_weierstrass::Projective;
use ark_ff::{BigInteger, PrimeField};
use ark_std::borrow::Borrow;
use ark_std::{vec, vec::Vec};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// The decomposition of a scalar.
///
/// The decomposition ($d$) of a scalar ($s$) has the following two properties:
///
/// - $\sum^{\mathsf{NUM_BITS} - 1}_{i=0} d_i * 2^i = s$
/// - $\sum^{\mathsf{NUM_BITS} - 1}_{i=0} d_i = \mathsf{NUM_BITS}$
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct ScalarDecomposition<F: PrimeField> {
    scalar: F,
    decomposition: Vec<u64>,
}

impl<F: PrimeField> ScalarDecomposition<F> {
    /// Decompose a non-zero scalar.
    ///
    /// Returns an error if the scalar is zero.
    ///
    /// This function is constant time if the scalar is non-zero.
    pub fn new(scalar: F) -> Result<Self, Error> {
        if scalar == F::ZERO {
            return Err(Error::ZeroScalar);
        }

        /*
          We need the sum of the coefficients to equal F::NUM_BITS. The scalar's bits will be less than
          F::NUM_BITS. Accordingly, we need to increment the sum of the coefficients without
          incrementing the scalar represented. We do this by finding the highest non-0 coefficient,
          decrementing it, and increasing the immediately less significant coefficient by 2. This
          increases the sum of the coefficients by 1 (-1+2=1).
        */
        let num_bits = u64::from(F::MODULUS_BIT_SIZE);

        // Obtain the bits of the scalar
        let num_bits_usize = usize::try_from(num_bits).unwrap();
        let mut decomposition = vec![0; num_bits_usize];
        let scalar_bigint = scalar.into_bigint();
        for (i, bit) in scalar_bigint
            .to_bits_le()
            .into_iter()
            .take(num_bits_usize)
            .enumerate()
        {
            decomposition[i] = u64::from(bit);
        }

        // The following algorithm only works if the value of the scalar exceeds num_bits
        // If it isn't, we increase it by the modulus such that it does exceed num_bits
        {
            let mut less_than_num_bits = Choice::from(0);
            for i in 0..num_bits {
                // F does not implement ConstantTimeEq
                // less_than_num_bits |= scalar.ct_eq(&F::from(i));
                less_than_num_bits =
                    less_than_num_bits | Choice::from(u8::from(scalar == F::from(i)));
            }
            let mut decomposition_of_modulus = vec![0; num_bits_usize];
            // Decompose negative one
            let neg_one_bigint = (-F::ONE).into_bigint();
            for (i, bit) in neg_one_bigint
                .to_bits_le()
                .into_iter()
                .take(num_bits_usize)
                .enumerate()
            {
                decomposition_of_modulus[i] = u64::from(bit);
            }
            // Increment it by one
            decomposition_of_modulus[0] += 1;

            // Add the decomposition onto the decomposition of the modulus
            for i in 0..num_bits_usize {
                let new_decomposition = <_>::conditional_select(
                    &decomposition[i],
                    &(decomposition[i] + decomposition_of_modulus[i]),
                    less_than_num_bits,
                );
                decomposition[i] = new_decomposition;
            }
        }

        // Calculate the sum of the coefficients
        let mut sum_of_coefficients: u64 = 0;
        for decomposition in &decomposition {
            sum_of_coefficients += *decomposition;
        }

        /*
          Now, because we added a log2(k)-bit number to a k-bit number, we may have our sum of
          coefficients be *too high*. We attempt to reduce the sum of the coefficients accordingly.

          This algorithm is guaranteed to complete as expected. Take the sequence `222`. `222` becomes
          `032` becomes `013`. Even if the next coefficient in the sequence is `2`, the third
          coefficient will be reduced once and the next coefficient (`2`, increased to `3`) will only
          be eligible for reduction once. This demonstrates, even for a worst case of log2(k) `2`s
          followed by `1`s (as possible if the modulus is a Mersenne prime), the log2(k) `2`s can be
          reduced as necessary so long as there is a single coefficient after (requiring the entire
          sequence be at least of length log2(k) + 1). For a 2-bit number, log2(k) + 1 == 2, so this
          holds for any odd prime field.

          To fully type out the demonstration for the Mersenne prime 3, with scalar to encode 1 (the
          highest value less than the number of bits):

          10 - Little-endian bits of 1
          21 - Little-endian bits of 1, plus the modulus
          02 - After one reduction, where the sum of the coefficients does in fact equal 2 (the target)
        */
        {
            let mut log2_num_bits = 0;
            while (1 << log2_num_bits) < num_bits {
                log2_num_bits += 1;
            }

            for _ in 0..log2_num_bits {
                // If the sum of coefficients is the number of bits, we're done
                let mut done = sum_of_coefficients.ct_eq(&num_bits);

                for i in 0..(num_bits_usize - 1) {
                    let should_act = (!done) & decomposition[i].ct_gt(&1);
                    // Subtract 2 from this coefficient
                    let amount_to_sub = <_>::conditional_select(&0, &2, should_act);
                    decomposition[i] -= amount_to_sub;
                    // Add 1 to the next coefficient
                    let amount_to_add = <_>::conditional_select(&0, &1, should_act);
                    decomposition[i + 1] += amount_to_add;

                    // Also update the sum of coefficients
                    sum_of_coefficients -= <_>::conditional_select(&0, &1, should_act);

                    // If we updated the coefficients this loop iter, we're done for this loop iter
                    done |= should_act;
                }
            }
        }

        for _ in 0..num_bits {
            // If the sum of coefficients is the number of bits, we're done
            let mut done = sum_of_coefficients.ct_eq(&num_bits);

            // Find the highest coefficient currently non-zero
            for i in (1..decomposition.len()).rev() {
                // If this is non-zero, we should decrement this coefficient if we haven't already
                // decremented a coefficient this round
                let is_non_zero = !(0.ct_eq(&decomposition[i]));
                let should_act = (!done) & is_non_zero;

                // Update this coefficient and the prior coefficient
                let amount_to_sub = <_>::conditional_select(&0, &1, should_act);
                decomposition[i] -= amount_to_sub;

                let amount_to_add = <_>::conditional_select(&0, &2, should_act);
                // i must be at least 1, so i - 1 will be at least 0 (meaning it's safe to index with)
                decomposition[i - 1] += amount_to_add;

                // Also update the sum of coefficients
                sum_of_coefficients += <_>::conditional_select(&0, &1, should_act);

                // If we updated the coefficients this loop iter, we're done for this loop iter
                done |= should_act;
            }
        }

        debug_assert!(bool::from(
            decomposition.iter().sum::<u64>().ct_eq(&num_bits)
        ));

        Ok(ScalarDecomposition {
            scalar,
            decomposition,
        })
    }

    /// The scalar.
    pub fn scalar(&self) -> &F {
        &self.scalar
    }

    /// The decomposition of the scalar.
    pub fn decomposition(&self) -> &[u64] {
        &self.decomposition
    }

    /// A divisor to prove a scalar multiplication.
    ///
    /// The divisor will interpolate $-(s \cdot G)$ with $d_i$ instances of $2^i \cdot G$.
    ///
    /// This function executes in constant time with regards to the scalar.
    ///
    /// This function MAY return an error if the interpolator is insufficient or if invalid arguments are provided.
    pub fn scalar_mul_divisor<C: DivisorCurve<ScalarField = F>>(
        &self,
        generator_source: impl GeneratorMultiplesSource<C>,
    ) -> Result<DivisorPoly<C::BaseField>, Error> {
        // 1 is used for the resulting point, NUM_BITS is used for the decomposition, and then we store
        // one additional index in a usize for the points we shouldn't write at all (hence the +2)
        // This check ensures MODULUS_BIT_SIZE + 2 fits in usize, which should always be true in practice
        let _ = usize::try_from(F::MODULUS_BIT_SIZE + 2)
            .expect("MODULUS_BIT_SIZE + 2 didn't fit in usize");
        let num_bits = u64::from(F::MODULUS_BIT_SIZE);
        let mut divisor_points = vec![<Projective<C>>::ZERO; num_bits as usize + 1];

        let mut generator_iter = generator_source.iter();
        let generator: Projective<C> = generator_iter.next().unwrap();

        // Write the inverse of the resulting point
        // divisor_points[0] = -(generator * self.scalar)
        divisor_points[0] = generator * (-self.scalar);
        let mut generator_point: Projective<C> = generator;

        // Write the decomposition
        let mut write_above: u64 = 0;
        for (j, coefficient) in self.decomposition.iter().enumerate() {
            for i in 1..=num_bits {
                if i > write_above {
                    divisor_points[i as usize] = generator_point;
                }
            }

            write_above += coefficient;
            if j < (self.decomposition.len() - 1) {
                generator_point = generator_iter.next().unwrap();
            }
        }

        // Create a divisor out of the points
        let res = new_divisor::<C>(&divisor_points, C::interpolator_for_scalar_mul().borrow())?;
        divisor_points.zeroize();
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar_decomposition::ScalarDecomposition;
    use crate::util::{DirectGenerator, DiscreteLogParameter, GeneratorTable};
    use ark_ec::short_weierstrass::Projective;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_std::UniformRand;
    use rand::prelude::StdRng;
    use rand_core::SeedableRng;
    use std::time::{Duration, Instant};

    use crate::curves::pallas::PallasParams;
    use ark_pallas::{Fq, Fr, PallasConfig};
    type PallasBase = Fq;
    type PallasScalar = Fr;

    use crate::curves::vesta::VestaParams;
    use ark_vesta::VestaConfig;
    type VestaBase = Fr;
    type VestaScalar = Fq;

    use crate::curves::helios::HeliosParams;
    use ark_helios::HeliosConfig;
    type HeliosBase = ark_helios::Fq;
    type HeliosScalar = ark_helios::Fr;

    use crate::curves::selene::SeleneParams;
    use ark_selene::SeleneConfig;
    type SeleneBase = ark_selene::Fq;
    type SeleneScalar = ark_selene::Fr;

    use crate::curves::wei25519::Wei25519Params;
    use ark_wei25519::Wei25519Config;
    type Wei25519Base = ark_wei25519::Fq;
    type Wei25519Scalar = ark_wei25519::Fr;

    fn to_xy_helper<C: DivisorCurve>(p: Projective<C>) -> Option<(C::BaseField, C::BaseField)> {
        let a = p.into_affine();
        if a.is_zero() { None } else { Some((a.x, a.y)) }
    }

    #[test]
    fn generator_source_equivalence() {
        fn check<C: DivisorCurve<BaseField = B>, Params: DiscreteLogParameter, B: PrimeField>(
            count: usize,
        ) {
            let mut rng = StdRng::seed_from_u64(0);
            let generator = Projective::<C>::rand(&mut rng);

            // Create generator table
            let table = GeneratorTable::<B, Params>::new::<C>(generator);

            let mut time_direct = Duration::default();
            let mut time_table = Duration::default();

            for _ in 0..count {
                let scalar = C::ScalarField::rand(&mut rng);
                let decomposition = ScalarDecomposition::new(scalar).unwrap();

                let start = Instant::now();
                let divisor_direct = decomposition
                    .scalar_mul_divisor(DirectGenerator::from(generator))
                    .unwrap();
                time_direct += start.elapsed();

                let start = Instant::now();
                let divisor_table = decomposition.scalar_mul_divisor::<C>(&table).unwrap();
                time_table += start.elapsed();

                assert_eq!(divisor_direct, divisor_table);
            }

            println!(
                "For {count} iters, direct took {:?} and table took {:?}",
                time_direct, time_table
            )
        }

        let count = 10;

        println!("Testing Pallas");
        check::<PallasConfig, PallasParams, PallasBase>(count);

        println!("Testing Vesta");
        check::<VestaConfig, VestaParams, VestaBase>(count);

        println!("Testing Helios");
        check::<HeliosConfig, HeliosParams, HeliosBase>(count);

        println!("Testing Selene");
        check::<SeleneConfig, SeleneParams, SeleneBase>(count);

        println!("Testing Wei25519");
        check::<Wei25519Config, Wei25519Params, Wei25519Base>(count);
    }

    #[test]
    fn scalar_mul_divisor_correctness() {
        fn check<C: DivisorCurve<BaseField = B, ScalarField = S>, B: PrimeField, S: PrimeField>(
            count: usize,
        ) {
            let mut rng = StdRng::seed_from_u64(0);

            let mut decomposition_times = Vec::new();
            let mut scalar_mul_times = Vec::new();

            assert!(ScalarDecomposition::new(S::ZERO).is_err());

            let mut powers_of_2 = vec![S::ONE];
            for i in 1..S::MODULUS_BIT_SIZE as usize {
                powers_of_2.push(powers_of_2[i - 1].double());
            }

            for i in 0..count + 1 {
                let scalar = if i == 0 {
                    S::ONE
                } else {
                    let mut scalar = S::rand(&mut rng);
                    while scalar == S::ZERO || scalar == S::ONE {
                        scalar = S::rand(&mut rng);
                    }
                    scalar
                };

                let decomposition_start = Instant::now();
                let decomposition = ScalarDecomposition::new(scalar).unwrap();
                decomposition_times.push(decomposition_start.elapsed());

                let coeffs = decomposition.decomposition();
                assert_eq!(coeffs.len(), S::MODULUS_BIT_SIZE as usize);

                // Sum of coefficients is modulus bits
                let sum = coeffs.iter().sum::<u64>();
                assert_eq!(sum, S::MODULUS_BIT_SIZE as u64);

                // Verify reconstruction
                let mut reconstructed = S::ZERO;
                for (j, &coeff) in coeffs.into_iter().enumerate() {
                    reconstructed += powers_of_2[j] * S::from(coeff);
                }
                assert_eq!(reconstructed, scalar);

                let generator = Projective::<C>::rand(&mut rng);

                let mul_start = Instant::now();
                let poly = decomposition
                    .scalar_mul_divisor(DirectGenerator::from(generator))
                    .unwrap();
                scalar_mul_times.push(mul_start.elapsed());

                // Vanishes at -(s * G)
                let neg_s_g = generator * (-scalar);
                let (x, y) = to_xy_helper::<C>(neg_s_g).unwrap();
                assert_eq!(poly.eval(x, y), B::ZERO);

                // Vanishes at 2^i * G for each coefficient count
                let mut p = generator;
                for &coeff in coeffs {
                    if coeff > 0 {
                        let (x, y) = to_xy_helper::<C>(p).unwrap();
                        assert_eq!(poly.eval(x, y), B::ZERO);
                    }
                    p = p.double();
                }
            }

            decomposition_times.sort();
            scalar_mul_times.sort();

            let decomposition_median = decomposition_times[decomposition_times.len() / 2];
            let scalar_mul_median = scalar_mul_times[scalar_mul_times.len() / 2];

            println!(
                "For {} iterations, median decomposition time {:?}, scalar_mul_divisor time {:?}",
                count + 1,
                decomposition_median,
                scalar_mul_median
            );
        }

        let count = 30;

        println!("Testing Pallas");
        check::<PallasConfig, PallasBase, PallasScalar>(count);

        println!("Testing Vesta");
        check::<VestaConfig, VestaBase, VestaScalar>(count);

        println!("Testing Helios");
        check::<HeliosConfig, HeliosBase, HeliosScalar>(count);

        println!("Testing Selene");
        check::<SeleneConfig, SeleneBase, SeleneScalar>(count);

        println!("Testing Wei25519");
        check::<Wei25519Config, Wei25519Base, Wei25519Scalar>(count);
    }
}
