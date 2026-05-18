#![deny(missing_docs)]
#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use ark_ec::AffineRepr;
use ark_ff::PrimeField;

use dock_crypto_utils::ff::inner_product;

/*/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
#[derive(ZeroizeOnDrop)]
pub struct VecPoly1<F: PrimeField>(pub Vec<F>, pub Vec<F>);*/

/*/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[derive(ZeroizeOnDrop)]
pub struct VecPoly3<F: PrimeField>(pub Vec<F>, pub Vec<F>, pub Vec<F>, pub Vec<F>);*/

/// The general case for Vector CP. This is a polynomial of degree `d` where each coefficient is a vector of length `n`.
pub struct VecPoly<F: PrimeField>(
    /// Outer vector has size `d + 1`, inner vector has size `n` where `n` is the size of the vector and `d` is the degree of the polynomial.
    Vec<Vec<F>>,
);

pub struct Poly<F: PrimeField>(Vec<F>);

impl<F: PrimeField> Poly<F> {
    pub fn zero(deg: usize) -> Self {
        Poly(vec![F::zero(); deg + 1])
    }

    #[inline]
    pub fn coeff_mut(&mut self) -> &mut [F] {
        &mut self.0
    }

    #[inline]
    pub fn deg(&self) -> usize {
        self.0.len() - 1
    }

    pub fn eval(&self, x: F) -> F {
        let mut out = F::zero();
        // Horner's rule, `a_0 + a_1 * x + a_2 * x^2 + ... + a_n * x^n = a_0 + x(a_1 + x(a_2 + x(... + x(a_{n-1} + x(a_n + 0))))`
        for v in self.0.iter().rev() {
            out *= x;
            out += v;
        }
        out
    }
}

impl<F: PrimeField> From<Vec<F>> for Poly<F> {
    fn from(v: Vec<F>) -> Self {
        Self(v)
    }
}

impl<F: PrimeField> VecPoly<F> {
    #[inline]
    pub fn coeff_mut(&mut self, deg: usize) -> &mut [F] {
        &mut self.0[deg]
    }

    #[inline]
    pub fn deg(&self) -> usize {
        self.0.len() - 1
    }

    #[inline]
    pub fn coeff(&self, deg: usize) -> &[F] {
        &self.0[deg]
    }

    pub fn zero(n: usize, deg: usize) -> Self {
        VecPoly(vec![vec![F::zero(); n]; deg + 1])
    }

    pub fn eval(&self, x: F) -> Vec<F> {
        let n = self.0[0].len();
        let mut out = vec![F::zero(); n];
        for i in 0..n {
            for v in self.0.iter().rev() {
                out[i] *= x;
                out[i] += v[i];
            }
        }
        out
    }

    pub fn inner_product(lhs: &Self, rhs: &Self) -> Poly<F> {
        let l_deg = lhs.deg();
        let r_deg = rhs.deg();
        // degree of resulting polynomial
        let deg = l_deg + r_deg;

        // log::debug!("combined degree: {}", deg);

        let mut res = Poly::zero(deg);

        for d in 0..(deg + 1) {
            // for each degree `d` of resulting polynomial, find all valid pairs of degrees (l, r) of
            // input polynomials such that `l + r = d`
            for l in 0..(d + 1) {
                let r = d - l;
                if l_deg >= l && r_deg >= r {
                    res.coeff_mut()[d] += inner_product(lhs.coeff(l), rhs.coeff(r));
                }
            }
        }
        res
    }
}

/*/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
#[derive(ZeroizeOnDrop)]
pub struct Poly2<F: PrimeField>(pub F, pub F, pub F);*/

/*/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
#[derive(ZeroizeOnDrop)]
pub struct Poly6<F: PrimeField> {
    pub t1: F,
    pub t2: F,
    pub t3: F,
    pub t4: F,
    pub t5: F,
    pub t6: F,
}*/

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp<F: PrimeField> {
    x: F,
    next_exp_x: F,
}

impl<F: PrimeField> Iterator for ScalarExp<F> {
    type Item = F;

    fn next(&mut self) -> Option<F> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter<F: PrimeField>(x: F) -> ScalarExp<F> {
    let next_exp_x = F::one();
    ScalarExp { x, next_exp_x }
}

pub fn add_vec<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    if a.len() != b.len() {
        // throw some error
        //log::debug!("lengths of vectors don't match for vector addition");
    }
    let mut out = vec![F::zero(); b.len()];
    for i in 0..a.len() {
        out[i] = a[i] + b[i];
    }
    out
}

/*impl<F: PrimeField> VecPoly1<F> {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![F::zero(); n], vec![F::zero(); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1<F>) -> Poly2<F> {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: F) -> Vec<F> {
        let n = self.0.len();
        let mut out = vec![F::zero(); n];
        for i in 0..n {
            out[i] = self.0[i] + self.1[i] * x;
        }
        out
    }
}*/

/*impl<F: PrimeField> VecPoly3<F> {
    pub fn zero(n: usize) -> Self {
        VecPoly3(
            vec![F::zero(); n],
            vec![F::zero(); n],
            vec![F::zero(); n],
            vec![F::zero(); n],
        )
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    ///
    /// This is the case in the constraint system proof.
    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> Poly6<F> {
        // TODO: make checks that l_poly.0 and r_poly.2 are zero.

        let t1 = inner_product(&lhs.1, &rhs.0);
        let t2 = inner_product(&lhs.1, &rhs.1) + inner_product(&lhs.2, &rhs.0);
        let t3 = inner_product(&lhs.2, &rhs.1) + inner_product(&lhs.3, &rhs.0);
        let t4 = inner_product(&lhs.1, &rhs.3) + inner_product(&lhs.3, &rhs.1);
        let t5 = inner_product(&lhs.2, &rhs.3);
        let t6 = inner_product(&lhs.3, &rhs.3);

        Poly6 {
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    pub fn eval(&self, x: F) -> Vec<F> {
        let n = self.0.len();
        let mut out = vec![F::zero(); n];
        for i in 0..n {
            out[i] = self.0[i] + x * (self.1[i] + x * (self.2[i] + x * self.3[i]));
        }
        out
    }
}*/

/*impl<F: PrimeField> Poly2<F> {
    pub fn eval(&self, x: F) -> F {
        self.0 + x * (self.1 + x * self.2)
    }
}*/

/*impl<F: PrimeField> Poly6<F> {
    pub fn eval(&self, x: F) -> F {
        x * (self.t1 + x * (self.t2 + x * (self.t3 + x * (self.t4 + x * (self.t5 + x * self.t6)))))
    }
}*/

/*/// Takes the sum of all the powers of `x`, up to `n`
/// If `n` is a power of 2, it uses the efficient algorithm with `2*lg n` multiplications and additions.
/// If `n` is not a power of 2, it uses the slow algorithm with `n` multiplications and additions.
/// In the Bulletproofs case, all calls to `sum_of_powers` should have `n` as a power of 2.
pub fn sum_of_powers<F: PrimeField>(x: &F, n: usize) -> F {
    if !n.is_power_of_two() {
        return sum_of_powers_slow(x, n);
    }
    if n == 0 || n == 1 {
        return F::from(n as u64);
    }
    let mut m = n;
    let mut result = F::one() + x;
    let mut factor = *x;
    while m > 2 {
        factor = factor * factor;
        result = result + factor * result;
        m /= 2;
    }
    result
}

// takes the sum of all of the powers of x, up to n
fn sum_of_powers_slow<F: PrimeField>(x: &F, n: usize) -> F {
    exp_iter(*x).take(n).sum()
}*/

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}

/// Hash a byte string to a curve point using try and increment
pub fn affine_from_bytes_tai<C: AffineRepr>(bytes: &[u8]) -> Option<C> {
    use sha3::{Digest, Sha3_256};

    for i in 0..=u8::MAX {
        let mut sha = Sha3_256::new();
        sha.update(bytes);
        sha.update([i]);
        let result = sha.finalize();
        let res = C::from_random_bytes(result.as_slice());
        if let Some(point) = res {
            return Some(point.clear_cofactor());
        }
    }
    None
}

pub fn field_as_bytes<F: PrimeField>(field: &F) -> Vec<u8> {
    let mut bytes = Vec::new();
    if let Err(e) = field.serialize_compressed(&mut bytes) {
        panic!("{}", e)
    }
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_log::test;

    use ark_pallas::*;

    type Scalar = <Affine as AffineRepr>::ScalarField;
    // use ark_ff::{One, Zero};

    #[test]
    fn exp_2_is_powers_of_2() {
        let exp_2: Vec<_> = exp_iter(Scalar::from(2u64)).take(4).collect();

        assert_eq!(exp_2[0], Scalar::from(1u64));
        assert_eq!(exp_2[1], Scalar::from(2u64));
        assert_eq!(exp_2[2], Scalar::from(4u64));
        assert_eq!(exp_2[3], Scalar::from(8u64));
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product(&a, &b));
    }

    /*#[test]
    fn test_sum_of_powers() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), sum_of_powers(&x, 0));
        assert_eq!(sum_of_powers_slow(&x, 1), sum_of_powers(&x, 1));
        assert_eq!(sum_of_powers_slow(&x, 2), sum_of_powers(&x, 2));
        assert_eq!(sum_of_powers_slow(&x, 4), sum_of_powers(&x, 4));
        assert_eq!(sum_of_powers_slow(&x, 8), sum_of_powers(&x, 8));
        assert_eq!(sum_of_powers_slow(&x, 16), sum_of_powers(&x, 16));
        assert_eq!(sum_of_powers_slow(&x, 32), sum_of_powers(&x, 32));
        assert_eq!(sum_of_powers_slow(&x, 64), sum_of_powers(&x, 64));
    }

    #[test]
    fn test_sum_of_powers_slow() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), Scalar::zero());
        assert_eq!(sum_of_powers_slow(&x, 1), Scalar::one());
        assert_eq!(sum_of_powers_slow(&x, 2), Scalar::from(11u64));
        assert_eq!(sum_of_powers_slow(&x, 3), Scalar::from(111u64));
        assert_eq!(sum_of_powers_slow(&x, 4), Scalar::from(1111u64));
        assert_eq!(sum_of_powers_slow(&x, 5), Scalar::from(11111u64));
        assert_eq!(sum_of_powers_slow(&x, 6), Scalar::from(111111u64));
    }*/
}
