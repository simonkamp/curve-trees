use crate::error::Error;
use ark_ff::PrimeField;
use ark_std::{vec, vec::Vec};
use core::ops::{Add, Mul, Neg, Sub};
use zeroize::Zeroize;

/// A structure representing a Polynomial with x^i, y^i, and y^i * x^j terms.
///
/// This represents a polynomial in the form f(x, y) = A(x) - yB(x), where A and B
/// are univariate polynomials in x, reduced modulo the curve equation y^2 = x^3 + Ax + B.
#[derive(Clone, Debug, Zeroize, Eq)]
pub struct DivisorPoly<F: PrimeField> {
    /// The coefficient for the `y^1` term.
    /// After reduction modulo `y^2 = x^3 + Ax + B`, only a single degree-1 `y` term remains.
    pub y_coefficient: F,
    /// `c[j] * y^1 * x^(j + 1)`
    /// After reduction there is only one y-degree, so this is a flat vec of x-coefficients
    /// for the mixed `y x^j` terms.
    pub yx_coefficients: Vec<F>,
    /// `c[i] * x^(i + 1)`
    pub x_coefficients: Vec<F>,
    /// Coefficient for `x^0`, `y^0`, and `x^0 y^0` (the coefficient for 1)
    pub zero_coefficient: F,
}

impl<F: PrimeField> PartialEq for DivisorPoly<F> {
    // This is not constant time and is not meant to be
    fn eq(&self, b: &DivisorPoly<F>) -> bool {
        if self.y_coefficient != b.y_coefficient {
            return false;
        }

        // `yx_coefficients` should be same of both except one of `yx_coefficients` could be padded with 0s.
        {
            let mutual_yx_coefficients = self.yx_coefficients.len().min(b.yx_coefficients.len());
            if self.yx_coefficients[..mutual_yx_coefficients]
                != b.yx_coefficients[..mutual_yx_coefficients]
            {
                return false;
            }
            for coeff in &self.yx_coefficients[mutual_yx_coefficients..] {
                if *coeff != F::zero() {
                    return false;
                }
            }
            for coeff in &b.yx_coefficients[mutual_yx_coefficients..] {
                if *coeff != F::zero() {
                    return false;
                }
            }
        }

        // `x_coefficients` should be same of both except one of `x_coefficients` could be padded with 0s.
        {
            let mutual_x_coefficients = self.x_coefficients.len().min(b.x_coefficients.len());
            if self.x_coefficients[..mutual_x_coefficients]
                != b.x_coefficients[..mutual_x_coefficients]
            {
                return false;
            }
            for coeff in &self.x_coefficients[mutual_x_coefficients..] {
                if *coeff != F::zero() {
                    return false;
                }
            }
            for coeff in &b.x_coefficients[mutual_x_coefficients..] {
                if *coeff != F::zero() {
                    return false;
                }
            }
        }

        self.zero_coefficient == b.zero_coefficient
    }
}

impl<F: PrimeField> DivisorPoly<F> {
    /// Create a zero polynomial.
    ///
    /// Returns a polynomial with all coefficients set to zero.
    pub fn zero() -> Self {
        DivisorPoly {
            y_coefficient: F::zero(),
            yx_coefficients: vec![],
            x_coefficients: vec![],
            zero_coefficient: F::zero(),
        }
    }

    /// Create a polynomial representing a constant
    pub fn constant(c: F) -> Self {
        DivisorPoly {
            y_coefficient: F::zero(),
            yx_coefficients: vec![],
            x_coefficients: vec![],
            zero_coefficient: c,
        }
    }

    /// Create a polynomial representing x
    pub fn x() -> Self {
        DivisorPoly {
            y_coefficient: F::zero(),
            yx_coefficients: vec![],
            x_coefficients: vec![F::ONE],
            zero_coefficient: F::zero(),
        }
    }

    /// Create a polynomial representing y
    pub fn y() -> Self {
        DivisorPoly {
            y_coefficient: F::ONE,
            yx_coefficients: vec![],
            x_coefficients: vec![],
            zero_coefficient: F::zero(),
        }
    }

    /// Normalize the x coefficient to 1.
    ///
    /// Panics if there is no x coefficient to normalize or if it cannot be normalized to 1.
    #[must_use]
    pub fn normalize_x_coefficient(self) -> Result<Self, Error> {
        let scalar = self.x_coefficients[0]
            .inverse()
            .ok_or_else(|| Error::InvertingZero)?;
        Ok(self * scalar)
    }
}

impl<F: PrimeField> Add<&Self> for DivisorPoly<F> {
    type Output = Self;

    fn add(mut self, other: &Self) -> Self {
        // Expand to the needed size
        while self.yx_coefficients.len() < other.yx_coefficients.len() {
            self.yx_coefficients.push(F::zero());
        }
        while self.x_coefficients.len() < other.x_coefficients.len() {
            self.x_coefficients.push(F::zero());
        }

        // Perform the addition
        self.y_coefficient += other.y_coefficient;
        for (i, coeff) in other.yx_coefficients.iter().enumerate() {
            self.yx_coefficients[i] += coeff;
        }
        for (i, coeff) in other.x_coefficients.iter().enumerate() {
            self.x_coefficients[i] += coeff;
        }
        self.zero_coefficient += other.zero_coefficient;

        self
    }
}

impl<F: PrimeField> Neg for DivisorPoly<F> {
    type Output = Self;

    fn neg(mut self) -> Self {
        self.y_coefficient = -self.y_coefficient;
        for yx_coeff in &mut self.yx_coefficients {
            *yx_coeff = -*yx_coeff;
        }
        for x_coeff in &mut self.x_coefficients {
            *x_coeff = -*x_coeff;
        }
        self.zero_coefficient = -self.zero_coefficient;

        self
    }
}

impl<F: PrimeField> Sub for DivisorPoly<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self + &-other
    }
}

impl<F: PrimeField> Mul<F> for DivisorPoly<F> {
    type Output = Self;

    fn mul(mut self, scalar: F) -> Self {
        self.y_coefficient *= scalar;
        for coeff in &mut self.yx_coefficients {
            *coeff *= scalar;
        }
        for x_coeff in &mut self.x_coefficients {
            *x_coeff *= scalar;
        }
        self.zero_coefficient *= scalar;

        self
    }
}

/*impl<F: PrimeField> Poly<F> {
    #[must_use]
    fn shift_by_x(mut self, power_of_x: usize) -> Self {
        if power_of_x == 0 {
            return self;
        }

        // Shift up every x coefficient
        for _ in 0..power_of_x {
            self.x_coefficients.insert(0, F::zero());
            for yx_coeffs in &mut self.yx_coefficients {
                yx_coeffs.insert(0, F::zero());
            }
        }

        // Move the zero coefficient
        self.x_coefficients[power_of_x - 1] = self.zero_coefficient;
        self.zero_coefficient = F::zero();

        // Move the y coefficients
        let mut yx_coefficients_to_push = vec![];
        while yx_coefficients_to_push.len() < power_of_x {
            yx_coefficients_to_push.push(F::zero());
        }
        while self.yx_coefficients.len() < self.y_coefficients.len() {
            self.yx_coefficients.push(yx_coefficients_to_push.clone());
        }
        for (i, y_coeff) in self.y_coefficients.drain(..).enumerate() {
            self.yx_coefficients[i][power_of_x - 1] = y_coeff;
        }

        self
    }

    #[must_use]
    fn shift_by_y(mut self, power_of_y: usize) -> Self {
        if power_of_y == 0 {
            return self;
        }

        // Shift up every y coefficient
        for _ in 0..power_of_y {
            self.y_coefficients.insert(0, F::zero());
            self.yx_coefficients.insert(0, vec![]);
        }

        // Move the zero coefficient
        self.y_coefficients[power_of_y - 1] = self.zero_coefficient;
        self.zero_coefficient = F::zero();

        // Move the x coefficients
        core::mem::swap(&mut self.yx_coefficients[power_of_y - 1], &mut self.x_coefficients);
        self.x_coefficients = vec![];

        self
    }
}

impl<F: PrimeField> Mul<&Poly<F>> for Poly<F> {
    type Output = Self;

    fn mul(self, other: &Self) -> Self {
        let mut res = self.clone() * other.zero_coefficient;

        for (i, y_coeff) in other.y_coefficients.iter().enumerate() {
            let scaled = self.clone() * *y_coeff;
            res = res + &scaled.shift_by_y(i + 1);
        }

        for (y_i, yx_coeffs) in other.yx_coefficients.iter().enumerate() {
            for (x_i, yx_coeff) in yx_coeffs.iter().enumerate() {
                let scaled = self.clone() * *yx_coeff;
                res = res + &scaled.shift_by_y(y_i + 1).shift_by_x(x_i + 1);
            }
        }

        for (i, x_coeff) in other.x_coefficients.iter().enumerate() {
            let scaled = self.clone() * *x_coeff;
            res = res + &scaled.shift_by_x(i + 1);
        }

        res
    }
}*/

impl<F: PrimeField> DivisorPoly<F> {
    /// Evaluate this polynomial with the specified `x`, `y` values.
    ///
    /// Panics on polynomials with terms whose powers exceed 2^64.
    #[cfg(test)]
    #[must_use]
    pub fn eval(&self, x: F, y: F) -> F {
        let mut res = self.zero_coefficient;
        res += y * self.y_coefficient;
        for (x_pow, coeff) in self
            .yx_coefficients
            .iter()
            .enumerate()
            .map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
        {
            res += y * x.pow([x_pow]) * coeff;
        }
        for (pow, coeff) in self
            .x_coefficients
            .iter()
            .enumerate()
            .map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
        {
            res += x.pow([pow]) * coeff;
        }
        res
    }

    /// Differentiate a polynomial, reduced by a modulus with a leading y term y^2 x^0, by x and y.
    /// This is partial differentiation
    /// This function has undefined behavior if unreduced.
    #[cfg(test)]
    #[must_use]
    pub fn differentiate(&self) -> (DivisorPoly<F>, DivisorPoly<F>) {
        // Differentiation by x practically involves:
        // - Dropping everything without an x component
        // - Shifting everything down a power of x
        // - Multiplying the new coefficient by the power it prior was used with
        let diff_x = {
            let mut diff_x = DivisorPoly {
                y_coefficient: F::zero(),
                yx_coefficients: vec![],
                x_coefficients: vec![],
                zero_coefficient: F::zero(),
            };
            if !self.x_coefficients.is_empty() {
                // Power rule of differentiation
                // Reduce the x power
                let mut x_coeffs = self.x_coefficients.clone();
                diff_x.zero_coefficient = x_coeffs.remove(0);
                diff_x.x_coefficients = x_coeffs;

                // Multiply the coefficient by its original power
                let mut prior_x_power = F::from(2u64);
                for x_coeff in &mut diff_x.x_coefficients {
                    *x_coeff *= prior_x_power;
                    prior_x_power += F::ONE;
                }
            }

            if !self.yx_coefficients.is_empty() {
                // Differentiate keeping y constant
                let mut yx_coeffs = self.yx_coefficients.clone();
                diff_x.y_coefficient = yx_coeffs.remove(0);
                diff_x.yx_coefficients = yx_coeffs;

                let mut prior_x_power = F::from(2u64);
                for yx_coeff in &mut diff_x.yx_coefficients {
                    *yx_coeff *= prior_x_power;
                    prior_x_power += F::ONE;
                }
            }

            diff_x
        };

        // Differentiation by y is trivial
        // It's the y coefficient as the zero coefficient, and the yx coefficients as the x
        // coefficients
        // This is thanks to any y term over y^2 being reduced out
        let diff_y = DivisorPoly {
            y_coefficient: F::zero(),
            yx_coefficients: vec![],
            x_coefficients: self.yx_coefficients.clone(),
            zero_coefficient: self.y_coefficient,
        };

        (diff_x, diff_y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand_core::OsRng;

    /*fn test_poly_generic<F: PrimeField + From<u64>>() {
        let zero = F::zero();
        let one = F::ONE;

        {
            // Test polynomial squaring: (y + y^2)^2 = y^2 + 2y^3 + y^4
            let mut poly = Poly::zero();
            poly.y_coefficients = vec![zero, one];

            let mut squared = Poly::zero();
            squared.y_coefficients = vec![zero, zero, zero, one];
            assert_eq!(poly.clone() * &poly, squared);
        }

        {
            let mut a = Poly::zero();
            a.zero_coefficient = F::from(2u64);

            let mut b = Poly::zero();
            b.zero_coefficient = F::from(3u64);

            let mut res = Poly::zero();
            res.zero_coefficient = F::from(6u64);
            assert_eq!(a.clone() * &b, res);

            b.y_coefficients = vec![F::from(4u64)];
            res.y_coefficients = vec![F::from(8u64)];
            assert_eq!(a.clone() * &b, res);
            assert_eq!(b.clone() * &a, res);

            a.x_coefficients = vec![F::from(5u64)];
            res.x_coefficients = vec![F::from(15u64)];
            res.yx_coefficients = vec![vec![F::from(20u64)]];
            assert_eq!(a.clone() * &b, res);
            assert_eq!(b.clone() * &a, res);

            // res is now 20xy + 8*y + 15*x + 6
            // res ** 2 =
            //   400*x^2*y^2 + 320*x*y^2 + 64*y^2 + 600*x^2*y + 480*x*y + 96*y + 225*x^2 + 180*x + 36

            let mut squared = Poly::zero();
            squared.y_coefficients = vec![F::from(96u64), F::from(64u64)];
            squared.yx_coefficients =
                vec![vec![F::from(480u64), F::from(600u64)], vec![F::from(320u64), F::from(400u64)]];
            squared.x_coefficients = vec![F::from(180u64), F::from(225u64)];
            squared.zero_coefficient = F::from(36u64);
            assert_eq!(res.clone() * &res, squared);
        }
    }*/

    /*#[test]
    fn test_poly() {
        test_poly_generic::<ark_pallas::Fq>();
        test_poly_generic::<ark_vesta::Fq>();
    }*/

    fn test_differentiation_generic<F: PrimeField + From<u64>>() {
        let random = || F::rand(&mut OsRng);

        {
            let input = DivisorPoly {
                y_coefficient: random(),
                yx_coefficients: vec![random()],
                x_coefficients: vec![random(), random(), random()],
                zero_coefficient: random(),
            };
            let (diff_x, diff_y) = input.differentiate();
            assert_eq!(
                diff_x,
                DivisorPoly {
                    y_coefficient: input.yx_coefficients[0],
                    yx_coefficients: vec![],
                    x_coefficients: vec![
                        F::from(2u64) * input.x_coefficients[1],
                        F::from(3u64) * input.x_coefficients[2]
                    ],
                    zero_coefficient: input.x_coefficients[0],
                }
            );
            assert_eq!(
                diff_y,
                DivisorPoly {
                    y_coefficient: F::zero(),
                    yx_coefficients: vec![],
                    x_coefficients: vec![input.yx_coefficients[0]],
                    zero_coefficient: input.y_coefficient,
                }
            );
        }

        {
            let input = DivisorPoly {
                y_coefficient: random(),
                yx_coefficients: vec![random(), random()],
                x_coefficients: vec![random(), random(), random(), random()],
                zero_coefficient: random(),
            };
            let (diff_x, diff_y) = input.differentiate();
            assert_eq!(
                diff_x,
                DivisorPoly {
                    y_coefficient: input.yx_coefficients[0],
                    yx_coefficients: vec![F::from(2u64) * input.yx_coefficients[1]],
                    x_coefficients: vec![
                        F::from(2u64) * input.x_coefficients[1],
                        F::from(3u64) * input.x_coefficients[2],
                        F::from(4u64) * input.x_coefficients[3],
                    ],
                    zero_coefficient: input.x_coefficients[0],
                }
            );
            assert_eq!(
                diff_y,
                DivisorPoly {
                    y_coefficient: F::zero(),
                    yx_coefficients: vec![],
                    x_coefficients: vec![input.yx_coefficients[0], input.yx_coefficients[1]],
                    zero_coefficient: input.y_coefficient,
                }
            );
        }
    }

    #[test]
    fn test_differentiation() {
        test_differentiation_generic::<ark_pallas::Fq>();
        test_differentiation_generic::<ark_vesta::Fq>();
    }
}
