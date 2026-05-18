use ark_ff::{PrimeField, batch_inversion};
use ark_std::{vec, vec::Vec};
use core::ops::Div;
use subtle::{Choice, ConditionallySelectable, CtOption};

use crate::DivisorPoly;
use crate::barycentric::Interpolator;
use crate::error::Error;

/// Evaluations of a polynomial at consecutive points.
///
/// This represents a polynomial by storing its evaluations at points 0, 1, 2, ..., n-1
/// rather than storing coefficients. This enables efficient pointwise operations.
#[derive(Debug, Clone)]
pub(super) struct Evals<F: PrimeField> {
    evals: Vec<F>,
    degree: u16,
}

impl<F: PrimeField> Evals<F> {
    fn new(evals: Vec<F>, degree: u16) -> Self {
        Self { evals, degree }
    }

    /// Compute evaluations of the curve modulus polynomial `x^3 + ax + b`.
    ///
    /// This computes the evaluations of the curve equation at `x = 0, 1, 2, ..., n-1`.
    pub(super) fn compute_modulus(a: F, b: F, amount_of_evals: u16) -> Evals<F> {
        let mut evals = Vec::with_capacity(amount_of_evals as usize);
        for i in 0..amount_of_evals {
            let x = F::from(u64::from(i));
            let x_cube = x.square() * x;
            let ax = x * a;
            evals.push(x_cube + ax + b);
        }
        Self::new(evals, 3)
    }

    fn len(&self) -> usize {
        self.evals.len()
    }

    fn from_degree_1(coeff: F, constant: F, amount_of_evals: u16) -> Self {
        let mut evals = Vec::with_capacity(amount_of_evals as usize);
        if amount_of_evals == 0 {
            return Evals { evals, degree: 1 };
        }
        let mut last_eval = constant;
        for _ in 0..amount_of_evals {
            evals.push(last_eval);
            last_eval += coeff;
        }
        Self { evals, degree: 1 }
    }

    fn from_degree_0(constant: F, evals: u16) -> Self {
        let evals = vec![constant; evals as usize];
        Evals { evals, degree: 0 }
    }
}

/// A small divisor representing a line through two points.
///
/// This represents a divisor of the form `y - slope * x - intercept`,
/// which corresponds to a line through two points on the curve.
#[derive(Debug, Clone, Copy)]
pub(super) struct SmallDivisor<F: PrimeField> {
    x_coefficient: F,
    zero_coefficient: F,
    y_coefficient: F,
}

impl<F: PrimeField> SmallDivisor<F> {
    pub(super) fn new(x_coefficient: F, zero_coefficient: F, y_coefficient: F) -> Self {
        Self {
            x_coefficient,
            zero_coefficient,
            y_coefficient,
        }
    }
}

/// A divisor function `f(x, y) = A(x) - yB(x)`.
///
/// `A` and `B` are represented as a sufficient amount of evaluations from them to perform
/// interpolation and recover them.
#[derive(Debug, Clone)]
pub(super) struct DivisorEvals<F: PrimeField> {
    a: Evals<F>,
    b: Evals<F>,
}

impl<F: PrimeField> Div<Evals<F>> for DivisorEvals<F> {
    type Output = Self;

    fn div(mut self, mut rhs: Evals<F>) -> Self::Output {
        debug_assert_eq!(self.a.len(), self.b.len());
        debug_assert_eq!(self.a.len(), rhs.len());

        batch_inversion(&mut rhs.evals);
        for ((a, b), denom) in self
            .a
            .evals
            .iter_mut()
            .zip(self.b.evals.iter_mut())
            .zip(rhs.evals)
        {
            *a *= denom;
            *b *= denom;
        }
        self.a.degree -= rhs.degree;
        self.b.degree -= rhs.degree;
        self
    }
}

impl<F: PrimeField> DivisorEvals<F> {
    pub(super) fn from_small(small: SmallDivisor<F>, modulus: &Evals<F>) -> Self {
        let SmallDivisor {
            x_coefficient,
            zero_coefficient,
            y_coefficient,
        } = small;
        let evals = modulus.len() as u16;
        let a = Evals::from_degree_1(x_coefficient, zero_coefficient, evals);
        let b = Evals::from_degree_0(y_coefficient, evals);
        Self { a, b }
    }

    fn ab(&self, i: usize) -> (F, F) {
        let a = self.a.evals[i];
        let b = self.b.evals[i];
        (a, b)
    }

    fn ab_mut(&mut self, i: usize) -> (&mut F, &mut F) {
        let a = &mut self.a.evals[i];
        let b = &mut self.b.evals[i];
        (a, b)
    }

    /// The degrees of the A/B polynomials after the multiplication of these divisors.
    fn degree_after_multiplication(&self, other_a_degree: u16, other_b_degree: u16) -> (u16, u16) {
        // f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2
        // A = A1A2 + (x^3 + ax + b) B1B2
        // B = A1B2 + A2B1
        // deg(A) = max(A1 + A2, 3 + B1 + B2)
        // deg(B) = max(A1 + B2, A2 + B1)
        let (a1, b1) = (self.a.degree, self.b.degree);
        let (a2, b2) = (other_a_degree, other_b_degree);
        let a = (a1 + a2).max(3 + b1 + b2);
        let b = (a1 + b2).max(a2 + b1);
        (a, b)
    }

    /// Multiply two divisors modulo the curve equation.
    ///
    /// Computes `f1 * f2` where multiplication is done modulo `y^2 = x^3 + ax + b`.
    ///
    /// The formula used is:
    /// - `f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2`
    /// - `A = A1A2 + (x^3 + ax + b) B1B2`
    /// - `B = A1B2 + A2B1`
    ///
    /// This is computed efficiently in the evaluation domain using pointwise operations.
    fn mul_mod(mut self, rhs: &Self, modulus: &Evals<F>) -> Self {
        debug_assert_eq!(self.a.len(), rhs.a.len());
        debug_assert_eq!(self.b.len(), rhs.b.len());
        debug_assert_eq!(self.a.len(), self.b.len());

        let len = self.a.len();

        let degree_after_multiplication =
            self.degree_after_multiplication(rhs.a.degree, rhs.b.degree);
        // f1 * f2 = A1A2 - y(A1B2 + A2B1) + y^2 B1B2
        // f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2
        // (A1+B1)(A2+B2)
        // A1A2 + A1B2 + B1A2 + B1B2
        for i in 0..len {
            let modulus = modulus.evals[i];
            let (a1, b1) = self.ab_mut(i);
            let (a2, b2) = rhs.ab(i);
            let a1a2 = *a1 * a2;
            let b1b2 = *b1 * b2;
            // (A1+B1)(A2+B2)
            let cross = (*a1 + *b1) * (a2 + b2);
            let b = cross - (a1a2 + b1b2);
            let a = a1a2 + (b1b2 * modulus);
            *a1 = a;
            *b1 = b;
        }
        self.a.degree = degree_after_multiplication.0;
        self.b.degree = degree_after_multiplication.1;
        self
    }

    fn mul_mod_small(mut self, rhs: SmallDivisor<F>, modulus: &Evals<F>) -> Self {
        debug_assert_eq!(self.a.len(), self.b.len());

        let len = self.a.len();

        let degree_after_multiplication = self.degree_after_multiplication(1, 0);
        // constant term for x = 0
        let mut a2 = rhs.zero_coefficient;
        let b2 = rhs.y_coefficient;
        for i in 0..len {
            let modulus = modulus.evals[i];
            let (a1, b1) = self.ab_mut(i);
            let a1a2 = *a1 * a2;
            let b1b2 = *b1 * b2;
            // (A1+B1)(A2+B2)
            let cross = (*a1 + *b1) * (a2 + b2);
            let b = cross - (a1a2 + b1b2);
            let a = a1a2 + b1b2 * modulus;
            a2 += rhs.x_coefficient;
            *a1 = a;
            *b1 = b;
        }
        self.a.degree = degree_after_multiplication.0;
        self.b.degree = degree_after_multiplication.1;
        self
    }

    /// Remove 2 points by dividing by `(x - x1) * (x - x2)`.
    ///
    /// This divides the divisor by the product `(x - x1)(x - x2)`, effectively
    /// removing zeros at x-coordinates x1 and x2. This is used when merging divisors
    /// to remove unwanted zeros at intermediate sum points.
    fn remove_diff(self, x1: CtOption<F>, x2: CtOption<F>) -> Self {
        debug_assert_eq!(self.a.len(), self.b.len());

        let mut denominator = Vec::with_capacity(self.a.len());
        let (mut x_l, mut x_r) = (F::zero(), F::zero());
        let inc_l = F::from(u64::from(x1.is_some().unwrap_u8()));
        let inc_r = F::from(u64::from(x2.is_some().unwrap_u8()));
        let neg1 = -F::ONE;

        // F does not implement ConditionallySelectable
        // let (x1, x2) = (x1.unwrap_or(neg1), x2.unwrap_or(neg1));
        let x1 = if x1.is_some().into() {
            x1.unwrap()
        } else {
            neg1
        };
        let x2 = if x2.is_some().into() {
            x2.unwrap()
        } else {
            neg1
        };

        for _ in 0..self.a.len() {
            denominator.push((x_l - x1) * (x_r - x2));
            x_l += inc_l;
            x_r += inc_r;
        }
        let denominator = Evals {
            evals: denominator,
            degree: 2,
        };
        self / denominator
    }

    /// Convert divisor from univariate to bivariate representation.
    pub fn to_poly(&self, interpolator: &Interpolator<F>) -> Result<DivisorPoly<F>, Error> {
        let [a, b] = self.interpolate(interpolator)?;
        let zero_coefficient = a[0];
        let x_coefficients = a[1..].to_vec();
        let yx_coefficients = b[1..].to_vec();
        let y_coefficient = b[0];
        Ok(DivisorPoly {
            zero_coefficient,
            x_coefficients,
            yx_coefficients,
            y_coefficient,
        })
    }

    pub(super) fn merge(
        divisors: [Self; 2],
        small: SmallDivisor<F>,
        denom: (CtOption<F>, CtOption<F>),
        modulus: &Evals<F>,
    ) -> Self {
        let [d0, d1] = divisors;
        let numerator = d0.mul_mod(&d1, modulus).mul_mod_small(small, modulus);
        let (x1, x2) = denom;
        numerator.remove_diff(x1, x2)
    }

    pub(super) fn interpolate(&self, interpolator: &Interpolator<F>) -> Result<[Vec<F>; 2], Error> {
        let max_degree = self.a.degree.max(self.b.degree);
        if max_degree > interpolator.degree() {
            return Err(Error::DegreeExceedsInterpolator(
                max_degree,
                interpolator.degree(),
            ));
        }
        let a = interpolator.interpolate(&self.a.evals)?;
        let b = interpolator.interpolate(&self.b.evals)?;
        Ok([a, b])
    }
}

impl<F> ConditionallySelectable for SmallDivisor<F>
where
    // F: PrimeField + ConditionallySelectable,
    F: PrimeField,
{
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        // F does not implement ConditionallySelectable
        // let x_coefficient = <_>::conditional_select(&a.x_coefficient, &b.x_coefficient, choice);
        // let zero_coefficient =
        //     <_>::conditional_select(&a.zero_coefficient, &b.zero_coefficient, choice);
        // let y_coefficient = <_>::conditional_select(&a.y_coefficient, &b.y_coefficient, choice);
        let c = bool::from(choice);
        let x_coefficient = if !c { a.x_coefficient } else { b.x_coefficient };
        let zero_coefficient = if !c {
            a.zero_coefficient
        } else {
            b.zero_coefficient
        };
        let y_coefficient = if !c { a.y_coefficient } else { b.y_coefficient };
        SmallDivisor {
            x_coefficient,
            zero_coefficient,
            y_coefficient,
        }
    }
}
