//! Definition of linear combinations.

use ark_ff::Field;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::{Add, Mul, Neg, Sub};

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Variable<F: Field> {
    /// A Pedersen vector commitment
    VectorCommit(usize, usize),
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// Represents the constant 1.
    One(PhantomData<F>),
}

impl<F: Field> From<Variable<F>> for LinearCombination<F> {
    fn from(v: Variable<F>) -> LinearCombination<F> {
        LinearCombination {
            terms: vec![(v, F::one())],
        }
    }
}

// impl<F: Field, S: Into<F> + Marker> From<S> for LinearCombination<F> {
//     fn from(s: S) -> LinearCombination<F> {
//         LinearCombination {
//             terms: vec![(Variable::One(), s.into())],
//         }
//     }
// }

impl<F: Field> From<F> for LinearCombination<F> {
    fn from(c: F) -> LinearCombination<F> {
        LinearCombination {
            terms: vec![(Variable::One(PhantomData), c)],
        }
    }
}

pub fn constant<F: Field, I: Into<F>>(c: I) -> LinearCombination<F> {
    LinearCombination {
        terms: vec![(Variable::One(PhantomData), c.into())],
    }
}

// Arithmetic on variables produces linear combinations

impl<F: Field> Neg for Variable<F> {
    type Output = LinearCombination<F>;

    fn neg(self) -> Self::Output {
        -LinearCombination::from(self)
    }
}

impl<F: Field, L: Into<LinearCombination<F>>> Add<L> for Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: L) -> Self::Output {
        LinearCombination::from(self) + other.into()
    }
}

impl<F: Field, L: Into<LinearCombination<F>>> Sub<L> for Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: L) -> Self::Output {
        LinearCombination::from(self) - other.into()
    }
}

impl<F: Field, S: Into<F>> Mul<S> for Variable<F> {
    type Output = LinearCombination<F>;

    fn mul(self, other: S) -> Self::Output {
        LinearCombination {
            terms: vec![(self, other.into())],
        }
    }
}

// Arithmetic on scalars with variables produces linear combinations

// pub trait Marker {}
// impl<F: Field> Marker for F {}

// impl<F: Field + Marker> Add<Variable<F>> for F {
//     type Output = LinearCombination<F>;

//     fn add(self, other: Variable<F>) -> Self::Output {
//         LinearCombination {
//             terms: vec![(Variable::One(), self), (other, F::one())],
//         }
//     }
// }

// impl Sub<Variable> for Field {
//     type Output = LinearCombination<Field>;

//     fn sub(self, other: Variable) -> Self::Output {
//         LinearCombination {
//             terms: vec![(Variable::One(), self), (other, -F::one())],
//         }
//     }
// }

// impl Mul<Variable> for Field {
//     type Output = LinearCombination<Field>;

//     fn mul(self, other: Variable) -> Self::Output {
//         LinearCombination {
//             terms: vec![(other, self)],
//         }
//     }
// }

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug, PartialEq)]
pub struct LinearCombination<F: Field> {
    pub(super) terms: Vec<(Variable<F>, F)>,
}

impl<F: Field> Default for LinearCombination<F> {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl<F: Field> FromIterator<(Variable<F>, F)> for LinearCombination<F> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Variable<F>, F)>,
    {
        LinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}

impl<'a, F: Field> FromIterator<&'a (Variable<F>, F)> for LinearCombination<F> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (Variable<F>, F)>,
    {
        LinearCombination {
            terms: iter.into_iter().copied().collect(),
        }
    }
}

// Arithmetic on linear combinations

impl<F: Field, L: Into<LinearCombination<F>>> Add<L> for LinearCombination<F> {
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self.terms.extend(rhs.into().terms.iter().copied());
        LinearCombination { terms: self.terms }
    }
}

impl<F: Field, L: Into<LinearCombination<F>>> Sub<L> for LinearCombination<F> {
    type Output = Self;

    fn sub(mut self, rhs: L) -> Self::Output {
        self.terms.extend(
            rhs.into()
                .terms
                .iter()
                .map(|(var, coeff)| (*var, -(*coeff))),
        );
        LinearCombination { terms: self.terms }
    }
}

// impl<F: Field> Mul<LinearCombination<F>> for F {
//     type Output = LinearCombination<F>;

//     fn mul(self, other: LinearCombination<F>) -> Self::Output {
//         let out_terms = other
//             .terms
//             .into_iter()
//             .map(|(var, scalar)| (var, scalar * self))
//             .collect();
//         LinearCombination { terms: out_terms }
//     }
// }

impl<F: Field> LinearCombination<F> {
    pub fn scalar_mul(self, scalar: F) -> LinearCombination<F> {
        let out_terms = self
            .terms
            .into_iter()
            .map(|(var, entry)| (var, entry * scalar))
            .collect();
        LinearCombination { terms: out_terms }
    }
}

impl<F: Field> Neg for LinearCombination<F> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = -*s
        }
        self
    }
}

impl<F: Field, S: Into<F>> Mul<S> for LinearCombination<F> {
    type Output = Self;

    fn mul(mut self, other: S) -> Self::Output {
        let other = other.into();
        for (_, s) in self.terms.iter_mut() {
            *s *= other
        }
        self
    }
}
