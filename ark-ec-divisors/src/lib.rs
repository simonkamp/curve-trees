#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

// This code is ported from [Monero's codebase](https://github.com/monero-oxide/monero-oxide/tree/fcmp%2B%2B/crypto/divisors)
// Read the audit. Consider SlverBullet paper

use ark_ec::short_weierstrass::Projective;
use ark_ec::{AdditiveGroup, CurveConfig, CurveGroup};
use ark_ff::{PrimeField, Zero, batch_inversion};
use ark_std::{vec, vec::Vec};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

mod barycentric;
pub use barycentric::Interpolator;

mod divisor;
use divisor::{DivisorEvals, SmallDivisor};

mod poly;
pub use poly::DivisorPoly;
pub mod curves;
pub mod scalar_decomposition;
pub mod util;

pub mod error;
use error::Error;

use crate::divisor::Evals;
pub use curves::DivisorCurve;
pub use scalar_decomposition::ScalarDecomposition;

type Xy<C> = (<C as CurveConfig>::BaseField, <C as CurveConfig>::BaseField);
type Denom<F> = (CtOption<F>, CtOption<F>);

struct LineArgs<C: DivisorCurve> {
    /// The `b` to use when calculating the line.
    ///
    /// This will be distinct if the points would otherwise share an `x` coordinate.
    b: Projective<C>,
    /// If both points were the identity point.
    both_are_identity: Choice,
    /// If one point was the identity, or the points were additive inverses, and the single `x`
    /// coordinate between the two if so.
    one_is_identity_or_additive_inverses: (Choice, C::BaseField),
}

/// Batch-convert projective points to affine (x, y) pairs.
fn batch_to_xy<C: DivisorCurve>(pts: &[Projective<C>]) -> Vec<(C::BaseField, C::BaseField)> {
    Projective::<C>::normalize_batch(pts)
        .into_iter()
        .map(|a| (a.x, a.y))
        .collect()
}

/// Prepare points to calculate their lines.
fn line_args<C: DivisorCurve>(
    a: Projective<C>,
    b: Projective<C>,
    a_x: C::BaseField,
    b_x: C::BaseField,
    g: &Projective<C>,
) -> LineArgs<C> {
    let a_is_identity = a.is_zero();
    let b_is_identity = b.is_zero();

    // TODO: Projective<C> does not implement subtle::ConditionallySelectable or ConstantTimeEq;
    // ideally these would be Choice values and we'd use conditional_select throughout.
    let both_are_identity = Choice::from(u8::from(a_is_identity && b_is_identity));

    let one_is_identity = a_is_identity || b_is_identity;
    let additive_inverses = a == -b;
    let one_is_identity_or_additive_inverses =
        Choice::from(u8::from(one_is_identity || additive_inverses));
    // F does not implement ConditionallySelectable
    // let one_is_identity_or_additive_inverses = (
    //     one_is_identity_or_additive_inverses,
    //     <_>::conditional_select(&a_x, &b_x, Choice::from(u8::from(a_is_identity))),
    // );
    let x_coordinate = if a_is_identity { b_x } else { a_x };
    let one_is_identity_or_additive_inverses = (one_is_identity_or_additive_inverses, x_coordinate);

    // TODO: ideally these would use conditional_select once Projective<C>: ConditionallySelectable
    let a = if a_is_identity { *g } else { a };
    let b = if b_is_identity { *g } else { b };
    let b = if additive_inverses { a.double() } else { b };
    let b = if a == b { -a.double() } else { b };

    LineArgs {
        b,
        both_are_identity,
        one_is_identity_or_additive_inverses,
    }
}

/// Computes all (slope, intercept) pairs between points `a[i]` and `b[i]`.
fn slopes_and_intercepts<C: DivisorCurve>(
    a: Vec<Xy<C>>,
    b: &[Projective<C>],
) -> Result<Vec<(C::BaseField, C::BaseField)>, Error> {
    debug_assert_eq!(a.len(), b.len());
    let b: Vec<Xy<C>> = batch_to_xy::<C>(b);
    // Compute \prod{1/(b_i.x - a_i.x)}
    let mut inv_diffs = a
        .iter()
        .zip(b.iter())
        .map(|(a, b)| {
            let (ax, bx) = (a.0, b.0);
            bx - ax
        })
        .collect::<Vec<C::BaseField>>();
    if inv_diffs.iter().any(|d| d.is_zero()) {
        return Err(Error::InvertingZero);
    }
    batch_inversion(&mut inv_diffs);

    Ok(a.into_iter()
        .zip(b)
        .zip(inv_diffs)
        .map(|((a, b), inv_diff)| {
            let (ax, ay) = a;
            let (bx, by) = b;

            let slope = (by - ay) * inv_diff;
            let intercept = by - (slope * bx);
            debug_assert!((ay - (slope * ax) - intercept).is_zero());
            debug_assert!((by - (slope * bx) - intercept).is_zero());
            (slope, intercept)
        })
        .collect())
}

/// Complete calculation of a line from its arguments and the (potentially stubbed)
/// slope/intercept.
///
/// Constructs a `SmallDivisor` representing the line `y - slope * x - intercept`,
/// handling special cases where points are at infinity or are additive inverses.
fn finish_line<F: PrimeField>(
    slope: F,
    intercept: F,
    both_are_identity: Choice,
    one_is_identity_or_additive_inverses: (Choice, F),
) -> SmallDivisor<F> {
    // y - slope x - intercept
    let mut res = SmallDivisor::new(-slope, -intercept, F::ONE);
    // `x - x`, where the first `x` is the coefficient and the second `x` is a constant of the `x`
    // coordinate present within this pair of points
    let (one_is_identity_or_additive_inverses, constant_term) =
        one_is_identity_or_additive_inverses;
    res = <_>::conditional_select(
        &res,
        &SmallDivisor::new(F::ONE, -constant_term, F::ZERO),
        one_is_identity_or_additive_inverses,
    );
    // 1
    <_>::conditional_select(
        &res,
        &SmallDivisor::new(F::ZERO, F::ONE, F::ZERO),
        both_are_identity,
    )
}

/// Computes all lines required to construct a divisor, batching expensive operations.
fn lines_and_denoms<C: DivisorCurve>(
    points: &[Projective<C>],
) -> Result<Vec<(SmallDivisor<C::BaseField>, Denom<C::BaseField>)>, Error> {
    // All the pairs of points from which lines will be created.
    // Builds a binary tree where `pairs` will contain leaves, followed by nodes above that leaf level,
    // followed by nodes of next upper level and so on. If number of nodes at any level is odd, the last node
    // is processed at next (upper) level
    // Each leaf is a pair of points and each parent is the sum of its 2 children.
    let pairs = {
        let mut pairs = Vec::<[Projective<C>; 2]>::with_capacity(points.len());
        let mut divs = Vec::<Projective<C>>::with_capacity(points.len().div_ceil(2));

        // Take 2 consecutive points from `points` and them to `pairs`. If length of `points` is odd, its last point is paired with point at infinity.
        // `divs` will contain the sums of each pair from `pairs`
        let mut iter = points.iter().copied();
        while let Some(a) = iter.next() {
            let b = iter.next();
            pairs.push([a, b.unwrap_or_else(Projective::<C>::zero)]);
            let div = match b {
                Some(b) => a + b,
                None => a,
            };
            divs.push(div);
        }

        while divs.len() > 1 {
            let mut next_divs = Vec::with_capacity((divs.len() / 2) + 1);
            // If there's an odd number of divisors, carry the odd one out to the next iteration
            if (divs.len() % 2) == 1 {
                next_divs.push(divs.pop().unwrap());
            }

            while let Some(a) = divs.pop() {
                let b = divs.pop().unwrap();
                pairs.push([a, b]);
                next_divs.push(a + b);
            }
            divs = next_divs;
        }
        pairs
    };

    // Get (x, y) coordinates of each point in the `pairs` list.
    let g: Projective<C> = C::GENERATOR.into();
    let (a_xy, b_xy) = {
        let mut pts = pairs
            .iter()
            .map(|[a, _]| {
                let is_identity = a.is_zero();
                // TODO: Projective<C> does not implement ConditionallySelectable
                // <_>::conditional_select(a, &g, Choice::from(u8::from(is_identity)))
                if is_identity { g } else { *a }
            })
            .collect::<Vec<_>>();
        let a_len = pts.len();
        pts.extend(pairs.iter().map(|[_, b]| {
            let is_identity = b.is_zero();
            // TODO: Projective<C> does not implement ConditionallySelectable
            // <_>::conditional_select(b, &g, Choice::from(u8::from(is_identity)))
            if is_identity { g } else { *b }
        }));
        let mut xy = batch_to_xy::<C>(&pts);
        let b_xy = xy.split_off(a_len);
        let a_xy = xy;
        (a_xy, b_xy)
    };

    let (line_args_and_denom, b_pts): (Vec<_>, Vec<_>) = pairs
        .into_iter()
        .zip(a_xy.iter().zip(b_xy))
        .map(|(pair, (a_xy, b_xy))| {
            let (a_x, _) = a_xy;
            let ax = CtOption::new(*a_x, !Choice::from(u8::from(pair[0].is_zero())));
            let (b_x, _) = b_xy;
            let bx = CtOption::new(b_x, !Choice::from(u8::from(pair[1].is_zero())));
            let denom = (ax, bx);
            let [a, b] = pair;
            let args = line_args::<C>(a, b, *a_x, b_x, &g);
            let LineArgs {
                b,
                both_are_identity,
                one_is_identity_or_additive_inverses,
            } = args;
            (
                (
                    (both_are_identity, one_is_identity_or_additive_inverses),
                    denom,
                ),
                b,
            )
        })
        .unzip();

    let slopes_and_intercepts = slopes_and_intercepts::<C>(a_xy, &b_pts)?;

    Ok(line_args_and_denom
        .into_iter()
        .zip(slopes_and_intercepts)
        .map(
            |(
                ((both_are_identity, one_is_identity_or_additive_inverses), denom),
                (slope, intercept),
            )| {
                let line = finish_line(
                    slope,
                    intercept,
                    both_are_identity,
                    one_is_identity_or_additive_inverses,
                );
                (line, denom)
            },
        )
        .collect())
}

/// Create a divisor interpolating the following points.
///
/// Returns an error if:
///   - No points were passed in
///   - The points don't sum to the point at infinity
///   - A passed in point was the point at infinity
///   - If too small of an interpolator was passed in
///
/// Output: DivisorPoly representing `D(x,y) = a(x) - b(x)*y` such that:
///   - `D(P_i) = 0` for each input point `P_i`
///   - D has poles only at the point at infinity
///   - Coefficient of `x^1` is normalized to 1
///
/// If the arguments were valid, this function executes in an amount of time constant to the amount
/// of points.
#[allow(clippy::new_ret_no_self)]
pub fn new_divisor<C: DivisorCurve>(
    points: &[Projective<C>],
    interpolator: &Interpolator<C::BaseField>,
) -> Result<DivisorPoly<C::BaseField>, Error> {
    // No points were passed in, this is the point at infinity, or the single point isn't infinity
    // and accordingly doesn't sum to infinity. All three cause us to return None
    // Checks a bit other than the first bit is set, meaning this is >= 2
    let mut invalid_args = (points.len() & (!1usize)).ct_eq(&0);

    // The points don't sum to the point at infinity
    let sum = points
        .iter()
        .copied()
        .reduce(|a, b| a + b)
        .unwrap_or_else(Projective::<C>::zero);
    // TODO: Projective<C> does not implement ConstantTimeEq; ideally this would be CT
    invalid_args |= Choice::from(u8::from(!sum.is_zero()));
    // A point was the point at identity
    for point in points {
        // TODO: Projective<C> does not implement ConstantTimeEq; ideally this would be CT
        invalid_args |= Choice::from(u8::from(point.is_zero()));
    }
    if invalid_args.into() {
        return Err(Error::InvalidArguments);
    }

    let points_len = points.len();

    let modulus =
        Evals::compute_modulus(C::COEFF_A, C::COEFF_B, interpolator.required_evaluations());
    // Create the initial set of divisors
    let mut divs = vec![];
    let mut all_lines = lines_and_denoms::<C>(points)?.into_iter();
    for _ in 0..((points_len / 2) + (points_len % 2)) {
        let (line, _) = all_lines.next().unwrap();
        divs.push(DivisorEvals::<C::BaseField>::from_small(line, &modulus));
    }

    // Our Poly algorithm is leaky and will create an excessive number of y x**j and x**j
    // coefficients which are zero, yet as our implementation is constant time, still come with
    // an immense performance cost. This code truncates the coefficients we know are zero.
    let trim = |divisor: &mut DivisorPoly<_>, points_len: usize| {
        // We should only be trimming divisors reduced by the modulus
        {
            let truncate_to = points_len.div_ceil(2).saturating_sub(2);
            for p in truncate_to..divisor.yx_coefficients.len() {
                let c: <C as CurveConfig>::BaseField = divisor.yx_coefficients[p];
                debug_assert!(c.is_zero());
            }
            divisor.yx_coefficients.truncate(truncate_to);
        }
        {
            let truncate_to = points_len / 2;
            for p in truncate_to..divisor.x_coefficients.len() {
                debug_assert!(divisor.x_coefficients[p].is_zero());
            }
            divisor.x_coefficients.truncate(truncate_to);
        }
    };

    // Pair them off until only one remains
    while divs.len() > 1 {
        let mut next_divs = vec![];
        // If there's an odd number of divisors, carry the odd one out to the next iteration
        if (divs.len() % 2) == 1 {
            next_divs.push(divs.pop().unwrap());
        }

        while let Some(a_div) = divs.pop() {
            let b_div = divs.pop().unwrap();

            // Merge the two divisors
            let (line, denom) = all_lines.next().unwrap();
            let merged = DivisorEvals::merge([a_div, b_div], line, denom, &modulus);
            next_divs.push(merged);
        }

        divs = next_divs;
    }

    // Return the unified divisor
    let divisor = divs.remove(0);
    let mut divisor = divisor.to_poly(interpolator)?;
    trim(&mut divisor, points_len);
    Ok(divisor)
}
