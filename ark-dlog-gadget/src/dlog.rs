use crate::error::Error;
use crate::utils::{
    CurveSpec, OnCurve, ScalarMulAndDivisor, incomplete_add_pub, inverse, on_curve,
};
use ark_ec::AffineRepr;
use ark_ec_divisors::util::{DiscreteLogParameter, GeneratorMultiplesSource, GeneratorTable};
use ark_ec_divisors::{DivisorCurve, DivisorPoly, ScalarDecomposition};
use ark_ff::{BigInteger, PrimeField, batch_inversion};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{boxed::Box, fmt::Debug, vec, vec::Vec};
use bulletproofs::BulletproofGens;
use bulletproofs::r1cs::{
    ConstraintSystem, LinearCombination, Prover, Variable, Verifier, constant,
};
use core::marker::PhantomData;
use core::ops::{Add, Div, Sub};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
pub use generic_array::typenum::{Diff, Quot, Sum, U1, U2, Unsigned};
use generic_array::typenum::{U255, U256};
pub use generic_array::{ArrayLength, GenericArray};
use rand_core::CryptoRngCore;

pub const DECOMPOSITION_SIZE: usize = 256;
pub const MAX_BITS_SUPPORTED: usize = 255;

/// Derived parameters for a discrete logarithm proof.
///
/// This should not be directly implemented. `DiscreteLogParameter` should be implemented for which
/// this will then be automatically derived.
pub trait DiscreteLogParameters: DiscreteLogParameter {
    /// The number of `x**i` coefficients in a divisor.
    ///
    /// This is the number of points in a divisor (the number of bits in a scalar, plus one) divided
    /// by two.
    type XCoefficients: ArrayLength;

    /// The number of `x**i` coefficients in a divisor, minus one.
    type XCoefficientsMinusOne: ArrayLength;

    /// The number of `y x**i` coefficients in a divisor.
    ///
    /// This is the number of points in a divisor (the number of bits in a scalar, plus one),
    /// ceiling division by two, minus two.
    type YxCoefficients: ArrayLength;
}

/// XCoefficients = (ScalarBits + 1) / 2
type XCoefficients<ScalarBits> = <<ScalarBits as Add<U1>>::Output as Div<U2>>::Output;

impl<P: DiscreteLogParameter> DiscreteLogParameters for P
where
  // XCoefficients
  P::ScalarBits: Add<U1>,
  <P::ScalarBits as Add<U1>>::Output: Add<U1> + Div<U2>,
  <<P::ScalarBits as Add<U1>>::Output as Div<U2>>::Output: ArrayLength + Sub<U1>,
  // XCoefficientsMinusOne
  XCoefficients<Self::ScalarBits>: Sub<U1>,
  <XCoefficients<Self::ScalarBits> as Sub<U1>>::Output: ArrayLength,
  // YxCoefficients
  <<P::ScalarBits as Add<U1>>::Output as Add<U1>>::Output: Div<U2>,
  <<<P::ScalarBits as Add<U1>>::Output as Add<U1>>::Output as Div<U2>>::Output: Sub<U2>,
  <<<<P::ScalarBits as Add<U1>>::Output as Add<U1>>::Output as Div<U2>>::Output as Sub<U2>>::Output:
    ArrayLength,
{
  type XCoefficients = XCoefficients<Self::ScalarBits>;
  // XCoefficients - 1
  type XCoefficientsMinusOne = Diff<XCoefficients<Self::ScalarBits>, U1>;
  // (ScalarBits + 1 + 1)/2 - 2 = (ScalarBits + 2)/2 - 2
  type YxCoefficients = Diff<Quot<Sum<Sum<Self::ScalarBits, U1>, U1>, U2>, U2>;
}

/// A representation of the divisor.
///
/// The coefficient for x**1 is explicitly excluded as it's expected to be normalized to 1.
#[derive(Clone)]
pub struct Divisor<F: PrimeField, Parameters: DiscreteLogParameters> {
    /// The coefficient for the `y` term of the divisor.
    ///
    /// There is never more than one `y**i x**0` coefficient as the leading term of the modulus is
    /// `y**2`. It's assumed the coefficient is non-zero (and present) as it will be for any divisor
    /// exceeding trivial complexity.
    pub y: Variable<F>,
    /// The coefficients for the `y**1 x**i` terms of the polynomial.
    pub yx: GenericArray<Variable<F>, Parameters::YxCoefficients>,
    /// The coefficients for the `x**i` terms of the polynomial, skipping x**1.
    ///
    /// x**1 is skipped as it's expected to be normalized to 1, and therefore constant, in order to
    /// ensure the divisor is non-zero (as necessary for the proof to be complete).
    // Subtract 1 from the length due to skipping the coefficient for x**1
    pub x_from_power_of_2: GenericArray<Variable<F>, Parameters::XCoefficientsMinusOne>,
    /// The constant term in the polynomial (alternatively, the coefficient for y**0 x**0).
    pub zero: Variable<F>,
}

/// A point, its discrete logarithm, and the divisor to prove it.
#[derive(Clone)]
pub struct PointWithDlog<F: PrimeField, Parameters: DiscreteLogParameters> {
    /// The point which is supposedly the result of scaling the generator by the discrete logarithm.
    pub point: (Variable<F>, Variable<F>),
    /// The discrete logarithm, represented as coefficients of a polynomial of 2**i.
    pub dlog: GenericArray<Variable<F>, Parameters::ScalarBits>,
    /// The divisor interpolating the relevant doublings of generator with the inverse of the point.
    pub divisor: Divisor<F, Parameters>,
}

/// Many points, with same discrete logarithm, and the divisors to prove it.
/// Similar to [`PointWithDlog`] but for multiple points.
#[derive(Clone)]
pub struct PointsWithDlog<F: PrimeField, Parameters: DiscreteLogParameters> {
    /// The points which are supposedly the result of scaling the generators by the discrete logarithm.
    pub points: Vec<(Variable<F>, Variable<F>)>,
    /// The discrete logarithm, represented as coefficients of a polynomial of 2**i.
    pub dlog: GenericArray<Variable<F>, Parameters::ScalarBits>,
    /// The divisors interpolating the relevant doublings of generators with the inverse of the corresponding points.
    pub divisors: Vec<Divisor<F, Parameters>>,
}

/// Commitments for the dlog and divisor witnesses combined.
#[derive(Debug, Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct DivisorComms<C: AffineRepr>(pub Vec<C>);

/// Blindings for the combined dlog and divisor witnesses commitments.
pub struct DivisorCommsBlindings<F: PrimeField>(pub Vec<F>);

/// A struct containing a point used for the evaluation of a divisor.
///
/// Preprocesses and caches as much of the calculation as possible to minimize work upon reuse of
/// challenge points.
#[derive(Debug)]
struct ChallengePoint<F: PrimeField, Parameters: DiscreteLogParameters> {
    y: F,
    yx: GenericArray<F, Parameters::YxCoefficients>,
    x: GenericArray<F, Parameters::XCoefficients>,
    p_0_n_0: F,
    x_p_0_n_0: GenericArray<F, Parameters::YxCoefficients>,
    p_1_n: F,
    p_1_d: F,
}

impl<F: PrimeField, Parameters: DiscreteLogParameters> ChallengePoint<F, Parameters> {
    fn new(
        curve: &CurveSpec<F>,
        // The slope between all of the challenge points
        slope: F,
        // The x and y coordinates
        x: F,
        y: F,
        // The inversion of twice the y coordinate
        // We accept this as an argument so that the caller can calculate these with a batch inversion
        inv_two_y: F,
    ) -> Self {
        // Powers of x, skipping x**0
        let divisor_x_len = Parameters::XCoefficients::USIZE;
        let mut x_pows = GenericArray::default();
        x_pows[0] = x;
        for i in 1..divisor_x_len {
            let last = x_pows[i - 1];
            x_pows[i] = last * x;
        }

        // Powers of x multiplied by y
        let divisor_yx_len = Parameters::YxCoefficients::USIZE;
        let mut yx = GenericArray::default();
        // Skips x**0
        yx[0] = y * x;
        for i in 1..divisor_yx_len {
            let last = yx[i - 1];
            yx[i] = last * x;
        }

        let x_sq = x.square();
        let three_x_sq = x_sq.double() + x_sq;
        let three_x_sq_plus_a = three_x_sq + curve.a;
        let two_y = y.double();

        // p_0_n_0 from `DivisorChallenge`
        let p_0_n_0 = three_x_sq_plus_a * inv_two_y;
        let mut x_p_0_n_0 = GenericArray::default();
        // Since this iterates over x, which skips x**0, this also skips p_0_n_0 x**0
        for (i, x) in x_pows.iter().take(divisor_yx_len).enumerate() {
            x_p_0_n_0[i] = p_0_n_0 * x;
        }

        // p_1_n from `DivisorChallenge`
        let p_1_n = two_y;
        // p_1_d from `DivisorChallenge`
        let p_1_d = (-slope * p_1_n) + three_x_sq_plus_a;

        ChallengePoint {
            x: x_pows,
            y,
            yx,
            p_0_n_0,
            x_p_0_n_0,
            p_1_n,
            p_1_d,
        }
    }
}

/// A challenge to evaluate divisors with.
///
/// This challenge must be sampled after writing the commitments to the transcript. This challenge
/// is reusable across various divisors.
// #[derive(Debug)]
pub struct DiscreteLogChallenge<F: PrimeField, Parameters: DiscreteLogParameters> {
    c0: Box<ChallengePoint<F, Parameters>>,
    c1: Box<ChallengePoint<F, Parameters>>,
    c2: Box<ChallengePoint<F, Parameters>>,
    slope: F,
    intercept: F,
}

/// A generator which has been challenged and is ready for use in evaluating discrete logarithm
/// claims.
#[derive(Debug)]
pub struct ChallengedGenerator<F: PrimeField, Parameters: DiscreteLogParameters>(
    GenericArray<F, Parameters::ScalarBits>,
);

impl<F: PrimeField, Parameters: DiscreteLogParameters> PointWithDlog<F, Parameters> {
    pub fn from_vars(
        mut decomposition: Vec<Variable<F>>,
        mut divisor: Vec<Variable<F>>,
    ) -> Box<Self> {
        let blind_x_var = decomposition.pop().unwrap();
        let blind_y_var = divisor.pop().unwrap();
        let dlog = GenericArray::<_, Parameters::ScalarBits>::from_slice(&decomposition).clone();

        let mut cursor_start = 1;
        let mut cursor_end = cursor_start + Parameters::YxCoefficients::USIZE;
        let yx = GenericArray::<_, Parameters::YxCoefficients>::from_slice(
            &divisor[cursor_start..cursor_end],
        )
        .clone();
        cursor_start = cursor_end;
        cursor_end += Parameters::XCoefficientsMinusOne::USIZE;
        let x_from_power_of_2 = GenericArray::<_, Parameters::XCoefficientsMinusOne>::from_slice(
            &divisor[cursor_start..cursor_end],
        )
        .clone();
        let divisor = Divisor {
            y: divisor[0],
            yx,
            x_from_power_of_2,
            zero: divisor[cursor_end],
        };
        Box::new(PointWithDlog {
            divisor,
            dlog,
            point: (blind_x_var, blind_y_var),
        })
    }
}

fn divisor_challenge_eval<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    divisor: &Divisor<F, Parameters>,
    challenge: &ChallengePoint<F, Parameters>,
) -> LinearCombination<F> {
    // The evaluation of the divisor differentiated by y, further multiplied by p_0_n_0
    // Differentiation drops everything without a y coefficient, and drops what remains by a power
    // of y
    // (y**1 -> y**0, yx**i -> x**i)
    // This aligns with p_0_n_1  from `DivisorChallenge`
    let mut p_0_n_1 = LinearCombination::from_iter([(divisor.y, challenge.p_0_n_0)]);
    for (j, var) in divisor.yx.iter().enumerate() {
        // This does not index by `j + 1` as x_p_0_n_0 omits x**0
        p_0_n_1 = p_0_n_1 + LinearCombination::from_iter([(*var, challenge.x_p_0_n_0[j])]);
    }

    // The evaluation of the divisor differentiated by x
    // This aligns with p_0_n_2 from `DivisorChallenge`
    // The coefficient for x**1 is 1, so 1 becomes the new zero coefficient
    let mut p_0_n_2 = constant(F::ONE);

    // Handle the new y coefficient
    p_0_n_2 = p_0_n_2 + LinearCombination::from_iter([(divisor.yx[0], challenge.y)]);

    // Handle the new yx coefficients
    for (j, yx) in divisor.yx.iter().enumerate().skip(1) {
        // For the power which was shifted down, we multiply this coefficient
        // 3 x**2 -> 2 * 3 x**1
        let original_power_of_x = F::from((j + 1) as u64);
        // `j - 1` so `j = 1` indexes yx[0] as yx[0] is the y x**1
        // (yx omits y x**0)
        let weight = original_power_of_x * challenge.yx[j - 1];
        p_0_n_2 = p_0_n_2 + LinearCombination::from_iter([(*yx, weight)]);
    }

    // Handle the x coefficients
    // We don't skip the first one as `x_from_power_of_2` already omits x**1
    for (i, x) in divisor.x_from_power_of_2.iter().enumerate() {
        // i + 2 as the paper expects i to start from 1 and be + 1, yet we start from 0
        let original_power_of_x = F::from((i + 2) as u64);
        // Still x[i] as x[0] is x**1
        let weight = original_power_of_x * challenge.x[i];
        p_0_n_2 = p_0_n_2 + LinearCombination::from_iter([(*x, weight)]);
    }

    // p_0_n from `DivisorChallenge`
    let p_0_n = p_0_n_1 + p_0_n_2;

    // Evaluation of the divisor
    // p_0_d from `DivisorChallenge`
    let mut p_0_d = LinearCombination::from_iter([(divisor.y, challenge.y)]);
    for (var, c_yx) in divisor.yx.iter().zip(&challenge.yx) {
        p_0_d = p_0_d + LinearCombination::from_iter([(*var, *c_yx)]);
    }

    for (i, var) in divisor.x_from_power_of_2.iter().enumerate() {
        // This `i+1` is preserved, despite most not being as x omits x**0, as this assumes we
        // start with `i=1`
        p_0_d = p_0_d + LinearCombination::from_iter([(*var, challenge.x[i + 1])]);
    }

    // Adding x effectively adds a `1 x` term, ensuring the divisor isn't 0
    p_0_d = p_0_d + LinearCombination::from_iter([(divisor.zero, F::ONE)]);
    p_0_d = p_0_d + challenge.x[0];

    // Calculate the joint numerator
    // p_n from `DivisorChallenge`
    let p_n = p_0_n * challenge.p_1_n;
    // Calculate the joint denominator
    // p_d from `DivisorChallenge`
    let p_d = p_0_d * challenge.p_1_d;

    // We want `n / d = o`
    // `n / d = o` == `n = d * o`
    // These are safe unwraps as they're solely done by the prover and should always be non-zero
    let p_d_inv = inverse(cs, p_d.clone());
    let (_, _, o) = cs.multiply(p_n, p_d_inv);
    o.into()
}

/// Sample a challenge for a series of discrete logarithm claims.
///
/// This must be called after writing the commitments to the transcript.
///
/// The generators are assumed to be non-empty. They are not transcripted. If your generators are
/// dynamic, they must be properly transcripted into the context.
///
/// May panic/have undefined behavior if an assumption is broken.
///
///
/// This is part of `DiscreteLog` from `Discrete Log Proof`, specifically, the challenges and
/// the calculations dependent solely on them
#[allow(clippy::type_complexity)]
pub fn discrete_log_challenge<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    curve: &CurveSpec<F>,
    generators: &[&GeneratorTable<F, Parameters>],
) -> Result<
    (
        DiscreteLogChallenge<F, Parameters>,
        Vec<ChallengedGenerator<F, Parameters>>,
    ),
    Error,
> {
    let transcript = cs.transcript();
    let mut sign_of_points = [0; 64];
    // Get the challenge points
    transcript.challenge_bytes(b"sign", &mut sign_of_points);
    let sign_of_point_0 = (sign_of_points[0] & 1) == 1;
    let sign_of_point_1 = ((sign_of_points[0] >> 1) & 1) == 1;

    fn sample_embedded_curve_point<F: PrimeField>(
        transcript: &mut MerlinTranscript,
        curve: &CurveSpec<F>,
        odd_y_coordinate: bool,
    ) -> (F, F) {
        loop {
            let c_x = transcript.challenge_scalar::<F>(b"c_x");
            let c_x_cube = c_x.square() * c_x;
            let ax = curve.a * c_x;
            let Some(c_y) = (c_x_cube + ax + curve.b).sqrt() else {
                continue;
            };
            // Takes a specific y coordinate as to not be dependent on whatever root the above sqrt
            // happens to returns
            let c_y_is_odd = c_y.into_bigint().is_odd();
            return (
                c_x,
                if c_y_is_odd != odd_y_coordinate {
                    -c_y
                } else {
                    c_y
                },
            );
        }
    }

    let (c0_x, c0_y) = sample_embedded_curve_point::<F>(transcript, curve, sign_of_point_0);

    let c1_x;
    let c1_y;

    loop {
        let (x, y) = sample_embedded_curve_point::<F>(transcript, curve, sign_of_point_1);
        if x == c0_x {
            // new point cant be same or negative of old point
            continue;
        } else {
            c1_x = x;
            c1_y = y;
            break;
        }
    }

    // mmadd-1998-cmo
    fn incomplete_add<F: PrimeField>(x1: F, y1: F, x2: F, y2: F) -> (F, F) {
        let u = y2 - y1;
        let uu = u * u;
        let v = x2 - x1;
        let vv = v * v;
        let vvv = v * vv;
        let r = vv * x1;
        let a = uu - vvv - r.double();
        let x3 = v * a;
        let y3 = (u * (r - a)) - (vvv * y1);
        let z3 = vvv;

        // Normalize from XYZ to XY
        // unwrap is as both points are chosen to be distinct and not negative of each other
        let z3_inv = z3.inverse().unwrap();
        let x3 = x3 * z3_inv;
        let y3 = y3 * z3_inv;

        (x3, y3)
    }

    let (c2_x, c2_y) = incomplete_add::<F>(c0_x, c0_y, c1_x, c1_y);
    // We want C0, C1, C2 = -(C0 + C1)
    let c2_y = -c2_y;

    // Calculate the slope and intercept
    // Safe invert as these x coordinates must be distinct due to passing the above incomplete_add
    let slope = (c1_y - c0_y) * (c1_x - c0_x).inverse().unwrap();
    let intercept = c0_y - (slope * c0_x);

    // Calculate the inversions for 2 c_y (for each c) and all of the challenged generators
    let mut inversions = vec![F::ZERO; 3 + (generators.len() * Parameters::ScalarBits::USIZE)];

    // Needed for the left-hand side eval
    {
        inversions[0] = c0_y.double();
        inversions[1] = c1_y.double();
        inversions[2] = c2_y.double();
    }

    // Perform the inversions for the generators
    for (i, generator) in generators.iter().enumerate() {
        // Needed for the right-hand side eval
        for (j, generator) in generator.0.iter().enumerate() {
            // `DiscreteLog` has weights of `(mu - (G_i.y + (slope * G_i.x)))**-1` in its last line
            inversions[3 + (i * Parameters::ScalarBits::USIZE) + j] =
                intercept - (generator.1 - (slope * generator.0));
        }
    }
    for challenge_inversion in &inversions {
        // This should be unreachable barring negligible probability
        if challenge_inversion.is_zero().into() {
            return Err(Error::InvertingZero);
        }
    }

    batch_inversion(&mut inversions);

    let mut inversions = inversions.into_iter();
    let inv_c0_two_y = inversions.next().unwrap();
    let inv_c1_two_y = inversions.next().unwrap();
    let inv_c2_two_y = inversions.next().unwrap();

    let c0 = Box::new(ChallengePoint::new(curve, slope, c0_x, c0_y, inv_c0_two_y));
    let c1 = Box::new(ChallengePoint::new(curve, slope, c1_x, c1_y, inv_c1_two_y));
    let c2 = Box::new(ChallengePoint::new(curve, slope, c2_x, c2_y, inv_c2_two_y));

    transcript.append(b"alpha[0]_num", &c0.p_1_n);
    transcript.append(b"alpha[0]_den", &c0.p_1_d);
    transcript.append(b"alpha[1]_num", &c1.p_1_n);
    transcript.append(b"alpha[1]_den", &c1.p_1_d);
    transcript.append(b"alpha[2]_num", &c2.p_1_n);
    transcript.append(b"alpha[2]_den", &c2.p_1_d);

    // Fill in the inverted values
    let mut challenged_generators = Vec::with_capacity(generators.len());
    for _ in 0..generators.len() {
        let mut challenged_generator = GenericArray::default();
        for i in 0..Parameters::ScalarBits::USIZE {
            challenged_generator[i] = inversions.next().unwrap();
            transcript.append(b"beta", &challenged_generator[i]);
        }
        challenged_generators.push(ChallengedGenerator(challenged_generator));
    }

    Ok((
        DiscreteLogChallenge {
            c0,
            c1,
            c2,
            slope,
            intercept,
        },
        challenged_generators,
    ))
}

/// Prove this point has the specified discrete logarithm over the specified generator.
///
/// The discrete logarithm is not validated to be in a canonical form. The only guarantee made on
/// it is that it's a consistent representation of _a_ discrete logarithm (reuse won't enable
/// re-interpretation as a distinct discrete logarithm).
///
/// This does ensure the point is on-curve.
///
/// This MUST only be called with `Variable`s present within commitments.
///
/// May panic/have undefined behavior if an assumption is broken, or if passed an invalid
/// witness.
///
/// `DiscreteLog` from `Discrete Log Proof`
pub fn discrete_log<F: PrimeField, CS: ConstraintSystem<F>, Parameters: DiscreteLogParameters>(
    cs: &mut CS,
    curve: &CurveSpec<F>,
    point: PointWithDlog<F, Parameters>,
    challenge: &DiscreteLogChallenge<F, Parameters>,
    challenged_generator: &ChallengedGenerator<F, Parameters>,
) -> OnCurve<F> {
    let PointWithDlog {
        divisor,
        dlog,
        point,
    } = point;

    // Ensure this is being safely called
    let arg_iter = [point.0, point.1, divisor.y, divisor.zero];
    let arg_iter = arg_iter.iter().chain(divisor.yx.iter());
    let arg_iter = arg_iter.chain(divisor.x_from_power_of_2.iter());
    let arg_iter = arg_iter.chain(dlog.iter());
    for variable in arg_iter {
        debug_assert!(
            matches!(
                variable,
                Variable::VectorCommit(_, _) | Variable::Committed(_)
            ),
            "discrete log proofs requires all arguments belong to commitments",
        );
    }

    constrain_challenge_eval(
        cs,
        curve,
        dlog,
        point,
        divisor,
        challenge,
        challenged_generator,
    );
    OnCurve {
        x: LinearCombination::from(point.0),
        y: LinearCombination::from(point.1),
    }
}

fn constrain_challenge_eval<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    curve: &CurveSpec<F>,
    dlog: GenericArray<Variable<F>, Parameters::ScalarBits>,
    point: (Variable<F>, Variable<F>),
    divisor: Divisor<F, Parameters>,
    challenge: &DiscreteLogChallenge<F, Parameters>,
    challenged_generator: &ChallengedGenerator<F, Parameters>,
) {
    // Check the point is on curve
    let point_on_curve = OnCurve {
        x: LinearCombination::from(point.0),
        y: LinearCombination::from(point.1),
    };
    on_curve(cs, point_on_curve, curve);

    // The challenge has already been sampled so those lines aren't necessary

    // lhs from the paper, evaluating the divisor
    let c0_eval = divisor_challenge_eval(cs, &divisor, &challenge.c0);
    let c1_eval = divisor_challenge_eval(cs, &divisor, &challenge.c1);
    let c2_eval = divisor_challenge_eval(cs, &divisor, &challenge.c2);
    let lhs_eval = LinearCombination::default() + c0_eval + c1_eval + c2_eval;

    // Interpolate the doublings of the generator
    let mut rhs_eval = LinearCombination::default();
    // We call this `bit` yet it's not constrained to being a bit
    // It's presumed to be yet may be malleated
    for (bit, weight) in dlog.into_iter().zip(&challenged_generator.0) {
        rhs_eval = rhs_eval + LinearCombination::from_iter([(bit, *weight)]);
    }

    // Interpolate the output point
    // intercept - (y - (slope * x))
    // intercept - y + (slope * x)
    // -y + (slope * x) + intercept
    // EXCEPT the output point we're proving the discrete log for isn't the one interpolated
    // Its negative is, so -y becomes y
    // y + (slope * x) + intercept
    let output_interpolation = LinearCombination::default()
        + challenge.intercept
        + point.1
        + LinearCombination::from_iter([(point.0, challenge.slope)]);

    let output_interpolation_eval_inv = inverse(cs, output_interpolation);
    rhs_eval = rhs_eval + output_interpolation_eval_inv;

    cs.constrain(lhs_eval - rhs_eval);
}

/// For enforcing `original_point + blind.point = blinded_point`
pub fn discrete_log_blinding<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    original_point: (
        impl Into<LinearCombination<F>>,
        impl Into<LinearCombination<F>>,
    ),
    blind: PointWithDlog<F, Parameters>,
    blinded_point: (F, F),
    curve: &CurveSpec<F>,
    table: &[&GeneratorTable<F, Parameters>],
) -> Result<(), Error> {
    let (challenge, challenged_generators) = discrete_log_challenge(cs, curve, table)?;
    let mut challenged_generators = challenged_generators.into_iter();
    let challenged_T = challenged_generators.next().unwrap();
    discrete_log_blinding_given_challenge(
        cs,
        original_point,
        blind,
        blinded_point,
        curve,
        &challenge,
        &challenged_T,
    );
    Ok(())
}

pub fn discrete_log_blinding_given_challenge<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    original_point: (
        impl Into<LinearCombination<F>>,
        impl Into<LinearCombination<F>>,
    ),
    blind: PointWithDlog<F, Parameters>,
    blinded_point: (F, F),
    curve: &CurveSpec<F>,
    challenge: &DiscreteLogChallenge<F, Parameters>,
    challenged_T: &ChallengedGenerator<F, Parameters>,
) {
    let o_x_lc = original_point.0.into();
    let o_y_lc = original_point.1.into();
    let (o_tilde_x, o_tilde_y) = blinded_point;

    // Check O is on curve
    let O = OnCurve {
        x: o_x_lc,
        y: o_y_lc,
    };
    on_curve(cs, O.clone(), &curve);

    // Discrete log for o_blind
    let o_blind = discrete_log(cs, &curve, blind, challenge, challenged_T);

    // Check O = O_tilde + o_blind
    incomplete_add_pub(cs, (o_tilde_x, o_tilde_y), o_blind, O);
}

#[derive(Debug, Clone)]
pub struct DivisorWitness<F: PrimeField, Parameters: DiscreteLogParameters> {
    /// Decomposition of the scalar
    pub decomposition: GenericArray<F, U256>,
    /// The divisor of the resulting point
    pub divisor: GenericArray<F, U256>,
    phantom: PhantomData<Parameters>,
}

impl<F: PrimeField, Parameters: DiscreteLogParameters> DivisorWitness<F, Parameters> {
    pub fn new(decomposition: GenericArray<F, U256>, divisor: GenericArray<F, U256>) -> Self {
        Self {
            decomposition,
            divisor,
            phantom: PhantomData,
        }
    }
}

/// When the same scalar is multiplied by multiple generators, we can use this for an efficient proof
/// A possible usage would be for curve tree where each level uses a different generator but same blinding
#[derive(Debug, Clone)]
pub struct DivisorWitnessMulti<F: PrimeField, Parameters: DiscreteLogParameters> {
    /// Decomposition of the scalar
    pub decomposition: GenericArray<F, U255>,
    /// x-coordinates of the resulting points
    pub result_xs: Vec<F>,
    /// Divisors for the resulting points
    pub divisors: Vec<GenericArray<F, U256>>,
    phantom: PhantomData<Parameters>,
}

impl<F: PrimeField, Parameters: DiscreteLogParameters> DivisorWitnessMulti<F, Parameters> {
    pub fn new(
        decomposition: GenericArray<F, U255>,
        result_xs: Vec<F>,
        divisors: Vec<GenericArray<F, U256>>,
    ) -> Self {
        Self {
            decomposition,
            result_xs,
            divisors,
            phantom: PhantomData,
        }
    }
}

pub fn create_divisor_and_decomposition<
    F: PrimeField,
    C: DivisorCurve<BaseField = F>,
    Parameters: DiscreteLogParameters,
>(
    generator_source: impl GeneratorMultiplesSource<C> + Clone,
    blinding: C::ScalarField,
) -> Result<Box<DivisorWitness<F, Parameters>>, Error> {
    let (scalar, mut decomposition_vec) =
        decompose_scalar::<C::ScalarField, C::BaseField, Parameters>(blinding)?;

    let scalar_mul_and_divisor = ScalarMulAndDivisor::<C>::new(&scalar, generator_source)?;
    let result_x = scalar_mul_and_divisor.x;
    let result_y = scalar_mul_and_divisor.y;

    decomposition_vec.push(result_x);

    let decomposition = GenericArray::from_slice(&decomposition_vec).clone();
    let divisor = get_divisor_array::<F, Parameters>(&scalar_mul_and_divisor.divisor, result_y)?;
    Ok(Box::new(DivisorWitness::<F, Parameters>::new(
        decomposition,
        divisor,
    )))
}

/// Assumes `vars_dlog` and `vars_divisor` are of appropriate length.
fn dlog_and_divisor_vars<F: PrimeField, Parameters: DiscreteLogParameters>(
    mut vars_dlog: Vec<Variable<F>>,
    mut vars_divisor: Vec<Variable<F>>,
) -> Box<PointWithDlog<F, Parameters>> {
    // x and y coordinates of the scalar multiplication result. By convention these are kept at the end
    let blind_x_var = vars_dlog.pop().unwrap();
    let blind_y_var = vars_divisor.pop().unwrap();

    // Remove padding elements as they are 0s
    while vars_dlog.len() > Parameters::ScalarBits::USIZE {
        vars_dlog.pop().unwrap();
    }
    let dlog = GenericArray::<_, Parameters::ScalarBits>::from_slice(&vars_dlog).clone();

    let mut cursor_start = 1;
    let mut cursor_end = cursor_start + Parameters::YxCoefficients::USIZE;
    let yx = GenericArray::<_, Parameters::YxCoefficients>::from_slice(
        &vars_divisor[cursor_start..cursor_end],
    )
    .clone();
    cursor_start = cursor_end;
    cursor_end += Parameters::XCoefficientsMinusOne::USIZE;
    let x_from_power_of_2 = GenericArray::<_, Parameters::XCoefficientsMinusOne>::from_slice(
        &vars_divisor[cursor_start..cursor_end],
    )
    .clone();
    let divisor = Divisor {
        y: vars_divisor[0],
        yx,
        x_from_power_of_2,
        zero: vars_divisor[cursor_end],
    };

    Box::new(PointWithDlog {
        divisor,
        dlog,
        point: (blind_x_var, blind_y_var),
    })
}

pub fn commit_witness_chunks_prover<
    F: PrimeField,
    C: AffineRepr<ScalarField = F>,
    R: CryptoRngCore,
    Parameters: DiscreteLogParameters,
>(
    rng: &mut R,
    cs: &mut Prover<MerlinTranscript, C>,
    divisor_witness: &DivisorWitness<F, Parameters>,
    chunk_len: usize,
    bp_gens: &BulletproofGens<C>,
) -> Result<
    (
        DivisorComms<C>,
        DivisorCommsBlindings<F>,
        Box<PointWithDlog<F, Parameters>>,
    ),
    Error,
> {
    // Combine scalar decomposition and divisor coefficients in single vector so they can be committed in chunks
    let combined_witness: Vec<F> = divisor_witness
        .decomposition
        .as_slice()
        .iter()
        .chain(divisor_witness.divisor.as_slice().iter())
        .cloned()
        .collect();
    if combined_witness.len() % chunk_len != 0 {
        return Err(Error::WitnessChunkLengthMismatch(
            combined_witness.len(),
            chunk_len,
        ));
    }

    let chunk_count = combined_witness.len() / chunk_len;
    let mut commitments = Vec::with_capacity(chunk_count);
    let mut blindings_vec = Vec::with_capacity(chunk_count);
    // Single vector of variables corresponding to each digit in scalar decomposition and each divisor coefficient
    let mut vars = Vec::with_capacity(combined_witness.len());

    // Divide `combined_witness` into 1 or more chunks and commit each chunk
    // Don't want to commit large vectors as they negatively impact perf, trading off proof size for time
    for i in 0..chunk_count {
        let chunk = &combined_witness[i * chunk_len..(i + 1) * chunk_len];
        let blinding = F::rand(rng);
        let (comm, vars_chunk) = cs.commit_vec(chunk, blinding, bp_gens);
        commitments.push(comm);
        blindings_vec.push(blinding);
        vars.extend(vars_chunk);
    }

    let comms = DivisorComms(commitments);
    let blindings = DivisorCommsBlindings(blindings_vec);

    // Split vars back into dlog and divisor parts
    let vars_dlog = vars[0..divisor_witness.decomposition.len()].to_vec();
    let vars_divisor = vars[divisor_witness.decomposition.len()..].to_vec();

    #[cfg(debug_assertions)]
    {
        // -1 since last element is zero
        for i in Parameters::ScalarBits::USIZE..(DECOMPOSITION_SIZE - 1) {
            debug_assert!(
                divisor_witness.decomposition[i].is_zero(),
                "dlog padding should be zero"
            );
        }
    }

    let point_with_dlog = dlog_and_divisor_vars(vars_dlog, vars_divisor);

    Ok((comms, blindings, point_with_dlog))
}

pub fn commit_witness_chunks_verifier<
    F: PrimeField,
    C: AffineRepr<ScalarField = F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut Verifier<MerlinTranscript, C>,
    comms: &DivisorComms<C>,
    chunk_len: usize,
) -> Result<Box<PointWithDlog<F, Parameters>>, Error> {
    if chunk_len == 0 {
        return Err(Error::ZeroChunkSize);
    }

    let expected_vars_len = DECOMPOSITION_SIZE * 2;
    let mut vars = Vec::with_capacity(expected_vars_len);

    for comm in &comms.0 {
        let chunk_vars = cs.commit_vec(chunk_len, *comm);
        vars.extend(chunk_vars);
    }
    // Allow padding
    if vars.len() < expected_vars_len {
        return Err(Error::VerifierWitnessVarCountMismatch {
            got: vars.len(),
            expected: expected_vars_len,
        });
    }

    let vars_dlog = vars[0..DECOMPOSITION_SIZE].to_vec();
    let vars_divisor = vars[DECOMPOSITION_SIZE..].to_vec();

    Ok(dlog_and_divisor_vars(vars_dlog, vars_divisor))
}

/// Each generator in `generator_sources` is multiplied by the scalar `blinding`
pub fn create_divisor_and_decomposition_multi_gen<
    F: PrimeField,
    C: DivisorCurve<BaseField = F>,
    Parameters: DiscreteLogParameters,
>(
    generator_sources: &[&GeneratorTable<F, Parameters>],
    blinding: C::ScalarField,
) -> Result<Box<DivisorWitnessMulti<F, Parameters>>, Error> {
    let (scalar, decomposition_vec) =
        decompose_scalar::<C::ScalarField, C::BaseField, Parameters>(blinding)?;

    let mut result_xs = Vec::with_capacity(generator_sources.len());
    let mut divisors = Vec::with_capacity(generator_sources.len());

    for &gen_table in generator_sources {
        let smd = ScalarMulAndDivisor::<C>::new(&scalar, gen_table)?;
        result_xs.push(smd.x);

        let result_y = smd.y;

        let divisor = get_divisor_array::<F, Parameters>(&smd.divisor, result_y)?;
        divisors.push(divisor);
    }

    let decomposition = GenericArray::from_slice(&decomposition_vec).clone();
    Ok(Box::new(DivisorWitnessMulti::<F, Parameters>::new(
        decomposition,
        result_xs,
        divisors,
    )))
}

/// Takes variables for resulting points and divisors and create the struct [`PointsWithDlog`].
fn dlog_and_divisor_vars_multi<F: PrimeField, Parameters: DiscreteLogParameters>(
    vars: Vec<Variable<F>>,
    num_points: usize,
) -> PointsWithDlog<F, Parameters> {
    let dlog_bits = Parameters::ScalarBits::USIZE;
    // Since the scalar is same in all multiplications (all points have same dlog), its decomposition is present only once
    let dlog = GenericArray::<_, Parameters::ScalarBits>::from_slice(&vars[0..dlog_bits]).clone();

    // Next get variables for x-coordinates of the resulting points
    let result_xs: Vec<Variable<F>> =
        vars[MAX_BITS_SUPPORTED..MAX_BITS_SUPPORTED + num_points].to_vec();

    let divisor_start = MAX_BITS_SUPPORTED + num_points;
    let divisor_block_size = DECOMPOSITION_SIZE;

    let mut points = Vec::with_capacity(num_points);
    let mut divisors = Vec::with_capacity(num_points);

    for i in 0..num_points {
        let div_block_start = divisor_start + i * divisor_block_size;
        // Variables corresponding to the coefficients of the divisor polynomial for i-th point
        let coeff_vars = &vars[div_block_start..div_block_start + divisor_block_size];

        let result_x_var = result_xs[i];
        let result_y_var = coeff_vars[divisor_block_size - 1];

        let y = coeff_vars[0];
        let mut cursor = 1;
        let yx = GenericArray::<_, Parameters::YxCoefficients>::from_slice(
            &coeff_vars[cursor..cursor + Parameters::YxCoefficients::USIZE],
        )
        .clone();
        cursor += Parameters::YxCoefficients::USIZE;
        let x_from_power_of_2 = GenericArray::<_, Parameters::XCoefficientsMinusOne>::from_slice(
            &coeff_vars[cursor..cursor + Parameters::XCoefficientsMinusOne::USIZE],
        )
        .clone();
        cursor += Parameters::XCoefficientsMinusOne::USIZE;
        let zero = coeff_vars[cursor];

        let divisor = Divisor {
            y,
            yx,
            x_from_power_of_2,
            zero,
        };
        points.push((result_x_var, result_y_var));
        divisors.push(divisor);
    }

    PointsWithDlog {
        points,
        dlog,
        divisors,
    }
}

pub fn commit_witness_chunks_prover_multi_gen<
    F: PrimeField,
    C: AffineRepr<ScalarField = F>,
    R: CryptoRngCore,
    Parameters: DiscreteLogParameters,
>(
    rng: &mut R,
    cs: &mut Prover<MerlinTranscript, C>,
    witness: &DivisorWitnessMulti<F, Parameters>,
    chunk_len: usize,
    bp_gens: &BulletproofGens<C>,
) -> Result<
    (
        DivisorComms<C>,
        DivisorCommsBlindings<F>,
        PointsWithDlog<F, Parameters>,
    ),
    Error,
> {
    let num_points = witness.divisors.len();
    // scalar decomposition + (x-coordinate per point) + (divisor coefficients per point)
    let len = witness.decomposition.len() + num_points + num_points * DECOMPOSITION_SIZE;

    let padded_len = if len % chunk_len == 0 {
        len
    } else {
        len + chunk_len - (len % chunk_len)
    };

    let mut combined_witness = Vec::with_capacity(padded_len);
    combined_witness.extend_from_slice(witness.decomposition.as_slice());
    combined_witness.extend_from_slice(&witness.result_xs);
    for div in &witness.divisors {
        combined_witness.extend_from_slice(div.as_slice());
    }
    combined_witness.resize(padded_len, F::ZERO);

    if combined_witness.len() % chunk_len != 0 {
        return Err(Error::WitnessChunkLengthMismatch(
            combined_witness.len(),
            chunk_len,
        ));
    }

    let chunk_count = combined_witness.len() / chunk_len;
    let mut commitments = Vec::with_capacity(chunk_count);
    let mut blindings_vec = Vec::with_capacity(chunk_count);

    // Single vector of variables corresponding to each digit in scalar decomposition and each divisor coefficient of all points
    let mut vars = Vec::with_capacity(combined_witness.len());

    // Divide `combined_witness` into 1 or more chunks and commit each chunk
    for i in 0..chunk_count {
        let chunk = &combined_witness[i * chunk_len..(i + 1) * chunk_len];
        let blinding = F::rand(rng);
        let (comm, vars_chunk) = cs.commit_vec(chunk, blinding, bp_gens);
        commitments.push(comm);
        blindings_vec.push(blinding);
        vars.extend(vars_chunk);
    }

    let comms = DivisorComms(commitments);
    let blindings = DivisorCommsBlindings(blindings_vec);
    let points_with_dlog = dlog_and_divisor_vars_multi(vars, num_points);

    Ok((comms, blindings, points_with_dlog))
}

pub fn commit_witness_chunks_verifier_multi_gen<
    F: PrimeField,
    C: AffineRepr<ScalarField = F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut Verifier<MerlinTranscript, C>,
    comms: &DivisorComms<C>,
    chunk_len: usize,
    num_generators: usize,
) -> Result<PointsWithDlog<F, Parameters>, Error> {
    if chunk_len == 0 {
        return Err(Error::ZeroChunkSize);
    }
    let expected_vars_len =
        MAX_BITS_SUPPORTED + num_generators + (num_generators * DECOMPOSITION_SIZE);
    let mut vars = Vec::with_capacity(expected_vars_len);
    for comm in &comms.0 {
        let chunk_vars = cs.commit_vec(chunk_len, *comm);
        vars.extend(chunk_vars);
    }
    // Allow padding
    if vars.len() < expected_vars_len {
        return Err(Error::VerifierWitnessVarCountMismatch {
            got: vars.len(),
            expected: expected_vars_len,
        });
    }
    Ok(dlog_and_divisor_vars_multi(vars, num_generators))
}

/// Similar to [`discrete_log`] but proves that given points have the specified discrete logarithm over
/// the specified generators.
///
/// Returns an error if the number of divisors, points, or challenged generators don't match.
pub fn discrete_log_multi_gen<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    curve: &CurveSpec<F>,
    points_with_dlog: PointsWithDlog<F, Parameters>,
    challenge: &DiscreteLogChallenge<F, Parameters>,
    challenged_generators: &[ChallengedGenerator<F, Parameters>],
) -> Result<Vec<OnCurve<F>>, Error> {
    let PointsWithDlog {
        divisors,
        dlog,
        points,
    } = points_with_dlog;

    if divisors.len() != points.len() {
        return Err(Error::MismatchedSize(divisors.len(), points.len()));
    }
    if divisors.len() != challenged_generators.len() {
        return Err(Error::MismatchedSize(
            divisors.len(),
            challenged_generators.len(),
        ));
    }

    let n = divisors.len();
    let mut result_points = Vec::with_capacity(n);

    for (i, ((point, divisor), challenged_generator)) in points
        .into_iter()
        .zip(divisors.into_iter())
        .into_iter()
        .zip(challenged_generators.into_iter())
        .enumerate()
    {
        let arg_iter = [point.0, point.1, divisor.y, divisor.zero];
        let arg_iter = arg_iter.iter().chain(divisor.yx.iter());
        let arg_iter = arg_iter.chain(divisor.x_from_power_of_2.iter());
        for variable in arg_iter {
            debug_assert!(
                matches!(
                    variable,
                    Variable::VectorCommit(_, _) | Variable::Committed(_)
                ),
                "discrete log proofs requires all arguments belong to commitments",
            );
        }
        if i == 0 {
            for variable in dlog.iter() {
                debug_assert!(
                    matches!(
                        variable,
                        Variable::VectorCommit(_, _) | Variable::Committed(_)
                    ),
                    "discrete log proofs requires all arguments belong to commitments",
                );
            }
        }

        constrain_challenge_eval(
            cs,
            curve,
            dlog.clone(),
            point,
            divisor,
            challenge,
            challenged_generator,
        );
        result_points.push(OnCurve {
            x: LinearCombination::from(point.0),
            y: LinearCombination::from(point.1),
        });
    }

    Ok(result_points)
}

/// For enforcing `original_points[i] + blinds[i].point = blinded_points[i]`. Each `blinds[i].point` has
/// the same discrete log but with a different generator
pub fn discrete_log_blinding_multi_gen<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    original_points: &[(Variable<F>, Variable<F>)],
    blinds: PointsWithDlog<F, Parameters>,
    blinded_points: &[(F, F)],
    curve: &CurveSpec<F>,
    tables: &[&GeneratorTable<F, Parameters>],
) -> Result<(), Error> {
    let (challenge, challenged_generators) = discrete_log_challenge(cs, curve, tables)?;
    discrete_log_blinding_multi_gen_given_challenge(
        cs,
        original_points,
        blinds,
        blinded_points,
        curve,
        &challenge,
        &challenged_generators,
    )
}

pub fn discrete_log_blinding_multi_gen_given_challenge<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    original_points: &[(Variable<F>, Variable<F>)],
    blinds: PointsWithDlog<F, Parameters>,
    blinded_points: &[(F, F)],
    curve: &CurveSpec<F>,
    challenge: &DiscreteLogChallenge<F, Parameters>,
    challenged_generators: &[ChallengedGenerator<F, Parameters>],
) -> Result<(), Error> {
    let n = original_points.len();

    if n != blinded_points.len() {
        return Err(Error::MismatchedSize(n, blinded_points.len()));
    }
    if n != blinds.points.len() {
        return Err(Error::MismatchedSize(n, blinds.points.len()));
    }
    if n != challenged_generators.len() {
        return Err(Error::MismatchedSize(n, challenged_generators.len()));
    }

    let original_on_curves: Vec<OnCurve<F>> = original_points
        .iter()
        .map(|(x, y)| {
            let oc = OnCurve {
                x: LinearCombination::from(*x),
                y: LinearCombination::from(*y),
            };
            on_curve(cs, oc.clone(), curve);
            oc
        })
        .collect();

    let blind_on_curves =
        discrete_log_multi_gen(cs, curve, blinds, challenge, challenged_generators)?;

    for i in 0..n {
        incomplete_add_pub(
            cs,
            blinded_points[i],
            blind_on_curves[i].clone(),
            original_on_curves[i].clone(),
        );
    }

    Ok(())
}

/// For 2 relations: `R = P + gen_1 * b` and `S = gen_2 * b`
/// Expects `points_with_dlog` to be for exactly 2 points
pub fn discrete_log_blinding_and_dlog<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    original_point: (Variable<F>, Variable<F>),
    points_with_dlog: PointsWithDlog<F, Parameters>,
    blinded_point: (F, F),
    curve: &CurveSpec<F>,
    tables: &[&GeneratorTable<F, Parameters>; 2],
) -> Result<OnCurve<F>, Error> {
    if tables.len() != 2 {
        return Err(Error::MismatchedSize(2, tables.len()));
    }
    if points_with_dlog.points.len() != 2 {
        return Err(Error::MismatchedSize(2, points_with_dlog.points.len()));
    }

    let (challenge, mut challenged_generators) = discrete_log_challenge(cs, curve, tables)?;
    let challenged_gen1 = challenged_generators.remove(0);
    let challenged_gen2 = challenged_generators.remove(0);

    discrete_log_blinding_and_dlog_given_challenge(
        cs,
        original_point,
        points_with_dlog,
        blinded_point,
        curve,
        &challenge,
        &challenged_gen1,
        &challenged_gen2,
    )
}

pub fn discrete_log_blinding_and_dlog_given_challenge<
    F: PrimeField,
    CS: ConstraintSystem<F>,
    Parameters: DiscreteLogParameters,
>(
    cs: &mut CS,
    original_point: (Variable<F>, Variable<F>),
    points_with_dlog: PointsWithDlog<F, Parameters>,
    blinded_point: (F, F),
    curve: &CurveSpec<F>,
    challenge: &DiscreteLogChallenge<F, Parameters>,
    challenged_gen1: &ChallengedGenerator<F, Parameters>,
    challenged_gen2: &ChallengedGenerator<F, Parameters>,
) -> Result<OnCurve<F>, Error> {
    if points_with_dlog.points.len() != 2 {
        return Err(Error::MismatchedSize(2, points_with_dlog.points.len()));
    }
    if points_with_dlog.divisors.len() != 2 {
        return Err(Error::MismatchedSize(2, points_with_dlog.divisors.len()));
    }

    let PointsWithDlog {
        mut points,
        dlog,
        mut divisors,
    } = points_with_dlog;

    // Extract the second point with dlog for discrete log relation
    let blind2 = PointWithDlog {
        point: points.pop().unwrap(),
        dlog: dlog.clone(),
        divisor: divisors.pop().unwrap(),
    };

    // Extract the first point with dlog for blinding relation
    let blind1 = PointWithDlog {
        point: points.pop().unwrap(),
        dlog,
        divisor: divisors.pop().unwrap(),
    };

    // For R = P + gen_1 * b
    discrete_log_blinding_given_challenge(
        cs,
        original_point,
        blind1,
        blinded_point,
        curve,
        challenge,
        challenged_gen1,
    );

    // For S = gen_2 * b
    let result = discrete_log(cs, curve, blind2, challenge, challenged_gen2);

    Ok(result)
}

/// The second returned value is a list containing the scalar's decomposition and padded with 0s until its length is MAX_BITS_SUPPORTED
fn decompose_scalar<S: PrimeField, B: PrimeField, Parameters: DiscreteLogParameters>(
    blinding: S,
) -> Result<(ScalarDecomposition<S>, Vec<B>), Error> {
    // TODO: This is not general and wont support fields over 255 bits
    let scalar = ScalarDecomposition::new(blinding)?;
    let dlog_bits = Parameters::ScalarBits::USIZE;
    if dlog_bits > MAX_BITS_SUPPORTED {
        return Err(Error::UnsupportedScalarBits(dlog_bits));
    }

    let dlog = scalar.decomposition();
    if dlog.len() != dlog_bits {
        return Err(Error::DecompositionLengthMismatch(dlog.len(), dlog_bits));
    }

    // Allocating size DECOMPOSITION_SIZE to store the x-coordinate of the result as well
    let mut decomposition = Vec::with_capacity(DECOMPOSITION_SIZE);
    for i in 0..dlog_bits {
        decomposition.push(B::from(dlog[i]));
    }
    while decomposition.len() < MAX_BITS_SUPPORTED {
        decomposition.push(B::ZERO);
    }

    Ok((scalar, decomposition))
}

fn get_divisor_array<F: PrimeField, Parameters: DiscreteLogParameters>(
    divisor: &DivisorPoly<F>,
    result_y: F,
) -> Result<GenericArray<F, U256>, Error> {
    let yx_expected_len = Parameters::YxCoefficients::USIZE;
    let x_expected_len = Parameters::XCoefficients::USIZE;

    let witness_len = 1 + yx_expected_len + (x_expected_len - 1) + 1;
    if witness_len >= DECOMPOSITION_SIZE {
        return Err(Error::DivisorWitnessLengthExceeded(witness_len));
    }

    let mut divisor_witness = [F::ZERO; DECOMPOSITION_SIZE];
    divisor_witness[0] = divisor.y_coefficient;

    if divisor.yx_coefficients.len() > yx_expected_len {
        return Err(Error::IncorrectDivisorWitness(
            divisor.yx_coefficients.len(),
            yx_expected_len,
        ));
    }

    let yx = &divisor.yx_coefficients;
    for i in 0..yx_expected_len {
        divisor_witness[1 + i] = *yx.get(i).unwrap_or(&F::ZERO);
    }

    for i in 1..x_expected_len {
        divisor_witness[1 + yx_expected_len + i - 1] =
            *divisor.x_coefficients.get(i).unwrap_or(&F::ZERO);
    }

    divisor_witness[1 + yx_expected_len + x_expected_len - 1] = divisor.zero_coefficient;

    divisor_witness[DECOMPOSITION_SIZE - 1] = result_y;

    let divisor = GenericArray::from_array(divisor_witness);
    Ok(divisor)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::CurveSpec;
    use ark_ec::AffineRepr;
    use ark_ec::CurveGroup;
    use ark_ec::short_weierstrass::Projective;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use bulletproofs::r1cs::{Prover, Verifier};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use rand;
    use rand::prelude::StdRng;
    use rand_core::SeedableRng;
    use std::time::{Duration, Instant};

    use ark_ec_divisors::curves::pallas::PallasParams;
    use ark_pallas::{Affine as PallasAffine, Fq, Fr, PallasConfig};

    use ark_ec_divisors::curves::vesta::VestaParams;
    use ark_vesta::{Affine as VestaAffine, VestaConfig};

    use ark_ec_divisors::curves::helios::HeliosParams;
    use ark_helios::{Affine as HeliosAffine, Fq as HeliosBase, Fr as HeliosScalar, HeliosConfig};

    use ark_ec_divisors::curves::selene::SeleneParams;
    use ark_selene::{Affine as SeleneAffine, Fq as SeleneBase, Fr as SeleneScalar, SeleneConfig};

    use ark_ec_divisors::curves::wei25519::Wei25519Params;
    use ark_wei25519::{Fq as Wei25519Fq, Fr as Wei25519Fr, Wei25519Config};

    type PallasBase = Fq;
    type PallasScalar = Fr;

    type VestaBase = Fr;
    type VestaScalar = Fq;

    type Wei25519Base = Wei25519Fq;
    type Wei25519Scalar = Wei25519Fr;

    fn to_xy<C: DivisorCurve>(p: Projective<C>) -> Option<(C::BaseField, C::BaseField)> {
        let aff = p.into_affine();
        aff.xy()
    }

    #[test]
    fn test_commit_witness_chunks_verifier_rejects_malformed_commitments() {
        let mut rng = StdRng::seed_from_u64(11);
        let pc_gens = PedersenGens::<VestaAffine>::default();
        let bp_gens = BulletproofGens::<VestaAffine>::new(512, 1);
        let generator = Projective::<PallasConfig>::rand(&mut rng);
        let generator_table =
            GeneratorTable::<PallasBase, PallasParams>::new::<PallasConfig>(generator);

        let witness = create_divisor_and_decomposition::<_, PallasConfig, PallasParams>(
            &generator_table,
            PallasScalar::rand(&mut rng),
        )
        .unwrap();

        let vc_len = 64;

        let transcript = MerlinTranscript::new(b"malformed-dlog-prover");
        let mut prover = Prover::new(&pc_gens, transcript);
        let (comms, _, _) = commit_witness_chunks_prover::<_, _, _, PallasParams>(
            &mut rng,
            &mut prover,
            &witness,
            vc_len,
            &bp_gens,
        )
        .unwrap();

        let mut missing_chunk = comms.clone();
        missing_chunk.0.pop();

        let transcript = MerlinTranscript::new(b"malformed-dlog-verifier-short");
        let mut verifier = Verifier::new(transcript);
        let result = commit_witness_chunks_verifier::<_, _, PallasParams>(
            &mut verifier,
            &missing_chunk,
            vc_len,
        );
        match result {
            Err(err) => match err {
                Error::VerifierWitnessVarCountMismatch {
                    got: _,
                    expected: _,
                } => (),
                other => panic!("unexpected error variant: {other:?}"),
            },
            _ => panic!("expected verifier witness var count mismatch"),
        }

        let transcript = MerlinTranscript::new(b"malformed-dlog-verifier-zero");
        let mut verifier = Verifier::new(transcript);
        let result = commit_witness_chunks_verifier::<_, _, PallasParams>(&mut verifier, &comms, 0);
        match result {
            Err(err) => assert!(matches!(err, Error::ZeroChunkSize)),
            _ => panic!("expected zero chunk size error"),
        }
    }

    #[test]
    fn test_blinding_with_discrete_log() {
        fn check<
            C: DivisorCurve<BaseField = B, ScalarField = S>,
            Params: DiscreteLogParameters,
            B: PrimeField,
            S: PrimeField,
            BP: AffineRepr<ScalarField = B>,
        >(
            count: usize,
            vc_len: usize,
        ) {
            let mut rng = StdRng::seed_from_u64(0);

            let curve = CurveSpec::<B> {
                a: C::COEFF_A,
                b: C::COEFF_B,
            };

            let pc_gens = PedersenGens::<BP>::default();
            let bp_gens = BulletproofGens::<BP>::new(512, 1);

            let generator = Projective::<C>::rand(&mut rng);
            let generator_table = GeneratorTable::<B, Params>::new::<C>(generator);

            let mut proving_times = Vec::with_capacity(count);
            let mut proving_times_0 = Vec::with_capacity(count);
            let mut proving_times_00 = Vec::with_capacity(count);
            let mut verifying_times = Vec::with_capacity(count);
            let mut verifying_times_0 = Vec::with_capacity(count);
            let mut verifying_times_00 = Vec::with_capacity(count);
            let mut proof_size = 0;
            for _ in 0..count {
                // Create scalar o and compute o_blind = o.generator
                let o = S::rand(&mut rng);
                let o_blind_point = generator * o;
                let (minus_o_blind_x, minus_o_blind_y) = to_xy::<C>(-o_blind_point).unwrap();

                // Create O (the original point)
                let O = Projective::<C>::from(C::GENERATOR) * S::rand(&mut rng);

                // Create O_tilde = O + o_blind
                let o_tilde_point = O + o_blind_point;
                let (o_tilde_x, o_tilde_y) = to_xy::<C>(o_tilde_point).unwrap();
                let (o_x, o_y) = to_xy::<C>(O).unwrap();

                let start = Instant::now();

                let transcript = MerlinTranscript::new(b"test");
                let mut prover = Prover::new(&pc_gens, transcript);

                let (comm_orig, mut vars_orig) =
                    prover.commit_vec(&[o_x, o_y], B::rand(&mut rng), &bp_gens);
                let o_y_var = vars_orig.pop().unwrap();
                let o_x_var = vars_orig.pop().unwrap();

                let (comms, o_blind_claim) = {
                    let witness =
                        create_divisor_and_decomposition::<_, C, Params>(&generator_table, -o)
                            .unwrap();
                    let (comms, _, o_blind_claim) =
                        commit_witness_chunks_prover::<_, _, _, Params>(
                            &mut rng,
                            &mut prover,
                            &witness,
                            vc_len,
                            &bp_gens,
                        )
                        .unwrap();

                    (comms, o_blind_claim)
                };

                proving_times_00.push(start.elapsed());

                assert_eq!(minus_o_blind_x, prover.eval(&o_blind_claim.point.0.into()));
                assert_eq!(minus_o_blind_y, prover.eval(&o_blind_claim.point.1.into()));

                discrete_log_blinding(
                    &mut prover,
                    (o_x_var, o_y_var),
                    *o_blind_claim,
                    (o_tilde_x, o_tilde_y),
                    &curve,
                    &[&generator_table],
                )
                .unwrap();

                proving_times_0.push(start.elapsed());

                let proof = prover.prove(&bp_gens).unwrap();
                proving_times.push(start.elapsed());

                if proof_size == 0 {
                    proof_size = proof.compressed_size()
                        + comms.compressed_size()
                        + comm_orig.compressed_size();
                }

                let start = Instant::now();

                let transcript = MerlinTranscript::new(b"test");
                let mut verifier = Verifier::new(transcript);

                let mut vars_orig = verifier.commit_vec(2, comm_orig);
                let o_y_var = vars_orig.pop().unwrap();
                let o_x_var = vars_orig.pop().unwrap();

                let o_blind_claim =
                    commit_witness_chunks_verifier::<_, _, Params>(&mut verifier, &comms, vc_len)
                        .unwrap();

                verifying_times_00.push(start.elapsed());

                discrete_log_blinding(
                    &mut verifier,
                    (o_x_var, o_y_var),
                    *o_blind_claim,
                    (o_tilde_x, o_tilde_y),
                    &curve,
                    &[&generator_table],
                )
                .unwrap();

                verifying_times_0.push(start.elapsed());
                verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
                verifying_times.push(start.elapsed());
            }

            proving_times_0.sort();
            proving_times.sort();
            verifying_times_0.sort();
            verifying_times.sort();

            let total_prove_00: Duration = proving_times_00.iter().sum();
            let total_prove_0: Duration = proving_times_0.iter().sum();
            let total_prove: Duration = proving_times.iter().sum();
            let total_verify_00: Duration = verifying_times_00.iter().sum();
            let total_verify_0: Duration = verifying_times_0.iter().sum();
            let total_verify: Duration = verifying_times.iter().sum();
            let median_prove_00 = proving_times_00[count / 2];
            let median_prove_0 = proving_times_0[count / 2];
            let median_prove = proving_times[count / 2];
            let median_verify_00 = verifying_times_00[count / 2];
            let median_verify_0 = verifying_times_0[count / 2];
            let median_verify = verifying_times[count / 2];

            println!(
                "For {count} iterations, and vec commitment size={vc_len}, proof size (single) = {proof_size}, \
        total proving time: {:?}, median proving time: {:?}, total verification time: {:?}, median verification time: {:?}. \
        For non BP proof generation/verification, total proving {:?}, median proving {:?}, total verification {:?}, median verification {:?}. \
        For commitments, total proving {:?}, median proving {:?}, total verification {:?}, median verification {:?}",
                total_prove,
                median_prove,
                total_verify,
                median_verify,
                total_prove_0,
                median_prove_0,
                total_verify_0,
                median_verify_0,
                total_prove_00,
                median_prove_00,
                total_verify_00,
                median_verify_00
            );
        }

        let count = 5;
        let vc_len = 32;

        println!("Testing Pallas");
        check::<PallasConfig, PallasParams, PallasBase, PallasScalar, VestaAffine>(count, vc_len);

        println!("Testing Vesta");
        check::<VestaConfig, VestaParams, VestaBase, VestaScalar, PallasAffine>(count, vc_len);

        println!("Testing Helios");
        check::<HeliosConfig, HeliosParams, HeliosBase, HeliosScalar, SeleneAffine>(count, vc_len);

        println!("Testing Selene");
        check::<SeleneConfig, SeleneParams, SeleneBase, SeleneScalar, HeliosAffine>(count, vc_len);

        // wei25519 curve's base field is same as scalar field of Selene curve but not other way, so its not a cycle
        println!("Testing wei25519");
        check::<Wei25519Config, Wei25519Params, Wei25519Base, Wei25519Scalar, SeleneAffine>(
            count, vc_len,
        );
    }

    #[test]
    fn test_blinding_with_discrete_log_combined() {
        fn check<
            C: DivisorCurve<BaseField = B, ScalarField = S>,
            Params: DiscreteLogParameters,
            B: PrimeField,
            S: PrimeField,
            BP: AffineRepr<ScalarField = B>,
        >(
            count: usize,
            vc_len: usize,
        ) {
            let mut rng = StdRng::seed_from_u64(0);

            let curve = CurveSpec::<B> {
                a: C::COEFF_A,
                b: C::COEFF_B,
            };

            let pc_gens = PedersenGens::<BP>::default();
            let bp_gens = BulletproofGens::<BP>::new(512, 1);

            let generator = Projective::<C>::rand(&mut rng);

            let generator_table = GeneratorTable::<B, Params>::new::<C>(generator);

            // Collect all the data for all iterations
            let mut all_o_blind_claims = Vec::new();
            let mut all_o_tilde_points = Vec::new();
            let mut all_divisor_commitments = Vec::new();

            let mut all_o = Vec::new();
            let mut all_o_coords = Vec::new();
            for _ in 0..count {
                // Create O (the original point)
                let O = Projective::<C>::from(C::GENERATOR) * S::rand(&mut rng);
                all_o.push(O);
                let (O_x, O_y) = to_xy::<C>(O).unwrap();
                all_o_coords.push(O_x);
                all_o_coords.push(O_y);
            }

            let start = Instant::now();
            let transcript = MerlinTranscript::new(b"test");
            let mut prover = Prover::new(&pc_gens, transcript);

            // Commit to all at once
            let (comm_orig, all_O_vars) =
                prover.commit_vec(&all_o_coords, B::rand(&mut rng), &bp_gens);

            for i in 0..count {
                // Create scalar o and compute o_blind = o.generator
                let o = S::rand(&mut rng);
                let o_blind_point = generator * o;
                let (o_blind_x, o_blind_y) = to_xy::<C>(o_blind_point).unwrap();

                let O = &all_o[i];

                // Create O_tilde = O - o_blind
                let O_tilde_point = (*O) - o_blind_point;
                let (O_tilde_x, O_tilde_y) = to_xy::<C>(O_tilde_point).unwrap();

                all_o_tilde_points.push((O_tilde_x, O_tilde_y));

                let (comms, o_blind_claim) = {
                    let witness =
                        create_divisor_and_decomposition::<_, C, Params>(&generator_table, o)
                            .unwrap();
                    let (comms, _, o_blind_claim) =
                        commit_witness_chunks_prover::<_, _, _, Params>(
                            &mut rng,
                            &mut prover,
                            &witness,
                            vc_len,
                            &bp_gens,
                        )
                        .unwrap();

                    assert_eq!(o_blind_x, prover.eval(&o_blind_claim.point.0.into()));
                    assert_eq!(o_blind_y, prover.eval(&o_blind_claim.point.1.into()));

                    (comms, o_blind_claim)
                };

                all_divisor_commitments.push(comms);
                all_o_blind_claims.push(o_blind_claim);
            }

            let proving_time_00 = start.elapsed();

            for (i, o_blind_claim) in all_o_blind_claims.into_iter().enumerate() {
                let (O_x_var, O_y_var) = (all_O_vars[2 * i], all_O_vars[2 * i + 1]);
                let (O_tilde_x, O_tilde_y) = all_o_tilde_points[i];
                discrete_log_blinding(
                    &mut prover,
                    (O_x_var, O_y_var),
                    *o_blind_claim,
                    (O_tilde_x, O_tilde_y),
                    &curve,
                    &[&generator_table],
                )
                .unwrap();
            }

            let proving_time_0 = start.elapsed();
            let proof = prover.prove(&bp_gens).unwrap();
            let proving_time = start.elapsed();

            let total_proof_size = proof.compressed_size()
                + comm_orig.compressed_size()
                + all_divisor_commitments.compressed_size();

            let start = Instant::now();
            let transcript = MerlinTranscript::new(b"test");
            let mut verifier = Verifier::new(transcript);

            let mut all_o_blind_claims = Vec::new();

            let vars_orig = verifier.commit_vec(2 * count, comm_orig);

            for i in 0..count {
                let O_x_var = vars_orig[2 * i];
                let O_y_var = vars_orig[2 * i + 1];

                let o_blind_claim = commit_witness_chunks_verifier::<_, _, Params>(
                    &mut verifier,
                    &all_divisor_commitments[i],
                    vc_len,
                )
                .unwrap();
                all_o_blind_claims.push((o_blind_claim, O_x_var, O_y_var));
            }

            let verifying_time_00 = start.elapsed();

            for (i, (o_blind_claim, o_x_var, o_y_var)) in all_o_blind_claims.into_iter().enumerate()
            {
                let (o_tilde_x, o_tilde_y) = all_o_tilde_points[i];
                discrete_log_blinding(
                    &mut verifier,
                    (o_x_var, o_y_var),
                    *o_blind_claim,
                    (o_tilde_x, o_tilde_y),
                    &curve,
                    &[&generator_table],
                )
                .unwrap();
            }

            let verifying_time_0 = start.elapsed();
            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
            let verifying_time = start.elapsed();

            println!(
                "For {count} discrete log proofs, vec commitment size={vc_len}, total proof size = {total_proof_size}, \
        proving time: {:?}, verification time: {:?}. For non BP proof generation/verification proving time {:?}, verification time {:?}. \
        For commitments, proving time {:?}, verification time {:?}",
                proving_time,
                verifying_time,
                proving_time_0,
                verifying_time_0,
                proving_time_00,
                verifying_time_00
            );
        }

        let count = 4;
        let vc_len = 64;

        println!("Testing Pallas");
        check::<PallasConfig, PallasParams, PallasBase, PallasScalar, VestaAffine>(count, vc_len);

        println!("Testing Vesta");
        check::<VestaConfig, VestaParams, VestaBase, VestaScalar, PallasAffine>(count, vc_len);

        println!("Testing Helios");
        check::<HeliosConfig, HeliosParams, HeliosBase, HeliosScalar, SeleneAffine>(count, vc_len);

        println!("Testing Selene");
        check::<SeleneConfig, SeleneParams, SeleneBase, SeleneScalar, HeliosAffine>(count, vc_len);

        // wei25519 curve's base field is same as scalar field of Selene curve but not other way, so its not a cycle
        println!("Testing wei25519");
        check::<Wei25519Config, Wei25519Params, Wei25519Base, Wei25519Scalar, SeleneAffine>(
            count, vc_len,
        );
    }

    #[test]
    fn test_blinding_with_discrete_log_combined_reuse_challenge() {
        fn check<
            C: DivisorCurve<BaseField = B, ScalarField = S>,
            Params: DiscreteLogParameters,
            B: PrimeField,
            S: PrimeField,
            BP: AffineRepr<ScalarField = B>,
        >(
            count: usize,
            vc_len: usize,
        ) {
            let mut rng = StdRng::seed_from_u64(0);

            // Create curve spec: y^2 = x^3 + 5
            let curve = CurveSpec::<B> {
                a: C::COEFF_A,
                b: C::COEFF_B,
            };

            let pc_gens = PedersenGens::<BP>::default();
            let bp_gens = BulletproofGens::<BP>::new(512, 1);

            let generator = Projective::<C>::rand(&mut rng);
            let generator_table = GeneratorTable::<B, Params>::new::<C>(generator);

            // Collect all the data for all iterations
            let mut all_o_blind_claims = Vec::new();
            let mut all_o_tilde_points = Vec::new();
            let mut all_divisor_commitments = Vec::new();

            let mut all_o = Vec::new();
            let mut all_o_coords = Vec::new();
            for _ in 0..count {
                // Create O (the original point)
                let O = Projective::<C>::from(C::GENERATOR) * S::rand(&mut rng);
                all_o.push(O);
                let (O_x, O_y) = to_xy::<C>(O).unwrap();
                all_o_coords.push(O_x);
                all_o_coords.push(O_y);
            }

            let start = Instant::now();
            let transcript = MerlinTranscript::new(b"test");
            let mut prover = Prover::new(&pc_gens, transcript);

            // Commit to all at once
            let (comm_orig, all_O_vars) =
                prover.commit_vec(&all_o_coords, B::rand(&mut rng), &bp_gens);

            for i in 0..count {
                // Create scalar o and compute o_blind = o.generator
                let o = S::rand(&mut rng);
                let o_blind_point = generator * o;
                let (o_blind_x, o_blind_y) = to_xy::<C>(o_blind_point).unwrap();

                let O = &all_o[i];

                // Create O_tilde = O - o_blind
                let O_tilde_point = (*O) - o_blind_point;
                let (O_tilde_x, O_tilde_y) = to_xy::<C>(O_tilde_point).unwrap();

                all_o_tilde_points.push((O_tilde_x, O_tilde_y));

                let (comms, o_blind_claim) = {
                    let witness =
                        create_divisor_and_decomposition::<_, C, Params>(&generator_table, o)
                            .unwrap();
                    let (comms, _, o_blind_claim) =
                        commit_witness_chunks_prover::<_, _, _, Params>(
                            &mut rng,
                            &mut prover,
                            &witness,
                            vc_len,
                            &bp_gens,
                        )
                        .unwrap();

                    assert_eq!(o_blind_x, prover.eval(&o_blind_claim.point.0.into()));
                    assert_eq!(o_blind_y, prover.eval(&o_blind_claim.point.1.into()));

                    (comms, o_blind_claim)
                };

                all_divisor_commitments.push(comms);
                all_o_blind_claims.push(o_blind_claim);
            }

            let proving_time_00 = start.elapsed();

            let (challenge, challenged_generators) =
                discrete_log_challenge(&mut prover, &curve, &[&generator_table]).unwrap();
            let mut challenged_generators = challenged_generators.into_iter();
            let challenged_T = challenged_generators.next().unwrap();

            for (i, o_blind_claim) in all_o_blind_claims.into_iter().enumerate() {
                let (O_x_var, O_y_var) = (all_O_vars[2 * i], all_O_vars[2 * i + 1]);
                let (O_tilde_x, O_tilde_y) = all_o_tilde_points[i];
                discrete_log_blinding_given_challenge(
                    &mut prover,
                    (O_x_var, O_y_var),
                    *o_blind_claim,
                    (O_tilde_x, O_tilde_y),
                    &curve,
                    &challenge,
                    &challenged_T,
                );
            }

            let proving_time_0 = start.elapsed();
            let proof = prover.prove(&bp_gens).unwrap();
            let proving_time = start.elapsed();

            let total_proof_size = proof.compressed_size()
                + comm_orig.compressed_size()
                + all_divisor_commitments.compressed_size();

            let start = Instant::now();
            let transcript = MerlinTranscript::new(b"test");
            let mut verifier = Verifier::new(transcript);

            let mut all_o_blind_claims = Vec::new();

            let vars_orig = verifier.commit_vec(2 * count, comm_orig);

            for i in 0..count {
                let O_x_var = vars_orig[2 * i];
                let O_y_var = vars_orig[2 * i + 1];

                let o_blind_claim = commit_witness_chunks_verifier::<_, _, Params>(
                    &mut verifier,
                    &all_divisor_commitments[i],
                    vc_len,
                )
                .unwrap();
                all_o_blind_claims.push((o_blind_claim, O_x_var, O_y_var));
            }

            let verifying_time_00 = start.elapsed();

            let (challenge, challenged_generators) =
                discrete_log_challenge(&mut verifier, &curve, &[&generator_table]).unwrap();
            let mut challenged_generators = challenged_generators.into_iter();
            let challenged_T = challenged_generators.next().unwrap();

            for (i, (o_blind_claim, o_x_var, o_y_var)) in all_o_blind_claims.into_iter().enumerate()
            {
                let (o_tilde_x, o_tilde_y) = all_o_tilde_points[i];
                discrete_log_blinding_given_challenge(
                    &mut verifier,
                    (o_x_var, o_y_var),
                    *o_blind_claim,
                    (o_tilde_x, o_tilde_y),
                    &curve,
                    &challenge,
                    &challenged_T,
                );
            }

            let verifying_time_0 = start.elapsed();
            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
            let verifying_time = start.elapsed();

            println!(
                "For {count} discrete log proofs, vec commitment size={vc_len}, total proof size = {total_proof_size}, \
        proving time: {:?}, verification time: {:?}. For non BP proof generation/verification proving time {:?}, verification time {:?}. \
        For commitments, proving time {:?}, verification time {:?}",
                proving_time,
                verifying_time,
                proving_time_0,
                verifying_time_0,
                proving_time_00,
                verifying_time_00
            );
        }

        let count = 10;
        let vc_len = 256;

        println!("Testing Pallas");
        check::<PallasConfig, PallasParams, PallasBase, PallasScalar, VestaAffine>(count, vc_len);

        println!("Testing Vesta");
        check::<VestaConfig, VestaParams, VestaBase, VestaScalar, PallasAffine>(count, vc_len);

        println!("Testing Helios");
        check::<HeliosConfig, HeliosParams, HeliosBase, HeliosScalar, SeleneAffine>(count, vc_len);

        println!("Testing Selene");
        check::<SeleneConfig, SeleneParams, SeleneBase, SeleneScalar, HeliosAffine>(count, vc_len);
    }

    #[test]
    fn test_shared_dlog() {
        fn check<
            C: DivisorCurve<BaseField = B, ScalarField = S>,
            Params: DiscreteLogParameters,
            B: PrimeField,
            S: PrimeField,
            BP: AffineRepr<ScalarField = B>,
        >(
            n: usize,
            vc_len: usize,
        ) {
            let mut rng = StdRng::seed_from_u64(42);

            let curve = CurveSpec::<B> {
                a: C::COEFF_A,
                b: C::COEFF_B,
            };
            let pc_gens = PedersenGens::<BP>::default();
            let bp_gens = BulletproofGens::<BP>::new(512, 1);

            let mut all_o = Vec::with_capacity(n);
            let mut all_o_coords = Vec::with_capacity(2 * n);
            for _ in 0..n {
                let O = Projective::<C>::from(C::GENERATOR) * S::rand(&mut rng);
                let (O_x, O_y) = to_xy::<C>(O).unwrap();
                all_o_coords.push(O_x);
                all_o_coords.push(O_y);
                all_o.push(O);
            }

            let mut generators = Vec::with_capacity(n);
            let mut gen_tables = Vec::with_capacity(n);
            for _ in 0..n {
                let generator = Projective::<C>::rand(&mut rng);
                generators.push(generator);
                gen_tables.push(GeneratorTable::<B, Params>::new::<C>(generator));
            }
            let gen_table_refs: Vec<&GeneratorTable<B, Params>> = gen_tables.iter().collect();

            let d = S::rand(&mut rng);

            let mut all_o_tilde = Vec::with_capacity(n);
            for i in 0..n {
                let blind_point = generators[i] * d;
                let O_tilde = all_o[i] - blind_point;
                let (O_tilde_x, O_tilde_y) = to_xy::<C>(O_tilde).unwrap();
                all_o_tilde.push((O_tilde_x, O_tilde_y));
            }

            let start = Instant::now();
            let transcript = MerlinTranscript::new(b"shared-dlog");
            let mut prover = Prover::new(&pc_gens, transcript);

            let (comm_orig, all_O_vars) =
                prover.commit_vec(&all_o_coords, B::rand(&mut rng), &bp_gens);

            let witness =
                create_divisor_and_decomposition_multi_gen::<_, C, Params>(&gen_table_refs, d)
                    .unwrap();
            let (comms, _, blinds) = commit_witness_chunks_prover_multi_gen::<_, _, _, Params>(
                &mut rng,
                &mut prover,
                &witness,
                vc_len,
                &bp_gens,
            )
            .unwrap();

            let commit_time = start.elapsed();

            let original_point_vars: Vec<(Variable<B>, Variable<B>)> = (0..n)
                .map(|i| (all_O_vars[2 * i], all_O_vars[2 * i + 1]))
                .collect();

            discrete_log_blinding_multi_gen(
                &mut prover,
                &original_point_vars,
                blinds,
                &all_o_tilde,
                &curve,
                &gen_table_refs,
            )
            .unwrap();

            let constrain_time = start.elapsed();
            let proof = prover.prove(&bp_gens).unwrap();
            let prove_time = start.elapsed();

            let proof_size =
                proof.compressed_size() + comm_orig.compressed_size() + comms.compressed_size();

            let start_v = Instant::now();
            let transcript = MerlinTranscript::new(b"shared-dlog");
            let mut verifier = Verifier::new(transcript);

            let vars_orig = verifier.commit_vec(2 * n, comm_orig);
            let blinds = commit_witness_chunks_verifier_multi_gen::<_, _, Params>(
                &mut verifier,
                &comms,
                vc_len,
                n,
            )
            .unwrap();
            let commit_time_v = start_v.elapsed();

            let original_point_vars: Vec<(Variable<B>, Variable<B>)> = (0..n)
                .map(|i| (vars_orig[2 * i], vars_orig[2 * i + 1]))
                .collect();

            discrete_log_blinding_multi_gen(
                &mut verifier,
                &original_point_vars,
                blinds,
                &all_o_tilde,
                &curve,
                &gen_table_refs,
            )
            .unwrap();

            let constrain_time_v = start_v.elapsed();
            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
            let verify_time = start_v.elapsed();

            println!("Shared dlog for n={n} blindings, vc_len={vc_len}");
            println!(
                "  proof size: {proof_size} bytes, prove: {:?} (commit {:?}, constrain {:?}), verify: {:?} (commit {:?}, constrain {:?})",
                prove_time,
                commit_time,
                constrain_time,
                verify_time,
                commit_time_v,
                constrain_time_v,
            );
        }

        let count = 4;
        let vc_len = 64;

        println!("Testing Pallas");
        check::<PallasConfig, PallasParams, PallasBase, PallasScalar, VestaAffine>(count, vc_len);

        println!("Testing Vesta");
        check::<VestaConfig, VestaParams, VestaBase, VestaScalar, PallasAffine>(count, vc_len);

        println!("Testing Helios");
        check::<HeliosConfig, HeliosParams, HeliosBase, HeliosScalar, SeleneAffine>(count, vc_len);

        println!("Testing Selene");
        check::<SeleneConfig, SeleneParams, SeleneBase, SeleneScalar, HeliosAffine>(count, vc_len);

        // wei25519 curve's base field is same as scalar field of Selene curve but not other way, so its not a cycle
        println!("Testing wei25519");
        check::<Wei25519Config, Wei25519Params, Wei25519Base, Wei25519Scalar, SeleneAffine>(
            count, vc_len,
        );
    }

    #[test]
    fn test_mixed_blinding_and_dlog() {
        fn check<
            C: DivisorCurve<BaseField = B, ScalarField = S>,
            Params: DiscreteLogParameters,
            B: PrimeField,
            S: PrimeField,
            BP: AffineRepr<ScalarField = B>,
        >(
            count: usize,
            vc_len: usize,
        ) {
            let mut rng = StdRng::seed_from_u64(0);

            let curve = CurveSpec::<B> {
                a: C::COEFF_A,
                b: C::COEFF_B,
            };

            let pc_gens = PedersenGens::<BP>::default();
            let bp_gens = BulletproofGens::<BP>::new(512, 1);

            let generator1 = Projective::<C>::rand(&mut rng);
            let generator_table1 = GeneratorTable::<B, Params>::new::<C>(generator1);

            let generator2 = Projective::<C>::rand(&mut rng);
            let generator_table2 = GeneratorTable::<B, Params>::new::<C>(generator2);

            let mut proving_times = Vec::with_capacity(count);
            let mut verifying_times = Vec::with_capacity(count);
            let mut proof_size = 0;

            for _ in 0..count {
                // Create scalar b
                let b = S::rand(&mut rng);

                // original point P which is hidden
                let P = Projective::<C>::rand(&mut rng);
                let (p_x, p_y) = to_xy::<C>(P).unwrap();

                // R = P + gen_1 * b, R is revealed
                let gen1_b = generator1 * b;
                let R = P + gen1_b;
                let (r_x, r_y) = to_xy::<C>(R).unwrap();

                // S = gen_2 * b, which is revealed
                let S = generator2 * b;
                let (minus_s_x, minus_s_y) = to_xy::<C>(-(S)).unwrap();

                let start = Instant::now();

                let transcript = MerlinTranscript::new(b"test");
                let mut prover = Prover::new(&pc_gens, transcript);

                let (comm_orig, mut vars_orig) =
                    prover.commit_vec(&[p_x, p_y], B::rand(&mut rng), &bp_gens);
                let p_y_var = vars_orig.pop().unwrap();
                let p_x_var = vars_orig.pop().unwrap();

                // Use multi_gen with 2 generators
                let gen_tables = [&generator_table1, &generator_table2];
                let witness =
                    create_divisor_and_decomposition_multi_gen::<_, C, Params>(&gen_tables, -b)
                        .unwrap();

                let (comms, _, points_with_dlog) =
                    commit_witness_chunks_prover_multi_gen::<_, _, _, Params>(
                        &mut rng,
                        &mut prover,
                        &witness,
                        vc_len,
                        &bp_gens,
                    )
                    .unwrap();

                let result_minus_s = discrete_log_blinding_and_dlog(
                    &mut prover,
                    (p_x_var, p_y_var), // P
                    points_with_dlog,
                    (r_x, r_y), // R
                    &curve,
                    &[&generator_table1, &generator_table2],
                )
                .unwrap();

                assert_eq!(minus_s_x, prover.eval(&result_minus_s.x.into()));
                assert_eq!(minus_s_y, prover.eval(&result_minus_s.y.into()));

                let proof = prover.prove(&bp_gens).unwrap();
                proving_times.push(start.elapsed());

                if proof_size == 0 {
                    proof_size = proof.compressed_size()
                        + comms.compressed_size()
                        + comm_orig.compressed_size();
                }

                let start = Instant::now();

                let transcript = MerlinTranscript::new(b"test");
                let mut verifier = Verifier::new(transcript);

                let mut vars_p = verifier.commit_vec(2, comm_orig);
                let p_y_var = vars_p.pop().unwrap();
                let p_x_var = vars_p.pop().unwrap();

                let points_with_dlog = commit_witness_chunks_verifier_multi_gen::<_, _, Params>(
                    &mut verifier,
                    &comms,
                    vc_len,
                    2,
                )
                .unwrap();

                discrete_log_blinding_and_dlog(
                    &mut verifier,
                    (p_x_var, p_y_var), // P
                    points_with_dlog,
                    (r_x, r_y), // R
                    &curve,
                    &[&generator_table1, &generator_table2],
                )
                .unwrap();

                verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
                verifying_times.push(start.elapsed());
            }

            proving_times.sort();
            verifying_times.sort();
            let median_prove = proving_times[count / 2];
            let median_verify = verifying_times[count / 2];

            println!(
                "For {count} iterations, and vec commitment size={vc_len}, proof size = {proof_size}, \
        median proving time: {:?}, median verification time: {:?}",
                median_prove, median_verify
            );
        }

        let count = 4;
        let vc_len = 32;

        println!("Testing Pallas");
        check::<PallasConfig, PallasParams, PallasBase, PallasScalar, VestaAffine>(count, vc_len);

        println!("Testing Vesta");
        check::<VestaConfig, VestaParams, VestaBase, VestaScalar, PallasAffine>(count, vc_len);

        println!("Testing Helios");
        check::<HeliosConfig, HeliosParams, HeliosBase, HeliosScalar, SeleneAffine>(count, vc_len);

        println!("Testing Selene");
        check::<SeleneConfig, SeleneParams, SeleneBase, SeleneScalar, HeliosAffine>(count, vc_len);

        // wei25519 curve's base field is same as scalar field of Selene curve but not other way, so its not a cycle
        println!("Testing wei25519");
        check::<Wei25519Config, Wei25519Params, Wei25519Base, Wei25519Scalar, SeleneAffine>(
            count, vc_len,
        );
    }
}
