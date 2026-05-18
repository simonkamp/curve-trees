use crate::util::DirectGenerator;
use crate::{DivisorCurve, DivisorPoly, ScalarDecomposition, new_divisor};
use ark_ec::short_weierstrass::Projective;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, Field, PrimeField, Zero};
use ark_std::UniformRand;
use core::borrow::Borrow;
use rand::rngs::StdRng;
use rand_core::{CryptoRngCore, SeedableRng};
use std::time::Instant;

/// Convert a projective point to (x, y), returning None for the identity.
fn to_xy<C: DivisorCurve>(p: Projective<C>) -> Option<(C::BaseField, C::BaseField)> {
    let aff = p.into_affine();
    aff.xy()
}

/// y^2 - x^3 - A x - B evaluated at a point (checks that the point is on the curve).
///
/// Section 2 of Eagen's security proofs define this modulus.
fn on_curve<C: DivisorCurve>(x: C::BaseField, y: C::BaseField) -> C::BaseField {
    y * y - x * x * x - C::COEFF_A * x - C::COEFF_B
}

/// Calculate the slope and intercept between two points.
///
/// This function panics when `a @ infinity`, `b @ infinity`, `a == b`, or when `a == -b`.
pub(crate) fn slope_intercept<C: DivisorCurve>(
    a: Projective<C>,
    b: Projective<C>,
) -> (C::BaseField, C::BaseField) {
    // slope = (by - ay) / (bx - ax)
    let (ax, ay) = to_xy::<C>(a).unwrap();
    debug_assert_eq!(on_curve::<C>(ax, ay), C::BaseField::zero());
    let (bx, by) = to_xy::<C>(b).unwrap();
    debug_assert_eq!(on_curve::<C>(bx, by), C::BaseField::zero());
    let slope = (by - ay) * Option::<C::BaseField>::from((bx - ax).inverse()).unwrap();

    // y = slope.x + intercept => intercept = y - slope.x
    let intercept = by - (slope * bx);

    // intercept calculated from a's coords is same
    debug_assert!((ay - (slope * ax) - intercept).is_zero());
    (slope, intercept)
}

// Equation 4 in the security proofs
fn check_divisor<C: DivisorCurve, R: CryptoRngCore>(rng: &mut R, points: Vec<Projective<C>>) {
    let precomputation = C::interpolator_for_scalar_mul();

    // Create the divisor
    let divisor = new_divisor::<C>(&points, precomputation.borrow()).unwrap();
    let eval = |c: Projective<C>| {
        let (x, y) = to_xy::<C>(c).unwrap();
        divisor.eval(x, y)
    };

    // Decide challenges
    let c0 = Projective::<C>::rand(rng);
    let mut c1 = Projective::<C>::rand(rng); // Different point
    while c1 == c0 {
        c1 = Projective::<C>::rand(rng);
    }
    let c2 = -(c0 + c1);
    let (slope, intercept) = slope_intercept::<C>(c0, c1);

    let mut rhs = C::BaseField::ONE;
    for point in points {
        let (x, y) = to_xy::<C>(point).unwrap();
        rhs *= intercept - (y - (slope * x));
    }
    assert_eq!(eval(c0) * eval(c1) * eval(c2), rhs);
}

fn test_divisor<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let precomputation = C::interpolator_for_scalar_mul();
    let num_bits = u64::from(C::ScalarField::MODULUS_BIT_SIZE);

    let mut new_divisor_times = Vec::new();
    let mut check_divisor_times = Vec::new();
    let mut total_times = Vec::new();

    for i in 1..=(num_bits as usize + 1) {
        let start_total = Instant::now();

        // Select points
        let mut points = vec![];
        for _ in 0..i {
            points.push(Projective::<C>::rand(&mut rng));
        }
        // Make sure points sum to identity
        let sum = points.iter().copied().reduce(|a, b| a + b).unwrap();
        points.push(-sum);

        let start_new_divisor = Instant::now();
        // Create the divisor
        let divisor = new_divisor::<C>(&points, precomputation.borrow()).unwrap();
        new_divisor_times.push(start_new_divisor.elapsed());

        // Perform the original check
        let start_check = Instant::now();
        check_divisor(&mut rng, points.clone());
        check_divisor_times.push(start_check.elapsed());

        total_times.push(start_total.elapsed());

        assert!(C::ScalarField::MODULUS_BIT_SIZE < 256);
        let x_len = divisor.x_coefficients.len().saturating_sub(1);
        assert!(x_len <= 127, "x-len={x_len}");

        // Decide challenges
        let c0 = Projective::<C>::rand(&mut rng);
        let mut c1 = Projective::<C>::rand(&mut rng); // Different point
        while c1 == c0 {
            c1 = Projective::<C>::rand(&mut rng);
        }
        // c2 = -(c0 + c1)
        let c2 = -(c0 + c1);
        let (slope, intercept) = slope_intercept::<C>(c0, c1);

        // Logarithmic derivative check
        {
            let dx_over_dz = {
                let dx = DivisorPoly {
                    y_coefficient: C::BaseField::zero(),
                    yx_coefficients: vec![],
                    x_coefficients: vec![C::BaseField::zero(), C::BaseField::from(3u64)],
                    zero_coefficient: C::COEFF_A,
                };

                let dy = DivisorPoly {
                    y_coefficient: C::BaseField::from(2u64),
                    yx_coefficients: vec![],
                    x_coefficients: vec![],
                    zero_coefficient: C::BaseField::zero(),
                };

                let dz = (dy.clone() * -slope) + &dx;

                // We want dx/dz, and dz/dx is equal to dy/dx - slope
                // Sagemath claims this, dy / dz, is the proper inverse
                (dy, dz)
            };

            {
                let sanity_eval = |c: Projective<C>| {
                    let (x, y) = to_xy::<C>(c).unwrap();
                    dx_over_dz.0.eval(x, y) * dx_over_dz.1.eval(x, y).inverse().unwrap()
                };
                let sanity = sanity_eval(c0) + sanity_eval(c1) + sanity_eval(c2);
                // This verifies the dx/dz polynomial is correct
                assert_eq!(sanity, C::BaseField::zero());
            }

            // Logarithmic derivative check
            let test = |divisor: DivisorPoly<_>| {
                let (dx, dy) = divisor.differentiate();

                let lhs = |c: Projective<C>| {
                    let (x, y) = to_xy::<C>(c).unwrap();

                    let n_0 = (C::BaseField::from(3u64) * (x * x)) + C::COEFF_A;
                    let d_0 = (C::BaseField::from(2u64) * y).inverse().unwrap();
                    let p_0_n_0 = n_0 * d_0;

                    let n_1 = dy.eval(x, y);
                    let first = p_0_n_0 * n_1;

                    let second = dx.eval(x, y);

                    let d_1 = divisor.eval(x, y);

                    let fraction_1_n = first + second;
                    let fraction_1_d = d_1;

                    let fraction_2_n = dx_over_dz.0.eval(x, y);
                    let fraction_2_d = dx_over_dz.1.eval(x, y);

                    fraction_1_n * fraction_2_n * (fraction_1_d * fraction_2_d).inverse().unwrap()
                };
                let lhs = lhs(c0) + lhs(c1) + lhs(c2);

                let mut rhs = C::BaseField::zero();
                for point in &points {
                    let (x, y) = to_xy::<C>(*point).unwrap();
                    rhs += (intercept - (y - (slope * x))).inverse().unwrap();
                }

                assert_eq!(lhs, rhs);
            };
            // Test the divisor
            test(divisor.clone());
        }
    }

    // Calculate medians
    new_divisor_times.sort();
    check_divisor_times.sort();
    total_times.sort();

    let new_divisor_median = new_divisor_times[new_divisor_times.len() / 2];
    let check_divisor_median = check_divisor_times[check_divisor_times.len() / 2];
    let total_median = total_times[total_times.len() / 2];

    println!(
        "test_divisor: new_divisor median {:?} ({} iterations), check_divisor median {:?} ({} iterations), total median {:?} ({} iterations)",
        new_divisor_median,
        new_divisor_times.len(),
        check_divisor_median,
        check_divisor_times.len(),
        total_median,
        total_times.len()
    );
}

fn test_same_point<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let p = Projective::<C>::rand(&mut rng);
    let mut points = vec![p, p];
    let sum = p + p;
    points.push(-sum);
    check_divisor(&mut rng, points);

    let p = C::GENERATOR.into_group();
    let mut points = vec![p, p];
    let sum = p + p;
    points.push(-sum);
    check_divisor(&mut rng, points);
}

fn test_subset_sum_to_infinity<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let mut check_divisor_times = Vec::new();

    // This executes the first pass to end up with [0, 0] for further reductions
    {
        let p = Projective::<C>::rand(&mut rng);
        let mut points = vec![p, -p];

        let next = Projective::<C>::rand(&mut rng);
        points.push(next);
        points.push(-next);

        let start = Instant::now();
        check_divisor(&mut rng, points);
        check_divisor_times.push(start.elapsed());
    }

    // This executes the first pass to end up with [0, X, -X, 0]
    {
        let p = Projective::<C>::rand(&mut rng);
        let mut points = vec![p, -p];

        let x_1 = Projective::<C>::rand(&mut rng);
        let x_2 = Projective::<C>::rand(&mut rng);
        points.push(x_1);
        points.push(x_2);

        points.push(-x_1);
        points.push(-x_2);

        let next = Projective::<C>::rand(&mut rng);
        points.push(next);
        points.push(-next);

        let start = Instant::now();
        check_divisor(&mut rng, points);
        check_divisor_times.push(start.elapsed());
    }

    // Five points summing to infinity
    {
        let mut points = vec![
            Projective::<C>::rand(&mut rng),
            Projective::<C>::rand(&mut rng),
            Projective::<C>::rand(&mut rng),
            Projective::<C>::rand(&mut rng),
        ];
        let sum = points.iter().copied().reduce(|a, b| a + b).unwrap();
        points.push(-sum);
        check_divisor(&mut rng, points);
    }

    // Calculate median
    check_divisor_times.sort();
    let median = check_divisor_times[check_divisor_times.len() / 2];

    println!(
        "test_subset_sum_to_infinity: median time {:?} ({} iterations)",
        median,
        check_divisor_times.len()
    );
}

fn decomposition_correctness<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let count = 100;

    let mut decomposition_times = Vec::new();

    // Test random scalars and specific edge cases like ONE
    let mut scalars = Vec::new();
    for _ in 0..count {
        scalars.push(C::ScalarField::rand(&mut rng));
    }
    // Add ONE (the multiplicative identity)
    scalars.push(C::ScalarField::ONE);

    assert!(ScalarDecomposition::<C::ScalarField>::new(C::ScalarField::ZERO).is_err());

    for scalar in scalars {
        if scalar == C::ScalarField::ZERO {
            continue;
        }

        let start = Instant::now();
        let decomposition = ScalarDecomposition::<C::ScalarField>::new(scalar).unwrap();
        decomposition_times.push(start.elapsed());

        // 1. Verify sum of coefficients is NUM_BITS
        let sum: u64 = decomposition.decomposition().iter().sum();
        assert_eq!(sum, u64::from(C::ScalarField::MODULUS_BIT_SIZE));

        // 2. Verify reconstruction
        let mut reconstructed = C::ScalarField::ZERO;
        let mut base = C::ScalarField::ONE;
        for &coeff in decomposition.decomposition() {
            reconstructed += base * C::ScalarField::from(coeff);
            base = base.double();
        }
        assert_eq!(reconstructed, scalar);
    }

    // Calculate median
    decomposition_times.sort();
    let median = decomposition_times[decomposition_times.len() / 2];

    println!(
        "decomposition_correctness: ScalarDecomposition::new median time {:?} ({} iterations)",
        median,
        decomposition_times.len()
    );
}

fn scalar_mul_divisor_correctness<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let count = 20;

    let mut decomposition_times = Vec::new();
    let mut scalar_mul_times = Vec::new();

    for _ in 0..count {
        let scalar = C::ScalarField::rand(&mut rng);
        if scalar == C::ScalarField::ZERO {
            return;
        }

        let decomposition_start = Instant::now();
        let decomposition = ScalarDecomposition::<C::ScalarField>::new(scalar).unwrap();
        decomposition_times.push(decomposition_start.elapsed());

        let generator = Projective::<C>::rand(&mut rng);

        let mul_start = Instant::now();
        let poly = decomposition
            .scalar_mul_divisor(DirectGenerator::from(generator))
            .unwrap();
        scalar_mul_times.push(mul_start.elapsed());

        // 1. Verify it vanishes at -(s * G)
        let neg_s_g = -(generator * scalar);
        let (x, y) = to_xy::<C>(neg_s_g).unwrap();
        assert!(poly.eval(x, y).is_zero());

        // 2. Verify it vanishes at 2^i * G for each coefficient count
        let mut p = generator;
        for &coeff in decomposition.decomposition() {
            if coeff > 0 {
                let (x, y) = to_xy::<C>(p).unwrap();
                assert!(poly.eval(x, y).is_zero());
            }
            p = p.double();
        }
    }

    // Calculate medians
    decomposition_times.sort();
    scalar_mul_times.sort();

    let decomposition_median = decomposition_times[decomposition_times.len() / 2];
    let scalar_mul_median = scalar_mul_times[scalar_mul_times.len() / 2];

    println!(
        "scalar_mul_divisor_correctness: ScalarDecomposition::new median {:?} ({} iterations), scalar_mul_divisor median {:?} ({} iterations)",
        decomposition_median,
        decomposition_times.len(),
        scalar_mul_median,
        scalar_mul_times.len()
    );
}

/*#[cfg(feature = "ed25519")]
#[test]
fn test_divisor_ed25519() {
    use ark_ed25519::EdwardsProjective;
    use ark_std::UniformRand;
    use rand_core::OsRng;

    // Since we're implementing Wei25519 ourselves, check the isomorphism works as expected
    {
        let incomplete_add = |p1: EdwardsProjective, p2: EdwardsProjective| {
            let (x1, y1) = EdwardsProjective::to_xy(p1).unwrap();
            let (x2, y2) = EdwardsProjective::to_xy(p2).unwrap();

            // mmadd-1998-cmo
            let u = y2 - y1;
            let uu = u * u;
            let v = x2 - x1;
            let vv = v * v;
            let vvv = v * vv;
            let R = vv * x1;
            let A = uu - vvv - R.double();
            let x3 = v * A;
            let y3 = (u * (R - A)) - (vvv * y1);
            let z3 = vvv;

            // Normalize from XYZ to XY
            let z3_inv = z3.inverse().unwrap();
            let x3 = x3 * z3_inv;
            let y3 = y3 * z3_inv;

            // Edwards addition -> Wei25519 coordinates should be equivalent to Wei25519 addition
            assert_eq!(EdwardsProjective::to_xy(p1 + p2).unwrap(), (x3, y3));
        };

        for _ in 0..256 {
            incomplete_add(
                EdwardsProjective::rand(&mut OsRng),
                EdwardsProjective::rand(&mut OsRng),
            );
        }
    }

    test_same_point::<EdwardsProjective>();
    test_subset_sum_to_infinity::<EdwardsProjective>();
    test_divisor::<EdwardsProjective>();
}*/

fn run_divisor_tests<C: DivisorCurve>() {
    test_same_point::<C>();
    test_subset_sum_to_infinity::<C>();
    test_divisor::<C>();
    decomposition_correctness::<C>();
    scalar_mul_divisor_correctness::<C>();
}

#[test]
fn test_divisor_pallas() {
    run_divisor_tests::<ark_pallas::PallasConfig>();
}

#[test]
fn test_divisor_vesta() {
    run_divisor_tests::<ark_vesta::VestaConfig>();
}

#[test]
fn test_divisor_helios() {
    run_divisor_tests::<ark_helios::HeliosConfig>();
}

#[test]
fn test_divisor_selene() {
    run_divisor_tests::<ark_selene::SeleneConfig>();
}

#[test]
fn test_divisor_wei25519() {
    run_divisor_tests::<ark_wei25519::Wei25519Config>();
}
