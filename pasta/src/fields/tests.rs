use crate::*;

use ark_algebra_test_templates::fields::{field_test, primefield_test, sqrt_field_test};
use ark_std::rand::Rng;
use ark_std::test_rng;

#[test]
fn test_fp() {
    let mut rng = test_rng();
    let a: Fp = rng.gen();
    let b: Fp = rng.gen();
    field_test(a, b);
    sqrt_field_test(a);
    primefield_test::<Fp>();
}

#[test]
fn test_fq() {
    let mut rng = test_rng();
    let a: Fq = rng.gen();
    let b: Fq = rng.gen();
    field_test(a, b);
    sqrt_field_test(a);
    primefield_test::<Fq>();
}
