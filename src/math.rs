use num::{BigInt,BigUint,Integer,One,Signed,Zero};
use num::bigint::Sign;
use std::ops::Neg;

// FIXME: This needs to be validated.
pub fn divmod(y: &BigInt, x: &BigInt, m: &BigUint) -> BigInt
{
    let sm = BigInt::from_biguint(Sign::Plus, m.clone());
    let xmod = x.mod_floor(&sm);
    assert!(xmod.is_positive());
    let uxmod = xmod.to_biguint().unwrap();
    let i = modinv(&uxmod, &m);
    let si = BigInt::from(i);
    let yi = y * &si;
    yi.mod_floor(&sm)
}

// fast modular inverse
pub fn modinv(e: &BigUint, phi: &BigUint) -> BigUint {
    let (_, mut x, _) = extended_euclidean(&e, &phi);
    let int_phi = BigInt::from_biguint(Sign::Plus, phi.clone());
    while x.is_negative() {
        x = x + &int_phi;
    }
    x.to_biguint().unwrap()
}

fn extended_euclidean(a: &BigUint, b: &BigUint) -> (BigInt, BigInt, BigInt) {
    let pos_int_a = BigInt::from_biguint(Sign::Plus, a.clone());
    let pos_int_b = BigInt::from_biguint(Sign::Plus, b.clone());
    let (d, x, y) = egcd(pos_int_a, pos_int_b);

    if d.is_negative() {
        (d.neg(), x.neg(), y.neg())
    } else {
        (d, x, y)
    }
}

fn egcd(a: BigInt, b: BigInt) -> (BigInt, BigInt, BigInt) {
    let mut s: BigInt = Zero::zero();
    let mut old_s     = One::one();
    let mut t: BigInt = One::one();
    let mut old_t     = Zero::zero();
    let mut r         = b.clone();
    let mut old_r     = a.clone();

    while !r.is_zero() {
        let quotient = old_r.clone() / r.clone();

        let prov_r = r.clone();
        let prov_s = s.clone();
        let prov_t = t.clone();

        r = old_r - (r * &quotient);
        s = old_s - (s * &quotient);
        t = old_t - (t * &quotient);

        old_r = prov_r;
        old_s = prov_s;
        old_t = prov_t;
    }

    (old_r, old_s, old_t)
}


