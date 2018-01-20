//! A simple DSA library.
//!
//! The library performs all the standard bits and pieces that you'd expect
//! from a DSA library, and does so using only Rust. It's a bit slow, but
//! it works. You probably shouldn't be using DSA, anyways, so consider this
//! the price you pay.
//!
//! Key generation is supported, because it's a lot easier to do testing that
//! way. But, again, hopefully you're only using this in legacy systems with
//! existing keys, and won't need that capability.
extern crate digest;
extern crate hmac;
extern crate num;
#[cfg(test)]
#[macro_use]
extern crate quickcheck;
extern crate rand;
extern crate sha1;
extern crate sha2;
extern crate simple_asn1;

mod rfc6979;

use digest::{BlockInput,FixedOutput,Input};
use digest::generic_array::ArrayLength;
use hmac::{Hmac,Mac};
use num::{BigInt,BigUint,Integer,One,Signed,Zero};
use num::bigint::Sign;
use num::cast::FromPrimitive;
use rand::{Rng,OsRng};
use rfc6979::{KIterator,bits2int};
use sha2::Sha256;
use simple_asn1::{ASN1Block,FromASN1,ToASN1,ASN1DecodeErr,ASN1EncodeErr,ASN1Class};
use std::clone::Clone;
use std::cmp::min;
use std::io;
use std::ops::{Add,Div,Neg,Sub};

#[derive(Clone,Copy,Debug,PartialEq)]
pub enum DSAParameterSize { L1024N160, L2048N224, L2048N256, L3072N256 }

#[derive(Debug)]
pub enum DSAError {
    ASN1DecodeErr(ASN1DecodeErr),
    InvalidParamSize
}

impl From<ASN1DecodeErr> for DSAError {
    fn from(e: ASN1DecodeErr) -> DSAError {
        DSAError::ASN1DecodeErr(e)
    }
}

fn n_bits(ps: DSAParameterSize) -> usize {
    match ps {
        DSAParameterSize::L1024N160 => 160,
        DSAParameterSize::L2048N224 => 224,
        DSAParameterSize::L2048N256 => 256,
        DSAParameterSize::L3072N256 => 256,
    }
}

fn l_bits(ps: DSAParameterSize) -> usize {
    match ps {
        DSAParameterSize::L1024N160 => 1024,
        DSAParameterSize::L2048N224 => 2048,
        DSAParameterSize::L2048N256 => 2048,
        DSAParameterSize::L3072N256 => 3072,
    }
}

#[derive(Debug)]
pub enum DSAGenError {
    RngFailure(io::Error),
    InvalidSeedLength, InvalidPrimeLength, TooManyGenAttempts
}

impl From<io::Error> for DSAGenError {
    fn from(e: io::Error) -> DSAGenError {
        DSAGenError::RngFailure(e)
    }
}

/// A set of DSA parameters, which are shared across both the public and private
/// keys.
#[derive(Clone,Debug,PartialEq)]
pub struct DSAParameters {
    size: DSAParameterSize,
    pub p: BigUint,
    pub g: BigUint,
    pub q: BigUint,
}

impl DSAParameters {
    /// Generate a new set of DSA parameters, from a certificate file or some
    /// other source. This will try to find an appropriate size based on the
    /// size of the values provided, but will fail (returning
    /// `DSAError::InvalidParamSize`) if it can't find a reasonable one.
    pub fn new(p: BigUint, g: BigUint, q: BigUint)
        -> Result<DSAParameters,DSAError>
    {
        let l = ((p.bits() + 255) / 256) * 256;
        let n = ((q.bits() + 15) / 16) * 16;
        let size  = match (l, n) {
                        (1024, 160) => DSAParameterSize::L1024N160,
                        (2048, 224) => DSAParameterSize::L2048N224,
                        (2048, 256) => DSAParameterSize::L2048N256,
                        (3072, 256) => DSAParameterSize::L3072N256,
                        _           => return Err(DSAError::InvalidParamSize)
                    };
        Ok(DSAParameters{ size: size, p: p, g: g, q: q })
    }

    /// Generate a new set of DSA parameters for use. You probably shouldn't be
    /// doing this.  This is equivalent to calling `generate_w_rng` with
    /// `OsRng`, which is supposed to be cryptographically sound.
    pub fn generate(ps: DSAParameterSize)
        -> Result<DSAParameters,DSAGenError>
    {
        let mut rng = OsRng::new()?;
        DSAParameters::generate_w_rng(&mut rng, ps)
    }

    /// Generate a new set of DSA parameters for use, using the given entropy
    /// source. I would normally include a note here about making sure to use
    /// a good one, but if you're using DSA you've already given up a little
    /// bit of the high ground, there.
    pub fn generate_w_rng<G: Rng>(rng: &mut G, ps: DSAParameterSize)
        -> Result<DSAParameters,DSAGenError>
    {
        let firstseed  = get_input_seed(rng, ps, n_bits(ps))?;
        let (p, q, ev) = generate_provable_primes(rng, &firstseed, ps)?;
        DSAParameters::generate_g(ps, p, q, ev, 0)
    }

    /// Using the given p and q values and an index, create a new DSAParameters
    /// by creating a new generator g that works with p and q.
    pub fn generate_g(ps: DSAParameterSize,
                      p: BigUint, q: BigUint,
                      ev: DSAGenEvidence,
                      idx: u8)
        -> Result<DSAParameters, DSAGenError>
    {
        let g = generate_verifiable_generator(&p, &q, &ev, idx)?;
        Ok(DSAParameters{ size: ps, p: p, q: q, g: g })
    }

    /// Given the provided evidence, validate that the domain parameters
    /// were appropriately constructed.
    pub fn validate(&self, evidence: &DSAGenEvidence)
        -> bool
    {
        let mut rng = OsRng::new().unwrap();
        self.validate_w_rng(&mut rng, evidence)
    }

    /// Given the provided evidence, validate that the domain parameters
    /// were appropriately constructed, using the given random number
    /// generator.
    pub fn validate_w_rng<G: Rng>(&self, rng: &mut G, evidence: &DSAGenEvidence)
        -> bool
    {
        validate_provable_primes(rng, &self.p, &self.q, evidence)
    }
}

#[derive(Debug,PartialEq)]
pub struct DSAGenEvidence {
    pub first_seed:   BigUint,
    pub p_seed:       BigUint,
    pub q_seed:       BigUint,
    pub pgen_counter: usize,
    pub qgen_counter: usize
}

fn get_domain_parameter_seed(ev: &DSAGenEvidence) -> Vec<u8> {
    let mut output = Vec::new();
    output.append(&mut ev.first_seed.to_bytes_be());
    output.append(&mut ev.p_seed.to_bytes_be());
    output.append(&mut ev.q_seed.to_bytes_be());
    output
}

fn generate_provable_primes<G: Rng>(rng: &mut G,
                                    firstseed: &BigUint,
                                    ps: DSAParameterSize)
    -> Result<(BigUint, BigUint, DSAGenEvidence),DSAGenError>
{
    let one: BigUint = One::one();
    let two: BigUint = BigUint::from(2 as u64);
    let three: BigUint = BigUint::from(3 as u64);
    // See Page 38 of FIPS 186-4!
    let n = n_bits(ps);
    let l = l_bits(ps);
    // 1. Check that the (L, N) pair is in the list of acceptable (L, N) pairs
    //    (see Section 4.2). If the pair is not in the list, return FAILURE.
    //
    //  Done because sum types are cool.
    //
    // 2. Using N as the length and firstseed as the input_seed, use the random
    //    prime generation routine in Appendix C.6 to obtain q, qseed and
    //    qgen_counter. If FAILURE is returned, then return FAILURE.
    let (q, qseed, qgen_counter) = shawe_taylor(rng, n, &firstseed)?;
    // 3. Using ceiling(L / 2 + 1) as the length and qseed as the input_seed,
    //    use the random prime generation routine in Appendix C.6 to obtain
    //    p0, pseed, and pgen_counter. If FAILURE is returned, then return
    //    FAILURE.
    //
    //  NOTE: The ceiling isn't required. All of the values of L divide
    //        evenly by 2, so it's just l / 2 + 1. I'm not sure why the
    //        spec mentions it, frankly.
    let (p0, mut pseed, mut pgen_counter) = shawe_taylor(rng, l/2 + 1, &qseed)?;
    // 4. iterations = ceiling(L / outlen) - 1.
    let iterations = ceildiv(&l, &256) - 1;
    // 5. old_counter = pgen_counter.
    let old_counter = pgen_counter;
    // 6. x = 0.
    let mut x_bytes = Vec::new();
    // 7. For i = 0 to iterations fo
    //      x + x + (Hash(pseed + i) * 2^(i * outlen).
    //  NOTE: WE run this backwards, much like we do in shawe_taylor()
    let mut i: i64 = iterations as i64;
    while i >= 0 {
        let bigi = BigUint::from_i64(i).unwrap();
        let prime_i = &pseed + &bigi;
        let mut hash_i = hash(&prime_i, l);
        x_bytes.append(&mut hash_i);
        i -= 1;
    }
    let x = BigUint::from_bytes_be(&x_bytes);
    // 8. pseed = pseed + iterations + 1.
    pseed = &pseed + iterations + &one;
    // 9. x = 2^(L-1) + (x mod 2^(L-1));
    let twol1: BigUint = &one << (l - 1);
    // 10. t = ceiling(x / (2 * q * p_0))
    let twoqp0 = &two * &q * &p0;
    let mut t = ceildiv(&x, &twoqp0);
    loop {
        // 11. If (2tqp_0 + 1) > 2^L, then t = ceiling(2^(L-1)/2qp0).
        let twotqp0p1 = (&t * &twoqp0) + &one;
        let twol = &one << l;
        if &twotqp0p1 > &twol {
            t = ceildiv(&twol1, &twoqp0);
        }
        // 12. p = 2tqp_0 + 1
        let p = twotqp0p1;
        // 13. pgen_counter = pgen_counter + 1
        pgen_counter = &pgen_counter + 1;
        // 14. a = 0
        let mut a_bytes = Vec::new();
        // 15. For i = 0 to iterations do
        //       a = a + (Hash(pseed + i) * 2^(i*outlen).
        i = iterations as i64;
        while i >= 0 {
            let bigi = BigUint::from_i64(i).unwrap();
            let prime_i = &pseed + &bigi;
            let mut hash_i = hash(&prime_i, l);
            a_bytes.append(&mut hash_i);
            i -= 1;
        }
        let mut a = BigUint::from_bytes_be(&a_bytes);
        // 16. pseed = pseed + iterations + 1.
        pseed = &pseed + iterations + &one;
        // 17. a = 2 + (a mod (p - 3))
        let pm3 = &p - &three;
        let amodpm3 = &a % &pm3;
        a = &two + &amodpm3;
        // 18. z = a^(2tq) mod p.
        let twotq = &two * &t * &q;
        let z = a.modpow(&twotq, &p);
        // 19. If ((1 = GCD(z-1,p)) and (1 = z^p0 mod p)), then return SUCCESS
        // and the values of p, q, and (optionally) pseed, qseed, pgen_counter,
        // and qgen_counter.
        let zm1 = &z - &one;
        if (&one == &zm1.gcd(&p)) && (&one == &z.modpow(&p0, &p)) {
            let evidence = DSAGenEvidence {
                             first_seed: firstseed.clone(),
                             p_seed: pseed,
                             q_seed: qseed,
                             pgen_counter: pgen_counter,
                             qgen_counter: qgen_counter
                           };
            return Ok((p, q, evidence));
        }
        // 20. If (pgen_counter > (4L + old_counter)), then return FAILURE.
        if pgen_counter > ((4 * l) + old_counter) {
            return Err(DSAGenError::TooManyGenAttempts);
        }
        // 21. t = t + 1
        t = &t + &one;
        // 22. Go to step 11.
    }
}

fn validate_provable_primes<G: Rng>(rng: &mut G,
                                    p: &BigUint, q: &BigUint,
                                    ev: &DSAGenEvidence)
    -> bool
{
    let one: BigUint = One::one();
    // This is from Page 40 of 186-4, section A.1.2.2.
    // 1. L = len(p);
    let l = ((p.bits() + 255) / 256) * 256;
    // 2. N = len(q);
    let n = ((q.bits() + 15) / 16) * 16;
    // 3. Check that the (L, N) pair is in the list of acceptable (L, N) pairs.
    //    If the pair is not in the list, then return failure.
    let params = match (l, n) {
                     (1024, 160) => DSAParameterSize::L1024N160,
                     (2048, 224) => DSAParameterSize::L2048N224,
                     (2048, 256) => DSAParameterSize::L2048N256,
                     (3072, 256) => DSAParameterSize::L3072N256,
                     _           => return false
                 };
    // 4. If (firstseed < 2^(n-1), then return FAILURE.
    let twon1 = &one << (n - 1);
    if &ev.first_seed < &twon1 {
        return false;
    }
    // 5. If (2^n <= q), then return FAILURE.
    let twon = &one << n;
    if &twon <= q {
        return false;
    }
    // 6. If (2^l <= p), then return FAILURE.
    let twol = &one << l;
    if &twol <= p {
        return false;
    }
    // 7. If ((p - 1) mod q /= 0), then return FAILURE.
    let pm1 = p - &one;
    if !pm1.mod_floor(&q).is_zero() {
        return false;
    }
    // 8. Using L, N and firstseed, perform the constructive prime generation
    //    procedure in Appendix A.1.2.1.2 to obtain p_val, q_val, pseed_val,
    //    qseed_val, pgen_counter_val, and qgen_counter_val. If FAILURE is
    //    returned, or if (q_val ≠ q) or (qseed_val ≠ qseed) or
    //    (qgen_counter_val ≠ qgen_counter) or (p_val ≠ p) or (pseed_val ≠
    //    pseed) or (pgen_counter_val ≠ pgen_counter), then return FAILURE.
    match generate_provable_primes(rng, &ev.first_seed, params) {
        Err(_) => false,
        Ok((p_val, q_val, ev2)) => {
            // 9. Return SUCCESS
            (&q_val == q) && (&p_val == p) && (ev == &ev2)
        }
    }
}

fn generate_verifiable_generator(p: &BigUint,
                                 q: &BigUint,
                                 ev: &DSAGenEvidence,
                                 index: u8)
    -> Result<BigUint,DSAGenError>
{
    // See FIPS 186-4, Section A.2.3: Verifiable Canonical Generatio of the
    // Generator g
    let one: BigUint = One::one();
    let two: BigUint = BigUint::from(2 as u64);
    // 1. If (index is incorrect), then return INVALID.
    //   NOTE: Can't happen, because types.
    // 2. N = len(q)
    let _n = q.bits();
    // 3. e = (p - 1)/q.
    let e = (p - &one) / q;
    // 4. count = 0.
    let mut count: u16 = 0;

    loop {
        // 5. count = count + 1;
        count = count + 1;
        // 6. if (count = 0), then return INVALID.
        if count == 0 {
            return Err(DSAGenError::TooManyGenAttempts);
        }
        // 7. U = domain_parameter_seed || "ggen" || index || count
        //     Comment: "ggen" is the bit string 0x6767656E.
        let mut u = get_domain_parameter_seed(&ev);
        u.push(0x67); u.push(0x67); u.push(0x65); u.push(0x6E);
        u.push(index);
        u.push((count >> 8) as u8); u.push((count & 0xFF) as u8);
        // 8. W = hash(U)
        let mut dgst = Sha256::default();
        dgst.process(&u);
        let w = BigUint::from_bytes_be(dgst.fixed_result().as_slice());
        // 9. g = W^e mod p
        let g = w.modpow(&e, &p);
        // 10. if (g < 2), then go to step 5.
        if &g >= &two {
            // 11. Return VALID and the value of g.
            return Ok(g);
        }
    }
}

fn verify_generator(p: &BigUint, q: &BigUint, ev: &DSAGenEvidence,
                    index: u8, g: &BigUint)
    -> bool
{
    // FIPS 186.4, Section A.2.4!
    let one: BigUint = One::one();
    let two = BigUint::from(2 as u64);
    // 1. If (index is incorrect), then return INVALID.
    //    NOTE: Not sure how this can be invalid.
    // 2. Verify that 2 <= g <= (p - 1). If not true, return INVALID.
    if g < &two {
        return false;
    }
    if g >= p {
        return false;
    }
    // 3. If (g^q /= 1 mod p), then return INVALID.
    if g.modpow(q, p) != one {
        return false;
    }
    // 4. N = len(q)
    let n = ((q.bits() + 15) / 15) * 15;
    // 5. e = (p - 1) / q
    let e = (p - &one) / q;
    // 6. count = 0
    let mut count: u16 = 0;
    loop {
        // 7. count = count + 1
        count = count + 1;
        // 8. if (count == 0), then return INVALID
        if count == 0 {
            return false;
        }
        // 9. U = domain_parameter_seed || "ggen" || index || count.
        let mut u = get_domain_parameter_seed(&ev);
        u.push(0x67); u.push(0x67); u.push(0x65); u.push(0x6E);
        u.push(index);
        u.push((count >> 8) as u8); u.push((count & 0xFF) as u8);
        // 10. W = Hash(U)
        let mut dgst = Sha256::default();
        dgst.process(&u);
        let w = BigUint::from_bytes_be(dgst.fixed_result().as_slice());
        // 11. computed_g = W^e mod p
        let computed_g = w.modpow(&e, &p);
        // 12. if (computed_g < 2), then go to step 7.
        if &computed_g < &two {
            continue;
        }
        // 13. if (computed_g == g), then return VALID, else return INVALID
        return &computed_g == g;
    }
}

fn get_input_seed<G: Rng>(rng: &mut G, size: DSAParameterSize, seedlen: usize)
    -> Result<BigUint,DSAGenError>
{
    let mut firstseed = Zero::zero();
    let one: BigUint = One::one();
    let n = n_bits(size);

    // 3. If (seedlen < N), then return FAILURE
    if seedlen < n {
        return Err(DSAGenError::InvalidSeedLength)
    }
    // 4. While firstseed < 2^(n-1) ...
    let twonm1 = one << (n - 1);
    while &firstseed < &twonm1 {
        // Get an arbitrary sequence of seedlen bits as firstseed.
        let bytes: Vec<u8> = rng.gen_iter().take(seedlen / 8).collect();
        firstseed = BigUint::from_bytes_be(&bytes);
    }
    // 5. Return SUCCESS and the value of firstseed
    Ok(firstseed)
}

// Appendix C.6: Shawe-Taylor Random_Prime Routine. Also referenced in 186-4
// as ST_Random_Prime, so when you see that in a bit, understand that it's a
// recursive call.
fn shawe_taylor<G: Rng>(rng: &mut G, length: usize, input_seed: &BigUint)
    -> Result<(BigUint,BigUint,usize),DSAGenError>
{
    // 1. If (length < 2), then return (FAILURE, 0, 0 {, 0}).
    if length < 2 {
        return Err(DSAGenError::InvalidPrimeLength);
    }
    // 2. If (length ≥ 33), then go to step 14.
    if length >= 33 {
        shawe_taylor_large(rng, length, input_seed)
    } else {
        shawe_taylor_small(length, input_seed)
    }
}

fn shawe_taylor_small(length: usize, input_seed: &BigUint)
    -> Result<(BigUint,BigUint,usize),DSAGenError>
{
    let one: BigUint = One::one();
    let two: BigUint = BigUint::from(2 as u64);
    // 3. prime_seed = input_seed.
    let mut prime_seed: BigUint = input_seed.clone();
    // 4. prime_gen_counter = 0
    let mut prime_gen_counter = 0;
    loop {
        // 5. c = Hash(prime_seed) ⊕ Hash(prime_seed + 1).
        let cbs = xorvecs(hash(&prime_seed, length),
                          hash(&(&prime_seed + &one), length));
        let mut c = BigUint::from_bytes_be(&cbs);
        // 6. c = 2^(length – 1) + (c mod 2^(length – 1))
        let twolm1: BigUint = &one << (length - 1);
        c = &twolm1 + (c % &twolm1);
        // 7. c = (2 ∗ floor(c / 2)) + 1.
        c = ((c >> 1) << 1) + &one;
        // 8. prime_gen_counter = prime_gen_counter + 1.
        prime_gen_counter = prime_gen_counter + 1;
        // 9. prime_seed = prime_seed + 2.
        prime_seed = prime_seed + &two;
        // 10. Perform a deterministic primality test on c. For example, since
        //     c is small, its primality can be tested by trial division. See
        //     Appendix C.7.
        let c_is_prime = prime_test(&c);
        // 11. If (c is a prime number), then
        if c_is_prime {
            // 11.1 prime = c.
            let prime = c;
            // 11.2 Return (SUCCESS, prime, prime_seed {, prime_gen_counter}).
            return Ok((prime, prime_seed.clone(), prime_gen_counter))
        }
        // 12. If (prime_gen_counter > (4 ∗ length)), then
        //     return (FAILURE, 0, 0 {, 0}).
        if prime_gen_counter > (4 * length) {
            return Err(DSAGenError::TooManyGenAttempts);
        }
        // 13. Go to step 5.
    }
}

fn shawe_taylor_large<G: Rng>(rng: &mut G, length: usize, input_seed: &BigUint)
    -> Result<(BigUint,BigUint,usize),DSAGenError>
{
    let one: BigUint = One::one();
    let two: BigUint = BigUint::from(2 as u64);
    let three: BigUint = BigUint::from(3 as u64);
    // 14. (status, c0, prime_seed, prime_gen_counter) =
    //          (ST_Random_Prime ((ceiling(length / 2) + 1), input_seed).
    let len2: usize = ceildiv(&length, &2);
    let (c0, mut prime_seed, mut prime_gen_counter) =
        shawe_taylor( rng, len2 + 1, input_seed )?;
    // 15. If FAILURE is returned, return (FAILURE, 0, 0 {, 0}).
    // 16. iterations = ceiling(length / outlen) – 1.
    let outlen = 256; // the size of the hash function output in bits
    let iterations = ceildiv(&length, &outlen) - 1;
    // 17. old_counter = prime_gen_counter.
    let old_counter = prime_gen_counter;
    // 18. x = 0.
    let mut x_bytes = Vec::new();
    // 19. For i = 0 to iterations do
    //        x = x + (Hash(prime_seed + i) ∗ 2^(i * outlen)).
    //
    //  We're going to actually run this backwards. What this computation
    //  does is essentially built up a large vector of hashes, one per iteration,
    //  shifting them bast each other via the 2^(i * outlen) term. So we'll just
    //  do this directly.
    let mut i: i64 = iterations as i64;
    while i >= 0 {
        let bigi = BigUint::from_i64(i).unwrap();
        let prime_i = &prime_seed + &bigi;
        let mut hash_i = hash(&prime_i, length);
        x_bytes.append(&mut hash_i);
        i -= 1;
    }
    let mut x = BigUint::from_bytes_be(&x_bytes);
    // 20. prime_seed = prime_seed + iterations + 1.
    prime_seed = &prime_seed + iterations + &one;
    // 21. x = 2^(length – 1) + (x mod 2^(length – 1)).
    let twolm1 = &one << (length - 1);
    x = &twolm1 + (&x % &twolm1);
    // 22. t = ceiling(x / (2c0)).
    let twoc0 = &two * &c0;
    let mut t: BigUint = ceildiv(&x, &twoc0);
    loop {
        // 23. If (2tc0 + 1 > 2^length), then t = ceiling(2^(length – 1) / (2c0)).
        let twotc0 = &t * &twoc0;
        if (&twotc0 + &one) > (&one << length) {
            t = ceildiv(&twolm1, &twoc0);
        }
        // 24. c = 2tc0 + 1.
        let c = &twotc0 + &one;

        // 25. prime_gen_counter = prime_gen_counter + 1.
        prime_gen_counter = prime_gen_counter + 1;
        // 26. a = 0.
        let mut a_bytes = Vec::new();
        // 27. For i = 0 to iterations do
        //           a = a + (Hash(prime_seed + i) ∗ 2 i * outlen).
        //
        //  As with the last time we did this, we're going to do this more constructively
        i = iterations as i64;
        while i >= 0 {
            let bigi = BigUint::from_i64(i).unwrap();
            let prime_i = &prime_seed + &bigi;
            let mut hash_i = hash(&prime_i, length);
            a_bytes.append(&mut hash_i);
            i -= 1;
        }
        let mut a = BigUint::from_bytes_be(&a_bytes);
        // 28. prime_seed = prime_seed + iterations + 1.
        prime_seed = &prime_seed + iterations + &one;
        // 29. a = 2 + (a mod (c – 3)).
        a = &two + (a % (&c - &three));
        // 30. z = a^2t mod c.
        let z: BigUint = a.modpow(&(&two * &t), &c);
        // 31. If ((1 = GCD(z – 1, c)) and (1 = z^c_0 mod c)), then
        let gcd_ok = &one == &c.gcd(&(&z - &one));
        let modpow_ok = &one == &z.modpow(&c0, &c);
        if gcd_ok && modpow_ok {
            // 31.1 prime = c.
            let prime = c;
            // 31.2 Return (SUCCESS, prime, prime_seed {, prime_gen_counter}).
            return Ok((prime, prime_seed, prime_gen_counter));
        }
        // 32. If (prime_gen_counter ≥ ((4 ∗ length) + old_counter)), then
        //     return (FAILURE, 0, 0 {, 0}).
        let limit = (4 * length) + old_counter;
        if prime_gen_counter >= limit {
            return Err(DSAGenError::TooManyGenAttempts)
        }
        // 33. t = t + 1.
        t = t + &one;
        // 34. Go to step 23.
    }
}

fn ceildiv<T>(a: &T, b: &T) -> T
 where T: Add<Output=T>,
       T: Sub<Output=T>,
       T: Div<Output=T>,
       T: Clone + One
{
    let aclone: T = a.clone();
    let bclone: T = b.clone();
    let one = One::one();
    let x: T = (aclone + bclone.clone()) - one;
    let res = x / bclone;
    res
}

fn prime_test(x: &BigUint) -> bool {
    let two = BigUint::from(2 as u64);
    let three = BigUint::from(3 as u64);
    let five = BigUint::from(5 as u64);

    if x.is_even() {
        if x == &two {
            return true;
        }
        return false;
    }

    if x.is_multiple_of(&three) {
        return false;
    }

    if x.is_multiple_of(&five) {
        return false;
    }

    let mut divisor = BigUint::from(7 as u32);
    let sqrtx = isqrt(&x);
    while &divisor < &sqrtx {
        if x.is_multiple_of(&divisor) {
            return false;
        }
        divisor = next_divisor(divisor);
    }

    true
}

fn isqrt(x: &BigUint) -> BigUint {
    let mut num = x.clone();
    let mut res = Zero::zero();
    let one: BigUint = One::one();
    let mut bit: BigUint = one << num.bits();

    while &bit > &num {
        bit >>= 2;
    }

    while !bit.is_zero() {
        if num >= (&res + &bit) {
            num = &num - (&res + &bit);
            res  = (&res >> 1) + &bit;
        } else {
            res >>= 1;
        }
        bit >>= 2;
    }

    res
}

fn next_divisor(input: BigUint) -> BigUint {
    let two = BigUint::from(2 as u64);
    let three = BigUint::from(3 as u64);
    let five = BigUint::from(5 as u64);
    let mut x = input;

    loop {
        x = &x + &two;

        if x.is_multiple_of(&three) {
            continue;
        }
        if x.is_multiple_of(&five) {
            continue;
        }

        return x;
    }
}

fn hash(x: &BigUint, len: usize) -> Vec<u8> {
    let mut base = x.to_bytes_be();
    let bytelen = len / 8;
    while base.len() < bytelen {
        base.insert(0,0);
    }
    let mut dgst = Sha256::default();
    dgst.process(&base);
    dgst.fixed_result().as_slice().to_vec()
}

fn xorvecs(a: Vec<u8>, b: Vec<u8>) -> Vec<u8> {
    assert!(a.len() == b.len());
    let mut c = Vec::with_capacity(a.len());

    for (a,b) in a.iter().zip(b.iter()) {
        c.push(a ^ b);
    }
    c
}

/// A DSA key pair
#[derive(Clone,Debug,PartialEq)]
pub struct DSAKeyPair {
    pub private: DSAPrivateKey,
    pub public:  DSAPublicKey
}

impl DSAKeyPair {
    pub fn generate(size: DSAParameterSize)
        -> Result<DSAKeyPair,DSAGenError>
    {
        let mut rng = OsRng::new()?;
        DSAKeyPair::generate_rng(&mut rng, size)
    }

    pub fn generate_rng<G: Rng>(rng: &mut G, size: DSAParameterSize)
        -> Result<DSAKeyPair,DSAGenError>
    {
        let params = DSAParameters::generate_w_rng(rng, size)?;
        DSAKeyPair::generate_w_params_rng(rng, &params)
    }

    pub fn generate_w_params(params: &DSAParameters)
        -> Result<DSAKeyPair,DSAGenError>
    {
        let mut rng = OsRng::new()?;
        DSAKeyPair::generate_w_params_rng(&mut rng, params)
    }

    pub fn generate_w_params_rng<G: Rng>(rng: &mut G, params: &DSAParameters)
        -> Result<DSAKeyPair,DSAGenError>
    {
        // 1. N = len(q); L = len(p);
        let n = n_bits(params.size);
        // 2. If the (L,N) pair is invalid, then return an ERROR indicator,
        //    Invalid_x, and Invalid_y.
        // 3. requested_security_strength = the security strength associated
        //    with the (L, N) pair; see SP 800-57.
        // 4. Obtain a string of N+64 returned_bits from an RBG with a security
        //    strength of requested_security_strength or more. If an ERROR
        //    indication is returned, then return an ERROR indication,
        //    Invalid_x, and Invalid_y.
        let returned_bits: Vec<u8> = rng.gen_iter().take(n + 8).collect();
        // 5. Convert returned_bits to the (non-negative) integer c.
        let c = BigUint::from_bytes_be(&returned_bits);
        // 6. x = (c mod (q-1)) + 1.
        let one = BigUint::from(1 as u64);
        let x = (&c % (&params.q - &one)) + &one;
        // 7. y = g^x mod p
        let y = params.g.modpow(&x, &params.p);
        // 8. Return SUCCESS, x, and y.
        let private = DSAPrivateKey { params: params.clone(), x: x };
        let public  = DSAPublicKey  { params: params.clone(), y: y };
        Ok(DSAKeyPair {
            private: private,
            public: public
        })
    }
}

/// A DSA key pair
#[derive(Clone,Debug,PartialEq)]
pub struct DSAPrivateKey {
    params: DSAParameters,
    x: BigUint
}

impl DSAPrivateKey {
    pub fn new(params: &DSAParameters, x: BigUint) -> DSAPrivateKey {
        DSAPrivateKey {
            params: params.clone(),
            x: x
        }
    }

    pub fn sign<Hash>(&self, m: &[u8]) -> DSASignature
      where
        Hash: Clone + BlockInput + Input + FixedOutput + Default,
        Hmac<Hash>: Clone,
        Hash::BlockSize: ArrayLength<u8>
    {
        // This algorithm is per RFC 6979, which has a nice, relatively
        // straightforward description of how to do DSA signing.
        //
        // 1.  H(m) is transformed into an integer modulo q using the bits2int
        //     transform and an extra modular reduction:
        //
        //        h = bits2int(H(m)) mod q
        //
        //     As was noted in the description of bits2octets, the extra
        //     modular reduction is no more than a conditional subtraction.
        //
        let mut digest = <Hash>::default();
        digest.process(m);
        let n = n_bits(self.params.size);
        let h1: Vec<u8> = digest.fixed_result()
                                .as_slice()
                                .iter()
                                .map(|x| *x)
                                .collect();
        let h0 = bits2int(&h1, &self.params.q, n);
        let h = h0.mod_floor(&self.params.q);

        // 2.  A random value modulo q, dubbed k, is generated.  That value
        //     shall not be 0; hence, it lies in the [1, q-1] range.  Most
        //     of the remainder of this document will revolve around the
        //     process used to generate k.  In plain DSA or ECDSA, k should
        //     be selected through a random selection that chooses a value
        //     among the q-1 possible values with uniform probability.
        for k in KIterator::<Hash>::new(&h1, n, &self.params.q, &self.x) {
            // 3. A value r (modulo q) is computed from k and the key
            //    parameters:
            //     *  For DSA:
            //           r = g^k mod p mod q
            //
            //           (The exponentiation is performed modulo p, yielding a
            //           number between 0 and p-1, which is then further reduced
            //           modulo q.)
            //     *  For ECDSA ...
            //
            //    If r turns out to be zero, a new k should be selected and r
            //    computed again (this is an utterly improbable occurrence).
            let r = self.params.g.modpow(&k, &self.params.p) % &self.params.q;
            if r.is_zero() {
                continue;
            }
            // 4.  The value s (modulo q) is computed:
            //
            //           s = (h+x*r)/k mod q
            //
            //     The pair (r, s) is the signature.
            let kinv = modinv(&k, &self.params.q);
            let s = ((&h + (&self.x * &r)) * &kinv) % &self.params.q;
            return DSASignature{ r: r, s: s };
        }
        panic!("The world is broken; couldn't find a k in sign().");
    }
}

/// A DSA key pair
#[derive(Clone,Debug,PartialEq)]
pub struct DSAPublicKey {
    params: DSAParameters,
    y: BigUint
}

impl DSAPublicKey {
    pub fn new(params: &DSAParameters, y: BigUint) -> DSAPublicKey {
        DSAPublicKey {
            params: params.clone(),
            y: y
        }
    }

    pub fn verify<Hash>(&self, m: &[u8], sig: &DSASignature) -> bool
      where Hash: Clone + Default + Input + FixedOutput
    {
        if sig.r >= self.params.q {
            return false;
        }
        if sig.s >= self.params.q {
            return false;
        }
        let n = n_bits(self.params.size);
        // w = (s')^-1 mod q;
        let w = modinv(&sig.s, &self.params.q);
        // z = the leftmost min(N, outlen) bits of Hash(M').
        let mut digest = <Hash>::default();
        digest.process(m);
        let z = { let mut bytes: Vec<u8> = digest.fixed_result()
                                                 .as_slice()
                                                 .iter()
                                                 .map(|x| *x)
                                                 .collect();
                  let n = n_bits(self.params.size) / 8;
                  let len = min(n, bytes.len());
                  bytes.truncate(len);
                  BigUint::from_bytes_be(&bytes) };
        // u1 = (zw) mod q
        let u1 = (&z * &w).mod_floor(&self.params.q);
        // u2 = (rw) mod q
        let u2 = (&sig.r * &w).mod_floor(&self.params.q);
        // v = (((g)^u1(y)^u2) mod p) mod q
        let v_1 = self.params.g.modpow(&u1, &self.params.p);
        let v_2 = self.y.modpow(&u2, &self.params.p);
        let v = (&v_1 * &v_2).mod_floor(&self.params.p).mod_floor(&self.params.q);
        // if v = r, then the signature is verified
        v == sig.r
    }
}

/// A DSA Signature
#[derive(Clone,Debug,PartialEq)]
pub struct DSASignature {
    r: BigUint,
    s: BigUint
}

fn miller_rabin<G: Rng>(g: &mut G, n: &BigUint, iters: usize)
    -> bool
{
    let one: BigUint = One::one();
    let two = &one + &one;
    let nm1 = n - &one;
    // Quoth Wikipedia:
    // write n - 1 as 2^r*d with d odd by factoring powers of 2 from n - 1
    let mut d = nm1.clone();
    let mut r = 0;
    while d.is_even() {
        d >>= 1;
        r += 1;
        assert!(r < n.bits());
    }
    // WitnessLoop: repeat k times
    'WitnessLoop: for _k in 0..iters {
        // pick a random integer a in the range [2, n - 2]
        let a = random_in_range(g, &two, &nm1);
        // x <- a^d mod n
        let mut x = a.modpow(&d, &n);
        // if x = 1 or x = n - 1 then
        if (&x == &one) || (&x == &nm1) {
            // continue WitnessLoop
            continue 'WitnessLoop;
        }
        // repeat r - 1 times:
        for _i in 0..r {
            // x <- x^2 mod n
            x = x.modpow(&two, &n);
            // if x = 1 then
            if &x == &one {
                // return composite
                return false;
            }
            // if x = n - 1 then
            if &x == &nm1 {
                // continue WitnessLoop
                continue 'WitnessLoop;
            }
        }
        // return composite
        return false;
    }
    // return probably prime
    true
}

fn random_in_range<G: Rng>(rng: &mut G, min: &BigUint, max: &BigUint)
    -> BigUint
{
    let bitlen = ((max.bits() + 31) / 32) * 32;
    loop {
        let candidate = random_number(rng, bitlen);

        if (&candidate >= min) && (&candidate < max) {
            return candidate;
        }
    }
}

fn random_number<G: Rng>(rng: &mut G, bitlen: usize) -> BigUint {
    assert!(bitlen % 32 == 0);
    let wordlen = bitlen / 32;
    let components = rng.gen_iter().take(wordlen).collect();
    BigUint::new(components)
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


#[cfg(test)]
mod tests {
//    use quickcheck::{Arbitrary,Gen};
    use sha1::Sha1;
    use sha2::{Sha224,Sha256,Sha384,Sha512};
    use super::*;

//    const DSA_SIZES: [DSAParameterSize; 4] =
//        [DSAParameterSize::L1024N160,
//         DSAParameterSize::L2048N224,
//         DSAParameterSize::L2048N256,
//         DSAParameterSize::L3072N256];
//
//    impl Arbitrary for DSAParameterSize {
//        fn arbitrary<G: Gen>(g: &mut G) -> DSAParameterSize {
//            g.choose(&DSA_SIZES).unwrap().clone()
//        }
//    }

    const NUM_TESTS: u32 = 2;

    //#[test]
    fn shawe_taylor_works() {
        let mut rng = OsRng::new().unwrap();
        let params = DSAParameterSize::L1024N160;

        for _ in 0..NUM_TESTS {
            let seed = get_input_seed(&mut rng,params,n_bits(params)).unwrap();
            let (v, _, _) = shawe_taylor(&mut rng,n_bits(params),&seed).unwrap();
            assert!(miller_rabin(&mut rng, &v, 64));
        }
    }

    //#[test]
    fn pqg_generation_checks() {
        let mut rng = OsRng::new().unwrap();
        let params = DSAParameterSize::L1024N160;

        for _ in 0..NUM_TESTS {
            let seed = get_input_seed(&mut rng,params,n_bits(params)).unwrap();
            let (p, q, ev) =
                generate_provable_primes(&mut rng, &seed, params).unwrap();
            assert!(validate_provable_primes(&mut rng, &p, &q, &ev));
            let index = rng.gen::<u8>();
            let g = generate_verifiable_generator(&p, &q, &ev, index).unwrap();
            assert!(verify_generator(&p, &q, &ev, index, &g));
        }
    }

    fn get_first_k<H>(msg: &[u8], qlen: usize, q: &BigUint, x: &BigUint)
        -> Vec<u8>
      where
        H: Clone + BlockInput + Input + FixedOutput + Default,
        Hmac<H>: Clone,
        H::BlockSize : ArrayLength<u8>
    {
        let mut hash = <H>::default();
        hash.process(msg);
        let h1 = hash.fixed_result().as_slice().to_vec();
        let mut iter = KIterator::<H>::new(&h1, qlen, q, x);
        let mut val = iter.next().unwrap();
        val.to_bytes_be()
    }

    macro_rules! run_rfc6979_test {
        ($hash: ty, $val: ident, $public: ident, $private: ident,
         k $k: expr,
         r $r: expr,
         s $s: expr) => ({
            let mut digest = <$hash>::default();
            digest.process(&$val);
            let h1 = digest.fixed_result().as_slice().to_vec();
            let rbytes = $r;
            let sbytes = $s;
            let kbytes = $k;
            let r = BigUint::from_bytes_be(&rbytes);
            let s = BigUint::from_bytes_be(&sbytes);
            let mut iter = KIterator::<$hash>::new(&h1,
                                                   n_bits($public.params.size),
                                                   &$public.params.q,
                                                   &$private.x);
            let k1 = iter.next().unwrap().to_bytes_be();
            assert_eq!($k, k1);
            let sig = $private.sign::<$hash>(&$val);
            assert_eq!(sig.r, r);
            assert_eq!(sig.s, s);
            assert!($public.verify::<$hash>(&$val, &sig));
        })
    }

    // these appendix_* tests are out of RFC6979
    #[test]
    fn appendix_a21() {
        let pbytes = vec![0x86, 0xF5, 0xCA, 0x03, 0xDC, 0xFE, 0xB2, 0x25,
                          0x06, 0x3F, 0xF8, 0x30, 0xA0, 0xC7, 0x69, 0xB9,
                          0xDD, 0x9D, 0x61, 0x53, 0xAD, 0x91, 0xD7, 0xCE,
                          0x27, 0xF7, 0x87, 0xC4, 0x32, 0x78, 0xB4, 0x47,
                          0xE6, 0x53, 0x3B, 0x86, 0xB1, 0x8B, 0xED, 0x6E,
                          0x8A, 0x48, 0xB7, 0x84, 0xA1, 0x4C, 0x25, 0x2C,
                          0x5B, 0xE0, 0xDB, 0xF6, 0x0B, 0x86, 0xD6, 0x38,
                          0x5B, 0xD2, 0xF1, 0x2F, 0xB7, 0x63, 0xED, 0x88,
                          0x73, 0xAB, 0xFD, 0x3F, 0x5B, 0xA2, 0xE0, 0xA8,
                          0xC0, 0xA5, 0x90, 0x82, 0xEA, 0xC0, 0x56, 0x93,
                          0x5E, 0x52, 0x9D, 0xAF, 0x7C, 0x61, 0x04, 0x67,
                          0x89, 0x9C, 0x77, 0xAD, 0xED, 0xFC, 0x84, 0x6C,
                          0x88, 0x18, 0x70, 0xB7, 0xB1, 0x9B, 0x2B, 0x58,
                          0xF9, 0xBE, 0x05, 0x21, 0xA1, 0x70, 0x02, 0xE3,
                          0xBD, 0xD6, 0xB8, 0x66, 0x85, 0xEE, 0x90, 0xB3,
                          0xD9, 0xA1, 0xB0, 0x2B, 0x78, 0x2B, 0x17, 0x79];
        let qbytes = vec![0x99, 0x6F, 0x96, 0x7F, 0x6C, 0x8E, 0x38, 0x8D,
                          0x9E, 0x28, 0xD0, 0x1E, 0x20, 0x5F, 0xBA, 0x95,
                          0x7A, 0x56, 0x98, 0xB1];
        let gbytes = vec![0x07, 0xB0, 0xF9, 0x25, 0x46, 0x15, 0x0B, 0x62,
                          0x51, 0x4B, 0xB7, 0x71, 0xE2, 0xA0, 0xC0, 0xCE,
                          0x38, 0x7F, 0x03, 0xBD, 0xA6, 0xC5, 0x6B, 0x50,
                          0x52, 0x09, 0xFF, 0x25, 0xFD, 0x3C, 0x13, 0x3D,
                          0x89, 0xBB, 0xCD, 0x97, 0xE9, 0x04, 0xE0, 0x91,
                          0x14, 0xD9, 0xA7, 0xDE, 0xFD, 0xEA, 0xDF, 0xC9,
                          0x07, 0x8E, 0xA5, 0x44, 0xD2, 0xE4, 0x01, 0xAE,
                          0xEC, 0xC4, 0x0B, 0xB9, 0xFB, 0xBF, 0x78, 0xFD,
                          0x87, 0x99, 0x5A, 0x10, 0xA1, 0xC2, 0x7C, 0xB7,
                          0x78, 0x9B, 0x59, 0x4B, 0xA7, 0xEF, 0xB5, 0xC4,
                          0x32, 0x6A, 0x9F, 0xE5, 0x9A, 0x07, 0x0E, 0x13,
                          0x6D, 0xB7, 0x71, 0x75, 0x46, 0x4A, 0xDC, 0xA4,
                          0x17, 0xBE, 0x5D, 0xCE, 0x2F, 0x40, 0xD1, 0x0A,
                          0x46, 0xA3, 0xA3, 0x94, 0x3F, 0x26, 0xAB, 0x7F,
                          0xD9, 0xC0, 0x39, 0x8F, 0xF8, 0xC7, 0x6E, 0xE0,
                          0xA5, 0x68, 0x26, 0xA8, 0xA8, 0x8F, 0x1D, 0xBD];
        let xbytes = vec![0x41, 0x16, 0x02, 0xCB, 0x19, 0xA6, 0xCC, 0xC3,
                          0x44, 0x94, 0xD7, 0x9D, 0x98, 0xEF, 0x1E, 0x7E,
                          0xD5, 0xAF, 0x25, 0xF7];
        let ybytes = vec![0x5D, 0xF5, 0xE0, 0x1D, 0xED, 0x31, 0xD0, 0x29,
                          0x7E, 0x27, 0x4E, 0x16, 0x91, 0xC1, 0x92, 0xFE,
                          0x58, 0x68, 0xFE, 0xF9, 0xE1, 0x9A, 0x84, 0x77,
                          0x64, 0x54, 0xB1, 0x00, 0xCF, 0x16, 0xF6, 0x53,
                          0x92, 0x19, 0x5A, 0x38, 0xB9, 0x05, 0x23, 0xE2,
                          0x54, 0x2E, 0xE6, 0x18, 0x71, 0xC0, 0x44, 0x0C,
                          0xB8, 0x7C, 0x32, 0x2F, 0xC4, 0xB4, 0xD2, 0xEC,
                          0x5E, 0x1E, 0x7E, 0xC7, 0x66, 0xE1, 0xBE, 0x8D,
                          0x4C, 0xE9, 0x35, 0x43, 0x7D, 0xC1, 0x1C, 0x3C,
                          0x8F, 0xD4, 0x26, 0x33, 0x89, 0x33, 0xEB, 0xFE,
                          0x73, 0x9C, 0xB3, 0x46, 0x5F, 0x4D, 0x36, 0x68,
                          0xC5, 0xE4, 0x73, 0x50, 0x82, 0x53, 0xB1, 0xE6,
                          0x82, 0xF6, 0x5C, 0xBD, 0xC4, 0xFA, 0xE9, 0x3C,
                          0x2E, 0xA2, 0x12, 0x39, 0x0E, 0x54, 0x90, 0x5A,
                          0x86, 0xE2, 0x22, 0x31, 0x70, 0xB4, 0x4E, 0xAA,
                          0x7D, 0xA5, 0xDD, 0x9F, 0xFC, 0xFB, 0x7F, 0x3B];
        //
        let p = BigUint::from_bytes_be(&pbytes);
        let q = BigUint::from_bytes_be(&qbytes);
        let g = BigUint::from_bytes_be(&gbytes);
        let params = DSAParameters::new(p, g, q).unwrap();
        let x = BigUint::from_bytes_be(&xbytes);
        let y = BigUint::from_bytes_be(&ybytes);
        let private = DSAPrivateKey::new(&params, x);
        let public = DSAPublicKey::new(&params, y);
        let size = DSAParameterSize::L1024N160;
        //
        let sample: [u8; 6] = [115, 97, 109, 112, 108, 101]; // "sample", ASCII
        let test:   [u8; 4] = [116, 101, 115, 116]; // "test", ASCII
        // With SHA-1, message = "sample":
        //    k = 7BDB6B0FF756E1BB5D53583EF979082F9AD5BD5B
        //    r = 2E1A0C2562B2912CAAF89186FB0F42001585DA55
        //    s = 29EFB6B0AFF2D7A68EB70CA313022253B9A88DF5
        run_rfc6979_test!(Sha1, sample, public, private,
          k vec![0x7B, 0xDB, 0x6B, 0x0F, 0xF7, 0x56, 0xE1, 0xBB,
                 0x5D, 0x53, 0x58, 0x3E, 0xF9, 0x79, 0x08, 0x2F,
                 0x9A, 0xD5, 0xBD, 0x5B],
          r vec![0x2E, 0x1A, 0x0C, 0x25, 0x62, 0xB2, 0x91, 0x2C,
                 0xAA, 0xF8, 0x91, 0x86, 0xFB, 0x0F, 0x42, 0x00,
                 0x15, 0x85, 0xDA, 0x55],
          s vec![0x29, 0xEF, 0xB6, 0xB0, 0xAF, 0xF2, 0xD7, 0xA6,
                 0x8E, 0xB7, 0x0C, 0xA3, 0x13, 0x02, 0x22, 0x53,
                 0xB9, 0xA8, 0x8D, 0xF5]);
        //  With SHA-224, message = "sample":
        //     k = 562097C06782D60C3037BA7BE104774344687649
        //     r = 4BC3B686AEA70145856814A6F1BB53346F02101E
        //     s = 410697B92295D994D21EDD2F4ADA85566F6F94C1
        run_rfc6979_test!(Sha224, sample, public, private,
           k vec![0x56, 0x20, 0x97, 0xC0, 0x67, 0x82, 0xD6, 0x0C,
                  0x30, 0x37, 0xBA, 0x7B, 0xE1, 0x04, 0x77, 0x43,
                  0x44, 0x68, 0x76, 0x49],
           r vec![0x4B, 0xC3, 0xB6, 0x86, 0xAE, 0xA7, 0x01, 0x45,
                  0x85, 0x68, 0x14, 0xA6, 0xF1, 0xBB, 0x53, 0x34,
                  0x6F, 0x02, 0x10, 0x1E],
           s vec![0x41, 0x06, 0x97, 0xB9, 0x22, 0x95, 0xD9, 0x94,
                  0xD2, 0x1E, 0xDD, 0x2F, 0x4A, 0xDA, 0x85, 0x56,
                  0x6F, 0x6F, 0x94, 0xC1]);
        // With SHA-256, message = "sample":
        //    k = 519BA0546D0C39202A7D34D7DFA5E760B318BCFB
        //    r = 81F2F5850BE5BC123C43F71A3033E9384611C545
        //    s = 4CDD914B65EB6C66A8AAAD27299BEE6B035F5E89
        run_rfc6979_test!(Sha256, sample, public, private,
            k vec![0x51, 0x9B, 0xA0, 0x54, 0x6D, 0x0C, 0x39, 0x20,
                   0x2A, 0x7D, 0x34, 0xD7, 0xDF, 0xA5, 0xE7, 0x60,
                   0xB3, 0x18, 0xBC, 0xFB],
            r vec![0x81, 0xF2, 0xF5, 0x85, 0x0B, 0xE5, 0xBC, 0x12,
                   0x3C, 0x43, 0xF7, 0x1A, 0x30, 0x33, 0xE9, 0x38,
                   0x46, 0x11, 0xC5, 0x45],
            s vec![0x4C, 0xDD, 0x91, 0x4B, 0x65, 0xEB, 0x6C, 0x66,
                   0xA8, 0xAA, 0xAD, 0x27, 0x29, 0x9B, 0xEE, 0x6B,
                   0x03, 0x5F, 0x5E, 0x89]);
        // With SHA-384, message = "sample":
        //    k = 95897CD7BBB944AA932DBC579C1C09EB6FCFC595
        //    r = 07F2108557EE0E3921BC1774F1CA9B410B4CE65A
        //    s = 54DF70456C86FAC10FAB47C1949AB83F2C6F7595
        run_rfc6979_test!(Sha384, sample, public, private,
            k vec![0x95, 0x89, 0x7C, 0xD7, 0xBB, 0xB9, 0x44, 0xAA,
                   0x93, 0x2D, 0xBC, 0x57, 0x9C, 0x1C, 0x09, 0xEB,
                   0x6F, 0xCF, 0xC5, 0x95],
            r vec![0x07, 0xF2, 0x10, 0x85, 0x57, 0xEE, 0x0E, 0x39,
                   0x21, 0xBC, 0x17, 0x74, 0xF1, 0xCA, 0x9B, 0x41,
                   0x0B, 0x4C, 0xE6, 0x5A],
            s vec![0x54, 0xDF, 0x70, 0x45, 0x6C, 0x86, 0xFA, 0xC1,
                   0x0F, 0xAB, 0x47, 0xC1, 0x94, 0x9A, 0xB8, 0x3F,
                   0x2C, 0x6F, 0x75, 0x95]);
        // With SHA-512, message = "sample":
        //    k = 09ECE7CA27D0F5A4DD4E556C9DF1D21D28104F8B
        //    r = 16C3491F9B8C3FBBDD5E7A7B667057F0D8EE8E1B
        //    s = 02C36A127A7B89EDBB72E4FFBC71DABC7D4FC69C
        run_rfc6979_test!(Sha512, sample, public, private,
            k vec![0x09, 0xEC, 0xE7, 0xCA, 0x27, 0xD0, 0xF5, 0xA4,
                   0xDD, 0x4E, 0x55, 0x6C, 0x9D, 0xF1, 0xD2, 0x1D,
                   0x28, 0x10, 0x4F, 0x8B],
            r vec![0x16, 0xC3, 0x49, 0x1F, 0x9B, 0x8C, 0x3F, 0xBB,
                   0xDD, 0x5E, 0x7A, 0x7B, 0x66, 0x70, 0x57, 0xF0,
                   0xD8, 0xEE, 0x8E, 0x1B],
            s vec![0x02, 0xC3, 0x6A, 0x12, 0x7A, 0x7B, 0x89, 0xED,
                   0xBB, 0x72, 0xE4, 0xFF, 0xBC, 0x71, 0xDA, 0xBC,
                   0x7D, 0x4F, 0xC6, 0x9C]);
        // With SHA-1, message = "test":
        //    k = 5C842DF4F9E344EE09F056838B42C7A17F4A6433
        //    r = 42AB2052FD43E123F0607F115052A67DCD9C5C77
        //    s = 183916B0230D45B9931491D4C6B0BD2FB4AAF088
        run_rfc6979_test!(Sha1, test, public, private,
            k vec![0x5C, 0x84, 0x2D, 0xF4, 0xF9, 0xE3, 0x44, 0xEE,
                   0x09, 0xF0, 0x56, 0x83, 0x8B, 0x42, 0xC7, 0xA1,
                   0x7F, 0x4A, 0x64, 0x33],
            r vec![0x42, 0xAB, 0x20, 0x52, 0xFD, 0x43, 0xE1, 0x23,
                   0xF0, 0x60, 0x7F, 0x11, 0x50, 0x52, 0xA6, 0x7D,
                   0xCD, 0x9C, 0x5C, 0x77],
            s vec![0x18, 0x39, 0x16, 0xB0, 0x23, 0x0D, 0x45, 0xB9,
                   0x93, 0x14, 0x91, 0xD4, 0xC6, 0xB0, 0xBD, 0x2F,
                   0xB4, 0xAA, 0xF0, 0x88]);
        // With SHA-224, message = "test":
        //    k = 4598B8EFC1A53BC8AECD58D1ABBB0C0C71E67297
        //    r = 6868E9964E36C1689F6037F91F28D5F2C30610F2
        //    s = 49CEC3ACDC83018C5BD2674ECAAD35B8CD22940F
        run_rfc6979_test!(Sha224, test, public, private,
            k vec![0x45, 0x98, 0xB8, 0xEF, 0xC1, 0xA5, 0x3B, 0xC8,
                   0xAE, 0xCD, 0x58, 0xD1, 0xAB, 0xBB, 0x0C, 0x0C,
                   0x71, 0xE6, 0x72, 0x97],
            r vec![0x68, 0x68, 0xE9, 0x96, 0x4E, 0x36, 0xC1, 0x68,
                   0x9F, 0x60, 0x37, 0xF9, 0x1F, 0x28, 0xD5, 0xF2,
                   0xC3, 0x06, 0x10, 0xF2],
            s vec![0x49, 0xCE, 0xC3, 0xAC, 0xDC, 0x83, 0x01, 0x8C,
                   0x5B, 0xD2, 0x67, 0x4E, 0xCA, 0xAD, 0x35, 0xB8,
                   0xCD, 0x22, 0x94, 0x0F]);
        // With SHA-256, message = "test":
        //    k = 5A67592E8128E03A417B0484410FB72C0B630E1A
        //    r = 22518C127299B0F6FDC9872B282B9E70D0790812
        //    s = 6837EC18F150D55DE95B5E29BE7AF5D01E4FE160
        run_rfc6979_test!(Sha256, test, public, private,
            k vec![0x5A, 0x67, 0x59, 0x2E, 0x81, 0x28, 0xE0, 0x3A,
                   0x41, 0x7B, 0x04, 0x84, 0x41, 0x0F, 0xB7, 0x2C,
                   0x0B, 0x63, 0x0E, 0x1A],
            r vec![0x22, 0x51, 0x8C, 0x12, 0x72, 0x99, 0xB0, 0xF6,
                   0xFD, 0xC9, 0x87, 0x2B, 0x28, 0x2B, 0x9E, 0x70,
                   0xD0, 0x79, 0x08, 0x12],
            s vec![0x68, 0x37, 0xEC, 0x18, 0xF1, 0x50, 0xD5, 0x5D,
                   0xE9, 0x5B, 0x5E, 0x29, 0xBE, 0x7A, 0xF5, 0xD0,
                   0x1E, 0x4F, 0xE1, 0x60]);
        // With SHA-384, message = "test":
        //    k = 220156B761F6CA5E6C9F1B9CF9C24BE25F98CD89
        //    r = 854CF929B58D73C3CBFDC421E8D5430CD6DB5E66
        //    s = 91D0E0F53E22F898D158380676A871A157CDA622
        run_rfc6979_test!(Sha384, test, public, private,
            k vec![0x22, 0x01, 0x56, 0xB7, 0x61, 0xF6, 0xCA, 0x5E,
                   0x6C, 0x9F, 0x1B, 0x9C, 0xF9, 0xC2, 0x4B, 0xE2,
                   0x5F, 0x98, 0xCD, 0x89],
            r vec![0x85, 0x4C, 0xF9, 0x29, 0xB5, 0x8D, 0x73, 0xC3,
                   0xCB, 0xFD, 0xC4, 0x21, 0xE8, 0xD5, 0x43, 0x0C,
                   0xD6, 0xDB, 0x5E, 0x66],
            s vec![0x91, 0xD0, 0xE0, 0xF5, 0x3E, 0x22, 0xF8, 0x98,
                   0xD1, 0x58, 0x38, 0x06, 0x76, 0xA8, 0x71, 0xA1,
                   0x57, 0xCD, 0xA6, 0x22]);
        // With SHA-512, message = "test":
        //    k = 65D2C2EEB175E370F28C75BFCDC028D22C7DBE9C
        //    r = 8EA47E475BA8AC6F2D821DA3BD212D11A3DEB9A0
        //    s = 7C670C7AD72B6C050C109E1790008097125433E8
        run_rfc6979_test!(Sha512, test, public, private,
            k vec![0x65, 0xD2, 0xC2, 0xEE, 0xB1, 0x75, 0xE3, 0x70,
                   0xF2, 0x8C, 0x75, 0xBF, 0xCD, 0xC0, 0x28, 0xD2,
                   0x2C, 0x7D, 0xBE, 0x9C],
            r vec![0x8E, 0xA4, 0x7E, 0x47, 0x5B, 0xA8, 0xAC, 0x6F,
                   0x2D, 0x82, 0x1D, 0xA3, 0xBD, 0x21, 0x2D, 0x11,
                   0xA3, 0xDE, 0xB9, 0xA0],
            s vec![0x7C, 0x67, 0x0C, 0x7A, 0xD7, 0x2B, 0x6C, 0x05,
                   0x0C, 0x10, 0x9E, 0x17, 0x90, 0x00, 0x80, 0x97,
                   0x12, 0x54, 0x33, 0xE8]);
    }

}
