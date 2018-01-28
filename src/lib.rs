//! A simple DSA library.
//!
//! The library performs all the standard bits and pieces that you'd expect
//! from a DSA/ECDSA library, and does so using only Rust. It's a bit slow,
//! but it works.
//!
//! Users considering new cryptographic systems should definitely use the
//! newer ECDSA routines, rather than DSA. We've included DSA in this
//! library largely to support legacy systems.
//!
extern crate digest;
extern crate hmac;
extern crate num;
extern crate rand;
extern crate sha1;
extern crate sha2;
extern crate simple_asn1;

pub mod dsa;
pub mod ecdsa;
mod math;
mod rfc6979;
mod sig;

pub use sig::*;
