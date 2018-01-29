use digest::{BlockInput,FixedOutput,Input};
use digest::generic_array::ArrayLength;
use hmac::Hmac;
use math::{divmod,modinv};
use num::{BigInt,BigUint,Integer,One,Signed,Zero};
use num::bigint::Sign;
use rand::{Rng,OsRng};
use rfc6979::{KIterator,bits2int};
use sig::DSASignature;
use simple_asn1::{ASN1Block,ASN1Class,ASN1DecodeErr,ASN1EncodeErr,
                  FromASN1,OID,ToASN1};
use std::cmp::min;

#[allow(non_snake_case)]
#[derive(Clone,Debug,PartialEq)]
pub struct EllipticCurve {
    pub p: BigUint,
    pub n: BigUint,
    pub SEED: BigUint,
    pub c: BigUint,
    pub a: BigUint,
    pub b: BigUint,
    pub Gx: BigInt,
    pub Gy: BigInt
}

impl EllipticCurve {
    /// Create a new elliptic curve structure that represents NIST's
    /// p192 curve. (secp192r1)
    pub fn p192() -> EllipticCurve {
        EllipticCurve {
            p:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
            n:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0x99, 0xde, 0xf8, 0x36,
                        0x14, 0x6b, 0xc9, 0xb1, 0xb4, 0xd2, 0x28, 0x31]),
            SEED:   BigUint::from_bytes_be(&vec![
                        0x30, 0x45, 0xae, 0x6f, 0xc8, 0x42, 0x2f, 0x64,
                        0xed, 0x57, 0x95, 0x28, 0xd3, 0x81, 0x20, 0xea,
                        0xe1, 0x21, 0x96, 0xd5]),
            c:      BigUint::from_bytes_be(&vec![
                        0x30, 0x99, 0xd2, 0xbb, 0xbf, 0xcb, 0x25, 0x38,
                        0x54, 0x2d, 0xcd, 0x5f, 0xb0, 0x78, 0xb6, 0xef,
                        0x5f, 0x3d, 0x6f, 0xe2, 0xc7, 0x45, 0xde, 0x65]),
            a:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfc]),
            b:      BigUint::from_bytes_be(&vec![
                        0x64, 0x21, 0x05, 0x19, 0xe5, 0x9c, 0x80, 0xe7,
                        0x0f, 0xa7, 0xe9, 0xab, 0x72, 0x24, 0x30, 0x49,
                        0xfe, 0xb8, 0xde, 0xec, 0xc1, 0x46, 0xb9, 0xb1]),
            Gx:     BigInt::from_bytes_be(Sign::Plus, &vec![
                        0x18, 0x8d, 0xa8, 0x0e, 0xb0, 0x30, 0x90, 0xf6,
                        0x7c, 0xbf, 0x20, 0xeb, 0x43, 0xa1, 0x88, 0x00,
                        0xf4, 0xff, 0x0a, 0xfd, 0x82, 0xff, 0x10, 0x12]),
            Gy:     BigInt::from_bytes_be(Sign::Plus, &vec![
                        0x07, 0x19, 0x2b, 0x95, 0xff, 0xc8, 0xda, 0x78,
                        0x63, 0x10, 0x11, 0xed, 0x6b, 0x24, 0xcd, 0xd5,
                        0x73, 0xf9, 0x77, 0xa1, 0x1e, 0x79, 0x48, 0x11])
        }
    }

    /// Create a new elliptic curve structure that represents NIST's
    /// p224 curve. (secp224r1)
    pub fn p224() -> EllipticCurve {
        EllipticCurve {
            p:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                        0x00, 0x00, 0x00, 0x01]),
            n:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0xa2,
                        0xe0, 0xb8, 0xf0, 0x3e, 0x13, 0xdd, 0x29, 0x45,
                        0x5c, 0x5c, 0x2a, 0x3d]),
            SEED:   BigUint::from_bytes_be(&vec![
                        0xbd, 0x71, 0x34, 0x47, 0x99, 0xd5, 0xc7, 0xfc,
                        0xdc, 0x45, 0xb5, 0x9f, 0xa3, 0xb9, 0xab, 0x8f,
                        0x6a, 0x94, 0x8b, 0xc5]),
            c:      BigUint::from_bytes_be(&vec![
                        0x5b, 0x05, 0x6c, 0x7e, 0x11, 0xdd, 0x68, 0xf4,
                        0x04, 0x69, 0xee, 0x7f, 0x3c, 0x7a, 0x7d, 0x74,
                        0xf7, 0xd1, 0x21, 0x11, 0x65, 0x06, 0xd0, 0x31,
                        0x21, 0x82, 0x91, 0xfb]),
            a:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xfe]),
            b:      BigUint::from_bytes_be(&vec![
                        0xb4, 0x05, 0x0a, 0x85, 0x0c, 0x04, 0xb3, 0xab,
                        0xf5, 0x41, 0x32, 0x56, 0x50, 0x44, 0xb0, 0xb7,
                        0xd7, 0xbf, 0xd8, 0xba, 0x27, 0x0b, 0x39, 0x43,
                        0x23, 0x55, 0xff, 0xb4]),
            Gx:      BigInt::from_bytes_be(Sign::Plus, &vec![
                        0xb7, 0x0e, 0x0c, 0xbd, 0x6b, 0xb4, 0xbf, 0x7f,
                        0x32, 0x13, 0x90, 0xb9, 0x4a, 0x03, 0xc1, 0xd3,
                        0x56, 0xc2, 0x11, 0x22, 0x34, 0x32, 0x80, 0xd6,
                        0x11, 0x5c, 0x1d, 0x21]),
            Gy:      BigInt::from_bytes_be(Sign::Plus, &vec![
                        0xbd, 0x37, 0x63, 0x88, 0xb5, 0xf7, 0x23, 0xfb,
                        0x4c, 0x22, 0xdf, 0xe6, 0xcd, 0x43, 0x75, 0xa0,
                        0x5a, 0x07, 0x47, 0x64, 0x44, 0xd5, 0x81, 0x99,
                        0x85, 0x00, 0x7e, 0x34])
        }
    }

    /// Create a new elliptic curve structure that represents NIST's
    /// p256 curve. (secp256r1)
    pub fn p256() -> EllipticCurve {
        EllipticCurve {
            p:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01,
                        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                        0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
            n:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84,
                        0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51]),
            SEED:   BigUint::from_bytes_be(&vec![
                        0xc4, 0x9d, 0x36, 0x08, 0x86, 0xe7, 0x04, 0x93,
                        0x6a, 0x66, 0x78, 0xe1, 0x13, 0x9d, 0x26, 0xb7,
                        0x81, 0x9f, 0x7e, 0x90]),
            c:      BigUint::from_bytes_be(&vec![
                        0x7e, 0xfb, 0xa1, 0x66, 0x29, 0x85, 0xbe, 0x94,
                        0x03, 0xcb, 0x05, 0x5c, 0x75, 0xd4, 0xf7, 0xe0,
                        0xce, 0x8d, 0x84, 0xa9, 0xc5, 0x11, 0x4a, 0xbc,
                        0xaf, 0x31, 0x77, 0x68, 0x01, 0x04, 0xfa, 0x0d]),
            a:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01,
                        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                        0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfc]),
            b:      BigUint::from_bytes_be(&vec![
                        0x5a, 0xc6, 0x35, 0xd8, 0xaa, 0x3a, 0x93, 0xe7,
                        0xb3, 0xeb, 0xbd, 0x55, 0x76, 0x98, 0x86, 0xbc,
                        0x65, 0x1d, 0x06, 0xb0, 0xcc, 0x53, 0xb0, 0xf6,
                        0x3b, 0xce, 0x3c, 0x3e, 0x27, 0xd2, 0x60, 0x4b]),
            Gx:      BigInt::from_bytes_be(Sign::Plus, &vec![
                        0x6b, 0x17, 0xd1, 0xf2, 0xe1, 0x2c, 0x42, 0x47,
                        0xf8, 0xbc, 0xe6, 0xe5, 0x63, 0xa4, 0x40, 0xf2,
                        0x77, 0x03, 0x7d, 0x81, 0x2d, 0xeb, 0x33, 0xa0,
                        0xf4, 0xa1, 0x39, 0x45, 0xd8, 0x98, 0xc2, 0x96]),
            Gy:      BigInt::from_bytes_be(Sign::Plus, &vec![
                        0x4f, 0xe3, 0x42, 0xe2, 0xfe, 0x1a, 0x7f, 0x9b,
                        0x8e, 0xe7, 0xeb, 0x4a, 0x7c, 0x0f, 0x9e, 0x16,
                        0x2b, 0xce, 0x33, 0x57, 0x6b, 0x31, 0x5e, 0xce,
                        0xcb, 0xb6, 0x40, 0x68, 0x37, 0xbf, 0x51, 0xf5])
        }
    }

    /// Create a new elliptic curve structure that represents NIST's
    /// p384 curve. (secp384r1)
    pub fn p384() -> EllipticCurve {
        EllipticCurve {
            p:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
                        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00,
                        0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff]),
            n:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xc7, 0x63, 0x4d, 0x81, 0xf4, 0x37, 0x2d, 0xdf,
                        0x58, 0x1a, 0x0d, 0xb2, 0x48, 0xb0, 0xa7, 0x7a,
                        0xec, 0xec, 0x19, 0x6a, 0xcc, 0xc5, 0x29, 0x73]),
            SEED:   BigUint::from_bytes_be(&vec![
                        0xa3, 0x35, 0x92, 0x6a, 0xa3, 0x19, 0xa2, 0x7a,
                        0x1d, 0x00, 0x89, 0x6a, 0x67, 0x73, 0xa4, 0x82,
                        0x7a, 0xcd, 0xac, 0x73]),
            c:      BigUint::from_bytes_be(&vec![
                        0x79, 0xd1, 0xe6, 0x55, 0xf8, 0x68, 0xf0, 0x2f,
                        0xff, 0x48, 0xdc, 0xde, 0xe1, 0x41, 0x51, 0xdd,
                        0xb8, 0x06, 0x43, 0xc1, 0x40, 0x6d, 0x0c, 0xa1,
                        0x0d, 0xfe, 0x6f, 0xc5, 0x20, 0x09, 0x54, 0x0a,
                        0x49, 0x5e, 0x80, 0x42, 0xea, 0x5f, 0x74, 0x4f,
                        0x6e, 0x18, 0x46, 0x67, 0xcc, 0x72, 0x24, 0x83]),
            a:      BigUint::from_bytes_be(&vec![
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
                        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00,
                        0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xfc]),
            b:      BigUint::from_bytes_be(&vec![
                        0xb3, 0x31, 0x2f, 0xa7, 0xe2, 0x3e, 0xe7, 0xe4,
                        0x98, 0x8e, 0x05, 0x6b, 0xe3, 0xf8, 0x2d, 0x19,
                        0x18, 0x1d, 0x9c, 0x6e, 0xfe, 0x81, 0x41, 0x12,
                        0x03, 0x14, 0x08, 0x8f, 0x50, 0x13, 0x87, 0x5a,
                        0xc6, 0x56, 0x39, 0x8d, 0x8a, 0x2e, 0xd1, 0x9d,
                        0x2a, 0x85, 0xc8, 0xed, 0xd3, 0xec, 0x2a, 0xef]),
            Gx:      BigInt::from_bytes_be(Sign::Plus, &vec![
                        0xaa, 0x87, 0xca, 0x22, 0xbe, 0x8b, 0x05, 0x37,
                        0x8e, 0xb1, 0xc7, 0x1e, 0xf3, 0x20, 0xad, 0x74,
                        0x6e, 0x1d, 0x3b, 0x62, 0x8b, 0xa7, 0x9b, 0x98,
                        0x59, 0xf7, 0x41, 0xe0, 0x82, 0x54, 0x2a, 0x38,
                        0x55, 0x02, 0xf2, 0x5d, 0xbf, 0x55, 0x29, 0x6c,
                        0x3a, 0x54, 0x5e, 0x38, 0x72, 0x76, 0x0a, 0xb7]),
            Gy:      BigInt::from_bytes_be(Sign::Plus, &vec![
                        0x36, 0x17, 0xde, 0x4a, 0x96, 0x26, 0x2c, 0x6f,
                        0x5d, 0x9e, 0x98, 0xbf, 0x92, 0x92, 0xdc, 0x29,
                        0xf8, 0xf4, 0x1d, 0xbd, 0x28, 0x9a, 0x14, 0x7c,
                        0xe9, 0xda, 0x31, 0x13, 0xb5, 0xf0, 0xb8, 0xc0,
                        0x0a, 0x60, 0xb1, 0xce, 0x1d, 0x7e, 0x81, 0x9d,
                        0x7a, 0x43, 0x1d, 0x7c, 0x90, 0xea, 0x0e, 0x5f])
        }
    }

    /// Create a new elliptic curve structure that represents NIST's
    /// p521 curve. (secp521r1)
    pub fn p521() -> EllipticCurve {
        EllipticCurve {
            p:      BigUint::from_bytes_be(&vec![
                        0x01, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff]),
            n:      BigUint::from_bytes_be(&vec![
                        0x01, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xfa, 0x51, 0x86, 0x87, 0x83, 0xbf, 0x2f,
                        0x96, 0x6b, 0x7f, 0xcc, 0x01, 0x48, 0xf7, 0x09,
                        0xa5, 0xd0, 0x3b, 0xb5, 0xc9, 0xb8, 0x89, 0x9c,
                        0x47, 0xae, 0xbb, 0x6f, 0xb7, 0x1e, 0x91, 0x38,
                        0x64, 0x09]),
            SEED:   BigUint::from_bytes_be(&vec![
                        0xd0, 0x9e, 0x88, 0x00, 0x29, 0x1c, 0xb8, 0x53,
                        0x96, 0xcc, 0x67, 0x17, 0x39, 0x32, 0x84, 0xaa,
                        0xa0, 0xda, 0x64, 0xba]),
            c:      BigUint::from_bytes_be(&vec![
                        0xb4, 0x8b, 0xfa, 0x5f, 0x42, 0x0a, 0x34, 0x94,
                        0x95, 0x39, 0xd2, 0xbd, 0xfc, 0x26, 0x4e, 0xee,
                        0xeb, 0x07, 0x76, 0x88, 0xe4, 0x4f, 0xbf, 0x0a,
                        0xd8, 0xf6, 0xd0, 0xed, 0xb3, 0x7b, 0xd6, 0xb5,
                        0x33, 0x28, 0x10, 0x00, 0x51, 0x8e, 0x19, 0xf1,
                        0xb9, 0xff, 0xbe, 0x0f, 0xe9, 0xed, 0x8a, 0x3c,
                        0x22, 0x00, 0xb8, 0xf8, 0x75, 0xe5, 0x23, 0x86,
                        0x8c, 0x70, 0xc1, 0xe5, 0xbf, 0x55, 0xba, 0xd6,
                        0x37]),
            a:      BigUint::from_bytes_be(&vec![
                        0x01, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xfc]),
            b:      BigUint::from_bytes_be(&vec![
                        0x51, 0x95, 0x3e, 0xb9, 0x61, 0x8e, 0x1c, 0x9a,
                        0x1f, 0x92, 0x9a, 0x21, 0xa0, 0xb6, 0x85, 0x40,
                        0xee, 0xa2, 0xda, 0x72, 0x5b, 0x99, 0xb3, 0x15,
                        0xf3, 0xb8, 0xb4, 0x89, 0x91, 0x8e, 0xf1, 0x09,
                        0xe1, 0x56, 0x19, 0x39, 0x51, 0xec, 0x7e, 0x93,
                        0x7b, 0x16, 0x52, 0xc0, 0xbd, 0x3b, 0xb1, 0xbf,
                        0x07, 0x35, 0x73, 0xdf, 0x88, 0x3d, 0x2c, 0x34,
                        0xf1, 0xef, 0x45, 0x1f, 0xd4, 0x6b, 0x50, 0x3f,
                        0x00]),
            Gx:      BigInt::from_bytes_be(Sign::Plus, &vec![
                        0xc6, 0x85, 0x8e, 0x06, 0xb7, 0x04, 0x04, 0xe9,
                        0xcd, 0x9e, 0x3e, 0xcb, 0x66, 0x23, 0x95, 0xb4,
                        0x42, 0x9c, 0x64, 0x81, 0x39, 0x05, 0x3f, 0xb5,
                        0x21, 0xf8, 0x28, 0xaf, 0x60, 0x6b, 0x4d, 0x3d,
                        0xba, 0xa1, 0x4b, 0x5e, 0x77, 0xef, 0xe7, 0x59,
                        0x28, 0xfe, 0x1d, 0xc1, 0x27, 0xa2, 0xff, 0xa8,
                        0xde, 0x33, 0x48, 0xb3, 0xc1, 0x85, 0x6a, 0x42,
                        0x9b, 0xf9, 0x7e, 0x7e, 0x31, 0xc2, 0xe5, 0xbd,
                        0x66]),
            Gy:      BigInt::from_bytes_be(Sign::Plus, &vec![
                        0x18, 0x39, 0x29, 0x6a, 0x78, 0x9a, 0x3b, 0xc0,
                        0x04, 0x5c, 0x8a, 0x5f, 0xb4, 0x2c, 0x7d, 0x1b,
                        0xd9, 0x98, 0xf5, 0x44, 0x49, 0x57, 0x9b, 0x44,
                        0x68, 0x17, 0xaf, 0xbd, 0x17, 0x27, 0x3e, 0x66,
                        0x2c, 0x97, 0xee, 0x72, 0x99, 0x5e, 0xf4, 0x26,
                        0x40, 0xc5, 0x50, 0xb9, 0x01, 0x3f, 0xad, 0x07,
                        0x61, 0x35, 0x3c, 0x70, 0x86, 0xa2, 0x72, 0xc2,
                        0x40, 0x88, 0xbe, 0x94, 0x76, 0x9f, 0xd1, 0x66,
                        0x50])
        }
    }
}

#[derive(Debug)]
pub enum ECDSAError {
    ASN1DecodeErr(ASN1DecodeErr),
    ASN1EncodeErr(ASN1EncodeErr),
    UnrecognizedCurve,
    InvalidCurvePoint
}

impl From<ASN1DecodeErr> for ECDSAError {
    fn from(e: ASN1DecodeErr) -> ECDSAError {
        ECDSAError::ASN1DecodeErr(e)
    }
}

impl From<ASN1EncodeErr> for ECDSAError {
    fn from(e: ASN1EncodeErr) -> ECDSAError {
        ECDSAError::ASN1EncodeErr(e)
    }
}

impl FromASN1 for EllipticCurve {
    type Error = ECDSAError;

    fn from_asn1(b: &[ASN1Block])
        -> Result<(EllipticCurve, &[ASN1Block]),ECDSAError>
    {
        match b.split_first() {
            None =>
                Err(ECDSAError::from(ASN1DecodeErr::EmptyBuffer)),
            Some((&ASN1Block::ObjectIdentifier(_, _, ref oid), rest)) => {
                if oid == oid!(1,2,840,10045,3,1,1,1) {
                    return Ok((EllipticCurve::p192(), rest))
                }
                if oid == oid!(1,3,132,0,33) {
                    return Ok((EllipticCurve::p224(), rest))
                }
                if oid == oid!(1,2,840,10045,3,1,1,7) {
                    return Ok((EllipticCurve::p256(), rest))
                }
                if oid == oid!(1,3,132,0,34) {
                    return Ok((EllipticCurve::p384(), rest))
                }
                if oid == oid!(1,3,132,0,35) {
                    return Ok((EllipticCurve::p521(), rest))
                }
                Err(ECDSAError::UnrecognizedCurve)
            }
            Some(_) =>
                Err(ECDSAError::UnrecognizedCurve)
        }
    }
}

impl ToASN1 for EllipticCurve {
    type Error = ECDSAError;

    fn to_asn1_class(&self, c: ASN1Class)
        -> Result<Vec<ASN1Block>, ECDSAError>
    {
        if self == &EllipticCurve::p192() {
            let oid = oid!(1,2,840,10045,3,1,1,1);
            return Ok(vec![ASN1Block::ObjectIdentifier(c, 0, oid)]);
        }
        if self == &EllipticCurve::p224() {
            let oid = oid!(1,3,132,0,33);
            return Ok(vec![ASN1Block::ObjectIdentifier(c, 0, oid)]);
        }
        if self == &EllipticCurve::p256() {
            let oid = oid!(1,2,840,10045,3,1,1,7);
            return Ok(vec![ASN1Block::ObjectIdentifier(c, 0, oid)]);
        }
        if self == &EllipticCurve::p384() {
            let oid = oid!(1,3,132,0,34);
            return Ok(vec![ASN1Block::ObjectIdentifier(c, 0, oid)]);
        }
        if self == &EllipticCurve::p521() {
            let oid = oid!(1,3,132,0,35);
            return Ok(vec![ASN1Block::ObjectIdentifier(c, 0, oid)]);
        }
        return Err(ECDSAError::UnrecognizedCurve)
    }
}

#[allow(non_snake_case)]
#[derive(Clone,Debug,PartialEq)]
pub struct ECCPoint {
    pub curve: EllipticCurve,
    pub x: BigInt,
    pub y: BigInt
}

impl ECCPoint {
    /// Generate the provided point on the given curve. This function returns
    /// a `Result` because it will validate that the point created is actually
    /// on the curve.
    pub fn new(ec: &EllipticCurve, x: BigInt, y: BigInt)
        -> Result<ECCPoint,ECDSAError>
    {
        if x.is_negative() || y.is_negative() {
            return Err(ECDSAError::InvalidCurvePoint);
        }

        let xu = x.to_biguint().unwrap();
        let yu = y.to_biguint().unwrap();

        if (&xu >= &ec.p) || (&yu >= &ec.p) {
            return Err(ECDSAError::InvalidCurvePoint);
        }

        let y2 = (&yu * &yu) % &ec.p;
        let x3axb = ((&xu * &xu * &xu) + (&ec.a * &xu) + &ec.b) % &ec.p;

        if y2 != x3axb {
            return Err(ECDSAError::InvalidCurvePoint);
        }

        Ok(ECCPoint {
            curve: ec.clone(),
            x: x,
            y: y
        })
    }

    /// Generate the default point G for the given elliptic curve.
    pub fn default(ec: &EllipticCurve) -> ECCPoint {
        ECCPoint {
            curve: ec.clone(),
            x: ec.Gx.clone(),
            y: ec.Gy.clone()
        }
    }

    /// Double the given point along the curve.
    pub fn double(&self) -> ECCPoint {
        let ua = BigInt::from_biguint(Sign::Plus, self.curve.a.clone());
        let up = BigInt::from_biguint(Sign::Plus, self.curve.p.clone());
        // lambda = (3 * xp ^ 2 + a) / 2 yp
        let xpsq = &self.x * &self.x;
        let lambda_top = &(&BigInt::from(3) * &xpsq) + &ua;
        let lambda_bot = &self.y << 1;
        let lambda = divmod(&lambda_top, &lambda_bot, &self.curve.p);
        // xr = lambda ^ 2 - 2 xp
        let xr_left = &lambda * &lambda;
        let xr_right = &self.x << 1;
        let xr = (xr_left - xr_right).mod_floor(&up);
        // yr = lambda (xp - xr) - yp
        let xdiff = &self.x - &xr;
        let yr_left = &lambda * &xdiff;
        let yr = (&yr_left - &self.y).mod_floor(&up);
        //
        ECCPoint{ curve: self.curve.clone(), x: xr, y: yr }
    }

    /// Add this point to another point, returning the new point.
    pub fn add(&self, other: &ECCPoint) -> ECCPoint {
        assert!(self.curve == other.curve);
        let xdiff = &self.x - &other.x;
        let ydiff = &self.y - &other.y;
        let s = divmod(&ydiff, &xdiff, &self.curve.p);
        let pp = BigInt::from_biguint(Sign::Plus, self.curve.p.clone());
        let xr = (&(&s * &s) - &self.x - &other.x).mod_floor(&pp);
        let yr = (&s * (&self.x - &xr) - &self.y).mod_floor(&pp);
        ECCPoint{ curve: self.curve.clone(), x: xr, y: yr }
    }

    /// Scale this point by the given factor.
    pub fn scale(&self, d: &BigUint) -> ECCPoint {
        assert!(!d.is_zero());
        let one: BigUint = One::one();
        #[allow(non_snake_case)]
        let mut Q = self.clone();
        let i = d.bits() - 2;
        let mut mask = &one << i;

        while !mask.is_zero() {
            Q = Q.double();

            let test = d & &mask;
            if !test.is_zero() {
                Q = Q.add(&self);
            }
            mask >>= 1;
        }

        Q
    }
}


#[derive(Clone,Debug,PartialEq)]
pub struct ECCKeyPair {
    pub private: ECCPrivateKey,
    pub public:  ECCPublicKey
}

impl ECCKeyPair {
    /// Generate new key pair against the given curve. This uses `OsRng` under
    /// the hood, which is supposed to be pretty good.
    pub fn generate(params: &EllipticCurve)
        -> ECCKeyPair
    {
        let mut rng = OsRng::new().unwrap();
        ECCKeyPair::generate_w_rng(&mut rng, params)

    }

    /// Generate a new key pair, but use the given RNG. You should pick a
    /// good one.
    pub fn generate_w_rng<G: Rng>(rng: &mut G, params: &EllipticCurve)
        -> ECCKeyPair
    {
        let one: BigUint = One::one();
        #[allow(non_snake_case)]
        let N = params.n.bits();
        let bits_to_generate = N + 64;
        let bytes_to_generate = (bits_to_generate + 7) / 8;
        let bits: Vec<u8> = rng.gen_iter().take(bytes_to_generate).collect();
        let bits_generated = bytes_to_generate * 8;
        let mut c = BigUint::from_bytes_be(&bits);
        c >>= bits_generated - bits_to_generate;
        let nm1 = &params.n - &one;
        let d = c.mod_floor(&nm1) + &one;
        #[allow(non_snake_case)]
        let Q = ECCPoint::default(params).scale(&d);
        ECCKeyPair {
            private: ECCPrivateKey {
                curve: params.clone(),
                d: d
            },
            public: ECCPublicKey {
                curve: params.clone(),
                Q: Q
            }
        }
    }
}

#[derive(Clone,Debug,PartialEq)]
pub struct ECCPrivateKey {
    pub curve: EllipticCurve,
    d: BigUint
}

impl ECCPrivateKey {
    /// Instantiate a private key against the given curve and value.
    pub fn new(c: &EllipticCurve, d: &BigUint) -> ECCPrivateKey {
        ECCPrivateKey {
            curve: c.clone(),
            d: d.clone()
        }
    }

    /// Sign a message. This uses the deterministic k-generation algorithm
    /// described in RFC 6979, so should be fairly robust against collisions
    /// in k, even without the use of a random number source.
    pub fn sign<Hash>(&self, m: &[u8]) -> DSASignature
      where
        Hash: Clone + BlockInput + Input + FixedOutput + Default,
        Hmac<Hash>: Clone,
        Hash::BlockSize: ArrayLength<u8>
    {
        let q = self.curve.n.clone();
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
        let n = self.curve.p.bits();
        let h1: Vec<u8> = digest.fixed_result()
                                .as_slice()
                                .iter()
                                .map(|x| *x)
                                .collect();
        let h0 = bits2int(&h1, n);
        let h = h0.mod_floor(&q);

        // 2.  A random value modulo q, dubbed k, is generated.  That value
        //     shall not be 0; hence, it lies in the [1, q-1] range.  Most
        //     of the remainder of this document will revolve around the
        //     process used to generate k.  In plain DSA or ECDSA, k should
        //     be selected through a random selection that chooses a value
        //     among the q-1 possible values with uniform probability.
        for k in KIterator::<Hash>::new(&h1, n, &self.curve.n, &self.curve.b) {
            // 3. A value r (modulo q) is computed from k and the key
            //    parameters:
            //     *  For DSA ...
            //     *  For ECDSA: the point kG is computed; its X coordinate (a
            //        member of the field over which E is defined) is converted
            //        to an integer, which is reduced modulo q, yielding r.
            //
            //    If r turns out to be zero, a new k should be selected and r
            //    computed again (this is an utterly improbable occurrence).
            let g = ECCPoint::default(&self.curve);
            let kg = g.scale(&k);
            let qi = BigInt::from_biguint(Sign::Plus, self.curve.n.clone());
            let r = kg.x.mod_floor(&qi);
            if r.is_zero() {
                continue;
            }
            // 4.  The value s (modulo q) is computed:
            //
            //           s = (h+x*r)/k mod q
            //
            //     The pair (r, s) is the signature.
            let kinv = BigInt::from_biguint(Sign::Plus, modinv(&k, &q));
            let di = BigInt::from_biguint(Sign::Plus, self.d.clone());
            let hi = BigInt::from_biguint(Sign::Plus, h);
            let s = ((&hi + (&di * &r)) * &kinv) % &qi;

            assert!(r.is_positive());
            assert!(s.is_positive());
            let ru = r.to_biguint().unwrap();
            let su = s.to_biguint().unwrap();
            return DSASignature{ r: ru, s: su };
        }
        panic!("The world is broken; couldn't find a k in sign().");
    }
}

#[allow(non_snake_case)]
#[derive(Clone,Debug,PartialEq)]
pub struct ECCPublicKey {
    pub curve: EllipticCurve,
    pub Q: ECCPoint
}

impl ECCPublicKey {
    /// Instantiate the given public key.
    pub fn new(curve: &EllipticCurve, point: &ECCPoint) -> ECCPublicKey {
        ECCPublicKey {
            curve: curve.clone(),
            Q: point.clone()
        }
    }

    /// Verify a signature of a message, using the associated hash function
    /// for this message.
    pub fn verify<Hash>(&self, m: &[u8], sig: &DSASignature) -> bool
      where Hash: Clone + Default + Input + FixedOutput
    {
        // (from wikipedia, of all places)
        // 1. Verify that r and s are integers in [1,n-1]. If not, the
        //    signature is invalid.
        if sig.r >= self.curve.n {
            return false;
        }
        if sig.s >= self.curve.n {
            return false;
        }
        // 2. Calculate e = HASH(m), where HASH is the same function used
        //    in the signature generation.
        // 3. Let z be the L_n leftmost bits of e.
        let mut digest = <Hash>::default();
        digest.process(m);
        let z = { let mut bytes: Vec<u8> = digest.fixed_result()
                                                 .as_slice()
                                                 .iter()
                                                 .map(|x| *x)
                                                 .collect();
                  let n = self.curve.n.bits();
                  let len = min(n / 8, bytes.len());
                  bytes.truncate(len);
                  BigUint::from_bytes_be(&bytes) };
        // 4. Calculate w = (s)^-1 mod n;
        let w = modinv(&sig.s, &self.curve.n);
        // 5. Calculate u1 = zw mod n and u2 = rw mod n
        let u1 = (&z * &w).mod_floor(&self.curve.n);
        let u2 = (&sig.r * &w).mod_floor(&self.curve.n);
        // 6. Calculate the curve point (x1, y1) = u1 * G + u2 * Qa. If
        // (x1, y1) = O then the signature is invalid.
        let curve_g = ECCPoint::default(&self.curve);
        let v = curve_g.scale(&u1).add(&self.Q.scale(&u2));
        // if v = r, then the signature is verified
        match v.x.to_biguint() {
            None => false,
            Some(vu) => vu == sig.r
        }
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Sha256,Sha512};
    use super::*;

    const NUM_TESTS: usize = 20;

    #[test]
    fn p256_double() {
        let xbytes = vec![0x7c, 0xf2, 0x7b, 0x18, 0x8d, 0x03, 0x4f, 0x7e,
                          0x8a, 0x52, 0x38, 0x03, 0x04, 0xb5, 0x1a, 0xc3,
                          0xc0, 0x89, 0x69, 0xe2, 0x77, 0xf2, 0x1b, 0x35,
                          0xa6, 0x0b, 0x48, 0xfc, 0x47, 0x66, 0x99, 0x78];
        let ybytes = vec![0x07, 0x77, 0x55, 0x10, 0xdb, 0x8e, 0xd0, 0x40,
                          0x29, 0x3d, 0x9a, 0xc6, 0x9f, 0x74, 0x30, 0xdb,
                          0xba, 0x7d, 0xad, 0xe6, 0x3c, 0xe9, 0x82, 0x29,
                          0x9e, 0x04, 0xb7, 0x9d, 0x22, 0x78, 0x73, 0xd1];
        let x = BigInt::from_bytes_be(Sign::Plus, &xbytes);
        let y = BigInt::from_bytes_be(Sign::Plus, &ybytes);
        let base = ECCPoint::default(&EllipticCurve::p256());
        let res = base.double();
        let goal = ECCPoint{ curve: base.curve.clone(), x: x, y: y };
        assert_eq!(res, goal);
    }

    #[test]
    fn p256_add() {
        let xbytes = vec![0x5e, 0xcb, 0xe4, 0xd1, 0xa6, 0x33, 0x0a, 0x44,
                          0xc8, 0xf7, 0xef, 0x95, 0x1d, 0x4b, 0xf1, 0x65,
                          0xe6, 0xc6, 0xb7, 0x21, 0xef, 0xad, 0xa9, 0x85,
                          0xfb, 0x41, 0x66, 0x1b, 0xc6, 0xe7, 0xfd, 0x6c];
        let ybytes = vec![0x87, 0x34, 0x64, 0x0c, 0x49, 0x98, 0xff, 0x7e,
                          0x37, 0x4b, 0x06, 0xce, 0x1a, 0x64, 0xa2, 0xec,
                          0xd8, 0x2a, 0xb0, 0x36, 0x38, 0x4f, 0xb8, 0x3d,
                          0x9a, 0x79, 0xb1, 0x27, 0xa2, 0x7d, 0x50, 0x32];
        let x = BigInt::from_bytes_be(Sign::Plus, &xbytes);
        let y = BigInt::from_bytes_be(Sign::Plus, &ybytes);
        let base = ECCPoint::default(&EllipticCurve::p256());
        let res = base.add(&base.double());
        let goal = ECCPoint{ curve: base.curve.clone(), x: x, y: y };
        assert_eq!(res, goal);
    }

    #[test]
    fn p256_scale() {
        let xbytes = vec![0xea, 0x68, 0xd7, 0xb6, 0xfe, 0xdf, 0x0b, 0x71,
                          0x87, 0x89, 0x38, 0xd5, 0x1d, 0x71, 0xf8, 0x72,
                          0x9e, 0x0a, 0xcb, 0x8c, 0x2c, 0x6d, 0xf8, 0xb3,
                          0xd7, 0x9e, 0x8a, 0x4b, 0x90, 0x94, 0x9e, 0xe0];
        let ybytes = vec![0x2a, 0x27, 0x44, 0xc9, 0x72, 0xc9, 0xfc, 0xe7,
                          0x87, 0x01, 0x4a, 0x96, 0x4a, 0x8e, 0xa0, 0xc8,
                          0x4d, 0x71, 0x4f, 0xea, 0xa4, 0xde, 0x82, 0x3f,
                          0xe8, 0x5a, 0x22, 0x4a, 0x4d, 0xd0, 0x48, 0xfa];
        let x = BigInt::from_bytes_be(Sign::Plus, &xbytes);
        let y = BigInt::from_bytes_be(Sign::Plus, &ybytes);
        let base = ECCPoint::default(&EllipticCurve::p256());
        let res = base.scale(&BigUint::from(9 as u64));
        let goal = ECCPoint{ curve: base.curve.clone(), x: x, y: y };
        assert_eq!(res, goal);
    }

    #[test]
    fn p256_sign_verify() {
        for _ in 0..NUM_TESTS {
            let curve = EllipticCurve::p256();
            let pair = ECCKeyPair::generate(&curve);
            let msg = vec![0,0,1,2,3,4,5,0,0];
            let sig = pair.private.sign::<Sha256>(&msg);
            assert!(pair.public.verify::<Sha256>(&msg, &sig));
        }
    }

    #[test]
    fn p384_sign_verify() {
        for _ in 0..NUM_TESTS {
            let curve = EllipticCurve::p384();
            let pair = ECCKeyPair::generate(&curve);
            let msg = vec![0,0,1,2,3,4,5,0,0,9,9];
            let sig = pair.private.sign::<Sha512>(&msg);
            assert!(pair.public.verify::<Sha512>(&msg, &sig));
        }
    }

    fn id_check(curve: EllipticCurve) {
        let blocks = curve.to_asn1().unwrap();
        let (res, _) = EllipticCurve::from_asn1(&blocks).unwrap();
        assert_eq!(curve, res);
    }

    #[test]
    fn curve_ids_right() {
        id_check(EllipticCurve::p192());
        id_check(EllipticCurve::p224());
        id_check(EllipticCurve::p256());
        id_check(EllipticCurve::p384());
        id_check(EllipticCurve::p521());
    }
}
