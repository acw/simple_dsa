use num::{BigInt,BigUint};
use simple_asn1::{ASN1Block,ASN1Class,ASN1DecodeErr,ASN1EncodeErr,
                  FromASN1, ToASN1};
use std::clone::Clone;

/// A DSA Signature
#[derive(Clone,Debug,PartialEq)]
pub struct DSASignature {
    pub r: BigUint,
    pub s: BigUint
}

#[derive(Clone,Debug,PartialEq)]
pub enum DSADecodeError {
    ASN1Error(ASN1DecodeErr),
    NoSignatureFound,
    NegativeSigValues
}

impl From<ASN1DecodeErr> for DSADecodeError {
    fn from(a: ASN1DecodeErr) -> DSADecodeError {
        DSADecodeError::ASN1Error(a)
    }
}

impl FromASN1 for DSASignature {
    type Error = DSADecodeError;

    fn from_asn1(v: &[ASN1Block])
        -> Result<(DSASignature,&[ASN1Block]),DSADecodeError>
    {
        match v.split_first() {
            Some((&ASN1Block::Sequence(_,_,ref info), rest))
                if info.len() == 2 =>
            {
                match (&info[0], &info[1]) {
                    (&ASN1Block::Integer(_,_,ref rint),
                     &ASN1Block::Integer(_,_,ref sint)) => {
                        match (rint.to_biguint(), sint.to_biguint()) {
                            (Some(r), Some(s)) =>
                                Ok((DSASignature{ r: r, s: s }, rest)),
                            _  =>
                                Err(DSADecodeError::NegativeSigValues)
                        }
                    }
                    _ => Err(DSADecodeError::NoSignatureFound)
                }
            }
            _ => Err(DSADecodeError::NoSignatureFound)
        }
    }
}

impl ToASN1 for DSASignature {
    type Error = ASN1EncodeErr;

    fn to_asn1_class(&self, c: ASN1Class)
        -> Result<Vec<ASN1Block>,ASN1EncodeErr>
    {
        let rb = ASN1Block::Integer(c, 0, BigInt::from(self.r.clone()));
        let sb = ASN1Block::Integer(c, 0, BigInt::from(self.s.clone()));
        Ok(vec![ASN1Block::Sequence(c, 0, vec![rb,sb])])
    }
}
