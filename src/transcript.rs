//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.

extern crate ark_bn254;

use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::CurveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use merlin::Transcript;

use crate::errors::ProofError;

pub trait TranscriptProtocol {
    /// Append a domain separator for an `n`-bit, `m`-party range proof.
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64);

    /// Append a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);

    /// Append a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);

    /// Commit a domain separator for a CS without randomized constraints.
    fn r1cs_1phase_domain_sep(&mut self);

    /// Commit a domain separator for a CS with randomized constraints.
    fn r1cs_2phase_domain_sep(&mut self);

    /// Append a `scalar` with the given `label`.
    fn append_scalar(&mut self, label: &'static [u8], scalar: &Fr);

    /// Append a `point` with the given `label`.
    fn append_point(&mut self, label: &'static [u8], point: &G1Projective);

    /// Check that a point is not the identity, then append it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_append_point(
        &mut self,
        label: &'static [u8],
        point: &G1Projective,
    ) -> Result<(), ProofError>;

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Fr;
}

impl TranscriptProtocol for Transcript {
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64) {
        self.append_message(b"dom-sep", b"rangeproof v1");
        self.append_u64(b"n", n);
        self.append_u64(b"m", m);
    }

    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"ipp v1");
        self.append_u64(b"n", n);
    }

    fn r1cs_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs v1");
    }

    fn r1cs_1phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-1phase");
    }

    fn r1cs_2phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-2phase");
    }

    fn append_scalar(&mut self, label: &'static [u8], scalar: &Fr) {
        let mut compressed_bytes = Vec::new();
        CanonicalSerialize::serialize_compressed(scalar, &mut compressed_bytes).unwrap();
        self.append_message(label, compressed_bytes.as_slice());
    }

    fn append_point(&mut self, label: &'static [u8], point: &G1Projective) {
        let mut compressed_bytes = Vec::new();
        point.serialize_compressed(&mut compressed_bytes).unwrap();
        self.append_message(label, compressed_bytes.as_slice());
    }

    fn validate_and_append_point(
        &mut self,
        label: &'static [u8],
        point: &G1Projective,
    ) -> Result<(), ProofError> {
        if G1Projective::into_affine(*point) == G1Affine::identity() {
            Err(ProofError::VerificationError)
        } else {
            let mut compressed_bytes = Vec::new();
            point.serialize_compressed(&mut compressed_bytes).unwrap();
            Ok(self.append_message(label, compressed_bytes.as_slice()))
        }
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Fr {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);

        Fr::from(num_bigint::BigUint::from_bytes_le(&buf[..]))
    }
}
