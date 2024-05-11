#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc(include = "../docs/inner-product-protocol.md"))]

extern crate alloc;

use alloc::borrow::Borrow;
use alloc::vec::Vec;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_ff::Field;

use core::iter;
use ark_bn254::{G1Projective, G1Affine, Fr};
use ark_ec::{CurveGroup, VariableBaseMSM};
use merlin::Transcript;

use crate::errors::ProofError;
use crate::transcript::TranscriptProtocol;

#[derive(Clone, Debug)]
pub struct InnerProductProof {
    pub(crate) L_vec: Vec<G1Projective>,
    pub(crate) R_vec: Vec<G1Projective>,
    pub(crate) a: Fr,
    pub(crate) b: Fr,
}

impl InnerProductProof {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut Transcript,
        Q: &G1Projective,
        G_factors: &[Fr],
        H_factors: &[Fr],
        mut G_vec: Vec<G1Projective>,
        mut H_vec: Vec<G1Projective>,
        mut a_vec: Vec<Fr>,
        mut b_vec: Vec<Fr>,
    ) -> InnerProductProof {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        if n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let L: G1Projective = {
                let bases: Vec<G1Affine> = G_R.iter()
                    .map(|p| G1Projective::into_affine(*p))
                    .chain(H_L.iter().map(|p| G1Projective::into_affine(*p)))
                    .chain(iter::once(G1Projective::into_affine(*Q))).collect();
                let scalars: Vec<Fr> = a_L.iter()
                    .zip(G_factors[n..2 * n].into_iter())
                    .map(|(a_L_i, g)| a_L_i * g)
                    .chain(
                        b_R.iter()
                            .zip(H_factors[0..n].into_iter())
                            .map(|(b_R_i, h)| b_R_i * h),
                    )
                    .chain(iter::once(c_L)).collect();
                
                VariableBaseMSM::msm(&bases, &scalars)
            }.unwrap();

            let R: G1Projective = {
                let bases: Vec<G1Affine> = G_L.iter()
                    .map(|p| G1Projective::into_affine(*p))
                    .chain(H_R.iter().map(|p| G1Projective::into_affine(*p)))
                    .chain(iter::once(G1Projective::into_affine(*Q))).collect();
                let scalars: Vec<Fr> = a_R.iter()
                    .zip(G_factors[0..n].into_iter())
                    .map(|(a_R_i, g)| a_R_i * g)
                    .chain(
                        b_L.iter()
                            .zip(H_factors[n..2 * n].into_iter())
                            .map(|(b_L_i, h)| b_L_i * h),
                    )
                    .chain(iter::once(c_R)).collect();
                
                VariableBaseMSM::msm(&bases, &scalars)
            }.unwrap();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.inverse().unwrap();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = VariableBaseMSM::msm(
                    &[G1Projective::into_affine(G_L[i]), G1Projective::into_affine(G_R[i])],
                    &[u_inv * G_factors[i], u * G_factors[n + i]],
                ).unwrap();
                H_L[i] = VariableBaseMSM::msm(
                    &[G1Projective::into_affine(H_L[i]), G1Projective::into_affine(H_R[i])],
                    &[u * H_factors[i], u_inv * H_factors[n + i]],
                ).unwrap()
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        while n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let L: G1Projective = {
                let bases: Vec<G1Affine> = G_R.iter()
                    .map(|p| G1Projective::into_affine(*p))
                    .chain(H_L.iter().map(|p| G1Projective::into_affine(*p)))
                    .chain(iter::once(G1Projective::into_affine(*Q))).collect();
                let scalars: Vec<Fr> = a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L)).cloned().collect();
                
                VariableBaseMSM::msm(&bases, &scalars)
            }.unwrap();

            let R: G1Projective = {
                let bases: Vec<G1Affine> = G_L.iter()
                    .map(|p| G1Projective::into_affine(*p))
                    .chain(H_R.iter().map(|p| G1Projective::into_affine(*p)))
                    .chain(iter::once(G1Projective::into_affine(*Q))).collect();
                let scalars: Vec<Fr> = a_R.iter().chain(b_L.iter()).chain(iter::once(&c_R)).cloned().collect();

                VariableBaseMSM::msm(&bases, &scalars)
            }.unwrap();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.inverse().unwrap();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = VariableBaseMSM::msm(&[G1Projective::into_affine(G_L[i]), G1Projective::into_affine(G_R[i])], &[u_inv, u]).unwrap();
                H_L[i] = VariableBaseMSM::msm(&[G1Projective::into_affine(H_L[i]), G1Projective::into_affine(H_R[i])], &[u, u_inv]).unwrap();
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        InnerProductProof {
            L_vec: L_vec,
            R_vec: R_vec,
            a: a[0],
            b: b[0],
        }
    }

    /// Computes three vectors of verification scalars \\([u\_{i}^{2}]\\), \\([u\_{i}^{-2}]\\) and \\([s\_{i}]\\) for combined multiscalar multiplication
    /// in a parent protocol. See [inner product protocol notes](index.html#verification-equation) for details.
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation within the inner product proof.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<(Vec<Fr>, Vec<Fr>, Vec<Fr>), ProofError> {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript

        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges.push(transcript.challenge_scalar(b"u"));
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1

        let challenges_inv = challenges.clone();
        let allinv = challenges_inv.iter().map(|scalar| scalar.inverse().unwrap());

        // 3. Compute u_i^2 and (1/u_i)^2
        let challenges_sq: Vec<Fr> = challenges.into_iter().map(|c| c * c).collect();
        let challenges_inv_sq: Vec<Fr> = allinv.clone().into_iter().map(|c_inv| c_inv * c_inv).collect();

        // 4. Compute s values inductively.

        let mut s = Vec::with_capacity(n);
        s.extend(allinv);
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            s.push(s[i - k] * u_lg_i_sq);
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

    /// This method is for testing that proof generation work,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify<IG, IH>(
        &self,
        n: usize,
        transcript: &mut Transcript,
        G_factors: IG,
        H_factors: IH,
        P: &G1Projective,
        Q: &G1Projective,
        G: &[G1Projective],
        H: &[G1Projective],
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<Fr>,
        IH: IntoIterator,
        IH::Item: Borrow<Fr>,
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| (self.a * s_i) * g_i.borrow())
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| (self.b * s_i_inv) * h_i.borrow());

        let neg_u_sq = u_sq.iter().map(|ui| Fr::from(-1)*ui);
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| Fr::from(-1)*ui);

        let Ls: Vec<G1Affine> = self
            .L_vec
            .iter()
            .map(|p| G1Projective::into_affine(*p))
            .collect();
        
        let Rs: Vec<G1Affine>  = self
            .R_vec
            .iter()
            .map(|p| G1Projective::into_affine(*p))
            .collect();

        let Qs: G1Affine = G1Projective::into_affine(*Q);

        let Gs: Vec<G1Affine> = G.iter()
            .map(|g| G1Projective::into_affine(*g))
            .collect();

        let Hs: Vec<G1Affine> = H.iter()
            .map(|h| G1Projective::into_affine(*h))
            .collect();
        
        let expect_P: G1Projective = {
            let scalars: Vec<Fr> = iter::once(self.a * self.b)
                .chain(g_times_a_times_s)
                .chain(h_times_b_div_s)
                .chain(neg_u_sq)
                .chain(neg_u_inv_sq)
                .collect();

            let points: Vec<G1Affine> = iter::once(Qs)
                .chain(Gs.iter().cloned())
                .chain(Hs.iter().cloned())
                .chain(Ls.iter().cloned())
                .chain(Rs.iter().cloned())
                .collect();
            
            VariableBaseMSM::msm(&points, &scalars)
        }.unwrap();

        if expect_P == *P {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    ///
    /// For vectors of length `n` the proof size is
    /// \\(32 \cdot (2\lg n+2)\\) bytes.
    pub fn serialized_size(&self) -> usize {
        (self.L_vec.len() * 2 + 2) * 32
    }

    /// Serializes the proof into a byte array of \\(2n+2\\) 32-byte elements.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            let mut l_bytes = Vec::new();
            let mut r_bytes = Vec::new();
            l.serialize_compressed(&mut l_bytes).unwrap();
            r.serialize_compressed(&mut r_bytes).unwrap();
            buf.extend_from_slice(l_bytes.as_slice());
            buf.extend_from_slice(r_bytes.as_slice());
        }
        let mut a_bytes = Vec::new();
        let mut b_bytes = Vec::new();
        self.a.serialize_compressed(&mut a_bytes).unwrap();
        self.b.serialize_compressed(&mut b_bytes).unwrap();
        buf.extend_from_slice(a_bytes.as_slice());
        buf.extend_from_slice(b_bytes.as_slice());
        buf
    }

    /// Converts the proof into a byte iterator over serialized view of the proof.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    /*#[inline]
    pub(crate) fn to_bytes_iter(&self) -> impl Iterator<Item = u8> + '_ {
        let a_compressed = Vec::new();
        let b_compressed = Vec::new();
        CanonicalSerialize::serialize_compressed(&self.a, a_compressed);
        CanonicalSerialize::serialize_compressed(&self.b, b_compressed);
        self.L_vec
            .iter()
            .zip(self.R_vec.iter())
            .flat_map(|(l, r)| {
                let mut l_compressed = Vec::new();
                let mut r_compressed = Vec::new();
                l.serialize_compressed(&mut l_compressed);
                r.serialize_compressed(&mut r_compressed);
                l_compressed.iter().chain(r_compressed.as_slice())
            })
            .chain(a_compressed.as_slice())
            .chain(b_compressed.as_slice())
            .copied()
    }*/
    pub(crate) fn to_bytes_iter(&self) -> impl Iterator<Item = u8> + '_ {
        let mut buf = Vec::new();
    
        // Serialize L and R vectors
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            l.serialize_compressed(&mut buf).unwrap(); // Handle errors as appropriate
            r.serialize_compressed(&mut buf).unwrap(); // Handle errors as appropriate
        }
    
        // Serialize a and b
        self.a.serialize_compressed(&mut buf).unwrap(); // Handle errors as appropriate
        self.b.serialize_compressed(&mut buf).unwrap(); // Handle errors as appropriate
    
        buf.into_iter()
    }

    /// Deserializes the proof from a byte slice.
    /// Returns an error in the following cases:
    /// * the slice does not have \\(2n+2\\) 32-byte elements,
    /// * \\(n\\) is larger or equal to 32 (proof is too big),
    /// * any of \\(2n\\) points are not valid compressed Ristretto points,
    /// * any of 2 scalars are not canonical scalars modulo Ristretto group order.
    pub fn from_bytes(slice: &[u8]) -> Result<InnerProductProof, ProofError> {
        let b = slice.len();
        if b % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        let num_elements = b / 32;
        if num_elements < 2 {
            return Err(ProofError::FormatError);
        }
        if (num_elements - 2) % 2 != 0 {
            return Err(ProofError::FormatError);
        }
        let lg_n = (num_elements - 2) / 2;
        if lg_n >= 32 {
            return Err(ProofError::FormatError);
        }

        let mut L_vec: Vec<G1Projective> = Vec::with_capacity(lg_n);
        let mut R_vec: Vec<G1Projective> = Vec::with_capacity(lg_n);
        for i in 0..lg_n {
            let pos = 2 * i * 32;
            L_vec.push(G1Projective::deserialize_compressed(&slice[pos..]).unwrap());
            R_vec.push(G1Projective::deserialize_compressed(&slice[pos + 32..]).unwrap());
        }

        let pos = 2 * lg_n * 32;
        let a: Fr = CanonicalDeserialize::deserialize_compressed(&slice[pos..])
            .map_err(|_| ProofError::FormatError)?;
        let b: Fr = CanonicalDeserialize::deserialize_compressed(&slice[pos + 32..])
            .map_err(|_| ProofError::FormatError)?;

        Ok(InnerProductProof { L_vec, R_vec, a, b })
    }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product(a: &[Fr], b: &[Fr]) -> Fr {
    let mut out = Fr::from(0);
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::util;
    use ark_serialize::CanonicalSerializeHashExt;
    use sha3::Sha3_512;

    fn test_helper_create(n: usize) {
        let mut rng = rand::thread_rng();

        use crate::generators::BulletproofGens;
        use ark_ff::UniformRand;
        let bp_gens = BulletproofGens::new(n, 1);
        let G: Vec<G1Projective> = bp_gens.share(0).G(n).cloned().collect();
        let H: Vec<G1Projective> = bp_gens.share(0).H(n).cloned().collect();

        // Q would be determined upstream in the protocol, so we pick a random one.
        let Q = G1Projective::hash::<Sha3_512>(&G1Projective::deserialize_compressed(b"test point".as_ref()).unwrap());

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let b: Vec<_> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let c = inner_product(&a, &b);

        let G_factors: Vec<Fr> = iter::repeat(Fr::from(1)).take(n).collect();

        // y_inv is (the inverse of) a random challenge
        let y_inv = Fr::rand(&mut rng);
        let H_factors: Vec<Fr> = util::exp_iter(y_inv).take(n).collect();

        // P would be determined upstream, but we need a correct P to check the proof.
        //
        // To generate P = <a,G> + <b,H'> + <a,b> Q, compute
        //             P = <a,G> + <b',H> + <a,b> Q,
        // where b' = b \circ y^(-n)
        let b_prime = b.iter().zip(util::exp_iter(y_inv)).map(|(bi, yi)| *bi * yi);
        // a.iter() has Item=&Scalar, need Item=Scalar to chain with b_prime
        let a_prime = a.iter().cloned();

        let P: G1Projective = {
            let bases: Vec<G1Affine> = G.iter()
                .map(|p| G1Projective::into_affine(*p))
                .chain(H.iter().map(|p| G1Projective::into_affine(*p)))
                .chain(iter::once(G1Projective::into_affine(G1Projective::deserialize_compressed(Q.as_slice()).unwrap()))).collect();
            let scalars: Vec<Fr> = a_prime.chain(b_prime).chain(iter::once(c)).collect();

            VariableBaseMSM::msm(&bases, &scalars)
        }.unwrap();

        let mut verifier = Transcript::new(b"innerproducttest");
        let proof = InnerProductProof::create(
            &mut verifier,
            &G1Projective::deserialize_compressed(Q.as_slice()).unwrap(),
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        );

        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                n,
                &mut verifier,
                iter::repeat(Fr::from(1)).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &G1Projective::deserialize_compressed(Q.as_slice()).unwrap(),
                &G,
                &H
            )
            .is_ok());

        let proof = InnerProductProof::from_bytes(proof.to_bytes().as_slice()).unwrap();
        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                n,
                &mut verifier,
                iter::repeat(Fr::from(1)).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &G1Projective::deserialize_compressed(Q.as_slice()).unwrap(),
                &G,
                &H
            )
            .is_ok());
    }

    #[test]
    fn make_ipp_1() {
        test_helper_create(1);
    }

    #[test]
    fn make_ipp_2() {
        test_helper_create(2);
    }

    #[test]
    fn make_ipp_4() {
        test_helper_create(4);
    }

    #[test]
    fn make_ipp_32() {
        test_helper_create(32);
    }

    #[test]
    fn make_ipp_64() {
        test_helper_create(64);
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(4u64),
        ];
        let b = vec![
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(4u64),
            Fr::from(5u64),
        ];
        assert_eq!(Fr::from(40u64), inner_product(&a, &b));
    }
}
