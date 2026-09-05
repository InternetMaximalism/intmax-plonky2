/// Keccak256-based Fiat-Shamir transcript for the MLE proving system.
///
/// Single transcript for all sub-protocols — no dual-system ambiguity.
/// Domain-separated with protocol and sub-protocol labels.
use ark_ff::PrimeField as ArkPrimeField;
use keccak_hash::keccak;
use plonky2_field::types::PrimeField64;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use crate::protocol_schema::MLE_TRANSCRIPT_PROTOCOL;

/// A Fiat-Shamir transcript using Keccak256.
///
/// All prover messages are absorbed before any challenge is derived.
/// Each squeeze produces a fresh challenge deterministically.
#[derive(Clone, Debug)]
pub struct Transcript {
    /// Accumulated absorbed data.
    state: Vec<u8>,
    /// Counter for sequential squeezes without intermediate absorbs.
    squeeze_counter: u64,
}

impl Transcript {
    /// Create a new transcript with protocol-level domain separation.
    pub fn new() -> Self {
        let mut t = Self {
            state: Vec::new(),
            squeeze_counter: 0,
        };
        t.domain_separate(MLE_TRANSCRIPT_PROTOCOL);
        t
    }

    /// Absorb a domain separation label. Resets squeeze counter.
    pub fn domain_separate(&mut self, label: &str) {
        let bytes = label.as_bytes();
        // Length-prefix to prevent ambiguity
        self.state
            .extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        self.state.extend_from_slice(bytes);
        self.squeeze_counter = 0;
    }

    /// Absorb a single field element. Resets squeeze counter.
    pub fn absorb_field<F: PrimeField64>(&mut self, elem: F) {
        let val = elem.to_canonical_u64();
        self.state.extend_from_slice(&val.to_le_bytes());
        self.squeeze_counter = 0;
    }

    /// Absorb a slice of field elements.
    pub fn absorb_field_vec<F: PrimeField64>(&mut self, elems: &[F]) {
        // Length-prefix
        self.state
            .extend_from_slice(&(elems.len() as u64).to_le_bytes());
        for &elem in elems {
            self.state
                .extend_from_slice(&elem.to_canonical_u64().to_le_bytes());
        }
        self.squeeze_counter = 0;
    }

    /// Absorb one canonical element of the cubic Goldilocks extension.
    ///
    /// The wire encoding is exactly three little-endian `u64` limbs in
    /// coefficient order `(c0, c1, c2)`.  It is deliberately distinct from a
    /// base-field vector: callers that need a vector must use
    /// [`Self::absorb_ext3_vec`], which prefixes the number of extension
    /// elements (not the number of base limbs).
    pub fn absorb_ext3(&mut self, elem: Field64_3) {
        for limb in [elem.c0, elem.c1, elem.c2] {
            self.state
                .extend_from_slice(&limb.into_bigint().0[0].to_le_bytes());
        }
        self.squeeze_counter = 0;
    }

    /// Absorb a length-prefixed vector of cubic-extension elements.
    pub fn absorb_ext3_vec(&mut self, elems: &[Field64_3]) {
        self.state
            .extend_from_slice(&(elems.len() as u64).to_le_bytes());
        for &elem in elems {
            for limb in [elem.c0, elem.c1, elem.c2] {
                self.state
                    .extend_from_slice(&limb.into_bigint().0[0].to_le_bytes());
            }
        }
        self.squeeze_counter = 0;
    }

    /// Absorb raw bytes. Resets squeeze counter.
    pub fn absorb_bytes(&mut self, data: &[u8]) {
        self.state
            .extend_from_slice(&(data.len() as u64).to_le_bytes());
        self.state.extend_from_slice(data);
        self.squeeze_counter = 0;
    }

    /// Squeeze a challenge field element from the transcript.
    ///
    /// Computes `Keccak256(state || counter)` and reduces modulo the field order.
    /// The 256-bit hash is interpreted as a little-endian integer and all four
    /// 64-bit limbs are reduced with Horner's rule. The reduction bias is
    /// below 2^-192 for Goldilocks.
    pub fn squeeze_challenge<F: PrimeField64>(&mut self) -> F {
        let mut to_hash = self.state.clone();
        to_hash.extend_from_slice(&self.squeeze_counter.to_le_bytes());
        self.squeeze_counter += 1;

        let hash = keccak(&to_hash);
        let bytes = hash.as_ref();

        // Process the little-endian limbs from most to least significant.
        // `radix` is 2^64 in F, constructed without a Goldilocks-specific
        // constant so the generic transcript implementation stays coherent.
        let radix = F::from_noncanonical_u96((0, 1));
        let mut acc = F::ZERO;
        for chunk in bytes.chunks(8).rev() {
            let limb = u64::from_le_bytes(chunk.try_into().unwrap_or([0u8; 8]));
            acc = acc * radix + F::from_noncanonical_u64(limb);
        }
        acc
    }

    /// Squeeze `n` independent challenge field elements.
    pub fn squeeze_challenges<F: PrimeField64>(&mut self, n: usize) -> Vec<F> {
        (0..n).map(|_| self.squeeze_challenge()).collect()
    }

    /// Squeeze one challenge in `Fp[theta]/(theta^3 - 2)`.
    ///
    /// Each coefficient is produced by a separate Keccak/counter squeeze.
    /// This is not a base-field entropy amplifier: the returned value is one
    /// element of the cubic extension and must be used by an extension-field
    /// algebraic check.  The assertion prevents accidental use with a
    /// different 64-bit prime while retaining the generic Goldilocks-facing
    /// prover API.
    pub fn squeeze_ext3<F: PrimeField64>(&mut self) -> Field64_3 {
        assert_eq!(
            F::ORDER,
            0xFFFF_FFFF_0000_0001,
            "Ext3 transcript is defined only over the Goldilocks prime"
        );
        let c0: F = self.squeeze_challenge();
        let c1: F = self.squeeze_challenge();
        let c2: F = self.squeeze_challenge();
        Field64_3::new(
            ArkGoldilocks::from(c0.to_canonical_u64()),
            ArkGoldilocks::from(c1.to_canonical_u64()),
            ArkGoldilocks::from(c2.to_canonical_u64()),
        )
    }

    /// Squeeze `n` independent cubic-extension challenges.
    pub fn squeeze_ext3_challenges<F: PrimeField64>(&mut self, n: usize) -> Vec<Field64_3> {
        (0..n).map(|_| self.squeeze_ext3::<F>()).collect()
    }

    /// Returns the current accumulated state bytes (for debugging/interop testing).
    pub fn state_bytes(&self) -> &[u8] {
        &self.state
    }

    /// Returns the current squeeze counter (for debugging/interop testing).
    pub fn current_squeeze_counter(&self) -> u64 {
        self.squeeze_counter
    }

    /// Returns the keccak256 hash that WOULD be used for the next squeeze,
    /// without advancing the counter. For debugging/interop testing only.
    pub fn peek_next_hash(&self) -> [u8; 32] {
        let mut to_hash = self.state.clone();
        to_hash.extend_from_slice(&self.squeeze_counter.to_le_bytes());
        let hash = keccak(&to_hash);
        let mut result = [0u8; 32];
        result.copy_from_slice(hash.as_ref());
        result
    }
}

impl Default for Transcript {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use plonky2_field::goldilocks_field::GoldilocksField;
    use plonky2_field::types::Field;

    use super::*;

    type F = GoldilocksField;

    #[test]
    fn test_determinism() {
        let mut t1 = Transcript::new();
        let mut t2 = Transcript::new();
        t1.absorb_field(F::from_canonical_u64(42));
        t2.absorb_field(F::from_canonical_u64(42));
        let c1: F = t1.squeeze_challenge();
        let c2: F = t2.squeeze_challenge();
        assert_eq!(c1, c2);
    }

    #[test]
    fn test_ordering_matters() {
        let mut t1 = Transcript::new();
        let mut t2 = Transcript::new();
        t1.absorb_field(F::from_canonical_u64(1));
        t1.absorb_field(F::from_canonical_u64(2));
        t2.absorb_field(F::from_canonical_u64(2));
        t2.absorb_field(F::from_canonical_u64(1));
        let c1: F = t1.squeeze_challenge();
        let c2: F = t2.squeeze_challenge();
        assert_ne!(c1, c2);
    }

    #[test]
    fn test_domain_separation() {
        let mut t1 = Transcript::new();
        let mut t2 = Transcript::new();
        t1.domain_separate("sub-protocol-A");
        t1.absorb_field(F::from_canonical_u64(99));
        t2.domain_separate("sub-protocol-B");
        t2.absorb_field(F::from_canonical_u64(99));
        let c1: F = t1.squeeze_challenge();
        let c2: F = t2.squeeze_challenge();
        assert_ne!(c1, c2);
    }

    #[test]
    fn test_sequential_squeezes_distinct() {
        let mut t = Transcript::new();
        t.absorb_field(F::from_canonical_u64(123));
        let c1: F = t.squeeze_challenge();
        let c2: F = t.squeeze_challenge();
        let c3: F = t.squeeze_challenge();
        assert_ne!(c1, c2);
        assert_ne!(c2, c3);
        assert_ne!(c1, c3);
    }

    #[test]
    fn test_absorb_resets_squeeze_counter() {
        let mut t1 = Transcript::new();
        let mut t2 = Transcript::new();

        t1.absorb_field(F::from_canonical_u64(10));
        let _: F = t1.squeeze_challenge(); // squeeze_counter = 1
        t1.absorb_field(F::from_canonical_u64(20));
        let c1: F = t1.squeeze_challenge(); // squeeze_counter reset to 0, then 1

        t2.absorb_field(F::from_canonical_u64(10));
        t2.absorb_field(F::from_canonical_u64(20));
        // t2 never squeezed in between, but same state
        // These should NOT be equal because t1's intermediate squeeze
        // did not change the state (only counter), but t1's state includes
        // the extra absorb_field which happens after the first squeeze.
        // Actually they differ because t1 squeezed (changing nothing in state),
        // then absorbed 20. t2 absorbed 10 then 20 without squeezing.
        // The states should be the same after absorbing the same data.
        // But t1's squeeze_counter was reset. So c1 uses counter=0 for
        // the second squeeze. t2 also uses counter=0.
        // The states should match: both have state = [domain_sep, 10, 20].
        let c2: F = t2.squeeze_challenge();
        assert_eq!(c1, c2);
    }
}
