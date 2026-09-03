//! Constant-state Keccak transcript for MLE/WHIR v2.
//!
//! V1 appended the entire transcript byte string and Solidity recopied that
//! growing string for every message. V2 commits each typed, length-framed
//! message into a 32-byte hash chain. Besides reducing EVM cost, this gives a
//! cheap and unambiguous transcript state. The v2 outer sumchecks use one
//! lockstep transcript: every round message is committed before any challenge
//! for that round is sampled.

use ark_ff::PrimeField as ArkPrimeField;
use keccak_hash::keccak;
use plonky2_field::types::PrimeField64;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use crate::protocol_schema_v2::{
    BASE_FIELD_MODULUS_V2, DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2, DOMAIN_OUTER_SUMCHECK_ROUND_V2,
    OUTER_TRANSCRIPT_PROTOCOL_V2, TAG_BYTES_V2, TAG_DOMAIN_V2, TAG_EXT3_V2, TAG_EXT3_VEC_V2,
    TAG_FIELD_V2, TAG_FIELD_VEC_V2, TRANSCRIPT_CHALLENGE_PREFIX_V2, TRANSCRIPT_FRAME_PREFIX_V2,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptV2 {
    state: [u8; 32],
    squeeze_counter: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoupledOuterRoundChallenges {
    pub log: Field64_3,
    pub gate: Field64_3,
}

impl TranscriptV2 {
    pub fn new() -> Self {
        let mut transcript = Self {
            state: [0u8; 32],
            squeeze_counter: 0,
        };
        transcript.domain_separate(OUTER_TRANSCRIPT_PROTOCOL_V2);
        transcript
    }

    fn absorb_frame(&mut self, tag: u8, payload: &[u8]) {
        let prefix = TRANSCRIPT_FRAME_PREFIX_V2.as_bytes();
        let mut frame = Vec::with_capacity(prefix.len() + 32 + 1 + 8 + payload.len());
        frame.extend_from_slice(prefix);
        frame.extend_from_slice(&self.state);
        frame.push(tag);
        frame.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        frame.extend_from_slice(payload);
        self.state.copy_from_slice(keccak(&frame).as_ref());
        self.squeeze_counter = 0;
    }

    pub fn domain_separate(&mut self, label: &str) {
        self.absorb_frame(TAG_DOMAIN_V2, label.as_bytes());
    }

    pub fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.absorb_frame(TAG_BYTES_V2, bytes);
    }

    pub fn absorb_field<F: PrimeField64>(&mut self, value: F) {
        assert_goldilocks::<F>();
        self.absorb_frame(TAG_FIELD_V2, &value.to_canonical_u64().to_le_bytes());
    }

    pub fn absorb_field_vec<F: PrimeField64>(&mut self, values: &[F]) {
        assert_goldilocks::<F>();
        let mut payload = Vec::with_capacity(8 + 8 * values.len());
        payload.extend_from_slice(&(values.len() as u64).to_le_bytes());
        for value in values {
            payload.extend_from_slice(&value.to_canonical_u64().to_le_bytes());
        }
        self.absorb_frame(TAG_FIELD_VEC_V2, &payload);
    }

    pub fn absorb_ext3(&mut self, value: Field64_3) {
        let mut payload = [0u8; 24];
        for (index, limb) in [value.c0, value.c1, value.c2].into_iter().enumerate() {
            payload[index * 8..(index + 1) * 8]
                .copy_from_slice(&limb.into_bigint().0[0].to_le_bytes());
        }
        self.absorb_frame(TAG_EXT3_V2, &payload);
    }

    pub fn absorb_ext3_vec(&mut self, values: &[Field64_3]) {
        let mut payload = Vec::with_capacity(8 + 24 * values.len());
        payload.extend_from_slice(&(values.len() as u64).to_le_bytes());
        for value in values {
            for limb in [value.c0, value.c1, value.c2] {
                payload.extend_from_slice(&limb.into_bigint().0[0].to_le_bytes());
            }
        }
        self.absorb_frame(TAG_EXT3_VEC_V2, &payload);
    }

    pub fn squeeze_challenge<F: PrimeField64>(&mut self) -> F {
        assert_goldilocks::<F>();
        let prefix = TRANSCRIPT_CHALLENGE_PREFIX_V2.as_bytes();
        let mut input = Vec::with_capacity(prefix.len() + 32 + 8);
        input.extend_from_slice(prefix);
        input.extend_from_slice(&self.state);
        input.extend_from_slice(&self.squeeze_counter.to_le_bytes());
        self.squeeze_counter += 1;
        reduce_keccak::<F>(keccak(&input).as_ref())
    }

    pub fn squeeze_challenges<F: PrimeField64>(&mut self, count: usize) -> Vec<F> {
        (0..count).map(|_| self.squeeze_challenge::<F>()).collect()
    }

    pub fn squeeze_ext3<F: PrimeField64>(&mut self) -> Field64_3 {
        let c0 = self.squeeze_challenge::<F>().to_canonical_u64();
        let c1 = self.squeeze_challenge::<F>().to_canonical_u64();
        let c2 = self.squeeze_challenge::<F>().to_canonical_u64();
        Field64_3::new(
            ArkGoldilocks::from(c0),
            ArkGoldilocks::from(c1),
            ArkGoldilocks::from(c2),
        )
    }

    pub fn squeeze_ext3_challenges<F: PrimeField64>(&mut self, count: usize) -> Vec<Field64_3> {
        (0..count).map(|_| self.squeeze_ext3::<F>()).collect()
    }

    /// Commit one complete outer-sumcheck round, then sample its challenge
    /// tuple. No challenge is available until both Ext3 messages have been
    /// absorbed. Security comes from each individual sumcheck challenge being
    /// sampled in Fp3; lockstep ordering alone must not be treated as an
    /// amplification mechanism.
    pub fn commit_coupled_outer_round<F: PrimeField64>(
        &mut self,
        round_index: usize,
        log_non_constant: &[Field64_3],
        gate_non_constant: &[Field64_3],
    ) -> CoupledOuterRoundChallenges {
        self.domain_separate(DOMAIN_OUTER_SUMCHECK_ROUND_V2);
        self.absorb_bytes(&(round_index as u64).to_le_bytes());
        self.absorb_ext3_vec(log_non_constant);
        self.absorb_ext3_vec(gate_non_constant);
        self.domain_separate(DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2);
        CoupledOuterRoundChallenges {
            log: self.squeeze_ext3::<F>(),
            gate: self.squeeze_ext3::<F>(),
        }
    }

    pub fn state_digest(&self) -> [u8; 32] {
        self.state
    }

    pub fn current_squeeze_counter(&self) -> u64 {
        self.squeeze_counter
    }
}

impl Default for TranscriptV2 {
    fn default() -> Self {
        Self::new()
    }
}

fn assert_goldilocks<F: PrimeField64>() {
    assert_eq!(
        F::ORDER,
        BASE_FIELD_MODULUS_V2,
        "v2 transcript is defined only over Goldilocks"
    );
}

fn reduce_keccak<F: PrimeField64>(bytes: &[u8]) -> F {
    debug_assert_eq!(bytes.len(), 32);
    let radix = F::from_noncanonical_u96((0, 1));
    bytes.chunks_exact(8).rev().fold(F::ZERO, |acc, chunk| {
        let limb = u64::from_le_bytes(chunk.try_into().expect("eight-byte Keccak limb"));
        acc * radix + F::from_noncanonical_u64(limb)
    })
}

#[cfg(test)]
mod tests {
    use plonky2_field::goldilocks_field::GoldilocksField;
    use plonky2_field::types::Field;

    use super::*;

    type F = GoldilocksField;

    #[test]
    fn typed_frames_cannot_alias() {
        let mut field = TranscriptV2::new();
        field.absorb_field(F::from_canonical_u64(7));
        let mut bytes = TranscriptV2::new();
        bytes.absorb_bytes(&7u64.to_le_bytes());
        assert_ne!(field.state_digest(), bytes.state_digest());
    }

    #[test]
    fn coupled_round_commits_every_message_before_squeezing() {
        let log = [Field64_3::from(11u64)];
        let gate = [Field64_3::from(21u64), Field64_3::from(22u64)];
        let mut first = TranscriptV2::new();
        let first_challenges = first.commit_coupled_outer_round::<F>(0, &log, &gate);
        assert_eq!(first.current_squeeze_counter(), 6);

        let mut changed = TranscriptV2::new();
        let mut changed_gate = gate;
        changed_gate[1] = Field64_3::from(24u64);
        let changed_challenges = changed.commit_coupled_outer_round::<F>(0, &log, &changed_gate);
        assert_ne!(first_challenges, changed_challenges);
    }

    #[test]
    fn ext3_uses_three_distinct_counter_squeezes() {
        let mut as_ext = TranscriptV2::new();
        let value = as_ext.squeeze_ext3::<F>();
        let mut as_base = TranscriptV2::new();
        let limbs = [
            as_base.squeeze_challenge::<F>().to_canonical_u64(),
            as_base.squeeze_challenge::<F>().to_canonical_u64(),
            as_base.squeeze_challenge::<F>().to_canonical_u64(),
        ];
        assert_eq!(value.c0.into_bigint().0[0], limbs[0]);
        assert_eq!(value.c1.into_bigint().0[0], limbs[1]);
        assert_eq!(value.c2.into_bigint().0[0], limbs[2]);
        assert_eq!(as_ext.current_squeeze_counter(), 3);
    }
}
