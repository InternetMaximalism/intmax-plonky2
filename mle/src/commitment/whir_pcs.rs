/// WHIR-based multilinear polynomial commitment scheme.
///
/// Integrates the `whir` crate (arkworks-based) with the plonky2_mle
/// proving system via the `MultilinearPCS` trait.
///
/// Field conversion: plonky2's GoldilocksField (u64 repr) ↔ arkworks
/// Field64 (Montgomery repr) via canonical u64 serialization.
use std::borrow::Cow;

use ark_ff::PrimeField as ArkPrimeField;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field, PrimeField64};
use sha3::{Digest, Keccak256};
use whir::algebra::embedding::Basefield;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};
use whir::algebra::linear_form::{Evaluate, LinearForm, MultilinearExtension};
use whir::hash::Hash as WhirHash;
use whir::parameters::ProtocolParameters;
use whir::protocols::whir::{Config as WhirConfig, SplitWitness, Witness as WhirWitness};
use whir::transcript::codecs::{Empty, U64};
#[cfg(debug_assertions)]
use whir::transcript::Interaction;
use whir::transcript::{
    Decoding, DomainSeparator, DuplexSpongeInterface, Encoding, Keccak256Chain, NargDeserialize,
    Proof as WhirProofData, ProverState, VerifierState,
};

use crate::dense_mle::DenseMultilinearExtension;
pub use crate::protocol_schema::WHIR_SESSION_SPLIT;
use crate::protocol_schema_v2::{
    WHIR_DEDUPLICATE_IN_DOMAIN_V2, WHIR_FOLDING_FACTOR_V2, WHIR_HASH_ID_V2,
    WHIR_MAX_STARTING_LOG_INV_RATE_V2, WHIR_POW_BITS_V2, WHIR_SECURITY_LEVEL_V2,
    WHIR_UNIQUE_DECODING_V2,
};

/// WHIR session name used for domain separation in Fiat-Shamir (legacy/default).
pub const WHIR_SESSION_NAME: &str = "plonky2-mle-whir";
/// WHIR session name for the auxiliary commitment (C̃ + h̃ oracle polynomials).
/// SECURITY: Must differ from all other session names to prevent cross-protocol confusion.
pub const WHIR_SESSION_AUX: &str = "plonky2-mle-whir-aux";

fn protocol_id_for_config(config: &WhirConfig<Basefield<Field64_3>>) -> [u8; 64] {
    let mut config_bytes = Vec::new();
    ciborium::into_writer(config, &mut config_bytes).expect("WHIR config CBOR serialization");
    let tagged_hash = |tag: u8| -> [u8; 32] {
        let mut hasher = Keccak256::new();
        hasher.update([tag]);
        hasher.update(&config_bytes);
        hasher.finalize().into()
    };
    let mut protocol_id = [0u8; 64];
    protocol_id[..32].copy_from_slice(&tagged_hash(0));
    protocol_id[32..].copy_from_slice(&tagged_hash(1));
    protocol_id
}

/// Exact WHIR session identifier consumed by Spongefish.
pub fn whir_session_id(session_name: &str) -> [u8; 32] {
    let mut encoded = Vec::new();
    ciborium::into_writer(&session_name.to_string(), &mut encoded)
        .expect("WHIR session CBOR serialization");
    Keccak256::digest(encoded).into()
}

// ═══════════════════════════════════════════════════════════════════════════
//  Field conversion
// ═══════════════════════════════════════════════════════════════════════════

/// Convert a plonky2 GoldilocksField element to arkworks Field64.
pub fn plonky2_to_ark(val: GoldilocksField) -> ArkGoldilocks {
    ArkGoldilocks::from(val.to_canonical_u64())
}

/// Convert an arkworks Field64 element to plonky2 GoldilocksField.
pub fn ark_to_plonky2(val: ArkGoldilocks) -> GoldilocksField {
    let repr: u64 = val.into_bigint().0[0];
    GoldilocksField::from_canonical_u64(repr)
}

/// Convert a vector of plonky2 field elements to arkworks.
pub fn plonky2_vec_to_ark(vals: &[GoldilocksField]) -> Vec<ArkGoldilocks> {
    vals.iter().map(|v| plonky2_to_ark(*v)).collect()
}

/// Convert a vector of arkworks field elements to plonky2.
pub fn ark_vec_to_plonky2(vals: &[ArkGoldilocks]) -> Vec<GoldilocksField> {
    vals.iter().map(|v| ark_to_plonky2(*v)).collect()
}

// ═══════════════════════════════════════════════════════════════════════════
//  WHIR PCS wrapper
// ═══════════════════════════════════════════════════════════════════════════

/// WHIR polynomial commitment scheme operating over GoldilocksField.
///
/// Uses `Basefield<Field64_3>` embedding: polynomial data lives in the 64-bit
/// base field, challenges use the 192-bit cubic extension for security.
/// The WHIR config is parameterised by rate, security level, and folding factor.
pub struct WhirPCS {
    pub params: ProtocolParameters,
    // Keep the commitment-query schedule in the protocol instance rather than
    // consulting the mutable v2 schema when a config is materialized. In
    // particular, frozen v1 instances must not change if a future v2 bumps its
    // query-deduplication policy.
    constituent_deduplicate_in_domain: bool,
}

/// Commitment: the serialized WHIR proof (for the verifier).
#[derive(Clone, Debug)]
pub struct WhirCommitment {
    /// Serialized WHIR proof bytes.
    pub proof_bytes: Vec<u8>,
}

/// Commit state: data the prover retains for the opening phase.
/// (Unused in the current two-phase API; kept for backward compat.)
#[derive(Clone)]
pub struct WhirCommitState {
    /// The original polynomial evaluations in arkworks representation.
    pub ark_evals: Vec<ArkGoldilocks>,
}

/// WHIR evaluation proof: the serialized interactive proof.
#[derive(Clone, Debug)]
pub struct WhirEvalProof {
    /// Serialized WHIR proof bytes (narg_string + hints).
    pub narg_string: Vec<u8>,
    pub hints: Vec<u8>,
    /// Transcript interaction pattern (debug mode only).
    /// Required for WHIR verifier transcript validation in debug builds.
    #[cfg(debug_assertions)]
    pub pattern: Vec<Interaction>,
}

/// Intermediate state for phased split-commit proving flow.
///
/// Supports adding vectors in phases: commit some vectors, derive external
/// challenges from their roots, then commit additional vectors before proving.
///
/// SECURITY: The WHIR internal transcript is advanced by each commit_single call.
/// External operations between commits do NOT affect the WHIR transcript.
/// The prove step computes cross-term OOD evaluations across ALL vectors.
pub struct WhirSplitCommitData {
    /// WHIR config for this polynomial size.
    pub config: WhirConfig<Basefield<Field64_3>>,
    /// Prover state (WHIR-internal transcript).
    pub prover_state: ProverState,
    /// Per-vector witnesses collected from commit_single calls.
    pub witnesses: Vec<WhirWitness<Field64_3, Basefield<Field64_3>>>,
    /// Per-vector polynomial evaluations in arkworks representation.
    pub ark_evals_list: Vec<Vec<ArkGoldilocks>>,
    /// Per-vector Merkle root hashes (32 bytes each).
    pub roots: Vec<Vec<u8>>,
    /// Number of variables (log2 of polynomial size).
    pub num_vars: usize,
}

/// Phased commitment state for the v1 constituent-binding protocol.
///
/// Every group is one WHIR commitment. Production uses `group_width = 1` and
/// packs the ordered constituent columns into that vector's high binary index
/// variables. The generic wrapper still supports wider batches for unit tests.
pub struct WhirGroupedCommitData {
    pub config: WhirConfig<Basefield<Field64_3>>,
    pub prover_state: ProverState,
    pub witnesses: Vec<WhirWitness<Field64_3, Basefield<Field64_3>>>,
    /// Group-major, then constituent-major polynomial evaluations.
    pub groups: Vec<Vec<Vec<ArkGoldilocks>>>,
    pub roots: Vec<Vec<u8>>,
    pub num_vars: usize,
    pub group_width: usize,
    #[cfg(test)]
    session_name: String,
}

/// Best-effort containment for upstream verifier panics in unwind builds.
/// This cannot catch `panic=abort`; the production grouped verifier therefore
/// preflights WHIR's known zero-divisor path before entering upstream code.
/// Legacy verifier entry points retain this wrapper but do not have the same
/// abort-mode guarantee.
fn catch_whir_verifier_panic<T>(operation: &str, verify: impl FnOnce() -> T) -> Result<T, String> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(verify))
        .map_err(|_| format!("{operation} aborted internally; proof rejected"))
}

fn checked_whir_size(num_vars: usize) -> Result<usize, String> {
    if num_vars >= usize::BITS as usize {
        return Err("WHIR variable count exceeds addressable hypercube size".to_string());
    }
    Ok(1usize << num_vars)
}

/// Transcript and typed-hint replay used to reject malformed encodings and
/// WHIR's zero final-fold divisor before entering the pinned upstream verifier.
/// Field rows are checked for canonical limbs and exact dimensions before the
/// upstream decoder can allocate from an attacker-controlled length prefix.
/// Authentication-path hints are skipped only at their exact raw-hash lengths;
/// the real WHIR verifier still performs every cryptographic check afterward.
struct GroupedWhirPreflight<'a> {
    sponge: Keccak256Chain,
    narg_string: &'a [u8],
    initial_narg_len: usize,
    hints: &'a [u8],
    all_hints: &'a [u8],
    initial_hint_len: usize,
    native_trace: Option<WhirNativeTraceRecorder>,
    #[cfg(test)]
    field64_3_offsets: Vec<usize>,
    #[cfg(test)]
    hint_field_offsets: Vec<(usize, usize)>,
    #[cfg(test)]
    hint_vector_prefix_offsets: Vec<usize>,
}

struct GroupedWhirFinalFold {
    #[cfg(test)]
    final_randomness: Vec<Field64_3>,
    #[cfg(test)]
    field64_3_offsets: Vec<usize>,
    #[cfg(test)]
    hint_field_offsets: Vec<(usize, usize)>,
    #[cfg(test)]
    hint_vector_prefix_offsets: Vec<usize>,
    native_trace: Vec<WhirNativeTraceEvent>,
    polynomial_eval: Field64_3,
}

/// Reconstruct Spongefish's debug-only interaction pattern from the exact
/// production preflight trace. The pattern is diagnostic metadata, not part of
/// the proof language; accepting a caller-supplied pattern lets malformed
/// proofs trigger upstream debug assertions (or allocate through arbitrarily
/// large interaction strings) before cryptographic verification starts.
#[cfg(debug_assertions)]
pub(crate) fn grouped_pattern_from_trace(
    trace: &[WhirNativeTraceEvent],
    hints: &[u8],
) -> Result<Vec<Interaction>, String> {
    use std::any::type_name;

    let mut pattern = Vec::new();
    let mut hint_start = 0usize;
    let mut saw_folding_round = false;
    let mut saw_eof = false;
    for event in trace {
        saw_folding_round |= event.label.starts_with("folding_round[");
        match event.kind {
            WhirNativeTraceEventKind::Absorb if event.label.starts_with("init.") => {}
            WhirNativeTraceEventKind::Absorb => {
                let rust_type = if event.label.ends_with(".bound_root") {
                    type_name::<[u8; 32]>()
                } else if event.label.ends_with(".root") {
                    type_name::<WhirHash>()
                } else if event.label.ends_with(".nonce") {
                    type_name::<U64>()
                } else {
                    type_name::<Field64_3>()
                };
                pattern.push(Interaction::ProverMessage(rust_type.to_owned()));
            }
            WhirNativeTraceEventKind::Squeeze => {
                let rust_type = if event.label.contains("pow.challenge") {
                    type_name::<[u8; 32]>()
                } else {
                    type_name::<Field64_3>()
                };
                pattern.push(Interaction::VerifierMessage(rust_type.to_owned()));
            }
            WhirNativeTraceEventKind::QuerySqueeze => {
                pattern.push(Interaction::VerifierMessage(type_name::<u8>().to_owned()));
            }
            WhirNativeTraceEventKind::QueryIndices => {}
            WhirNativeTraceEventKind::Hint => {
                let hint_end = event.hint_position;
                let segment = hints.get(hint_start..hint_end).ok_or_else(|| {
                    "WHIR trace returned an invalid debug-pattern hint range".to_string()
                })?;
                let base_field_hint = event.label.contains("folding_round[0].previous_opening")
                    || (event.label.starts_with("final.opening") && !saw_folding_round);
                let field_bytes = if base_field_hint {
                    GOLDILOCKS_LIMB_BYTES
                } else {
                    FIELD64_3_NARG_BYTES
                };
                let count_prefix = segment.get(..8).ok_or_else(|| {
                    "WHIR debug-pattern hint vector prefix is truncated".to_string()
                })?;
                let mut count_bytes = [0u8; 8];
                count_bytes.copy_from_slice(count_prefix);
                let field_count = usize::try_from(u64::from_le_bytes(count_bytes))
                    .map_err(|_| "WHIR debug-pattern hint length does not fit usize".to_string())?;
                let fields_end = field_count
                    .checked_mul(field_bytes)
                    .and_then(|bytes| bytes.checked_add(8))
                    .ok_or_else(|| "WHIR debug-pattern hint boundary overflow".to_string())?;
                if fields_end > segment.len() || !(segment.len() - fields_end).is_multiple_of(32) {
                    return Err(
                        "WHIR debug-pattern hint segment has an invalid boundary".to_string()
                    );
                }
                let vector_type = if base_field_hint {
                    type_name::<Vec<ArkGoldilocks>>()
                } else {
                    type_name::<Vec<Field64_3>>()
                };
                pattern.push(Interaction::Hint(vector_type.to_owned()));
                for _ in 0..(segment.len() - fields_end) / 32 {
                    pattern.push(Interaction::Hint(type_name::<WhirHash>().to_owned()));
                }
                hint_start = hint_end;
            }
            WhirNativeTraceEventKind::Eof => {
                if hint_start != hints.len() {
                    return Err("WHIR debug-pattern trace did not consume all hints".to_string());
                }
                saw_eof = true;
            }
        }
    }
    if !saw_eof {
        return Err("WHIR debug-pattern trace did not reach EOF".to_string());
    }
    Ok(pattern)
}

/// Operation classes in the diagnostic replay of the production grouped-WHIR
/// verifier preflight. Numeric values are stable because the cross-language
/// golden trace stores them directly.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum WhirNativeTraceEventKind {
    Absorb = 0,
    Squeeze = 1,
    QuerySqueeze = 2,
    QueryIndices = 3,
    Hint = 4,
    Eof = 5,
}

/// One native WHIR Keccak-chain checkpoint produced by the exact parser and
/// challenge schedule used by [`WhirPCS::verify_grouped`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhirNativeTraceEvent {
    pub label: String,
    pub kind: WhirNativeTraceEventKind,
    pub narg_position: usize,
    pub hint_position: usize,
    pub sponge_state: [u8; 32],
    pub squeeze_counter: u64,
    /// Absorbed bytes, squeezed bytes, query entropy, or a Keccak digest of a
    /// consumed hint segment, according to `kind`.
    pub event_bytes: Vec<u8>,
    /// Populated only for `QueryIndices` checkpoints.
    pub query_indices: Vec<usize>,
}

#[derive(Default)]
struct WhirNativeTraceRecorder {
    state: [u8; 32],
    squeeze_counter: u64,
    events: Vec<WhirNativeTraceEvent>,
}

impl WhirNativeTraceRecorder {
    fn squeeze_bytes(&mut self, count: usize) -> Result<Vec<u8>, String> {
        let mut output = Vec::with_capacity(count);
        while output.len() < count {
            let mut hasher = Keccak256::new();
            hasher.update(self.state);
            hasher.update(b"squeeze");
            hasher.update(self.squeeze_counter.to_be_bytes());
            let block: [u8; 32] = hasher.finalize().into();
            let take = (count - output.len()).min(block.len());
            output.extend_from_slice(&block[..take]);
            self.squeeze_counter = self
                .squeeze_counter
                .checked_add(1)
                .ok_or_else(|| "WHIR trace squeeze counter overflow".to_string())?;
        }
        Ok(output)
    }

    fn assert_matches_sponge(&self, sponge: &Keccak256Chain) -> Result<(), String> {
        let mut actual_sponge = sponge.clone();
        let mut actual_next = [0u8; 32];
        actual_sponge.squeeze(&mut actual_next);

        let mut expected = Self {
            state: self.state,
            squeeze_counter: self.squeeze_counter,
            events: Vec::new(),
        };
        let expected_next = expected.squeeze_bytes(32)?;
        if actual_next.as_slice() != expected_next {
            return Err("WHIR trace mirror diverged from production Keccak sponge".to_string());
        }
        Ok(())
    }

    fn record(
        &mut self,
        label: String,
        kind: WhirNativeTraceEventKind,
        narg_position: usize,
        hint_position: usize,
        event_bytes: Vec<u8>,
        query_indices: Vec<usize>,
    ) {
        self.events.push(WhirNativeTraceEvent {
            label,
            kind,
            narg_position,
            hint_position,
            sponge_state: self.state,
            squeeze_counter: self.squeeze_counter,
            event_bytes,
            query_indices,
        });
    }
}

#[derive(Clone, Copy)]
struct GroupedWhirOpeningPreflight {
    codeword_length: usize,
    sample_count: usize,
    deduplicate: bool,
    num_cols: usize,
    num_leaves: usize,
    merkle_layers: usize,
    field_limbs: usize,
    num_commitments: usize,
    label: &'static str,
}

const GOLDILOCKS_LIMB_BYTES: usize = 8;
const FIELD64_3_NARG_BYTES: usize = 3 * GOLDILOCKS_LIMB_BYTES;
const GOLDILOCKS_MODULUS: u64 = <ArkGoldilocks as ArkPrimeField>::MODULUS.0[0];

fn validate_canonical_goldilocks_limbs(
    encoding: &[u8],
    expected_limbs: usize,
    label: &str,
    stream_name: &str,
    stream_offset: usize,
) -> Result<(), String> {
    let expected_bytes = expected_limbs
        .checked_mul(GOLDILOCKS_LIMB_BYTES)
        .ok_or_else(|| format!("WHIR preflight {label} field width overflow"))?;
    if encoding.len() != expected_bytes {
        return Err(format!("WHIR preflight {label} is truncated or malformed"));
    }

    for (limb_index, chunk) in encoding.chunks_exact(GOLDILOCKS_LIMB_BYTES).enumerate() {
        let mut limb_bytes = [0u8; GOLDILOCKS_LIMB_BYTES];
        limb_bytes.copy_from_slice(chunk);
        let raw = u64::from_le_bytes(limb_bytes);
        if raw >= GOLDILOCKS_MODULUS {
            return Err(format!(
                "WHIR preflight {label} has non-canonical Goldilocks limb {limb_index} at {stream_name} byte {}",
                stream_offset + limb_index * GOLDILOCKS_LIMB_BYTES
            ));
        }
    }
    Ok(())
}

impl<'a> GroupedWhirPreflight<'a> {
    fn new(
        config: &WhirConfig<Basefield<Field64_3>>,
        session_name: &str,
        narg_string: &'a [u8],
        hints: &'a [u8],
        record_native_trace: bool,
    ) -> Result<Self, String> {
        // Byte-for-byte equivalent to whir::transcript::DomainSeparator. Its
        // fields are private, so a standalone replay must derive the same IDs.
        let protocol_id = protocol_id_for_config(config);

        let session_id = whir_session_id(session_name);

        // Spongefish absorbs protocol, session, then the Empty instance. Even
        // the empty absorption advances Keccak256Chain once.
        let mut preflight = Self {
            sponge: Keccak256Chain::default(),
            narg_string,
            initial_narg_len: narg_string.len(),
            hints,
            all_hints: hints,
            initial_hint_len: hints.len(),
            native_trace: record_native_trace.then(WhirNativeTraceRecorder::default),
            #[cfg(test)]
            field64_3_offsets: Vec::new(),
            #[cfg(test)]
            hint_field_offsets: Vec::new(),
            #[cfg(test)]
            hint_vector_prefix_offsets: Vec::new(),
        };
        preflight.absorb_event("init.protocol", &protocol_id)?;
        preflight.absorb_event("init.session", &session_id)?;
        preflight.absorb_event("init.instance", &[])?;
        Ok(preflight)
    }

    fn narg_offset(&self) -> Result<usize, String> {
        self.initial_narg_len
            .checked_sub(self.narg_string.len())
            .ok_or_else(|| "WHIR preflight NARG cursor moved backwards".to_string())
    }

    fn trace_event(
        &mut self,
        label: impl Into<String>,
        kind: WhirNativeTraceEventKind,
        event_bytes: &[u8],
        query_indices: &[usize],
    ) -> Result<(), String> {
        let narg_position = self.narg_offset()?;
        let hint_position = self.hint_offset()?;
        if let Some(trace) = &mut self.native_trace {
            trace.assert_matches_sponge(&self.sponge)?;
            trace.record(
                label.into(),
                kind,
                narg_position,
                hint_position,
                event_bytes.to_vec(),
                query_indices.to_vec(),
            );
        }
        Ok(())
    }

    fn absorb_event(&mut self, label: impl Into<String>, encoded: &[u8]) -> Result<(), String> {
        self.sponge.absorb(encoded);
        if let Some(trace) = &mut self.native_trace {
            let mut hasher = Keccak256::new();
            hasher.update(trace.state);
            hasher.update(encoded);
            trace.state = hasher.finalize().into();
            trace.squeeze_counter = 0;
        }
        self.trace_event(label, WhirNativeTraceEventKind::Absorb, encoded, &[])
    }

    fn prover_message<T>(&mut self, label: &str) -> Result<T, String>
    where
        T: Encoding<[u8]> + NargDeserialize,
    {
        let message = T::deserialize_from_narg(&mut self.narg_string)
            .map_err(|_| format!("WHIR preflight {label} is truncated or malformed"))?;
        {
            let encoded = message.encode();
            self.absorb_event(label, encoded.as_ref())?;
        }
        Ok(message)
    }

    fn prover_message_field64_3(&mut self, label: &str) -> Result<Field64_3, String> {
        // Pinned spongefish decodes each 8-byte arkworks field limb with
        // `from_le_bytes_mod_order`. Inspect the raw bytes first: otherwise P
        // is accepted as a second encoding of zero, unlike the Solidity path.
        let raw = self
            .narg_string
            .get(..FIELD64_3_NARG_BYTES)
            .ok_or_else(|| format!("WHIR preflight {label} is truncated or malformed"))?;
        let narg_offset = self.narg_offset()?;
        validate_canonical_goldilocks_limbs(raw, 3, label, "NARG", narg_offset)?;
        #[cfg(test)]
        self.field64_3_offsets.push(narg_offset);
        self.prover_message(label)
    }

    fn prover_messages_field64_3(
        &mut self,
        count: usize,
        label: &str,
    ) -> Result<Vec<Field64_3>, String> {
        (0..count)
            .map(|index| self.prover_message_field64_3(&format!("{label}[{index}]")))
            .collect()
    }

    fn hint_offset(&self) -> Result<usize, String> {
        self.initial_hint_len
            .checked_sub(self.hints.len())
            .ok_or_else(|| "WHIR preflight hint cursor moved backwards".to_string())
    }

    fn consume_hint_bytes(&mut self, count: usize, label: &str) -> Result<&'a [u8], String> {
        if count > self.hints.len() {
            return Err(format!("WHIR preflight {label} hint is truncated"));
        }
        let (head, tail) = self.hints.split_at(count);
        self.hints = tail;
        Ok(head)
    }

    fn merkle_sibling_count(
        raw_indices: &[usize],
        num_leaves: usize,
        merkle_layers: usize,
        label: &str,
    ) -> Result<usize, String> {
        if raw_indices.iter().any(|&index| index >= num_leaves) {
            return Err(format!(
                "WHIR preflight {label} Merkle index is out of range"
            ));
        }
        let mut indices = raw_indices.to_vec();
        indices.sort_unstable();
        indices.dedup();
        let mut sibling_count = 0usize;

        for _ in 0..merkle_layers {
            let mut next_indices = Vec::with_capacity(indices.len());
            let mut cursor = 0usize;
            while cursor < indices.len() {
                let index = indices[cursor];
                if cursor + 1 < indices.len() && indices[cursor + 1] == index ^ 1 {
                    cursor += 2;
                } else {
                    sibling_count = sibling_count.checked_add(1).ok_or_else(|| {
                        format!("WHIR preflight {label} Merkle sibling count overflow")
                    })?;
                    cursor += 1;
                }
                next_indices.push(index >> 1);
            }
            indices = next_indices;
        }
        Ok(sibling_count)
    }

    fn consume_hint_openings(
        &mut self,
        opening: GroupedWhirOpeningPreflight,
        indices: &[usize],
        trace_scope: &str,
    ) -> Result<(), String> {
        if opening.codeword_length != opening.num_leaves {
            return Err(format!(
                "WHIR preflight {} codeword/Merkle shape mismatch",
                opening.label
            ));
        }
        let expected_elements = indices
            .len()
            .checked_mul(opening.num_cols)
            .ok_or_else(|| format!("WHIR preflight {} hint field count overflow", opening.label))?;
        let expected_elements_u64 = u64::try_from(expected_elements).map_err(|_| {
            format!(
                "WHIR preflight {} hint field count exceeds u64",
                opening.label
            )
        })?;
        let element_bytes = opening
            .field_limbs
            .checked_mul(GOLDILOCKS_LIMB_BYTES)
            .ok_or_else(|| {
                format!(
                    "WHIR preflight {} hint element width overflow",
                    opening.label
                )
            })?;
        let field_bytes = expected_elements
            .checked_mul(element_bytes)
            .ok_or_else(|| format!("WHIR preflight {} hint byte count overflow", opening.label))?;
        let sibling_count = Self::merkle_sibling_count(
            indices,
            opening.num_leaves,
            opening.merkle_layers,
            opening.label,
        )?;
        let sibling_bytes = sibling_count.checked_mul(32).ok_or_else(|| {
            format!(
                "WHIR preflight {} Merkle hint byte count overflow",
                opening.label
            )
        })?;

        for commitment_index in 0..opening.num_commitments {
            let hint_start = self.hint_offset()?;
            #[cfg(test)]
            let prefix_offset = self.hint_offset()?;
            let prefix = self.consume_hint_bytes(8, opening.label)?;
            let mut prefix_bytes = [0u8; 8];
            prefix_bytes.copy_from_slice(prefix);
            let encoded_elements = u64::from_le_bytes(prefix_bytes);
            if encoded_elements != expected_elements_u64 {
                return Err(format!(
                    "WHIR preflight {} commitment {commitment_index} hint vector length mismatch: got {encoded_elements}, expected {expected_elements_u64}",
                    opening.label
                ));
            }
            #[cfg(test)]
            self.hint_vector_prefix_offsets.push(prefix_offset);

            let fields_offset = self.hint_offset()?;
            let fields = self.consume_hint_bytes(field_bytes, opening.label)?;
            for element_index in 0..expected_elements {
                let relative_offset =
                    element_index.checked_mul(element_bytes).ok_or_else(|| {
                        format!(
                            "WHIR preflight {} hint element offset overflow",
                            opening.label
                        )
                    })?;
                let element_offset =
                    fields_offset.checked_add(relative_offset).ok_or_else(|| {
                        format!(
                            "WHIR preflight {} absolute hint offset overflow",
                            opening.label
                        )
                    })?;
                let element_end = relative_offset.checked_add(element_bytes).ok_or_else(|| {
                    format!("WHIR preflight {} hint element end overflow", opening.label)
                })?;
                let element = fields.get(relative_offset..element_end).ok_or_else(|| {
                    format!("WHIR preflight {} hint element is truncated", opening.label)
                })?;
                validate_canonical_goldilocks_limbs(
                    element,
                    opening.field_limbs,
                    opening.label,
                    "hint",
                    element_offset,
                )?;
                #[cfg(test)]
                self.hint_field_offsets
                    .push((element_offset, opening.field_limbs));
            }
            let _ = self.consume_hint_bytes(sibling_bytes, "Merkle authentication path")?;
            let hint_end = self.hint_offset()?;
            let hint_segment = self
                .all_hints
                .get(hint_start..hint_end)
                .ok_or_else(|| format!("WHIR preflight {} hint range is invalid", opening.label))?;
            if self.native_trace.is_some() {
                let hint_digest = Keccak256::digest(hint_segment);
                self.trace_event(
                    format!("{trace_scope}.hint[{commitment_index}]"),
                    WhirNativeTraceEventKind::Hint,
                    hint_digest.as_slice(),
                    &[],
                )?;
            }
        }
        Ok(())
    }

    fn finish(&mut self) -> Result<(), String> {
        if !self.narg_string.is_empty() {
            return Err("WHIR preflight proof not fully consumed: trailing NARG bytes".to_string());
        }
        if !self.hints.is_empty() {
            return Err("WHIR preflight proof not fully consumed: trailing hint bytes".to_string());
        }
        self.trace_event("eof", WhirNativeTraceEventKind::Eof, &[], &[])
    }

    fn verifier_message<T>(&mut self, label: &str) -> Result<T, String>
    where
        T: Decoding<[u8]>,
    {
        let mut buffer = T::Repr::default();
        self.sponge.squeeze(buffer.as_mut());
        if let Some(trace) = &mut self.native_trace {
            let expected = trace.squeeze_bytes(buffer.as_mut().len())?;
            if buffer.as_mut() != expected {
                return Err(format!("WHIR trace squeeze diverged at {label}"));
            }
        }
        self.trace_event(
            label,
            WhirNativeTraceEventKind::Squeeze,
            buffer.as_mut(),
            &[],
        )?;
        Ok(T::decode(buffer))
    }

    fn verifier_query_byte(&mut self, label: &str) -> Result<u8, String> {
        let mut output = [0u8; 1];
        self.sponge.squeeze(&mut output);
        if let Some(trace) = &mut self.native_trace {
            let expected = trace.squeeze_bytes(1)?;
            if output.as_slice() != expected {
                return Err(format!("WHIR trace query squeeze diverged at {label}"));
            }
        }
        self.trace_event(label, WhirNativeTraceEventKind::QuerySqueeze, &output, &[])?;
        Ok(output[0])
    }

    fn consume_commitment(
        &mut self,
        num_vectors: usize,
        out_domain_samples: usize,
        trace_scope: &str,
    ) -> Result<(), String> {
        let _: WhirHash = self.prover_message(&format!("{trace_scope}.root"))?;
        for sample in 0..out_domain_samples {
            let _: Field64_3 =
                self.verifier_message(&format!("{trace_scope}.ood_point[{sample}]"))?;
        }
        let eval_count = out_domain_samples
            .checked_mul(num_vectors)
            .ok_or_else(|| "WHIR preflight OOD evaluation count overflow".to_string())?;
        let _: Vec<Field64_3> =
            self.prover_messages_field64_3(eval_count, &format!("{trace_scope}.ood_answer"))?;
        Ok(())
    }

    fn consume_pow(&mut self, threshold: u64, trace_scope: &str) -> Result<(), String> {
        if threshold != u64::MAX {
            let _: [u8; 32] = self.verifier_message(&format!("{trace_scope}.challenge"))?;
            let _: U64 = self.prover_message(&format!("{trace_scope}.nonce"))?;
        }
        Ok(())
    }

    fn consume_sumcheck(
        &mut self,
        num_rounds: usize,
        pow_threshold: u64,
        trace_scope: &str,
    ) -> Result<Vec<Field64_3>, String> {
        let mut randomness = Vec::with_capacity(num_rounds);
        for round in 0..num_rounds {
            let round_scope = format!("{trace_scope}.round[{round}]");
            let _: Field64_3 = self.prover_message_field64_3(&format!("{round_scope}.c0"))?;
            let _: Field64_3 = self.prover_message_field64_3(&format!("{round_scope}.c2"))?;
            self.consume_pow(pow_threshold, &format!("{round_scope}.pow"))?;
            randomness.push(self.verifier_message(&format!("{round_scope}.challenge"))?);
        }
        Ok(randomness)
    }

    fn consume_geometric_challenge(&mut self, count: usize, label: &str) -> Result<(), String> {
        if count > 1 {
            let _: Field64_3 = self.verifier_message(label)?;
        }
        Ok(())
    }

    fn consume_opening_challenges(
        &mut self,
        codeword_length: usize,
        sample_count: usize,
        deduplicate: bool,
        trace_scope: &str,
    ) -> Result<Vec<usize>, String> {
        if sample_count == 0 {
            self.trace_event(
                format!("{trace_scope}.query_indices"),
                WhirNativeTraceEventKind::QueryIndices,
                &[],
                &[],
            )?;
            return Ok(Vec::new());
        }
        if !codeword_length.is_power_of_two() {
            return Err("WHIR preflight codeword length is not a power of two".to_string());
        }
        if codeword_length == 1 {
            let indices = if deduplicate {
                vec![0]
            } else {
                vec![0; sample_count]
            };
            self.trace_event(
                format!("{trace_scope}.query_indices"),
                WhirNativeTraceEventKind::QueryIndices,
                &[],
                &indices,
            )?;
            return Ok(indices);
        }
        let bytes_per_index = (codeword_length.ilog2() as usize).div_ceil(8);
        let entropy_len = sample_count
            .checked_mul(bytes_per_index)
            .ok_or_else(|| "WHIR preflight query entropy count overflow".to_string())?;
        let mut entropy = Vec::with_capacity(entropy_len);
        for byte in 0..entropy_len {
            entropy
                .push(self.verifier_query_byte(&format!("{trace_scope}.query_entropy[{byte}]"))?);
        }
        let mut indices: Vec<usize> = entropy
            .chunks_exact(bytes_per_index)
            .map(|chunk| {
                chunk
                    .iter()
                    .fold(0usize, |acc, &byte| (acc << 8) | byte as usize)
                    % codeword_length
            })
            .collect();
        if deduplicate {
            indices.sort_unstable();
            indices.dedup();
        }
        self.trace_event(
            format!("{trace_scope}.query_indices"),
            WhirNativeTraceEventKind::QueryIndices,
            &entropy,
            &indices,
        )?;
        Ok(indices)
    }
}

fn preflight_grouped_final_fold(
    config: &WhirConfig<Basefield<Field64_3>>,
    proof: &WhirProofData,
    session_name: &str,
    num_groups: usize,
    num_bound_evals: usize,
) -> Result<GroupedWhirFinalFold, String> {
    preflight_grouped_final_fold_impl(
        config,
        proof,
        session_name,
        num_groups,
        num_bound_evals,
        cfg!(debug_assertions),
    )
}

fn preflight_grouped_final_fold_impl(
    config: &WhirConfig<Basefield<Field64_3>>,
    proof: &WhirProofData,
    session_name: &str,
    num_groups: usize,
    num_bound_evals: usize,
    record_native_trace: bool,
) -> Result<GroupedWhirFinalFold, String> {
    let mut transcript = GroupedWhirPreflight::new(
        config,
        session_name,
        &proof.narg_string,
        &proof.hints,
        record_native_trace,
    )?;
    let batch_size = config.initial_committer.num_vectors;
    let total_vectors = num_groups
        .checked_mul(batch_size)
        .ok_or_else(|| "WHIR preflight vector count overflow".to_string())?;
    if total_vectors == 0 || !num_bound_evals.is_multiple_of(total_vectors) {
        return Err("WHIR preflight evaluation shape mismatch".to_string());
    }
    let num_linear_forms = num_bound_evals / total_vectors;

    for group in 0..num_groups {
        let scope = format!("initial.group[{group}]");
        transcript.consume_commitment(
            batch_size,
            config.initial_committer.out_domain_samples,
            &scope,
        )?;
        let _: [u8; 32] = transcript.prover_message(&format!("{scope}.bound_root"))?;
    }
    let _: Vec<Field64_3> =
        transcript.prover_messages_field64_3(num_bound_evals, "initial.statement.claim")?;

    // Complete every commitment's OOD row with its cross-group values.
    let cross_values = num_groups
        .checked_mul(config.initial_committer.out_domain_samples)
        .and_then(|count| count.checked_mul(total_vectors - batch_size))
        .ok_or_else(|| "WHIR preflight cross-term count overflow".to_string())?;
    let _: Vec<Field64_3> =
        transcript.prover_messages_field64_3(cross_values, "initial.cross_ood")?;

    transcript.consume_geometric_challenge(total_vectors, "initial.vector_rlc")?;
    let initial_constraint_count = num_groups
        .checked_mul(config.initial_committer.out_domain_samples)
        .and_then(|count| count.checked_add(num_linear_forms))
        .ok_or_else(|| "WHIR preflight constraint count overflow".to_string())?;
    transcript.consume_geometric_challenge(initial_constraint_count, "initial.constraint_rlc")?;
    if initial_constraint_count == 0 {
        for round in 0..config.initial_sumcheck.num_rounds {
            let _: Field64_3 = transcript
                .verifier_message(&format!("initial.zero_sumcheck.challenge[{round}]"))?;
        }
        transcript.consume_pow(config.initial_skip_pow.threshold, "initial.skip_pow")?;
    } else {
        let _ = transcript.consume_sumcheck(
            config.initial_sumcheck.num_rounds,
            config.initial_sumcheck.round_pow.threshold,
            "initial.sumcheck",
        )?;
    }

    let initial_merkle = &config.initial_committer.matrix_commit.merkle_tree;
    let mut previous_opening = GroupedWhirOpeningPreflight {
        codeword_length: config.initial_committer.codeword_length,
        sample_count: config.initial_committer.in_domain_samples,
        deduplicate: config.initial_committer.deduplicate_in_domain,
        num_cols: config.initial_committer.num_cols(),
        num_leaves: initial_merkle.num_leaves,
        merkle_layers: initial_merkle.layers.len(),
        field_limbs: 1,
        num_commitments: num_groups,
        label: "initial opening",
    };
    for (round_index, round) in config.round_configs.iter().enumerate() {
        let scope = format!("folding_round[{round_index}]");
        transcript.consume_commitment(
            round.irs_committer.num_vectors,
            round.irs_committer.out_domain_samples,
            &scope,
        )?;
        transcript.consume_pow(round.pow.threshold, &format!("{scope}.pow"))?;
        let in_domain_indices = transcript.consume_opening_challenges(
            previous_opening.codeword_length,
            previous_opening.sample_count,
            previous_opening.deduplicate,
            &format!("{scope}.previous_opening"),
        )?;
        transcript.consume_hint_openings(
            previous_opening,
            &in_domain_indices,
            &format!("{scope}.previous_opening"),
        )?;
        let constraint_count = round
            .irs_committer
            .out_domain_samples
            .checked_add(in_domain_indices.len())
            .ok_or_else(|| "WHIR preflight round constraint count overflow".to_string())?;
        transcript
            .consume_geometric_challenge(constraint_count, &format!("{scope}.constraint_rlc"))?;
        let _ = transcript.consume_sumcheck(
            round.sumcheck.num_rounds,
            round.sumcheck.round_pow.threshold,
            &format!("{scope}.sumcheck"),
        )?;
        let round_merkle = &round.irs_committer.matrix_commit.merkle_tree;
        previous_opening = GroupedWhirOpeningPreflight {
            codeword_length: round.irs_committer.codeword_length,
            sample_count: round.irs_committer.in_domain_samples,
            deduplicate: round.irs_committer.deduplicate_in_domain,
            num_cols: round.irs_committer.num_cols(),
            num_leaves: round_merkle.num_leaves,
            merkle_layers: round_merkle.layers.len(),
            field_limbs: 3,
            num_commitments: 1,
            label: "round opening",
        };
    }

    let final_vector: Vec<Field64_3> =
        transcript.prover_messages_field64_3(config.final_sumcheck.initial_size, "final.vector")?;
    transcript.consume_pow(config.final_pow.threshold, "final.pow")?;
    let final_opening_indices = transcript.consume_opening_challenges(
        previous_opening.codeword_length,
        previous_opening.sample_count,
        previous_opening.deduplicate,
        "final.opening",
    )?;
    transcript.consume_hint_openings(previous_opening, &final_opening_indices, "final.opening")?;
    let final_randomness = transcript.consume_sumcheck(
        config.final_sumcheck.num_rounds,
        config.final_sumcheck.round_pow.threshold,
        "final.sumcheck",
    )?;
    let expected_final_size = 1usize
        .checked_shl(
            u32::try_from(final_randomness.len())
                .map_err(|_| "WHIR preflight final dimension overflow".to_string())?,
        )
        .ok_or_else(|| "WHIR preflight final dimension overflow".to_string())?;
    if final_vector.len() != expected_final_size {
        return Err("WHIR preflight final polynomial shape mismatch".to_string());
    }
    transcript.finish()?;
    let polynomial_eval = whir::algebra::multilinear_extend(&final_vector, &final_randomness);
    let native_trace = transcript
        .native_trace
        .take()
        .map_or_else(Vec::new, |trace| trace.events);
    Ok(GroupedWhirFinalFold {
        #[cfg(test)]
        final_randomness,
        #[cfg(test)]
        field64_3_offsets: transcript.field64_3_offsets,
        #[cfg(test)]
        hint_field_offsets: transcript.hint_field_offsets,
        #[cfg(test)]
        hint_vector_prefix_offsets: transcript.hint_vector_prefix_offsets,
        native_trace,
        polynomial_eval,
    })
}

impl WhirPCS {
    /// Create a WHIR PCS with the given parameters.
    /// rate = 1/2^starting_log_inv_rate (e.g., 4 for rate 1/16).
    pub fn new(
        security_level: usize,
        pow_bits: usize,
        starting_log_inv_rate: usize,
        folding_factor: usize,
    ) -> Self {
        let params = ProtocolParameters {
            security_level,
            pow_bits,
            initial_folding_factor: folding_factor,
            folding_factor,
            unique_decoding: false,
            starting_log_inv_rate,
            batch_size: 1,
            hash_id: whir::hash::KECCAK,
        };
        Self {
            params,
            // Preserve the historical behavior of generic callers. Versioned
            // constituent constructors below overwrite this explicitly.
            constituent_deduplicate_in_domain: true,
        }
    }

    /// Default: rate 1/16, 90-bit security, 0 PoW bits, folding factor 4.
    pub fn default_rate_16() -> Self {
        Self::new(90, 0, 4, 4)
    }

    /// Create a WHIR PCS with parameters adapted for a given polynomial size.
    /// Ensures folding_factor <= num_vars and PoW bits within WHIR limits.
    pub fn for_num_vars(num_vars: usize) -> Self {
        let folding_factor = num_vars.clamp(1, 4);
        // Rate 1/16 (starting_log_inv_rate=4).
        // Must leave room for folding: num_vars > starting_log_inv_rate + folding
        let starting_log_inv_rate = if num_vars <= 4 {
            1
        } else {
            4.min(num_vars - folding_factor)
        };
        // PoW disabled; security level capped at 90 bits.
        let security_level = 90.min(num_vars * 5 + 10);
        let pow_bits = 0;
        Self::new(
            security_level,
            pow_bits,
            starting_log_inv_rate,
            folding_factor,
        )
    }

    /// Parameters for the production constituent-binding statement.
    ///
    /// The target-133 profile is evaluated with every ordered group commitment
    /// and linear form supplied by the versioned caller included in the
    /// soundness accounting. Summing all charged native WHIR events at the
    /// maximum admitted packed dimension gives about 128.356 bits of aggregate
    /// generic work (target 132 gives only about 127.356 bits). This is a local
    /// PCS work-factor statement, not a whole-system security claim.
    /// Constituent projection itself is over Field64_3.
    // Keep the generated-configuration guard if the schema changes its mode.
    #[allow(clippy::assertions_on_constants)]
    pub fn for_constituents(num_vars: usize, group_width: usize) -> Self {
        assert_eq!(WHIR_HASH_ID_V2, "keccak-256", "unsupported v2 WHIR hash");
        assert!(
            !WHIR_UNIQUE_DECODING_V2,
            "unsupported v2 WHIR decoding mode"
        );
        Self::for_constituents_with_profile(
            num_vars,
            group_width,
            WHIR_SECURITY_LEVEL_V2,
            WHIR_POW_BITS_V2,
            WHIR_MAX_STARTING_LOG_INV_RATE_V2,
            WHIR_FOLDING_FACTOR_V2,
            WHIR_DEDUPLICATE_IN_DOMAIN_V2,
        )
    }

    /// Reconstruct the two exact WHIR security profiles admitted by the
    /// one-time wire-v3 configuration cutover.
    ///
    /// This is crate-private and deliberately separate from
    /// [`Self::for_constituents`], so no prover or verifier path can select a
    /// historical security target. It exists only so the artifact writer can
    /// fully validate a staged target-132 config before replacing it with the
    /// current target-133 config.
    pub(crate) fn for_constituents_whir_133_config_cutover(
        num_vars: usize,
        group_width: usize,
        security_level: usize,
    ) -> Result<Self, &'static str> {
        if WHIR_SECURITY_LEVEL_V2 != 133 {
            return Err("WHIR-133 config cutover is only defined while the current target is 133");
        }
        if security_level != 132 && security_level != 133 {
            return Err("WHIR-133 config cutover admits only security targets 132 and 133");
        }
        Ok(Self::for_constituents_with_profile(
            num_vars,
            group_width,
            security_level,
            WHIR_POW_BITS_V2,
            WHIR_MAX_STARTING_LOG_INV_RATE_V2,
            WHIR_FOLDING_FACTOR_V2,
            WHIR_DEDUPLICATE_IN_DOMAIN_V2,
        ))
    }

    /// Frozen constructor for the already-deployed packed-v1 transcript.
    ///
    /// v1 pre-dates the generated WHIR security constants. Its historical
    /// profile happened to share v2's values until v2 enabled explicit query
    /// grinding. Keep v1 callers isolated so a v2 schema migration cannot
    /// silently invalidate legacy proofs, fixtures, or protocol identifiers.
    pub fn for_constituents_v1(num_vars: usize, group_width: usize) -> Self {
        // `true` is part of the frozen packed-v1 WHIR profile. Do not source
        // it from a v2 generated constant.
        Self::for_constituents_with_profile(num_vars, group_width, 130, 0, 4, 4, true)
    }

    fn for_constituents_with_profile(
        num_vars: usize,
        group_width: usize,
        security_level: usize,
        pow_bits: usize,
        maximum_starting_log_inv_rate: usize,
        maximum_folding_factor: usize,
        deduplicate_in_domain: bool,
    ) -> Self {
        assert!(group_width > 0, "constituent group width must be non-zero");
        // Production packs a whole group into one vector, so factor four costs
        // only 16 base elements per initial leaf and avoids an unnecessary
        // round per packed variable. Retain factor one for generic multi-vector
        // unit-test callers, where leaf width still scales with batch size.
        let folding_factor = if group_width == 1 {
            maximum_folding_factor.min(num_vars.saturating_sub(1).max(1))
        } else {
            1
        };
        let starting_log_inv_rate = if num_vars <= folding_factor {
            1
        } else {
            maximum_starting_log_inv_rate.min(num_vars - folding_factor)
        };
        let mut pcs = Self::new(
            security_level,
            pow_bits,
            starting_log_inv_rate,
            folding_factor,
        );
        pcs.params.batch_size = group_width;
        pcs.constituent_deduplicate_in_domain = deduplicate_in_domain;
        pcs
    }

    /// Build the exact WHIR config used by the constituent protocol. Repeated
    /// in-domain indices are opened once and referenced through WHIR hints;
    /// for small codewords this reveals the whole codeword instead of emitting
    /// hundreds of duplicate multi-vector leaves.
    pub fn constituent_config(&self, size: usize) -> WhirConfig<Basefield<Field64_3>> {
        let mut config = WhirConfig::<Basefield<Field64_3>>::new(size, &self.params);
        config.initial_committer.deduplicate_in_domain = self.constituent_deduplicate_in_domain;
        for round in &mut config.round_configs {
            round.irs_committer.deduplicate_in_domain = self.constituent_deduplicate_in_domain;
        }
        config
    }

    /// Exact 64-byte WHIR protocol identifier derived from the canonical CBOR
    /// encoding of the production constituent configuration.
    pub fn constituent_protocol_id(&self, size: usize) -> [u8; 64] {
        protocol_id_for_config(&self.constituent_config(size))
    }

    /// Replay a grouped proof with the exact production preflight parser and
    /// challenge schedule, returning every native Keccak-chain checkpoint.
    ///
    /// This diagnostic API deliberately traces the production Rust verifier
    /// replay rather than maintaining a second parser. It does not instrument
    /// upstream WHIR prover call sites or the deployed Solidity verifier; the
    /// cross-language golden test pairs it with a test-only replay of the same
    /// events through Solidity's production `Keccak256Chain` primitive.
    pub fn trace_grouped_preflight(
        &self,
        num_vars: usize,
        proof: &WhirEvalProof,
        session_name: &str,
        num_groups: usize,
        num_bound_evals: usize,
    ) -> Result<Vec<WhirNativeTraceEvent>, String> {
        if num_groups == 0 || self.params.batch_size == 0 || num_bound_evals == 0 {
            return Err("grouped WHIR trace requires a non-empty statement".to_string());
        }
        let size = checked_whir_size(num_vars)?;
        let config = self.constituent_config(size);
        let proof_data = WhirProofData {
            narg_string: proof.narg_string.clone(),
            hints: proof.hints.clone(),
            #[cfg(debug_assertions)]
            // Preflight never consumes Spongefish's diagnostic pattern. Do not
            // clone caller-controlled debug metadata into this parser.
            pattern: Vec::new(),
        };
        Ok(preflight_grouped_final_fold_impl(
            &config,
            &proof_data,
            session_name,
            num_groups,
            num_bound_evals,
            true,
        )?
        .native_trace)
    }

    /// Conservative WHIR/Ext3 binding level for the complete grouped
    /// statement, including vector and linear-form combination losses.
    pub fn constituent_security_level(
        &self,
        size: usize,
        num_groups: usize,
        num_points: usize,
    ) -> f64 {
        self.constituent_config(size)
            .security_level(num_groups * self.params.batch_size, num_points)
    }

    // ═══════════════════════════════════════════════════════════════════════
    //  v1 grouped constituent API
    // ═══════════════════════════════════════════════════════════════════════

    /// Commit one or more ordered groups of constituent vectors.
    pub fn commit_grouped(
        &self,
        groups: &[Vec<Vec<ArkGoldilocks>>],
        session_name: &str,
    ) -> WhirGroupedCommitData {
        assert!(!groups.is_empty(), "must provide at least one group");
        let group_width = self.params.batch_size;
        let size = groups[0][0].len();
        assert!(size.is_power_of_two(), "vector size must be a power of two");
        let num_vars = size.trailing_zeros() as usize;

        let config = self.constituent_config(size);
        let ds = DomainSeparator::protocol(&config)
            .session(&session_name.to_string())
            .instance(&Empty);
        let mut prover_state = ProverState::new_std(&ds);
        let mut witnesses = Vec::with_capacity(groups.len());
        let mut roots = Vec::with_capacity(groups.len());

        for group in groups {
            assert_eq!(group.len(), group_width, "group width mismatch");
            for vector in group {
                assert_eq!(vector.len(), size, "constituent vector size mismatch");
            }
            let refs: Vec<&[ArkGoldilocks]> = group.iter().map(Vec::as_slice).collect();
            let witness = config.commit(&mut prover_state, &refs);
            let root = witness.matrix_witness.root().0;
            // The commitment protocol already writes this root internally.
            // Repeat it as an explicit typed statement after the commitment's
            // OOD cycle so the outer MLE transcript root can be equality-bound
            // without relying on private WHIR commitment fields.
            prover_state.prover_message(&root);
            roots.push(root.to_vec());
            witnesses.push(witness);
        }

        WhirGroupedCommitData {
            config,
            prover_state,
            witnesses,
            groups: groups.to_vec(),
            roots,
            num_vars,
            group_width,
            #[cfg(test)]
            session_name: session_name.to_string(),
        }
    }

    /// Commit another challenge-dependent group in the same WHIR session.
    pub fn commit_additional_group(
        &self,
        data: &mut WhirGroupedCommitData,
        group: Vec<Vec<ArkGoldilocks>>,
    ) -> Vec<u8> {
        assert_eq!(group.len(), data.group_width, "group width mismatch");
        let size = 1usize << data.num_vars;
        for vector in &group {
            assert_eq!(vector.len(), size, "constituent vector size mismatch");
        }
        let refs: Vec<&[ArkGoldilocks]> = group.iter().map(Vec::as_slice).collect();
        let witness = data.config.commit(&mut data.prover_state, &refs);
        let root_array = witness.matrix_witness.root().0;
        data.prover_state.prover_message(&root_array);
        let root = root_array.to_vec();
        data.witnesses.push(witness);
        data.groups.push(group);
        data.roots.push(root.clone());
        root
    }

    /// Open every constituent in every group at every requested point.
    ///
    /// The complete evaluation matrix is written into the WHIR transcript
    /// before `Config::prove` samples its Ext3 vector RLC.  This ordering is
    /// essential: without it, an adversary can choose evaluation deltas in the
    /// post-challenge RLC kernel even though the constituent roots came first.
    pub fn prove_grouped_with_eval(
        &self,
        mut data: WhirGroupedCommitData,
        eval_points: &[&[Field64_3]],
    ) -> (WhirEvalProof, Vec<Vec<Field64_3>>) {
        assert!(
            !eval_points.is_empty(),
            "at least one evaluation point is required"
        );
        for point in eval_points {
            assert_eq!(
                point.len(),
                data.num_vars,
                "evaluation point width mismatch"
            );
        }

        let flat_vectors: Vec<&Vec<ArkGoldilocks>> =
            data.groups.iter().flat_map(|group| group.iter()).collect();
        let points_ext3: Vec<Vec<Field64_3>> = eval_points
            .iter()
            .map(|point| {
                // The MLE layer numbers variables LSB-first. WHIR's evaluator
                // consumes the first point coordinate as the highest table bit,
                // so the byte-exact bridge reverses coordinates here.
                point.iter().rev().copied().collect()
            })
            .collect();
        let per_point_evals: Vec<Vec<Field64_3>> = points_ext3
            .iter()
            .map(|point| {
                let lf = MultilinearExtension::new(point.clone());
                flat_vectors
                    .iter()
                    .map(|evals| lf.evaluate(data.config.embedding(), evals.as_slice()))
                    .collect()
            })
            .collect();
        let evaluations: Vec<Field64_3> = per_point_evals.iter().flatten().copied().collect();
        #[cfg(test)]
        let num_bound_evals = evaluations.len();

        // Public-statement binding before WHIR's vector RLC challenge.
        for evaluation in &evaluations {
            data.prover_state.prover_message(evaluation);
        }

        let vectors: Vec<Cow<'_, [ArkGoldilocks]>> = flat_vectors
            .iter()
            .map(|evals| Cow::Borrowed(evals.as_slice()))
            .collect();
        let witnesses: Vec<Cow<'_, WhirWitness<Field64_3, Basefield<Field64_3>>>> =
            data.witnesses.iter().map(Cow::Borrowed).collect();
        let linear_forms: Vec<Box<dyn LinearForm<Field64_3>>> = points_ext3
            .into_iter()
            .map(|point| {
                Box::new(MultilinearExtension::new(point)) as Box<dyn LinearForm<Field64_3>>
            })
            .collect();

        let _final_claim = data.config.prove(
            &mut data.prover_state,
            vectors,
            witnesses,
            linear_forms,
            Cow::Owned(evaluations),
        );
        let proof = data.prover_state.proof();

        #[cfg(test)]
        {
            let replay = preflight_grouped_final_fold_impl(
                &data.config,
                &proof,
                &data.session_name,
                data.groups.len(),
                num_bound_evals,
                true,
            )
            .expect("grouped WHIR preflight must replay prover transcript");
            assert_eq!(
                replay.native_trace.last().map(|event| event.kind),
                Some(WhirNativeTraceEventKind::Eof),
                "grouped WHIR prover transcript trace must reach exact EOF"
            );
            let final_rounds = data.config.final_sumcheck.num_rounds;
            let final_point_start = _final_claim
                .evaluation_point
                .len()
                .checked_sub(final_rounds)
                .expect("WHIR final point length");
            assert_eq!(
                replay.final_randomness,
                _final_claim.evaluation_point[final_point_start..],
                "grouped WHIR preflight diverged from prover transcript"
            );
        }
        (
            WhirEvalProof {
                narg_string: proof.narg_string,
                hints: proof.hints,
                #[cfg(debug_assertions)]
                pattern: proof.pattern,
            },
            per_point_evals,
        )
    }

    /// Verify the grouped constituent statement and its pre-RLC evaluation
    /// binding.
    // Keep each independently checked part of the PCS statement explicit.
    #[allow(clippy::too_many_arguments)]
    pub fn verify_grouped(
        &self,
        num_vars: usize,
        proof: &WhirEvalProof,
        expected_evals: &[Option<Field64_3>],
        session_name: &str,
        eval_points: &[&[Field64_3]],
        num_groups: usize,
        expected_roots: &[&[u8]],
    ) -> Result<(), String> {
        if num_groups == 0 || self.params.batch_size == 0 {
            return Err("grouped WHIR requires non-empty groups".to_string());
        }
        let total_vectors = num_groups
            .checked_mul(self.params.batch_size)
            .ok_or_else(|| "grouped WHIR vector count overflow".to_string())?;
        let expected_eval_count = eval_points
            .len()
            .checked_mul(total_vectors)
            .ok_or_else(|| "grouped WHIR evaluation count overflow".to_string())?;
        if expected_evals.len() != expected_eval_count {
            return Err("grouped WHIR evaluation shape mismatch".to_string());
        }
        if expected_roots.len() != num_groups || expected_roots.iter().any(|root| root.len() != 32)
        {
            return Err("grouped WHIR root shape mismatch".to_string());
        }
        if eval_points.is_empty() || eval_points.iter().any(|point| point.len() != num_vars) {
            return Err("grouped WHIR query-point shape mismatch".to_string());
        }
        let size = checked_whir_size(num_vars)?;
        let config = self.constituent_config(size);
        // Root positions are fixed by the config, unlike later query-dependent
        // hint positions. Bind both copies before transcript replay so a bad
        // root cannot steer preflight challenges and mask the root error.
        let initial_ood_bytes = config
            .initial_committer
            .out_domain_samples
            .checked_mul(config.initial_committer.num_vectors)
            .and_then(|count| count.checked_mul(FIELD64_3_NARG_BYTES))
            .ok_or_else(|| "WHIR initial commitment byte count overflow".to_string())?;
        let commitment_stride = 32usize
            .checked_add(initial_ood_bytes)
            .and_then(|count| count.checked_add(32))
            .ok_or_else(|| "WHIR initial commitment stride overflow".to_string())?;
        for (group, expected_root) in expected_roots.iter().enumerate() {
            let actual_root_start = group
                .checked_mul(commitment_stride)
                .ok_or_else(|| "WHIR commitment root offset overflow".to_string())?;
            let actual_root_end = actual_root_start
                .checked_add(32)
                .ok_or_else(|| "WHIR commitment root end overflow".to_string())?;
            let actual_root = proof
                .narg_string
                .get(actual_root_start..actual_root_end)
                .ok_or_else(|| "WHIR commitment root is truncated".to_string())?;
            if actual_root != *expected_root {
                return Err(
                    "WHIR actual commitment root does not match outer transcript".to_string(),
                );
            }
            let bound_root_start = actual_root_end
                .checked_add(initial_ood_bytes)
                .ok_or_else(|| "WHIR bound root offset overflow".to_string())?;
            let bound_root_end = bound_root_start
                .checked_add(32)
                .ok_or_else(|| "WHIR bound root end overflow".to_string())?;
            let bound_root = proof
                .narg_string
                .get(bound_root_start..bound_root_end)
                .ok_or_else(|| "WHIR bound root is truncated".to_string())?;
            if bound_root != *expected_root {
                return Err("WHIR commitment root does not match outer transcript".to_string());
            }
        }
        let ds = DomainSeparator::protocol(&config)
            .session(&session_name.to_string())
            .instance(&Empty);
        #[allow(unused_mut)]
        let mut proof_data = WhirProofData {
            narg_string: proof.narg_string.clone(),
            hints: proof.hints.clone(),
            #[cfg(debug_assertions)]
            // This is reconstructed below from the validated byte grammar.
            // Caller-supplied debug metadata is not part of the proof.
            pattern: Vec::new(),
        };
        let preflight = preflight_grouped_final_fold(
            &config,
            &proof_data,
            session_name,
            num_groups,
            expected_evals.len(),
        )?;
        #[cfg(debug_assertions)]
        {
            proof_data.pattern =
                grouped_pattern_from_trace(&preflight.native_trace, &proof_data.hints)?;
        }
        if preflight.polynomial_eval == Field64_3::default() {
            return Err("WHIR final folded polynomial evaluates to zero".to_string());
        }
        let mut verifier_state = VerifierState::new_std(&ds, &proof_data);
        let mut commitments = Vec::with_capacity(num_groups);
        for expected_root in expected_roots {
            let commitment = config
                .receive_commitment(&mut verifier_state)
                .map_err(|e| format!("WHIR group commitment failed: {e:?}"))?;
            let bound_root: [u8; 32] = verifier_state
                .prover_message()
                .map_err(|e| format!("WHIR bound root decode failed: {e:?}"))?;
            if bound_root.as_slice() != *expected_root {
                return Err("WHIR commitment root does not match outer transcript".to_string());
            }
            commitments.push(commitment);
        }

        // Compare the transcript-bound claims byte-for-byte before WHIR draws
        // the vector-combination challenge.
        let mut bound_evals = Vec::with_capacity(expected_evals.len());
        for (index, expected) in expected_evals.iter().enumerate() {
            let bound: Field64_3 = verifier_state
                .prover_message()
                .map_err(|e| format!("WHIR bound evaluation decode failed: {e:?}"))?;
            if let Some(expected) = expected {
                if bound != *expected {
                    return Err(format!(
                        "WHIR bound evaluation mismatch at {index}: bound={bound:?}, expected={expected:?}"
                    ));
                }
            }
            bound_evals.push(bound);
        }

        let commitment_refs: Vec<&_> = commitments.iter().collect();
        let final_claim = catch_whir_verifier_panic("WHIR grouped verification", || {
            config.verify(&mut verifier_state, &commitment_refs, &bound_evals)
        })?
        .map_err(|e| format!("WHIR grouped verification failed: {e:?}"))?;
        let linear_forms: Vec<Box<dyn LinearForm<Field64_3>>> = eval_points
            .iter()
            .map(|point| {
                let ext3 = point.iter().rev().copied().collect();
                Box::new(MultilinearExtension::new(ext3)) as Box<dyn LinearForm<Field64_3>>
            })
            .collect();
        final_claim
            .verify(linear_forms.iter().map(|form| form.as_ref()))
            .map_err(|e| format!("WHIR grouped final claim failed: {e:?}"))?;
        verifier_state
            .check_eof()
            .map_err(|e| format!("WHIR grouped proof not fully consumed: {e:?}"))?;
        Ok(())
    }

    // ═══════════════════════════════════════════════════════════════════════
    //  Split-commit API (unified proof for multiple vectors)
    // ═══════════════════════════════════════════════════════════════════════

    /// Compute the WHIR commitment root for a preprocessed polynomial.
    ///
    /// Uses WHIR_SESSION_SPLIT for domain separation to match the
    /// split-commit proving flow.
    ///
    /// SECURITY: The commitment root binds the prover to a specific polynomial.
    /// Changing any evaluation changes the Merkle root. The root is the first
    /// 32 bytes of the WHIR proof output, deterministic for a given polynomial
    /// + WHIR parameters + session name.
    pub fn commit_root(&self, poly: &DenseMultilinearExtension<GoldilocksField>) -> Vec<u8> {
        let num_vars = poly.num_vars;
        let size = 1 << num_vars;
        let ark_evals = plonky2_vec_to_ark(&poly.evaluations);

        let config = WhirConfig::<Basefield<Field64_3>>::new(size, &self.params);
        let ds = DomainSeparator::protocol(&config)
            .session(&WHIR_SESSION_SPLIT.to_string())
            .instance(&Empty);

        let mut prover_state = ProverState::new_std(&ds);
        // Commit a single vector to get its deterministic Merkle root.
        // The root is written as the first prover_message_hash in the transcript.
        let _witness = config.commit(&mut prover_state, &[&ark_evals]);
        let proof = prover_state.proof();
        proof.narg_string[..32.min(proof.narg_string.len())].to_vec()
    }

    /// Begin a phased split-commit by committing initial vectors.
    ///
    /// Each vector gets its own Merkle tree and root. The returned
    /// `WhirSplitCommitData` can be extended with `commit_additional`
    /// before calling `prove_split_with_eval`.
    ///
    /// SECURITY: The `session_name` creates domain separation.
    pub fn commit_split(
        &self,
        evals_list: &[&[ArkGoldilocks]],
        session_name: &str,
    ) -> WhirSplitCommitData {
        assert!(!evals_list.is_empty(), "Must provide at least one vector");
        let size = evals_list[0].len();
        let num_vars = size.trailing_zeros() as usize;
        assert!(size.is_power_of_two(), "Vector size must be a power of 2");
        for evals in evals_list {
            assert_eq!(evals.len(), size, "All vectors must have the same size");
        }

        let config = WhirConfig::<Basefield<Field64_3>>::new(size, &self.params);
        let ds = DomainSeparator::protocol(&config)
            .session(&session_name.to_string())
            .instance(&Empty);

        let mut prover_state = ProverState::new_std(&ds);

        // Use commit_single for each vector (phased approach).
        let mut witnesses = Vec::with_capacity(evals_list.len());
        let mut roots = Vec::with_capacity(evals_list.len());
        for evals in evals_list {
            let (witness, root) = config.commit_single(&mut prover_state, evals);
            roots.push(root.0.to_vec());
            witnesses.push(witness);
        }

        let ark_evals_list: Vec<Vec<ArkGoldilocks>> =
            evals_list.iter().map(|evals| evals.to_vec()).collect();

        WhirSplitCommitData {
            config,
            prover_state,
            witnesses,
            ark_evals_list,
            roots,
            num_vars,
        }
    }

    /// Add an additional vector to a phased split-commit session.
    ///
    /// Call this after deriving challenges from earlier commitment roots
    /// and computing challenge-dependent polynomials (e.g., C̃, h̃).
    ///
    /// SECURITY: The new vector is committed to the same WHIR transcript,
    /// ensuring cross-term OOD binding with all previous vectors.
    pub fn commit_additional(
        &self,
        commit_data: &mut WhirSplitCommitData,
        evals: &[ArkGoldilocks],
    ) -> Vec<u8> {
        let size = 1 << commit_data.num_vars;
        assert_eq!(evals.len(), size, "Additional vector size mismatch");

        let (witness, root) = commit_data
            .config
            .commit_single(&mut commit_data.prover_state, evals);
        let root_bytes = root.0.to_vec();
        commit_data.roots.push(root_bytes.clone());
        commit_data.witnesses.push(witness);
        commit_data.ark_evals_list.push(evals.to_vec());
        root_bytes
    }

    /// Generate a unified WHIR proof for split-committed vectors at one or more
    /// evaluation points.
    ///
    /// Each evaluation point becomes a separate `LinearForm` in the WHIR proof.
    /// Evaluations are returned per-point, per-vector (outer: points, inner: vectors).
    ///
    /// SECURITY: The evaluation values are computed internally using WHIR's
    /// embedding to ensure consistency with how WHIR verifies. Each evaluation
    /// point should be a sumcheck output point (e.g., constraint r, permutation
    /// r_perm) so that WHIR directly binds polynomial evaluations at the points
    /// where the verifier needs them.
    pub fn prove_split_with_eval(
        &self,
        mut commit_data: WhirSplitCommitData,
        eval_points: &[&[GoldilocksField]],
    ) -> (WhirEvalProof, Vec<Vec<Field64_3>>) {
        let num_vars = commit_data.num_vars;
        let num_vectors = commit_data.ark_evals_list.len();
        assert!(
            !eval_points.is_empty(),
            "SECURITY: At least one evaluation point is required"
        );
        for (i, pt) in eval_points.iter().enumerate() {
            assert_eq!(
                pt.len(),
                num_vars,
                "SECURITY: eval_points[{i}] length {} must match num_vars {num_vars}",
                pt.len()
            );
        }

        // Convert each evaluation point to Ext3 and build LinearForms.
        let points_ext3: Vec<Vec<Field64_3>> = eval_points
            .iter()
            .map(|pt| {
                pt.iter()
                    .map(|f| Field64_3::from(f.to_canonical_u64()))
                    .collect()
            })
            .collect();

        // Evaluate each vector at each point.
        // Layout: per_point_evals[point_idx] = [vec_0_eval, vec_1_eval, ...]
        let per_point_evals: Vec<Vec<Field64_3>> = points_ext3
            .iter()
            .map(|pt| {
                let lf = MultilinearExtension::new(pt.clone());
                commit_data
                    .ark_evals_list
                    .iter()
                    .map(|evals| lf.evaluate(commit_data.config.embedding(), evals))
                    .collect()
            })
            .collect();

        // Flatten evaluations: row-major (num_linear_forms × num_vectors).
        let evaluations: Vec<Field64_3> = per_point_evals.iter().flatten().copied().collect();
        assert_eq!(evaluations.len(), eval_points.len() * num_vectors);

        // Build LinearForms — one per evaluation point.
        let prove_lf: Vec<Box<dyn LinearForm<Field64_3>>> = points_ext3
            .into_iter()
            .map(|pt| Box::new(MultilinearExtension::new(pt)) as Box<dyn LinearForm<Field64_3>>)
            .collect();

        // Build vectors for prove_split.
        let vectors: Vec<Cow<'_, [ArkGoldilocks]>> = commit_data
            .ark_evals_list
            .iter()
            .map(|evals| Cow::Borrowed(evals.as_slice()))
            .collect();

        // Build SplitWitness from individually collected witnesses.
        let roots: Vec<whir::hash::Hash> = commit_data
            .roots
            .iter()
            .map(|r| {
                let mut arr = [0u8; 32];
                arr.copy_from_slice(&r[..32]);
                whir::hash::Hash(arr)
            })
            .collect();
        let split_witness = SplitWitness::new(commit_data.witnesses, roots);

        let _final_claim = commit_data.config.prove_split(
            &mut commit_data.prover_state,
            vectors,
            split_witness,
            prove_lf,
            Cow::Owned(evaluations),
        );

        let proof = commit_data.prover_state.proof();

        let eval_proof = WhirEvalProof {
            narg_string: proof.narg_string,
            hints: proof.hints,
            #[cfg(debug_assertions)]
            pattern: proof.pattern,
        };

        (eval_proof, per_point_evals)
    }

    /// Verify a unified WHIR proof for split-committed vectors at one or more
    /// evaluation points.
    ///
    /// SECURITY: The session name must match the one used during proving.
    /// `eval_values` is flattened row-major: [point_0_vec_0, point_0_vec_1, ...,
    /// point_1_vec_0, point_1_vec_1, ...]. `num_vectors` is the number of
    /// committed vectors (typically 2: preprocessed + witness).
    pub fn verify_split(
        &self,
        num_vars: usize,
        proof: &WhirEvalProof,
        eval_values: &[Field64_3],
        session_name: &str,
        eval_points: &[&[GoldilocksField]],
        num_vectors: usize,
    ) -> Result<(), String> {
        if eval_points.is_empty() || num_vectors == 0 {
            return Err("WHIR split verification requires points and vectors".to_string());
        }
        let expected_eval_count = eval_points
            .len()
            .checked_mul(num_vectors)
            .ok_or_else(|| "WHIR split evaluation count overflow".to_string())?;
        if eval_values.len() != expected_eval_count {
            return Err("WHIR split evaluation shape mismatch".to_string());
        }
        if eval_points.iter().any(|point| point.len() != num_vars) {
            return Err("WHIR split query-point shape mismatch".to_string());
        }

        let size = checked_whir_size(num_vars)?;

        let config = WhirConfig::<Basefield<Field64_3>>::new(size, &self.params);
        let ds = DomainSeparator::protocol(&config)
            .session(&session_name.to_string())
            .instance(&Empty);

        let proof_data = WhirProofData {
            narg_string: proof.narg_string.clone(),
            hints: proof.hints.clone(),
            #[cfg(debug_assertions)]
            pattern: proof.pattern.clone(),
        };

        let mut verifier_state = VerifierState::new_std(&ds, &proof_data);

        // Receive per-vector commitments (split mode).
        let commitments = config
            .receive_split_commitment(&mut verifier_state, num_vectors)
            .map_err(|e| format!("WHIR split commitment verification failed: {:?}", e))?;
        let commitment_refs: Vec<&_> = commitments.iter().collect();

        // Verify the combined proof.
        let final_claim = catch_whir_verifier_panic("WHIR split verification", || {
            config.verify_split(&mut verifier_state, &commitment_refs, eval_values)
        })?
        .map_err(|e| format!("WHIR split verification failed: {:?}", e))?;

        // Build LinearForms — one per evaluation point.
        let verify_lf: Vec<Box<dyn LinearForm<Field64_3>>> = eval_points
            .iter()
            .map(|pt| {
                let ext3: Vec<Field64_3> = pt
                    .iter()
                    .map(|f| Field64_3::from(f.to_canonical_u64()))
                    .collect();
                Box::new(MultilinearExtension::new(ext3)) as Box<dyn LinearForm<Field64_3>>
            })
            .collect();

        final_claim
            .verify(
                verify_lf
                    .iter()
                    .map(|l| l.as_ref() as &dyn LinearForm<Field64_3>),
            )
            .map_err(|e| format!("WHIR split evaluation verification failed: {:?}", e))?;

        verifier_state
            .check_eof()
            .map_err(|e| format!("WHIR split proof not fully consumed: {:?}", e))?;

        Ok(())
    }

    // ═══════════════════════════════════════════════════════════════════════
    //  Auxiliary single-vector API (commit + multi-point prove)
    // ═══════════════════════════════════════════════════════════════════════

    /// Commit and prove a single auxiliary polynomial at multiple evaluation points.
    ///
    /// Used for the auxiliary commitment round: after challenges are derived,
    /// the prover commits C̃ and h̃ (batched into one polynomial) and proves
    /// evaluation at both the constraint point r and the permutation point r_perm.
    ///
    /// Returns (commitment_root, proof, per_point_evals).
    ///
    /// SECURITY: Uses a dedicated session name to prevent cross-protocol confusion
    /// with the main split-commit WHIR proof. The auxiliary polynomial binds
    /// C̃(r) and h̃(r_perm) to the committed polynomial, closing the oracle gap.
    pub fn commit_and_prove_aux(
        &self,
        poly: &DenseMultilinearExtension<GoldilocksField>,
        eval_points: &[&[GoldilocksField]],
        session_name: &str,
    ) -> (Vec<u8>, WhirEvalProof, Vec<Field64_3>) {
        let num_vars = poly.num_vars;
        let size = 1 << num_vars;
        let ark_evals = plonky2_vec_to_ark(&poly.evaluations);

        assert!(
            !eval_points.is_empty(),
            "SECURITY: At least one evaluation point required"
        );
        for (i, pt) in eval_points.iter().enumerate() {
            assert_eq!(
                pt.len(),
                num_vars,
                "SECURITY: eval_points[{i}] length must match num_vars {num_vars}"
            );
        }

        let config = WhirConfig::<Basefield<Field64_3>>::new(size, &self.params);
        let ds = DomainSeparator::protocol(&config)
            .session(&session_name.to_string())
            .instance(&Empty);

        let mut prover_state = ProverState::new_std(&ds);
        let witness = config.commit(&mut prover_state, &[&ark_evals]);

        // Extract commitment root (first 32 bytes of transcript).
        let commit_proof = prover_state.proof();
        let root = commit_proof.narg_string[..32.min(commit_proof.narg_string.len())].to_vec();
        // Reset prover state — we need to re-create it because proof() consumes state.
        // Instead, re-do the commit to get fresh prover_state for proving.
        let mut prover_state = ProverState::new_std(&ds);
        let _witness = config.commit(&mut prover_state, &[&ark_evals]);

        // Build LinearForms and evaluate at each point.
        let points_ext3: Vec<Vec<Field64_3>> = eval_points
            .iter()
            .map(|pt| {
                pt.iter()
                    .map(|f| Field64_3::from(f.to_canonical_u64()))
                    .collect()
            })
            .collect();

        let per_point_evals: Vec<Field64_3> = points_ext3
            .iter()
            .map(|pt| {
                let lf = MultilinearExtension::new(pt.clone());
                lf.evaluate(config.embedding(), &ark_evals)
            })
            .collect();

        let prove_lf: Vec<Box<dyn LinearForm<Field64_3>>> = points_ext3
            .into_iter()
            .map(|pt| Box::new(MultilinearExtension::new(pt)) as Box<dyn LinearForm<Field64_3>>)
            .collect();

        let _final_claim = config.prove(
            &mut prover_state,
            vec![Cow::Borrowed(ark_evals.as_slice())],
            vec![Cow::Owned(witness)],
            prove_lf,
            Cow::Owned(per_point_evals.clone()),
        );

        let proof = prover_state.proof();

        let eval_proof = WhirEvalProof {
            narg_string: proof.narg_string,
            hints: proof.hints,
            #[cfg(debug_assertions)]
            pattern: proof.pattern,
        };

        (root, eval_proof, per_point_evals)
    }

    /// Verify a single-vector auxiliary WHIR proof at multiple evaluation points.
    ///
    /// SECURITY: Session name must match the one used during proving.
    pub fn verify_aux(
        &self,
        num_vars: usize,
        proof: &WhirEvalProof,
        eval_values: &[Field64_3],
        eval_points: &[&[GoldilocksField]],
        session_name: &str,
    ) -> Result<(), String> {
        if eval_points.is_empty() || eval_values.len() != eval_points.len() {
            return Err("WHIR auxiliary evaluation shape mismatch".to_string());
        }
        if eval_points.iter().any(|point| point.len() != num_vars) {
            return Err("WHIR auxiliary query-point shape mismatch".to_string());
        }

        let size = checked_whir_size(num_vars)?;
        let config = WhirConfig::<Basefield<Field64_3>>::new(size, &self.params);
        let ds = DomainSeparator::protocol(&config)
            .session(&session_name.to_string())
            .instance(&Empty);

        let proof_data = WhirProofData {
            narg_string: proof.narg_string.clone(),
            hints: proof.hints.clone(),
            #[cfg(debug_assertions)]
            pattern: proof.pattern.clone(),
        };

        let mut verifier_state = VerifierState::new_std(&ds, &proof_data);

        let commitment = config
            .receive_commitment(&mut verifier_state)
            .map_err(|e| format!("WHIR aux commitment verification failed: {:?}", e))?;

        let final_claim = catch_whir_verifier_panic("WHIR auxiliary verification", || {
            config.verify(&mut verifier_state, &[&commitment], eval_values)
        })?
        .map_err(|e| format!("WHIR aux verification failed: {:?}", e))?;

        let verify_lf: Vec<Box<dyn LinearForm<Field64_3>>> = eval_points
            .iter()
            .map(|pt| {
                let ext3: Vec<Field64_3> = pt
                    .iter()
                    .map(|f| Field64_3::from(f.to_canonical_u64()))
                    .collect();
                Box::new(MultilinearExtension::new(ext3)) as Box<dyn LinearForm<Field64_3>>
            })
            .collect();

        final_claim
            .verify(
                verify_lf
                    .iter()
                    .map(|l| l.as_ref() as &dyn LinearForm<Field64_3>),
            )
            .map_err(|e| format!("WHIR aux evaluation verification failed: {:?}", e))?;

        verifier_state
            .check_eof()
            .map_err(|e| format!("WHIR aux proof not fully consumed: {:?}", e))?;

        Ok(())
    }

    // ═══════════════════════════════════════════════════════════════════════
    //  Legacy single-vector API (kept for backward compatibility)
    // ═══════════════════════════════════════════════════════════════════════

    /// Generate a WHIR proof with evaluation binding at a specific point.
    ///
    /// SECURITY: The evaluation value is computed internally using WHIR's
    /// `mixed_multilinear_extend` to ensure consistency with how WHIR verifies.
    /// If `eval_point` is None, uses a canonical evaluation point.
    /// Returns (commitment, proof, whir_eval_value) where whir_eval_value is the
    /// evaluation computed via WHIR's mixed_multilinear_extend (needed for verify).
    pub fn prove_at_point(
        &self,
        poly: &DenseMultilinearExtension<GoldilocksField>,
        eval_point: Option<&[GoldilocksField]>,
        _eval_value: Option<GoldilocksField>,
    ) -> (WhirCommitment, WhirEvalProof, Field64_3) {
        self.prove_at_point_with_session(poly, eval_point, WHIR_SESSION_NAME)
    }

    /// Generate a WHIR proof with a custom session name for domain separation.
    ///
    /// SECURITY: Different sub-protocols (preprocessed vs witness) MUST use
    /// different session names to prevent cross-protocol proof swapping.
    pub fn prove_at_point_with_session(
        &self,
        poly: &DenseMultilinearExtension<GoldilocksField>,
        eval_point: Option<&[GoldilocksField]>,
        session_name: &str,
    ) -> (WhirCommitment, WhirEvalProof, Field64_3) {
        let num_vars = poly.num_vars;
        let size = 1 << num_vars;
        let ark_evals = plonky2_vec_to_ark(&poly.evaluations);

        let config = WhirConfig::<Basefield<Field64_3>>::new(size, &self.params);
        let ds = DomainSeparator::protocol(&config)
            .session(&session_name.to_string())
            .instance(&Empty);

        let mut prover_state = ProverState::new_std(&ds);
        let witness = config.commit(&mut prover_state, &[&ark_evals]);

        // Build evaluation point — always compute value via WHIR's own evaluate()
        // to ensure consistency with verifier-side computation.
        let point_ext3: Vec<Field64_3> = if let Some(pt) = eval_point {
            pt.iter()
                .map(|f| Field64_3::from(f.to_canonical_u64()))
                .collect()
        } else {
            (0..num_vars)
                .map(|i| Field64_3::from((i + 1) as u64))
                .collect()
        };
        let lf = MultilinearExtension::new(point_ext3.clone());
        let eval_ext3 = lf.evaluate(config.embedding(), &ark_evals);

        let prove_lf: Vec<Box<dyn LinearForm<Field64_3>>> =
            vec![Box::new(MultilinearExtension::new(point_ext3))];

        let _final_claim = config.prove(
            &mut prover_state,
            vec![Cow::Borrowed(ark_evals.as_slice())],
            vec![Cow::Owned(witness)],
            prove_lf,
            Cow::Owned(vec![eval_ext3]),
        );

        let proof = prover_state.proof();

        (
            WhirCommitment {
                proof_bytes: proof.narg_string.clone(),
            },
            WhirEvalProof {
                narg_string: proof.narg_string,
                hints: proof.hints,
                #[cfg(debug_assertions)]
                pattern: proof.pattern,
            },
            eval_ext3,
        )
    }

    /// Generate a WHIR proof with canonical evaluation point (legacy API).
    pub fn prove(
        &self,
        poly: &DenseMultilinearExtension<GoldilocksField>,
    ) -> (WhirCommitment, WhirEvalProof) {
        let (c, p, _) = self.prove_at_point(poly, None, None);
        (c, p)
    }

    /// Verify a WHIR proof with evaluation binding.
    ///
    /// If `eval_point` is provided, verifies that the committed polynomial
    /// evaluates correctly at that point (via WHIR's FinalClaim + linear form).
    /// `eval_value` is the expected evaluation (used as the claimed sum).
    /// If None, verifies only the commitment.
    /// Available only for historical `legacy-conformance`; use the bound
    /// grouped statement through the current MLE verifier in production.
    #[cfg(feature = "legacy-conformance")]
    pub fn verify(
        &self,
        num_vars: usize,
        proof: &WhirEvalProof,
        eval_point: Option<&[GoldilocksField]>,
        eval_value_ext3: Option<Field64_3>,
    ) -> Result<(), String> {
        self.verify_with_session(
            num_vars,
            proof,
            eval_point,
            eval_value_ext3,
            WHIR_SESSION_NAME,
        )
    }

    /// Verify a WHIR proof with a custom session name.
    ///
    /// SECURITY: The session name must match the one used during proving.
    /// Different sub-protocols use different session names to prevent
    /// cross-protocol proof confusion.
    /// Available only for historical `legacy-conformance` because an omitted
    /// evaluation skips the final linear-form check.
    #[cfg(feature = "legacy-conformance")]
    pub fn verify_with_session(
        &self,
        num_vars: usize,
        proof: &WhirEvalProof,
        eval_point: Option<&[GoldilocksField]>,
        eval_value_ext3: Option<Field64_3>,
        session_name: &str,
    ) -> Result<(), String> {
        if eval_point.is_some_and(|point| point.len() != num_vars) {
            return Err("WHIR query-point shape mismatch".to_string());
        }
        let size = checked_whir_size(num_vars)?;

        let config = WhirConfig::<Basefield<Field64_3>>::new(size, &self.params);
        let ds = DomainSeparator::protocol(&config)
            .session(&session_name.to_string())
            .instance(&Empty);

        let proof_data = WhirProofData {
            narg_string: proof.narg_string.clone(),
            hints: proof.hints.clone(),
            #[cfg(debug_assertions)]
            pattern: proof.pattern.clone(),
        };

        let mut verifier_state = VerifierState::new_std(&ds, &proof_data);

        let commitment = config
            .receive_commitment(&mut verifier_state)
            .map_err(|e| format!("WHIR commitment verification failed: {:?}", e))?;

        // Build evaluation point — must match prover's prove_at_point_with_session.
        // The prover always includes an evaluation at some point (canonical if None).
        // The verifier must match this exactly for transcript consistency.
        let point_ext3: Vec<Field64_3> = if let Some(pt) = eval_point {
            pt.iter()
                .map(|f| Field64_3::from(f.to_canonical_u64()))
                .collect()
        } else {
            // Canonical evaluation point (1, 2, 3, ..., n) — must match prover
            (0..num_vars)
                .map(|i| Field64_3::from((i + 1) as u64))
                .collect()
        };

        let has_eval_binding = eval_value_ext3.is_some();
        let evaluations: Vec<Field64_3> = if let Some(val) = eval_value_ext3 {
            vec![val]
        } else {
            // No expected value provided. We still must pass the evaluation
            // structure to match the prover's transcript (the prover always
            // includes an evaluation). We use a placeholder — the FinalClaim
            // linear form check will be skipped below.
            vec![Field64_3::from(0u64)]
        };

        let verify_lf: Vec<Box<dyn LinearForm<Field64_3>>> =
            vec![Box::new(MultilinearExtension::new(point_ext3)) as Box<dyn LinearForm<Field64_3>>];

        let final_claim = catch_whir_verifier_panic("WHIR verification", || {
            config.verify(&mut verifier_state, &[&commitment], &evaluations)
        })?
        .map_err(|e| format!("WHIR verification failed: {:?}", e))?;

        // Verify the linear form (evaluation at the claimed point).
        // Only check when the caller provided an expected eval value.
        // The proximity test (WHIR commitment binding) is always verified
        // by config.verify() above regardless.
        if has_eval_binding {
            final_claim
                .verify(
                    verify_lf
                        .iter()
                        .map(|l| l.as_ref() as &dyn LinearForm<Field64_3>),
                )
                .map_err(|e| format!("WHIR evaluation verification failed: {:?}", e))?;
        }

        verifier_state
            .check_eof()
            .map_err(|e| format!("WHIR proof not fully consumed: {:?}", e))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::Field as _;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

    use super::*;
    use crate::proof::{
        constituent_index_bits, packed_group_num_vars, NUM_PACKED_VECTORS_PER_GROUP,
        NUM_SPLIT_COMMITMENTS,
    };

    #[test]
    fn test_field_conversion_roundtrip() {
        for i in 0..100u64 {
            let p2 = GoldilocksField::from_canonical_u64(i);
            let ark = plonky2_to_ark(p2);
            let back = ark_to_plonky2(ark);
            assert_eq!(p2, back, "Roundtrip failed for {i}");
        }

        let p = 0xFFFFFFFF00000001u64;
        for offset in [0u64, 1, 2, 100, 1000, 1 << 32, 1 << 53, p - 2, p - 1] {
            let val = offset.min(p - 1);
            let p2 = GoldilocksField::from_canonical_u64(val);
            let ark = plonky2_to_ark(p2);
            let back = ark_to_plonky2(ark);
            assert_eq!(p2, back, "Roundtrip failed for val={val}");
        }
    }

    #[test]
    fn test_field_arithmetic_consistency() {
        let a_p2 = GoldilocksField::from_canonical_u64(123456789);
        let b_p2 = GoldilocksField::from_canonical_u64(987654321);

        let a_ark = plonky2_to_ark(a_p2);
        let b_ark = plonky2_to_ark(b_p2);

        assert_eq!(a_p2 + b_p2, ark_to_plonky2(a_ark + b_ark));
        assert_eq!(a_p2 * b_p2, ark_to_plonky2(a_ark * b_ark));
        assert_eq!(a_p2.inverse(), ark_to_plonky2(a_ark.inverse().unwrap()));
    }

    #[test]
    #[cfg(feature = "legacy-conformance")]
    fn test_whir_prove_verify_small() {
        let evals: Vec<GoldilocksField> = (0..16)
            .map(|i| GoldilocksField::from_canonical_u64(i + 1))
            .collect();
        let poly = DenseMultilinearExtension::new(evals);

        let pcs = WhirPCS::new(32, 0, 1, 2);
        let (_commitment, proof) = pcs.prove(&poly);

        let result = pcs.verify(poly.num_vars, &proof, None, None);
        assert!(result.is_ok(), "WHIR verify failed: {:?}", result.err());
    }

    #[test]
    #[cfg(feature = "legacy-conformance")]
    fn test_whir_prove_verify_medium() {
        let evals: Vec<GoldilocksField> = (0..256)
            .map(|i| GoldilocksField::from_canonical_u64(i * 7 + 3))
            .collect();
        let poly = DenseMultilinearExtension::new(evals);

        let pcs = WhirPCS::new(32, 0, 1, 2);
        let (_commitment, proof) = pcs.prove(&poly);

        let result = pcs.verify(poly.num_vars, &proof, None, None);
        assert!(result.is_ok(), "WHIR verify failed: {:?}", result.err());
    }

    #[test]
    #[cfg(feature = "legacy-conformance")]
    fn test_whir_prove_at_point_verify() {
        let evals: Vec<GoldilocksField> = (0..16)
            .map(|i| GoldilocksField::from_canonical_u64(i + 1))
            .collect();
        let poly = DenseMultilinearExtension::new(evals);
        let num_vars = poly.num_vars;

        let pcs = WhirPCS::new(32, 0, 1, 2);

        // Simulate a sumcheck-derived evaluation point
        let eval_point: Vec<GoldilocksField> = (0..num_vars)
            .map(|i| GoldilocksField::from_canonical_u64((i as u64) * 3 + 7))
            .collect();

        // Prove with eval binding — eval_ext3 is computed internally by prove_at_point
        let (_commitment, proof, eval_ext3) = pcs.prove_at_point(&poly, Some(&eval_point), None);

        // Verify with evaluation binding — pass the same Ext3 value
        let result = pcs.verify(num_vars, &proof, Some(&eval_point), Some(eval_ext3));
        assert!(
            result.is_ok(),
            "prove_at_point verify failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_whir_split_commit_prove_verify_single_point() {
        // Two vectors of size 16 (4 variables), single evaluation point
        let evals_a: Vec<ArkGoldilocks> = (0..16)
            .map(|i| ArkGoldilocks::from((i + 1) as u64))
            .collect();
        let evals_b: Vec<ArkGoldilocks> = (0..16)
            .map(|i| ArkGoldilocks::from((i * 3 + 7) as u64))
            .collect();

        let pcs = WhirPCS::new(32, 0, 1, 2);

        // Split commit
        let commit_data = pcs.commit_split(&[&evals_a, &evals_b], WHIR_SESSION_SPLIT);

        // Verify we got per-vector roots
        assert_eq!(commit_data.roots.len(), 2);
        assert_eq!(commit_data.roots[0].len(), 32);
        assert_eq!(commit_data.roots[1].len(), 32);
        assert_ne!(commit_data.roots[0], commit_data.roots[1]);

        let num_vars = commit_data.num_vars;

        // Simulate sumcheck output point (non-canonical)
        let eval_point: Vec<GoldilocksField> = (0..num_vars)
            .map(|i| GoldilocksField::from_canonical_u64((i as u64) * 3 + 7))
            .collect();

        // Prove at sumcheck output point
        let (eval_proof, per_point_evals) = pcs.prove_split_with_eval(commit_data, &[&eval_point]);
        assert_eq!(per_point_evals.len(), 1); // 1 point
        assert_eq!(per_point_evals[0].len(), 2); // 2 vectors

        // Flatten evaluations for verify
        let flat_evals: Vec<Field64_3> = per_point_evals.into_iter().flatten().collect();

        // Verify
        let result = pcs.verify_split(
            num_vars,
            &eval_proof,
            &flat_evals,
            WHIR_SESSION_SPLIT,
            &[&eval_point],
            2, // num_vectors
        );
        assert!(result.is_ok(), "Split verify failed: {:?}", result.err());

        let mut trailing_hint = eval_proof.clone();
        trailing_hint.hints.push(0);
        let err = pcs
            .verify_split(
                num_vars,
                &trailing_hint,
                &flat_evals,
                WHIR_SESSION_SPLIT,
                &[&eval_point],
                2,
            )
            .expect_err("split verifier accepted a trailing hint byte");
        assert!(
            err.contains("not fully consumed"),
            "unexpected trailing-hint error: {err}"
        );

        let mut trailing_narg = eval_proof.clone();
        trailing_narg.narg_string.push(0);
        let err = pcs
            .verify_split(
                num_vars,
                &trailing_narg,
                &flat_evals,
                WHIR_SESSION_SPLIT,
                &[&eval_point],
                2,
            )
            .expect_err("split verifier accepted a trailing transcript byte");
        assert!(
            err.contains("not fully consumed"),
            "unexpected trailing-transcript error: {err}"
        );
    }

    #[test]
    fn test_whir_split_commit_prove_verify_two_points() {
        // Two vectors, TWO evaluation points (simulating r and r_perm)
        let evals_a: Vec<ArkGoldilocks> = (0..16)
            .map(|i| ArkGoldilocks::from((i + 1) as u64))
            .collect();
        let evals_b: Vec<ArkGoldilocks> = (0..16)
            .map(|i| ArkGoldilocks::from((i * 3 + 7) as u64))
            .collect();

        let pcs = WhirPCS::new(32, 0, 1, 2);
        let commit_data = pcs.commit_split(&[&evals_a, &evals_b], WHIR_SESSION_SPLIT);
        let num_vars = commit_data.num_vars;

        // Two distinct evaluation points (constraint r and permutation r_perm)
        let r: Vec<GoldilocksField> = (0..num_vars)
            .map(|i| GoldilocksField::from_canonical_u64((i as u64) * 3 + 7))
            .collect();
        let r_perm: Vec<GoldilocksField> = (0..num_vars)
            .map(|i| GoldilocksField::from_canonical_u64((i as u64) * 11 + 2))
            .collect();

        // Prove at both points
        let (eval_proof, per_point_evals) = pcs.prove_split_with_eval(commit_data, &[&r, &r_perm]);
        assert_eq!(per_point_evals.len(), 2); // 2 points
        assert_eq!(per_point_evals[0].len(), 2); // 2 vectors each

        // Evaluations at different points should differ
        assert_ne!(per_point_evals[0], per_point_evals[1]);

        // Flatten: [P_a(r), P_b(r), P_a(r_perm), P_b(r_perm)]
        let flat_evals: Vec<Field64_3> = per_point_evals.into_iter().flatten().collect();
        assert_eq!(flat_evals.len(), 4);

        // Verify
        let result = pcs.verify_split(
            num_vars,
            &eval_proof,
            &flat_evals,
            WHIR_SESSION_SPLIT,
            &[&r, &r_perm],
            2, // num_vectors
        );
        assert!(
            result.is_ok(),
            "Two-point split verify failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_split_commit_root_matches_standalone() {
        // The root from commit_root() must match the root from commit_split()
        // for the same polynomial (both use WHIR_SESSION_SPLIT).
        let gl_evals: Vec<GoldilocksField> = (0..16)
            .map(|i| GoldilocksField::from_canonical_u64(i + 1))
            .collect();
        let poly = DenseMultilinearExtension::new(gl_evals.clone());

        let pcs = WhirPCS::new(32, 0, 1, 2);

        // Standalone root
        let standalone_root = pcs.commit_root(&poly);

        // Split commit root (first vector)
        let ark_evals = plonky2_vec_to_ark(&poly.evaluations);
        let dummy_evals: Vec<ArkGoldilocks> = (0..16)
            .map(|i| ArkGoldilocks::from((i * 5 + 3) as u64))
            .collect();
        let commit_data = pcs.commit_split(&[&ark_evals, &dummy_evals], WHIR_SESSION_SPLIT);

        assert_eq!(
            standalone_root, commit_data.roots[0],
            "commit_root() must produce the same root as commit_split()[0]"
        );
    }

    #[test]
    fn test_grouped_statement_binds_every_root_point_and_ext3_limb() {
        let num_vars = 4;
        let size = 1usize << num_vars;
        let width = 2;
        let pcs = WhirPCS::for_constituents(num_vars, width);
        let groups: Vec<Vec<Vec<ArkGoldilocks>>> = (0..4)
            .map(|group| {
                (0..width)
                    .map(|vector| {
                        (0..size)
                            .map(|row| {
                                ArkGoldilocks::from((1 + row + 17 * vector + 101 * group) as u64)
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let commit_data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
        let roots = commit_data.roots.clone();
        let points: Vec<Vec<Field64_3>> = (0..4)
            .map(|point| {
                (0..num_vars)
                    .map(|coordinate| Field64_3::from((2 + point * 11 + coordinate * 3) as u64))
                    .collect()
            })
            .collect();
        let point_refs: Vec<&[Field64_3]> = points.iter().map(Vec::as_slice).collect();
        let (proof, per_point) = pcs.prove_grouped_with_eval(commit_data, &point_refs);
        let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
        let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

        pcs.verify_grouped(
            num_vars,
            &proof,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            4,
            &root_refs,
        )
        .expect("honest grouped statement");

        let mut swapped_roots = roots.clone();
        swapped_roots.swap(0, 1);
        let swapped_root_refs: Vec<&[u8]> = swapped_roots.iter().map(Vec::as_slice).collect();
        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                4,
                &swapped_root_refs,
            )
            .is_err(),
            "cross-group root reorder was accepted"
        );

        let mut duplicate_roots = roots.clone();
        duplicate_roots[1] = duplicate_roots[0].clone();
        let duplicate_root_refs: Vec<&[u8]> = duplicate_roots.iter().map(Vec::as_slice).collect();
        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                4,
                &duplicate_root_refs,
            )
            .is_err(),
            "cross-group root reuse was accepted"
        );

        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                4,
                &root_refs[..3],
            )
            .is_err(),
            "omitted root was accepted"
        );
        let mut extended_root_refs = root_refs.clone();
        extended_root_refs.push(root_refs[0]);
        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                4,
                &extended_root_refs,
            )
            .is_err(),
            "extended root vector was accepted"
        );

        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected[..expected.len() - 1],
                WHIR_SESSION_SPLIT,
                &point_refs,
                4,
                &root_refs,
            )
            .is_err(),
            "truncated claim vector was accepted"
        );
        let mut extended_expected = expected.clone();
        extended_expected.push(expected[0]);
        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &extended_expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                4,
                &root_refs,
            )
            .is_err(),
            "extended claim vector was accepted"
        );

        let mut truncated_points = points.clone();
        truncated_points[0].pop();
        let truncated_point_refs: Vec<&[Field64_3]> =
            truncated_points.iter().map(Vec::as_slice).collect();
        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &truncated_point_refs,
                4,
                &root_refs,
            )
            .is_err(),
            "truncated query-point coordinates were accepted"
        );

        let mut extended_points = points.clone();
        extended_points[0].push(Field64_3::from(99_u64));
        let extended_point_refs: Vec<&[Field64_3]> =
            extended_points.iter().map(Vec::as_slice).collect();
        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &extended_point_refs,
                4,
                &root_refs,
            )
            .is_err(),
            "extended query-point coordinates were accepted"
        );

        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                "plonky2-mle-whir-split-v0",
                &point_refs,
                4,
                &root_refs,
            )
            .is_err(),
            "old/new WHIR session mixing was accepted"
        );

        for root_index in 0..4 {
            let mut changed_roots = roots.clone();
            changed_roots[root_index][0] ^= 1;
            let changed_refs: Vec<&[u8]> = changed_roots.iter().map(Vec::as_slice).collect();
            assert!(
                pcs.verify_grouped(
                    num_vars,
                    &proof,
                    &expected,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    4,
                    &changed_refs,
                )
                .is_err(),
                "root {root_index} was not bound"
            );
        }

        // One representative coordinate for every (point, group), with c0,
        // c1 and c2 mutations. This is the full direct-opening boundary used
        // by the outer terminal checks.
        for point in 0..4 {
            for group in 0..4 {
                let index = point * 4 * width + group * width;
                for limb in 0..3 {
                    let mut changed = expected.clone();
                    let mut value = changed[index].expect("bound coordinate");
                    let mut coeffs: Vec<ArkGoldilocks> =
                        ark_ff::Field::to_base_prime_field_elements(&value).collect();
                    coeffs[limb] += ArkGoldilocks::ONE;
                    value = Field64_3::from_base_prime_field_elems(coeffs).unwrap();
                    changed[index] = Some(value);
                    assert!(
                        pcs.verify_grouped(
                            num_vars,
                            &proof,
                            &changed,
                            WHIR_SESSION_SPLIT,
                            &point_refs,
                            4,
                            &root_refs,
                        )
                        .is_err(),
                        "point {point}, group {group}, Ext3 limb {limb} was not bound"
                    );
                }
            }
        }

        let mut permuted_points = points.clone();
        permuted_points.swap(0, 1);
        let permuted_refs: Vec<&[Field64_3]> = permuted_points.iter().map(Vec::as_slice).collect();
        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &permuted_refs,
                4,
                &root_refs,
            )
            .is_err(),
            "query-point permutation was accepted"
        );
    }

    #[test]
    fn test_packed_grouped_statement_binds_both_root_slots() {
        const CONSTITUENT_WIDTH: usize = 160;
        const DEGREE_BITS: usize = 2;

        let index_bits = constituent_index_bits(CONSTITUENT_WIDTH);
        assert_eq!(index_bits, 8);
        let num_vars = packed_group_num_vars(DEGREE_BITS, CONSTITUENT_WIDTH);
        assert_eq!(num_vars, DEGREE_BITS + index_bits);
        let size = 1usize << num_vars;
        let pcs = WhirPCS::for_constituents(num_vars, NUM_PACKED_VECTORS_PER_GROUP);
        assert_eq!(pcs.params.batch_size, 1);

        let groups: Vec<Vec<Vec<ArkGoldilocks>>> = (0..NUM_SPLIT_COMMITMENTS)
            .map(|group| {
                vec![(0..size)
                    .map(|row| ArkGoldilocks::from((1 + row + 101 * group) as u64))
                    .collect()]
            })
            .collect();
        let commit_data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
        let roots = commit_data.roots.clone();
        let point: Vec<Field64_3> = (0..num_vars)
            .map(|coordinate| Field64_3::from((2 + coordinate * 3) as u64))
            .collect();
        let point_refs = [point.as_slice()];
        let (proof, per_point) = pcs.prove_grouped_with_eval(commit_data, &point_refs);
        let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
        let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

        pcs.verify_grouped(
            num_vars,
            &proof,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            NUM_SPLIT_COMMITMENTS,
            &root_refs,
        )
        .expect("honest packed grouped statement");

        let mut trailing_narg = proof.clone();
        trailing_narg.narg_string.push(0);
        let narg_error = pcs
            .verify_grouped(
                num_vars,
                &trailing_narg,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                NUM_SPLIT_COMMITMENTS,
                &root_refs,
            )
            .expect_err("packed grouped verifier accepted a trailing transcript byte");
        assert!(
            narg_error.contains("not fully consumed"),
            "unexpected trailing-transcript error: {narg_error}"
        );

        let mut trailing_hint = proof.clone();
        trailing_hint.hints.push(0);
        let hint_error = pcs
            .verify_grouped(
                num_vars,
                &trailing_hint,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                NUM_SPLIT_COMMITMENTS,
                &root_refs,
            )
            .expect_err("packed grouped verifier accepted a trailing hint byte");
        assert!(
            hint_error.contains("not fully consumed"),
            "unexpected trailing-hint error: {hint_error}"
        );

        let config = pcs.constituent_config(size);
        let ood_bytes =
            config.initial_committer.out_domain_samples * NUM_PACKED_VECTORS_PER_GROUP * 24;
        let commitment_stride = 32 + ood_bytes + 32;
        for (group, root) in roots.iter().enumerate() {
            let actual_root_offset = group * commitment_stride;
            let bound_root_offset = actual_root_offset + 32 + ood_bytes;
            assert_eq!(
                &proof.narg_string[actual_root_offset..actual_root_offset + 32],
                root.as_slice(),
                "unexpected actual-root slot for group {group}"
            );
            assert_eq!(
                &proof.narg_string[bound_root_offset..bound_root_offset + 32],
                root.as_slice(),
                "unexpected bound-root slot for group {group}"
            );

            let mut changed_actual = proof.clone();
            changed_actual.narg_string[actual_root_offset] ^= 1;
            let actual_error = pcs
                .verify_grouped(
                    num_vars,
                    &changed_actual,
                    &expected,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_SPLIT_COMMITMENTS,
                    &root_refs,
                )
                .expect_err("mutated actual WHIR root was accepted");
            assert_eq!(
                actual_error,
                "WHIR actual commitment root does not match outer transcript"
            );

            let mut changed_bound = proof.clone();
            changed_bound.narg_string[bound_root_offset] ^= 1;
            let bound_error = pcs
                .verify_grouped(
                    num_vars,
                    &changed_bound,
                    &expected,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_SPLIT_COMMITMENTS,
                    &root_refs,
                )
                .expect_err("mutated transcript-bound root was accepted");
            assert_eq!(
                bound_error,
                "WHIR commitment root does not match outer transcript"
            );
        }
    }

    /// Commit the two audit-recorded `BEFORE` triples in an honest packed-v1
    /// statement, then replace exactly those three public constituent claims
    /// by the recorded `AFTER` values while keeping the roots and complete
    /// WHIR proof byte-for-byte fixed. This is deliberately a PCS-layer
    /// regression: the historical v0 Fiat-Shamir challenges cannot be made
    /// equal to a fresh v1 transcript without a 64-bit preimage search, but
    /// the production grouped PCS can still prove directly that the exact
    /// values are not openings of the commitments that contain their matching
    /// historical baselines.
    #[test]
    #[cfg(feature = "legacy-conformance")]
    fn test_historical_frozen_triples_reach_packed_v1_pcs_rejection() {
        use ark_ff::AdditiveGroup;

        use crate::proof::{GROUP_INVERSE_HELPERS, GROUP_WITNESS};
        use crate::protocol_schema::POINT_INVERSE;

        const DEGREE_BITS: usize = 2;
        const NUM_ROWS: usize = 1 << DEGREE_BITS;
        const CONSTITUENT_WIDTH: usize = 160;
        const INDEX_BITS: usize = 8;

        #[derive(Clone, Copy)]
        struct FrozenTriple {
            name: &'static str,
            w0_before: u64,
            w0_after: u64,
            w1: u64,
            w80_before: u64,
            w80_after: u64,
            a0: u64,
            a1_before: u64,
            a1_after: u64,
            b0: u64,
            rho: u64,
            beta: u64,
            gamma: u64,
            lambda_inv: u64,
            mu_inv: u64,
            k1: u64,
            g_sub: u64,
        }

        const CASES: [FrozenTriple; 2] = [
            FrozenTriple {
                name: "small_mul",
                w0_before: 3_051_498_664_030_569_048,
                w0_after: 3_051_498_664_030_569_049,
                w1: 78_509_372_807_566_819,
                w80_before: 6_063_719_204_085_150_528,
                w80_after: 2_587_698_932_769_584_699,
                a0: 16_828_114_539_042_804_903,
                a1_before: 7_495_656_216_612_080_666,
                a1_after: 14_584_819_668_673_277_578,
                b0: 13_178_207_313_111_168_954,
                rho: 4_731_229_214_337_826_042,
                beta: 17_800_375_341_204_939_063,
                gamma: 9_041_901_820_383_133_626,
                lambda_inv: 16_769_653_635_246_974_393,
                mu_inv: 11_315_289_580_255_226_170,
                k1: 14_293_326_489_335_486_720,
                g_sub: 11_042_185_228_133_710_199,
            },
            FrozenTriple {
                name: "parent validity",
                w0_before: 8_093_513_556_413_711_660,
                w0_after: 8_093_513_556_413_711_661,
                w1: 12_819_036_921_327_938_012,
                w80_before: 2_800_508_231_593_448_274,
                w80_after: 15_862_999_140_234_155_880,
                a0: 9_601_097_877_492_032_537,
                a1_before: 17_516_173_920_822_186_472,
                a1_after: 6_112_368_312_529_039_975,
                b0: 8_488_046_535_134_267_022,
                rho: 6_145_656_649_326_269_386,
                beta: 18_087_660_371_601_274_625,
                gamma: 10_481_604_735_508_439_039,
                lambda_inv: 1_097_435_823_362_543_930,
                mu_inv: 171_987_289_746_320_364,
                k1: 14_293_326_489_335_486_720,
                g_sub: 13_562_199_838_588_320_182,
            },
        ];

        fn packed_constant_group(
            claims: &[ArkGoldilocks],
            constituent_width: usize,
            num_rows: usize,
        ) -> Vec<Vec<ArkGoldilocks>> {
            assert_eq!(claims.len(), constituent_width);
            let mut packed =
                vec![ArkGoldilocks::ZERO; num_rows * constituent_width.next_power_of_two()];
            for (constituent, &claim) in claims.iter().enumerate() {
                let start = constituent * num_rows;
                packed[start..start + num_rows].fill(claim);
            }
            vec![packed]
        }

        fn fold_claim(claims: &[ArkGoldilocks], index_point: &[Field64_3]) -> Field64_3 {
            let mut layer = vec![Field64_3::default(); claims.len().next_power_of_two()];
            for (slot, &claim) in claims.iter().enumerate() {
                layer[slot] = Field64_3::new(claim, ArkGoldilocks::ZERO, ArkGoldilocks::ZERO);
            }
            for &challenge in index_point {
                for slot in 0..layer.len() / 2 {
                    let even = layer[2 * slot];
                    let odd = layer[2 * slot + 1];
                    layer[slot] = even + challenge * (odd - even);
                }
                layer.truncate(layer.len() / 2);
            }
            assert_eq!(layer.len(), 1);
            layer[0]
        }

        fn fixture_hex(bytes: &[u8]) -> String {
            const HEX: &[u8; 16] = b"0123456789abcdef";
            let mut encoded = String::with_capacity(2 + bytes.len() * 2);
            encoded.push_str("0x");
            for &byte in bytes {
                encoded.push(HEX[(byte >> 4) as usize] as char);
                encoded.push(HEX[(byte & 0x0f) as usize] as char);
            }
            encoded
        }

        fn fixture_field(value: ArkGoldilocks) -> serde_json::Value {
            serde_json::Value::String(value.into_bigint().0[0].to_string())
        }

        fn fixture_ext3(value: Field64_3) -> serde_json::Value {
            serde_json::json!({
                "c0": fixture_field(value.c0),
                "c1": fixture_field(value.c1),
                "c2": fixture_field(value.c2),
            })
        }

        fn fixture_fields(values: &[ArkGoldilocks]) -> serde_json::Value {
            serde_json::Value::Array(values.iter().copied().map(fixture_field).collect())
        }

        fn fixture_ext3s(values: &[Field64_3]) -> serde_json::Value {
            serde_json::Value::Array(values.iter().copied().map(fixture_ext3).collect())
        }

        fn fixture_protocol_id(config: &WhirConfig<Basefield<Field64_3>>) -> Vec<u8> {
            let mut config_bytes = Vec::new();
            ciborium::into_writer(config, &mut config_bytes)
                .expect("historical fixture config encoding");
            let tagged_hash = |tag: u8| -> [u8; 32] {
                let mut hasher = Keccak256::new();
                hasher.update([tag]);
                hasher.update(&config_bytes);
                hasher.finalize().into()
            };
            [tagged_hash(0), tagged_hash(1)].concat()
        }

        fn fixture_session_id(session: &str) -> Vec<u8> {
            let mut session_bytes = Vec::new();
            ciborium::into_writer(&session.to_string(), &mut session_bytes)
                .expect("historical fixture session encoding");
            Keccak256::digest(&session_bytes).to_vec()
        }

        assert_eq!(constituent_index_bits(CONSTITUENT_WIDTH), INDEX_BITS);
        let packed_num_vars = packed_group_num_vars(DEGREE_BITS, CONSTITUENT_WIDTH);
        let pcs = WhirPCS::for_constituents_v1(packed_num_vars, NUM_PACKED_VECTORS_PER_GROUP);
        let config = pcs.constituent_config(1 << packed_num_vars);
        let protocol_id = fixture_protocol_id(&config);
        let session_id = fixture_session_id(WHIR_SESSION_SPLIT);
        let mut fixture_cases = Vec::with_capacity(CASES.len());

        for case in CASES {
            let field = ArkGoldilocks::from;

            // First pin that these exact constants are the two historical
            // scalar-RLC/Phi_inv kernels rather than merely similarly shaped
            // mutations.
            let witness_delta = field(case.w0_after) - field(case.w0_before)
                + field(case.rho).pow([80]) * (field(case.w80_after) - field(case.w80_before));
            assert_eq!(
                witness_delta,
                ArkGoldilocks::ZERO,
                "{} witness kernel",
                case.name
            );
            let denom_id_1 = field(case.beta)
                + field(case.w1)
                + field(case.gamma) * field(case.k1) * field(case.g_sub);
            let terminal_delta = field(case.a0)
                + field(case.mu_inv) * field(case.b0)
                + field(case.lambda_inv)
                    * denom_id_1
                    * (field(case.a1_after) - field(case.a1_before));
            assert_eq!(
                terminal_delta,
                ArkGoldilocks::ZERO,
                "{} terminal kernel",
                case.name
            );

            let mut witness_before = vec![ArkGoldilocks::ZERO; CONSTITUENT_WIDTH];
            witness_before[0] = field(case.w0_before);
            witness_before[1] = field(case.w1);
            witness_before[80] = field(case.w80_before);
            let mut inverse_before = vec![ArkGoldilocks::ZERO; CONSTITUENT_WIDTH];
            inverse_before[0] = field(case.a0);
            inverse_before[1] = field(case.a1_before);
            inverse_before[80] = field(case.b0);
            let zero_claims = vec![ArkGoldilocks::ZERO; CONSTITUENT_WIDTH];

            let groups = vec![
                packed_constant_group(&zero_claims, CONSTITUENT_WIDTH, NUM_ROWS),
                packed_constant_group(&witness_before, CONSTITUENT_WIDTH, NUM_ROWS),
                packed_constant_group(&inverse_before, CONSTITUENT_WIDTH, NUM_ROWS),
                packed_constant_group(&zero_claims, CONSTITUENT_WIDTH, NUM_ROWS),
            ];
            let commit_data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
            let roots = commit_data.roots.clone();
            let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

            // Use the production four-linear-form shape. Row coordinates are
            // base-field embedded; index coordinates exercise all Ext3 limbs.
            let points: Vec<Vec<Field64_3>> = (0..4)
                .map(|point| {
                    (0..DEGREE_BITS)
                        .map(|coordinate| Field64_3::from((2 + 7 * point + coordinate) as u64))
                        .chain((0..INDEX_BITS).map(|coordinate| {
                            let seed = (3 + 19 * point + 5 * coordinate) as u64;
                            Field64_3::new(
                                ArkGoldilocks::from(seed),
                                ArkGoldilocks::from(seed + 1),
                                ArkGoldilocks::from(seed + 2),
                            )
                        }))
                        .collect()
                })
                .collect();
            let point_refs: Vec<&[Field64_3]> = points.iter().map(Vec::as_slice).collect();
            let (proof, per_point) = pcs.prove_grouped_with_eval(commit_data, &point_refs);
            let honest_expected: Vec<Option<Field64_3>> =
                per_point.into_iter().flatten().map(Some).collect();
            pcs.verify_grouped(
                packed_num_vars,
                &proof,
                &honest_expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                NUM_SPLIT_COMMITMENTS,
                &root_refs,
            )
            .unwrap_or_else(|error| {
                panic!("{} honest packed-v1 baseline failed: {error}", case.name)
            });

            let mut witness_after = witness_before.clone();
            witness_after[0] = field(case.w0_after);
            witness_after[80] = field(case.w80_after);
            let mut inverse_after = inverse_before.clone();
            inverse_after[1] = field(case.a1_after);
            assert_eq!(
                witness_before
                    .iter()
                    .zip(&witness_after)
                    .filter(|(before, after)| before != after)
                    .count(),
                2,
                "{} changed a non-historical witness claim",
                case.name
            );
            assert_eq!(
                inverse_before
                    .iter()
                    .zip(&inverse_after)
                    .filter(|(before, after)| before != after)
                    .count(),
                1,
                "{} changed a non-historical inverse claim",
                case.name
            );

            let index_point = &points[POINT_INVERSE][DEGREE_BITS..];
            let honest_witness_fold = fold_claim(&witness_before, index_point);
            let forged_witness_fold = fold_claim(&witness_after, index_point);
            let honest_inverse_fold = fold_claim(&inverse_before, index_point);
            let forged_inverse_fold = fold_claim(&inverse_after, index_point);
            let witness_slot = POINT_INVERSE * NUM_SPLIT_COMMITMENTS + GROUP_WITNESS;
            let inverse_slot = POINT_INVERSE * NUM_SPLIT_COMMITMENTS + GROUP_INVERSE_HELPERS;
            assert_eq!(honest_expected[witness_slot], Some(honest_witness_fold));
            assert_eq!(honest_expected[inverse_slot], Some(honest_inverse_fold));
            assert_ne!(
                forged_witness_fold, honest_witness_fold,
                "{} witness projection",
                case.name
            );
            assert_ne!(
                forged_inverse_fold, honest_inverse_fold,
                "{} inverse projection",
                case.name
            );

            // The immutable roots, transcript, hints, and four query points
            // remain those of the honest BEFORE proof. Only the three
            // constituent claims used to calculate these two public packed
            // evaluations have changed.
            let mut forged_expected = honest_expected.clone();
            forged_expected[witness_slot] = Some(forged_witness_fold);
            forged_expected[inverse_slot] = Some(forged_inverse_fold);
            let error = pcs
                .verify_grouped(
                    packed_num_vars,
                    &proof,
                    &forged_expected,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_SPLIT_COMMITMENTS,
                    &root_refs,
                )
                .expect_err("historical AFTER triple opened the BEFORE commitments");
            assert!(
                error.contains(&format!("WHIR bound evaluation mismatch at {witness_slot}")),
                "{} was rejected outside the packed PCS claim boundary: {error}",
                case.name
            );

            // Export the exact production proof consumed by the Solidity
            // regression. Points are stored in WHIR/MSB order, while the
            // constituent index point is additionally stored in dense-LSB
            // order for PackedClaimLib.fold.
            let whir_points = points
                .iter()
                .map(|point| {
                    let reversed: Vec<Field64_3> = point.iter().rev().copied().collect();
                    fixture_ext3s(&reversed)
                })
                .collect::<Vec<_>>();
            let honest_evaluations = honest_expected
                .iter()
                .map(|value| fixture_ext3(value.expect("complete grouped evaluation matrix")))
                .collect::<Vec<_>>();
            fixture_cases.push(serde_json::json!({
                "name": case.name,
                "roots": roots.iter().map(|root| fixture_hex(root)).collect::<Vec<_>>(),
                "whirTranscript": fixture_hex(&proof.narg_string),
                "whirHints": fixture_hex(&proof.hints),
                "whirPoints": whir_points,
                "indexPointAtInverse": fixture_ext3s(index_point),
                "honestEvaluations": honest_evaluations,
                "witnessBefore": fixture_fields(&witness_before),
                "witnessAfter": fixture_fields(&witness_after),
                "inverseBefore": fixture_fields(&inverse_before),
                "inverseAfter": fixture_fields(&inverse_after),
            }));
        }

        let fixture = serde_json::json!({
            "schemaVersion": 1,
            "description": "Exact audit-recorded triples committed in honest packed-v1 WHIR proofs; only AFTER constituent folds must be rejected.",
            "paramsFixture": "small_mul.json",
            "degreeBits": DEGREE_BITS,
            "constituentWidth": CONSTITUENT_WIDTH,
            "numCommitments": NUM_SPLIT_COMMITMENTS,
            "numLinearForms": 4,
            "whirProtocolId": fixture_hex(&protocol_id),
            "whirSplitSessionId": fixture_hex(&session_id),
            "cases": fixture_cases,
        });
        let mut encoded = serde_json::to_string_pretty(&fixture)
            .expect("serialize historical packed PCS fixture");
        encoded.push('\n');
        let fixture_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("contracts/test/fixtures/historical_pcs_triples.json");
        if std::env::var_os("MLE_WRITE_HISTORICAL_PCS_FIXTURE").as_deref()
            == Some(std::ffi::OsStr::new("1"))
        {
            std::fs::write(&fixture_path, &encoded).expect("write historical packed PCS fixture");
        } else {
            let checked = std::fs::read_to_string(&fixture_path)
                .expect("historical packed PCS fixture is missing; regenerate with MLE_WRITE_HISTORICAL_PCS_FIXTURE=1");
            assert_eq!(
                checked, encoded,
                "historical packed PCS fixture drift; regenerate with MLE_WRITE_HISTORICAL_PCS_FIXTURE=1"
            );
        }
    }

    #[test]
    fn test_canonical_goldilocks_narg_limb_validation() {
        let canonical_base = 0u64.to_le_bytes();
        validate_canonical_goldilocks_limbs(&canonical_base, 1, "base field", "NARG", 17)
            .expect("zero must have a canonical base-field encoding");

        let modulus_alias = GOLDILOCKS_MODULUS.to_le_bytes();
        let mut upstream_base_cursor = modulus_alias.as_slice();
        assert_eq!(
            ArkGoldilocks::deserialize_from_narg(&mut upstream_base_cursor)
                .expect("pinned NARG decoder accepts P modulo the field"),
            ArkGoldilocks::default(),
            "test no longer models the pinned NARG alias"
        );
        assert!(upstream_base_cursor.is_empty());
        let base_error =
            validate_canonical_goldilocks_limbs(&modulus_alias, 1, "base field", "NARG", 17)
                .expect_err("P aliases zero and must not be accepted as a base-field encoding");
        assert!(base_error.contains("limb 0 at NARG byte 17"));

        for limb in 0..3 {
            let mut encoded_ext3 = [0u8; FIELD64_3_NARG_BYTES];
            let start = limb * GOLDILOCKS_LIMB_BYTES;
            encoded_ext3[start..start + GOLDILOCKS_LIMB_BYTES].copy_from_slice(&modulus_alias);
            let mut upstream_ext3_cursor = encoded_ext3.as_slice();
            assert_eq!(
                Field64_3::deserialize_from_narg(&mut upstream_ext3_cursor)
                    .expect("pinned NARG decoder accepts P modulo each Ext3 limb"),
                Field64_3::default(),
                "test no longer models the pinned NARG alias in limb {limb}"
            );
            assert!(upstream_ext3_cursor.is_empty());
            let error =
                validate_canonical_goldilocks_limbs(&encoded_ext3, 3, "Ext3 field", "NARG", 29)
                    .expect_err("P aliases zero and must not be accepted in any Ext3 limb");
            assert!(
                error.contains(&format!("limb {limb} at NARG byte {}", 29 + start)),
                "unexpected limb error: {error}"
            );
        }
    }

    #[test]
    fn test_ark_hint_decoder_rejects_noncanonical_base_and_ext3_limbs() {
        let modulus_alias = GOLDILOCKS_MODULUS.to_le_bytes();

        let mut canonical_base_hint = Vec::new();
        vec![ArkGoldilocks::default()]
            .serialize_compressed(&mut canonical_base_hint)
            .expect("serialize base-field hint vector");
        assert_eq!(canonical_base_hint.len(), 8 + GOLDILOCKS_LIMB_BYTES);
        for raw in [GOLDILOCKS_MODULUS, u64::MAX] {
            let mut malformed = canonical_base_hint.clone();
            malformed[8..8 + GOLDILOCKS_LIMB_BYTES].copy_from_slice(&raw.to_le_bytes());
            assert!(
                Vec::<ArkGoldilocks>::deserialize_compressed(malformed.as_slice()).is_err(),
                "Arkworks hint decoder accepted non-canonical base-field value {raw:#x}"
            );
        }

        let mut canonical_ext3_hint = Vec::new();
        vec![Field64_3::default()]
            .serialize_compressed(&mut canonical_ext3_hint)
            .expect("serialize Ext3 hint vector");
        assert_eq!(canonical_ext3_hint.len(), 8 + FIELD64_3_NARG_BYTES);
        for limb in 0..3 {
            let mut malformed = canonical_ext3_hint.clone();
            let offset = 8 + limb * GOLDILOCKS_LIMB_BYTES;
            malformed[offset..offset + GOLDILOCKS_LIMB_BYTES].copy_from_slice(&modulus_alias);
            assert!(
                Vec::<Field64_3>::deserialize_compressed(malformed.as_slice()).is_err(),
                "Arkworks hint decoder accepted P as zero in Ext3 limb {limb}"
            );
        }
    }

    #[test]
    fn test_grouped_verifier_rejects_noncanonical_base_hint_without_unwind() {
        let num_vars = 4;
        let size = 1usize << num_vars;
        let pcs = WhirPCS::for_constituents(num_vars, NUM_PACKED_VECTORS_PER_GROUP);
        let groups: Vec<Vec<Vec<ArkGoldilocks>>> = (0..NUM_SPLIT_COMMITMENTS)
            .map(|group| {
                vec![(0..size)
                    .map(|row| ArkGoldilocks::from((1 + row + 101 * group) as u64))
                    .collect()]
            })
            .collect();
        let data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
        let roots = data.roots.clone();
        let point: Vec<Field64_3> = (0..num_vars)
            .map(|coordinate| Field64_3::from((2 + coordinate * 3) as u64))
            .collect();
        let point_refs = [point.as_slice()];
        let (mut proof, per_point) = pcs.prove_grouped_with_eval(data, &point_refs);
        let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
        let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

        let first_hint_len = proof
            .hints
            .get(..8)
            .and_then(|bytes| <[u8; 8]>::try_from(bytes).ok())
            .map(u64::from_le_bytes)
            .expect("initial Arkworks Vec length prefix");
        assert!(first_hint_len > 0, "initial hint row vector is empty");
        let first_field = proof
            .hints
            .get(8..8 + GOLDILOCKS_LIMB_BYTES)
            .and_then(|bytes| <[u8; 8]>::try_from(bytes).ok())
            .map(u64::from_le_bytes)
            .expect("first base-field hint element");
        assert!(first_field < GOLDILOCKS_MODULUS);
        proof.hints[8..8 + GOLDILOCKS_LIMB_BYTES]
            .copy_from_slice(&GOLDILOCKS_MODULUS.to_le_bytes());

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                NUM_SPLIT_COMMITMENTS,
                &root_refs,
            )
        }));
        assert!(
            result
                .expect("non-canonical base-field hint unwound the caller")
                .is_err(),
            "grouped verifier accepted a non-canonical base-field hint"
        );
    }

    #[test]
    fn test_grouped_hint_preflight_rejects_lengths_tails_and_every_field_limb_without_unwind() {
        let num_vars = 2;
        let size = 1usize << num_vars;
        let group_width = 2;
        let pcs = WhirPCS::for_constituents(num_vars, group_width);
        let groups: Vec<Vec<Vec<ArkGoldilocks>>> = (0..NUM_SPLIT_COMMITMENTS)
            .map(|group| {
                (0..group_width)
                    .map(|vector| {
                        (0..size)
                            .map(|row| {
                                ArkGoldilocks::from((1 + row + 17 * vector + 101 * group) as u64)
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
        let roots = data.roots.clone();
        let point: Vec<Field64_3> = (0..num_vars)
            .map(|coordinate| Field64_3::from((2 + coordinate * 3) as u64))
            .collect();
        let point_refs = [point.as_slice()];
        let (proof, per_point) = pcs.prove_grouped_with_eval(data, &point_refs);
        let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
        let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();
        let config = pcs.constituent_config(size);
        assert!(
            !config.round_configs.is_empty(),
            "test config must exercise both base and Ext3 hint rows"
        );

        let proof_data = WhirProofData {
            narg_string: proof.narg_string.clone(),
            hints: proof.hints.clone(),
            #[cfg(debug_assertions)]
            pattern: proof.pattern.clone(),
        };
        let replay = preflight_grouped_final_fold(
            &config,
            &proof_data,
            WHIR_SESSION_SPLIT,
            NUM_SPLIT_COMMITMENTS,
            expected.len(),
        )
        .expect("honest hint preflight replay");
        let base_fields = replay
            .hint_field_offsets
            .iter()
            .filter(|(_, limbs)| *limbs == 1)
            .count();
        let ext3_fields = replay
            .hint_field_offsets
            .iter()
            .filter(|(_, limbs)| *limbs == 3)
            .count();
        assert!(base_fields > 0, "no base-field hint rows were traced");
        assert!(ext3_fields > 0, "no Ext3 hint rows were traced");
        assert!(
            replay
                .hint_field_offsets
                .windows(2)
                .all(|fields| { fields[0].0 + fields[0].1 * GOLDILOCKS_LIMB_BYTES <= fields[1].0 }),
            "typed hint fields overlap or are out of order"
        );

        let assert_rejected = |malformed: &WhirEvalProof, expected_fragment: &str, case: &str| {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                pcs.verify_grouped(
                    num_vars,
                    malformed,
                    &expected,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_SPLIT_COMMITMENTS,
                    &root_refs,
                )
            }));
            let verification =
                result.unwrap_or_else(|_| panic!("{case} unwound the grouped verifier"));
            let error = verification.expect_err(&format!("{case} was accepted"));
            assert!(
                error.contains(expected_fragment),
                "unexpected {case} rejection: {error}"
            );
        };

        for (prefix_index, &prefix_offset) in replay.hint_vector_prefix_offsets.iter().enumerate() {
            let mut malformed = proof.clone();
            malformed.hints[prefix_offset..prefix_offset + 8]
                .copy_from_slice(&u64::MAX.to_le_bytes());
            assert_rejected(
                &malformed,
                "hint vector length mismatch",
                &format!("oversized hint Vec prefix {prefix_index}"),
            );
        }

        let modulus_alias = GOLDILOCKS_MODULUS.to_le_bytes();
        let mut mutation_count = 0usize;
        for (field_index, &(field_offset, limbs)) in replay.hint_field_offsets.iter().enumerate() {
            for limb in 0..limbs {
                let limb_offset = field_offset + limb * GOLDILOCKS_LIMB_BYTES;
                let mut malformed = proof.clone();
                malformed.hints[limb_offset..limb_offset + GOLDILOCKS_LIMB_BYTES]
                    .copy_from_slice(&modulus_alias);
                assert_rejected(
                    &malformed,
                    &format!("non-canonical Goldilocks limb {limb} at hint byte {limb_offset}"),
                    &format!("non-canonical hint field {field_index} limb {limb}"),
                );
                mutation_count += 1;
            }
        }

        let mut short_prefix = proof.clone();
        short_prefix.hints.truncate(7);
        assert_rejected(&short_prefix, "hint is truncated", "truncated hint prefix");

        let mut short_path = proof.clone();
        short_path.hints.pop();
        assert_rejected(
            &short_path,
            "hint is truncated",
            "truncated Merkle authentication path",
        );

        let mut trailing = proof.clone();
        trailing.hints.push(0);
        assert_rejected(&trailing, "trailing hint bytes", "trailing hint byte");

        eprintln!(
            "checked {base_fields} base and {ext3_fields} Ext3 hint fields, {mutation_count} limb mutations, and {} Vec prefixes",
            replay.hint_vector_prefix_offsets.len()
        );
    }

    #[test]
    fn test_grouped_verifier_rejects_every_noncanonical_ext3_narg_limb_without_unwind() {
        let num_vars = 4;
        let size = 1usize << num_vars;
        let pcs = WhirPCS::for_constituents(num_vars, NUM_PACKED_VECTORS_PER_GROUP);
        let groups: Vec<Vec<Vec<ArkGoldilocks>>> = (0..NUM_SPLIT_COMMITMENTS)
            .map(|group| {
                vec![(0..size)
                    .map(|row| ArkGoldilocks::from((1 + row + 101 * group) as u64))
                    .collect()]
            })
            .collect();
        let data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
        let roots = data.roots.clone();
        let point: Vec<Field64_3> = (0..num_vars)
            .map(|coordinate| Field64_3::from((2 + coordinate * 3) as u64))
            .collect();
        let point_refs = [point.as_slice()];
        let (proof, per_point) = pcs.prove_grouped_with_eval(data, &point_refs);
        let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
        let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

        pcs.verify_grouped(
            num_vars,
            &proof,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            NUM_SPLIT_COMMITMENTS,
            &root_refs,
        )
        .expect("honest grouped proof");

        let config = pcs.constituent_config(size);
        let proof_data = WhirProofData {
            narg_string: proof.narg_string.clone(),
            hints: proof.hints.clone(),
            #[cfg(debug_assertions)]
            pattern: proof.pattern.clone(),
        };
        let replay = preflight_grouped_final_fold(
            &config,
            &proof_data,
            WHIR_SESSION_SPLIT,
            NUM_SPLIT_COMMITMENTS,
            expected.len(),
        )
        .expect("honest preflight replay");
        assert!(
            !replay.field64_3_offsets.is_empty(),
            "test proof unexpectedly contains no typed Ext3 NARG fields"
        );
        assert!(
            replay
                .field64_3_offsets
                .windows(2)
                .all(|offsets| offsets[0] < offsets[1]),
            "typed Ext3 NARG offsets must be strictly ordered"
        );
        eprintln!(
            "checking {} typed Ext3 NARG fields ({} individual base limbs)",
            replay.field64_3_offsets.len(),
            replay.field64_3_offsets.len() * 3
        );

        let modulus_alias = GOLDILOCKS_MODULUS.to_le_bytes();
        let mut zero_alias_mutations = 0usize;
        for (field_index, &field_offset) in replay.field64_3_offsets.iter().enumerate() {
            for limb in 0..3 {
                let limb_offset = field_offset + limb * GOLDILOCKS_LIMB_BYTES;
                if proof.narg_string[limb_offset..limb_offset + GOLDILOCKS_LIMB_BYTES]
                    == 0u64.to_le_bytes()
                {
                    zero_alias_mutations += 1;
                }
                let mut malformed = proof.clone();
                malformed.narg_string[limb_offset..limb_offset + GOLDILOCKS_LIMB_BYTES]
                    .copy_from_slice(&modulus_alias);

                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    pcs.verify_grouped(
                        num_vars,
                        &malformed,
                        &expected,
                        WHIR_SESSION_SPLIT,
                        &point_refs,
                        NUM_SPLIT_COMMITMENTS,
                        &root_refs,
                    )
                }));
                let verification = result.unwrap_or_else(|_| {
                    panic!("non-canonical Ext3 field {field_index} limb {limb} unwound the caller")
                });
                let error = verification.expect_err(&format!(
                    "non-canonical Ext3 field {field_index} limb {limb} was accepted"
                ));
                assert!(
                    error.contains(&format!(
                        "non-canonical Goldilocks limb {limb} at NARG byte {limb_offset}"
                    )),
                    "unexpected rejection for Ext3 field {field_index} limb {limb}: {error}"
                );
            }
        }
        assert!(
            zero_alias_mutations > 0,
            "test proof did not exercise the concrete zero-to-P alias"
        );
        eprintln!("{zero_alias_mutations} mutations were exact zero-to-P aliases");
    }

    #[test]
    fn test_constituent_security_budget_exceeds_128_bits() {
        const CONSTITUENT_WIDTH: usize = 160;
        const NUM_POINTS: usize = 4;
        const GOLDILOCKS_MODULUS: u64 = 0xffff_ffff_0000_0001;

        let index_bits = constituent_index_bits(CONSTITUENT_WIDTH);
        assert_eq!(index_bits, 8);

        // Each of the four point-specific index challenges can project every
        // group. A non-zero multilinear difference has total index degree at
        // most `index_bits`, so Schwartz-Zippel plus a union bound gives this
        // conservative failure probability over Field64_3.
        let projection_events = NUM_SPLIT_COMMITMENTS * NUM_POINTS * index_bits;
        assert_eq!(projection_events, 128);
        let projection_bits =
            3.0 * (GOLDILOCKS_MODULUS as f64).log2() - (projection_events as f64).log2();
        assert!(
            projection_bits >= 128.0,
            "Ext3 constituent-projection binding is only {projection_bits:.2} bits"
        );

        for degree_bits in [2usize, 3, 4, 11, 12, 13] {
            let num_vars = packed_group_num_vars(degree_bits, CONSTITUENT_WIDTH);
            assert_eq!(num_vars, degree_bits + 8);
            let pcs = WhirPCS::for_constituents_v1(num_vars, NUM_PACKED_VECTORS_PER_GROUP);
            assert_eq!(pcs.params.batch_size, 1);
            let bits = pcs.constituent_security_level(
                1usize << num_vars,
                NUM_SPLIT_COMMITMENTS,
                NUM_POINTS,
            );
            eprintln!(
                "degree_bits={degree_bits}, packed_num_vars={num_vars}: WHIR={bits:.12} bits, Ext3 projection={projection_bits:.12} bits"
            );
            assert!(
                bits >= 128.0,
                "packed grouped WHIR security is only {bits:.2} bits at degree {degree_bits}"
            );
        }
    }

    #[test]
    fn test_v1_and_v2_constituent_profiles_are_version_isolated() {
        const NUM_VARS: usize = 10;
        const SIZE: usize = 1 << NUM_VARS;

        let v1 = WhirPCS::for_constituents_v1(NUM_VARS, 1);
        let v2 = WhirPCS::for_constituents(NUM_VARS, 1);
        assert_eq!(v1.params.security_level, 130);
        assert_eq!(v1.params.pow_bits, 0);
        assert_eq!(v2.params.security_level, WHIR_SECURITY_LEVEL_V2);
        assert_eq!(v2.params.pow_bits, WHIR_POW_BITS_V2);

        let v1_config = v1.constituent_config(SIZE);
        let v2_config = v2.constituent_config(SIZE);
        assert!(v1_config.initial_committer.deduplicate_in_domain);
        assert_eq!(
            v2_config.initial_committer.deduplicate_in_domain,
            WHIR_DEDUPLICATE_IN_DOMAIN_V2
        );
        assert_eq!(v1_config.round_configs[0].pow.threshold, u64::MAX);
        assert_eq!(v1_config.final_pow.threshold, u64::MAX);
        assert_ne!(v2_config.round_configs[0].pow.threshold, u64::MAX);
        assert_ne!(v2_config.final_pow.threshold, u64::MAX);
        assert_ne!(
            v1.constituent_protocol_id(SIZE),
            v2.constituent_protocol_id(SIZE)
        );
        assert!(v2.constituent_security_level(SIZE, 3, 2) + 1e-9 >= WHIR_SECURITY_LEVEL_V2 as f64);
    }

    #[cfg(debug_assertions)]
    #[test]
    fn test_grouped_verifier_ignores_untrusted_debug_pattern() {
        let num_vars = 4;
        let size = 1usize << num_vars;
        let pcs = WhirPCS::for_constituents(num_vars, 1);
        let groups: Vec<Vec<Vec<ArkGoldilocks>>> = (0..3)
            .map(|group| {
                vec![(0..size)
                    .map(|row| ArkGoldilocks::from((1 + row + 101 * group) as u64))
                    .collect()]
            })
            .collect();
        let data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
        let roots = data.roots.clone();
        let points = [
            vec![Field64_3::from(2_u64); num_vars],
            vec![Field64_3::from(3_u64); num_vars],
        ];
        let point_refs = points.iter().map(Vec::as_slice).collect::<Vec<_>>();
        let (mut proof, per_point) = pcs.prove_grouped_with_eval(data, &point_refs);
        let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
        let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

        // This field is emitted only for upstream debug assertions and never
        // appears in the canonical compact proof. Before canonical
        // reconstruction, this one-element mutation panicked before the first
        // commitment could be decoded; a long string also forced a redundant
        // attacker-sized clone.
        proof.pattern = vec![Interaction::ProverMessage("attacker".repeat(1 << 17))];
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                groups.len(),
                &root_refs,
            )
        }));
        result
            .expect("debug-only proof metadata unwound the grouped verifier")
            .expect("valid proof bytes were rejected because of debug-only metadata");
    }

    #[test]
    fn test_zero_grouped_statement_is_rejected_without_unwinding() {
        let num_vars = 4;
        let size = 1usize << num_vars;
        let pcs = WhirPCS::for_constituents(num_vars, 1);
        let groups = vec![vec![vec![ArkGoldilocks::from(0_u64); size]]; 4];
        let data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
        let roots = data.roots.clone();
        let point = vec![Field64_3::from(2_u64); num_vars];
        let point_refs = [point.as_slice()];
        let (proof, per_point) = pcs.prove_grouped_with_eval(data, &point_refs);
        let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
        let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

        let empty_groups = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            pcs.verify_grouped(
                num_vars,
                &proof,
                &[],
                WHIR_SESSION_SPLIT,
                &point_refs,
                0,
                &[],
            )
        }));
        assert!(
            empty_groups
                .expect("empty grouped statement unwound the caller")
                .is_err(),
            "empty grouped statement was accepted"
        );

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                4,
                &root_refs,
            )
        }));
        let verification = result.expect("malformed grouped proof unwound the caller");
        let error = verification.expect_err("degenerate zero grouped proof was accepted");
        assert!(
            error.contains("final folded polynomial evaluates to zero"),
            "unexpected zero-divisor rejection: {error}"
        );
    }
}
