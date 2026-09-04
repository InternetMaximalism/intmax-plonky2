//! Production export format for the atomic Solidity MLE/WHIR v2 verifier.
//!
//! This module is deliberately separate from the historical [`crate::fixture`]
//! exporter.  The object under [`MleVerifierV2Fixture::proof`] has exactly the
//! sixteen fields of `MleVerifierV2.MleProof`, while the verification key,
//! complete call-time configuration, native WHIR identifiers, Solidity ABI
//! proof bytes, and compact proof bytes are all derived from the same verified
//! Rust objects.  Consumers must not reconstruct or patch any of those fields.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use ark_ff::{FftField, PrimeField as ArkPrimeField};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::circuit_data::{CircuitData, CommonCircuitData};
use plonky2::plonk::config::{GenericConfig, Hasher};
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::Extendable;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field, PrimeField64};
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use crate::commitment::whir_pcs::{whir_session_id, WhirPCS};
use crate::compact_v2::{decode_compact_v2, encode_compact_v2, CompactV2Error, CompactV2Shape};
use crate::fixture::{WhirParamsFixture, WhirRoundParamsFixture};
use crate::proof_v2::{
    constituent_group_width_v2, packed_group_num_vars_v2, GateInfoV2, MleProofV2,
    MleVerificationKeyV2, MLE_PROTOCOL_VERSION_CURRENT, NUM_PACKED_VECTORS_PER_GROUP_V2,
    NUM_PCS_CLAIMS_V2, NUM_PCS_GROUPS_V2, WHIR_SESSION_SPLIT_V2,
};
use crate::protocol_schema_v2::{
    BASE_FIELD_MODULUS_V2, CIRCUIT_DIGEST_LENGTH_V2, COMPACT_LAYOUT_HASH_V2, COMPACT_MAGIC_V2,
    LOG_ROUND_DEGREE_V2, MAX_COMPACT_PROOF_BYTES_V2, MAX_CONSTITUENT_INDEX_BITS_V2,
    MAX_CONSTITUENT_WIDTH_V2, MAX_ROW_VARIABLES_V2, MAX_WHIR_HINT_BYTES_V2, MAX_WHIR_NARG_BYTES_V2,
    MLE_PROOF_ABI_FIELDS_V2, MLE_PROOF_ABI_FIELD_COUNT_V2, MLE_PROOF_ABI_SIGNATURE_V2,
    MLE_PROOF_LAYOUT_HASH_V2, SCHEMA_VERSION_CURRENT, WHIR_DEDUPLICATE_IN_DOMAIN_V2,
    WHIR_FOLDING_FACTOR_V2, WHIR_HASH_ID_V2, WHIR_MAX_STARTING_LOG_INV_RATE_V2, WHIR_POW_BITS_V2,
    WHIR_SECURITY_LEVEL_V2, WHIR_UNIQUE_DECODING_V2,
};
use crate::prover_v2::{mle_prove_v2, mle_setup_v2};
use crate::sumcheck::coefficients::Ext3CoefficientSumcheckProof;
use crate::verifier_v2::mle_verify_v2;

pub const MLE_VERIFIER_FIXTURE_SCHEMA_V2: &str = "plonky2-mle-v3-solidity";
pub const MLE_VERIFIER_CONFIG_FIXTURE_SCHEMA_V2: &str = "plonky2-mle-v3-solidity-config";
pub const SOLIDITY_MLE_PROOF_ENCODING_V2: &str = "abi.encode(MleVerifierV2.MleProof)";
pub const SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2: &str =
    "abi.encode(MleVerifierV2.VerificationConfig)";
/// Historical target admitted only by the explicit target-132 -> target-133
/// proof-free configuration cutover. Normal proving and verification always
/// use [`WHIR_SECURITY_LEVEL_V2`].
pub const RETIRED_WHIR_SECURITY_LEVEL_V2_CONFIG_CUTOVER: usize = 132;
const ROOT_BYTES: usize = 32;
const WHIR_PROTOCOL_ID_BYTES: usize = 64;
const WHIR_SESSION_ID_BYTES: usize = 32;
const ABI_WORD_BYTES: usize = 32;
const EXT3_BYTES: usize = 24;
const WHIR_HINT_LENGTH_PREFIX_BYTES: usize = 8;

/// A canonical cubic-extension limb tuple matching
/// `GoldilocksExt3.Ext3 { c0, c1, c2 }`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Ext3V2Fixture {
    pub c0: String,
    pub c1: String,
    pub c2: String,
}

/// One coefficient-form sumcheck round matching the Solidity ABI.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CoefficientRoundV2Fixture {
    pub non_constant: Vec<Ext3V2Fixture>,
}

/// A coefficient-form sumcheck proof matching the Solidity ABI.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SumcheckProofV2Fixture {
    pub rounds: Vec<CoefficientRoundV2Fixture>,
}

/// Exact JSON view of `MleVerifierV2.MleProof`.
///
/// SECURITY: aliases, optional fields, and flattened compatibility tails are
/// intentionally absent.  `deny_unknown_fields` makes an old or hand-patched
/// proof object fail closed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct MleProofV2Fixture {
    pub protocol_version: u64,
    pub constituent_width: usize,
    pub circuit_digest: Vec<String>,
    pub public_inputs: Vec<String>,
    pub preprocessed_root: String,
    pub witness_root: String,
    pub norm_inverse_root: String,
    pub whir_transcript: String,
    pub whir_hints: String,
    pub log_proof: SumcheckProofV2Fixture,
    pub log_preprocessed: Vec<Ext3V2Fixture>,
    pub log_witness: Vec<Ext3V2Fixture>,
    pub log_norm_inverse: Vec<Ext3V2Fixture>,
    pub gate_proof: SumcheckProofV2Fixture,
    pub gate_preprocessed: Vec<Ext3V2Fixture>,
    pub gate_witness: Vec<Ext3V2Fixture>,
}

impl MleProofV2Fixture {
    /// Convert a native proof to the exact Solidity proof object.
    pub fn encode<F: Field + PrimeField64>(proof: &MleProofV2<F>) -> Self {
        Self {
            protocol_version: proof.protocol_version,
            constituent_width: proof.constituent_width,
            circuit_digest: encode_base_vec(&proof.circuit_digest),
            public_inputs: encode_base_vec(&proof.public_inputs),
            preprocessed_root: encode_hex(&proof.preprocessed_root),
            witness_root: encode_hex(&proof.witness_root),
            norm_inverse_root: encode_hex(&proof.norm_inverse_root),
            whir_transcript: encode_hex(&proof.whir_eval_proof.narg_string),
            whir_hints: encode_hex(&proof.whir_eval_proof.hints),
            log_proof: SumcheckProofV2Fixture::encode(&proof.log_sumcheck_proof),
            log_preprocessed: encode_ext3_vec(&proof.log_preprocessed_evals),
            log_witness: encode_ext3_vec(&proof.log_witness_evals),
            log_norm_inverse: encode_ext3_vec(&proof.log_norm_inverse_evals),
            gate_proof: SumcheckProofV2Fixture::encode(&proof.gate_proof.sumcheck_proof),
            gate_preprocessed: encode_ext3_vec(&proof.gate_proof.preprocessed_evals),
            gate_witness: encode_ext3_vec(&proof.gate_proof.witness_evals),
        }
    }

    /// Enforce the schema-generated exact sixteen-key proof ABI.
    pub fn validate_abi_keys(&self) -> Result<(), FixtureV2Error> {
        let value = serde_json::to_value(self)?;
        let object = value
            .as_object()
            .ok_or(FixtureV2Error::Invalid("v2 proof JSON is not an object"))?;
        let actual = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
        let expected = MLE_PROOF_ABI_FIELDS_V2
            .iter()
            .map(|(_, json_name, _, _)| *json_name)
            .collect::<BTreeSet<_>>();
        if object.len() != MLE_PROOF_ABI_FIELD_COUNT_V2 || actual != expected {
            return Err(FixtureV2Error::Invalid(
                "v2 proof JSON keys drifted from the generated Solidity ABI schema",
            ));
        }
        Ok(())
    }
}

impl SumcheckProofV2Fixture {
    fn encode(proof: &Ext3CoefficientSumcheckProof) -> Self {
        Self {
            rounds: proof
                .rounds
                .iter()
                .map(|round| CoefficientRoundV2Fixture {
                    non_constant: encode_ext3_vec(&round.non_constant),
                })
                .collect(),
        }
    }
}

/// Exact gate-dispatch record used by `Plonky2GateEvaluatorExt3`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct GateInfoV2Fixture {
    pub gate_id: u8,
    pub selector_index: u8,
    pub group_start: u8,
    pub group_end: u8,
    pub gate_row_index: u8,
    pub num_constraints: u16,
    pub num_or_consts: u16,
    pub param2: u16,
    pub param3: u16,
}

impl From<GateInfoV2> for GateInfoV2Fixture {
    fn from(value: GateInfoV2) -> Self {
        Self {
            gate_id: value.gate_id,
            selector_index: value.selector_index,
            group_start: value.group_start,
            group_end: value.group_end,
            gate_row_index: value.gate_row_index,
            num_constraints: value.num_constraints,
            num_or_consts: value.num_or_consts,
            param2: value.param2,
            param3: value.param3,
        }
    }
}

impl From<GateInfoV2Fixture> for GateInfoV2 {
    fn from(value: GateInfoV2Fixture) -> Self {
        Self {
            gate_id: value.gate_id,
            selector_index: value.selector_index,
            group_start: value.group_start,
            group_end: value.group_end,
            gate_row_index: value.gate_row_index,
            num_constraints: value.num_constraints,
            num_or_consts: value.num_or_consts,
            param2: value.param2,
            param3: value.param3,
        }
    }
}

/// Constructor-pinned verification key plus all circuit configuration fields.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct MleVerificationKeyV2Fixture {
    pub protocol_version: u64,
    pub constituent_width: usize,
    pub circuit_digest: Vec<String>,
    pub preprocessed_commitment_root: String,
    pub whir_protocol_id: String,
    pub whir_session_id: String,
    pub circuit_config_digest: String,
    pub num_selectors: usize,
    pub num_gate_constraints: usize,
    pub quotient_degree_factor: usize,
    pub gates: Vec<GateInfoV2Fixture>,
    pub public_input_wire_map: String,
    pub num_constants: usize,
    pub num_routed_wires: usize,
    pub num_wires: usize,
    pub k_is: Vec<String>,
    pub subgroup_gen_powers: Vec<String>,
}

impl MleVerificationKeyV2Fixture {
    pub fn encode<F: Field + PrimeField64>(vk: &MleVerificationKeyV2<F>) -> Self {
        Self {
            protocol_version: vk.protocol_version,
            constituent_width: vk.constituent_width,
            circuit_digest: encode_base_vec(&vk.circuit_digest),
            preprocessed_commitment_root: encode_hex(&vk.preprocessed_commitment_root),
            whir_protocol_id: encode_hex(&vk.whir_protocol_id),
            whir_session_id: encode_hex(&vk.whir_session_id),
            circuit_config_digest: encode_hex(&vk.circuit_config_digest),
            num_selectors: vk.num_selectors,
            num_gate_constraints: vk.num_gate_constraints,
            quotient_degree_factor: vk.quotient_degree_factor,
            gates: vk.gates.iter().copied().map(Into::into).collect(),
            public_input_wire_map: encode_hex(&vk.public_input_wire_map),
            num_constants: vk.num_constants,
            num_routed_wires: vk.num_routed_wires,
            num_wires: vk.num_wires,
            k_is: encode_base_vec(&vk.k_is),
            subgroup_gen_powers: encode_base_vec(&vk.subgroup_gen_powers),
        }
    }

    pub fn try_decode<F: Field + PrimeField64>(
        &self,
    ) -> Result<MleVerificationKeyV2<F>, FixtureV2Error> {
        require_goldilocks::<F>()?;
        Ok(MleVerificationKeyV2 {
            protocol_version: self.protocol_version,
            constituent_width: self.constituent_width,
            circuit_digest: decode_base_vec(&self.circuit_digest, "verificationKey.circuitDigest")?,
            preprocessed_commitment_root: decode_fixed_hex_vec(
                &self.preprocessed_commitment_root,
                ROOT_BYTES,
                "verificationKey.preprocessedCommitmentRoot",
            )?,
            whir_protocol_id: decode_fixed_hex(
                &self.whir_protocol_id,
                "verificationKey.whirProtocolId",
            )?,
            whir_session_id: decode_fixed_hex(
                &self.whir_session_id,
                "verificationKey.whirSessionId",
            )?,
            circuit_config_digest: decode_fixed_hex(
                &self.circuit_config_digest,
                "verificationKey.circuitConfigDigest",
            )?,
            num_selectors: self.num_selectors,
            num_gate_constraints: self.num_gate_constraints,
            quotient_degree_factor: self.quotient_degree_factor,
            gates: self.gates.iter().copied().map(Into::into).collect(),
            public_input_wire_map: decode_hex(
                &self.public_input_wire_map,
                "verificationKey.publicInputWireMap",
            )?,
            num_constants: self.num_constants,
            num_routed_wires: self.num_routed_wires,
            num_wires: self.num_wires,
            k_is: decode_base_vec(&self.k_is, "verificationKey.kIs")?,
            subgroup_gen_powers: decode_base_vec(
                &self.subgroup_gen_powers,
                "verificationKey.subgroupGenPowers",
            )?,
        })
    }

    /// Panicking compatibility helper for deterministic checked-in tests.
    /// Production consumers should use [`Self::try_decode`].
    pub fn decode<F: Field + PrimeField64>(&self) -> MleVerificationKeyV2<F> {
        self.try_decode()
            .expect("canonical MLE/WHIR v2 verification-key fixture")
    }
}

/// Scalar circuit portion of `MleVerifierV2.VerificationConfig`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CircuitParametersV2Fixture {
    pub degree_bits: usize,
    pub num_public_inputs: usize,
    pub num_constants: usize,
    pub num_routed_wires: usize,
    pub num_wires: usize,
    pub num_selectors: usize,
    pub num_gate_constraints: usize,
    pub quotient_degree_factor: usize,
}

/// Exact JSON view of `SpongefishWhirVerify.WhirParams` for a pinned
/// deployment configuration.  The three point arrays must be empty: the
/// atomic verifier derives both terminal points from the outer sumchecks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct WhirParamsV2Fixture {
    pub num_variables: usize,
    pub folding_factor: usize,
    pub num_vectors: usize,
    pub num_commitments: usize,
    pub out_domain_samples: usize,
    pub in_domain_samples: usize,
    pub initial_sumcheck_rounds: usize,
    pub num_rounds: usize,
    pub final_sumcheck_rounds: usize,
    pub final_size: usize,
    pub initial_codeword_length: usize,
    pub initial_merkle_depth: usize,
    pub initial_domain_generator: String,
    pub initial_interleaving_depth: usize,
    pub initial_num_variables: usize,
    pub initial_coset_size: usize,
    pub initial_num_cosets: usize,
    pub initial_sumcheck_pow_threshold: String,
    pub final_pow_threshold: String,
    pub final_sumcheck_pow_threshold: String,
    pub evaluation_point: Vec<Ext3V2Fixture>,
    pub evaluation_point2: Vec<Ext3V2Fixture>,
    pub additional_evaluation_points: Vec<Vec<Ext3V2Fixture>>,
    pub rounds: Vec<WhirRoundParamsFixture>,
}

impl WhirParamsV2Fixture {
    fn from_without_points(params: WhirParamsFixture) -> Self {
        Self {
            num_variables: params.num_variables,
            folding_factor: params.folding_factor,
            num_vectors: params.num_vectors,
            num_commitments: params.num_commitments,
            out_domain_samples: params.out_domain_samples,
            in_domain_samples: params.in_domain_samples,
            initial_sumcheck_rounds: params.initial_sumcheck_rounds,
            num_rounds: params.num_rounds,
            final_sumcheck_rounds: params.final_sumcheck_rounds,
            final_size: params.final_size,
            initial_codeword_length: params.initial_codeword_length,
            initial_merkle_depth: params.initial_merkle_depth,
            initial_domain_generator: params.initial_domain_generator,
            initial_interleaving_depth: params.initial_interleaving_depth,
            initial_num_variables: params.initial_num_variables,
            initial_coset_size: params.initial_coset_size,
            initial_num_cosets: params.initial_num_cosets,
            initial_sumcheck_pow_threshold: params.initial_sumcheck_pow_threshold,
            final_pow_threshold: params.final_pow_threshold,
            final_sumcheck_pow_threshold: params.final_sumcheck_pow_threshold,
            evaluation_point: Vec::new(),
            evaluation_point2: Vec::new(),
            additional_evaluation_points: Vec::new(),
            rounds: params.rounds,
        }
    }

    /// Return the point-free shape used by the existing cross-language trace
    /// snapshot.  No semantic information is lost because deployment points
    /// are required to be empty.
    pub fn without_points(&self) -> Result<WhirParamsFixture, FixtureV2Error> {
        self.require_empty_points()?;
        Ok(WhirParamsFixture {
            num_variables: self.num_variables,
            folding_factor: self.folding_factor,
            num_vectors: self.num_vectors,
            num_commitments: self.num_commitments,
            out_domain_samples: self.out_domain_samples,
            in_domain_samples: self.in_domain_samples,
            initial_sumcheck_rounds: self.initial_sumcheck_rounds,
            num_rounds: self.num_rounds,
            final_sumcheck_rounds: self.final_sumcheck_rounds,
            final_size: self.final_size,
            initial_codeword_length: self.initial_codeword_length,
            initial_merkle_depth: self.initial_merkle_depth,
            initial_domain_generator: self.initial_domain_generator.clone(),
            initial_interleaving_depth: self.initial_interleaving_depth,
            initial_num_variables: self.initial_num_variables,
            initial_coset_size: self.initial_coset_size,
            initial_num_cosets: self.initial_num_cosets,
            initial_sumcheck_pow_threshold: self.initial_sumcheck_pow_threshold.clone(),
            final_pow_threshold: self.final_pow_threshold.clone(),
            final_sumcheck_pow_threshold: self.final_sumcheck_pow_threshold.clone(),
            rounds: self.rounds.clone(),
        })
    }

    fn require_empty_points(&self) -> Result<(), FixtureV2Error> {
        if !self.evaluation_point.is_empty()
            || !self.evaluation_point2.is_empty()
            || !self.additional_evaluation_points.is_empty()
        {
            return Err(FixtureV2Error::Invalid(
                "deployment WHIR point arrays must be empty and verifier-derived",
            ));
        }
        if self.rounds.len() != self.num_rounds {
            return Err(FixtureV2Error::Invalid(
                "WHIR round count disagrees with the serialized rounds",
            ));
        }
        Ok(())
    }
}

/// Complete call-time `MleVerifierV2.VerificationConfig` object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct MleVerificationConfigV2Fixture {
    pub circuit: CircuitParametersV2Fixture,
    pub public_input_wire_map: String,
    pub k_is: Vec<String>,
    pub subgroup_gen_powers: Vec<String>,
    pub gates: Vec<GateInfoV2Fixture>,
    pub whir: WhirParamsV2Fixture,
}

/// All immutable values pinned by one `MleVerifierV2` deployment.  The
/// separately serialized [`MleVerificationConfigV2Fixture`] supplies the
/// complete dynamic constructor/call object whose digests are recorded here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PinnedMleVerifierV2Fixture {
    pub preprocessed_commitment_root: String,
    pub circuit_config_digest: String,
    pub whir_parameters_digest: String,
    pub verification_config_digest: String,
    pub whir_protocol_id: String,
    pub whir_session_id: String,
    pub circuit_digest: [String; CIRCUIT_DIGEST_LENGTH_V2],
}

/// Trusted compact decoder dimensions exported from the same common data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CompactV2ShapeFixture {
    pub degree_bits: usize,
    pub constituent_width: usize,
    pub circuit_digest_len: usize,
    pub public_inputs_len: usize,
    pub num_constants: usize,
    pub num_routed_wires: usize,
    pub num_wires: usize,
    pub gate_round_degree: usize,
    pub max_whir_narg_bytes: usize,
    pub max_whir_hint_bytes: usize,
    pub max_encoded_bytes: usize,
}

impl CompactV2ShapeFixture {
    pub fn encode(shape: &CompactV2Shape) -> Self {
        Self {
            degree_bits: shape.degree_bits,
            constituent_width: shape.constituent_width,
            circuit_digest_len: shape.circuit_digest_len,
            public_inputs_len: shape.public_inputs_len,
            num_constants: shape.num_constants,
            num_routed_wires: shape.num_routed_wires,
            num_wires: shape.num_wires,
            gate_round_degree: shape.gate_round_degree,
            max_whir_narg_bytes: shape.max_whir_narg_bytes,
            max_whir_hint_bytes: shape.max_whir_hint_bytes,
            max_encoded_bytes: shape.max_encoded_bytes,
        }
    }

    pub fn decode(&self) -> CompactV2Shape {
        CompactV2Shape {
            degree_bits: self.degree_bits,
            constituent_width: self.constituent_width,
            circuit_digest_len: self.circuit_digest_len,
            public_inputs_len: self.public_inputs_len,
            num_constants: self.num_constants,
            num_routed_wires: self.num_routed_wires,
            num_wires: self.num_wires,
            gate_round_degree: self.gate_round_degree,
            max_whir_narg_bytes: self.max_whir_narg_bytes,
            max_whir_hint_bytes: self.max_whir_hint_bytes,
            max_encoded_bytes: self.max_encoded_bytes,
        }
    }
}

/// One canonical proof byte representation and its integrity metadata.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct EncodedProofV2Fixture {
    pub encoding: String,
    pub byte_length: usize,
    pub keccak256: String,
    pub bytes: String,
}

impl EncodedProofV2Fixture {
    pub fn from_bytes(encoding: impl Into<String>, bytes: &[u8]) -> Self {
        let digest: [u8; 32] = Keccak256::digest(bytes).into();
        Self {
            encoding: encoding.into(),
            byte_length: bytes.len(),
            keccak256: encode_hex(&digest),
            bytes: encode_hex(bytes),
        }
    }

    /// Decode a byte record only when its encoding label, recorded length,
    /// canonical lowercase hex, and Keccak digest all agree.
    pub fn decode_and_validate(&self, encoding: &str) -> Result<Vec<u8>, FixtureV2Error> {
        if self.encoding != encoding {
            return Err(FixtureV2Error::Invalid("proof encoding label mismatch"));
        }
        let bytes = decode_hex(&self.bytes, "encoded proof bytes")?;
        if bytes.len() != self.byte_length {
            return Err(FixtureV2Error::Invalid(
                "encoded proof byte length mismatch",
            ));
        }
        let digest: [u8; 32] = Keccak256::digest(&bytes).into();
        let recorded = decode_fixed_hex::<32>(&self.keccak256, "encoded proof keccak256")?;
        if digest != recorded {
            return Err(FixtureV2Error::Invalid("encoded proof keccak256 mismatch"));
        }
        Ok(bytes)
    }
}

/// Machine-readable proof sizing for DA/gas admission policy.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ProofEncodingStatsV2Fixture {
    pub solidity_abi_bytes: usize,
    pub solidity_abi_verification_config_bytes: usize,
    pub compact_bytes: usize,
    pub whir_transcript_bytes: usize,
    pub whir_hint_bytes: usize,
}

/// Exact grammar-theoretic maximum for one WHIR Merkle opening.
///
/// `max_distinct_queries` assumes every sampled index is distinct until the
/// codeword is exhausted. `max_merkle_siblings_per_commitment` additionally
/// places those leaves so that the canonical binary multiproof contains the
/// greatest possible number of sibling hashes. This is independent of any
/// particular Fiat--Shamir draw.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct WhirOpeningSizeUpperBoundV2 {
    pub codeword_length: usize,
    pub sample_count: usize,
    pub max_distinct_queries: usize,
    pub num_columns: usize,
    pub field_limbs: usize,
    pub num_commitments: usize,
    pub max_field_bytes_per_commitment: usize,
    pub max_merkle_siblings_per_commitment: usize,
    pub max_bytes_per_commitment: usize,
    pub max_bytes: usize,
}

/// Exact NARG length and worst-case canonical hint length for one native WHIR
/// profile. The NARG grammar has no query-dependent lengths; hints do.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct WhirProofSizeUpperBoundV2 {
    pub packed_num_variables: usize,
    pub narg_bytes: usize,
    pub max_hint_bytes: usize,
    pub max_total_bytes: usize,
    pub openings: Vec<WhirOpeningSizeUpperBoundV2>,
}

/// Worst-case proof sizes for a complete circuit shape. These values combine
/// the exact fixed outer grammar with [`WhirProofSizeUpperBoundV2`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ProofEncodingSizeUpperBoundV2 {
    pub packed_num_variables: usize,
    pub fixed_compact_bytes: usize,
    pub max_whir_transcript_bytes: usize,
    pub max_whir_hint_bytes: usize,
    pub max_compact_bytes: usize,
    pub max_solidity_abi_bytes: usize,
    pub compact_cap_bytes: usize,
    pub fits_whir_blob_caps: bool,
    pub fits_compact_cap: bool,
    pub whir: WhirProofSizeUpperBoundV2,
}

/// Deterministic deployment/configuration artifact for one MLE/WHIR V2
/// implementation circuit using the current wire-v3 protocol.
///
/// Unlike [`MleVerifierV2Fixture`], this object contains no proof and needs no
/// witness. Every field is derived from the circuit, [`mle_setup_v2`], and the
/// generated wire-v3 schema (retained under historical V2 filenames). Deployment tooling should consume this
/// artifact rather than treating one randomized proof fixture as the source
/// of constructor configuration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct MleVerifierV2ConfigFixture {
    pub schema: String,
    pub schema_version: u64,
    pub protocol_version: u64,
    pub proof_abi_signature: String,
    pub proof_layout_hash: String,
    pub compact_layout_hash: String,
    pub compact_proof_encoding: String,
    pub whir_pow_bits: usize,
    pub verification_key: MleVerificationKeyV2Fixture,
    pub verification_config: MleVerificationConfigV2Fixture,
    pub pinned_verifier: PinnedMleVerifierV2Fixture,
    pub solidity_abi_verification_config: EncodedProofV2Fixture,
    pub compact_shape: CompactV2ShapeFixture,
    pub size_upper_bound: ProofEncodingSizeUpperBoundV2,
}

/// Self-contained production artifact for one atomic MLE/WHIR v2 proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct MleVerifierV2Fixture {
    pub schema: String,
    pub schema_version: u64,
    pub protocol_version: u64,
    pub proof_abi_signature: String,
    pub proof_layout_hash: String,
    pub proof: MleProofV2Fixture,
    pub verification_key: MleVerificationKeyV2Fixture,
    pub verification_config: MleVerificationConfigV2Fixture,
    pub pinned_verifier: PinnedMleVerifierV2Fixture,
    pub solidity_abi_proof: EncodedProofV2Fixture,
    pub solidity_abi_verification_config: EncodedProofV2Fixture,
    pub compact_shape: CompactV2ShapeFixture,
    pub compact_proof: EncodedProofV2Fixture,
    pub stats: ProofEncodingStatsV2Fixture,
    pub size_upper_bound: ProofEncodingSizeUpperBoundV2,
}

/// Native canonical WHIR deployment profile and all identifiers pinned by the
/// verifier constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirDeploymentProfileV2 {
    pub params: WhirParamsV2Fixture,
    pub protocol_id: [u8; WHIR_PROTOCOL_ID_BYTES],
    pub session_id: [u8; WHIR_SESSION_ID_BYTES],
    pub parameters_digest: [u8; 32],
    pub proof_size_upper_bound: WhirProofSizeUpperBoundV2,
}

/// Result of the one-shot prove-and-export API.  Keeping the native proof and
/// VK beside the serialized artifact lets callers persist either form without
/// proving twice.
#[derive(Clone, Debug)]
pub struct ProvedMleV2Fixture<F: Field> {
    pub proof: MleProofV2<F>,
    pub verification_key: MleVerificationKeyV2<F>,
    pub fixture: MleVerifierV2Fixture,
}

/// Export failure.  Every variant is non-convicting configuration/tooling
/// failure; callers must never reinterpret it as an invalid submitted proof.
#[derive(Debug)]
pub enum FixtureV2Error {
    Invalid(&'static str),
    InvalidOwned(String),
    Compact(CompactV2Error),
    Json(serde_json::Error),
    Verification(anyhow::Error),
}

impl core::fmt::Display for FixtureV2Error {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Invalid(message) => formatter.write_str(message),
            Self::InvalidOwned(message) => formatter.write_str(message),
            Self::Compact(error) => write!(formatter, "compact-v2 error: {error}"),
            Self::Json(error) => write!(formatter, "v2 fixture JSON error: {error}"),
            Self::Verification(error) => write!(formatter, "v2 proof/configuration error: {error}"),
        }
    }
}

impl std::error::Error for FixtureV2Error {}

impl From<CompactV2Error> for FixtureV2Error {
    fn from(value: CompactV2Error) -> Self {
        Self::Compact(value)
    }
}

impl From<serde_json::Error> for FixtureV2Error {
    fn from(value: serde_json::Error) -> Self {
        Self::Json(value)
    }
}

impl MleVerifierV2ConfigFixture {
    /// Serialize the deterministic configuration with stable pretty
    /// formatting and one trailing newline.
    pub fn to_canonical_json(&self) -> Result<String, FixtureV2Error> {
        require_config_header(self)?;
        let mut json = serde_json::to_string_pretty(self)?;
        json.push('\n');
        Ok(json)
    }

    /// Strictly parse the config-only schema. Unknown and compatibility
    /// fields fail via serde.
    pub fn from_json(json: &str) -> Result<Self, FixtureV2Error> {
        let fixture: Self = serde_json::from_str(json)?;
        fixture.validate_self_consistency()?;
        Ok(fixture)
    }

    /// Parse and require byte-for-byte canonical JSON formatting.
    pub fn from_canonical_json(json: &str) -> Result<Self, FixtureV2Error> {
        let fixture = Self::from_json(json)?;
        if fixture.to_canonical_json()? != json {
            return Err(FixtureV2Error::Invalid(
                "v2 config fixture JSON is valid but not canonically encoded",
            ));
        }
        Ok(fixture)
    }

    /// Validate every proof-free view that can be checked without rebuilding
    /// the Plonky2 circuit. This is the deployment-artifact trust boundary:
    /// the JSON VK, call-time config, packed PI wire map, WHIR profile,
    /// compact shape, Solidity ABI bytes, and immutable digest views must all
    /// describe one canonical current-generation object.
    ///
    /// [`Self::validate_against_circuit`] remains the stronger producer-side
    /// check because only the circuit can authenticate its preprocessing root
    /// and gate semantics. Consumers that only possess the deployment
    /// artifact still get this complete cross-view validation through
    /// [`Self::from_json`] and [`Self::from_canonical_json`].
    pub fn validate_self_consistency(&self) -> Result<(), FixtureV2Error> {
        self.validate_self_consistency_at_whir_security(WHIR_SECURITY_LEVEL_V2)
    }

    fn validate_self_consistency_at_whir_security(
        &self,
        whir_security_level: usize,
    ) -> Result<(), FixtureV2Error> {
        require_config_header(self)?;
        validate_config_pinned_views(self)?;

        let vk = self.verification_key.try_decode::<GoldilocksField>()?;
        let circuit = &self.verification_config.circuit;
        let expected_width = constituent_group_width_v2(
            circuit.num_constants,
            circuit.num_routed_wires,
            circuit.num_wires,
        );
        if circuit.degree_bits == 0
            || circuit.degree_bits > MAX_ROW_VARIABLES_V2
            || circuit.num_public_inputs > crate::protocol_schema_v2::MAX_PUBLIC_INPUTS_V2
            || circuit.num_routed_wires > crate::protocol_schema_v2::MAX_ROUTED_WIRES_V2
            || expected_width == 0
            || expected_width > MAX_CONSTITUENT_WIDTH_V2
            || circuit.num_gate_constraints > crate::protocol_schema_v2::MAX_GATE_CONSTRAINTS_V2
            || circuit.quotient_degree_factor == 0
            || circuit.quotient_degree_factor + 2
                > crate::protocol_schema_v2::MAX_GATE_ROUND_DEGREE_V2
            || self.verification_config.gates.is_empty()
            || self.verification_config.gates.len() > crate::protocol_schema_v2::MAX_GATE_ROWS_V2
            || circuit.num_selectors == 0
        {
            return Err(FixtureV2Error::Invalid(
                "config circuit exceeds the reviewed MLE security profile",
            ));
        }

        if vk.constituent_width != expected_width
            || vk.circuit_digest.len() != CIRCUIT_DIGEST_LENGTH_V2
            || vk.num_constants != circuit.num_constants
            || vk.num_routed_wires != circuit.num_routed_wires
            || vk.num_wires != circuit.num_wires
            || vk.num_selectors != circuit.num_selectors
            || vk.num_gate_constraints != circuit.num_gate_constraints
            || vk.quotient_degree_factor != circuit.quotient_degree_factor
            || self.verification_key.public_input_wire_map
                != self.verification_config.public_input_wire_map
            || self.verification_key.k_is != self.verification_config.k_is
            || self.verification_key.subgroup_gen_powers
                != self.verification_config.subgroup_gen_powers
            || self.verification_key.gates != self.verification_config.gates
        {
            return Err(FixtureV2Error::Invalid(
                "config verification-key and Solidity configuration views disagree",
            ));
        }

        let degree = 1usize
            .checked_shl(
                u32::try_from(circuit.degree_bits)
                    .map_err(|_| FixtureV2Error::Invalid("config degree bits do not fit u32"))?,
            )
            .ok_or(FixtureV2Error::Invalid("config row degree overflow"))?;
        crate::vk_v2::decode_public_input_wire_map_v2(
            &vk.public_input_wire_map,
            circuit.num_public_inputs,
            degree,
            circuit.num_routed_wires,
        )
        .map_err(|error| {
            FixtureV2Error::InvalidOwned(format!("invalid public-input wire map: {error}"))
        })?;
        if vk.k_is.len() != circuit.num_routed_wires
            || vk.subgroup_gen_powers.len() != circuit.degree_bits
        {
            return Err(FixtureV2Error::Invalid(
                "config coset shifts or subgroup powers have the wrong length",
            ));
        }
        let mut subgroup_value = GoldilocksField::two_adic_subgroup(circuit.degree_bits)
            .get(1)
            .copied()
            .unwrap_or(GoldilocksField::ONE);
        let mut expected_subgroup_powers = Vec::with_capacity(circuit.degree_bits);
        for _ in 0..circuit.degree_bits {
            expected_subgroup_powers.push(subgroup_value);
            subgroup_value *= subgroup_value;
        }
        if vk.subgroup_gen_powers != expected_subgroup_powers {
            return Err(FixtureV2Error::Invalid(
                "config subgroup generator powers are not canonical",
            ));
        }
        let expected_circuit_config_digest = crate::vk_v2::circuit_config_digest_from_parts_v2(
            circuit.degree_bits,
            circuit.num_public_inputs,
            circuit.num_constants,
            circuit.num_routed_wires,
            circuit.num_wires,
            circuit.num_selectors,
            circuit.num_gate_constraints,
            circuit.quotient_degree_factor,
            &vk.circuit_digest,
            &vk.k_is,
            &vk.subgroup_gen_powers,
            &vk.gates,
            &vk.public_input_wire_map,
        )
        .map_err(|error| {
            FixtureV2Error::InvalidOwned(format!(
                "invalid circuit-configuration digest preimage: {error}"
            ))
        })?;
        if vk.circuit_config_digest != expected_circuit_config_digest {
            return Err(FixtureV2Error::Invalid(
                "config circuit-configuration digest does not match its VK fields",
            ));
        }

        validate_config_whir_profile_at_security(
            self,
            circuit.degree_bits,
            expected_width,
            whir_security_level,
        )?;
        let expected_config_abi =
            solidity_abi_encode_verification_config_v2(&self.verification_config)?;
        let actual_config_abi = self
            .solidity_abi_verification_config
            .decode_and_validate(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2)?;
        if actual_config_abi != expected_config_abi {
            return Err(FixtureV2Error::Invalid(
                "recorded Solidity verification-config ABI bytes are not canonical",
            ));
        }

        let expected_shape = CompactV2Shape {
            degree_bits: circuit.degree_bits,
            constituent_width: expected_width,
            circuit_digest_len: CIRCUIT_DIGEST_LENGTH_V2,
            public_inputs_len: circuit.num_public_inputs,
            num_constants: circuit.num_constants,
            num_routed_wires: circuit.num_routed_wires,
            num_wires: circuit.num_wires,
            gate_round_degree: circuit.quotient_degree_factor + 2,
            max_whir_narg_bytes: MAX_WHIR_NARG_BYTES_V2,
            max_whir_hint_bytes: MAX_WHIR_HINT_BYTES_V2,
            max_encoded_bytes: MAX_COMPACT_PROOF_BYTES_V2,
        };
        expected_shape.fixed_encoded_len()?;
        if self.compact_shape.decode() != expected_shape {
            return Err(FixtureV2Error::Invalid(
                "config compact shape drifted from its circuit dimensions",
            ));
        }
        let expected_upper_bound =
            proof_encoding_size_upper_bound_at_security_v2(&expected_shape, whir_security_level)?;
        if self.size_upper_bound != expected_upper_bound {
            return Err(FixtureV2Error::Invalid(
                "config proof-size bound drifted from its canonical shape",
            ));
        }
        require_deployable_size_upper_bound(&expected_upper_bound)?;
        Ok(())
    }

    /// Re-derive the deterministic VK and every deployment view from the
    /// supplied circuit. This authenticates the preprocessed commitment root;
    /// checking only common data cannot do so because that root depends on
    /// prover-only preprocessing.
    pub fn validate_against_circuit<
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F>,
        const D: usize,
    >(
        &self,
        circuit: &CircuitData<F, C, D>,
    ) -> Result<(), FixtureV2Error>
    where
        C::Hasher: Hasher<F>,
    {
        let expected_vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
        validate_config_fixture_against_common_and_vk(self, &circuit.common, &expected_vk)
    }
}

impl MleVerifierV2Fixture {
    /// Project the deterministic deployment/configuration portion of a full
    /// proof fixture. The result is byte-for-byte equal to
    /// [`try_export_mle_v2_config_fixture`] for the same circuit.
    pub fn config_fixture(&self) -> MleVerifierV2ConfigFixture {
        MleVerifierV2ConfigFixture {
            schema: MLE_VERIFIER_CONFIG_FIXTURE_SCHEMA_V2.to_string(),
            schema_version: self.schema_version,
            protocol_version: self.protocol_version,
            proof_abi_signature: self.proof_abi_signature.clone(),
            proof_layout_hash: self.proof_layout_hash.clone(),
            compact_layout_hash: encode_hex(&COMPACT_LAYOUT_HASH_V2),
            compact_proof_encoding: std::str::from_utf8(&COMPACT_MAGIC_V2)
                .expect("compact-v2 magic is ASCII")
                .to_string(),
            whir_pow_bits: WHIR_POW_BITS_V2,
            verification_key: self.verification_key.clone(),
            verification_config: self.verification_config.clone(),
            pinned_verifier: self.pinned_verifier.clone(),
            solidity_abi_verification_config: self.solidity_abi_verification_config.clone(),
            compact_shape: self.compact_shape.clone(),
            size_upper_bound: self.size_upper_bound.clone(),
        }
    }

    /// Serialize with stable pretty formatting and one trailing newline.
    pub fn to_canonical_json(&self) -> Result<String, FixtureV2Error> {
        self.proof.validate_abi_keys()?;
        let mut json = serde_json::to_string_pretty(self)?;
        json.push('\n');
        Ok(json)
    }

    /// Strictly parse the schema.  Unknown fields fail via serde.  Use
    /// [`Self::validate_against_common`] before consuming the result.
    pub fn from_json(json: &str) -> Result<Self, FixtureV2Error> {
        let fixture: Self = serde_json::from_str(json)?;
        // Header identity is part of the artifact boundary, not something that
        // may be deferred until a caller happens to possess circuit data. In
        // particular, `config_fixture()` intentionally projects the full schema
        // into the distinct config schema, so a later full/config equality
        // check cannot recover or authenticate the original top-level string.
        require_header(&fixture)?;
        fixture.proof.validate_abi_keys()?;
        Ok(fixture)
    }

    /// Parse and require byte-for-byte canonical JSON formatting.
    pub fn from_canonical_json(json: &str) -> Result<Self, FixtureV2Error> {
        let fixture = Self::from_json(json)?;
        if fixture.to_canonical_json()? != json {
            return Err(FixtureV2Error::Invalid(
                "v2 fixture JSON is valid but not canonically encoded",
            ));
        }
        Ok(fixture)
    }

    /// Decode both native objects and check every duplicate view, digest,
    /// schema marker, byte encoding, and the complete Rust verifier.
    pub fn validate_against_common<F: RichField + Extendable<D>, const D: usize>(
        &self,
        common_data: &CommonCircuitData<F, D>,
    ) -> Result<(MleProofV2<F>, MleVerificationKeyV2<F>), FixtureV2Error> {
        require_header(self)?;
        validate_pinned_views(self)?;
        self.proof.validate_abi_keys()?;

        // Authenticate every deterministic deployment/configuration field via
        // the same consumer path as the config-only artifact. This prevents
        // the full and proof-free schemas from silently acquiring different
        // profile, digest, ABI, or size checks.
        let config_fixture = self.config_fixture();
        let vk = validate_config_fixture_against_common(&config_fixture, common_data)?;
        let shape = config_fixture.compact_shape.decode();
        let compact = self
            .compact_proof
            .decode_and_validate(std::str::from_utf8(&COMPACT_MAGIC_V2).unwrap())?;
        let proof = decode_compact_v2::<F>(&compact, &shape)?;
        if MleProofV2Fixture::encode(&proof) != self.proof {
            return Err(FixtureV2Error::Invalid(
                "Solidity proof object disagrees with canonical compact bytes",
            ));
        }
        let expected_abi = solidity_abi_encode_mle_proof_v2(&self.proof)?;
        let actual_abi = self
            .solidity_abi_proof
            .decode_and_validate(SOLIDITY_MLE_PROOF_ENCODING_V2)?;
        if actual_abi != expected_abi {
            return Err(FixtureV2Error::Invalid(
                "recorded Solidity ABI proof bytes are not canonical",
            ));
        }

        let actual_config_abi = config_fixture
            .solidity_abi_verification_config
            .decode_and_validate(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2)?;
        validate_stats(self, &proof, &compact, &actual_abi, &actual_config_abi)?;
        mle_verify_v2(common_data, &vk, &proof).map_err(FixtureV2Error::Verification)?;
        Ok((proof, vk))
    }
}

/// Export the complete deterministic deployment configuration for a circuit
/// without constructing a witness or proof.
///
/// The VK is derived internally with [`mle_setup_v2`]. Callers cannot supply
/// independently assembled roots, WHIR identifiers, shapes, or Solidity ABI
/// bytes.
pub fn try_export_mle_v2_config_fixture<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    circuit: &CircuitData<F, C, D>,
) -> Result<MleVerifierV2ConfigFixture, FixtureV2Error>
where
    C::Hasher: Hasher<F>,
{
    let verification_key = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    try_export_mle_v2_config_fixture_from_vk(&circuit.common, &verification_key)
}

fn try_export_mle_v2_config_fixture_from_vk<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    vk: &MleVerificationKeyV2<F>,
) -> Result<MleVerifierV2ConfigFixture, FixtureV2Error> {
    let shape = compact_v2_shape_for_common(common_data, vk.constituent_width)?;
    let profile =
        derive_whir_deployment_profile_v2(common_data.degree_bits(), vk.constituent_width)?;
    if profile.protocol_id != vk.whir_protocol_id || profile.session_id != vk.whir_session_id {
        return Err(FixtureV2Error::Invalid(
            "VK WHIR identifiers differ from the canonical deployment profile",
        ));
    }
    let verification_config = verification_config_v2(common_data, vk)?;
    if verification_config.whir != profile.params {
        return Err(FixtureV2Error::Invalid(
            "derived WHIR config differs from the canonical deployment profile",
        ));
    }
    let size_upper_bound = proof_encoding_size_upper_bound_v2(&shape)?;
    if size_upper_bound.whir != profile.proof_size_upper_bound {
        return Err(FixtureV2Error::Invalid(
            "WHIR proof-size bound differs between profile and circuit derivation",
        ));
    }
    require_deployable_size_upper_bound(&size_upper_bound)?;
    let solidity_abi_verification_config =
        solidity_abi_encode_verification_config_v2(&verification_config)?;
    let verification_config_digest: [u8; 32] =
        Keccak256::digest(&solidity_abi_verification_config).into();
    let fixture = MleVerifierV2ConfigFixture {
        schema: MLE_VERIFIER_CONFIG_FIXTURE_SCHEMA_V2.to_string(),
        schema_version: SCHEMA_VERSION_CURRENT,
        protocol_version: MLE_PROTOCOL_VERSION_CURRENT,
        proof_abi_signature: MLE_PROOF_ABI_SIGNATURE_V2.to_string(),
        proof_layout_hash: encode_hex(&MLE_PROOF_LAYOUT_HASH_V2),
        compact_layout_hash: encode_hex(&COMPACT_LAYOUT_HASH_V2),
        compact_proof_encoding: std::str::from_utf8(&COMPACT_MAGIC_V2)
            .expect("compact-v2 magic is ASCII")
            .to_string(),
        whir_pow_bits: WHIR_POW_BITS_V2,
        verification_key: MleVerificationKeyV2Fixture::encode(vk),
        verification_config,
        pinned_verifier: PinnedMleVerifierV2Fixture {
            preprocessed_commitment_root: encode_hex(&vk.preprocessed_commitment_root),
            circuit_config_digest: encode_hex(&vk.circuit_config_digest),
            whir_parameters_digest: encode_hex(&profile.parameters_digest),
            verification_config_digest: encode_hex(&verification_config_digest),
            whir_protocol_id: encode_hex(&vk.whir_protocol_id),
            whir_session_id: encode_hex(&vk.whir_session_id),
            circuit_digest: encode_circuit_digest(&vk.circuit_digest)?,
        },
        solidity_abi_verification_config: EncodedProofV2Fixture::from_bytes(
            SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2,
            &solidity_abi_verification_config,
        ),
        compact_shape: CompactV2ShapeFixture::encode(&shape),
        size_upper_bound,
    };
    validate_config_fixture_against_common_and_vk(&fixture, common_data, vk)?;
    Ok(fixture)
}

/// Verify a native proof and export every representation needed by Solidity,
/// deployment tooling, publishers, and DA attestation.
pub fn try_export_mle_v2_fixture<F: RichField + Extendable<D>, const D: usize>(
    proof: &MleProofV2<F>,
    vk: &MleVerificationKeyV2<F>,
    common_data: &CommonCircuitData<F, D>,
) -> Result<MleVerifierV2Fixture, FixtureV2Error> {
    // This is intentionally first.  No fixture is emitted for a proof that is
    // only structurally encodable but invalid against the pinned VK.
    mle_verify_v2(common_data, vk, proof).map_err(FixtureV2Error::Verification)?;

    // Build the deterministic deployment half through exactly the same
    // internal path as the proof-free public exporter.
    let config_fixture = try_export_mle_v2_config_fixture_from_vk(common_data, vk)?;
    let shape = config_fixture.compact_shape.decode();
    let compact = encode_compact_v2(proof, &shape)?;
    let decoded = decode_compact_v2::<F>(&compact, &shape)?;
    let proof_fixture = MleProofV2Fixture::encode(proof);
    if MleProofV2Fixture::encode(&decoded) != proof_fixture {
        return Err(FixtureV2Error::Invalid(
            "compact-v2 export did not round-trip the Solidity proof view",
        ));
    }
    proof_fixture.validate_abi_keys()?;

    let solidity_abi = solidity_abi_encode_mle_proof_v2(&proof_fixture)?;
    let solidity_abi_verification_config = config_fixture
        .solidity_abi_verification_config
        .decode_and_validate(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2)?;
    let fixture = MleVerifierV2Fixture {
        schema: MLE_VERIFIER_FIXTURE_SCHEMA_V2.to_string(),
        schema_version: config_fixture.schema_version,
        protocol_version: config_fixture.protocol_version,
        proof_abi_signature: config_fixture.proof_abi_signature.clone(),
        proof_layout_hash: config_fixture.proof_layout_hash.clone(),
        proof: proof_fixture,
        verification_key: config_fixture.verification_key.clone(),
        verification_config: config_fixture.verification_config.clone(),
        pinned_verifier: config_fixture.pinned_verifier.clone(),
        solidity_abi_proof: EncodedProofV2Fixture::from_bytes(
            SOLIDITY_MLE_PROOF_ENCODING_V2,
            &solidity_abi,
        ),
        solidity_abi_verification_config: config_fixture.solidity_abi_verification_config.clone(),
        compact_shape: config_fixture.compact_shape.clone(),
        compact_proof: EncodedProofV2Fixture::from_bytes(
            std::str::from_utf8(&COMPACT_MAGIC_V2).unwrap(),
            &compact,
        ),
        stats: ProofEncodingStatsV2Fixture {
            solidity_abi_bytes: solidity_abi.len(),
            solidity_abi_verification_config_bytes: solidity_abi_verification_config.len(),
            compact_bytes: compact.len(),
            whir_transcript_bytes: proof.whir_eval_proof.narg_string.len(),
            whir_hint_bytes: proof.whir_eval_proof.hints.len(),
        },
        size_upper_bound: config_fixture.size_upper_bound.clone(),
    };
    if fixture.config_fixture() != config_fixture {
        return Err(FixtureV2Error::Invalid(
            "full proof fixture drifted from the shared config-only export",
        ));
    }
    // Pure cross-view checks are cheap and catch exporter drift immediately.
    require_header(&fixture)?;
    validate_pinned_views(&fixture)?;
    validate_stats(
        &fixture,
        proof,
        &compact,
        &solidity_abi,
        &solidity_abi_verification_config,
    )?;
    // Exercise the public consumer path before publishing: strict JSON-facing
    // views, both ABI payloads, compact decoding, all digests, and the native
    // verifier must agree on this exact artifact.
    let _ = fixture.validate_against_common(common_data)?;
    Ok(fixture)
}

/// One-shot production path from an arbitrary Plonky2 circuit and partial
/// witness to the native v2 proof/VK and every serialized Solidity/DA view.
///
/// The returned artifact has already passed `mle_verify_v2`; callers do not
/// need (and must not implement) a second fixture assembly step.
pub fn try_prove_and_export_mle_v2<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    circuit: &CircuitData<F, C, D>,
    witness: PartialWitness<F>,
    timing: &mut TimingTree,
) -> Result<ProvedMleV2Fixture<F>, FixtureV2Error>
where
    C::Hasher: Hasher<F>,
    C::InnerHasher: Hasher<F>,
{
    let verification_key = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let proof = mle_prove_v2::<F, C, D>(&circuit.prover_only, &circuit.common, witness, timing)
        .map_err(FixtureV2Error::Verification)?;
    let fixture = try_export_mle_v2_fixture(&proof, &verification_key, &circuit.common)?;
    Ok(ProvedMleV2Fixture {
        proof,
        verification_key,
        fixture,
    })
}

/// Canonical compact dimensions for a circuit.  Resource caps come only from
/// the generated v2 schema.
pub fn compact_v2_shape_for_common<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    constituent_width: usize,
) -> Result<CompactV2Shape, FixtureV2Error> {
    let expected_width = constituent_group_width_v2(
        common_data.num_constants,
        common_data.config.num_routed_wires,
        common_data.config.num_wires,
    );
    if constituent_width != expected_width {
        return Err(FixtureV2Error::Invalid(
            "requested compact shape has a non-canonical constituent width",
        ));
    }
    let shape = CompactV2Shape {
        degree_bits: common_data.degree_bits(),
        constituent_width,
        circuit_digest_len: CIRCUIT_DIGEST_LENGTH_V2,
        public_inputs_len: common_data.num_public_inputs,
        num_constants: common_data.num_constants,
        num_routed_wires: common_data.config.num_routed_wires,
        num_wires: common_data.config.num_wires,
        gate_round_degree: common_data.quotient_degree_factor + 2,
        max_whir_narg_bytes: MAX_WHIR_NARG_BYTES_V2,
        max_whir_hint_bytes: MAX_WHIR_HINT_BYTES_V2,
        max_encoded_bytes: MAX_COMPACT_PROOF_BYTES_V2,
    };
    // Use the codec's reviewed shape validation rather than duplicating it.
    shape.fixed_encoded_len()?;
    Ok(shape)
}

/// Maximum number of sibling hashes emitted by the pinned binary Merkle
/// multiproof for `distinct_queries` distinct leaves.
///
/// Let `a_j` be the number of occupied ancestors after `j` tree levels. The
/// verifier consumes `2*a_(j+1) - a_j` siblings at level `j`, so the total is
/// `sum(a_1 .. a_(L-1)) + 2 - k`. Every `a_j` is at most
/// `min(k, N / 2^j)`, and a bit-reversal placement of the leaves attains all
/// those maxima simultaneously. Consequently this computes the exact maximum,
/// rather than the looser `queries * depth` bound.
pub fn max_merkle_multiproof_siblings_v2(
    num_leaves: usize,
    distinct_queries: usize,
) -> Result<usize, FixtureV2Error> {
    if !num_leaves.is_power_of_two() {
        return Err(FixtureV2Error::Invalid(
            "WHIR Merkle leaf count is not a power of two",
        ));
    }
    if distinct_queries > num_leaves {
        return Err(FixtureV2Error::Invalid(
            "WHIR distinct query count exceeds the Merkle leaf count",
        ));
    }
    if distinct_queries == 0 || num_leaves == 1 {
        return Ok(0);
    }

    let mut occupied_ancestor_sum = 0usize;
    let mut level_nodes = num_leaves / 2;
    // The root is excluded from the sum and contributes the final `+ 2`.
    while level_nodes > 1 {
        occupied_ancestor_sum = size_add(
            occupied_ancestor_sum,
            distinct_queries.min(level_nodes),
            "WHIR Merkle sibling bound",
        )?;
        level_nodes /= 2;
    }
    size_add(occupied_ancestor_sum, 2, "WHIR Merkle sibling bound")?
        .checked_sub(distinct_queries)
        .ok_or(FixtureV2Error::Invalid(
            "WHIR Merkle sibling bound underflow",
        ))
}

/// Derive the native WHIR proof-size boundary directly from the complete
/// Solidity deployment parameters. No proof sampling is involved.
pub fn whir_proof_size_upper_bound_v2(
    params: &WhirParamsV2Fixture,
) -> Result<WhirProofSizeUpperBoundV2, FixtureV2Error> {
    params.require_empty_points()?;
    if params.num_variables == 0
        || params.num_vectors != NUM_PACKED_VECTORS_PER_GROUP_V2
        || params.num_commitments != NUM_PCS_GROUPS_V2
    {
        return Err(FixtureV2Error::Invalid(
            "WHIR sizing requires the canonical grouped-v2 statement shape",
        ));
    }
    if params.initial_merkle_depth != log2_power_of_two(params.initial_codeword_length)? {
        return Err(FixtureV2Error::Invalid(
            "initial WHIR Merkle depth disagrees with its codeword length",
        ));
    }
    if params.initial_interleaving_depth == 0 || params.final_size == 0 {
        return Err(FixtureV2Error::Invalid(
            "WHIR sizing encountered a zero-width vector",
        ));
    }

    let initial_columns = size_mul(
        params.initial_interleaving_depth,
        params.num_vectors,
        "initial WHIR column count",
    )?;
    let mut openings = vec![whir_opening_size_upper_bound_v2(
        params.initial_codeword_length,
        params.initial_merkle_depth,
        params.in_domain_samples,
        initial_columns,
        1,
        params.num_commitments,
    )?];
    for round in &params.rounds {
        if round.merkle_depth != log2_power_of_two(round.codeword_length)? {
            return Err(FixtureV2Error::Invalid(
                "round WHIR Merkle depth disagrees with its codeword length",
            ));
        }
        if round.interleaving_depth == 0 {
            return Err(FixtureV2Error::Invalid(
                "round WHIR interleaving depth is zero",
            ));
        }
        // Native folding-round commitments always contain one extension-field
        // vector, so interleaving depth is also the matrix column count.
        openings.push(whir_opening_size_upper_bound_v2(
            round.codeword_length,
            round.merkle_depth,
            round.in_domain_samples,
            round.interleaving_depth,
            3,
            1,
        )?);
    }

    // Mirror `preflight_grouped_final_fold_impl` exactly. Hashes are 32 bytes,
    // extension-field elements are three canonical little-endian u64 limbs,
    // and an enabled proof-of-work contributes one u64 nonce.
    let batch_size = params.num_vectors;
    let total_vectors = size_mul(
        params.num_commitments,
        batch_size,
        "initial WHIR total vector count",
    )?;
    let mut narg_bytes = size_mul(params.num_commitments, 2 * ROOT_BYTES, "initial WHIR roots")?;
    narg_bytes = size_add(
        narg_bytes,
        size_mul(
            size_mul(
                size_mul(
                    params.num_commitments,
                    params.out_domain_samples,
                    "initial WHIR OOD count",
                )?,
                batch_size,
                "initial WHIR OOD count",
            )?,
            EXT3_BYTES,
            "initial WHIR OOD bytes",
        )?,
        "WHIR NARG length",
    )?;
    narg_bytes = size_add(
        narg_bytes,
        size_mul(
            NUM_PCS_CLAIMS_V2,
            EXT3_BYTES,
            "initial WHIR statement claims",
        )?,
        "WHIR NARG length",
    )?;
    let cross_vectors = total_vectors
        .checked_sub(batch_size)
        .ok_or(FixtureV2Error::Invalid(
            "initial WHIR cross-vector count underflow",
        ))?;
    narg_bytes = size_add(
        narg_bytes,
        size_mul(
            size_mul(
                size_mul(
                    params.num_commitments,
                    params.out_domain_samples,
                    "initial WHIR cross-OOD count",
                )?,
                cross_vectors,
                "initial WHIR cross-OOD count",
            )?,
            EXT3_BYTES,
            "initial WHIR cross-OOD bytes",
        )?,
        "WHIR NARG length",
    )?;
    narg_bytes = size_add(
        narg_bytes,
        sumcheck_narg_bytes(
            params.initial_sumcheck_rounds,
            &params.initial_sumcheck_pow_threshold,
        )?,
        "WHIR NARG length",
    )?;

    for round in &params.rounds {
        narg_bytes = size_add(narg_bytes, ROOT_BYTES, "WHIR NARG length")?;
        narg_bytes = size_add(
            narg_bytes,
            size_mul(round.out_domain_samples, EXT3_BYTES, "round WHIR OOD bytes")?,
            "WHIR NARG length",
        )?;
        narg_bytes = size_add(
            narg_bytes,
            pow_nonce_bytes(&round.pow_threshold)?,
            "WHIR NARG length",
        )?;
        narg_bytes = size_add(
            narg_bytes,
            sumcheck_narg_bytes(round.sumcheck_rounds, &round.sumcheck_pow_threshold)?,
            "WHIR NARG length",
        )?;
    }
    narg_bytes = size_add(
        narg_bytes,
        size_mul(params.final_size, EXT3_BYTES, "final WHIR vector bytes")?,
        "WHIR NARG length",
    )?;
    narg_bytes = size_add(
        narg_bytes,
        pow_nonce_bytes(&params.final_pow_threshold)?,
        "WHIR NARG length",
    )?;
    narg_bytes = size_add(
        narg_bytes,
        sumcheck_narg_bytes(
            params.final_sumcheck_rounds,
            &params.final_sumcheck_pow_threshold,
        )?,
        "WHIR NARG length",
    )?;

    let max_hint_bytes = openings.iter().try_fold(0usize, |total, opening| {
        size_add(total, opening.max_bytes, "WHIR hint upper bound")
    })?;
    let max_total_bytes = size_add(narg_bytes, max_hint_bytes, "WHIR proof upper bound")?;
    Ok(WhirProofSizeUpperBoundV2 {
        packed_num_variables: params.num_variables,
        narg_bytes,
        max_hint_bytes,
        max_total_bytes,
        openings,
    })
}

/// Exact canonical `abi.encode(MleProof)` byte length for the supplied circuit
/// shape and WHIR blob lengths. This is useful for resource probes that do not
/// construct or allocate a proof.
pub fn solidity_abi_mle_proof_encoded_len_v2(
    shape: &CompactV2Shape,
    whir_narg_bytes: usize,
    whir_hint_bytes: usize,
) -> Result<usize, FixtureV2Error> {
    // Run the reviewed compact shape validator first; both wire encodings use
    // the same structural dimensions.
    shape.fixed_encoded_len()?;
    let preprocessed = size_add(
        shape.num_constants,
        shape.num_routed_wires,
        "ABI preprocessed terminal length",
    )?;
    let norm_inverse = size_mul(
        2,
        shape.num_routed_wires,
        "ABI norm-inverse terminal length",
    )?;

    // One top-level offset followed by the sixteen-word MleProof tuple head.
    let mut bytes = size_add(
        ABI_WORD_BYTES,
        size_mul(
            MLE_PROOF_ABI_FIELD_COUNT_V2,
            ABI_WORD_BYTES,
            "MleProof ABI tuple head",
        )?,
        "MleProof ABI length",
    )?;
    for array_len in [shape.circuit_digest_len, shape.public_inputs_len] {
        bytes = size_add(
            bytes,
            abi_base_array_encoded_len(array_len)?,
            "MleProof ABI length",
        )?;
    }
    for blob_len in [whir_narg_bytes, whir_hint_bytes] {
        bytes = size_add(
            bytes,
            abi_bytes_encoded_len(blob_len)?,
            "MleProof ABI length",
        )?;
    }
    bytes = size_add(
        bytes,
        abi_sumcheck_encoded_len(shape.degree_bits, LOG_ROUND_DEGREE_V2)?,
        "MleProof ABI length",
    )?;
    for array_len in [preprocessed, shape.num_wires, norm_inverse] {
        bytes = size_add(
            bytes,
            abi_ext3_array_encoded_len(array_len)?,
            "MleProof ABI length",
        )?;
    }
    bytes = size_add(
        bytes,
        abi_sumcheck_encoded_len(shape.degree_bits, shape.gate_round_degree)?,
        "MleProof ABI length",
    )?;
    for array_len in [preprocessed, shape.num_wires] {
        bytes = size_add(
            bytes,
            abi_ext3_array_encoded_len(array_len)?,
            "MleProof ABI length",
        )?;
    }
    Ok(bytes)
}

/// Derive proof-size maxima for any reviewed compact circuit shape.
pub fn proof_encoding_size_upper_bound_v2(
    shape: &CompactV2Shape,
) -> Result<ProofEncodingSizeUpperBoundV2, FixtureV2Error> {
    proof_encoding_size_upper_bound_at_security_v2(shape, WHIR_SECURITY_LEVEL_V2)
}

fn proof_encoding_size_upper_bound_at_security_v2(
    shape: &CompactV2Shape,
    whir_security_level: usize,
) -> Result<ProofEncodingSizeUpperBoundV2, FixtureV2Error> {
    let fixed_compact_bytes = shape.fixed_encoded_len()?;
    let padded_width =
        shape
            .constituent_width
            .checked_next_power_of_two()
            .ok_or(FixtureV2Error::Invalid(
                "constituent width padding overflow",
            ))?;
    let packed_num_variables = size_add(
        shape.degree_bits,
        padded_width.trailing_zeros() as usize,
        "packed WHIR variable count",
    )?;
    let profile = derive_whir_deployment_profile_for_packed_num_vars_at_security_v2(
        packed_num_variables,
        whir_security_level,
    )?;
    let whir = profile.proof_size_upper_bound;
    let max_compact_bytes = size_add(
        fixed_compact_bytes,
        whir.max_total_bytes,
        "compact proof upper bound",
    )?;
    let max_solidity_abi_bytes =
        solidity_abi_mle_proof_encoded_len_v2(shape, whir.narg_bytes, whir.max_hint_bytes)?;
    let fits_whir_blob_caps = whir.narg_bytes <= shape.max_whir_narg_bytes
        && whir.max_hint_bytes <= shape.max_whir_hint_bytes;
    Ok(ProofEncodingSizeUpperBoundV2 {
        packed_num_variables,
        fixed_compact_bytes,
        max_whir_transcript_bytes: whir.narg_bytes,
        max_whir_hint_bytes: whir.max_hint_bytes,
        max_compact_bytes,
        max_solidity_abi_bytes,
        compact_cap_bytes: shape.max_encoded_bytes,
        fits_whir_blob_caps,
        fits_compact_cap: fits_whir_blob_caps && max_compact_bytes <= shape.max_encoded_bytes,
        whir,
    })
}

fn whir_opening_size_upper_bound_v2(
    codeword_length: usize,
    merkle_depth: usize,
    sample_count: usize,
    num_columns: usize,
    field_limbs: usize,
    num_commitments: usize,
) -> Result<WhirOpeningSizeUpperBoundV2, FixtureV2Error> {
    if num_columns == 0 || field_limbs == 0 || num_commitments == 0 {
        return Err(FixtureV2Error::Invalid(
            "WHIR opening sizing encountered a zero-width shape",
        ));
    }
    if merkle_depth != log2_power_of_two(codeword_length)? {
        return Err(FixtureV2Error::Invalid(
            "WHIR opening Merkle depth disagrees with codeword length",
        ));
    }
    let max_distinct_queries = sample_count.min(codeword_length);
    let revealed_queries = if WHIR_DEDUPLICATE_IN_DOMAIN_V2 {
        max_distinct_queries
    } else {
        sample_count
    };
    let max_field_bytes_per_commitment = size_mul(
        size_mul(
            size_mul(revealed_queries, num_columns, "WHIR opening field count")?,
            field_limbs,
            "WHIR opening limb count",
        )?,
        8,
        "WHIR opening field bytes",
    )?;
    let max_merkle_siblings_per_commitment =
        max_merkle_multiproof_siblings_v2(codeword_length, max_distinct_queries)?;
    let max_bytes_per_commitment = size_add(
        size_add(
            WHIR_HINT_LENGTH_PREFIX_BYTES,
            max_field_bytes_per_commitment,
            "WHIR opening bytes",
        )?,
        size_mul(
            max_merkle_siblings_per_commitment,
            ROOT_BYTES,
            "WHIR opening sibling bytes",
        )?,
        "WHIR opening bytes",
    )?;
    let max_bytes = size_mul(
        max_bytes_per_commitment,
        num_commitments,
        "WHIR opening bytes",
    )?;
    Ok(WhirOpeningSizeUpperBoundV2 {
        codeword_length,
        sample_count,
        max_distinct_queries,
        num_columns,
        field_limbs,
        num_commitments,
        max_field_bytes_per_commitment,
        max_merkle_siblings_per_commitment,
        max_bytes_per_commitment,
        max_bytes,
    })
}

/// Derive the exact Solidity WHIR deployment profile from the canonical Rust
/// PCS constructor, including native protocol/session identifiers and the
/// `keccak256(abi.encode(WhirParams))` profile digest.
pub fn derive_whir_deployment_profile_v2(
    degree_bits: usize,
    constituent_width: usize,
) -> Result<WhirDeploymentProfileV2, FixtureV2Error> {
    derive_whir_deployment_profile_at_security_v2(
        degree_bits,
        constituent_width,
        WHIR_SECURITY_LEVEL_V2,
    )
}

fn derive_whir_deployment_profile_at_security_v2(
    degree_bits: usize,
    constituent_width: usize,
    whir_security_level: usize,
) -> Result<WhirDeploymentProfileV2, FixtureV2Error> {
    if degree_bits == 0
        || degree_bits > MAX_ROW_VARIABLES_V2
        || constituent_width == 0
        || constituent_width > MAX_CONSTITUENT_WIDTH_V2
    {
        return Err(FixtureV2Error::Invalid(
            "WHIR deployment profile dimensions exceed the v2 schema envelope",
        ));
    }
    let num_variables = packed_group_num_vars_v2(degree_bits, constituent_width);
    derive_whir_deployment_profile_for_packed_num_vars_at_security_v2(
        num_variables,
        whir_security_level,
    )
}

/// Derive a canonical profile directly from the packed WHIR dimension.  This
/// is the single production constructor used by the generated on-chain
/// profile table for every supported dimension.
pub fn derive_whir_deployment_profile_for_packed_num_vars_v2(
    num_variables: usize,
) -> Result<WhirDeploymentProfileV2, FixtureV2Error> {
    derive_whir_deployment_profile_for_packed_num_vars_at_security_v2(
        num_variables,
        WHIR_SECURITY_LEVEL_V2,
    )
}

fn derive_whir_deployment_profile_for_packed_num_vars_at_security_v2(
    num_variables: usize,
    whir_security_level: usize,
) -> Result<WhirDeploymentProfileV2, FixtureV2Error> {
    if num_variables == 0 || num_variables > MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2 {
        return Err(FixtureV2Error::Invalid(
            "packed WHIR variable count exceeds the v2 schema envelope",
        ));
    }
    let size = 1usize
        .checked_shl(
            u32::try_from(num_variables)
                .map_err(|_| FixtureV2Error::Invalid("WHIR variable count does not fit u32"))?,
        )
        .ok_or(FixtureV2Error::Invalid("WHIR domain size overflow"))?;
    if whir_security_level != WHIR_SECURITY_LEVEL_V2 {
        return Err(FixtureV2Error::Invalid(
            "only the generated current WHIR security target is derivable",
        ));
    }
    let pcs = WhirPCS::for_constituents(num_variables, NUM_PACKED_VECTORS_PER_GROUP_V2);
    let expected_folding_factor =
        WHIR_FOLDING_FACTOR_V2.min(num_variables.saturating_sub(1).max(1));
    let expected_starting_log_inv_rate = if num_variables <= pcs.params.initial_folding_factor {
        1
    } else {
        WHIR_MAX_STARTING_LOG_INV_RATE_V2.min(num_variables - pcs.params.initial_folding_factor)
    };
    if pcs.params.security_level != whir_security_level
        || pcs.params.pow_bits != WHIR_POW_BITS_V2
        || WHIR_HASH_ID_V2 != "keccak-256"
        || pcs.params.hash_id != whir::hash::KECCAK
        || pcs.params.unique_decoding != WHIR_UNIQUE_DECODING_V2
        || pcs.params.batch_size != NUM_PACKED_VECTORS_PER_GROUP_V2
        || pcs.params.folding_factor != expected_folding_factor
        || pcs.params.starting_log_inv_rate != expected_starting_log_inv_rate
    {
        return Err(FixtureV2Error::Invalid(
            "native WHIR constructor drifted from the generated v2 security profile",
        ));
    }
    let config = pcs.constituent_config(size);
    if config.initial_committer.deduplicate_in_domain != WHIR_DEDUPLICATE_IN_DOMAIN_V2
        || config
            .round_configs
            .iter()
            .any(|round| round.irs_committer.deduplicate_in_domain != WHIR_DEDUPLICATE_IN_DOMAIN_V2)
    {
        return Err(FixtureV2Error::Invalid(
            "native WHIR domain deduplication drifted from the v2 schema",
        ));
    }
    let mut remaining_variables = num_variables
        .checked_sub(pcs.params.initial_folding_factor)
        .ok_or(FixtureV2Error::Invalid(
            "invalid WHIR initial folding factor",
        ))?;
    for _ in &config.round_configs {
        remaining_variables = remaining_variables.saturating_sub(pcs.params.folding_factor);
    }
    let initial_codeword_length = config.initial_committer.codeword_length;
    let initial_coset_size = whir_coset_size(
        initial_codeword_length,
        config.initial_committer.masked_message_length(),
    )?;
    let rounds = config
        .round_configs
        .iter()
        .map(|round| {
            let codeword_length = round.irs_committer.codeword_length;
            let coset_size =
                whir_coset_size(codeword_length, round.irs_committer.masked_message_length())?;
            Ok(WhirRoundParamsFixture {
                codeword_length,
                merkle_depth: log2_power_of_two(codeword_length)?,
                domain_generator: goldilocks_root_of_unity(codeword_length)?.to_string(),
                in_domain_samples: round.irs_committer.in_domain_samples,
                out_domain_samples: round.irs_committer.out_domain_samples,
                sumcheck_rounds: round.sumcheck.num_rounds,
                interleaving_depth: round.irs_committer.interleaving_depth,
                coset_size,
                num_cosets: codeword_length / coset_size,
                num_variables: round.initial_num_variables(),
                pow_threshold: round.pow.threshold.to_string(),
                sumcheck_pow_threshold: round.sumcheck.round_pow.threshold.to_string(),
            })
        })
        .collect::<Result<Vec<_>, FixtureV2Error>>()?;
    let without_points = WhirParamsFixture {
        num_variables,
        folding_factor: pcs.params.folding_factor,
        num_vectors: pcs.params.batch_size,
        num_commitments: NUM_PCS_GROUPS_V2,
        out_domain_samples: config.initial_committer.out_domain_samples,
        in_domain_samples: config.initial_committer.in_domain_samples,
        initial_sumcheck_rounds: config.initial_sumcheck.num_rounds,
        num_rounds: config.round_configs.len(),
        final_sumcheck_rounds: config.final_sumcheck.num_rounds,
        final_size: 1usize
            .checked_shl(u32::try_from(remaining_variables).map_err(|_| {
                FixtureV2Error::Invalid("WHIR final variable count does not fit u32")
            })?)
            .ok_or(FixtureV2Error::Invalid("WHIR final size overflow"))?,
        initial_codeword_length,
        initial_merkle_depth: log2_power_of_two(initial_codeword_length)?,
        initial_domain_generator: goldilocks_root_of_unity(initial_codeword_length)?.to_string(),
        initial_interleaving_depth: config.initial_committer.interleaving_depth,
        initial_num_variables: config.initial_num_variables(),
        initial_coset_size,
        initial_num_cosets: initial_codeword_length / initial_coset_size,
        initial_sumcheck_pow_threshold: config.initial_sumcheck.round_pow.threshold.to_string(),
        final_pow_threshold: config.final_pow.threshold.to_string(),
        final_sumcheck_pow_threshold: config.final_sumcheck.round_pow.threshold.to_string(),
        rounds,
    };
    let params = WhirParamsV2Fixture::from_without_points(without_points);
    let proof_size_upper_bound = whir_proof_size_upper_bound_v2(&params)?;
    let abi = solidity_abi_encode_whir_params_v2(&params)?;
    Ok(WhirDeploymentProfileV2 {
        params,
        protocol_id: pcs.constituent_protocol_id(size),
        session_id: whir_session_id(WHIR_SESSION_SPLIT_V2),
        parameters_digest: Keccak256::digest(abi).into(),
        proof_size_upper_bound,
    })
}

/// Exact `abi.encode(WhirParams)` implementation for the canonical empty-point
/// deployment profile.
pub fn solidity_abi_encode_whir_params_v2(
    params: &WhirParamsV2Fixture,
) -> Result<Vec<u8>, FixtureV2Error> {
    params.require_empty_points()?;
    let mut encoded = Vec::with_capacity(928 + 384 * params.rounds.len());
    push_abi_usize(&mut encoded, 0x20, "top-level WHIR tuple offset")?;
    for value in [
        params.num_variables,
        params.folding_factor,
        params.num_vectors,
        params.num_commitments,
        params.out_domain_samples,
        params.in_domain_samples,
        params.initial_sumcheck_rounds,
        params.num_rounds,
        params.final_sumcheck_rounds,
        params.final_size,
        params.initial_codeword_length,
        params.initial_merkle_depth,
    ] {
        push_abi_usize(&mut encoded, value, "WHIR scalar")?;
    }
    push_abi_decimal(
        &mut encoded,
        &params.initial_domain_generator,
        "initialDomainGenerator",
    )?;
    for value in [
        params.initial_interleaving_depth,
        params.initial_num_variables,
        params.initial_coset_size,
        params.initial_num_cosets,
    ] {
        push_abi_usize(&mut encoded, value, "WHIR scalar")?;
    }
    push_abi_decimal(
        &mut encoded,
        &params.initial_sumcheck_pow_threshold,
        "initialSumcheckPowThreshold",
    )?;
    push_abi_decimal(
        &mut encoded,
        &params.final_pow_threshold,
        "finalPowThreshold",
    )?;
    push_abi_decimal(
        &mut encoded,
        &params.final_sumcheck_pow_threshold,
        "finalSumcheckPowThreshold",
    )?;
    for offset in [0x300usize, 0x320, 0x340, 0x360] {
        push_abi_usize(&mut encoded, offset, "WHIR dynamic offset")?;
    }
    for _ in 0..3 {
        push_abi_usize(&mut encoded, 0, "empty WHIR point array")?;
    }
    push_abi_usize(&mut encoded, params.rounds.len(), "WHIR round count")?;
    for round in &params.rounds {
        for value in [round.codeword_length, round.merkle_depth] {
            push_abi_usize(&mut encoded, value, "WHIR round scalar")?;
        }
        push_abi_decimal(
            &mut encoded,
            &round.domain_generator,
            "round.domainGenerator",
        )?;
        for value in [
            round.in_domain_samples,
            round.out_domain_samples,
            round.sumcheck_rounds,
            round.interleaving_depth,
            round.coset_size,
            round.num_cosets,
            round.num_variables,
        ] {
            push_abi_usize(&mut encoded, value, "WHIR round scalar")?;
        }
        push_abi_decimal(&mut encoded, &round.pow_threshold, "round.powThreshold")?;
        push_abi_decimal(
            &mut encoded,
            &round.sumcheck_pow_threshold,
            "round.sumcheckPowThreshold",
        )?;
    }
    let expected = 928usize
        .checked_add(
            384usize
                .checked_mul(params.rounds.len())
                .ok_or(FixtureV2Error::Invalid("WHIR ABI encoded length overflow"))?,
        )
        .ok_or(FixtureV2Error::Invalid("WHIR ABI encoded length overflow"))?;
    if encoded.len() != expected {
        return Err(FixtureV2Error::Invalid(
            "internal WHIR ABI layout length mismatch",
        ));
    }
    Ok(encoded)
}

/// Exact `abi.encode(MleVerifierV2.VerificationConfig)` bytes. The nested
/// `WhirParams` payload is produced by [`solidity_abi_encode_whir_params_v2`]
/// and embedded as a dynamic tuple without reconstructing any field.
pub fn solidity_abi_encode_verification_config_v2(
    config: &MleVerificationConfigV2Fixture,
) -> Result<Vec<u8>, FixtureV2Error> {
    config.whir.require_empty_points()?;
    let circuit = &config.circuit;
    let mut head = Vec::with_capacity(13 * ABI_WORD_BYTES);
    for value in [
        circuit.degree_bits,
        circuit.num_public_inputs,
        circuit.num_constants,
        circuit.num_routed_wires,
        circuit.num_wires,
        circuit.num_selectors,
        circuit.num_gate_constraints,
        circuit.quotient_degree_factor,
    ] {
        head.extend_from_slice(&abi_word_usize(
            value,
            "verification-config circuit scalar",
        )?);
    }

    let whir_abi = solidity_abi_encode_whir_params_v2(&config.whir)?;
    let whir_tuple = whir_abi
        .get(ABI_WORD_BYTES..)
        .ok_or(FixtureV2Error::Invalid(
            "canonical WHIR ABI payload is missing its top-level offset",
        ))?
        .to_vec();
    let dynamic = [
        abi_bytes(&decode_hex(
            &config.public_input_wire_map,
            "verificationConfig.publicInputWireMap",
        )?)?,
        abi_base_array(&config.k_is, "verificationConfig.kIs")?,
        abi_base_array(
            &config.subgroup_gen_powers,
            "verificationConfig.subgroupGenPowers",
        )?,
        abi_gate_info_array(&config.gates)?,
        whir_tuple,
    ];
    let head_len = 13 * ABI_WORD_BYTES;
    let mut tail = Vec::new();
    for value in dynamic {
        let offset = size_add(head_len, tail.len(), "verification-config ABI offset")?;
        head.extend_from_slice(&abi_word_usize(offset, "verification-config ABI offset")?);
        tail.extend_from_slice(&value);
    }
    if head.len() != head_len {
        return Err(FixtureV2Error::Invalid(
            "verification-config ABI head length mismatch",
        ));
    }
    head.extend_from_slice(&tail);
    let mut encoded = Vec::with_capacity(ABI_WORD_BYTES + head.len());
    encoded.extend_from_slice(&abi_word_u64(ABI_WORD_BYTES as u64));
    encoded.extend_from_slice(&head);
    Ok(encoded)
}

/// Exact canonical `abi.encode(MleVerifierV2.MleProof)` bytes.
pub fn solidity_abi_encode_mle_proof_v2(
    proof: &MleProofV2Fixture,
) -> Result<Vec<u8>, FixtureV2Error> {
    proof.validate_abi_keys()?;
    let dynamic = |bytes: Vec<u8>| AbiField::Dynamic(bytes);
    let fields = vec![
        AbiField::Static(abi_word_u64(proof.protocol_version)),
        AbiField::Static(abi_word_usize(proof.constituent_width, "constituentWidth")?),
        dynamic(abi_base_array(&proof.circuit_digest, "circuitDigest")?),
        dynamic(abi_base_array(&proof.public_inputs, "publicInputs")?),
        AbiField::Static(decode_fixed_hex::<32>(
            &proof.preprocessed_root,
            "preprocessedRoot",
        )?),
        AbiField::Static(decode_fixed_hex::<32>(&proof.witness_root, "witnessRoot")?),
        AbiField::Static(decode_fixed_hex::<32>(
            &proof.norm_inverse_root,
            "normInverseRoot",
        )?),
        dynamic(abi_bytes(&decode_hex(
            &proof.whir_transcript,
            "whirTranscript",
        )?)?),
        dynamic(abi_bytes(&decode_hex(&proof.whir_hints, "whirHints")?)?),
        dynamic(abi_sumcheck(&proof.log_proof, "logProof")?),
        dynamic(abi_ext3_array(&proof.log_preprocessed, "logPreprocessed")?),
        dynamic(abi_ext3_array(&proof.log_witness, "logWitness")?),
        dynamic(abi_ext3_array(&proof.log_norm_inverse, "logNormInverse")?),
        dynamic(abi_sumcheck(&proof.gate_proof, "gateProof")?),
        dynamic(abi_ext3_array(
            &proof.gate_preprocessed,
            "gatePreprocessed",
        )?),
        dynamic(abi_ext3_array(&proof.gate_witness, "gateWitness")?),
    ];
    if fields.len() != MLE_PROOF_ABI_FIELD_COUNT_V2 {
        return Err(FixtureV2Error::Invalid(
            "internal Solidity proof ABI field count mismatch",
        ));
    }
    let tuple = abi_tuple(fields)?;
    let mut encoded = Vec::with_capacity(32 + tuple.len());
    encoded.extend_from_slice(&abi_word_u64(32));
    encoded.extend_from_slice(&tuple);
    Ok(encoded)
}

fn verification_config_v2<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    vk: &MleVerificationKeyV2<F>,
) -> Result<MleVerificationConfigV2Fixture, FixtureV2Error> {
    if vk.num_constants != common_data.num_constants
        || vk.num_routed_wires != common_data.config.num_routed_wires
        || vk.num_wires != common_data.config.num_wires
        || vk.num_selectors != common_data.selectors_info.num_selectors()
        || vk.num_gate_constraints != common_data.num_gate_constraints
        || vk.quotient_degree_factor != common_data.quotient_degree_factor
        || vk.k_is != common_data.k_is
    {
        return Err(FixtureV2Error::Invalid(
            "VK circuit configuration disagrees with common data",
        ));
    }
    let profile =
        derive_whir_deployment_profile_v2(common_data.degree_bits(), vk.constituent_width)?;
    Ok(MleVerificationConfigV2Fixture {
        circuit: CircuitParametersV2Fixture {
            degree_bits: common_data.degree_bits(),
            num_public_inputs: common_data.num_public_inputs,
            num_constants: common_data.num_constants,
            num_routed_wires: common_data.config.num_routed_wires,
            num_wires: common_data.config.num_wires,
            num_selectors: common_data.selectors_info.num_selectors(),
            num_gate_constraints: common_data.num_gate_constraints,
            quotient_degree_factor: common_data.quotient_degree_factor,
        },
        public_input_wire_map: encode_hex(&vk.public_input_wire_map),
        k_is: encode_base_vec(&vk.k_is),
        subgroup_gen_powers: encode_base_vec(&vk.subgroup_gen_powers),
        gates: vk.gates.iter().copied().map(Into::into).collect(),
        whir: profile.params,
    })
}

fn validate_config_fixture_against_common<F: RichField + Extendable<D>, const D: usize>(
    fixture: &MleVerifierV2ConfigFixture,
    common_data: &CommonCircuitData<F, D>,
) -> Result<MleVerificationKeyV2<F>, FixtureV2Error> {
    let vk = fixture.verification_key.try_decode::<F>()?;
    validate_config_fixture_against_common_and_vk(fixture, common_data, &vk)?;
    Ok(vk)
}

fn validate_config_fixture_against_common_and_vk<F: RichField + Extendable<D>, const D: usize>(
    fixture: &MleVerifierV2ConfigFixture,
    common_data: &CommonCircuitData<F, D>,
    expected_vk: &MleVerificationKeyV2<F>,
) -> Result<(), FixtureV2Error> {
    require_config_header(fixture)?;
    if fixture.verification_key != MleVerificationKeyV2Fixture::encode(expected_vk) {
        return Err(FixtureV2Error::Invalid(
            "serialized verification key differs from the circuit-derived MLE v2 VK",
        ));
    }
    validate_config_pinned_views(fixture)?;

    let expected_config = verification_config_v2(common_data, expected_vk)?;
    if fixture.verification_config != expected_config {
        return Err(FixtureV2Error::Invalid(
            "serialized verification config drifted from common data/VK",
        ));
    }
    let expected_config_abi = solidity_abi_encode_verification_config_v2(&expected_config)?;
    let actual_config_abi = fixture
        .solidity_abi_verification_config
        .decode_and_validate(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2)?;
    if actual_config_abi != expected_config_abi {
        return Err(FixtureV2Error::Invalid(
            "recorded Solidity verification-config ABI bytes are not canonical",
        ));
    }

    let expected_shape = compact_v2_shape_for_common(common_data, expected_vk.constituent_width)?;
    if fixture.compact_shape.decode() != expected_shape {
        return Err(FixtureV2Error::Invalid(
            "serialized compact shape drifted from common data/schema caps",
        ));
    }
    let expected_upper_bound = proof_encoding_size_upper_bound_v2(&expected_shape)?;
    if fixture.size_upper_bound != expected_upper_bound {
        return Err(FixtureV2Error::Invalid(
            "serialized proof-size upper bound drifted from native WHIR/circuit parameters",
        ));
    }
    require_deployable_size_upper_bound(&expected_upper_bound)?;
    validate_config_whir_profile(
        fixture,
        common_data.degree_bits(),
        expected_vk.constituent_width,
    )?;
    Ok(())
}

fn validate_config_whir_profile(
    fixture: &MleVerifierV2ConfigFixture,
    degree_bits: usize,
    width: usize,
) -> Result<(), FixtureV2Error> {
    validate_config_whir_profile_at_security(fixture, degree_bits, width, WHIR_SECURITY_LEVEL_V2)
}

fn validate_config_whir_profile_at_security(
    fixture: &MleVerifierV2ConfigFixture,
    degree_bits: usize,
    width: usize,
    whir_security_level: usize,
) -> Result<(), FixtureV2Error> {
    let profile =
        derive_whir_deployment_profile_at_security_v2(degree_bits, width, whir_security_level)?;
    if fixture.verification_config.whir != profile.params
        || fixture.verification_key.whir_protocol_id != encode_hex(&profile.protocol_id)
        || fixture.verification_key.whir_session_id != encode_hex(&profile.session_id)
        || fixture.pinned_verifier.whir_parameters_digest != encode_hex(&profile.parameters_digest)
        || fixture.size_upper_bound.whir != profile.proof_size_upper_bound
    {
        return Err(FixtureV2Error::Invalid(
            "config fixture WHIR profile, sizing, or pinned identifiers drifted",
        ));
    }
    Ok(())
}

fn require_config_header(fixture: &MleVerifierV2ConfigFixture) -> Result<(), FixtureV2Error> {
    if fixture.schema != MLE_VERIFIER_CONFIG_FIXTURE_SCHEMA_V2
        || fixture.schema_version != SCHEMA_VERSION_CURRENT
        || fixture.protocol_version != MLE_PROTOCOL_VERSION_CURRENT
        || fixture.verification_key.protocol_version != MLE_PROTOCOL_VERSION_CURRENT
        || fixture.proof_abi_signature != MLE_PROOF_ABI_SIGNATURE_V2
        || fixture.proof_layout_hash != encode_hex(&MLE_PROOF_LAYOUT_HASH_V2)
        || fixture.compact_layout_hash != encode_hex(&COMPACT_LAYOUT_HASH_V2)
        || fixture.compact_proof_encoding
            != std::str::from_utf8(&COMPACT_MAGIC_V2).expect("compact-v2 magic is ASCII")
        || fixture.whir_pow_bits != WHIR_POW_BITS_V2
    {
        return Err(FixtureV2Error::Invalid(
            "config fixture header/schema/proof/compact/WHIR identity mismatch",
        ));
    }
    Ok(())
}

fn validate_config_pinned_views(
    fixture: &MleVerifierV2ConfigFixture,
) -> Result<(), FixtureV2Error> {
    let vk = &fixture.verification_key;
    if fixture.pinned_verifier.preprocessed_commitment_root != vk.preprocessed_commitment_root
        || fixture.pinned_verifier.circuit_config_digest != vk.circuit_config_digest
        || fixture.pinned_verifier.verification_config_digest
            != fixture.solidity_abi_verification_config.keccak256
        || fixture.pinned_verifier.whir_protocol_id != vk.whir_protocol_id
        || fixture.pinned_verifier.whir_session_id != vk.whir_session_id
        || fixture.pinned_verifier.circuit_digest.as_slice() != vk.circuit_digest
    {
        return Err(FixtureV2Error::Invalid(
            "config fixture VK/pinned-verifier views disagree",
        ));
    }
    Ok(())
}

fn require_header(fixture: &MleVerifierV2Fixture) -> Result<(), FixtureV2Error> {
    if fixture.schema != MLE_VERIFIER_FIXTURE_SCHEMA_V2
        || fixture.schema_version != SCHEMA_VERSION_CURRENT
        || fixture.protocol_version != MLE_PROTOCOL_VERSION_CURRENT
        || fixture.proof.protocol_version != MLE_PROTOCOL_VERSION_CURRENT
        || fixture.verification_key.protocol_version != MLE_PROTOCOL_VERSION_CURRENT
        || fixture.proof_abi_signature != MLE_PROOF_ABI_SIGNATURE_V2
        || fixture.proof_layout_hash != encode_hex(&MLE_PROOF_LAYOUT_HASH_V2)
    {
        return Err(FixtureV2Error::Invalid(
            "fixture header/schema/proof ABI identity mismatch",
        ));
    }
    Ok(())
}

fn validate_pinned_views(fixture: &MleVerifierV2Fixture) -> Result<(), FixtureV2Error> {
    let vk = &fixture.verification_key;
    let proof = &fixture.proof;
    if fixture.pinned_verifier.preprocessed_commitment_root != vk.preprocessed_commitment_root
        || proof.preprocessed_root != vk.preprocessed_commitment_root
        || fixture.pinned_verifier.circuit_config_digest != vk.circuit_config_digest
        || fixture.pinned_verifier.verification_config_digest
            != fixture.solidity_abi_verification_config.keccak256
        || fixture.pinned_verifier.whir_protocol_id != vk.whir_protocol_id
        || fixture.pinned_verifier.whir_session_id != vk.whir_session_id
        || fixture.pinned_verifier.circuit_digest.as_slice() != vk.circuit_digest
        || proof.circuit_digest != vk.circuit_digest
    {
        return Err(FixtureV2Error::Invalid(
            "proof/VK/pinned-verifier views disagree",
        ));
    }
    Ok(())
}

fn validate_stats<F: Field + PrimeField64>(
    fixture: &MleVerifierV2Fixture,
    proof: &MleProofV2<F>,
    compact: &[u8],
    solidity_abi: &[u8],
    solidity_abi_verification_config: &[u8],
) -> Result<(), FixtureV2Error> {
    let expected = ProofEncodingStatsV2Fixture {
        solidity_abi_bytes: solidity_abi.len(),
        solidity_abi_verification_config_bytes: solidity_abi_verification_config.len(),
        compact_bytes: compact.len(),
        whir_transcript_bytes: proof.whir_eval_proof.narg_string.len(),
        whir_hint_bytes: proof.whir_eval_proof.hints.len(),
    };
    if fixture.stats != expected {
        return Err(FixtureV2Error::Invalid("v2 proof encoding stats drifted"));
    }
    let shape = fixture.compact_shape.decode();
    let upper_bound = proof_encoding_size_upper_bound_v2(&shape)?;
    if fixture.size_upper_bound != upper_bound {
        return Err(FixtureV2Error::Invalid("v2 proof-size upper bound drifted"));
    }
    require_deployable_size_upper_bound(&upper_bound)?;
    if proof.whir_eval_proof.narg_string.len() != upper_bound.max_whir_transcript_bytes {
        return Err(FixtureV2Error::Invalid(
            "WHIR NARG length disagrees with the canonical native grammar",
        ));
    }
    if proof.whir_eval_proof.hints.len() > upper_bound.max_whir_hint_bytes
        || compact.len() > upper_bound.max_compact_bytes
        || solidity_abi.len() > upper_bound.max_solidity_abi_bytes
    {
        return Err(FixtureV2Error::Invalid(
            "proof encoding exceeds its deterministic size upper bound",
        ));
    }
    let expected_compact_len = size_add(
        upper_bound.fixed_compact_bytes,
        size_add(
            proof.whir_eval_proof.narg_string.len(),
            proof.whir_eval_proof.hints.len(),
            "actual WHIR proof bytes",
        )?,
        "actual compact proof bytes",
    )?;
    if compact.len() != expected_compact_len {
        return Err(FixtureV2Error::Invalid(
            "compact proof length disagrees with its canonical grammar",
        ));
    }
    let expected_abi_len = solidity_abi_mle_proof_encoded_len_v2(
        &shape,
        proof.whir_eval_proof.narg_string.len(),
        proof.whir_eval_proof.hints.len(),
    )?;
    if solidity_abi.len() != expected_abi_len {
        return Err(FixtureV2Error::Invalid(
            "Solidity proof ABI length disagrees with its canonical grammar",
        ));
    }
    Ok(())
}

fn require_deployable_size_upper_bound(
    upper_bound: &ProofEncodingSizeUpperBoundV2,
) -> Result<(), FixtureV2Error> {
    if !upper_bound.fits_whir_blob_caps {
        return Err(FixtureV2Error::Invalid(
            "canonical WHIR proof upper bound exceeds a schema blob cap",
        ));
    }
    if !upper_bound.fits_compact_cap {
        return Err(FixtureV2Error::Invalid(
            "canonical compact proof upper bound exceeds the DA schema cap",
        ));
    }
    Ok(())
}

fn size_add(left: usize, right: usize, label: &str) -> Result<usize, FixtureV2Error> {
    left.checked_add(right)
        .ok_or_else(|| FixtureV2Error::InvalidOwned(format!("{label} overflow")))
}

fn size_mul(left: usize, right: usize, label: &str) -> Result<usize, FixtureV2Error> {
    left.checked_mul(right)
        .ok_or_else(|| FixtureV2Error::InvalidOwned(format!("{label} overflow")))
}

fn parse_decimal_u64(value: &str, field: &str) -> Result<u64, FixtureV2Error> {
    let parsed = value.parse::<u64>().map_err(|error| {
        FixtureV2Error::InvalidOwned(format!("{field} is not canonical decimal u64: {error}"))
    })?;
    if parsed.to_string() != value {
        return Err(FixtureV2Error::InvalidOwned(format!(
            "{field} is not minimal decimal u64"
        )));
    }
    Ok(parsed)
}

fn pow_nonce_bytes(threshold: &str) -> Result<usize, FixtureV2Error> {
    Ok(usize::from(parse_decimal_u64(threshold, "WHIR PoW threshold")? != u64::MAX) * 8)
}

fn sumcheck_narg_bytes(rounds: usize, pow_threshold: &str) -> Result<usize, FixtureV2Error> {
    size_mul(
        rounds,
        size_add(
            2 * EXT3_BYTES,
            pow_nonce_bytes(pow_threshold)?,
            "WHIR sumcheck round bytes",
        )?,
        "WHIR sumcheck bytes",
    )
}

fn abi_base_array_encoded_len(elements: usize) -> Result<usize, FixtureV2Error> {
    size_add(
        ABI_WORD_BYTES,
        size_mul(elements, ABI_WORD_BYTES, "ABI base-array bytes")?,
        "ABI base-array bytes",
    )
}

fn abi_ext3_array_encoded_len(elements: usize) -> Result<usize, FixtureV2Error> {
    size_add(
        ABI_WORD_BYTES,
        size_mul(elements, 3 * ABI_WORD_BYTES, "ABI Ext3-array bytes")?,
        "ABI Ext3-array bytes",
    )
}

fn abi_sumcheck_encoded_len(rounds: usize, round_degree: usize) -> Result<usize, FixtureV2Error> {
    // Sumcheck tuple offset + dynamic-array length, followed by one array
    // offset, one CoefficientRound tuple offset, one Ext3[] length, and the
    // coefficient words for every round.
    let per_round = size_mul(
        3 * ABI_WORD_BYTES,
        size_add(round_degree, 1, "ABI sumcheck round degree")?,
        "ABI sumcheck round bytes",
    )?;
    size_add(
        2 * ABI_WORD_BYTES,
        size_mul(rounds, per_round, "ABI sumcheck bytes")?,
        "ABI sumcheck bytes",
    )
}

fn abi_bytes_encoded_len(bytes: usize) -> Result<usize, FixtureV2Error> {
    let padded =
        size_add(bytes, ABI_WORD_BYTES - 1, "ABI bytes padding")? / ABI_WORD_BYTES * ABI_WORD_BYTES;
    size_add(ABI_WORD_BYTES, padded, "ABI dynamic bytes")
}

fn whir_coset_size(
    codeword_length: usize,
    masked_message_length: usize,
) -> Result<usize, FixtureV2Error> {
    if codeword_length == 0 || masked_message_length == 0 {
        return Err(FixtureV2Error::Invalid(
            "invalid zero WHIR domain dimension",
        ));
    }
    let mut coset_size = masked_message_length
        .checked_next_power_of_two()
        .ok_or(FixtureV2Error::Invalid("WHIR coset size overflow"))?;
    while codeword_length % coset_size != 0 {
        coset_size = coset_size
            .checked_mul(2)
            .ok_or(FixtureV2Error::Invalid("WHIR coset size overflow"))?;
        if coset_size > codeword_length {
            return Err(FixtureV2Error::Invalid(
                "WHIR codeword length has no compatible coset size",
            ));
        }
    }
    Ok(coset_size)
}

fn log2_power_of_two(value: usize) -> Result<usize, FixtureV2Error> {
    if !value.is_power_of_two() {
        return Err(FixtureV2Error::Invalid(
            "WHIR codeword length is not a power of two",
        ));
    }
    Ok(value.trailing_zeros() as usize)
}

fn goldilocks_root_of_unity(size: usize) -> Result<u64, FixtureV2Error> {
    ArkGoldilocks::get_root_of_unity(
        u64::try_from(size).map_err(|_| FixtureV2Error::Invalid("WHIR domain does not fit u64"))?,
    )
    .map(|value| value.into_bigint().0[0])
    .ok_or(FixtureV2Error::Invalid(
        "Goldilocks field has no root for the WHIR domain",
    ))
}

fn encode_base<F: PrimeField64>(value: &F) -> String {
    format!("0x{:016x}", value.to_canonical_u64())
}

fn encode_base_vec<F: PrimeField64>(values: &[F]) -> Vec<String> {
    values.iter().map(encode_base).collect()
}

fn encode_circuit_digest<F: PrimeField64>(
    values: &[F],
) -> Result<[String; CIRCUIT_DIGEST_LENGTH_V2], FixtureV2Error> {
    values
        .iter()
        .map(encode_base)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|values: Vec<String>| {
            FixtureV2Error::InvalidOwned(format!(
                "circuit digest has {} limbs; expected {CIRCUIT_DIGEST_LENGTH_V2}",
                values.len()
            ))
        })
}

fn encode_ext3(value: &Field64_3) -> Ext3V2Fixture {
    Ext3V2Fixture {
        c0: format!("0x{:016x}", value.c0.into_bigint().0[0]),
        c1: format!("0x{:016x}", value.c1.into_bigint().0[0]),
        c2: format!("0x{:016x}", value.c2.into_bigint().0[0]),
    }
}

fn encode_ext3_vec(values: &[Field64_3]) -> Vec<Ext3V2Fixture> {
    values.iter().map(encode_ext3).collect()
}

fn decode_base<F: Field + PrimeField64>(value: &str, field: &str) -> Result<F, FixtureV2Error> {
    Ok(F::from_canonical_u64(decode_limb(value, field)?))
}

fn decode_base_vec<F: Field + PrimeField64>(
    values: &[String],
    field: &str,
) -> Result<Vec<F>, FixtureV2Error> {
    values
        .iter()
        .map(|value| decode_base(value, field))
        .collect()
}

fn decode_limb(value: &str, field: &str) -> Result<u64, FixtureV2Error> {
    let digits = value
        .strip_prefix("0x")
        .ok_or_else(|| FixtureV2Error::InvalidOwned(format!("{field} is missing its 0x prefix")))?;
    if digits.len() != 16
        || !digits
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(FixtureV2Error::InvalidOwned(format!(
            "{field} is not canonical fixed-width lowercase u64 hex"
        )));
    }
    let limb = u64::from_str_radix(digits, 16)
        .map_err(|error| FixtureV2Error::InvalidOwned(format!("{field} is not a u64: {error}")))?;
    if limb >= BASE_FIELD_MODULUS_V2 {
        return Err(FixtureV2Error::InvalidOwned(format!(
            "{field} contains a non-canonical Goldilocks limb"
        )));
    }
    Ok(limb)
}

fn encode_hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(2 + 2 * bytes.len());
    encoded.push_str("0x");
    for byte in bytes {
        write!(&mut encoded, "{byte:02x}").unwrap();
    }
    encoded
}

fn decode_hex(value: &str, field: &str) -> Result<Vec<u8>, FixtureV2Error> {
    let digits = value
        .strip_prefix("0x")
        .ok_or_else(|| FixtureV2Error::InvalidOwned(format!("{field} is missing its 0x prefix")))?;
    if digits.len() % 2 != 0
        || !digits
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(FixtureV2Error::InvalidOwned(format!(
            "{field} is not canonical lowercase byte hex"
        )));
    }
    (0..digits.len())
        .step_by(2)
        .map(|index| {
            u8::from_str_radix(&digits[index..index + 2], 16).map_err(|error| {
                FixtureV2Error::InvalidOwned(format!("{field} contains invalid hex: {error}"))
            })
        })
        .collect()
}

fn decode_fixed_hex<const N: usize>(value: &str, field: &str) -> Result<[u8; N], FixtureV2Error> {
    let bytes = decode_hex(value, field)?;
    bytes.try_into().map_err(|bytes: Vec<u8>| {
        FixtureV2Error::InvalidOwned(format!("{field} has {} bytes; expected {N}", bytes.len()))
    })
}

fn decode_fixed_hex_vec(
    value: &str,
    expected: usize,
    field: &str,
) -> Result<Vec<u8>, FixtureV2Error> {
    let bytes = decode_hex(value, field)?;
    if bytes.len() != expected {
        return Err(FixtureV2Error::InvalidOwned(format!(
            "{field} has {} bytes; expected {expected}",
            bytes.len()
        )));
    }
    Ok(bytes)
}

fn require_goldilocks<F: PrimeField64>() -> Result<(), FixtureV2Error> {
    if F::ORDER != BASE_FIELD_MODULUS_V2 {
        return Err(FixtureV2Error::Invalid(
            "MLE/WHIR v2 fixtures require the Goldilocks base field",
        ));
    }
    Ok(())
}

enum AbiField {
    Static([u8; 32]),
    Dynamic(Vec<u8>),
}

fn abi_tuple(fields: Vec<AbiField>) -> Result<Vec<u8>, FixtureV2Error> {
    let head_len = 32usize
        .checked_mul(fields.len())
        .ok_or(FixtureV2Error::Invalid("ABI tuple head length overflow"))?;
    let mut head = Vec::with_capacity(head_len);
    let mut tail = Vec::new();
    for field in fields {
        match field {
            AbiField::Static(word) => head.extend_from_slice(&word),
            AbiField::Dynamic(value) => {
                let offset = head_len
                    .checked_add(tail.len())
                    .ok_or(FixtureV2Error::Invalid("ABI tuple offset overflow"))?;
                head.extend_from_slice(&abi_word_usize(offset, "ABI tuple offset")?);
                tail.extend_from_slice(&value);
            }
        }
    }
    head.extend_from_slice(&tail);
    Ok(head)
}

fn abi_base_array(values: &[String], field: &str) -> Result<Vec<u8>, FixtureV2Error> {
    let mut encoded = Vec::with_capacity(32 + 32 * values.len());
    encoded.extend_from_slice(&abi_word_usize(values.len(), "ABI base-array length")?);
    for value in values {
        encoded.extend_from_slice(&abi_word_u64(decode_limb(value, field)?));
    }
    Ok(encoded)
}

fn abi_ext3_array(values: &[Ext3V2Fixture], field: &str) -> Result<Vec<u8>, FixtureV2Error> {
    let capacity = 32usize
        .checked_add(
            96usize
                .checked_mul(values.len())
                .ok_or(FixtureV2Error::Invalid("ABI Ext3-array length overflow"))?,
        )
        .ok_or(FixtureV2Error::Invalid("ABI Ext3-array length overflow"))?;
    let mut encoded = Vec::with_capacity(capacity);
    encoded.extend_from_slice(&abi_word_usize(values.len(), "ABI Ext3-array length")?);
    for value in values {
        for limb in [&value.c0, &value.c1, &value.c2] {
            encoded.extend_from_slice(&abi_word_u64(decode_limb(limb, field)?));
        }
    }
    Ok(encoded)
}

fn abi_gate_info_array(values: &[GateInfoV2Fixture]) -> Result<Vec<u8>, FixtureV2Error> {
    let mut encoded = Vec::with_capacity(size_add(
        ABI_WORD_BYTES,
        size_mul(
            values.len(),
            9 * ABI_WORD_BYTES,
            "ABI gate-info array bytes",
        )?,
        "ABI gate-info array bytes",
    )?);
    encoded.extend_from_slice(&abi_word_usize(values.len(), "ABI gate-info array length")?);
    for gate in values {
        for value in [
            u64::from(gate.gate_id),
            u64::from(gate.selector_index),
            u64::from(gate.group_start),
            u64::from(gate.group_end),
            u64::from(gate.gate_row_index),
            u64::from(gate.num_constraints),
            u64::from(gate.num_or_consts),
            u64::from(gate.param2),
            u64::from(gate.param3),
        ] {
            encoded.extend_from_slice(&abi_word_u64(value));
        }
    }
    Ok(encoded)
}

fn abi_sumcheck(
    proof: &SumcheckProofV2Fixture,
    field: &'static str,
) -> Result<Vec<u8>, FixtureV2Error> {
    let rounds = proof
        .rounds
        .iter()
        .map(|round| {
            // CoefficientRound is a one-field dynamic tuple.
            abi_tuple(vec![AbiField::Dynamic(abi_ext3_array(
                &round.non_constant,
                field,
            )?)])
        })
        .collect::<Result<Vec<_>, FixtureV2Error>>()?;
    let rounds_array = abi_dynamic_array(rounds)?;
    // SumcheckProof is likewise a one-field dynamic tuple.
    abi_tuple(vec![AbiField::Dynamic(rounds_array)])
}

fn abi_dynamic_array(elements: Vec<Vec<u8>>) -> Result<Vec<u8>, FixtureV2Error> {
    let head_len = 32usize
        .checked_mul(elements.len())
        .ok_or(FixtureV2Error::Invalid("ABI dynamic-array head overflow"))?;
    let mut encoded = Vec::new();
    encoded.extend_from_slice(&abi_word_usize(elements.len(), "ABI dynamic-array length")?);
    let mut offset = head_len;
    for element in &elements {
        encoded.extend_from_slice(&abi_word_usize(offset, "ABI dynamic-array offset")?);
        offset = offset
            .checked_add(element.len())
            .ok_or(FixtureV2Error::Invalid("ABI dynamic-array offset overflow"))?;
    }
    for element in elements {
        encoded.extend_from_slice(&element);
    }
    Ok(encoded)
}

fn abi_bytes(bytes: &[u8]) -> Result<Vec<u8>, FixtureV2Error> {
    let padded = bytes
        .len()
        .checked_add(31)
        .map(|value| value / 32 * 32)
        .ok_or(FixtureV2Error::Invalid("ABI bytes padded length overflow"))?;
    let mut encoded = Vec::with_capacity(32 + padded);
    encoded.extend_from_slice(&abi_word_usize(bytes.len(), "ABI bytes length")?);
    encoded.extend_from_slice(bytes);
    encoded.resize(32 + padded, 0);
    Ok(encoded)
}

fn abi_word_u64(value: u64) -> [u8; 32] {
    let mut word = [0u8; 32];
    word[24..].copy_from_slice(&value.to_be_bytes());
    word
}

fn abi_word_usize(value: usize, field: &str) -> Result<[u8; 32], FixtureV2Error> {
    Ok(abi_word_u64(u64::try_from(value).map_err(|_| {
        FixtureV2Error::InvalidOwned(format!("{field} does not fit the fixture ABI u64 envelope"))
    })?))
}

fn push_abi_usize(output: &mut Vec<u8>, value: usize, field: &str) -> Result<(), FixtureV2Error> {
    output.extend_from_slice(&abi_word_usize(value, field)?);
    Ok(())
}

fn push_abi_decimal(output: &mut Vec<u8>, value: &str, field: &str) -> Result<(), FixtureV2Error> {
    let parsed = value.parse::<u64>().map_err(|error| {
        FixtureV2Error::InvalidOwned(format!("{field} is not canonical decimal u64: {error}"))
    })?;
    if parsed.to_string() != value {
        return Err(FixtureV2Error::InvalidOwned(format!(
            "{field} is not minimal decimal u64"
        )));
    }
    output.extend_from_slice(&abi_word_u64(parsed));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn actual_merkle_siblings(mut indices: Vec<usize>, layers: usize) -> usize {
        let mut siblings = 0;
        indices.sort_unstable();
        indices.dedup();
        for _ in 0..layers {
            let mut next = Vec::with_capacity(indices.len());
            let mut cursor = 0;
            while cursor < indices.len() {
                let index = indices[cursor];
                if cursor + 1 < indices.len() && indices[cursor + 1] == index ^ 1 {
                    cursor += 2;
                } else {
                    siblings += 1;
                    cursor += 1;
                }
                next.push(index >> 1);
            }
            indices = next;
        }
        siblings
    }

    #[test]
    fn exact_merkle_multiproof_maximum_matches_exhaustive_small_trees() {
        for num_leaves in [1usize, 2, 4, 8, 16] {
            let layers = num_leaves.trailing_zeros() as usize;
            for query_count in 0..=num_leaves {
                let actual_max = (0usize..(1usize << num_leaves))
                    .filter(|mask| mask.count_ones() as usize == query_count)
                    .map(|mask| {
                        let indices = (0..num_leaves)
                            .filter(|index| mask & (1usize << index) != 0)
                            .collect();
                        actual_merkle_siblings(indices, layers)
                    })
                    .max()
                    .unwrap_or(0);
                assert_eq!(
                    max_merkle_multiproof_siblings_v2(num_leaves, query_count).unwrap(),
                    actual_max,
                    "N={num_leaves}, k={query_count}"
                );
            }
        }
    }

    #[test]
    fn proof_fixture_keys_are_exactly_schema_generated() {
        let empty = MleProofV2Fixture {
            protocol_version: MLE_PROTOCOL_VERSION_CURRENT,
            constituent_width: 1,
            circuit_digest: Vec::new(),
            public_inputs: Vec::new(),
            preprocessed_root: encode_hex(&[0u8; 32]),
            witness_root: encode_hex(&[0u8; 32]),
            norm_inverse_root: encode_hex(&[0u8; 32]),
            whir_transcript: "0x".to_string(),
            whir_hints: "0x".to_string(),
            log_proof: SumcheckProofV2Fixture { rounds: Vec::new() },
            log_preprocessed: Vec::new(),
            log_witness: Vec::new(),
            log_norm_inverse: Vec::new(),
            gate_proof: SumcheckProofV2Fixture { rounds: Vec::new() },
            gate_preprocessed: Vec::new(),
            gate_witness: Vec::new(),
        };
        empty.validate_abi_keys().unwrap();
        let json = serde_json::to_string(&empty).unwrap();
        assert!(serde_json::from_str::<MleProofV2Fixture>(
            &json.replace("\"gateWitness\":[]", "\"gateWitness\":[],\"legacy\":0")
        )
        .is_err());
    }

    #[test]
    fn nested_dynamic_abi_offsets_are_relative_to_the_array_payload() {
        let proof = SumcheckProofV2Fixture {
            rounds: vec![CoefficientRoundV2Fixture {
                non_constant: vec![Ext3V2Fixture {
                    c0: "0x0000000000000001".to_string(),
                    c1: "0x0000000000000002".to_string(),
                    c2: "0x0000000000000003".to_string(),
                }],
            }],
        };
        let encoded = abi_sumcheck(&proof, "proof").unwrap();
        // Sumcheck tuple -> rounds offset; array length; first element offset;
        // CoefficientRound tuple -> nonConstant offset; Ext3[] length.
        assert_eq!(&encoded[24..32], &32u64.to_be_bytes());
        assert_eq!(&encoded[56..64], &1u64.to_be_bytes());
        assert_eq!(&encoded[88..96], &32u64.to_be_bytes());
        assert_eq!(&encoded[120..128], &32u64.to_be_bytes());
        assert_eq!(&encoded[152..160], &1u64.to_be_bytes());
    }
}
