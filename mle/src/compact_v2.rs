//! Strict, schema-bound compact encoding for [`MleProofV2`].
//!
//! The wire format deliberately carries no lengths for vectors whose sizes
//! are fixed by the circuit schema. The only length-prefixed values are the
//! two opaque WHIR byte streams. Goldilocks values are always canonical
//! eight-byte little-endian limbs; cubic-extension values are encoded in
//! `c0, c1, c2` order.

use ark_ff::PrimeField as ArkPrimeField;
use plonky2_field::types::{Field, Field64, PrimeField64};
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use crate::commitment::whir_pcs::WhirEvalProof;
#[cfg(debug_assertions)]
use crate::commitment::whir_pcs::WhirPCS;
use crate::proof_v2::{
    GateProofV2, MleProofV2, MAX_CONSTITUENT_WIDTH_V2, MAX_GATE_ROUND_DEGREE_V2,
    MAX_ROUTED_WIRES_V2, MAX_ROW_VARIABLES_V2, MLE_PROTOCOL_VERSION_CURRENT,
};
#[cfg(debug_assertions)]
use crate::proof_v2::{
    NUM_PACKED_VECTORS_PER_GROUP_V2, NUM_PCS_CLAIMS_V2, NUM_PCS_GROUPS_V2, WHIR_SESSION_SPLIT_V2,
};
use crate::protocol_schema_v2::{
    BASE_FIELD_MODULUS_V2, CIRCUIT_DIGEST_LENGTH_V2, COMPACT_MAGIC_V2, LOG_ROUND_DEGREE_V2,
    MAX_COMPACT_PROOF_BYTES_V2, MAX_PUBLIC_INPUTS_V2, MAX_WHIR_HINT_BYTES_V2,
    MAX_WHIR_NARG_BYTES_V2,
};
use crate::sumcheck::coefficients::{Ext3CoefficientRound, Ext3CoefficientSumcheckProof};

const BASE_LIMB_BYTES: usize = 8;
const EXT3_BYTES: usize = 3 * BASE_LIMB_BYTES;
const ROOT_BYTES: usize = 32;

/// Trusted dimensions and resource limits for decoding one compact v2 proof.
///
/// This is verifier configuration, not attacker-controlled proof data. Every
/// fixed-size vector in the proof is decoded using these exact dimensions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompactV2Shape {
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

impl CompactV2Shape {
    /// Number of bytes excluding the contents of the two opaque WHIR blobs.
    /// Their two `u32` length prefixes are included.
    pub fn fixed_encoded_len(&self) -> Result<usize, CompactV2Error> {
        self.validate()?;
        self.fixed_encoded_len_unchecked()
    }

    /// Exact encoded length for the supplied WHIR blob lengths.
    pub fn encoded_len(
        &self,
        whir_narg_len: usize,
        whir_hint_len: usize,
    ) -> Result<usize, CompactV2Error> {
        self.validate()?;
        if whir_narg_len > self.max_whir_narg_bytes {
            return Err(CompactV2Error::WhirBlobTooLarge {
                blob: "narg_string",
                got: whir_narg_len,
                max: self.max_whir_narg_bytes,
            });
        }
        if whir_hint_len > self.max_whir_hint_bytes {
            return Err(CompactV2Error::WhirBlobTooLarge {
                blob: "hints",
                got: whir_hint_len,
                max: self.max_whir_hint_bytes,
            });
        }
        u32::try_from(whir_narg_len)
            .map_err(|_| CompactV2Error::LengthDoesNotFitU32("narg_string"))?;
        u32::try_from(whir_hint_len).map_err(|_| CompactV2Error::LengthDoesNotFitU32("hints"))?;
        let total = checked_add(
            self.fixed_encoded_len_unchecked()?,
            checked_add(whir_narg_len, whir_hint_len)?,
        )?;
        if total > self.max_encoded_bytes {
            return Err(CompactV2Error::ProofTooLarge {
                got: total,
                max: self.max_encoded_bytes,
            });
        }
        Ok(total)
    }

    fn validate(&self) -> Result<(), CompactV2Error> {
        if self.degree_bits == 0 {
            return Err(CompactV2Error::InvalidShape(
                "row-variable count must be non-zero",
            ));
        }
        if self.constituent_width == 0 {
            return Err(CompactV2Error::InvalidShape(
                "constituent width must be non-zero",
            ));
        }
        if self.gate_round_degree < 3 {
            return Err(CompactV2Error::InvalidShape(
                "gate round degree must include a positive quotient degree factor",
            ));
        }
        if self.circuit_digest_len != CIRCUIT_DIGEST_LENGTH_V2 {
            return Err(CompactV2Error::InvalidShape(
                "circuit digest length does not match the wire-v3 protocol",
            ));
        }
        if self.public_inputs_len > MAX_PUBLIC_INPUTS_V2 {
            return Err(CompactV2Error::InvalidShape(
                "public-input count exceeds the reviewed v2 envelope",
            ));
        }
        if self.degree_bits > MAX_ROW_VARIABLES_V2 {
            return Err(CompactV2Error::InvalidShape(
                "row-variable count exceeds the reviewed v2 envelope",
            ));
        }
        if self.num_routed_wires > MAX_ROUTED_WIRES_V2 {
            return Err(CompactV2Error::InvalidShape(
                "routed-wire count exceeds the reviewed v2 envelope",
            ));
        }
        if self.constituent_width > MAX_CONSTITUENT_WIDTH_V2 {
            return Err(CompactV2Error::InvalidShape(
                "constituent width exceeds the reviewed v2 envelope",
            ));
        }
        if self.gate_round_degree > MAX_GATE_ROUND_DEGREE_V2 {
            return Err(CompactV2Error::InvalidShape(
                "gate round degree exceeds the reviewed v2 envelope",
            ));
        }
        let expected_width = checked_add(self.num_constants, self.num_routed_wires)?
            .max(self.num_wires)
            .max(checked_mul(2, self.num_routed_wires)?);
        if self.constituent_width != expected_width {
            return Err(CompactV2Error::InvalidShape(
                "constituent width does not match circuit dimensions",
            ));
        }
        let padded_width = self
            .constituent_width
            .checked_next_power_of_two()
            .ok_or(CompactV2Error::ShapeOverflow)?;
        let index_bits = padded_width.trailing_zeros() as usize;
        let packed_num_vars = checked_add(self.degree_bits, index_bits)?;
        if packed_num_vars >= usize::BITS as usize {
            return Err(CompactV2Error::InvalidShape(
                "packed WHIR dimension is not addressable",
            ));
        }
        if self.max_whir_narg_bytes > u32::MAX as usize {
            return Err(CompactV2Error::LengthDoesNotFitU32("max narg_string"));
        }
        if self.max_whir_hint_bytes > u32::MAX as usize {
            return Err(CompactV2Error::LengthDoesNotFitU32("max hints"));
        }
        if self.max_whir_narg_bytes > MAX_WHIR_NARG_BYTES_V2 {
            return Err(CompactV2Error::InvalidShape(
                "WHIR transcript cap exceeds the reviewed v2 envelope",
            ));
        }
        if self.max_whir_hint_bytes > MAX_WHIR_HINT_BYTES_V2 {
            return Err(CompactV2Error::InvalidShape(
                "WHIR hint cap exceeds the reviewed v2 envelope",
            ));
        }
        if self.max_encoded_bytes > MAX_COMPACT_PROOF_BYTES_V2 {
            return Err(CompactV2Error::InvalidShape(
                "compact proof cap exceeds the reviewed v2 envelope",
            ));
        }
        let fixed = self.fixed_encoded_len_unchecked()?;
        if fixed > self.max_encoded_bytes {
            return Err(CompactV2Error::ProofTooLarge {
                got: fixed,
                max: self.max_encoded_bytes,
            });
        }
        Ok(())
    }

    fn fixed_encoded_len_unchecked(&self) -> Result<usize, CompactV2Error> {
        // magic, protocol_version, constituent_width, roots, and two blob lengths.
        let mut size = 8usize + 8 + 4 + 3 * ROOT_BYTES + 2 * 4;
        size = checked_add(
            size,
            checked_mul(
                checked_add(self.circuit_digest_len, self.public_inputs_len)?,
                BASE_LIMB_BYTES,
            )?,
        )?;

        // One degree-five Ext3 coefficient vector per outer variable.
        size = checked_add(
            size,
            checked_mul(
                checked_mul(self.degree_bits, LOG_ROUND_DEGREE_V2)?,
                EXT3_BYTES,
            )?,
        )?;

        let preprocessed_len = checked_add(self.num_constants, self.num_routed_wires)?;
        let norm_inverse_len = checked_mul(2, self.num_routed_wires)?;
        let log_terminal_len = checked_add(
            checked_add(preprocessed_len, self.num_wires)?,
            norm_inverse_len,
        )?;
        size = checked_add(size, checked_mul(log_terminal_len, EXT3_BYTES)?)?;

        let gate_round_values = checked_mul(self.degree_bits, self.gate_round_degree)?;
        let gate_terminal_values = checked_add(preprocessed_len, self.num_wires)?;
        let gate_values = checked_add(gate_round_values, gate_terminal_values)?;
        size = checked_add(size, checked_mul(gate_values, EXT3_BYTES)?)?;
        Ok(size)
    }

    fn preprocessed_len(&self) -> Result<usize, CompactV2Error> {
        checked_add(self.num_constants, self.num_routed_wires)
    }

    fn norm_inverse_len(&self) -> Result<usize, CompactV2Error> {
        checked_mul(2, self.num_routed_wires)
    }

    #[cfg(debug_assertions)]
    fn packed_num_vars(&self) -> Result<usize, CompactV2Error> {
        let padded_width = self
            .constituent_width
            .checked_next_power_of_two()
            .ok_or(CompactV2Error::ShapeOverflow)?;
        checked_add(self.degree_bits, padded_width.trailing_zeros() as usize)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompactV2Error {
    InvalidShape(&'static str),
    ShapeOverflow,
    WrongField,
    BadMagic,
    WrongProtocolVersion {
        got: u64,
    },
    WrongConstituentWidth {
        got: usize,
        expected: usize,
    },
    WrongVectorLength {
        field: &'static str,
        got: usize,
        expected: usize,
    },
    WrongRootLength {
        root: &'static str,
        got: usize,
    },
    LengthDoesNotFitU32(&'static str),
    WhirBlobTooLarge {
        blob: &'static str,
        got: usize,
        max: usize,
    },
    ProofTooLarge {
        got: usize,
        max: usize,
    },
    UnexpectedEof {
        offset: usize,
        needed: usize,
        remaining: usize,
    },
    NonCanonicalGoldilocks {
        offset: usize,
        value: u64,
    },
    TrailingBytes {
        count: usize,
    },
    WhirPatternReconstruction(String),
}

impl core::fmt::Display for CompactV2Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidShape(message) => write!(f, "invalid compact-v2 shape: {message}"),
            Self::ShapeOverflow => write!(f, "compact-v2 shape arithmetic overflow"),
            Self::WrongField => write!(f, "compact-v2 requires the Goldilocks base field"),
            Self::BadMagic => write!(f, "invalid compact-v2 magic"),
            Self::WrongProtocolVersion { got } => {
                write!(f, "invalid compact-v2 protocol version {got}")
            }
            Self::WrongConstituentWidth { got, expected } => write!(
                f,
                "invalid compact-v2 constituent width {got}; expected {expected}"
            ),
            Self::WrongVectorLength {
                field,
                got,
                expected,
            } => write!(
                f,
                "invalid compact-v2 {field} length {got}; expected {expected}"
            ),
            Self::WrongRootLength { root, got } => {
                write!(
                    f,
                    "invalid compact-v2 {root} root length {got}; expected 32"
                )
            }
            Self::LengthDoesNotFitU32(field) => {
                write!(f, "compact-v2 {field} length does not fit u32")
            }
            Self::WhirBlobTooLarge { blob, got, max } => {
                write!(f, "compact-v2 WHIR {blob} is {got} bytes; maximum is {max}")
            }
            Self::ProofTooLarge { got, max } => {
                write!(f, "compact-v2 proof is {got} bytes; maximum is {max}")
            }
            Self::UnexpectedEof {
                offset,
                needed,
                remaining,
            } => write!(
                f,
                "compact-v2 proof is truncated at byte {offset}: need {needed}, have {remaining}"
            ),
            Self::NonCanonicalGoldilocks { offset, value } => write!(
                f,
                "non-canonical Goldilocks limb {value} at compact-v2 byte {offset}"
            ),
            Self::TrailingBytes { count } => {
                write!(f, "compact-v2 proof has {count} trailing bytes")
            }
            Self::WhirPatternReconstruction(message) => {
                write!(f, "WHIR debug-pattern reconstruction failed: {message}")
            }
        }
    }
}

impl std::error::Error for CompactV2Error {}

/// Encode a proof using the exact dimensions and resource bounds in `shape`.
pub fn encode_compact_v2<F: Field + PrimeField64>(
    proof: &MleProofV2<F>,
    shape: &CompactV2Shape,
) -> Result<Vec<u8>, CompactV2Error> {
    require_goldilocks::<F>()?;
    shape.validate()?;
    validate_proof_shape(proof, shape)?;

    let narg_len = proof.whir_eval_proof.narg_string.len();
    let hint_len = proof.whir_eval_proof.hints.len();
    let encoded_len = shape.encoded_len(narg_len, hint_len)?;
    let mut writer = Writer::with_capacity(encoded_len);
    writer.bytes(&COMPACT_MAGIC_V2);
    writer.u64(MLE_PROTOCOL_VERSION_CURRENT);
    writer.u32(
        u32::try_from(shape.constituent_width)
            .map_err(|_| CompactV2Error::LengthDoesNotFitU32("constituent width"))?,
    );
    writer.base_vec(&proof.circuit_digest);
    writer.base_vec(&proof.public_inputs);
    writer.root(&proof.preprocessed_root, "preprocessed")?;
    writer.root(&proof.witness_root, "witness")?;
    writer.root(&proof.norm_inverse_root, "norm_inverse")?;
    writer.blob(&proof.whir_eval_proof.narg_string, "narg_string")?;
    writer.blob(&proof.whir_eval_proof.hints, "hints")?;

    for round in &proof.log_sumcheck_proof.rounds {
        writer.ext3_vec(&round.non_constant);
    }
    writer.ext3_vec(&proof.log_preprocessed_evals);
    writer.ext3_vec(&proof.log_witness_evals);
    writer.ext3_vec(&proof.log_norm_inverse_evals);

    for round in &proof.gate_proof.sumcheck_proof.rounds {
        writer.ext3_vec(&round.non_constant);
    }
    writer.ext3_vec(&proof.gate_proof.preprocessed_evals);
    writer.ext3_vec(&proof.gate_proof.witness_evals);
    debug_assert_eq!(writer.output.len(), encoded_len);
    Ok(writer.output)
}

/// Decode a single canonical proof. Every byte must be consumed exactly.
///
/// In debug builds, upstream WHIR requires a non-wire transcript interaction
/// pattern. It is reconstructed from WHIR's strict production preflight; it is
/// never accepted from attacker-controlled compact bytes.
pub fn decode_compact_v2<F: Field + PrimeField64>(
    encoded: &[u8],
    shape: &CompactV2Shape,
) -> Result<MleProofV2<F>, CompactV2Error> {
    require_goldilocks::<F>()?;
    shape.validate()?;
    if encoded.len() > shape.max_encoded_bytes {
        return Err(CompactV2Error::ProofTooLarge {
            got: encoded.len(),
            max: shape.max_encoded_bytes,
        });
    }
    let mut reader = Reader::new(encoded);
    if reader.take(COMPACT_MAGIC_V2.len())? != COMPACT_MAGIC_V2 {
        return Err(CompactV2Error::BadMagic);
    }
    let protocol_version = reader.u64()?;
    if protocol_version != MLE_PROTOCOL_VERSION_CURRENT {
        return Err(CompactV2Error::WrongProtocolVersion {
            got: protocol_version,
        });
    }
    let constituent_width = reader.u32()? as usize;
    if constituent_width != shape.constituent_width {
        return Err(CompactV2Error::WrongConstituentWidth {
            got: constituent_width,
            expected: shape.constituent_width,
        });
    }

    let circuit_digest = reader.base_vec::<F>(shape.circuit_digest_len)?;
    let public_inputs = reader.base_vec::<F>(shape.public_inputs_len)?;
    let preprocessed_root = reader.root()?.to_vec();
    let witness_root = reader.root()?.to_vec();
    let norm_inverse_root = reader.root()?.to_vec();
    let narg_string = reader.blob("narg_string", shape.max_whir_narg_bytes)?;
    let hints = reader.blob("hints", shape.max_whir_hint_bytes)?;

    let log_sumcheck_proof = Ext3CoefficientSumcheckProof {
        rounds: (0..shape.degree_bits)
            .map(|_| {
                Ok(Ext3CoefficientRound {
                    non_constant: reader.ext3_vec(LOG_ROUND_DEGREE_V2)?,
                })
            })
            .collect::<Result<_, CompactV2Error>>()?,
    };
    let log_preprocessed_evals = reader.ext3_vec(shape.preprocessed_len()?)?;
    let log_witness_evals = reader.ext3_vec(shape.num_wires)?;
    let log_norm_inverse_evals = reader.ext3_vec(shape.norm_inverse_len()?)?;

    let gate_proof = GateProofV2 {
        sumcheck_proof: Ext3CoefficientSumcheckProof {
            rounds: (0..shape.degree_bits)
                .map(|_| {
                    Ok(Ext3CoefficientRound {
                        non_constant: reader.ext3_vec(shape.gate_round_degree)?,
                    })
                })
                .collect::<Result<_, CompactV2Error>>()?,
        },
        preprocessed_evals: reader.ext3_vec(shape.preprocessed_len()?)?,
        witness_evals: reader.ext3_vec(shape.num_wires)?,
    };
    if reader.remaining() != 0 {
        return Err(CompactV2Error::TrailingBytes {
            count: reader.remaining(),
        });
    }

    let whir_eval_proof = make_whir_eval_proof(shape, narg_string, hints)?;
    Ok(MleProofV2 {
        protocol_version,
        constituent_width,
        circuit_digest,
        public_inputs,
        whir_eval_proof,
        preprocessed_root,
        witness_root,
        norm_inverse_root,
        log_sumcheck_proof,
        log_preprocessed_evals,
        log_witness_evals,
        log_norm_inverse_evals,
        gate_proof,
    })
}

fn validate_proof_shape<F: Field>(
    proof: &MleProofV2<F>,
    shape: &CompactV2Shape,
) -> Result<(), CompactV2Error> {
    if proof.protocol_version != MLE_PROTOCOL_VERSION_CURRENT {
        return Err(CompactV2Error::WrongProtocolVersion {
            got: proof.protocol_version,
        });
    }
    if proof.constituent_width != shape.constituent_width {
        return Err(CompactV2Error::WrongConstituentWidth {
            got: proof.constituent_width,
            expected: shape.constituent_width,
        });
    }
    expect_len(
        "circuit_digest",
        proof.circuit_digest.len(),
        shape.circuit_digest_len,
    )?;
    expect_len(
        "public_inputs",
        proof.public_inputs.len(),
        shape.public_inputs_len,
    )?;
    for (root, name) in [
        (&proof.preprocessed_root, "preprocessed"),
        (&proof.witness_root, "witness"),
        (&proof.norm_inverse_root, "norm_inverse"),
    ] {
        if root.len() != ROOT_BYTES {
            return Err(CompactV2Error::WrongRootLength {
                root: name,
                got: root.len(),
            });
        }
    }
    expect_len(
        "log sumcheck rounds",
        proof.log_sumcheck_proof.rounds.len(),
        shape.degree_bits,
    )?;
    for round in &proof.log_sumcheck_proof.rounds {
        expect_len(
            "log round coefficients",
            round.non_constant.len(),
            LOG_ROUND_DEGREE_V2,
        )?;
    }
    expect_len(
        "log preprocessed evaluations",
        proof.log_preprocessed_evals.len(),
        shape.preprocessed_len()?,
    )?;
    expect_len(
        "log witness evaluations",
        proof.log_witness_evals.len(),
        shape.num_wires,
    )?;
    expect_len(
        "log norm-inverse evaluations",
        proof.log_norm_inverse_evals.len(),
        shape.norm_inverse_len()?,
    )?;
    expect_len(
        "gate sumcheck rounds",
        proof.gate_proof.sumcheck_proof.rounds.len(),
        shape.degree_bits,
    )?;
    for round in &proof.gate_proof.sumcheck_proof.rounds {
        expect_len(
            "gate round coefficients",
            round.non_constant.len(),
            shape.gate_round_degree,
        )?;
    }
    expect_len(
        "gate preprocessed evaluations",
        proof.gate_proof.preprocessed_evals.len(),
        shape.preprocessed_len()?,
    )?;
    expect_len(
        "gate witness evaluations",
        proof.gate_proof.witness_evals.len(),
        shape.num_wires,
    )?;
    Ok(())
}

fn expect_len(field: &'static str, got: usize, expected: usize) -> Result<(), CompactV2Error> {
    if got != expected {
        return Err(CompactV2Error::WrongVectorLength {
            field,
            got,
            expected,
        });
    }
    Ok(())
}

fn require_goldilocks<F: Field64>() -> Result<(), CompactV2Error> {
    if F::ORDER != BASE_FIELD_MODULUS_V2 {
        return Err(CompactV2Error::WrongField);
    }
    Ok(())
}

fn checked_add(left: usize, right: usize) -> Result<usize, CompactV2Error> {
    left.checked_add(right).ok_or(CompactV2Error::ShapeOverflow)
}

fn checked_mul(left: usize, right: usize) -> Result<usize, CompactV2Error> {
    left.checked_mul(right).ok_or(CompactV2Error::ShapeOverflow)
}

struct Writer {
    output: Vec<u8>,
}

impl Writer {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            output: Vec::with_capacity(capacity),
        }
    }

    fn bytes(&mut self, value: &[u8]) {
        self.output.extend_from_slice(value);
    }

    fn u32(&mut self, value: u32) {
        self.bytes(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes(&value.to_le_bytes());
    }

    fn base<F: PrimeField64>(&mut self, value: &F) {
        self.u64(value.to_canonical_u64());
    }

    fn base_vec<F: PrimeField64>(&mut self, values: &[F]) {
        for value in values {
            self.base(value);
        }
    }

    fn ext3(&mut self, value: &Field64_3) {
        self.u64(value.c0.into_bigint().0[0]);
        self.u64(value.c1.into_bigint().0[0]);
        self.u64(value.c2.into_bigint().0[0]);
    }

    fn ext3_vec(&mut self, values: &[Field64_3]) {
        for value in values {
            self.ext3(value);
        }
    }

    fn root(&mut self, root: &[u8], name: &'static str) -> Result<(), CompactV2Error> {
        if root.len() != ROOT_BYTES {
            return Err(CompactV2Error::WrongRootLength {
                root: name,
                got: root.len(),
            });
        }
        self.bytes(root);
        Ok(())
    }

    fn blob(&mut self, blob: &[u8], name: &'static str) -> Result<(), CompactV2Error> {
        self.u32(u32::try_from(blob.len()).map_err(|_| CompactV2Error::LengthDoesNotFitU32(name))?);
        self.bytes(blob);
        Ok(())
    }
}

struct Reader<'a> {
    encoded: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn new(encoded: &'a [u8]) -> Self {
        Self { encoded, offset: 0 }
    }

    fn remaining(&self) -> usize {
        self.encoded.len() - self.offset
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], CompactV2Error> {
        let end = self
            .offset
            .checked_add(count)
            .ok_or(CompactV2Error::ShapeOverflow)?;
        if end > self.encoded.len() {
            return Err(CompactV2Error::UnexpectedEof {
                offset: self.offset,
                needed: count,
                remaining: self.remaining(),
            });
        }
        let output = &self.encoded[self.offset..end];
        self.offset = end;
        Ok(output)
    }

    fn u32(&mut self) -> Result<u32, CompactV2Error> {
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(self.take(4)?);
        Ok(u32::from_le_bytes(bytes))
    }

    fn u64(&mut self) -> Result<u64, CompactV2Error> {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(self.take(8)?);
        Ok(u64::from_le_bytes(bytes))
    }

    fn base<F: Field + PrimeField64>(&mut self) -> Result<F, CompactV2Error> {
        let offset = self.offset;
        let value = self.u64()?;
        if value >= BASE_FIELD_MODULUS_V2 {
            return Err(CompactV2Error::NonCanonicalGoldilocks { offset, value });
        }
        Ok(F::from_canonical_u64(value))
    }

    fn base_vec<F: Field + PrimeField64>(
        &mut self,
        count: usize,
    ) -> Result<Vec<F>, CompactV2Error> {
        let bytes = checked_mul(count, BASE_LIMB_BYTES)?;
        if bytes > self.remaining() {
            return Err(CompactV2Error::UnexpectedEof {
                offset: self.offset,
                needed: bytes,
                remaining: self.remaining(),
            });
        }
        (0..count).map(|_| self.base()).collect()
    }

    fn ext3(&mut self) -> Result<Field64_3, CompactV2Error> {
        let c0 = self.ark_base()?;
        let c1 = self.ark_base()?;
        let c2 = self.ark_base()?;
        Ok(Field64_3::new(c0, c1, c2))
    }

    fn ext3_vec(&mut self, count: usize) -> Result<Vec<Field64_3>, CompactV2Error> {
        let bytes = checked_mul(count, EXT3_BYTES)?;
        if bytes > self.remaining() {
            return Err(CompactV2Error::UnexpectedEof {
                offset: self.offset,
                needed: bytes,
                remaining: self.remaining(),
            });
        }
        (0..count).map(|_| self.ext3()).collect()
    }

    fn ark_base(&mut self) -> Result<ArkGoldilocks, CompactV2Error> {
        let offset = self.offset;
        let value = self.u64()?;
        if value >= BASE_FIELD_MODULUS_V2 {
            return Err(CompactV2Error::NonCanonicalGoldilocks { offset, value });
        }
        Ok(ArkGoldilocks::from(value))
    }

    fn root(&mut self) -> Result<[u8; ROOT_BYTES], CompactV2Error> {
        let mut root = [0u8; ROOT_BYTES];
        root.copy_from_slice(self.take(ROOT_BYTES)?);
        Ok(root)
    }

    fn blob(&mut self, name: &'static str, maximum: usize) -> Result<Vec<u8>, CompactV2Error> {
        let length = self.u32()? as usize;
        if length > maximum {
            return Err(CompactV2Error::WhirBlobTooLarge {
                blob: name,
                got: length,
                max: maximum,
            });
        }
        Ok(self.take(length)?.to_vec())
    }
}

fn make_whir_eval_proof(
    shape: &CompactV2Shape,
    narg_string: Vec<u8>,
    hints: Vec<u8>,
) -> Result<WhirEvalProof, CompactV2Error> {
    #[allow(unused_mut)]
    let mut proof = WhirEvalProof {
        narg_string,
        hints,
        #[cfg(debug_assertions)]
        pattern: Vec::new(),
    };
    #[cfg(debug_assertions)]
    {
        proof.pattern = reconstruct_whir_pattern(shape, &proof)?;
    }
    #[cfg(not(debug_assertions))]
    let _ = shape;
    Ok(proof)
}

#[cfg(debug_assertions)]
fn reconstruct_whir_pattern(
    shape: &CompactV2Shape,
    proof: &WhirEvalProof,
) -> Result<Vec<whir::transcript::Interaction>, CompactV2Error> {
    let pcs = WhirPCS::for_constituents(shape.packed_num_vars()?, NUM_PACKED_VECTORS_PER_GROUP_V2);
    let trace = pcs
        .trace_grouped_preflight(
            shape.packed_num_vars()?,
            proof,
            WHIR_SESSION_SPLIT_V2,
            NUM_PCS_GROUPS_V2,
            NUM_PCS_CLAIMS_V2,
        )
        .map_err(CompactV2Error::WhirPatternReconstruction)?;
    crate::commitment::whir_pcs::grouped_pattern_from_trace(&trace, &proof.hints)
        .map_err(CompactV2Error::WhirPatternReconstruction)
}
