//! Canonical wire-v3 circuit-configuration digest shared with Solidity.
//!
//! Plonky2's circuit digest and preprocessed root do not, by themselves,
//! provide a convenient cross-language commitment to every gate-dispatch
//! parameter. The historical `V2` API generation therefore hashes the exact
//! terminal-evaluator configuration
//! using fixed-width little-endian fields and absorbs that digest before any
//! outer challenge.

use anyhow::{ensure, Context, Result};
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_data::{CommonCircuitData, ProverOnlyCircuitData};
use plonky2::plonk::config::GenericConfig;
use plonky2::plonk::prover::canonical_public_input_wires;
use plonky2_field::extension::Extendable;
use sha3::{Digest, Keccak256};

use crate::fixture::classify_gate;
use crate::proof_v2::{GateInfoV2, MLE_PROTOCOL_VERSION_CURRENT};
use crate::protocol_schema_v2::{
    CIRCUIT_CONFIG_HASH_DOMAIN_V2, CIRCUIT_DIGEST_LENGTH_V2, INNER_EXTENSION_DEGREE_V2,
};

fn narrow_u8(value: usize, label: &str) -> Result<u8> {
    u8::try_from(value).with_context(|| format!("v2 gate {label} does not fit u8"))
}

fn narrow_u16(value: usize, label: &str) -> Result<u16> {
    u16::try_from(value).with_context(|| format!("v2 gate {label} does not fit u16"))
}

/// Extract the exact ordered gate records consumed by
/// `Plonky2GateEvaluatorExt3.sol`; unknown or non-representable gates fail closed.
pub fn collect_gate_info_v2<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
) -> Result<Vec<GateInfoV2>> {
    let selectors = &common_data.selectors_info;
    common_data
        .gates
        .iter()
        .enumerate()
        .map(|(row, gate)| {
            let params = classify_gate::<F, D>(gate)?;
            let selector_index = *selectors
                .selector_indices
                .get(row)
                .context("v2 gate has no selector index")?;
            let group = selectors
                .groups
                .get(selector_index)
                .context("v2 gate selector group is missing")?;
            Ok(GateInfoV2 {
                gate_id: params.gate_id,
                selector_index: narrow_u8(selector_index, "selector index")?,
                group_start: narrow_u8(group.start, "group start")?,
                group_end: narrow_u8(group.end, "group end")?,
                gate_row_index: narrow_u8(row, "row index")?,
                num_constraints: narrow_u16(gate.0.num_constraints(), "constraint count")?,
                num_or_consts: params.num_or_consts,
                param2: params.param2,
                param3: params.param3,
            })
        })
        .collect()
}

fn push_u64(bytes: &mut Vec<u8>, value: usize, label: &str) -> Result<()> {
    let narrowed = u64::try_from(value).with_context(|| format!("v2 {label} does not fit u64"))?;
    bytes.extend_from_slice(&narrowed.to_le_bytes());
    Ok(())
}

/// Encode the ordered canonical routed-wire location of every public input as
/// `row_u16_le || column_u8`. Public-input order and duplicate targets are
/// preserved; no sorting or deduplication is permitted.
pub fn public_input_wire_map_v2<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    prover_data: &ProverOnlyCircuitData<F, C, D>,
    common_data: &CommonCircuitData<F, D>,
) -> Result<Vec<u8>> {
    let wires = canonical_public_input_wires(prover_data, common_data)?;
    encode_public_input_wires_v2(
        wires.iter().map(|wire| (wire.row, wire.column)),
        common_data.num_public_inputs,
        common_data.degree(),
        common_data.config.num_routed_wires,
    )
}

/// Encode already-derived public-input wire locations using the canonical
/// three-byte entry format.
pub fn encode_public_input_wires_v2(
    wires: impl IntoIterator<Item = (usize, usize)>,
    num_public_inputs: usize,
    degree: usize,
    num_routed_wires: usize,
) -> Result<Vec<u8>> {
    let mut encoded = Vec::with_capacity(3 * num_public_inputs);
    for (row, column) in wires {
        ensure!(row < degree, "v2 public-input wire row is out of range");
        ensure!(
            column < num_routed_wires,
            "v2 public-input wire column is not routed"
        );
        let row = u16::try_from(row).context("v2 public-input wire row does not fit u16")?;
        let column = u8::try_from(column).context("v2 public-input wire column does not fit u8")?;
        encoded.extend_from_slice(&row.to_le_bytes());
        encoded.push(column);
    }
    ensure!(
        encoded.len() == 3 * num_public_inputs,
        "v2 public-input wire-map length mismatch"
    );
    Ok(encoded)
}

/// Validate and decode the canonical three-byte public-input wire map.
pub fn decode_public_input_wire_map_v2(
    encoded: &[u8],
    num_public_inputs: usize,
    degree: usize,
    num_routed_wires: usize,
) -> Result<Vec<(usize, usize)>> {
    ensure!(
        encoded.len() == 3 * num_public_inputs,
        "v2 public-input wire-map length mismatch"
    );
    encoded
        .chunks_exact(3)
        .map(|entry| {
            let row = u16::from_le_bytes([entry[0], entry[1]]) as usize;
            let column = entry[2] as usize;
            ensure!(row < degree, "v2 public-input wire row is out of range");
            ensure!(
                column < num_routed_wires,
                "v2 public-input wire column is not routed"
            );
            Ok((row, column))
        })
        .collect()
}

/// Return the byte-exact digest preimage for differential tests and deployer
/// tooling. Field elements are canonical Goldilocks u64 little-endian limbs.
pub fn circuit_config_digest_preimage_v2<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    circuit_digest: &[F],
    subgroup_gen_powers: &[F],
    gates: &[GateInfoV2],
    public_input_wire_map: &[u8],
) -> Result<Vec<u8>> {
    ensure!(
        common_data.luts.is_empty(),
        "v2 lookup configuration is unsupported"
    );
    ensure!(
        circuit_digest.len() == CIRCUIT_DIGEST_LENGTH_V2,
        "v2 circuit digest shape mismatch"
    );
    ensure!(
        gates.len() == common_data.gates.len(),
        "v2 gate metadata count mismatch"
    );
    ensure!(
        subgroup_gen_powers.len() == common_data.degree_bits(),
        "v2 subgroup-power count mismatch"
    );
    ensure!(
        D == INNER_EXTENSION_DEGREE_V2,
        "v2 requires the schema-bound Plonky2 extension degree"
    );
    circuit_config_digest_preimage_from_parts_v2(
        common_data.degree_bits(),
        common_data.num_public_inputs,
        common_data.num_constants,
        common_data.config.num_routed_wires,
        common_data.config.num_wires,
        common_data.selectors_info.num_selectors(),
        common_data.num_gate_constraints,
        common_data.quotient_degree_factor,
        circuit_digest,
        &common_data.k_is,
        subgroup_gen_powers,
        gates,
        public_input_wire_map,
    )
}

/// Construct the canonical circuit-configuration digest preimage from an
/// already decoded proof-free artifact. This is byte-identical to
/// [`circuit_config_digest_preimage_v2`] and lets deployment consumers verify
/// the digest without reconstructing the circuit or trusting duplicate JSON
/// fields.
#[allow(clippy::too_many_arguments)]
pub fn circuit_config_digest_preimage_from_parts_v2<F: RichField>(
    degree_bits: usize,
    num_public_inputs: usize,
    num_constants: usize,
    num_routed_wires: usize,
    num_wires: usize,
    num_selectors: usize,
    num_gate_constraints: usize,
    quotient_degree_factor: usize,
    circuit_digest: &[F],
    k_is: &[F],
    subgroup_gen_powers: &[F],
    gates: &[GateInfoV2],
    public_input_wire_map: &[u8],
) -> Result<Vec<u8>> {
    ensure!(
        circuit_digest.len() == CIRCUIT_DIGEST_LENGTH_V2,
        "v2 circuit digest shape mismatch"
    );
    ensure!(
        k_is.len() == num_routed_wires,
        "v2 coset-shift count mismatch"
    );
    ensure!(
        subgroup_gen_powers.len() == degree_bits,
        "v2 subgroup-power count mismatch"
    );
    let degree_bits_u32 =
        u32::try_from(degree_bits).context("v2 row variable count does not fit u32")?;
    let degree = 1usize
        .checked_shl(degree_bits_u32)
        .context("v2 row degree overflow")?;
    decode_public_input_wire_map_v2(
        public_input_wire_map,
        num_public_inputs,
        degree,
        num_routed_wires,
    )?;

    let mut bytes = Vec::with_capacity(
        CIRCUIT_CONFIG_HASH_DOMAIN_V2.len()
            + 16 * 8
            + 8 * (circuit_digest.len() + k_is.len() + subgroup_gen_powers.len())
            + 13 * gates.len()
            + 8
            + public_input_wire_map.len(),
    );
    bytes.extend_from_slice(CIRCUIT_CONFIG_HASH_DOMAIN_V2.as_bytes());
    bytes.extend_from_slice(&MLE_PROTOCOL_VERSION_CURRENT.to_le_bytes());
    push_u64(&mut bytes, INNER_EXTENSION_DEGREE_V2, "extension degree")?;
    push_u64(&mut bytes, degree_bits, "row variable count")?;
    push_u64(&mut bytes, num_public_inputs, "public-input count")?;
    push_u64(&mut bytes, num_constants, "constant count")?;
    push_u64(&mut bytes, num_routed_wires, "routed-wire count")?;
    push_u64(&mut bytes, num_wires, "wire count")?;
    push_u64(&mut bytes, num_selectors, "selector count")?;
    push_u64(&mut bytes, num_gate_constraints, "gate-constraint count")?;
    push_u64(&mut bytes, quotient_degree_factor, "quotient-degree factor")?;

    push_u64(&mut bytes, circuit_digest.len(), "circuit-digest length")?;
    for value in circuit_digest {
        bytes.extend_from_slice(&value.to_canonical_u64().to_le_bytes());
    }
    push_u64(&mut bytes, k_is.len(), "coset-shift count")?;
    for value in k_is {
        bytes.extend_from_slice(&value.to_canonical_u64().to_le_bytes());
    }
    push_u64(
        &mut bytes,
        subgroup_gen_powers.len(),
        "subgroup-power count",
    )?;
    for value in subgroup_gen_powers {
        bytes.extend_from_slice(&value.to_canonical_u64().to_le_bytes());
    }
    push_u64(&mut bytes, gates.len(), "gate count")?;
    for gate in gates {
        bytes.extend_from_slice(&[
            gate.gate_id,
            gate.selector_index,
            gate.group_start,
            gate.group_end,
            gate.gate_row_index,
        ]);
        bytes.extend_from_slice(&gate.num_constraints.to_le_bytes());
        bytes.extend_from_slice(&gate.num_or_consts.to_le_bytes());
        bytes.extend_from_slice(&gate.param2.to_le_bytes());
        bytes.extend_from_slice(&gate.param3.to_le_bytes());
    }
    push_u64(
        &mut bytes,
        public_input_wire_map.len(),
        "public-input wire-map byte length",
    )?;
    bytes.extend_from_slice(public_input_wire_map);
    Ok(bytes)
}

/// Hash [`circuit_config_digest_preimage_from_parts_v2`] for a proof-free
/// configuration artifact.
#[allow(clippy::too_many_arguments)]
pub fn circuit_config_digest_from_parts_v2<F: RichField>(
    degree_bits: usize,
    num_public_inputs: usize,
    num_constants: usize,
    num_routed_wires: usize,
    num_wires: usize,
    num_selectors: usize,
    num_gate_constraints: usize,
    quotient_degree_factor: usize,
    circuit_digest: &[F],
    k_is: &[F],
    subgroup_gen_powers: &[F],
    gates: &[GateInfoV2],
    public_input_wire_map: &[u8],
) -> Result<[u8; 32]> {
    Ok(
        Keccak256::digest(circuit_config_digest_preimage_from_parts_v2(
            degree_bits,
            num_public_inputs,
            num_constants,
            num_routed_wires,
            num_wires,
            num_selectors,
            num_gate_constraints,
            quotient_degree_factor,
            circuit_digest,
            k_is,
            subgroup_gen_powers,
            gates,
            public_input_wire_map,
        )?)
        .into(),
    )
}

pub fn circuit_config_digest_v2<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    circuit_digest: &[F],
    subgroup_gen_powers: &[F],
    gates: &[GateInfoV2],
    public_input_wire_map: &[u8],
) -> Result<[u8; 32]> {
    Ok(Keccak256::digest(circuit_config_digest_preimage_v2(
        common_data,
        circuit_digest,
        subgroup_gen_powers,
        gates,
        public_input_wire_map,
    )?)
    .into())
}
