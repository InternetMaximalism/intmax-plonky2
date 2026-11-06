//! Cheating-prover regression fixtures for the wire-v3 MLE/WHIR verifier.
//!
//! Every existing negative test perturbs an *honest* proof, so the transcript
//! or WHIR check fires first and the three terminal checks downstream of the
//! PCS (the Ext3 gate terminal, the norm/logUp terminal and the preprocessed
//! root pin) are never the check that rejects. This file builds proofs from
//! tampered `EvaluationTables` instead: the prover commits the tampered tables
//! honestly, runs both sumchecks honestly over them and produces a WHIR proof
//! that opens exactly what it committed. The PCS/transcript part is therefore
//! valid and only the targeted relation check can reject the proof.
//!
//! Circuit: the `v2_cross_language` small-mul chain (`public = x^6`,
//! `degree_bits = 2`). `CircuitBuilder::mul(a, b)` lowers to
//! `arithmetic(1, 0, a, b, a)`, so each op's addend column is routed (copy
//! constrained to `a`) but multiplied by the zero constant and hence not gate
//! constrained; that is what makes a copy-only violation possible.
//!
//! The checked-in JSON `contracts/test/fixtures/v2_cheating_prover.json` is
//! consumed by `contracts/test/CheatingProverFixtureV2.t.sol`. It is produced
//! by [`export_cheating_fixture_unverified`], which deliberately bypasses the
//! production exporter (`try_export_mle_v2_fixture` refuses to emit a proof
//! that does not verify) and must never be used for an honest deployment
//! artifact.

use plonky2::hash::hash_types::HashOut;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, EvaluationTables};
use plonky2::plonk::config::{Hasher, PoseidonGoldilocksConfig};
use plonky2::plonk::prover::extract_evaluation_tables;
use plonky2::plonk::vanishing_poly::evaluate_gate_constraints;
use plonky2::plonk::vars::EvaluationVars;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::quadratic::QuadraticExtension;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field, PrimeField64};
use plonky2_mle::compact_v2::{decode_compact_v2, encode_compact_v2, CompactV2Shape};
use plonky2_mle::fixture_v2::{
    compact_v2_shape_for_common, solidity_abi_encode_mle_proof_v2,
    try_export_mle_v2_config_fixture, CompactV2ShapeFixture, EncodedProofV2Fixture,
    MleProofV2Fixture, PinnedMleVerifierV2Fixture, SOLIDITY_MLE_PROOF_ENCODING_V2,
    SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2,
};
use plonky2_mle::proof_v2::{MleProofV2, MleVerificationKeyV2};
use plonky2_mle::protocol_schema_v2::COMPACT_MAGIC_V2;
use plonky2_mle::prover_v2::{mle_prove_v2_from_tables, mle_setup_v2};
use plonky2_mle::verifier_v2::mle_verify_v2;
use serde::{Deserialize, Serialize};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
type FE = QuadraticExtension<GoldilocksField>;
const D: usize = 2;

const FIXTURE_RELATIVE_PATH: &str = "contracts/test/fixtures/v2_cheating_prover.json";
const FIXTURE_SCHEMA: &str = "plonky2-mle-cheating-prover-fixture-v3";
const CHECKED_IN_FIXTURE: &str = include_str!("../contracts/test/fixtures/v2_cheating_prover.json");

const ERR_GATE_TERMINAL: &str = "gate terminal equation failed";
const ERR_LOG_TERMINAL: &str = "norm/logUp terminal equation failed";
const ERR_ROOT_PIN: &str = "preprocessed root is not VK-bound";

// ---------------------------------------------------------------------------
// Fixture schema
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CheatingProverFixture {
    schema: String,
    description: String,
    circuit: CircuitRecord,
    /// Honest VK pins (same values the production config exporter emits).
    pinned_verifier: PinnedMleVerifierV2Fixture,
    /// Honest `abi.encode(MleVerifierV2.VerificationConfig)`.
    solidity_abi_verification_config: EncodedProofV2Fixture,
    compact_shape: CompactV2ShapeFixture,
    /// Positive control: an honest proof for the same circuit and VK.
    honest: ProofRecord,
    cases: Vec<CheatingCaseRecord>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CircuitRecord {
    builder: String,
    relation: String,
    degree_bits: usize,
    num_public_inputs: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProofRecord {
    name: String,
    solidity_abi_proof: EncodedProofV2Fixture,
    compact_proof: EncodedProofV2Fixture,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CheatingCaseRecord {
    name: String,
    description: String,
    /// Which table entry was tampered, for humans reading the JSON.
    tamper: String,
    /// Substring of the `mle_verify_v2` error for this case.
    expected_rust_error: String,
    /// Whether the proof's preprocessed root still equals the VK pin (true for
    /// every case except the preprocessed-root mismatch).
    preprocessed_root_matches_vk: bool,
    solidity_abi_proof: EncodedProofV2Fixture,
    compact_proof: EncodedProofV2Fixture,
}

// ---------------------------------------------------------------------------
// Circuit and honest tables
// ---------------------------------------------------------------------------

struct Honest {
    circuit: CircuitData<F, C, D>,
    vk: MleVerificationKeyV2<F>,
    tables: EvaluationTables<F>,
}

/// Same builder as `v2_cross_language_fixture::build_small_mul`.
fn build_small_mul() -> Honest {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let x = builder.add_virtual_target();
    let mut current = x;
    for _ in 0..5 {
        current = builder.mul(current, x);
    }
    builder.register_public_input(current);
    let circuit = builder.build::<C>();
    let mut witness = PartialWitness::new();
    witness.set_target(x, F::from_canonical_u64(2)).unwrap();
    let mut timing = TimingTree::default();
    let tables = extract_evaluation_tables::<F, C, D>(
        &circuit.prover_only,
        &circuit.common,
        witness,
        &mut timing,
    )
    .expect("evaluation-table extraction");
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    Honest {
        circuit,
        vk,
        tables,
    }
}

fn clone_tables(tables: &EvaluationTables<F>) -> EvaluationTables<F> {
    EvaluationTables {
        wire_values: tables.wire_values.clone(),
        constant_values: tables.constant_values.clone(),
        sigma_values: tables.sigma_values.clone(),
        public_inputs: tables.public_inputs.clone(),
        public_input_wires: tables.public_input_wires.clone(),
        public_inputs_hash: tables.public_inputs_hash,
        num_wires: tables.num_wires,
        num_routed_wires: tables.num_routed_wires,
        k_is: tables.k_is.clone(),
        subgroup: tables.subgroup.clone(),
        degree: tables.degree,
        degree_bits: tables.degree_bits,
    }
}

fn prove(honest: &Honest, tables: &EvaluationTables<F>) -> MleProofV2<F> {
    mle_prove_v2_from_tables(&honest.circuit.common, tables, &honest.vk.circuit_digest)
        .expect("the table-level prover accepts any self-consistent tables")
}

fn verify(honest: &Honest, proof: &MleProofV2<F>) -> Result<(), String> {
    mle_verify_v2::<F, D>(&honest.circuit.common, &honest.vk, proof).map_err(|e| e.to_string())
}

// ---------------------------------------------------------------------------
// Relation oracles over the tables (Plonky2's own gate evaluator; sigma as a
// permutation of `(value, position)` pairs)
// ---------------------------------------------------------------------------

fn gate_constraints_at_row(
    circuit: &CircuitData<F, C, D>,
    tables: &EvaluationTables<F>,
    row: usize,
) -> Vec<FE> {
    let local_constants: Vec<FE> = tables.constant_values[row]
        .iter()
        .map(|&value| FE::from(value))
        .collect();
    let local_wires: Vec<FE> = (0..tables.num_wires)
        .map(|column| FE::from(tables.wire_values[column][row]))
        .collect();
    let public_inputs_hash: HashOut<F> = tables.public_inputs_hash;
    let vars = EvaluationVars {
        local_constants: &local_constants,
        local_wires: &local_wires,
        public_inputs_hash: &public_inputs_hash,
    };
    evaluate_gate_constraints::<F, D>(&circuit.common, vars)
}

fn all_gate_constraints_hold(circuit: &CircuitData<F, C, D>, tables: &EvaluationTables<F>) -> bool {
    (0..tables.degree).all(|row| {
        gate_constraints_at_row(circuit, tables, row)
            .iter()
            .all(|value| *value == FE::ZERO)
    })
}

fn identity(tables: &EvaluationTables<F>, row: usize, column: usize) -> F {
    tables.k_is[column] * tables.subgroup[row]
}

fn is_singleton(tables: &EvaluationTables<F>, row: usize, column: usize) -> bool {
    tables.sigma_values[row][column] == identity(tables, row, column)
}

/// The routed cell `sigma(row, column)` points at.
fn sigma_target(tables: &EvaluationTables<F>, row: usize, column: usize) -> (usize, usize) {
    let target = tables.sigma_values[row][column];
    for r in 0..tables.degree {
        for c in 0..tables.num_routed_wires {
            if identity(tables, r, c) == target {
                return (r, c);
            }
        }
    }
    panic!("sigma({row}, {column}) does not point at a routed cell");
}

/// Multiset `{(wire value, sigma)}` versus `{(wire value, identity)}`: the
/// exact relation the norm/logUp lane enforces.
fn permutation_relation_holds(tables: &EvaluationTables<F>) -> bool {
    let mut lhs = Vec::new();
    let mut rhs = Vec::new();
    for row in 0..tables.degree {
        for column in 0..tables.num_routed_wires {
            let value = tables.wire_values[column][row].to_canonical_u64();
            lhs.push((value, tables.sigma_values[row][column].to_canonical_u64()));
            rhs.push((value, identity(tables, row, column).to_canonical_u64()));
        }
    }
    lhs.sort_unstable();
    rhs.sort_unstable();
    lhs == rhs
}

fn is_public_input_cell(tables: &EvaluationTables<F>, row: usize, column: usize) -> bool {
    tables
        .public_input_wires
        .iter()
        .any(|wire| wire.row == row && wire.column == column)
}

// ---------------------------------------------------------------------------
// The four cheating provers
// ---------------------------------------------------------------------------

struct Cheat {
    name: &'static str,
    description: &'static str,
    tamper: String,
    expected_rust_error: &'static str,
    preprocessed_root_matches_vk: bool,
    tables: EvaluationTables<F>,
}

/// (a) One singleton routed cell on a gate row is bumped. The cell is its own
/// sigma fixed point, so the permutation multiset is unchanged and only the
/// gate relation is violated.
fn cheat_gate_violation_only(honest: &Honest) -> Cheat {
    let base = &honest.tables;
    for row in 0..base.degree {
        for column in 0..base.num_routed_wires {
            if !is_singleton(base, row, column) || is_public_input_cell(base, row, column) {
                continue;
            }
            let mut tables = clone_tables(base);
            tables.wire_values[column][row] += F::ONE;
            if all_gate_constraints_hold(&honest.circuit, &tables) {
                continue; // unconstrained cell, not a violation
            }
            assert!(
                permutation_relation_holds(&tables),
                "a singleton cell must keep the permutation relation"
            );
            return Cheat {
                name: "gate_violation_only",
                description: "one singleton routed witness cell bumped by one: the gate relation \
                              is violated while the copy relation, the public inputs and the \
                              preprocessed commitment stay honest",
                tamper: format!("wire_values[column {column}][row {row}] += 1"),
                expected_rust_error: ERR_GATE_TERMINAL,
                preprocessed_root_matches_vk: true,
                tables,
            };
        }
    }
    panic!("no gate-constrained singleton routed cell found");
}

/// (b) One cell of a non-trivial copy class is bumped at a position no gate
/// constraint reads (the zero-weighted addend column of a `mul`). Every gate
/// constraint still holds; only the copy relation is violated.
fn cheat_copy_constraint_violation_only(honest: &Honest) -> Cheat {
    let base = &honest.tables;
    for row in 0..base.degree {
        for column in 0..base.num_routed_wires {
            if is_singleton(base, row, column) || is_public_input_cell(base, row, column) {
                continue;
            }
            let mut tables = clone_tables(base);
            tables.wire_values[column][row] += F::ONE;
            if !all_gate_constraints_hold(&honest.circuit, &tables) {
                continue;
            }
            assert!(!permutation_relation_holds(&tables));
            return Cheat {
                name: "copy_constraint_violation_only",
                description: "one routed witness cell inside a copy class bumped by one at a \
                              column no gate constraint reads: every gate constraint still holds \
                              and only the permutation (norm/logUp) relation is violated",
                tamper: format!("wire_values[column {column}][row {row}] += 1"),
                expected_rust_error: ERR_LOG_TERMINAL,
                preprocessed_root_matches_vk: true,
                tables,
            };
        }
    }
    panic!("no gate-free copy-class cell found");
}

/// (c) Two sigma entries of cells in the same copy class are swapped. The
/// cells hold equal values, so the permutation multiset relation still holds
/// with the honest witness and every gate constraint is untouched. The prover
/// commits this sigma table, so its preprocessed root differs from the VK's:
/// the VK root pin is the only check that can reject the proof.
fn cheat_preprocessed_root_mismatch(honest: &Honest) -> Cheat {
    let base = &honest.tables;
    for row in 0..base.degree {
        for column in 0..base.num_routed_wires {
            if is_singleton(base, row, column) {
                continue;
            }
            let (target_row, target_column) = sigma_target(base, row, column);
            assert_eq!(
                base.wire_values[column][row], base.wire_values[target_column][target_row],
                "honest copy classes hold equal values"
            );
            let mut tables = clone_tables(base);
            let a = tables.sigma_values[row][column];
            let b = tables.sigma_values[target_row][target_column];
            tables.sigma_values[row][column] = b;
            tables.sigma_values[target_row][target_column] = a;
            assert_ne!(tables.sigma_values, base.sigma_values);
            assert!(permutation_relation_holds(&tables));
            assert!(all_gate_constraints_hold(&honest.circuit, &tables));
            return Cheat {
                name: "preprocessed_root_mismatch",
                description: "sigma entries of two cells in the same copy class swapped: the \
                              honest witness still satisfies the rerouted permutation and every \
                              gate; the prover commits and opens its own preprocessed table, so \
                              only the VK preprocessed-root pin can reject the proof",
                tamper: format!(
                    "swap sigma_values[row {row}][column {column}] <-> \
                     sigma_values[row {target_row}][column {target_column}]"
                ),
                expected_rust_error: ERR_ROOT_PIN,
                preprocessed_root_matches_vk: false,
                tables,
            };
        }
    }
    panic!("no non-trivial copy class found");
}

/// (d) The claimed public input is changed while the witness cell the VK's
/// public-input wire map points at keeps the honest value. The prover hashes
/// the forged statement exactly like the verifier does.
fn cheat_public_input_mismatch(honest: &Honest) -> Cheat {
    let mut tables = clone_tables(&honest.tables);
    tables.public_inputs[0] += F::ONE;
    tables.public_inputs_hash = PoseidonHash::hash_no_pad(&tables.public_inputs);
    assert!(permutation_relation_holds(&tables));
    Cheat {
        name: "public_input_mismatch",
        description: "public_inputs[0] bumped by one while the mapped witness cell keeps the \
                      honest value (the public-input hash is recomputed for the forged \
                      statement, as the verifier does)",
        tamper: "public_inputs[0] += 1; public_inputs_hash = poseidon(public_inputs)".to_string(),
        // The log lane's D_PI binding fires first in both verifiers; the gate
        // lane is also violated (the in-circuit Poseidon hash of the public
        // inputs no longer matches the PublicInputGate wires).
        expected_rust_error: ERR_LOG_TERMINAL,
        preprocessed_root_matches_vk: true,
        tables,
    }
}

fn all_cheats(honest: &Honest) -> Vec<Cheat> {
    vec![
        cheat_gate_violation_only(honest),
        cheat_copy_constraint_violation_only(honest),
        cheat_preprocessed_root_mismatch(honest),
        cheat_public_input_mismatch(honest),
    ]
}

// ---------------------------------------------------------------------------
// Non-verifying export (test-only; never for deployment artifacts)
// ---------------------------------------------------------------------------

/// Encode a proof into the Solidity ABI and compact views WITHOUT verifying
/// it. The production exporter `try_export_mle_v2_fixture` runs
/// `mle_verify_v2` first and refuses invalid proofs; cheating fixtures need
/// exactly those bytes, so this test-local helper assembles them from the
/// public encoders. It must never be used for an honest deployment artifact.
fn export_cheating_fixture_unverified(
    name: &str,
    proof: &MleProofV2<F>,
    shape: &CompactV2Shape,
) -> ProofRecord {
    let view = MleProofV2Fixture::encode(proof);
    let abi = solidity_abi_encode_mle_proof_v2(&view).expect("Solidity ABI proof encoding");
    let compact = encode_compact_v2(proof, shape).expect("compact-v2 proof encoding");
    let decoded = decode_compact_v2::<F>(&compact, shape).expect("compact-v2 proof decoding");
    assert_eq!(
        MleProofV2Fixture::encode(&decoded),
        view,
        "compact bytes must round-trip the exact proof the ABI bytes carry"
    );
    ProofRecord {
        name: name.to_string(),
        solidity_abi_proof: EncodedProofV2Fixture::from_bytes(SOLIDITY_MLE_PROOF_ENCODING_V2, &abi),
        compact_proof: EncodedProofV2Fixture::from_bytes(
            std::str::from_utf8(&COMPACT_MAGIC_V2).expect("compact-v2 magic is ASCII"),
            &compact,
        ),
    }
}

fn build_fixture() -> CheatingProverFixture {
    let honest = build_small_mul();
    let config = try_export_mle_v2_config_fixture(&honest.circuit)
        .expect("honest deployment configuration export");
    let shape = compact_v2_shape_for_common(&honest.circuit.common, honest.vk.constituent_width)
        .expect("canonical compact-v2 shape");
    assert_eq!(CompactV2ShapeFixture::encode(&shape), config.compact_shape);

    let honest_proof = prove(&honest, &honest.tables);
    verify(&honest, &honest_proof).expect("honest table-level proof verifies");
    let honest_record = export_cheating_fixture_unverified("honest", &honest_proof, &shape);

    let cases = all_cheats(&honest)
        .into_iter()
        .map(|cheat| {
            let proof = prove(&honest, &cheat.tables);
            let error = verify(&honest, &proof).expect_err("cheating proof must be rejected");
            assert!(
                error.contains(cheat.expected_rust_error),
                "{}: expected `{}`, got `{error}`",
                cheat.name,
                cheat.expected_rust_error
            );
            let record = export_cheating_fixture_unverified(cheat.name, &proof, &shape);
            CheatingCaseRecord {
                name: cheat.name.to_string(),
                description: cheat.description.to_string(),
                tamper: cheat.tamper,
                expected_rust_error: cheat.expected_rust_error.to_string(),
                preprocessed_root_matches_vk: cheat.preprocessed_root_matches_vk,
                solidity_abi_proof: record.solidity_abi_proof,
                compact_proof: record.compact_proof,
            }
        })
        .collect();

    CheatingProverFixture {
        schema: FIXTURE_SCHEMA.to_string(),
        description: "Proofs whose WHIR/transcript part is honest but whose committed tables \
                      violate exactly one relation. Generated by \
                      mle/tests/cheating_prover_fixtures.rs::regenerate_v2_cheating_prover_fixture \
                      through a NON-verifying export path; never a deployment artifact."
            .to_string(),
        circuit: CircuitRecord {
            builder: "CircuitConfig::standard_recursion_config()".to_string(),
            relation: "public = x^6".to_string(),
            degree_bits: honest.circuit.common.degree_bits(),
            num_public_inputs: honest.circuit.common.num_public_inputs,
        },
        pinned_verifier: config.pinned_verifier,
        solidity_abi_verification_config: config.solidity_abi_verification_config,
        compact_shape: config.compact_shape,
        honest: honest_record,
        cases,
    }
}

fn fixture_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_RELATIVE_PATH)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Each cheating prover is rejected by exactly the targeted native check, and
/// the honest control from the same tables verifies.
#[test]
fn cheating_provers_are_rejected_by_the_targeted_terminal_or_pin() {
    let honest = build_small_mul();
    let honest_proof = prove(&honest, &honest.tables);
    verify(&honest, &honest_proof).expect("honest table-level proof verifies");
    assert_eq!(
        honest_proof.preprocessed_root, honest.vk.preprocessed_commitment_root,
        "honest prover commits the VK-pinned preprocessed root"
    );

    let cheats = all_cheats(&honest);
    assert_eq!(cheats.len(), 4);
    for cheat in &cheats {
        let proof = prove(&honest, &cheat.tables);
        // The PCS side is honest for every cheating prover: the witness and
        // norm-inverse commitments open to exactly what the sumchecks used,
        // and every case but (c) also commits the honest preprocessed root.
        assert_eq!(
            proof.preprocessed_root == honest.vk.preprocessed_commitment_root,
            cheat.preprocessed_root_matches_vk,
            "{}: preprocessed root pin expectation",
            cheat.name
        );
        assert_eq!(proof.circuit_digest, honest.vk.circuit_digest);
        let error = verify(&honest, &proof).expect_err("cheating proof must be rejected");
        println!("{}: {error}", cheat.name);
        assert!(
            error.contains(cheat.expected_rust_error),
            "{}: expected `{}`, got `{error}`",
            cheat.name,
            cheat.expected_rust_error
        );
    }
}

/// The copy-only and root-mismatch cheats really leave every gate satisfied,
/// and the gate-only cheat really leaves the permutation relation satisfied:
/// the oracle assertions that make the "exactly one relation" claim precise.
#[test]
fn cheating_tables_violate_exactly_one_relation() {
    let honest = build_small_mul();
    assert!(all_gate_constraints_hold(&honest.circuit, &honest.tables));
    assert!(permutation_relation_holds(&honest.tables));

    let cheats = all_cheats(&honest);
    let gate = &cheats[0];
    assert_eq!(gate.name, "gate_violation_only");
    assert!(!all_gate_constraints_hold(&honest.circuit, &gate.tables));
    assert!(permutation_relation_holds(&gate.tables));
    assert_eq!(gate.tables.sigma_values, honest.tables.sigma_values);
    assert_eq!(gate.tables.public_inputs, honest.tables.public_inputs);

    let copy = &cheats[1];
    assert_eq!(copy.name, "copy_constraint_violation_only");
    assert!(all_gate_constraints_hold(&honest.circuit, &copy.tables));
    assert!(!permutation_relation_holds(&copy.tables));
    assert_eq!(copy.tables.sigma_values, honest.tables.sigma_values);
    assert_eq!(copy.tables.public_inputs, honest.tables.public_inputs);

    let root = &cheats[2];
    assert_eq!(root.name, "preprocessed_root_mismatch");
    assert!(all_gate_constraints_hold(&honest.circuit, &root.tables));
    assert!(permutation_relation_holds(&root.tables));
    assert_eq!(root.tables.wire_values, honest.tables.wire_values);
    assert_eq!(root.tables.constant_values, honest.tables.constant_values);
    assert_ne!(root.tables.sigma_values, honest.tables.sigma_values);

    let pi = &cheats[3];
    assert_eq!(pi.name, "public_input_mismatch");
    assert_eq!(pi.tables.wire_values, honest.tables.wire_values);
    assert_ne!(pi.tables.public_inputs, honest.tables.public_inputs);
    assert_eq!(
        pi.tables.public_input_wires,
        honest.tables.public_input_wires
    );
}

/// The checked-in JSON decodes to proofs that the native verifier rejects for
/// exactly the recorded reason (and accepts for the honest control), and its
/// ABI/compact views and honest configuration bytes match a fresh export.
#[test]
fn checked_in_cheating_fixture_matches_the_native_verdicts() {
    let fixture: CheatingProverFixture =
        serde_json::from_str(CHECKED_IN_FIXTURE).expect("checked-in cheating fixture parses");
    assert_eq!(fixture.schema, FIXTURE_SCHEMA);

    let honest = build_small_mul();
    let config = try_export_mle_v2_config_fixture(&honest.circuit)
        .expect("honest deployment configuration export");
    assert_eq!(fixture.pinned_verifier, config.pinned_verifier);
    assert_eq!(
        fixture.solidity_abi_verification_config,
        config.solidity_abi_verification_config
    );
    assert_eq!(fixture.compact_shape, config.compact_shape);
    assert_eq!(
        fixture.circuit.degree_bits,
        honest.circuit.common.degree_bits()
    );
    assert_eq!(
        fixture.circuit.num_public_inputs,
        honest.circuit.common.num_public_inputs
    );
    fixture
        .solidity_abi_verification_config
        .decode_and_validate(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2)
        .expect("config bytes carry their own integrity metadata");
    let shape = fixture.compact_shape.decode();

    let decode =
        |record_name: &str, abi: &EncodedProofV2Fixture, compact: &EncodedProofV2Fixture| {
            let compact_bytes = compact
                .decode_and_validate(std::str::from_utf8(&COMPACT_MAGIC_V2).unwrap())
                .unwrap_or_else(|e| panic!("{record_name}: compact record integrity: {e:?}"));
            let proof = decode_compact_v2::<F>(&compact_bytes, &shape)
                .unwrap_or_else(|e| panic!("{record_name}: compact decode: {e:?}"));
            let abi_bytes = abi
                .decode_and_validate(SOLIDITY_MLE_PROOF_ENCODING_V2)
                .unwrap_or_else(|e| panic!("{record_name}: ABI record integrity: {e:?}"));
            let reencoded = solidity_abi_encode_mle_proof_v2(&MleProofV2Fixture::encode(&proof))
                .expect("ABI re-encoding");
            assert_eq!(
                reencoded, abi_bytes,
                "{record_name}: ABI bytes and compact bytes must carry the same proof"
            );
            proof
        };

    let honest_proof = decode(
        "honest",
        &fixture.honest.solidity_abi_proof,
        &fixture.honest.compact_proof,
    );
    verify(&honest, &honest_proof).expect("checked-in honest control verifies");

    let expected_names = [
        "gate_violation_only",
        "copy_constraint_violation_only",
        "preprocessed_root_mismatch",
        "public_input_mismatch",
    ];
    assert_eq!(fixture.cases.len(), expected_names.len());
    for (case, expected_name) in fixture.cases.iter().zip(expected_names) {
        assert_eq!(case.name, expected_name);
        let proof = decode(&case.name, &case.solidity_abi_proof, &case.compact_proof);
        assert_eq!(
            proof.preprocessed_root == honest.vk.preprocessed_commitment_root,
            case.preprocessed_root_matches_vk,
            "{}: recorded root-pin expectation",
            case.name
        );
        let error = verify(&honest, &proof).expect_err("checked-in cheating proof is rejected");
        assert!(
            error.contains(&case.expected_rust_error),
            "{}: expected `{}`, got `{error}`",
            case.name,
            case.expected_rust_error
        );
    }
}

/// Rewrite `contracts/test/fixtures/v2_cheating_prover.json`.
///
/// `cargo test --offline -p plonky2_mle --test cheating_prover_fixtures \
///     regenerate_v2_cheating_prover_fixture -- --ignored`
#[test]
#[ignore = "writes the cheating-prover snapshot only on explicit opt-in"]
fn regenerate_v2_cheating_prover_fixture() {
    let fixture = build_fixture();
    let mut json = serde_json::to_string_pretty(&fixture).expect("serialize cheating fixture");
    json.push('\n');
    std::fs::write(fixture_path(), json).expect("write cheating-prover fixture");
}
