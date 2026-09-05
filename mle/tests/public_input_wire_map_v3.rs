//! Release tests for the protocol-v3 direct public-input/witness map.

use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::plonk::prover::canonical_public_input_wires;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_mle::prover_v2::mle_setup_v2;
use plonky2_mle::vk_v2::{
    circuit_config_digest_v2, decode_public_input_wire_map_v2, public_input_wire_map_v2,
};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

#[test]
fn setup_rederives_row_major_canonical_map_and_preserves_pi_order_and_duplicates() {
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let x = builder.add_virtual_target();
    let y = builder.add_virtual_target();
    let product = builder.mul(x, y);
    // Duplicates are intentional protocol data, not a set. The third PI also
    // pins that reordering entries changes the byte-exact configuration.
    builder.register_public_input(product);
    builder.register_public_input(product);
    builder.register_public_input(x);
    let data = builder.build::<C>();

    let wires = canonical_public_input_wires(&data.prover_only, &data.common).unwrap();
    assert_eq!(wires.len(), 3);
    assert_eq!(
        wires[0], wires[1],
        "duplicate PI targets must stay duplicated"
    );

    // Independently scan each copy-equivalence class in the specified
    // row-major / routed-column order and compare setup's chosen coordinate.
    let degree = data.common.degree();
    let num_wires = data.common.config.num_wires;
    let num_routed = data.common.config.num_routed_wires;
    let mut saw_multiple_routed_members = false;
    for (&target, chosen) in data.prover_only.public_inputs.iter().zip(&wires) {
        let target_rep = data.prover_only.representative_map[target.index(num_wires, degree)];
        let routed_members = (0..degree)
            .flat_map(|row| (0..num_routed).map(move |column| (row, column)))
            .filter(|&(row, column)| {
                data.prover_only.representative_map[row * num_wires + column] == target_rep
            })
            .collect::<Vec<_>>();
        let expected = routed_members[0];
        saw_multiple_routed_members |= routed_members.len() > 1;
        assert_eq!((chosen.row, chosen.column), expected);
    }
    assert!(
        saw_multiple_routed_members,
        "fixture must exercise canonical selection within a multi-wire copy class"
    );

    let encoded = public_input_wire_map_v2(&data.prover_only, &data.common).unwrap();
    assert_eq!(encoded.len(), 9);
    assert_eq!(&encoded[0..3], &encoded[3..6]);
    let decoded = decode_public_input_wire_map_v2(&encoded, 3, degree, num_routed).unwrap();
    assert_eq!(
        decoded,
        wires
            .iter()
            .map(|wire| (wire.row, wire.column))
            .collect::<Vec<_>>()
    );

    let vk = mle_setup_v2::<F, C, D>(&data.prover_only, &data.common);
    assert_eq!(vk.public_input_wire_map, encoded);
    let canonical_digest = circuit_config_digest_v2(
        &data.common,
        &vk.circuit_digest,
        &vk.subgroup_gen_powers,
        &vk.gates,
        &encoded,
    )
    .unwrap();
    assert_eq!(canonical_digest, vk.circuit_config_digest);

    let mut reordered = encoded.clone();
    let third = reordered[6..9].to_vec();
    reordered.copy_within(0..6, 3);
    reordered[0..3].copy_from_slice(&third);
    assert_ne!(reordered, encoded);
    assert_ne!(
        circuit_config_digest_v2(
            &data.common,
            &vk.circuit_digest,
            &vk.subgroup_gen_powers,
            &vk.gates,
            &reordered,
        )
        .unwrap(),
        canonical_digest,
        "map order must be configuration-bound"
    );
}

#[test]
fn three_byte_decoder_fails_closed_on_length_row_and_column() {
    assert!(decode_public_input_wire_map_v2(&[0, 0], 1, 8, 4).is_err());
    assert!(decode_public_input_wire_map_v2(&[8, 0, 0], 1, 8, 4).is_err());
    assert!(decode_public_input_wire_map_v2(&[0, 0, 4], 1, 8, 4).is_err());
}

#[test]
fn default_103_public_input_sponge_spans_thirteen_canonical_rows() {
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    for _ in 0..103 {
        let target = builder.add_virtual_target();
        builder.register_public_input(target);
    }
    let data = builder.build::<C>();
    let wires = canonical_public_input_wires(&data.prover_only, &data.common).unwrap();
    assert_eq!(wires.len(), 103);
    assert_eq!(
        wires
            .iter()
            .map(|wire| (wire.row, wire.column))
            .collect::<Vec<_>>(),
        (0..103)
            .map(|index| (index / 8, index % 8))
            .collect::<Vec<_>>()
    );
    let mut rows = wires.iter().map(|wire| wire.row).collect::<Vec<_>>();
    rows.sort_unstable();
    rows.dedup();
    assert_eq!(rows, (0..13).collect::<Vec<_>>());
}
