use ark_ff::{AdditiveGroup, PrimeField};
use whir::algebra::fields::{Field64, Field64_3};

fn ext(seed: u64) -> Field64_3 {
    Field64_3::new(
        Field64::from(seed),
        Field64::from(3 * seed + 1),
        Field64::from(5 * seed + 2),
    )
}

fn sequence(length: usize, start: u64) -> Vec<Field64_3> {
    (0..length).map(|index| ext(start + index as u64)).collect()
}

/// Independent specification implementation of the packed constituent-index
/// fold. It intentionally uses WHIR's Field64_3 arithmetic directly, so the
/// fixed limbs below are a cross-language oracle for PackedClaimExt3.sol.
fn fold_ext3(values: &[Field64_3], width: usize, point: &[Field64_3]) -> Field64_3 {
    assert!(width > 0 && width <= 160);
    assert!(values.len() <= width);
    assert_eq!(
        point.len(),
        width.next_power_of_two().trailing_zeros() as usize
    );

    let mut layer = vec![Field64_3::ZERO; width.next_power_of_two()];
    layer[..values.len()].copy_from_slice(values);
    for &challenge in point {
        for index in 0..layer.len() / 2 {
            layer[index] = layer[2 * index] + challenge * (layer[2 * index + 1] - layer[2 * index]);
        }
        layer.truncate(layer.len() / 2);
    }
    layer[0]
}

fn limbs(value: Field64_3) -> [u64; 3] {
    [
        value.c0.into_bigint().0[0],
        value.c1.into_bigint().0[0],
        value.c2.into_bigint().0[0],
    ]
}

#[test]
fn rust_reference_for_solidity_v2_five_cell_vector() {
    // numConstants=1, numRoutedWires=2, numWires=5 gives the non-power-of-two
    // width max(3, 5, 4)=5 and therefore exercises zero padding through slot 7.
    let width = 5;
    let log_point = [ext(101), ext(103), ext(107)];
    let gate_point = [ext(109), ext(113), ext(127)];
    let claims = [
        sequence(3, 2),
        sequence(5, 11),
        sequence(4, 23),
        sequence(3, 37),
        sequence(5, 47),
    ];
    let expected = [
        fold_ext3(&claims[0], width, &log_point),
        fold_ext3(&claims[1], width, &log_point),
        fold_ext3(&claims[2], width, &log_point),
        fold_ext3(&claims[3], width, &gate_point),
        fold_ext3(&claims[4], width, &gate_point),
    ];

    assert_eq!(
        expected.map(limbs),
        [
            [
                0x0000_000b_213f_b740,
                0x0000_000a_96ee_c832,
                0x0000_0007_a03d_794a
            ],
            [
                0x0000_001f_f57a_16ae,
                0x0000_001e_57bb_10da,
                0x0000_0015_df2a_a962
            ],
            [
                0xffff_fffe_fe8b_0783,
                0xffff_fffe_ff25_c655,
                0xffff_fffe_ff07_0d05
            ],
            [
                0x0000_0076_21c0_21a4,
                0x0000_0070_02e7_779a,
                0x0000_0050_cf4c_063c
            ],
            [
                0x0000_0096_3511_766a,
                0x0000_008e_75f5_235a,
                0x0000_0066_bf82_35f0
            ],
        ]
    );

    // The V2 implementation's wire-v3 protocol uses the first five cells of a
    // 2-point x 3-group Cartesian
    // matrix and leaves (gate, norm-inverse) unused.
    assert_eq!(0x1f_u8.count_ones(), 5);
}

#[test]
fn rust_reference_is_lsb_first_and_preserves_nonbase_limbs() {
    let values = sequence(5, 2);
    let point = [ext(101), ext(103), ext(107)];
    let expected = fold_ext3(&values, 5, &point);

    let mut changed_c1 = values.clone();
    changed_c1[4].c1 += Field64::from(1u64);
    assert_ne!(fold_ext3(&changed_c1, 5, &point), expected);

    let mut changed_c2 = values.clone();
    changed_c2[4].c2 += Field64::from(1u64);
    assert_ne!(fold_ext3(&changed_c2, 5, &point), expected);

    let reversed = [point[2], point[1], point[0]];
    assert_ne!(fold_ext3(&values, 5, &reversed), expected);
}
