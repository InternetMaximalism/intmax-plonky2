use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::Field;
use plonky2::hash::poseidon::{Poseidon, PoseidonHash};
use plonky2::plonk::config::Hasher;

/// Independent source of truth for the Solidity rate-boundary vectors. The
/// 103-element case exercises 13 permutations and a final seven-element short
/// chunk, including Plonky2's overwrite-without-padding behavior.
#[test]
fn sequential_hash_no_pad_rate_boundary_vectors() {
    let vectors = [
        (0, [0, 0, 0, 0]),
        (
            1,
            [
                4_330_397_376_401_421_145,
                14_124_799_381_142_128_323,
                8_742_572_140_681_234_676,
                14_345_658_006_221_440_202,
            ],
        ),
        (
            7,
            [
                13_371_083_541_496_999_660,
                7_739_921_955_450_379_130,
                10_572_004_275_396_999_076,
                3_599_502_497_184_312_851,
            ],
        ),
        (
            8,
            [
                17_291_601_223_193_097_753,
                9_133_441_755_544_524_598,
                17_736_579_132_324_177_718,
                14_132_891_516_240_416_332,
            ],
        ),
        (
            9,
            [
                18_007_381_329_477_297_286,
                11_010_590_292_829_788_888,
                258_931_329_831_288_973,
                9_046_877_563_820_385_107,
            ],
        ),
        (
            103,
            [
                17_287_484_645_839_759_726,
                2_836_085_724_020_267_508,
                11_420_194_361_566_745_580,
                12_353_543_096_432_783_826,
            ],
        ),
    ];

    for (length, expected) in vectors {
        let inputs = (0..length)
            .map(GoldilocksField::from_canonical_usize)
            .collect::<Vec<_>>();
        assert_eq!(
            PoseidonHash::hash_no_pad(&inputs).elements.map(|x| x.0),
            expected
        );
    }
}

/// All twelve outputs pin the exact circulant orientation and the sole
/// diagonal coefficient used by the Solidity integer-FFT MDS implementation.
#[test]
fn sequential_poseidon_mds_vector() {
    let state = core::array::from_fn(|i| GoldilocksField::from_canonical_usize(i));
    assert_eq!(
        <GoldilocksField as Poseidon>::mds_layer(&state).map(|x| x.0),
        [1496, 1512, 1360, 1400, 1188, 1288, 1388, 1308, 1540, 1604, 1368, 1444]
    );
}
