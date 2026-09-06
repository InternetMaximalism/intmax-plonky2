import Audit.Wire3.GoldilocksFoundation

/-!
# Exact orders for the fixed Goldilocks domain generator

This is a mathematical bridge for the FIXED construction
  g_k = 7^((p-1)/2^k), 0 <= k <= 32.
The full order of seven is proved from the existing six-factor certificate,
not assumed from an arbitrary shape-valid WHIR domain or from a Field trait.

Source correspondence: fixed WHIR 3db5dec uses FConfig64(generator=7,
small_subgroup_base=15), and ark-ff 0.5 get_root_of_unity produces this formula
on power-of-two sizes. Its NttEngine removes the unsupported factor five and
uses the same resulting root. This file does NOT formally translate those
Rust/Ark constructors, their macro expansion, or their machine arithmetic.
Nor does it prove that a digest-accepted config equals a canonical config,
the generated profile table's derivation, sampling probability, or WHIR soundness.

The independent transpose lemmas concern the exact Nat index formula used by
_computeEvalPoints and transpose_permute, with explicit dimensions and bounds.
-/
namespace Audit.Wire3.GoldilocksDomain
open Audit.Wire3

attribute [local instance 2000] instPowNat
local notation "p" => Arithmetic.modulus

theorem seven_full_power : (7 : ZMod p) ^ (p-1) = 1 :=
  GoldilocksFoundation.nat_mod_power_to_zmod 7 (p-1) 1 (by decide)
    GoldilocksCertificate.base_seven_full_power_value

theorem seven_prime_factor_powers_ne_one (q : Nat) (hq : q.Prime) (hd : q ∣ p-1) :
    (7 : ZMod p) ^ ((p-1)/q) ≠ 1 := by
  rcases GoldilocksFoundation.prime_divisor_cases q hq hd with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact GoldilocksFoundation.certificate_factor_power_ne_one 2 18446744069414584320 (by decide)
  · exact GoldilocksFoundation.certificate_factor_power_ne_one 3 18446744065119617025 (by decide)
  · exact GoldilocksFoundation.certificate_factor_power_ne_one 5 1373043270956696022 (by decide)
  · exact GoldilocksFoundation.certificate_factor_power_ne_one 17 16301593560560007290 (by decide)
  · exact GoldilocksFoundation.certificate_factor_power_ne_one 257 995085315851368103 (by decide)
  · exact GoldilocksFoundation.certificate_factor_power_ne_one 65537 8478886009461009681 (by decide)

theorem seven_order_exact : orderOf (7 : ZMod p) = p-1 :=
  orderOf_eq_of_pow_and_pow_div_prime (by decide) seven_full_power
    seven_prime_factor_powers_ne_one

theorem two_power_divides_modulus_minus_one (k : Nat) (hk : k ≤ 32) : 2^k ∣ p-1 := by
  exact dvd_trans (Nat.pow_dvd_pow 2 hk) (by decide)

def generator (k : Nat) : ZMod p := (7 : ZMod p) ^ ((p-1)/2^k)

theorem generator_order_exact (k : Nat) (hk : k ≤ 32) :
    orderOf (generator k) = 2^k := by
  have h := orderOf_pow_orderOf_div (x := (7 : ZMod p))
    (show orderOf (7 : ZMod p) ≠ 0 by rw [seven_order_exact]; decide)
    (show 2^k ∣ orderOf (7 : ZMod p) by
      rw [seven_order_exact]; exact two_power_divides_modulus_minus_one k hk)
  simpa only [seven_order_exact,generator] using h

theorem generator_full_power (k : Nat) (hk : k ≤ 32) :
    generator k ^ (2^k) = 1 := by
  rw [← generator_order_exact k hk]
  exact pow_orderOf_eq_one _

theorem generator_no_smaller_positive_power (k exponent : Nat) (hk : k ≤ 32)
    (hp : 0 < exponent) (hsmall : exponent < 2^k) : generator k ^ exponent ≠ 1 := by
  apply pow_ne_one_of_lt_orderOf (by omega)
  rw [generator_order_exact k hk]
  exact hsmall

theorem generator_power_eq_one_iff (k exponent : Nat) (hk : k ≤ 32) :
    generator k ^ exponent = 1 ↔ 2^k ∣ exponent := by
  rw [← orderOf_dvd_iff_pow_eq_one,generator_order_exact k hk]

theorem generator_nonzero (k : Nat) (hk : k ≤ 32) : generator k ≠ 0 := by
  intro hzero
  have h := generator_full_power k hk
  rw [hzero,zero_pow (show 2^k ≠ 0 from ne_of_gt (Nat.pow_pos (by decide)))] at h
  exact zero_ne_one h

def point (k : Nat) (index : Fin (2^k)) : ZMod p := generator k ^ index.val

theorem generator_powers_injective (k : Nat) (hk : k ≤ 32) :
    Function.Injective (point k) := by
  intro i j hij
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := generator k) ?_ ?_ hij
  · change i.val < orderOf (generator k)
    rw [generator_order_exact k hk]
    exact i.isLt
  · change j.val < orderOf (generator k)
    rw [generator_order_exact k hk]
    exact j.isLt

theorem canonical_point_values_injective (k : Nat) (hk : k ≤ 32) :
    Function.Injective (fun index : Fin (2^k) => (point k index).val) := by
  intro i j hij
  apply generator_powers_injective k hk
  exact ZMod.val_injective p hij

theorem generator_as_nat_residue (k : Nat) :
    generator k = ((7 ^ ((p-1)/2^k) % p : Nat) : ZMod p) := by
  simp only [generator,ZMod.natCast_mod,Nat.cast_pow,Nat.cast_ofNat]

theorem generator_canonical_value (k : Nat) :
    (generator k).val = 7 ^ ((p-1)/2^k) % p := by
  have h := congrArg ZMod.val (generator_as_nat_residue k)
  simpa only [ZMod.val_natCast,Nat.mod_mod] using h

theorem canonical_value_of_power (a : ZMod p) (exponent : Nat) :
    (a ^ exponent).val = a.val ^ exponent % p := by
  have h : ((a.val ^ exponent : Nat) : ZMod p) = a ^ exponent := by
    rw [Nat.cast_pow,ZMod.natCast_zmod_val]
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast] using hv.symm

theorem zero_bit_generator : generator 0 = 1 := by
  simpa [generator] using seven_full_power

theorem zero_bit_point (i : Fin (2^0)) : point 0 i = 1 := by
  simp [point,zero_bit_generator]

theorem one_bit_generator_value : (generator 1).val = p-1 := by
  rw [generator_canonical_value]
  have h := GoldilocksCertificate.each_factor_power_value 2 18446744069414584320 (by decide)
  simpa only [Nat.pow_one] using h

theorem maximum_two_adic_order : orderOf (generator 32) = 4294967296 :=
  generator_order_exact 32 (by decide)

/-- The source's row-major-to-column-major exponent permutation. -/
def transposeIndex (cosetSize numCosets index : Nat) : Nat :=
  index / cosetSize + (index % cosetSize) * numCosets

theorem transpose_index_bound (cosetSize numCosets index : Nat)
    (hc : 0 < cosetSize) (_hn : 0 < numCosets)
    (hi : index < cosetSize * numCosets) :
    transposeIndex cosetSize numCosets index < cosetSize * numCosets := by
  have hr : index / cosetSize < numCosets := by
    exact (Nat.div_lt_iff_lt_mul hc).mpr (by simpa [Nat.mul_comm] using hi)
  have hm := Nat.mod_lt index hc
  unfold transposeIndex
  have hmul : (index % cosetSize + 1) * numCosets ≤ cosetSize * numCosets :=
    Nat.mul_le_mul_right numCosets (by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hmul
  omega

theorem transpose_index_quotient (cosetSize numCosets index : Nat)
    (hc : 0 < cosetSize) (hn : 0 < numCosets)
    (hi : index < cosetSize * numCosets) :
    transposeIndex cosetSize numCosets index / numCosets = index % cosetSize := by
  have hr : index / cosetSize < numCosets :=
    (Nat.div_lt_iff_lt_mul hc).mpr (by simpa [Nat.mul_comm] using hi)
  simp only [transposeIndex,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt hr,Nat.zero_add]

theorem transpose_index_remainder (cosetSize numCosets index : Nat)
    (hc : 0 < cosetSize) (_hn : 0 < numCosets)
    (hi : index < cosetSize * numCosets) :
    transposeIndex cosetSize numCosets index % numCosets = index / cosetSize := by
  have hr : index / cosetSize < numCosets :=
    (Nat.div_lt_iff_lt_mul hc).mpr (by simpa [Nat.mul_comm] using hi)
  simp [transposeIndex,Nat.add_mod,Nat.mod_eq_of_lt hr]

theorem transpose_index_roundtrip (cosetSize numCosets index : Nat)
    (hc : 0 < cosetSize) (hn : 0 < numCosets)
    (hi : index < cosetSize * numCosets) :
    transposeIndex numCosets cosetSize (transposeIndex cosetSize numCosets index) = index := by
  change transposeIndex cosetSize numCosets index / numCosets +
    (transposeIndex cosetSize numCosets index % numCosets) * cosetSize = index
  rw [transpose_index_quotient cosetSize numCosets index hc hn hi,
    transpose_index_remainder cosetSize numCosets index hc hn hi]
  simpa [Nat.mul_comm] using Nat.mod_add_div index cosetSize

theorem transpose_index_injective (cosetSize numCosets : Nat)
    (hc : 0 < cosetSize) (hn : 0 < numCosets) :
    Function.Injective (fun i : Fin (cosetSize*numCosets) =>
      transposeIndex cosetSize numCosets i.val) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg (transposeIndex numCosets cosetSize) hij
  simpa only [transpose_index_roundtrip cosetSize numCosets i.val hc hn i.isLt,
    transpose_index_roundtrip cosetSize numCosets j.val hc hn j.isLt] using h

/-- The actual exponent formula composed with the fixed generator. No
arbitrary shape-valid generator is silently replaced by this definition. -/
def transposedPoint (k cosetSize numCosets : Nat) (index : Fin (2^k)) : ZMod p :=
  generator k ^ transposeIndex cosetSize numCosets index.val

/-- Explicit bridge to the Nat.mod power used for domain-point base limbs. -/
theorem transposed_point_canonical_value (k cosetSize numCosets : Nat) (index : Fin (2^k)) :
    (transposedPoint k cosetSize numCosets index).val =
      (generator k).val ^
        (index.val / cosetSize + (index.val % cosetSize) * numCosets) % p :=
  canonical_value_of_power _ _

theorem transposed_points_injective (k cosetSize numCosets : Nat) (hk : k ≤ 32)
    (hc : 0 < cosetSize) (hn : 0 < numCosets) (hsize : cosetSize*numCosets = 2^k) :
    Function.Injective (transposedPoint k cosetSize numCosets) := by
  intro i j hij
  have hi : i.val < cosetSize*numCosets := by rw [hsize]; exact i.isLt
  have hj : j.val < cosetSize*numCosets := by rw [hsize]; exact j.isLt
  have hip : transposeIndex cosetSize numCosets i.val < orderOf (generator k) := by
    rw [generator_order_exact k hk]
    simpa only [hsize] using transpose_index_bound cosetSize numCosets i.val hc hn hi
  have hjp : transposeIndex cosetSize numCosets j.val < orderOf (generator k) := by
    rw [generator_order_exact k hk]
    simpa only [hsize] using transpose_index_bound cosetSize numCosets j.val hc hn hj
  have hexp := pow_injOn_Iio_orderOf (x := generator k) hip hjp hij
  apply Fin.ext
  have h := congrArg (transposeIndex numCosets cosetSize) hexp
  simpa only [transpose_index_roundtrip cosetSize numCosets i.val hc hn hi,
    transpose_index_roundtrip cosetSize numCosets j.val hc hn hj] using h

theorem transposed_canonical_values_injective (k cosetSize numCosets : Nat) (hk : k ≤ 32)
    (hc : 0 < cosetSize) (hn : 0 < numCosets) (hsize : cosetSize*numCosets = 2^k) :
    Function.Injective (fun index : Fin (2^k) =>
      (transposedPoint k cosetSize numCosets index).val) := by
  intro i j hij
  apply transposed_points_injective k cosetSize numCosets hk hc hn hsize
  exact ZMod.val_injective p hij

theorem distinct_indices_give_distinct_points (k cosetSize numCosets : Nat) (hk : k ≤ 32)
    (hc : 0 < cosetSize) (hn : 0 < numCosets) (hsize : cosetSize*numCosets = 2^k)
    (i j : Fin (2^k)) (hne : i ≠ j) :
    transposedPoint k cosetSize numCosets i ≠ transposedPoint k cosetSize numCosets j := by
  intro h
  exact hne (transposed_points_injective k cosetSize numCosets hk hc hn hsize h)

theorem transpose_example :
    (List.range 8).map (transposeIndex 4 2) = [0,2,4,6,1,3,5,7] := by decide

theorem transpose_singleton_example : transposeIndex 1 1 0 = 0 := rfl

end Audit.Wire3.GoldilocksDomain
