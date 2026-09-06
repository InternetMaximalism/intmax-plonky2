import Audit.Wire3.ModularPower
import Audit.Wire3.WhirDomainBridge

/-!
# Bitwise rendering of the actual domain exponentiation loop

The source is SpongefishWhirVerify._glPow: initialize result=1, mask the
uint64 input, test the low bit, mulmod on that branch, shift right, then
square with mulmod. The Nat bit operations below are kept distinct from the
existing arithmetic exponentiation runner until their equality is proved.
The 256-step fuel is a proved exponent-bit bound, NOT a source guard or gas.

This is still a manually transcribed scalar loop. Fin input bounds and
intermediate canonical bounds are not a compiler/Yul/EVM refinement theorem.
No memory model, source parser, compiled bytecode, gas, config generation,
Hash/Fiat--Shamir distribution or PCS soundness is supplied here.
-/
namespace Audit.Wire3.WhirDomainPower
open Audit.Wire3

attribute [local instance 2000] instPowNat

def maskedBase (base : Nat) : Nat := base &&& (2^64-1)

def loop : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, exponent, acc => if exponent = 0 then some acc else none
  | fuel+1, base, exponent, acc =>
      if exponent = 0 then some acc else
        let nextAcc := if exponent &&& 1 = 0 then acc else Arithmetic.mul acc base
        let nextExponent := exponent >>> 1
        let nextBase := Arithmetic.mul base base
        loop fuel nextBase nextExponent nextAcc

theorem mask_is_low_64_bits (base : Nat) : maskedBase base = base % 2^64 :=
  Nat.and_pow_two_is_mod base 64

theorem mask_preserves_bounded_input (base : Nat) (h : base < 2^64) : maskedBase base = base := by
  rw [mask_is_low_64_bits,Nat.mod_eq_of_lt h]

theorem mask_always_bounded (base : Nat) : maskedBase base < 2^64 := by
  rw [mask_is_low_64_bits]
  exact Nat.mod_lt _ (by decide)

theorem bit_test_is_arithmetic_branch (exponent acc base : Nat) :
    (if exponent &&& 1 = 0 then acc else Arithmetic.mul acc base) =
      (if exponent % 2 = 1 then Arithmetic.mul acc base else acc) := by
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one exponent with h | h <;> simp [h]

theorem shift_is_integer_halving (exponent : Nat) : exponent >>> 1 = exponent / 2 := by
  simpa only [Nat.pow_one] using Nat.shiftRight_eq_div_pow exponent 1

theorem bitwise_loop_equals_existing_power_loop (fuel base exponent acc : Nat) :
    loop fuel base exponent acc = WhirFinal.modPowLoop fuel base exponent acc := by
  induction fuel generalizing base exponent acc with
  | zero => rfl
  | succ fuel ih =>
      simp only [loop,WhirFinal.modPowLoop,bit_test_is_arithmetic_branch,shift_is_integer_halving,ih]

theorem loop_success_exact (fuel base exponent acc result : Nat) (ha : acc < Arithmetic.modulus)
    (h : loop fuel base exponent acc = some result) :
    result = acc * base^exponent % Arithmetic.modulus := by
  rw [bitwise_loop_equals_existing_power_loop] at h
  exact ModularPower.mod_pow_success_exact fuel base exponent acc result ha h

theorem loop_success_canonical (fuel base exponent acc result : Nat) (ha : acc < Arithmetic.modulus)
    (h : loop fuel base exponent acc = some result) : result < Arithmetic.modulus := by
  rw [bitwise_loop_equals_existing_power_loop] at h
  exact ModularPower.mod_pow_success_canonical fuel base exponent acc result ha h

theorem loop_has_output_iff_bit_budget (fuel base exponent acc : Nat) :
    (∃ result, loop fuel base exponent acc = some result) ↔ exponent < 2^fuel := by
  rw [bitwise_loop_equals_existing_power_loop]
  exact ModularPower.mod_pow_has_output_iff_bit_fuel fuel base exponent acc

theorem bounded_exponent_executes (base exponent : Nat) (he : exponent < 2^256) :
    loop 256 (maskedBase base) exponent 1 =
      some ((base % 2^64)^exponent % Arithmetic.modulus) := by
  rw [bitwise_loop_equals_existing_power_loop,mask_is_low_64_bits]
  simpa only [Nat.one_mul] using
    ModularPower.mod_pow_exact_with_sufficient_bits 256 (base % 2^64) exponent 1 (by decide) he

abbrev BaseWord := Fin (2^64)
abbrev ExponentWord := Fin (2^256)

def glPow (base : BaseWord) (exponent : ExponentWord) : Option Nat :=
  loop 256 (maskedBase base.val) exponent.val 1

theorem typed_power_exact (base : BaseWord) (exponent : ExponentWord) :
    glPow base exponent = some (base.val^exponent.val % Arithmetic.modulus) := by
  simpa only [glPow,Nat.mod_eq_of_lt base.isLt] using bounded_exponent_executes base.val exponent.val exponent.isLt

theorem typed_power_always_executes (base : BaseWord) (exponent : ExponentWord) :
    ∃ result, glPow base exponent = some result ∧ result < Arithmetic.modulus ∧ result < 2^64 := by
  have h : base.val^exponent.val % Arithmetic.modulus < Arithmetic.modulus :=
    Nat.mod_lt _ Arithmetic.modulus_positive
  exact ⟨_,typed_power_exact base exponent,h,h.trans Arithmetic.modulus_below_u64⟩

theorem multiply_square_intermediates_canonical (acc base : Nat) :
    Arithmetic.mul acc base < Arithmetic.modulus ∧ Arithmetic.mul base base < Arithmetic.modulus :=
  ⟨Arithmetic.reduce_canonical _,Arithmetic.reduce_canonical _⟩

theorem branch_accumulator_canonical (acc base exponent : Nat) (ha : acc < Arithmetic.modulus) :
    (if exponent &&& 1 = 0 then acc else Arithmetic.mul acc base) < Arithmetic.modulus := by
  split
  · exact ha
  · exact Arithmetic.reduce_canonical _

def transposedExponent (o : WhirIntermediate.OpenParams) (index : Nat) : Nat :=
  index / o.cosetSize + (index % o.cosetSize)*o.numCosets

def domainPoint (o : WhirIntermediate.OpenParams) (index : Nat) : Option Arithmetic.Ext3 :=
  (loop 256 (maskedBase o.domainGenerator.val) (transposedExponent o index) 1).map Arithmetic.fromBase

theorem actual_generator_fits_input_word (o : WhirIntermediate.OpenParams) :
    o.domainGenerator.val < 2^64 := o.domainGenerator.isLt.trans Arithmetic.modulus_below_u64

theorem bounded_domain_point_equals_existing_point (o : WhirIntermediate.OpenParams) (index : Nat)
    (he : transposedExponent o index < 2^256) :
    domainPoint o index = some (WhirIntermediate.domainPoint o index) := by
  unfold domainPoint
  rw [bounded_exponent_executes o.domainGenerator.val (transposedExponent o index) he,
    Nat.mod_eq_of_lt (actual_generator_fits_input_word o)]
  change some (Arithmetic.fromBase (o.domainGenerator.val ^ transposedExponent o index % Arithmetic.modulus)) = _
  simp only [Arithmetic.fromBase,Arithmetic.reduce,Nat.mod_mod,
    WhirIntermediate.domainPoint,transposedExponent]

theorem transposed_exponent_bounded (o : WhirIntermediate.OpenParams) (k : Nat) (index : Fin (2^k))
    (hc : 0 < o.cosetSize) (hn : 0 < o.numCosets) (hs : o.cosetSize*o.numCosets = 2^k) :
    transposedExponent o index.val < 2^k := by
  have h := GoldilocksDomain.transpose_index_bound o.cosetSize o.numCosets index.val hc hn
    (by simpa only [hs] using index.isLt)
  simpa only [hs] using h

theorem domain_query_uses_same_point (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (index : Fin (2^k)) (hc : 0 < o.cosetSize) (hn : 0 < o.numCosets)
    (hs : o.cosetSize*o.numCosets = 2^k) :
    domainPoint o index.val = some (WhirIntermediate.domainPoint o index.val) := by
  apply bounded_domain_point_equals_existing_point
  have h := transposed_exponent_bounded o k index hc hn hs
  have hp : 2^k ≤ 2^256 := Nat.pow_le_pow_right (by decide) (by omega)
  exact h.trans_le hp

theorem zero_exponent_is_one (base : BaseWord) : glPow base ⟨0,by decide⟩ = some 1 := rfl

theorem base_seven_squared_example : glPow ⟨7,by decide⟩ ⟨2,by decide⟩ = some 49 := rfl

end Audit.Wire3.WhirDomainPower
