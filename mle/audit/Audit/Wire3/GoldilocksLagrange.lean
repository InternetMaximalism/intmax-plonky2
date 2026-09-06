import Audit.Wire3.GoldilocksExt3Field

/-!
# Concrete repeated squaring and the partial evalL0 operation

Sources: GoldilocksExt3.sol square, expPowerOf2, evalL0 (becfe98e).
The square operation is the existing Norm.square with the exact specialized
coefficient formulas. expPowerOf2 starts at x and iterates that square. evalL0
checks degreeBits < 64, computes nScalar = 1 << degreeBits, checks nScalar < p,
then computes (x^n - 1) * inverse((x - 1) * n) using actual WhirFinal.inverse.

Reverts are represented by none. In particular x=1 FAILS: no removable-
singularity convention L0(1)=1 is silently inserted. The second scalar guard
is retained although it is proved redundant after the first guard for this p.
The guarded scalar fits uint64; proving machine shift/cast instructions, Yul
memory, gas, compilation, or full WHIR success is outside this Nat.mod model.

All field statements use the constructed concrete Element Field; no free
field or nonzero-norm assumption is introduced. Inputs are canonical by type.
-/
namespace Audit.Wire3.GoldilocksLagrange
open Audit.Wire3
open GoldilocksExt3Field
local notation "p" => Arithmetic.modulus

def scalarSize (degreeBits : Nat) : Nat := Nat.shiftLeft 1 degreeBits

theorem scalar_size_is_power (degreeBits : Nat) : scalarSize degreeBits = 2 ^ degreeBits :=
  Nat.one_shiftLeft degreeBits

theorem admissible_scalar_positive_and_below_modulus (degreeBits : Nat) (h : degreeBits < 64) :
    0 < scalarSize degreeBits ∧ scalarSize degreeBits < p := by
  rw [scalar_size_is_power]
  refine ⟨Nat.pow_pos (by decide), ?_⟩
  have hh : degreeBits ≤ 63 := by omega
  have hb := Nat.pow_le_pow_right (by decide : 0 < 2) hh
  exact lt_of_le_of_lt hb (by decide : 2 ^ 63 < p)

theorem admissible_scalar_fits_u64 (degreeBits : Nat) (h : degreeBits < 64) :
    scalarSize degreeBits < 2 ^ 64 :=
  lt_trans (admissible_scalar_positive_and_below_modulus degreeBits h).2 Arithmetic.modulus_below_u64

/-- Tail-recursive form of the source's in-place repeated-square loop. -/
def expPowerOf2 : Verifier.Ext3 → Nat → Verifier.Ext3
  | x, 0 => x
  | x, degreeBits + 1 => expPowerOf2 (Norm.square x) degreeBits

theorem exp_power_zero_iterations (x : Verifier.Ext3) : expPowerOf2 x 0 = x := rfl

theorem specialized_square_matches_field (x : Element) :
    Element.mk (Norm.square x.toVerifier) = x * x :=
  congrArg Element.mk (Algebra.norm_square_is_multiplication x.toVerifier)

theorem repeated_square_matches_power (x : Element) (degreeBits : Nat) :
    Element.mk (expPowerOf2 x.toVerifier degreeBits) = x ^ (2 ^ degreeBits) := by
  induction degreeBits generalizing x with
  | zero => simp only [expPowerOf2, pow_zero, pow_one]
  | succ bits ih =>
      calc
        Element.mk (expPowerOf2 x.toVerifier (bits + 1)) =
            (Element.mk (Norm.square x.toVerifier)) ^ (2 ^ bits) := ih _
        _ = (x * x) ^ (2 ^ bits) := by rw [specialized_square_matches_field]
        _ = x ^ (2 * 2 ^ bits) := by rw [← pow_two, ← pow_mul]
        _ = x ^ (2 ^ (bits + 1)) := by rw [Nat.pow_succ, Nat.mul_comm 2]

theorem repeated_square_result_canonical (x : Verifier.Ext3) (degreeBits : Nat) :
    Arithmetic.Canonical (expPowerOf2 x degreeBits).val := (expPowerOf2 x degreeBits).property

def numerator (x : Verifier.Ext3) (degreeBits : Nat) : Verifier.Ext3 :=
  Verifier.sub (expPowerOf2 x degreeBits) Norm.one

def denominator (x : Verifier.Ext3) (degreeBits : Nat) : Verifier.Ext3 :=
  Verifier.scalar (Verifier.sub x Norm.one) (scalarSize degreeBits)

def evalL0 (x : Verifier.Ext3) (degreeBits : Nat) : Option Arithmetic.Ext3 :=
  if degreeBits < 64 then
    if scalarSize degreeBits < p then
      (WhirFinal.inverse (denominator x degreeBits).val).map
        (Arithmetic.emul (numerator x degreeBits).val)
    else none
  else none

def rationalFormula (x : Element) (degreeBits : Nat) : Element :=
  (x ^ (2 ^ degreeBits) - 1) / ((x - 1) * (scalarSize degreeBits : Element))

theorem numerator_matches_field (x : Element) (degreeBits : Nat) :
    Element.mk (numerator x.toVerifier degreeBits) = x ^ (2 ^ degreeBits) - 1 :=
  congrArg (fun a : Element => a - 1) (repeated_square_matches_power x degreeBits)

theorem denominator_matches_field (x : Element) (degreeBits : Nat) :
    Element.mk (denominator x.toVerifier degreeBits) =
      (x - 1) * (scalarSize degreeBits : Element) := by
  unfold denominator
  rw [Algebra.scalar_as_embedded_mul]
  rfl

theorem admissible_scalar_nonzero_in_field (degreeBits : Nat) (h : degreeBits < 64) :
    (scalarSize degreeBits : Element) ≠ 0 := by
  intro hz
  have hd := (field_nat_cast_zero_iff (scalarSize degreeBits)).mp hz
  have hm := Nat.mod_eq_zero_of_dvd hd
  have hb := admissible_scalar_positive_and_below_modulus degreeBits h
  rw [Nat.mod_eq_of_lt hb.2] at hm
  exact (Nat.ne_of_gt hb.1) hm

theorem nonone_denominator_nonzero (x : Element) (degreeBits : Nat)
    (hbits : degreeBits < 64) (hx : x ≠ 1) :
    Element.mk (denominator x.toVerifier degreeBits) ≠ 0 := by
  rw [denominator_matches_field]
  exact mul_ne_zero (sub_ne_zero.mpr hx) (admissible_scalar_nonzero_in_field degreeBits hbits)

theorem denominator_inverse_really_executes (x : Element) (degreeBits : Nat)
    (hbits : degreeBits < 64) (hx : x ≠ 1) :
    WhirFinal.inverse (denominator x.toVerifier degreeBits).val =
      some ((Element.mk (denominator x.toVerifier degreeBits))⁻¹).toVerifier.val :=
  field_inverse_executes_when_nonzero _ (nonone_denominator_nonzero x degreeBits hbits hx)

/-- Correct rational formula only where the actual source inverse is defined. -/
theorem evalL0_nonone_exact (x : Element) (degreeBits : Nat)
    (hbits : degreeBits < 64) (hx : x ≠ 1) :
    evalL0 x.toVerifier degreeBits = some (rationalFormula x degreeBits).toVerifier.val := by
  have hs := (admissible_scalar_positive_and_below_modulus degreeBits hbits).2
  rw [evalL0, if_pos hbits, if_pos hs, denominator_inverse_really_executes x degreeBits hbits hx]
  have he : (Element.mk (numerator x.toVerifier degreeBits)) *
      (Element.mk (denominator x.toVerifier degreeBits))⁻¹ = rationalFormula x degreeBits := by
    rw [numerator_matches_field, denominator_matches_field, rationalFormula, div_eq_mul_inv]
  exact congrArg (fun a : Element => some a.toVerifier.val) he

theorem degree_guard_rejects (x : Verifier.Ext3) (degreeBits : Nat) (h : 64 ≤ degreeBits) :
    evalL0 x degreeBits = none := by
  simp only [evalL0, if_neg (Nat.not_lt.mpr h)]

theorem scalar_guard_rejects (x : Verifier.Ext3) (degreeBits : Nat)
    (h : p ≤ scalarSize degreeBits) : evalL0 x degreeBits = none := by
  unfold evalL0
  split
  · exact if_neg (Nat.not_lt.mpr h)
  · rfl

theorem denominator_at_one (degreeBits : Nat) : denominator Norm.one degreeBits = Verifier.zero := by
  have h := denominator_matches_field (1 : Element) degreeBits
  simp only [sub_self, zero_mul] at h
  exact congrArg Element.toVerifier h

/-- The code rejects the removable singularity at x=1; its result is NOT 1. -/
theorem evalL0_at_one_fails (degreeBits : Nat) : evalL0 Norm.one degreeBits = none := by
  unfold evalL0
  split
  · split
    · rw [denominator_at_one]
      rfl
    · rfl
  · rfl

theorem evalL0_has_output_iff (x : Element) (degreeBits : Nat) :
    (∃ output, evalL0 x.toVerifier degreeBits = some output) ↔ degreeBits < 64 ∧ x ≠ 1 := by
  constructor
  · rintro ⟨output,ho⟩
    have hb : degreeBits < 64 := by
      by_contra hb
      rw [degree_guard_rejects _ _ (Nat.le_of_not_lt hb)] at ho
      contradiction
    refine ⟨hb, ?_⟩
    intro hx
    subst x
    change evalL0 Norm.one degreeBits = some output at ho
    rw [evalL0_at_one_fails] at ho
    contradiction
  · rintro ⟨hb,hx⟩
    exact ⟨_,evalL0_nonone_exact x degreeBits hb hx⟩

theorem successful_output_canonical (x : Verifier.Ext3) (degreeBits : Nat)
    (output : Arithmetic.Ext3) (h : evalL0 x degreeBits = some output) :
    Arithmetic.Canonical output := by
  have hs := (evalL0_has_output_iff (Element.mk x) degreeBits).mp ⟨output,h⟩
  have he := evalL0_nonone_exact (Element.mk x) degreeBits hs.1 hs.2
  rw [he] at h
  cases h
  exact (rationalFormula (Element.mk x) degreeBits).toVerifier.property

theorem zero_iterations_nonone_is_one (x : Element) (hx : x ≠ 1) :
    evalL0 x.toVerifier 0 = some Arithmetic.one := by
  rw [evalL0_nonone_exact x 0 (by decide) hx]
  have hr : rationalFormula x 0 = 1 := by
    change (x ^ (2 ^ 0) - 1) / ((x - 1) * (1 : Element)) = 1
    simp only [pow_zero, pow_one, mul_one, div_self (sub_ne_zero.mpr hx)]
  rw [hr]
  rfl

/-- A zero VALUE is legitimate away from x=1: other n-th roots of unity
produce zero, after the actual denominator inverse successfully executes. -/
theorem proper_root_of_unity_returns_zero (x : Element) (degreeBits : Nat)
    (hbits : degreeBits < 64) (hx : x ≠ 1) (hroot : x ^ (2 ^ degreeBits) = 1) :
    evalL0 x.toVerifier degreeBits = some Arithmetic.zero := by
  rw [evalL0_nonone_exact x degreeBits hbits hx]
  simp only [rationalFormula, hroot, sub_self, zero_div]
  rfl

set_option maxRecDepth 4096 in
theorem zero_iterations_zero_input : evalL0 Verifier.zero 0 = some Arithmetic.one := by decide

set_option maxRecDepth 4096 in
theorem degree_bits_two_zero_input :
    evalL0 Verifier.zero 2 = some (Arithmetic.fromBase 13835058052060938241) := by decide

set_option maxRecDepth 4096 in
theorem degree_bits_one_input_two :
    evalL0 (Norm.embed 2) 1 = some (Arithmetic.fromBase 9223372034707292162) := by decide

theorem one_input_is_not_patched : evalL0 Norm.one 3 = none := by decide

theorem degree_bits_64_is_rejected : evalL0 (Norm.embed 2) 64 = none := by decide

end Audit.Wire3.GoldilocksLagrange
