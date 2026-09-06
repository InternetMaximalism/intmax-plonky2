import Audit.Wire3.GoldilocksFoundation
import Mathlib.Tactic.Ring

/-!
# Concrete Goldilocks norm nonvanishing and total nonzero inverse

Source correspondence: GoldilocksExt3.sol inv computes the three adjugate
coordinates (a*a-2*b*c, 2*c*c-a*b, b*b-a*c), then
a*d0 + 2*(c*d1+b*d2). WhirFinal.adjugate/norm are the existing mathematical
Nat.mod translation of precisely these operations and this coefficient order.
The expanded norm is a^3 + 2*b^3 + 4*c^3 - 6*a*b*c.
Rust norm_logup::formal_adjugate_from_coords/formal_norm_from_coords use the
same order and coefficients for base-coordinate evaluations. The generic
off-cube formal evaluation over Ext3 is not a nonvanishing claim here.

This module uses the PROVED base-modulus primality/Fermat foundation and
no-root result, not a field assumption for the implementation's Ext3 type.
It does not establish compiler/Yul
refinement, general formal-Ext3-over-Ext3 norm nonvanishing, or PCS probability.
-/
namespace Audit.Wire3.GoldilocksNorm
open Audit.Wire3
open GoldilocksFoundation
local notation "p" => Arithmetic.modulus
local notation "F" => ZMod Arithmetic.modulus
attribute [local instance 2000] instPowNat

def d0 (a b c : F) : F := a ^ 2 - 2 * b * c
def d1 (a b c : F) : F := 2 * c ^ 2 - a * b
def d2 (a b c : F) : F := b ^ 2 - a * c
def normF (a b c : F) : F := a * d0 a b c + 2 * (c * d1 a b c + b * d2 a b c)

theorem norm_expansion (a b c : F) :
    normF a b c = a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c := by
  unfold normF d0 d1 d2
  ring

theorem adjugate_adjugate_0 (a b c : F) :
    d0 a b c ^ 2 - 2 * d1 a b c * d2 a b c = a * normF a b c := by
  unfold normF d0 d1 d2
  ring

theorem adjugate_adjugate_1 (a b c : F) :
    2 * d2 a b c ^ 2 - d0 a b c * d1 a b c = b * normF a b c := by
  unfold normF d0 d1 d2
  ring

theorem adjugate_adjugate_2 (a b c : F) :
    d1 a b c ^ 2 - d0 a b c * d2 a b c = c * normF a b c := by
  unfold normF d0 d1 d2
  ring

theorem no_cubic_root_in_zmod (x : F) : x ^ 3 ≠ 2 := by
  intro hx
  have h : ((x.val ^ 3 : Nat) : F) = ((2 : Nat) : F) := by
    simpa only [Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_ofNat] using hx
  have hm := (ZMod.natCast_eq_natCast_iff' (x.val ^ 3) 2 p).mp h
  exact no_cubic_root_of_two x.val (by
    simpa only [Nat.mod_eq_of_lt (show 2 < p by decide)] using hm)

/-- These are precisely the homogeneous adjugate equations. If z were
nonzero, y/z would be a prohibited cube root of two. -/
theorem homogeneous_adjugate_equations_force_zero (x y z : F)
    (h0 : x ^ 2 = 2 * y * z) (h1 : y ^ 2 = x * z)
    (h2 : x * y = 2 * z ^ 2) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hz : z = 0 := by
    by_contra hz
    have hc : y ^ 3 = 2 * z ^ 3 := by
      calc
        y ^ 3 = y ^ 2 * y := by ring
        _ = (x * z) * y := by rw [h1]
        _ = (x * y) * z := by ring
        _ = 2 * z ^ 3 := by rw [h2]; ring
    apply no_cubic_root_in_zmod (y / z)
    rw [div_pow, div_eq_iff (pow_ne_zero 3 hz)]
    exact hc
  have hy : y = 0 := sq_eq_zero_iff.mp (by simpa only [hz, mul_zero] using h1)
  have hx : x = 0 := sq_eq_zero_iff.mp (by simpa only [hz, mul_zero] using h0)
  exact ⟨hx,hy,hz⟩

theorem zero_norm_forces_zero_adjugate (a b c : F) (hn : normF a b c = 0) :
    d0 a b c = 0 ∧ d1 a b c = 0 ∧ d2 a b c = 0 := by
  apply homogeneous_adjugate_equations_force_zero
  · apply sub_eq_zero.mp
    rw [adjugate_adjugate_0, hn, mul_zero]
  · apply sub_eq_zero.mp
    rw [adjugate_adjugate_2, hn, mul_zero]
  · apply Eq.symm
    apply sub_eq_zero.mp
    rw [adjugate_adjugate_1, hn, mul_zero]

theorem zero_adjugate_forces_zero_coordinates (a b c : F)
    (h0 : d0 a b c = 0) (h1 : d1 a b c = 0) (h2 : d2 a b c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  apply homogeneous_adjugate_equations_force_zero
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h2
  · exact (sub_eq_zero.mp h1).symm

theorem norm_zero_iff_coordinates_zero (a b c : F) :
    normF a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hn
    rcases zero_norm_forces_zero_adjugate a b c hn with ⟨h0,h1,h2⟩
    exact zero_adjugate_forces_zero_coordinates a b c h0 h1 h2
  · rintro ⟨rfl,rfl,rfl⟩
    simp [normF, d0, d1, d2]

theorem cast_reduce (a : Nat) : (Arithmetic.reduce a : F) = (a : F) :=
  ZMod.natCast_mod a p

theorem cast_add (a b : Nat) : (Arithmetic.add a b : F) = (a : F) + (b : F) := by
  simp only [Arithmetic.add, cast_reduce, Nat.cast_add]

theorem cast_mul (a b : Nat) : (Arithmetic.mul a b : F) = (a : F) * (b : F) := by
  simp only [Arithmetic.mul, cast_reduce, Nat.cast_mul]

theorem cast_sub (a b : Nat) : (Arithmetic.sub a b : F) = (a : F) - (b : F) := by
  simp only [Arithmetic.sub, cast_reduce, Nat.cast_add,
    Nat.cast_sub (Nat.le_of_lt (Arithmetic.reduce_canonical b)),
    ZMod.natCast_self, zero_sub]
  exact (sub_eq_add_neg _ _).symm

theorem cast_actual_norm (a : Arithmetic.Ext3) :
    (WhirFinal.norm a : F) = normF (a.c0 : F) (a.c1 : F) (a.c2 : F) := by
  simp only [WhirFinal.norm, WhirFinal.adjugate, cast_add, cast_mul, cast_sub,
    Nat.cast_ofNat, normF, d0, d1, d2, pow_two]
  ring

theorem canonical_cast_zero_iff (a : Nat) (ha : a < p) : (a : F) = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_zero] using hv
  · rintro rfl
    exact Nat.cast_zero

/-- Exact source-model norm: canonicality is required only to conclude raw
coordinate equality, not silently inferred from an arbitrary Nat triple. -/
theorem actual_norm_zero_iff (a : Arithmetic.Ext3) (ha : Arithmetic.Canonical a) :
    WhirFinal.norm a = 0 ↔ a = Arithmetic.zero := by
  constructor
  · intro hn
    have hf : normF (a.c0 : F) (a.c1 : F) (a.c2 : F) = 0 := by
      rw [← cast_actual_norm, hn, Nat.cast_zero]
    rcases (norm_zero_iff_coordinates_zero _ _ _).mp hf with ⟨h0,h1,h2⟩
    have h0 := (canonical_cast_zero_iff a.c0 ha.1).mp h0
    have h1 := (canonical_cast_zero_iff a.c1 ha.2.1).mp h1
    have h2 := (canonical_cast_zero_iff a.c2 ha.2.2).mp h2
    cases a
    simp_all [Arithmetic.zero]
  · rintro rfl
    rfl

theorem nonzero_actual_norm (a : Verifier.Ext3) (ha : a.val ≠ Arithmetic.zero) :
    WhirFinal.norm a.val ≠ 0 := by
  intro hn
  exact ha ((actual_norm_zero_iff a.val a.property).mp hn)

theorem actual_inverse_has_output_iff_nonzero (a : Verifier.Ext3) :
    (∃ output, WhirFinal.inverse a.val = some output) ↔ a.val ≠ Arithmetic.zero := by
  rw [ModularPower.inverse_has_output_iff_norm_nonzero]
  exact not_congr (actual_norm_zero_iff a.val a.property)

/-- The actual executable inverse returns a canonical, two-sided inverse for
EVERY nonzero canonical Ext3 input, without a norm or Fermat hypothesis. -/
theorem nonzero_actual_inverse_exists (a : Verifier.Ext3) (ha : a.val ≠ Arithmetic.zero) :
    ∃ output, WhirFinal.inverse a.val = some output ∧ Arithmetic.Canonical output ∧
      Arithmetic.emul a.val output = Arithmetic.one ∧
      Arithmetic.emul output a.val = Arithmetic.one := by
  have hn := nonzero_actual_norm a ha
  obtain ⟨output,hi⟩ := (ModularPower.inverse_has_output_iff_norm_nonzero a.val).mpr hn
  have hu := successful_actual_inverse_is_two_sided a output hi
  exact ⟨output,hi,FermatBridge.inverse_success_is_canonical a.val output hi,hu.1,hu.2⟩

set_option maxRecDepth 4096 in
/-- Non-base input theta: the actual 64-step binary exponentiation executes
and returns theta^2/2, not an independently supplied inverse witness. -/
theorem theta_actual_inverse_executes :
    WhirFinal.inverse ⟨0,1,0⟩ = some ⟨0,0,9223372034707292161⟩ := by decide

theorem theta_inverse_is_two_sided :
    Arithmetic.emul ⟨0,1,0⟩ ⟨0,0,9223372034707292161⟩ = Arithmetic.one ∧
      Arithmetic.emul ⟨0,0,9223372034707292161⟩ ⟨0,1,0⟩ = Arithmetic.one := by
  exact successful_actual_inverse_is_two_sided ⟨⟨0,1,0⟩,by decide⟩ _ theta_actual_inverse_executes

end Audit.Wire3.GoldilocksNorm
