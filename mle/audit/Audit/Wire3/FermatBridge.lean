import Audit.Wire3.GoldilocksCertificate

/-!
# Conditional bridge from numerical Fermat equations to actual inverse units

FermatAt is an EXPLICIT per-value hypothesis, never an axiom or typeclass
instance. The general statement that every nonzero Goldilocks residue satisfies
it is not proved here. Under this hypothesis for norm(a), the actual executable
WhirFinal.inverse succeeds, produces canonical limbs, and is a two-sided inverse
for Arithmetic.emul. Cancellation and inverse uniqueness then follow from the
concrete modular ring laws already proved in Algebra, not assumed ring laws.

The independent base-two certificate also rules out x^3 = 2 modulo p for every
x that satisfies the explicit FermatAt hypothesis. This does not prove p prime,
general Fermat, X^3 - 2 irreducible, or norm(a) nonzero for every nonzero a.
Solidity/Rust instruction refinement and probabilistic PCS soundness remain
outside this deterministic algebraic bridge.
GoldilocksFoundation/GoldilocksNorm subsequently prove the general Fermat and
nonzero-norm facts needed to discharge these visible hypotheses; the conditional
theorems here remain useful independently of that pinned-Mathlib extension.
-/
namespace Audit.Wire3.FermatBridge
open Arithmetic

def FermatAt (n : Nat) : Prop := n ^ (modulus - 1) % modulus = 1

theorem fermat_exponent_positive : 0 < modulus - 1 := by decide

theorem zero_does_not_satisfy_fermat : ¬ FermatAt 0 := by
  unfold FermatAt
  rw [Nat.zero_pow fermat_exponent_positive]
  decide

theorem fermat_at_reduction_iff (n : Nat) : FermatAt (reduce n) ↔ FermatAt n := by
  unfold FermatAt reduce
  rw [ModularPower.reduced_base_power]

theorem fermat_at_requires_nonzero (n : Nat) (h : FermatAt n) : n ≠ 0 := by
  intro hz
  rw [hz] at h
  exact zero_does_not_satisfy_fermat h

theorem fermat_at_requires_nonzero_residue (n : Nat) (h : FermatAt n) : reduce n ≠ 0 :=
  fermat_at_requires_nonzero _ ((fermat_at_reduction_iff n).mpr h)

theorem fermat_at_one : FermatAt 1 := by
  unfold FermatAt
  rw [Nat.one_pow]
  rfl

theorem fermat_at_product (a b : Nat) (ha : FermatAt a) (hb : FermatAt b) :
    FermatAt (mul a b) := by
  apply (fermat_at_reduction_iff (a*b)).mpr
  unfold FermatAt at ha hb ⊢
  rw [Nat.mul_pow,Nat.mul_mod,ha,hb]
  rfl

theorem fermat_at_power (a exponent : Nat) (ha : FermatAt a) : FermatAt (a ^ exponent) := by
  unfold FermatAt at ha ⊢
  calc
    (a ^ exponent) ^ (modulus - 1) % modulus = (a ^ (modulus - 1)) ^ exponent % modulus := by
      rw [← Nat.pow_mul,← Nat.pow_mul,Nat.mul_comm exponent (modulus - 1)]
    _ = (a ^ (modulus - 1) % modulus) ^ exponent % modulus :=
      (ModularPower.reduced_base_power _ _ _).symm
    _ = 1 := by rw [ha,Nat.one_pow]; rfl

theorem certificate_proves_fermat_at_seven : FermatAt 7 :=
  GoldilocksCertificate.base_seven_full_power_value

theorem actual_norm_is_canonical (a : Arithmetic.Ext3) : WhirFinal.norm a < modulus :=
  add_canonical _ _

theorem inverse_success_is_canonical (a output : Arithmetic.Ext3)
    (h : WhirFinal.inverse a = some output) : Canonical output := by
  have hn := (ModularPower.inverse_has_output_iff_norm_nonzero a).mp ⟨output,h⟩
  rw [ModularPower.inverse_exact_if_norm_nonzero a hn] at h
  rw [← Option.some.inj h]
  exact scalar_canonical _ _

/-- The first operational bridge: the scalar Fermat equation forces the norm
    guard to pass and the 64-step inverse loop to return a concrete result. -/
theorem norm_fermat_makes_inverse_execute (a : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a)) :
    WhirFinal.inverse a = some (scalar (WhirFinal.adjugate a)
      (WhirFinal.norm a ^ (modulus - 2) % modulus)) :=
  ModularPower.inverse_exact_if_norm_nonzero a (fermat_at_requires_nonzero _ hf)

theorem inverse_success_is_right_inverse (a : Verifier.Ext3) (output : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (h : WhirFinal.inverse a.val = some output) :
    emul a.val output = one := by
  rw [ModularPower.inverse_success_product_is_fermat_power a output h]
  rw [show WhirFinal.norm a.val ^ (modulus - 1) % modulus = 1 from hf]
  rfl

theorem inverse_success_is_left_inverse (a : Verifier.Ext3) (output : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (h : WhirFinal.inverse a.val = some output) :
    emul output a.val = one := by
  rw [Algebra.emul_comm]
  exact inverse_success_is_right_inverse a output hf h

/-- No independent inverse oracle appears in this existence theorem. The
    returned value is exactly the output of WhirFinal.inverse. -/
theorem norm_fermat_gives_actual_two_sided_unit (a : Verifier.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) :
    ∃ output, WhirFinal.inverse a.val = some output ∧ Canonical output ∧
      emul a.val output = one ∧ emul output a.val = one := by
  have hi := norm_fermat_makes_inverse_execute a.val hf
  exact ⟨_,hi,inverse_success_is_canonical _ _ hi,
    inverse_success_is_right_inverse a _ hf hi,inverse_success_is_left_inverse a _ hf hi⟩

theorem left_unit_cancels_canonical (a inverse x y : Arithmetic.Ext3)
    (hu : emul inverse a = one) (hx : Canonical x) (hy : Canonical y)
    (h : emul a x = emul a y) : x = y := by
  have hh := congrArg (emul inverse) h
  rw [← Algebra.emul_assoc,← Algebra.emul_assoc,hu,
    Algebra.one_emul_of_canonical x hx,Algebra.one_emul_of_canonical y hy] at hh
  exact hh

/-- For raw noncanonical values, cancellation yields equality of normalized
    residues, not unsound equality of their unrestricted Nat representations. -/
theorem left_unit_cancels_normalized (a inverse x y : Arithmetic.Ext3)
    (hu : emul inverse a = one) (h : emul a x = emul a y) : normalize x = normalize y := by
  have hh := congrArg (emul inverse) h
  rw [← Algebra.emul_assoc,← Algebra.emul_assoc,hu,
    Algebra.one_emul_normalizes,Algebra.one_emul_normalizes] at hh
  exact hh

theorem actual_inverse_cancels_left (a : Verifier.Ext3) (output x y : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (hi : WhirFinal.inverse a.val = some output)
    (hx : Canonical x) (hy : Canonical y) (h : emul a.val x = emul a.val y) : x = y :=
  left_unit_cancels_canonical a.val output x y (inverse_success_is_left_inverse a output hf hi) hx hy h

theorem actual_inverse_cancels_right (a : Verifier.Ext3) (output x y : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (hi : WhirFinal.inverse a.val = some output)
    (hx : Canonical x) (hy : Canonical y) (h : emul x a.val = emul y a.val) : x = y := by
  apply actual_inverse_cancels_left a output x y hf hi hx hy
  simpa only [Algebra.emul_comm] using h

theorem actual_inverse_is_unique (a : Verifier.Ext3) (output candidate : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (hi : WhirFinal.inverse a.val = some output)
    (hc : Canonical candidate) (hunit : emul a.val candidate = one) : candidate = output := by
  apply actual_inverse_cancels_left a output candidate output hf hi hc (inverse_success_is_canonical _ _ hi)
  rw [hunit,inverse_success_is_right_inverse a output hf hi]

/-- This is the exact multiply-by-inverse pattern used by finalClaim. -/
theorem actual_division_multiply_back (a : Verifier.Ext3) (output value : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (hi : WhirFinal.inverse a.val = some output)
    (hv : Canonical value) : emul (emul value output) a.val = value := by
  rw [Algebra.emul_assoc,inverse_success_is_left_inverse a output hf hi,
    Algebra.emul_one_of_canonical value hv]

theorem actual_division_equation_iff (a : Verifier.Ext3) (output value quotient : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (hi : WhirFinal.inverse a.val = some output)
    (hv : Canonical value) (hq : Canonical quotient) :
    emul value output = quotient ↔ value = emul quotient a.val := by
  constructor
  · intro h
    have hh := congrArg (fun x => emul x a.val) h
    dsimp only at hh
    rw [actual_division_multiply_back a output value hf hi hv] at hh
    exact hh
  · intro h
    rw [h,Algebra.emul_assoc,inverse_success_is_right_inverse a output hf hi,
      Algebra.emul_one_of_canonical quotient hq]

theorem actual_division_preserves_nonzero (a : Verifier.Ext3) (output value : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (hi : WhirFinal.inverse a.val = some output)
    (hv : Canonical value) : emul value output = zero ↔ value = zero := by
  rw [actual_division_equation_iff a output value zero hf hi hv zero_canonical,zero_emul]

theorem actual_unit_has_no_nonzero_annihilator (a : Verifier.Ext3) (x : Arithmetic.Ext3)
    (hf : FermatAt (WhirFinal.norm a.val)) (hx : Canonical x) : emul a.val x = zero ↔ x = zero := by
  obtain ⟨output,hi,_,_,_⟩ := norm_fermat_gives_actual_two_sided_unit a hf
  constructor
  · intro hz
    apply actual_inverse_cancels_left a output x zero hf hi hx zero_canonical
    rw [hz,emul_zero]
  · intro hz
    rw [hz,emul_zero]

/-- Products of concretely returned inverses are genuine units too. This does
    NOT yet identify the candidate with inverse(a*b), because that additional
    execution theorem needs a nonzero-norm/product-norm argument. -/
theorem actual_units_have_product_unit (a b : Verifier.Ext3)
    (ha : FermatAt (WhirFinal.norm a.val)) (hb : FermatAt (WhirFinal.norm b.val)) :
    ∃ inverseA inverseB,
      WhirFinal.inverse a.val = some inverseA ∧ WhirFinal.inverse b.val = some inverseB ∧
      Canonical (emul inverseB inverseA) ∧
      emul (emul a.val b.val) (emul inverseB inverseA) = one ∧
      emul (emul inverseB inverseA) (emul a.val b.val) = one := by
  obtain ⟨ia,hia,hca,hua,_⟩ := norm_fermat_gives_actual_two_sided_unit a ha
  obtain ⟨ib,hib,_,hub,_⟩ := norm_fermat_gives_actual_two_sided_unit b hb
  have hu : emul (emul a.val b.val) (emul ib ia) = one := by
    rw [Algebra.emul_assoc,← Algebra.emul_assoc b.val ib ia,hub,
      Algebra.one_emul_of_canonical ia hca,hua]
  exact ⟨ia,ib,hia,hib,emul_canonical _ _,hu,by rw [Algebra.emul_comm]; exact hu⟩

theorem certified_base_two_value_excludes_cubic_root (x : Nat) (hf : FermatAt x) :
    x ^ 3 % modulus ≠ 2 := by
  intro hx
  apply GoldilocksCertificate.base_two_third_exponent_not_one
  calc
    2 ^ ((modulus - 1) / 3) % modulus =
        (x ^ 3 % modulus) ^ ((modulus - 1) / 3) % modulus := by rw [hx]
    _ = (x ^ 3) ^ ((modulus - 1) / 3) % modulus := ModularPower.reduced_base_power _ _ _
    _ = x ^ (3 * ((modulus - 1) / 3)) % modulus := by rw [Nat.pow_mul]
    _ = x ^ (modulus - 1) % modulus := by rw [GoldilocksCertificate.exponent_for_three_has_no_remainder]
    _ = 1 := hf

/-- Explicitly conditional: the missing general Fermat theorem is a visible
    parameter. The conclusion concerns actual Nat.mod cubes, not an assumed
    polynomial/field interpretation. -/
theorem general_fermat_would_exclude_all_cubic_roots
    (hf : ∀ x, x < modulus → x ≠ 0 → FermatAt x) :
    ∀ x, x ^ 3 % modulus ≠ 2 := by
  intro x hx
  have hred : (reduce x) ^ 3 % modulus = 2 := by
    unfold reduce
    rw [ModularPower.reduced_base_power,hx]
  have hn : reduce x ≠ 0 := by
    intro hz
    rw [hz] at hred
    have hh : (0 : Nat) ^ 3 % modulus = 0 := rfl
    rw [hh] at hred
    contradiction
  exact certified_base_two_value_excludes_cubic_root (reduce x)
    (hf _ (reduce_canonical _) hn) hred

/-- A nontrivial concrete unit, derived through the numerical certificate and
    the conditional bridge without a general Fermat/primality assumption. -/
theorem norm_of_embedded_seven : WhirFinal.norm (Norm.embed 7).val = 7 ^ 3 := by decide

theorem embedded_seven_actual_inverse_is_two_sided :
    ∃ output, WhirFinal.inverse (Norm.embed 7).val = some output ∧ Canonical output ∧
      emul (Norm.embed 7).val output = one ∧ emul output (Norm.embed 7).val = one := by
  apply norm_fermat_gives_actual_two_sided_unit
  rw [norm_of_embedded_seven]
  exact fermat_at_power 7 3 certificate_proves_fermat_at_seven

theorem powers_of_seven_cannot_be_cubic_root_of_two (exponent : Nat) :
    (7 ^ exponent) ^ 3 % modulus ≠ 2 :=
  certified_base_two_value_excludes_cubic_root _
    (fermat_at_power 7 exponent certificate_proves_fermat_at_seven)

end Audit.Wire3.FermatBridge
