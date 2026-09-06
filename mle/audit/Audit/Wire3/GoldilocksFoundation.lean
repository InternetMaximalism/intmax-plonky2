import Mathlib.NumberTheory.LucasPrimality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import Audit.Wire3.FermatBridge

/-!
# Concrete Goldilocks modulus primality and Fermat foundation

This module consumes the audit's concrete binary modular-power certificate and
Mathlib 4.10's proved Lucas criterion, with the exact dependency source revisions
checked separately. Primality and Fermat are conclusions, not input assumptions.
No primality, general Fermat, or extension-field axiom is introduced.

The conclusions concern the concrete Nat.mod arithmetic of the existing audit.
They do not prove instruction-level source refinement, norm nonvanishing for
all nonzero Ext3 values, polynomial irreducibility, or probabilistic PCS soundness.
-/
namespace Audit.Wire3.GoldilocksFoundation
open Audit.Wire3

-- Keep concrete Nat powers syntactically aligned with the Std-only audit.
-- Mathlib's Monoid.toNatPow is extensionally the same, but elaborating that
-- conversion at a 64-bit exponent would try to compute the enormous power.
attribute [local instance 2000] instPowNat

local notation "p" => Arithmetic.modulus

theorem small_factors_prime :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 17 ∧
      Nat.Prime 257 ∧ Nat.Prime 65537 := by norm_num

/-- Exhaustiveness, not just divisibility, of the six certified prime factors. -/
theorem prime_divisor_cases (q : Nat) (hq : q.Prime) (hd : q ∣ p - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
  rw [GoldilocksCertificate.modulus_minus_one_factorization] at hd
  have hd' : q ∣ 2 ^ 32 ∨ q ∣ 3 ∨ q ∣ 5 ∨ q ∣ 17 ∨ q ∣ 257 ∨ q ∣ 65537 := by
    simpa only [hq.dvd_mul, or_assoc] using hd
  rcases small_factors_prime with ⟨h2,h3,h5,h17,h257,h65537⟩
  rcases hd' with hd | hd | hd | hd | hd | hd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq h2).mp (hq.dvd_of_dvd_pow hd))
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq h3).mp hd))
  · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq h5).mp hd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq h17).mp hd))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((Nat.prime_dvd_prime_iff_eq hq h257).mp hd)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hq h65537).mp hd)))))

theorem nat_mod_power_to_zmod (a exponent value : Nat) (hv : value < p)
    (h : a ^ exponent % p = value) :
    (a : ZMod p) ^ exponent = (value : ZMod p) := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff']
  exact h.trans (Nat.mod_eq_of_lt hv).symm

theorem certificate_factor_power_ne_one (q value : Nat)
    (hm : (q,value) ∈ GoldilocksCertificate.factorResidues) :
    ((7 : Nat) : ZMod p) ^ ((p - 1) / q) ≠ 1 := by
  have hc := GoldilocksCertificate.each_factor_check q value hm
  have he := nat_mod_power_to_zmod 7 ((p - 1) / q) value hc.2.2.1
    (GoldilocksCertificate.each_factor_power_value q value hm)
  intro h
  have hv : value = 1 := by
    have hv' : (value : ZMod p) = (1 : Nat) := he.symm.trans h
    rw [ZMod.natCast_eq_natCast_iff'] at hv'
    simpa only [Nat.mod_eq_of_lt hc.2.2.1, Nat.mod_eq_of_lt (show 1 < p by decide)] using hv'
  have hg := hc.2.2.2.2.2
  rw [hv] at hg
  norm_num [Arithmetic.modulus] at hg

/-- This is the first genuine primality conclusion: it applies a proved Lucas
criterion to all prime divisors, using the executable audit certificate. -/
theorem modulus_prime : Nat.Prime p := by
  apply lucas_primality p ((7 : Nat) : ZMod p)
  · exact nat_mod_power_to_zmod 7 (p - 1) 1 (by decide)
      GoldilocksCertificate.base_seven_full_power_value
  · intro q hq hd
    rcases prime_divisor_cases q hq hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact certificate_factor_power_ne_one 2 18446744069414584320 (by decide)
    · exact certificate_factor_power_ne_one 3 18446744065119617025 (by decide)
    · exact certificate_factor_power_ne_one 5 1373043270956696022 (by decide)
    · exact certificate_factor_power_ne_one 17 16301593560560007290 (by decide)
    · exact certificate_factor_power_ne_one 257 995085315851368103 (by decide)
    · exact certificate_factor_power_ne_one 65537 8478886009461009681 (by decide)

/-- A derived instance, backed by modulus_prime, not a field assumption. -/
instance goldilocksPrime : Fact (Nat.Prime p) := ⟨modulus_prime⟩

theorem general_fermat_zmod (a : ZMod p) (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one ha

theorem general_fermat_nat (a : Nat) (ha : a % p ≠ 0) :
    a ^ (p - 1) % p = 1 := by
  have hz : (a : ZMod p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    exact ha (by simpa only [ZMod.val_natCast, ZMod.val_zero] using hv)
  have h := general_fermat_zmod (a : ZMod p) hz
  rw [← Nat.cast_pow] at h
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt (show 1 < p by decide)] using hv

theorem general_fermat_canonical (a : Nat) (ha : a < p) (hne : a ≠ 0) :
    FermatBridge.FermatAt a := by
  exact general_fermat_nat a (by simpa only [Nat.mod_eq_of_lt ha] using hne)

/-- The previous explicit Fermat hypothesis is discharged for every residue.
This rules out cubic roots of two but does not yet construct a polynomial
irreducibility proof or a field instance for the concrete Ext3 implementation. -/
theorem no_cubic_root_of_two (a : Nat) : a ^ 3 % p ≠ 2 :=
  FermatBridge.general_fermat_would_exclude_all_cubic_roots general_fermat_canonical a

/-- Every successful actual inverse now has its Fermat side condition proved.
It still does not assert nonzero norm for every nonzero Ext3 input. -/
theorem successful_actual_inverse_is_two_sided (a : Verifier.Ext3) (output : Arithmetic.Ext3)
    (h : WhirFinal.inverse a.val = some output) :
    Arithmetic.emul a.val output = Arithmetic.one ∧
      Arithmetic.emul output a.val = Arithmetic.one := by
  have hn : WhirFinal.norm a.val ≠ 0 :=
    (ModularPower.inverse_has_output_iff_norm_nonzero a.val).mp ⟨output,h⟩
  have hf := general_fermat_canonical (WhirFinal.norm a.val)
    (FermatBridge.actual_norm_is_canonical a.val) hn
  exact ⟨FermatBridge.inverse_success_is_right_inverse a output hf h,
    FermatBridge.inverse_success_is_left_inverse a output hf h⟩

end Audit.Wire3.GoldilocksFoundation
