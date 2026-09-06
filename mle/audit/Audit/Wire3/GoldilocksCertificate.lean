import Audit.Wire3.ModularPower

/-!
# Kernel-checked numerical certificates for the Goldilocks modulus

This module records concrete factorization, modular-power and gcd calculations
for p = 18446744069414584321. Every calculation is checked by Lean's kernel;
modular exponentiation uses the existing 64-bit-iteration WhirFinal.modPowLoop,
whose Nat.mod meaning is proved in ModularPower. No external checker, native
evaluation axiom, or imported primality/field assumption is used.

These are INPUT DATA for a future sound Lucas/Pratt-style argument. This module
does NOT prove that such a criterion is sound, that the six candidate factors
are prime, that p is prime, general Fermat, or irreducibility of X^3 - 2. In
particular, one base satisfying Fermat's numerical congruence is not silently
generalized to every nonzero residue. The cubic nonresidue calculation likewise
does not by itself rule out a root without the missing general field argument.
No theorem here is named Prime or presented as a primality theorem.
-/
namespace Audit.Wire3.GoldilocksCertificate
open Arithmetic

def factorCandidates : List Nat := [2, 3, 5, 17, 257, 65537]

/-- Distinct candidate factors paired with the residue of 7^((p-1)/q). -/
def factorResidues : List (Nat × Nat) :=
  [(2, 18446744069414584320),
   (3, 18446744065119617025),
   (5, 1373043270956696022),
   (17, 16301593560560007290),
   (257, 995085315851368103),
   (65537, 8478886009461009681)]

theorem modulus_minus_one_factorization :
    modulus - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := by decide

theorem certificate_candidates_exact : factorResidues.map Prod.fst = factorCandidates := rfl

theorem certificate_has_six_entries : factorResidues.length = 6 := rfl

theorem candidate_factor_positions_distinct :
    ∀ i j : Fin 6, i ≠ j → factorCandidates.getD i.val 0 ≠ factorCandidates.getD j.val 0 := by decide

def factorCheck (entry : Nat × Nat) : Bool := decide (
  2 ≤ entry.1 ∧ (modulus - 1) % entry.1 = 0 ∧
  entry.2 < modulus ∧ 0 < entry.2 ∧
  WhirFinal.modPowLoop 64 7 ((modulus - 1) / entry.1) 1 = some entry.2 ∧
  Nat.gcd (entry.2 - 1) modulus = 1)

set_option maxRecDepth 4096 in
theorem all_factor_checks_accept : factorResidues.all factorCheck = true := by decide

theorem each_factor_check (q value : Nat) (h : (q,value) ∈ factorResidues) :
    2 ≤ q ∧ (modulus - 1) % q = 0 ∧ value < modulus ∧ 0 < value ∧
      WhirFinal.modPowLoop 64 7 ((modulus - 1) / q) 1 = some value ∧
      Nat.gcd (value - 1) modulus = 1 := by
  have hc := List.all_eq_true.mp all_factor_checks_accept (q,value) h
  simpa only [factorCheck,decide_eq_true_eq] using hc

theorem each_factor_power_value (q value : Nat) (h : (q,value) ∈ factorResidues) :
    7 ^ ((modulus - 1) / q) % modulus = value := by
  have hp := (each_factor_check q value h).2.2.2.2.1
  have he := ModularPower.mod_pow_success_exact 64 7 ((modulus - 1) / q) 1 value (by decide) hp
  simpa only [Nat.one_mul] using he.symm

theorem each_factor_power_gcd (q value : Nat) (h : (q,value) ∈ factorResidues) :
    Nat.gcd (7 ^ ((modulus - 1) / q) % modulus - 1) modulus = 1 := by
  rw [each_factor_power_value q value h]
  exact (each_factor_check q value h).2.2.2.2.2

set_option maxRecDepth 4096 in
theorem full_exponent_loop_value : WhirFinal.modPowLoop 64 7 (modulus - 1) 1 = some 1 := by decide

/-- A numerical congruence for the single concrete base seven, not Fermat's
    theorem for arbitrary residues and not a primality conclusion. -/
theorem base_seven_full_power_value : 7 ^ (modulus - 1) % modulus = 1 := by
  have he := ModularPower.mod_pow_success_exact 64 7 (modulus - 1) 1 1 (by decide) full_exponent_loop_value
  simpa only [Nat.one_mul] using he.symm

theorem exponent_for_three_exact : (modulus - 1) / 3 = 6148914689804861440 := by decide

theorem exponent_for_three_has_no_remainder : 3 * ((modulus - 1) / 3) = modulus - 1 := by decide

set_option maxRecDepth 4096 in
theorem base_two_third_exponent_loop_value :
    WhirFinal.modPowLoop 64 2 ((modulus - 1) / 3) 1 = some 4294967295 := by decide

theorem base_two_third_exponent_value :
    2 ^ ((modulus - 1) / 3) % modulus = 4294967295 := by
  have he := ModularPower.mod_pow_success_exact 64 2 ((modulus - 1) / 3) 1 4294967295
    (by decide) base_two_third_exponent_loop_value
  simpa only [Nat.one_mul] using he.symm

theorem base_two_third_exponent_not_one :
    2 ^ ((modulus - 1) / 3) % modulus ≠ 1 := by
  rw [base_two_third_exponent_value]
  decide

theorem base_two_third_exponent_canonical :
    0 < 4294967295 ∧ 4294967295 < modulus := by decide

end Audit.Wire3.GoldilocksCertificate
