import Audit.Wire3.NormIdentity

/-!
# Concrete binary modular exponentiation and the inverse's remaining obligation

`WhirFinal.modPowLoop` is the existing fuel-bounded mathematical rendering of
GoldilocksExt3.inv's binary exponentiation: multiply the accumulator on a set
low bit, divide the exponent by two, and square the base modulo Goldilocks p.
Fuel counts exponent-bit iterations, not EVM gas. On exponent zero the loop
returns its accumulator unchanged, even with zero fuel; a canonical initial
accumulator is therefore necessary for an unreduced equality of the output.
There is no transcript read, challenge, hash, or proof-dependent oracle in this
function. Nat operations below do not certify Solidity's word/assembly semantics.

The successful inverse product is reduced to the explicit base-field expression
norm^(p-1) mod p. We do NOT assume or prove primality, Fermat's theorem, extension
irreducibility, or that a nonzero Ext3 necessarily has nonzero norm. Thus the
final expression is not silently replaced by one and is not PCS soundness.
-/
namespace Audit.Wire3.ModularPower
open Arithmetic Algebra

theorem reduced_base_power (b exponent m : Nat) :
    (b % m) ^ exponent % m = b ^ exponent % m := by
  induction exponent with
  | zero => rfl
  | succ n ih =>
      simp only [Nat.pow_succ]
      rw [nat_mod_mul_right]
      calc
        ((b % m) ^ n * b) % m = (((b % m) ^ n % m) * b) % m :=
          (nat_mod_mul_left _ _ _).symm
        _ = ((b ^ n % m) * b) % m := by rw [ih]
        _ = (b ^ n * b) % m := nat_mod_mul_left _ _ _

theorem multiplied_reduced_base_power (acc b exponent m : Nat) :
    (acc * (b % m) ^ exponent) % m = (acc * b ^ exponent) % m := by
  calc
    _ = (acc * ((b % m) ^ exponent % m)) % m := (nat_mod_mul_right _ _ _).symm
    _ = (acc * (b ^ exponent % m)) % m := by rw [reduced_base_power]
    _ = _ := nat_mod_mul_right _ _ _

theorem squared_base_power (acc b exponent : Nat) :
    (acc * (mul b b) ^ exponent) % modulus =
      (acc * b ^ (2 * exponent)) % modulus := by
  unfold mul reduce
  rw [multiplied_reduced_base_power, Nat.pow_mul]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

theorem binary_step_preserves_power (acc b exponent : Nat) :
    ((if exponent % 2 = 1 then mul acc b else acc) *
      (mul b b) ^ (exponent / 2)) % modulus = (acc * b ^ exponent) % modulus := by
  by_cases hbit : exponent % 2 = 1
  · have he : exponent = 2 * (exponent / 2) + 1 := by omega
    simp only [hbit, ↓reduceIte]
    rw [squared_base_power]
    unfold mul reduce
    rw [nat_mod_mul_left]
    have hp : b ^ exponent = b ^ (2 * (exponent / 2)) * b :=
      (congrArg (fun n => b ^ n) he).trans (Nat.pow_succ _ _)
    rw [hp]
    congr 1
    ac_rfl
  · have he : exponent = 2 * (exponent / 2) := by omega
    simp only [hbit, ↓reduceIte]
    rw [squared_base_power, ← he]

/-- Reduction of the output is valid without any canonical input condition. -/
theorem mod_pow_success_reduced (fuel b exponent acc output : Nat)
    (h : WhirFinal.modPowLoop fuel b exponent acc = some output) :
    output % modulus = (acc * b ^ exponent) % modulus := by
  induction fuel generalizing b exponent acc with
  | zero =>
      simp only [WhirFinal.modPowLoop] at h
      split at h
      · cases h
        simp [‹exponent = 0›]
      · contradiction
  | succ fuel ih =>
      simp only [WhirFinal.modPowLoop] at h
      split at h
      · cases h
        simp [‹exponent = 0›]
      · exact (ih _ _ _ h).trans (binary_step_preserves_power acc b exponent)

theorem mod_pow_success_canonical (fuel b exponent acc output : Nat)
    (hacc : acc < modulus)
    (h : WhirFinal.modPowLoop fuel b exponent acc = some output) : output < modulus := by
  induction fuel generalizing b exponent acc with
  | zero =>
      simp only [WhirFinal.modPowLoop] at h
      split at h
      · cases h; exact hacc
      · contradiction
  | succ fuel ih =>
      simp only [WhirFinal.modPowLoop] at h
      split at h
      · cases h; exact hacc
      · apply ih _ _ _ _ h
        split
        · exact reduce_canonical _
        · exact hacc

/-- Exact success value, including the zero-exponent/zero-fuel cases. -/
theorem mod_pow_success_exact (fuel b exponent acc output : Nat)
    (hacc : acc < modulus)
    (h : WhirFinal.modPowLoop fuel b exponent acc = some output) :
    output = (acc * b ^ exponent) % modulus := by
  have hc := mod_pow_success_canonical fuel b exponent acc output hacc h
  have hv := mod_pow_success_reduced fuel b exponent acc output h
  simpa only [Nat.mod_eq_of_lt hc] using hv

/-- Sufficient bit fuel yields the specified answer, not just some answer. -/
theorem mod_pow_exact_with_sufficient_bits (fuel b exponent acc : Nat)
    (hacc : acc < modulus) (hbits : exponent < 2 ^ fuel) :
    WhirFinal.modPowLoop fuel b exponent acc = some ((acc * b ^ exponent) % modulus) := by
  obtain ⟨output, h⟩ := WhirFinal.mod_pow_terminates_with_sufficient_bits fuel b exponent acc hbits
  rw [← mod_pow_success_exact fuel b exponent acc output hacc h]
  exact h

theorem mod_pow_success_requires_bit_fuel (fuel b exponent acc output : Nat)
    (h : WhirFinal.modPowLoop fuel b exponent acc = some output) : exponent < 2 ^ fuel := by
  induction fuel generalizing b exponent acc with
  | zero =>
      simp only [WhirFinal.modPowLoop] at h
      split at h
      · simp [‹exponent = 0›]
      · contradiction
  | succ fuel ih =>
      simp only [WhirFinal.modPowLoop] at h
      split at h
      · rw [‹exponent = 0›]
        exact Nat.two_pow_pos _
      · have hb := ih _ _ _ h
        rw [Nat.pow_succ]
        omega

/-- This characterizes model fuel exhaustion separately from arithmetic value. -/
theorem mod_pow_has_output_iff_bit_fuel (fuel b exponent acc : Nat) :
    (∃ output, WhirFinal.modPowLoop fuel b exponent acc = some output) ↔ exponent < 2 ^ fuel := by
  constructor
  · rintro ⟨output,h⟩
    exact mod_pow_success_requires_bit_fuel fuel b exponent acc output h
  · exact WhirFinal.mod_pow_terminates_with_sufficient_bits fuel b exponent acc

theorem mod_pow_fuel_independent (fuel₁ fuel₂ b exponent acc output₁ output₂ : Nat)
    (hacc : acc < modulus)
    (h₁ : WhirFinal.modPowLoop fuel₁ b exponent acc = some output₁)
    (h₂ : WhirFinal.modPowLoop fuel₂ b exponent acc = some output₂) : output₁ = output₂ := by
  exact (mod_pow_success_exact fuel₁ b exponent acc output₁ hacc h₁).trans
    (mod_pow_success_exact fuel₂ b exponent acc output₂ hacc h₂).symm

theorem zero_exponent_returns_accumulator (fuel b acc : Nat) :
    WhirFinal.modPowLoop fuel b 0 acc = some acc := by
  cases fuel <;> simp [WhirFinal.modPowLoop]

theorem inverse_scalar_power_exact (b : Nat) :
    WhirFinal.modPowLoop 64 b (modulus - 2) 1 = some (b ^ (modulus - 2) % modulus) := by
  simpa only [Nat.one_mul] using mod_pow_exact_with_sufficient_bits 64 b (modulus - 2) 1
    (by decide) (by decide)

/-- Exact computation, with no mathematical invertibility conclusion. -/
theorem inverse_exact_if_norm_nonzero (a : Arithmetic.Ext3) (h : WhirFinal.norm a ≠ 0) :
    WhirFinal.inverse a = some (Arithmetic.scalar (WhirFinal.adjugate a)
      (WhirFinal.norm a ^ (modulus - 2) % modulus)) := by
  simp [WhirFinal.inverse, h, inverse_scalar_power_exact]

theorem inverse_has_output_iff_norm_nonzero (a : Arithmetic.Ext3) :
    (∃ output, WhirFinal.inverse a = some output) ↔ WhirFinal.norm a ≠ 0 := by
  constructor
  · rintro ⟨output,h⟩ hn
    simp [WhirFinal.inverse, hn] at h
  · intro hn
    exact ⟨_, inverse_exact_if_norm_nonzero a hn⟩

theorem modulus_minus_one_exponent : modulus - 1 = (modulus - 2) + 1 := by decide

theorem scalar_inverse_product_is_fermat_power (b : Nat) :
    Arithmetic.mul b (b ^ (modulus - 2) % modulus) = b ^ (modulus - 1) % modulus := by
  unfold mul reduce
  rw [nat_mod_mul_right, modulus_minus_one_exponent, Nat.pow_succ, Nat.mul_comm]

/-- The cubic adjugate identity and exact exponentiation meet here. The right
    side is the explicit remaining Fermat expression, not an assumed one. -/
theorem inverse_success_product_is_fermat_power (a : Verifier.Ext3) (output : Arithmetic.Ext3)
    (h : WhirFinal.inverse a.val = some output) :
    Arithmetic.emul a.val output =
      Arithmetic.fromBase (WhirFinal.norm a.val ^ (modulus - 1) % modulus) := by
  obtain ⟨n, hn, hp⟩ := NormIdentity.inverse_success_reduces_to_scalar_product a output h
  rw [inverse_scalar_power_exact] at hn
  have hv : n = WhirFinal.norm a.val ^ (modulus - 2) % modulus := (Option.some.inj hn).symm
  rw [hp, hv, scalar_inverse_product_is_fermat_power]

end Audit.Wire3.ModularPower
