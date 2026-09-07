import Audit.Wire3.EqTableProvenance
import Audit.Wire3.GoldilocksDomain

/-!
# Provenance of the verifying key's `subgroup_gen_powers` (wire v3)

This module DISCHARGES `Audit.Wire3.EqTableProvenance.SubgroupPowersProvenance`,
the one hypothesis the adopted subgroup chain kept visible.  It models, in the
audit's own concrete `Nat`-mod arithmetic, the exact plonky2 derivation that the
wire-v3 verifier recomputes, and proves that the recomputation check accepts a
verifying key IF AND ONLY IF its `subgroup_gen_powers` are the repeated squares
of the generator whose powers fill the prover's evaluation-domain table.

## Rust sources modelled (worktree intmax-plonky2-lean-wire3)

* `field/src/goldilocks_field.rs:76` `TWO_ADICITY = 32`, `:77`
  `CHARACTERISTIC_TWO_ADICITY = TWO_ADICITY`, `:87`
  `POWER_OF_TWO_GENERATOR = GoldilocksField(7277203076849721926)`.
  Modelled as `twoAdicity` and `powerOfTwoGenerator`.
* `field/src/types.rs:359-365` `exp_power_of_2`: `let mut res = *self;
  for _ in 0..power_log { res = res.square(); } res`.  Modelled as
  `expPowerOfTwo`, with one recursive call, matching the loop's single
  accumulator.
* `field/src/types.rs:268-272` `primitive_root_of_unity(n_log)`:
  `assert!(n_log <= Self::TWO_ADICITY); POWER_OF_TWO_GENERATOR.exp_power_of_2(
  TWO_ADICITY - n_log)`.  Modelled as `primitiveRootOfUnity`; the `assert!` is
  the explicit `nLog ≤ 32` hypothesis of the order theorems, which is exactly
  where it is mathematically needed.
* `field/src/types.rs:280-283` `two_adic_subgroup(n_log)` =
  `primitive_root_of_unity(n_log).powers().take(1 << n_log)`, with `:429-431`
  `powers() = shifted_powers(ONE)`, `:433-438` `shifted_powers` and `:577-584`
  `Iterator::next` (`let result = self.current; self.current *= self.base`).
  Modelled as `shiftedPowers` / `twoAdicSubgroup`.
* `plonky2/src/plonk/circuit_builder.rs:1214`
  `let subgroup = F::two_adic_subgroup(degree_bits);`, stored at
  `plonky2/src/plonk/circuit_data.rs:370` (`ProverOnlyCircuitData.subgroup`)
  and `:716-717` (`EvaluationTables.subgroup`, "evaluation domain subgroup of
  order `degree`").  That list is what the norm prover turns into its
  `subgroup` column (`mle/src/permutation/norm_logup.rs:414-491`, field
  `subgroup: Ext3DenseMle::from_base(subgroup)`), i.e. the adopted
  `EqTableProvenance.subgroupTable`.
* `mle/src/verifier_v2.rs:130-147` — THE CHECK:
  `ensure!(vk.subgroup_gen_powers.len() == degree_bits, ...)`;
  `let subgroup = F::two_adic_subgroup(degree_bits);
   let mut value = subgroup.get(1).copied().unwrap_or(F::ONE);
   for _ in 0..degree_bits { powers.push(value); value *= value; }`;
  `ensure!(vk.subgroup_gen_powers == expected_subgroup_gen_powers, ...)`.
  Modelled as `subgroupSecondOrOne` / `squaringLoop` /
  `expectedSubgroupGenPowers` / `checkSubgroupGenPowers`.  The source's
  `unwrap_or(F::ONE)` default read is modelled VERBATIM and then proved dead:
  `two_adic_subgroup_second` shows index `1` is in range for every `1 ≤ nLog`,
  and `primitive_root_zero_bits` shows that at `nLog = 0` the default `F::ONE`
  IS `primitive_root_of_unity(0)`.  No conclusion below lets a default value
  stand in for a source bound.
* `mle/src/prover_v2.rs:250-258` and `:369-377`: the prover fills
  `subgroup_gen_powers` with the same loop from `prover_data.subgroup.get(1)`.
* `mle/src/verifier_v2.rs:396-412` and
  `mle/contracts/src/OuterLogupExt3Verifier.sol:878-893` (`_subgroupEvaluation`),
  `:956` (length) and `:976-977` (canonicality range): the consumers, already
  covered by the adopted
  `EqTableProvenance.bound_subgroup_table_is_subgroup_evaluation`.

## Adopted Lean reused (not re-proved)

`Audit.Wire3.GoldilocksFoundation` (`modulus_prime`, the `Fact` instance,
`nat_mod_power_to_zmod`), `Audit.Wire3.ModularPower` +
`Audit.Wire3.GoldilocksCertificate` (`mod_pow_success_exact`, i.e. the
kernel-checked `WhirFinal.modPowLoop` binary exponentiation),
`Audit.Wire3.Arithmetic` (`mul`/`reduce` on `Nat`),
`Audit.Wire3.GoldilocksExt3Field` (the `CommRing Element` instance whose
`natCast` IS `Norm.embed`), and `Audit.Wire3.EqTableProvenance`
(`baseElement`, `powersFrom`, `subgroupTable`, `generatorPowers`,
`SubgroupPowersProvenance`, `NormColumnProvenance`,
`bound_subgroup_table_is_subgroup_evaluation`,
`fully_bound_target_is_norm_evaluate_of_columns`,
`honest_prover_terminal_of_columns`).  No order fact of
`Audit.Wire3.GoldilocksDomain` is re-proved; that module fixes the WHIR
domain generator `7 ^ ((p-1)/2^k)`, whereas plonky2's evaluation domain uses
the DIFFERENT constant `POWER_OF_TWO_GENERATOR`, so its order is certified here
by the same `modPowLoop` route.

## Boundaries (explicitly NOT proved)

* Nothing here is a soundness, WHIR/PCS, transcript, Fiat--Shamir, memory- or
  compiler-refinement statement.  `Arithmetic.mul` is mathematical `Nat`
  modular arithmetic, not Goldilocks' branch-free `u64` reduction, and not
  Yul/EVM semantics.
* Nothing here says that the VK the verifier checked is the VK the prover's
  circuit produced, nor that `degree_bits` equals the prover's `t.remaining`;
  those remain hypotheses, exactly as in the adopted corollaries.
* The `honest_*` corollary is honest-prover-only, exactly as the adopted
  theorem it restates.
-/

namespace Audit.Wire3.VkSubgroupProvenance

open Audit.Wire3 GoldilocksExt3Field NormDenseRound NormTerminalBinding EqTableProvenance

attribute [local instance 2000] instPowNat

local notation "modP" => Arithmetic.modulus

/-! ## 1. The base-field embedding `Nat → Element` is a ring map

`Verifier.Base` is `Fin Arithmetic.modulus` and carries no `Mul`; the adopted
`EqTableProvenance.baseElement` sends it into the `Element` field via
`Norm.embed`.  Because `GoldilocksExt3Field.instCommRing` defines
`natCast n = ⟨Norm.embed n⟩`, `baseElement` IS the `Nat`-cast of the canonical
value, so multiplicativity of the embedding follows from the ring's own
`Nat.cast_mul` once `(modulus : Element) = 0` is checked.  This is the
arithmetic wrapper the adopted note reported as missing. -/

/-- The base-field embedding as a NAMED function, so that list maps never pick
up Lean's automatic monadic coercion lifting. -/
def embedBase (n : Nat) : Element := (n : Element)

theorem embed_base_exact (n : Nat) : embedBase n = ((n : Nat) : Element) := rfl

theorem base_element_is_cast (b : Verifier.Base) : baseElement b = embedBase b.val := rfl

theorem cast_modulus_zero : ((modP : Nat) : Element) = 0 := by
  apply element_eq
  apply Subtype.eq
  decide

theorem cast_reduce (a : Nat) : ((Arithmetic.reduce a : Nat) : Element) = (a : Element) := by
  have hd : Arithmetic.reduce a = a % modP := rfl
  rw [hd]
  conv_rhs => rw [← Nat.div_add_mod a modP]
  rw [Nat.cast_add, Nat.cast_mul, cast_modulus_zero, zero_mul, zero_add]

theorem cast_mul_base (a b : Nat) :
    ((Arithmetic.mul a b : Nat) : Element) = (a : Element) * (b : Element) := by
  have hd : Arithmetic.mul a b = Arithmetic.reduce (a * b) := rfl
  rw [hd, cast_reduce, Nat.cast_mul]

/-- Distinct canonical base values embed to distinct `Element`s, so an
equality of embedded lists is an equality of the canonical `u64` limbs the
source compares. -/
theorem embed_base_mul (a b : Nat) :
    embedBase (Arithmetic.mul a b) = embedBase a * embedBase b := cast_mul_base a b

theorem embed_base_one : embedBase 1 = 1 := Nat.cast_one

theorem cast_injective_on_canonical {a b : Nat} (ha : a < modP) (hb : b < modP)
    (h : ((a : Nat) : Element) = ((b : Nat) : Element)) : a = b := by
  have hc : Arithmetic.reduce a = Arithmetic.reduce b :=
    congrArg (fun e : Element => e.toVerifier.val.c0) h
  rwa [Arithmetic.reduce_fixed ha, Arithmetic.reduce_fixed hb] at hc

theorem canonical_lists_eq_of_cast_eq : ∀ (a b : List Nat),
    (∀ x ∈ a, x < modP) → (∀ x ∈ b, x < modP) →
    a.map embedBase = b.map embedBase → a = b := by
  intro a
  induction a with
  | nil =>
      intro b _ _ h
      cases b with
      | nil => rfl
      | cons y ys =>
          have hl := congrArg List.length h
          simp only [List.length_map, List.length_nil, List.length_cons] at hl
  | cons x xs ih =>
      intro b ha hb h
      cases b with
      | nil =>
          have hl := congrArg List.length h
          simp only [List.length_map, List.length_nil, List.length_cons] at hl
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          have hx := cast_injective_on_canonical (ha x (List.mem_cons_self _ _))
            (hb y (List.mem_cons_self _ _)) h.1
          subst hx
          rw [ih ys (fun z hz => ha z (List.mem_cons_of_mem _ hz))
            (fun z hz => hb z (List.mem_cons_of_mem _ hz)) h.2]

theorem map_base_element (l : List Verifier.Base) :
    l.map baseElement = (l.map Fin.val).map embedBase := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, ih, base_element_is_cast]

/-! ## 2. plonky2's Goldilocks two-adic constants and derivation -/

/-- `field/src/goldilocks_field.rs:76-77`. -/
def twoAdicity : Nat := 32

/-- `field/src/goldilocks_field.rs:87`. -/
def powerOfTwoGenerator : Nat := 7277203076849721926

theorem power_of_two_generator_canonical : powerOfTwoGenerator < modP := by decide

/-- `Field::square` on Goldilocks, i.e. `mulmod` by itself. -/
def square (a : Nat) : Nat := Arithmetic.mul a a

/-- `field/src/types.rs:359-365`. -/
def expPowerOfTwo (b : Nat) : Nat → Nat
  | 0 => b
  | k + 1 => square (expPowerOfTwo b k)

theorem exp_power_of_two_value (b : Nat) (hb : b < modP) (k : Nat) :
    expPowerOfTwo b k = b ^ (2 ^ k) % modP := by
  induction k with
  | zero =>
      have h0 : expPowerOfTwo b 0 = b := rfl
      rw [h0, Nat.pow_zero, Nat.pow_one, Nat.mod_eq_of_lt hb]
  | succ k ih =>
      have hs : expPowerOfTwo b (k + 1) =
          Arithmetic.mul (expPowerOfTwo b k) (expPowerOfTwo b k) := rfl
      have hm : ∀ x y : Nat, Arithmetic.mul x y = x * y % modP := fun _ _ => rfl
      rw [hs, hm, ih, ← Nat.mul_mod, ← Nat.pow_add]
      have h2 : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      rw [h2]

theorem exp_power_of_two_canonical (b : Nat) (hb : b < modP) (k : Nat) :
    expPowerOfTwo b k < modP := by
  rw [exp_power_of_two_value b hb k]
  exact Nat.mod_lt _ Arithmetic.modulus_positive

/-- `field/src/types.rs:268-272`. -/
def primitiveRootOfUnity (nLog : Nat) : Nat :=
  expPowerOfTwo powerOfTwoGenerator (twoAdicity - nLog)

theorem primitive_root_canonical (nLog : Nat) : primitiveRootOfUnity nLog < modP :=
  exp_power_of_two_canonical _ power_of_two_generator_canonical _

/-- `field/src/types.rs:433-438` with `:577-584`: `current` is emitted, then
multiplied by `base`; `:429-431` starts `current` at `ONE`. -/
def shiftedPowers (g : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | v, k + 1 => v :: shiftedPowers g (Arithmetic.mul v g) k

/-- `field/src/types.rs:280-283`. -/
def twoAdicSubgroup (nLog : Nat) : List Nat :=
  shiftedPowers (primitiveRootOfUnity nLog) 1 (2 ^ nLog)

theorem shifted_powers_length (g : Nat) : ∀ (v k : Nat), (shiftedPowers g v k).length = k
  | _, 0 => rfl
  | v, k + 1 => by
      have h : shiftedPowers g v (k + 1) = v :: shiftedPowers g (Arithmetic.mul v g) k := rfl
      rw [h, List.length_cons, shifted_powers_length g (Arithmetic.mul v g) k]

theorem two_adic_subgroup_length (nLog : Nat) : (twoAdicSubgroup nLog).length = 2 ^ nLog :=
  shifted_powers_length _ _ _

theorem shifted_powers_getD (g : Nat) : ∀ (k v i d : Nat), v < modP → i < k →
    (shiftedPowers g v k).getD i d = v * g ^ i % modP
  | 0, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, v, 0, _, hv, _ => by
      have h : shiftedPowers g v (k + 1) = v :: shiftedPowers g (Arithmetic.mul v g) k := rfl
      rw [h, List.getD_cons_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hv]
  | k + 1, v, i + 1, d, _, hi => by
      have h : shiftedPowers g v (k + 1) = v :: shiftedPowers g (Arithmetic.mul v g) k := rfl
      have hmul : Arithmetic.mul v g = v * g % modP := rfl
      rw [h, List.getD_cons_succ,
        shifted_powers_getD g k (Arithmetic.mul v g) i d
          (by rw [hmul]; exact Nat.mod_lt _ Arithmetic.modulus_positive) (by omega),
        hmul, Nat.mod_mul_mod, Nat.pow_succ]
      congr 1
      ac_rfl

/-- Index `i < 2 ^ nLog` is IN RANGE, so the value does not depend on the
default `d`: this lemma is a source-bound read, not a default read. -/
theorem two_adic_subgroup_getD (nLog i d : Nat) (hi : i < 2 ^ nLog) :
    (twoAdicSubgroup nLog).getD i d = primitiveRootOfUnity nLog ^ i % modP := by
  rw [twoAdicSubgroup, shifted_powers_getD _ _ 1 i d (by decide) hi, Nat.one_mul]

/-! ## 3. Order of the derived root of unity

The certificates are kernel-checked with the adopted `WhirFinal.modPowLoop`
binary exponentiation, exactly as `GoldilocksCertificate` does for the base
seven.  The two bridge lemmas keep base and exponent as VARIABLES, so no
declaration in this file carries a closed `Nat` power with a 2^32-sized
exponent. -/

theorem mod_pow_from_loop (b e v : Nat) (h : WhirFinal.modPowLoop 64 b e 1 = some v) :
    b ^ e % modP = v := by
  have h2 := ModularPower.mod_pow_success_exact 64 b e 1 v (by decide) h
  rw [Nat.one_mul] at h2
  exact h2.symm

theorem loop_to_zmod (b e v : Nat) (hv : v < modP)
    (h : WhirFinal.modPowLoop 64 b e 1 = some v) :
    ((b : Nat) : ZMod modP) ^ e = ((v : Nat) : ZMod modP) :=
  GoldilocksFoundation.nat_mod_power_to_zmod b e v hv (mod_pow_from_loop b e v h)

set_option maxRecDepth 8192 in
theorem power_of_two_generator_full_loop :
    WhirFinal.modPowLoop 64 powerOfTwoGenerator (2 ^ 32) 1 = some 1 := by decide

set_option maxRecDepth 8192 in
theorem power_of_two_generator_half_loop :
    WhirFinal.modPowLoop 64 powerOfTwoGenerator (2 ^ 31) 1
      = some 18446744069414584320 := by decide

theorem power_of_two_generator_full_power :
    ((powerOfTwoGenerator : Nat) : ZMod modP) ^ (2 ^ 32) = 1 := by
  have h := loop_to_zmod powerOfTwoGenerator (2 ^ 32) 1 (by decide)
    power_of_two_generator_full_loop
  rwa [Nat.cast_one] at h

theorem power_of_two_generator_half_power :
    ((powerOfTwoGenerator : Nat) : ZMod modP) ^ (2 ^ 31)
      = ((18446744069414584320 : Nat) : ZMod modP) :=
  loop_to_zmod powerOfTwoGenerator (2 ^ 31) 18446744069414584320 (by decide)
    power_of_two_generator_half_loop

theorem minus_one_cast_ne_one : ((18446744069414584320 : Nat) : ZMod modP) ≠ 1 := by
  intro h
  have h1 : ((18446744069414584320 : Nat) : ZMod modP) = ((1 : Nat) : ZMod modP) := by
    rw [h, Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  revert h1
  decide

/-- (1) `POWER_OF_TWO_GENERATOR` really generates the full two-adic subgroup:
its order is exactly `2 ^ TWO_ADICITY`.  Nothing is taken from the Sage comment
at `goldilocks_field.rs:81-86`; the two kernel certificates force it. -/
theorem power_of_two_generator_order :
    orderOf ((powerOfTwoGenerator : Nat) : ZMod modP) = 2 ^ 32 := by
  have hdvd : orderOf ((powerOfTwoGenerator : Nat) : ZMod modP) ∣ 2 ^ 32 :=
    orderOf_dvd_of_pow_eq_one power_of_two_generator_full_power
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases Nat.lt_or_ge j 32 with hlt | hge
  · exfalso
    have hdd : orderOf ((powerOfTwoGenerator : Nat) : ZMod modP) ∣ 2 ^ 31 := by
      rw [hjo]
      exact Nat.pow_dvd_pow 2 (by omega)
    have hone := orderOf_dvd_iff_pow_eq_one.mp hdd
    rw [power_of_two_generator_half_power] at hone
    exact minus_one_cast_ne_one hone
  · rw [hjo, le_antisymm hj hge]

theorem primitive_root_cast (nLog : Nat) :
    ((primitiveRootOfUnity nLog : Nat) : ZMod modP)
      = ((powerOfTwoGenerator : Nat) : ZMod modP) ^ (2 ^ (twoAdicity - nLog)) := by
  have hv := exp_power_of_two_value powerOfTwoGenerator power_of_two_generator_canonical
    (twoAdicity - nLog)
  have h := GoldilocksFoundation.nat_mod_power_to_zmod powerOfTwoGenerator
    (2 ^ (twoAdicity - nLog)) (powerOfTwoGenerator ^ (2 ^ (twoAdicity - nLog)) % modP)
    (Nat.mod_lt _ Arithmetic.modulus_positive) rfl
  show ((expPowerOfTwo powerOfTwoGenerator (twoAdicity - nLog) : Nat) : ZMod modP) = _
  rw [hv, ← h]

/-- (2a) The generator plonky2 derives for `degree_bits = nLog` has order
EXACTLY `2 ^ nLog`.  This is where the source's
`assert!(n_log <= Self::TWO_ADICITY)` is needed; it appears as `hn`. -/
theorem primitive_root_order_exact (nLog : Nat) (hn : nLog ≤ 32) :
    orderOf ((primitiveRootOfUnity nLog : Nat) : ZMod modP) = 2 ^ nLog := by
  have hdvd : 2 ^ nLog ∣ orderOf ((powerOfTwoGenerator : Nat) : ZMod modP) := by
    rw [power_of_two_generator_order]
    exact Nat.pow_dvd_pow 2 hn
  have hne : orderOf ((powerOfTwoGenerator : Nat) : ZMod modP) ≠ 0 := by
    rw [power_of_two_generator_order]
    decide
  have h := orderOf_pow_orderOf_div (x := ((powerOfTwoGenerator : Nat) : ZMod modP)) hne hdvd
  rw [power_of_two_generator_order, Nat.pow_div hn (by decide)] at h
  rw [primitive_root_cast]
  exact h

theorem primitive_root_full_power (nLog : Nat) (hn : nLog ≤ 32) :
    ((primitiveRootOfUnity nLog : Nat) : ZMod modP) ^ (2 ^ nLog) = 1 := by
  rw [← primitive_root_order_exact nLog hn]
  exact pow_orderOf_eq_one _

theorem primitive_root_no_smaller_power (nLog e : Nat) (hn : nLog ≤ 32)
    (he : 0 < e) (hlt : e < 2 ^ nLog) :
    ((primitiveRootOfUnity nLog : Nat) : ZMod modP) ^ e ≠ 1 := by
  apply pow_ne_one_of_lt_orderOf (by omega)
  rw [primitive_root_order_exact nLog hn]
  exact hlt

theorem two_adic_subgroup_getD_cast (nLog i : Nat) (hi : i < 2 ^ nLog) :
    (((twoAdicSubgroup nLog).getD i 0 : Nat) : ZMod modP)
      = ((primitiveRootOfUnity nLog : Nat) : ZMod modP) ^ i := by
  rw [two_adic_subgroup_getD nLog i 0 hi]
  exact (GoldilocksFoundation.nat_mod_power_to_zmod (primitiveRootOfUnity nLog) i
    (primitiveRootOfUnity nLog ^ i % modP)
    (Nat.mod_lt _ Arithmetic.modulus_positive) rfl).symm

/-- (2b) The listed domain has `2 ^ nLog` PAIRWISE DISTINCT canonical entries:
`two_adic_subgroup` really enumerates a subgroup of that size. -/
theorem two_adic_subgroup_entries_distinct (nLog : Nat) (hn : nLog ≤ 32) (i j : Nat)
    (hi : i < 2 ^ nLog) (hj : j < 2 ^ nLog) (hij : i ≠ j) :
    (twoAdicSubgroup nLog).getD i 0 ≠ (twoAdicSubgroup nLog).getD j 0 := by
  intro h
  apply hij
  have hc : ((primitiveRootOfUnity nLog : Nat) : ZMod modP) ^ i
      = ((primitiveRootOfUnity nLog : Nat) : ZMod modP) ^ j := by
    rw [← two_adic_subgroup_getD_cast nLog i hi, ← two_adic_subgroup_getD_cast nLog j hj, h]
  apply pow_injOn_Iio_orderOf (x := ((primitiveRootOfUnity nLog : Nat) : ZMod modP)) ?_ ?_ hc
  · show i < orderOf ((primitiveRootOfUnity nLog : Nat) : ZMod modP)
    rw [primitive_root_order_exact nLog hn]
    exact hi
  · show j < orderOf ((primitiveRootOfUnity nLog : Nat) : ZMod modP)
    rw [primitive_root_order_exact nLog hn]
    exact hj

/-! ## 4. The verifier's recomputation (verifier_v2.rs:130-147) -/

/-- `subgroup.get(1).copied().unwrap_or(F::ONE)` (verifier_v2.rs:136,
prover_v2.rs:252), modelled verbatim, default included. -/
def subgroupSecondOrOne (nLog : Nat) : Nat := (twoAdicSubgroup nLog).getD 1 1

/-- `for _ in 0..degree_bits { powers.push(value); value *= value; }`. -/
def squaringLoop (v : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => v :: squaringLoop (Arithmetic.mul v v) k

def expectedSubgroupGenPowers (nLog : Nat) : List Nat :=
  squaringLoop (subgroupSecondOrOne nLog) nLog

theorem squaring_loop_length : ∀ (v k : Nat), (squaringLoop v k).length = k
  | _, 0 => rfl
  | v, k + 1 => by
      have h : squaringLoop v (k + 1) = v :: squaringLoop (Arithmetic.mul v v) k := rfl
      rw [h, List.length_cons, squaring_loop_length (Arithmetic.mul v v) k]

theorem expected_powers_length (nLog : Nat) :
    (expectedSubgroupGenPowers nLog).length = nLog := squaring_loop_length _ _

theorem squaring_loop_canonical : ∀ (k v : Nat), v < modP → ∀ x ∈ squaringLoop v k, x < modP
  | 0, v, _, x, hx => by
      have h : squaringLoop v 0 = [] := rfl
      rw [h] at hx
      exact absurd hx (List.not_mem_nil x)
  | k + 1, v, hv, x, hx => by
      have h : squaringLoop v (k + 1) = v :: squaringLoop (Arithmetic.mul v v) k := rfl
      rw [h, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hv
      · exact squaring_loop_canonical k (Arithmetic.mul v v) (Arithmetic.mul_canonical _ _) x hx

set_option maxRecDepth 8192 in
/-- `primitive_root_of_unity(0) = POWER_OF_TWO_GENERATOR.exp_power_of_2(32) = 1`,
so at `degree_bits = 0` the `unwrap_or(F::ONE)` default is not standing in for a
missing value: it is the same value. -/
theorem primitive_root_zero_bits : primitiveRootOfUnity 0 = 1 := by decide

/-- The `get(1)` read is IN RANGE for every `1 ≤ nLog`: the `unwrap_or` default
branch is dead there, and index `1` holds the primitive root. -/
theorem two_adic_subgroup_second (nLog : Nat) (hn : 1 ≤ nLog) :
    subgroupSecondOrOne nLog = primitiveRootOfUnity nLog := by
  have hlen : 1 < 2 ^ nLog := by
    calc 1 < 2 ^ 1 := by decide
      _ ≤ 2 ^ nLog := Nat.pow_le_pow_right (by decide) hn
  rw [subgroupSecondOrOne, two_adic_subgroup_getD nLog 1 1 hlen, Nat.pow_one,
    Nat.mod_eq_of_lt (primitive_root_canonical nLog)]

theorem subgroup_second_is_primitive_root (nLog : Nat) :
    subgroupSecondOrOne nLog = primitiveRootOfUnity nLog := by
  cases nLog with
  | zero =>
      rw [primitive_root_zero_bits]
      rfl
  | succ k => exact two_adic_subgroup_second (k + 1) (Nat.succ_le_succ (Nat.zero_le k))

theorem expected_powers_canonical (nLog : Nat) :
    ∀ x ∈ expectedSubgroupGenPowers nLog, x < modP := by
  rw [expectedSubgroupGenPowers, subgroup_second_is_primitive_root]
  exact squaring_loop_canonical _ _ (primitive_root_canonical nLog)

/-! ## 5. Embedding the source lists into the adopted `Element` model -/

theorem cast_shifted_powers (g : Nat) : ∀ (k v : Nat),
    (shiftedPowers g v k).map embedBase
      = powersFrom (g : Element) (v : Element) k
  | 0, _ => rfl
  | k + 1, v => by
      have h : shiftedPowers g v (k + 1) = v :: shiftedPowers g (Arithmetic.mul v g) k := rfl
      have hp : powersFrom (g : Element) (v : Element) (k + 1)
          = (v : Element) :: powersFrom (g : Element) ((v : Element) * (g : Element)) k := rfl
      rw [h, hp, List.map_cons, cast_shifted_powers g k (Arithmetic.mul v g), cast_mul_base,
        embed_base_exact]

/-- The prover's evaluation-domain column IS the adopted `subgroupTable` of the
embedded `primitive_root_of_unity(nLog)`. -/
theorem cast_two_adic_subgroup (nLog : Nat) :
    (twoAdicSubgroup nLog).map embedBase
      = subgroupTable ((primitiveRootOfUnity nLog : Nat) : Element) nLog := by
  rw [twoAdicSubgroup, cast_shifted_powers, subgroupTable, Nat.cast_one]

theorem cast_squaring_loop : ∀ (k v : Nat),
    (squaringLoop v k).map embedBase = generatorPowers (v : Element) k
  | 0, _ => rfl
  | k + 1, v => by
      have h : squaringLoop v (k + 1) = v :: squaringLoop (Arithmetic.mul v v) k := rfl
      have hg : generatorPowers (v : Element) (k + 1)
          = (v : Element) :: generatorPowers ((v : Element) * (v : Element)) k := rfl
      rw [h, hg, List.map_cons, cast_squaring_loop k (Arithmetic.mul v v), cast_mul_base,
        embed_base_exact]

/-- The `Element`-level generator of the evaluation domain of `2 ^ nLog` rows. -/
def subgroupGenerator (nLog : Nat) : Element := ((primitiveRootOfUnity nLog : Nat) : Element)

/-- (2c) THE derivation theorem: the source's `expected_subgroup_gen_powers`
ARE the repeated squares `g, g^2, g^4, …` of the generator whose powers fill
the prover's `two_adic_subgroup` table. -/
theorem expected_powers_are_generator_powers (nLog : Nat) :
    (expectedSubgroupGenPowers nLog).map embedBase
      = generatorPowers (subgroupGenerator nLog) nLog := by
  rw [expectedSubgroupGenPowers, cast_squaring_loop, subgroup_second_is_primitive_root,
    subgroupGenerator]

/-! ## 6. The check, and what an accepted VK determines -/

inductive Rejection where
  | wrongLength
  | notCanonical
  deriving DecidableEq

/-- `mle/src/verifier_v2.rs:130-147`: both `ensure!`s, with the source's own
rejection rather than any default-value fallback. -/
def checkSubgroupGenPowers (degreeBits : Nat) (vkPowers : List Verifier.Base) :
    Except Rejection Unit :=
  if vkPowers.length ≠ degreeBits then .error .wrongLength
  else if vkPowers.map Fin.val ≠ expectedSubgroupGenPowers degreeBits then .error .notCanonical
  else .ok ()

theorem check_rejects_wrong_length (degreeBits : Nat) (vkPowers : List Verifier.Base)
    (h : vkPowers.length ≠ degreeBits) :
    checkSubgroupGenPowers degreeBits vkPowers = .error .wrongLength := by
  rw [checkSubgroupGenPowers, if_pos h]

theorem check_accepts_iff (degreeBits : Nat) (vkPowers : List Verifier.Base) :
    checkSubgroupGenPowers degreeBits vkPowers = .ok ()
      ↔ vkPowers.map Fin.val = expectedSubgroupGenPowers degreeBits := by
  constructor
  · intro h
    unfold checkSubgroupGenPowers at h
    split at h
    · exact h.elim
    · split at h
      · exact h.elim
      · rename_i hne
        exact not_not.mp hne
  · intro he
    have hlen : vkPowers.length = degreeBits := by
      rw [← List.length_map vkPowers Fin.val, he, expected_powers_length]
    unfold checkSubgroupGenPowers
    rw [if_neg (fun hc => hc hlen), if_neg (fun hc => hc he)]

theorem vk_powers_canonical (vkPowers : List Verifier.Base) :
    ∀ x ∈ vkPowers.map Fin.val, x < modP := by
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  exact b.isLt

/-- (3) THE discharge.  A verifying key PASSES the source's recomputation check
at `verifier_v2.rs:130-147` EXACTLY when it satisfies the adopted, previously
assumed, `SubgroupPowersProvenance` for the generator of the evaluation domain
of `2 ^ degreeBits` rows.  Nothing is read out of range and no default value
stands in for a source bound.

SOURCE REGIME.  `field/src/types.rs:269` asserts `n_log <= TWO_ADICITY = 32`
and PANICS above it, whereas Lean's truncated `twoAdicity - nLog` makes
`primitiveRootOfUnity nLog = powerOfTwoGenerator` for `nLog > 32`, so this
model ACCEPTS in a regime where the source aborts.  The iff is therefore
faithful to source behaviour exactly for `degreeBits <= 32`.  That regime is
unreachable for any deployable configuration -- `Verifier.envelope` forces
`degreeBits <= 13` -- so no corollary below carries the bound as a hypothesis;
it is recorded here rather than silently ignored. -/
theorem check_accepts_iff_provenance (degreeBits : Nat) (vkPowers : List Verifier.Base) :
    checkSubgroupGenPowers degreeBits vkPowers = .ok ()
      ↔ (vkPowers.length = degreeBits ∧
          SubgroupPowersProvenance vkPowers (subgroupGenerator degreeBits) degreeBits) := by
  constructor
  · intro h
    have hv := (check_accepts_iff degreeBits vkPowers).mp h
    refine ⟨?_, ?_⟩
    · rw [← List.length_map vkPowers Fin.val, hv, expected_powers_length]
    · show vkPowers.map baseElement = generatorPowers (subgroupGenerator degreeBits) degreeBits
      rw [map_base_element, hv, expected_powers_are_generator_powers]
  · rintro ⟨_, hp⟩
    have hp' : vkPowers.map baseElement
        = generatorPowers (subgroupGenerator degreeBits) degreeBits := hp
    rw [map_base_element, ← expected_powers_are_generator_powers] at hp'
    exact (check_accepts_iff degreeBits vkPowers).mpr
      (canonical_lists_eq_of_cast_eq _ _ (vk_powers_canonical vkPowers)
        (expected_powers_canonical degreeBits) hp')

theorem accepted_vk_has_subgroup_powers_provenance (degreeBits : Nat)
    (vkPowers : List Verifier.Base)
    (h : checkSubgroupGenPowers degreeBits vkPowers = .ok ()) :
    SubgroupPowersProvenance vkPowers (subgroupGenerator degreeBits) degreeBits :=
  ((check_accepts_iff_provenance degreeBits vkPowers).mp h).2

/-! ## 7. Corollaries: the adopted results with the hypothesis discharged -/

/-- The norm prover's structural columns stated ENTIRELY in source terms: the
subgroup column is the embedded `F::two_adic_subgroup(degree_bits)` list, and
the VK merely passed the verifier's own recomputation check. -/
structure VkNormColumnProvenance (t : Tables) (c : Verifier.Config) (ch : Norm.Challenges)
    (tau : List Element) (degreeBits : Nat) : Prop where
  eqColumn : t.eq = eqTable tau
  tauValues : values tau = ch.tau
  tauWidth : tau.length = t.remaining
  /-- The ONE identification this module does not itself derive: the circuit's
  `degree_bits` (the `common_data.degree_bits()` the verifier checks against at
  `verifier_v2.rs:131`) is the norm state's variable width.  It is named here
  rather than silently assumed. -/
  degreeMatchesWidth : degreeBits = t.remaining
  subgroupColumn : t.subgroup = (twoAdicSubgroup degreeBits).map embedBase
  vkAccepted : checkSubgroupGenPowers degreeBits c.subgroupPowers = .ok ()

theorem vk_norm_column_provenance (t : Tables) (c : Verifier.Config) (ch : Norm.Challenges)
    (tau : List Element) (degreeBits : Nat)
    (hprov : VkNormColumnProvenance t c ch tau degreeBits) :
    NormColumnProvenance t c ch tau (subgroupGenerator degreeBits) := by
  obtain ⟨heq, htv, htw, hd, hsub, hok⟩ := hprov
  subst hd
  exact
    { eqColumn := heq
      tauValues := htv
      tauWidth := htw
      subgroupColumn := by rw [hsub, cast_two_adic_subgroup]; rfl
      powers := accepted_vk_has_subgroup_powers_provenance _ c.subgroupPowers hok }

/-- (4) The adopted subgroup-evaluation theorem with the hypothesis replaced by
the VK check. -/
theorem bound_subgroup_table_is_subgroup_evaluation_of_vk (n : Nat) (point : List Element)
    (vkPowers : List Verifier.Base) (hp : point.length = n)
    (hok : checkSubgroupGenPowers n vkPowers = .ok ()) :
    (cell (bindColumn ((twoAdicSubgroup n).map embedBase) point)).toVerifier
      = Norm.subgroupEvaluation vkPowers (values point) := by
  rw [cast_two_adic_subgroup]
  exact bound_subgroup_table_is_subgroup_evaluation ((primitiveRootOfUnity n : Nat) : Element)
    n point vkPowers hp (accepted_vk_has_subgroup_powers_provenance n vkPowers hok)

/-- (4) `EqTableProvenance.fully_bound_target_is_norm_evaluate_of_columns` with
`SubgroupPowersProvenance` GONE: it is now derived from "the VK passed
`verifier_v2.rs:130-147`". -/
theorem fully_bound_target_is_norm_evaluate_of_vk
    (t t' : Tables) (prep : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (point : List Element) (tau : List Element)
    (degreeBits : Nat)
    (h : Shape t prep) (hpoint : point.length = t.remaining)
    (hb : bindTablesMany point t = some t')
    (hprov : VkNormColumnProvenance t c prep.challenges tau degreeBits)
    (hc : Compatible c t' prep constants) (hlam : LambdaProvenance prep)
    (hmap : WireMapMatches c.publicInputWireMap t'.bindings)
    (heta : EtaProvenance (NormPolynomial.lift prep.challenges.eta) t'.bindings)
    (hprefix : PrefixAt (values point) t'.bindings) :
    Shape t' prep ∧ FullyBound t' ∧
      terminalTarget t' prep
        = some (Norm.evaluate c prep.challenges (toTerminalInput t' constants extra)
            (values point)) :=
  fully_bound_target_is_norm_evaluate_of_columns t t' prep c constants extra point tau
    (subgroupGenerator degreeBits) h hpoint hb
    (vk_norm_column_provenance t c prep.challenges tau degreeBits hprov)
    hc hlam hmap heta hprefix

/-- (4) HONEST PROVER ONLY, exactly as the adopted theorem it restates.
`EqTableProvenance.honest_prover_terminal_of_columns` with
`SubgroupPowersProvenance` discharged from the VK check. -/
theorem honest_prover_terminal_of_vk (t : Tables) (prep : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (point : List Element)
    (pairs : List (Nat × Nat × Verifier.Base)) (tau : List Element) (degreeBits : Nat)
    (h : Shape t prep) (h0 : t.boundVariables = 0) (hpoint : point.length = t.remaining)
    (hbuild : t.bindings = buildBindings (NormPolynomial.lift prep.challenges.eta) 1 pairs)
    (hc : Compatible c t prep constants) (hlam : LambdaProvenance prep)
    (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (hprov : VkNormColumnProvenance t c prep.challenges tau degreeBits) :
    ∃ t', bindTablesMany point t = some t' ∧ FullyBound t' ∧
      PrefixAt (point.map Element.toVerifier) t'.bindings ∧
      terminalTarget t' prep
        = some (Norm.evaluate c prep.challenges (toTerminalInput t' constants extra)
            (values point)) :=
  honest_prover_terminal_of_columns t prep c constants extra point pairs tau
    (subgroupGenerator degreeBits) h h0 hpoint hbuild hc hlam hmap
    (vk_norm_column_provenance t c prep.challenges tau degreeBits hprov)

/-! ## 8. Concrete small-degree examples -/

set_option maxRecDepth 8192 in
theorem primitive_root_one : primitiveRootOfUnity 1 = 18446744069414584320 := by decide

set_option maxRecDepth 8192 in
theorem primitive_root_two : primitiveRootOfUnity 2 = 281474976710656 := by decide

set_option maxRecDepth 8192 in
theorem primitive_root_three : primitiveRootOfUnity 3 = 16777216 := by decide

set_option maxRecDepth 8192 in
theorem two_adic_subgroup_one_example :
    twoAdicSubgroup 1 = [1, 18446744069414584320] := by decide

set_option maxRecDepth 8192 in
theorem expected_powers_one_example :
    expectedSubgroupGenPowers 1 = [18446744069414584320] := by decide

set_option maxRecDepth 8192 in
theorem two_adic_subgroup_two_example :
    twoAdicSubgroup 2 = [1, 281474976710656, 18446744069414584320,
      18446462594437873665] := by decide

set_option maxRecDepth 8192 in
theorem expected_powers_two_example :
    expectedSubgroupGenPowers 2 = [281474976710656, 18446744069414584320] := by decide

theorem example_root_order_two :
    orderOf ((primitiveRootOfUnity 2 : Nat) : ZMod modP) = 4 :=
  primitive_root_order_exact 2 (by decide)

def exampleVk2 : List Verifier.Base :=
  [⟨281474976710656, by decide⟩, ⟨18446744069414584320, by decide⟩]

set_option maxRecDepth 8192 in
theorem example_vk2_accepted : checkSubgroupGenPowers 2 exampleVk2 = .ok () :=
  (check_accepts_iff 2 exampleVk2).mpr (by decide)

theorem example_vk2_provenance :
    SubgroupPowersProvenance exampleVk2 (subgroupGenerator 2) 2 :=
  accepted_vk_has_subgroup_powers_provenance 2 exampleVk2 example_vk2_accepted

set_option maxRecDepth 8192 in
theorem expected_powers_three_example :
    expectedSubgroupGenPowers 3 = [16777216, 281474976710656, 18446744069414584320] := by decide

theorem example_root_order_one :
    orderOf ((primitiveRootOfUnity 1 : Nat) : ZMod modP) = 2 :=
  primitive_root_order_exact 1 (by decide)

theorem example_root_order_three :
    orderOf ((primitiveRootOfUnity 3 : Nat) : ZMod modP) = 8 :=
  primitive_root_order_exact 3 (by decide)

def exampleVk1 : List Verifier.Base := [⟨18446744069414584320, by decide⟩]

def exampleVk3 : List Verifier.Base :=
  [⟨16777216, by decide⟩, ⟨281474976710656, by decide⟩, ⟨18446744069414584320, by decide⟩]

set_option maxRecDepth 8192 in
theorem example_vk1_accepted : checkSubgroupGenPowers 1 exampleVk1 = .ok () :=
  (check_accepts_iff 1 exampleVk1).mpr (by decide)

set_option maxRecDepth 8192 in
theorem example_vk3_accepted : checkSubgroupGenPowers 3 exampleVk3 = .ok () :=
  (check_accepts_iff 3 exampleVk3).mpr (by decide)

theorem example_vk1_provenance :
    SubgroupPowersProvenance exampleVk1 (subgroupGenerator 1) 1 :=
  accepted_vk_has_subgroup_powers_provenance 1 exampleVk1 example_vk1_accepted

theorem example_vk3_provenance :
    SubgroupPowersProvenance exampleVk3 (subgroupGenerator 3) 3 :=
  accepted_vk_has_subgroup_powers_provenance 3 exampleVk3 example_vk3_accepted

def exampleVk3Perturbed : List Verifier.Base :=
  [⟨16777217, by decide⟩, ⟨281474976710656, by decide⟩, ⟨18446744069414584320, by decide⟩]

set_option maxRecDepth 8192 in
theorem example_vk3_perturbed_rejected :
    checkSubgroupGenPowers 3 exampleVk3Perturbed ≠ .ok () := by
  intro h
  have hv := (check_accepts_iff 3 exampleVk3Perturbed).mp h
  revert hv
  decide

theorem example_vk3_wrong_length_rejected :
    checkSubgroupGenPowers 3 exampleVk1 = .error .wrongLength :=
  check_rejects_wrong_length 3 exampleVk1 (by decide)

end Audit.Wire3.VkSubgroupProvenance
