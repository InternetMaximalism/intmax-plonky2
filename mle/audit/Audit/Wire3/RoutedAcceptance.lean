import Audit.Wire3.DerivedAcceptance
import Audit.Wire3.IndexHalfTransport
import Audit.Wire3.OuterInitial
import Audit.Wire3.CommitmentOrder

/-!
# Routed acceptance: `numRouted = 80` at a digest-ignoring hash

**THE TRADE, STATED FIRST.**  This module exhibits `Verifier.verify` accepting at
`numRouted = 80` on the adopted `DerivedAcceptance.derivedEngine`.  **It does NOT
remove the last degenerate pin without cost.**  `routedHash` answers on the
counter suffix of the challenge input and ignores the digest
(`routed_hash_is_a_transcript_collision`).  Derived relation challenges
(`rho`, `lambda`, `kappa`, `beta`) are independent of the statement
(`rho_ignores_the_statement`): two proofs that differ in `normInverseRoot` share
every one of them, and BOTH accept (`alt_proof_is_also_accepted`).  The adopted
dependence implication holds here because its collision disjunct is true -- the
same pattern `DerivedAcceptance.constantHash` was introduced to witness, except
that module used the collapsing hash as a REFUTATION witness and this module
uses one as the ACCEPTING hash.  **Headline: the acceptance line does not now
have both routed wires and proof-dependent challenges.**  Universal
quantification over `thash` was already disclosed as the price; proof-independence
of the challenges is the other half of that price.

**WHAT THIS MODULE ESTABLISHES.**  The adopted `Audit.Wire3.DerivedAcceptance`
exhibits `Verifier.verify` accepting on an engine ten of whose twelve fields are
the adopted concrete components, at `degreeBits 13`, `numWires 160`,
`numConstants 80`, `indexBits 8`, `quotientDegree 8` -- but with `numRouted = 0`,
which is literally one of the three quantities the original degeneracy forced and
which the adopted `NonDegenerateAcceptance.maximalConfig` carries at `80`.
`routedConfig` is `DerivedAcceptance.derivedConfig` with `numRouted` moved from
`0` to `80` -- the ceiling `Verifier.envelope` permits
(`envelope_caps_the_routed_count`) and the value `maximalConfig` carries -- and
`kIs` lengthened to match; `routed_config_agrees_with_the_derived_config_off_the_routed_wires`
states that NOTHING else moved.  The headline is

    `Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash P) (routedPin khash) 1
       routedConfig routedProof = .ok ()`

under the single hypothesis `PinnedWhirProfile.profileOk P routedConfig = true`,
discharged at the adopted stand-in profile
(`routed_acceptance_at_the_profile_witness`) and at the adopted SHARP profile
(`routed_acceptance_at_the_sharp_profile`); and the same instance again through
the adopted `Integrated.verify` (`routed_integrated_acceptance`), whose checked
norm adapter enforces the FULL `Norm.shapeValid` predicate including
`c.kIs.length = c.numRouted` at eighty (`routed_norm_shape_valid`).  The ENGINE
is LITERALLY the adopted `DerivedAcceptance.derivedEngine`, and the claims record
is LITERALLY the adopted `IndexHalfTransport.matchingClaims`, at the new
configuration.  `khash` remains UNIVERSALLY QUANTIFIED, and so does the WHIR
profile `P` (under the profile hypothesis).

**HOW THE OBSTRUCTION IS DEFEATED -- ROUTE (b), NOT ROUTE (a).**  The adopted
`DerivedAcceptance.probe_acceptance_at_one_routed_wire_forces_a_challenge_coincidence`
proves that acceptance at a routed wire with the adopted all-zero norm-inverse
column is EQUIVALENT to `eq(tau, logPoint) * ((0 - 1) + rho * (0 - 1)) = 0`.
This module makes the SECOND factor vanish, by exhibiting a transcript hash at
which the derived `rho` is exactly `-1` (`routed_rho_is_minus_one`), so that
`1 + rho = 0`; the first factor is untouched.
`routed_hash_realises_the_adopted_challenge_coincidence` states exactly that, in
the adopted theorem's own words.  The claims record is NOT changed: route (a) --
a non-zero norm-inverse column whose packed fold nevertheless vanishes at the
derived index point -- was NOT taken and is NOT claimed impossible here; I did
not find such a column and no adopted lemma gives one.

**HOW THE HASH WORKS, AND WHAT IT IS NOT.**  `Transcript.challengeAt` calls the
hash on `Transcript.challengeInput d counter = challengePrefix ++ d.bytes ++ le 8
counter`, whose last eight bytes are the counter.  `routedHash` answers by those
eight bytes ALONE: `modulus - 1` at counter three, zero at counters four and
five, and two everywhere else.  Because the answer does not depend on the digest,
NO digest chain is ever computed: `rho` is drawn at counters three, four and five
of the relation state, so `rho = -1` at EVERY configuration and EVERY statement,
with no evaluation of the absorbed transcript.  `routedHash` is an arbitrary
element of the model type `Transcript.Hash = Bytes -> Digest`.  It is NOT Keccak,
NOT a permutation, NOT collision-resistant, and NOT a claim that the deployed
hash has this property.  It is a model object exhibiting that the verifier's
acceptance set at `numRouted = 80` is non-empty.  It is not constant
(`routed_hash_is_not_constant`); that fact does NOT mean it uses the digest -- it
varies with the counter suffix only.  The derived `lambda`, `kappa` and `beta`
are all the non-zero value `twoEverywhere`
(`routed_lambda_is_two_everywhere`, `routed_kappa_is_two_everywhere`,
`routed_beta_is_two_everywhere`), so the lambda ladder, the logup summand and the
denominator coordinates all carry live challenges.  The derived `gamma` is `-1`
as a side effect of the counter layout; that is recorded, not hidden.

**WHAT GATE 7 NOW CARRIES.**  At the adopted derived instance gate 7 was
`Verifier.zero` at every observation, point and public-input-free claim record,
so it could not distinguish any two proofs.  Here the wire loop executes eighty
times (`routed_wire_loop_runs_eighty_times`), the lambda ladder performs eighty
multiplications by a non-zero derived lambda (`routed_lambda_ladder_runs`), and
each wire's helper-check contribution is exactly the difference of two
helper-times-formal-norm products
(`routed_wire_step_helper_check_at_minus_one_rho`), so both
`Norm.denominatorTerms` calls per wire -- hence `denominatorCoordinates`,
`formalAdjugate` and `formalNormFromAdjugate`, one hundred and sixty invocations
in all -- really run, against the proof's own norm-inverse entries; the logup
pair runs likewise through `recomposeFormalAdjugate`
(`routed_wire_step_logup_sum`).  **What IS established about separation:** gate 7
does NOT separate `routedProof` from `altProof`, a proof that differs only in
`normInverseRoot` (`alt_proof_is_also_accepted`).  `Verifier.shape` binds
`preprocessedRoot` to the pin and does not bind the other two roots; at this
hash those roots are free.  A rejection at a different helper column was not
constructed and is not claimed impossible.

**WHAT THIS MODULE DOES NOT ESTABLISH.**

* **IT DOES NOT DOMINATE THE ADOPTED `DerivedAcceptance.derivedConfig`, AND IT
  DOES NOT DOMINATE `NonDegenerateAcceptance.maximalConfig`; ALL THREE ARE
  PAIRWISE INCOMPARABLE.**  Against the derived instance this one is strictly
  better on `numRouted` and equal on every other configuration field, but
  strictly weaker in quantifier strength AND in Fiat--Shamir dependence: the
  derived acceptance holds at EVERY `thash` and records `constantHash` as a
  collapsing witness; this one instantiates a collapsing hash as the accepting
  one.  Against the maximal instance this one ties on six numeric fields
  including `numRouted` (`routed_config_ties_the_adopted_maximal_on_six_fields`)
  and is strictly better on the engine, but is strictly below on
  `numPublicInputs`, `numSelectors`, `numGateConstraints` and `gateRows`
  (`routed_config_is_below_the_adopted_maximal_on_four_fields`); at Section 13's
  `routedPublicConfig` seven fields tie and only the THREE fields the stand-in
  gate decoder forces remain below
  (`routed_public_config_ties_the_adopted_maximal_on_seven_fields`,
  `routed_public_config_is_below_the_adopted_maximal_on_three_fields`).  Even
  there the two are incomparable, because `maximalConfig`'s acceptance is at the
  FIXTURE engine and this one is at an instantiated transcript hash.  No
  conclusion may be drawn by combining any two of the three.
* **The WHIR parse and the WHIR tail are still NOT installed.**  They are the
  adopted fixture's, exactly as in `DerivedAcceptance`; every caveat recorded in
  that module's header about them applies here verbatim and is not restated.
* **`numPublicInputs` is lifted too, in Section 13, but at a SECOND
  configuration.**  With `numRouted = 80` the adopted
  `probe_shape_valid_forces_no_public_inputs` no longer bites, so
  `routedPublicConfig` carries `numPublicInputs = 3` -- the adopted maximal
  value -- with the full `Norm.shapeValid` predicate satisfied INCLUDING its
  public-input clause (`routed_public_targets_are_in_range`), and both
  `Verifier.verify` and `Integrated.verify` accept there.  `routedConfig` itself
  keeps `numPublicInputs = 0` so that the comparison with
  `DerivedAcceptance.derivedConfig` stays a one-field comparison.
* **Gate 2 is still non-binding.**  `routedPin` is DEFINED from `khash`, so the
  configuration-hash gate closes by `rfl`, exactly as in the adopted derived
  module.  Universal quantification over `khash` is generality of the
  acceptance, not strength of the guard.
* **Nothing is claimed about the adopted `AdaptiveAssemblyFailure` event, and no
  vacuity `IndexHalfTransport` record is lifted.**

**PROOF HYGIENE.**  Acceptance is assembled gate by gate through the adopted
constructor `NonDegenerateAcceptance.verify_of_checks`, never by one kernel
reduction.  No `set_option` of any kind is used: the shape gate is discharged
structurally through `List.length_replicate` rather than by a deep `rfl`.
-/

namespace Audit.Wire3.RoutedAcceptance

open Verifier

/-! ## 1. Two list helpers -/

theorem take_append_of_length {α : Type} :
    ∀ (xs ys : List α) (n : Nat), xs.length = n → (xs ++ ys).take n = xs
  | [], _, 0, _ => rfl
  | [], _, _ + 1, h => absurd h (by simp)
  | x :: xs, ys, 0, h => absurd h (by simp)
  | x :: xs, ys, n + 1, h => by
      have hx : xs.length = n := by simpa using h
      simpa only [List.cons_append, List.take_succ_cons, List.cons.injEq, true_and] using
        take_append_of_length xs ys n hx

/-! ## 2. The tuned transcript hash -/

def counterTag (n : Nat) : Transcript.Bytes := (Transcript.le 8 n).reverse

def zeroDigest : Transcript.Digest := ⟨List.replicate 32 (0 : Transcript.Byte), by simp⟩

def twoDigest : Transcript.Digest :=
  ⟨(2 : Transcript.Byte) :: List.replicate 31 (0 : Transcript.Byte), by simp⟩

/-- Little-endian bytes of `modulus - 1 = 0xFFFFFFFF00000000`. -/
def minusOneDigest : Transcript.Digest :=
  ⟨[(0 : Transcript.Byte), 0, 0, 0, 255, 255, 255, 255] ++
    List.replicate 24 (0 : Transcript.Byte), by simp⟩

/-- **THE TUNED HASH.**  It answers by the counter suffix of the challenge
input alone: `modulus - 1` at counter three, zero at counters four and five, and
two everywhere else. -/
def routedHash : Transcript.Hash := fun b =>
  if b.reverse.take 8 = counterTag 3 then minusOneDigest
  else if b.reverse.take 8 = counterTag 4 then zeroDigest
  else if b.reverse.take 8 = counterTag 5 then zeroDigest
  else twoDigest

theorem challenge_input_tail (d : Transcript.Digest) (k : Nat) :
    (Transcript.challengeInput d k).reverse.take 8 = counterTag k := by
  show ((Transcript.challengePrefix ++ Transcript.digestBytes d) ++
    Transcript.le 8 k).reverse.take 8 = _
  rw [List.reverse_append]
  exact take_append_of_length _ _ 8
    (by rw [List.length_reverse, Transcript.le_length])

theorem routed_hash_at_three (d : Transcript.Digest) :
    routedHash (Transcript.challengeInput d 3) = minusOneDigest := by
  show (if _ then _ else _) = _
  rw [challenge_input_tail, if_pos rfl]

theorem routed_hash_at_four (d : Transcript.Digest) :
    routedHash (Transcript.challengeInput d 4) = zeroDigest := by
  show (if _ then _ else _) = _
  rw [challenge_input_tail, if_neg (by decide), if_pos rfl]

theorem routed_hash_at_five (d : Transcript.Digest) :
    routedHash (Transcript.challengeInput d 5) = zeroDigest := by
  show (if _ then _ else _) = _
  rw [challenge_input_tail, if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem routed_challenge_at_three (d : Transcript.Digest) :
    Transcript.challengeAt routedHash d 3 = ⟨18446744069414584320, by decide⟩ := by
  apply Fin.ext
  show Transcript.fromLe (Transcript.digestBytes (routedHash
    (Transcript.challengeInput d 3))) % Transcript.modulus = _
  rw [routed_hash_at_three]
  decide

theorem routed_challenge_at_four (d : Transcript.Digest) :
    Transcript.challengeAt routedHash d 4 = ⟨0, by decide⟩ := by
  apply Fin.ext
  show Transcript.fromLe (Transcript.digestBytes (routedHash
    (Transcript.challengeInput d 4))) % Transcript.modulus = _
  rw [routed_hash_at_four]
  decide

theorem routed_challenge_at_five (d : Transcript.Digest) :
    Transcript.challengeAt routedHash d 5 = ⟨0, by decide⟩ := by
  apply Fin.ext
  show Transcript.fromLe (Transcript.digestBytes (routedHash
    (Transcript.challengeInput d 5))) % Transcript.modulus = _
  rw [routed_hash_at_five]
  decide

/-- The draw that starts at counter three is exactly `-1`, at EVERY digest. -/
theorem routed_draw_at_three (d : Transcript.Digest) :
    (OuterInitial.draw routedHash ⟨d, 3⟩).1 = Verifier.sub Verifier.zero Norm.one := by
  show Connections.fromTranscript ⟨Transcript.challengeAt routedHash d 3,
    Transcript.challengeAt routedHash d (3 + 1),
    Transcript.challengeAt routedHash d (3 + 2)⟩ = _
  rw [show (3 + 1 : Nat) = 4 from rfl, show (3 + 2 : Nat) = 5 from rfl,
    routed_challenge_at_three, routed_challenge_at_four, routed_challenge_at_five]
  apply Subtype.eq
  decide

/-- Every challenge drawn at a counter other than three, four or five is the
constant two -- so the tuned hash is NOT a constant hash and does NOT zero the
relation challenges. -/
def twoEverywhere : Verifier.Ext3 := ⟨⟨2, 2, 2⟩, by decide⟩

theorem routed_hash_off_the_tuned_counters (d : Transcript.Digest) (k : Nat)
    (h3 : counterTag k ≠ counterTag 3) (h4 : counterTag k ≠ counterTag 4)
    (h5 : counterTag k ≠ counterTag 5) :
    routedHash (Transcript.challengeInput d k) = twoDigest := by
  show (if _ then _ else _) = _
  rw [challenge_input_tail, if_neg h3, if_neg h4, if_neg h5]

theorem routed_challenge_off_the_tuned_counters (d : Transcript.Digest) (k : Nat)
    (h3 : counterTag k ≠ counterTag 3) (h4 : counterTag k ≠ counterTag 4)
    (h5 : counterTag k ≠ counterTag 5) :
    Transcript.challengeAt routedHash d k = ⟨2, by decide⟩ := by
  apply Fin.ext
  show Transcript.fromLe (Transcript.digestBytes (routedHash
    (Transcript.challengeInput d k))) % Transcript.modulus = _
  rw [routed_hash_off_the_tuned_counters d k h3 h4 h5]
  decide

theorem routed_draw_at_zero (d : Transcript.Digest) :
    (OuterInitial.draw routedHash ⟨d, 0⟩).1 = twoEverywhere := by
  show Connections.fromTranscript ⟨Transcript.challengeAt routedHash d 0,
    Transcript.challengeAt routedHash d (0 + 1),
    Transcript.challengeAt routedHash d (0 + 2)⟩ = _
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 2 : Nat) = 2 from rfl,
    routed_challenge_off_the_tuned_counters d 0 (by decide) (by decide) (by decide),
    routed_challenge_off_the_tuned_counters d 1 (by decide) (by decide) (by decide),
    routed_challenge_off_the_tuned_counters d 2 (by decide) (by decide) (by decide)]
  apply Subtype.eq
  decide

theorem routed_draw_at_six (d : Transcript.Digest) :
    (OuterInitial.draw routedHash ⟨d, 6⟩).1 = twoEverywhere := by
  show Connections.fromTranscript ⟨Transcript.challengeAt routedHash d 6,
    Transcript.challengeAt routedHash d (6 + 1),
    Transcript.challengeAt routedHash d (6 + 2)⟩ = _
  rw [show (6 + 1 : Nat) = 7 from rfl, show (6 + 2 : Nat) = 8 from rfl,
    routed_challenge_off_the_tuned_counters d 6 (by decide) (by decide) (by decide),
    routed_challenge_off_the_tuned_counters d 7 (by decide) (by decide) (by decide),
    routed_challenge_off_the_tuned_counters d 8 (by decide) (by decide) (by decide)]
  apply Subtype.eq
  decide

theorem two_everywhere_is_not_zero : twoEverywhere ≠ Verifier.zero := by decide

/-! ## 3. The derived relation challenges at the tuned hash -/

/-- **THE OBSTRUCTION FACTOR IS KILLED.**  At the tuned hash the DERIVED `rho`
is exactly `-1`, at EVERY configuration and EVERY statement -- no digest chain
is computed, because the tuned hash answers by counter alone. -/
theorem routed_rho_is_minus_one (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive routedHash c s).log.rho = Verifier.sub Verifier.zero Norm.one := by
  show (OuterInitial.draw routedHash
    (OuterInitial.draw routedHash (OuterInitial.relationState routedHash c s)).2).1 = _
  exact routed_draw_at_three _

/-- The lambda challenge is NOT zero: the per-wire ladder really runs. -/
theorem routed_lambda_is_two_everywhere (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive routedHash c s).log.lambda = twoEverywhere := by
  show (OuterInitial.draw routedHash (OuterInitial.relationState routedHash c s)).1 = _
  exact routed_draw_at_zero _

/-- The kappa challenge is NOT zero: the logup summand really reaches the
terminal. -/
theorem routed_kappa_is_two_everywhere (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive routedHash c s).log.kappa = twoEverywhere := by
  show (OuterInitial.draw routedHash (OuterInitial.draw routedHash
    (OuterInitial.draw routedHash (OuterInitial.relationState routedHash c s)).2).2).1 = _
  exact routed_draw_at_six _

/-- The beta challenge is NOT zero: the denominator coordinates really move. -/
theorem routed_beta_is_two_everywhere (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive routedHash c s).log.beta = twoEverywhere := by
  show (OuterInitial.draw routedHash (OuterInitial.denominatorState routedHash c s)).1 = _
  exact routed_draw_at_zero _

/-! ## 4. The algebra: `rho = -1` folds each wire pair -/

theorem minus_one_is_the_negated_one :
    Verifier.sub Verifier.zero Norm.one = Algebra.vneg Norm.one := by
  rw [Algebra.vsub_as_add_neg, Algebra.vzero_add]

theorem minus_one_pair_vanishes :
    Verifier.add (Verifier.sub Verifier.zero Norm.one)
      (Verifier.mul (Verifier.sub Verifier.zero Norm.one)
        (Verifier.sub Verifier.zero Norm.one)) = Verifier.zero := by
  rw [minus_one_is_the_negated_one, Algebra.vneg_mul, Algebra.vone_mul, Algebra.vneg_neg,
    Algebra.vneg_add_cancel]

/-- **WHAT `rho = -1` DOES TO A WIRE.**  The two `- 1` summands of the identity
and sigma helper checks cancel: the wire contributes exactly the DIFFERENCE of
the two helper products. -/
theorem minus_one_folds_the_wire_pair (A B : Verifier.Ext3) :
    Verifier.add (Verifier.sub A Norm.one)
      (Verifier.mul (Verifier.sub Verifier.zero Norm.one) (Verifier.sub B Norm.one)) =
      Verifier.sub A B := by
  rw [minus_one_is_the_negated_one, Algebra.vneg_mul, Algebra.vone_mul,
    Algebra.vsub_as_add_neg A Norm.one, Algebra.vsub_as_add_neg B Norm.one,
    Algebra.vneg_add, Algebra.vneg_neg, Algebra.vsub_as_add_neg A B,
    Algebra.vadd_assoc A (Algebra.vneg Norm.one),
    ← Algebra.vadd_assoc (Algebra.vneg Norm.one) (Algebra.vneg B) Norm.one,
    Algebra.vadd_comm (Algebra.vneg Norm.one) (Algebra.vneg B),
    Algebra.vadd_assoc (Algebra.vneg B) (Algebra.vneg Norm.one) Norm.one,
    Algebra.vneg_add_cancel, Algebra.vadd_zero]

/-! ## 5. The norm terminal at an all-zero helper column and `rho = -1` -/

theorem wire_step_at_zero_helpers (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (sg : Verifier.Ext3) (index : Nat) (s : Norm.WireState)
    (hz0 : t.normInverse.getD index Verifier.zero = Verifier.zero)
    (hz1 : t.normInverse.getD (c.numRouted + index) Verifier.zero = Verifier.zero)
    (hrho : ch.rho = Verifier.sub Verifier.zero Norm.one) :
    (Norm.wireStep c ch t sg index s).helperChecks = s.helperChecks ∧
      (Norm.wireStep c ch t sg index s).logupSum = s.logupSum := by
  constructor
  · simp only [Norm.wireStep, hz0, hz1, hrho, Algebra.vzero_mul, minus_one_pair_vanishes,
      Algebra.vmul_zero, Algebra.vadd_zero]
  · simp only [Norm.wireStep, hz0, hz1, Algebra.vzero_mul, Algebra.vsub_self,
      Algebra.vadd_zero]

theorem run_wires_at_zero_helpers (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (sg : Verifier.Ext3)
    (hz : ∀ j, t.normInverse.getD j Verifier.zero = Verifier.zero)
    (hrho : ch.rho = Verifier.sub Verifier.zero Norm.one) :
    ∀ (count index : Nat) (s : Norm.WireState),
      (Norm.runWires c ch t sg index count s).helperChecks = s.helperChecks ∧
        (Norm.runWires c ch t sg index count s).logupSum = s.logupSum := by
  intro count
  induction count with
  | zero =>
      intro index s
      rw [DerivedAcceptance.run_wires_at_zero_count]
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro index s
      have hstep := wire_step_at_zero_helpers c ch t sg index s (hz index) (hz _) hrho
      have h := ih (index + 1) (Norm.wireStep c ch t sg index s)
      refine ⟨?_, ?_⟩
      · simp only [Norm.runWires, h.1, hstep.1]
      · simp only [Norm.runWires, h.2, hstep.2]

/-- **THE PERMUTATION TERMINAL VANISHES WITH ROUTED WIRES PRESENT.**  No
hypothesis on `c.numRouted`: the wire loop runs its full length and every wire
contributes zero because `rho = -1` cancels the two `- 1` summands. -/
theorem permutation_terminal_vanishes_at_minus_one_rho (c : Verifier.Config)
    (ch : Norm.Challenges) (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3)
    (hz : ∀ j, t.normInverse.getD j Verifier.zero = Verifier.zero)
    (hrho : ch.rho = Verifier.sub Verifier.zero Norm.one) :
    Norm.permutationTerminal c ch t point = Verifier.zero := by
  have h := run_wires_at_zero_helpers c ch t
    (Norm.subgroupEvaluation c.subgroupPowers point) hz hrho c.numRouted 0 Norm.wireStart
  simp only [Norm.permutationTerminal, h.1, h.2]
  show Verifier.add (Verifier.mul _ Verifier.zero) (Verifier.mul _ Verifier.zero) = _
  rw [Algebra.vmul_zero, Algebra.vmul_zero, Algebra.vadd_zero]

theorem norm_terminal_vanishes_at_minus_one_rho (c : Verifier.Config) (i : Verifier.Initial)
    (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3)
    (hz : ∀ j, t.normInverse.getD j Verifier.zero = Verifier.zero)
    (hpi : t.publicInputs = [])
    (hrho : (Norm.challengesFromInitial i).rho = Verifier.sub Verifier.zero Norm.one) :
    Norm.normEvaluation c i t point = Verifier.zero := by
  simp only [Norm.normEvaluation, Norm.evaluate,
    permutation_terminal_vanishes_at_minus_one_rho c _ t point hz hrho,
    Norm.public_input_empty_is_zero c t point _ hpi, Algebra.vmul_zero, Algebra.vadd_zero]

/-! ## 6. The configuration, the proof and the pin -/

/-- **THE CONFIGURATION.**  It is the adopted `DerivedAcceptance.derivedConfig`
with `numRouted` moved from `0` to `80` -- the ceiling `Verifier.envelope`
permits and the value the adopted `NonDegenerateAcceptance.maximalConfig`
carries -- and `kIs` lengthened to match.  Every other field is unchanged. -/
def routedConfig : Verifier.Config :=
  { Verifier.testConfig with
      degreeBits := 13, numConstants := 80, numRouted := 80, numWires := 160,
      numPublicInputs := 0, numSelectors := 2, numGateConstraints := 1,
      quotientDegree := 8, gateRows := 2, indexBits := 8,
      kIs := List.replicate 80 (Verifier.base 1),
      subgroupPowers := List.replicate 13 (Verifier.base 1),
      publicInputWireMap := [] }

/-- The proof record: the adopted `IndexHalfTransport.matchingClaims` at this
configuration, with the shape-pinned round lists.  Its five claim columns are
all of length `160` now, the norm-inverse column included. -/
def routedProof : Verifier.Proof :=
  { Verifier.testProof with
      constituentWidth := 160,
      publicInputs := [],
      logRounds := List.replicate 13 (List.replicate 5 Verifier.zero),
      gateRounds := List.replicate 13 (List.replicate 10 Verifier.zero),
      used := IndexHalfTransport.matchingClaims routedConfig }

/-- The pinned deployment record: the concrete configuration digest of
`routedConfig` under an arbitrary `khash`. -/
def routedPin (khash : Verifier.Bytes → Verifier.Root) : Verifier.Pinned :=
  ⟨1, ExplicitEngine.concreteConfigurationHash khash routedConfig, Verifier.testRoot⟩

/-- The engine is LITERALLY the adopted `DerivedAcceptance.derivedEngine`, taken
at the tuned outer transcript hash. -/
theorem routed_engine_installed_fields (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine routedHash khash P).normEvaluation = Norm.normEvaluation ∧
      (DerivedAcceptance.derivedEngine routedHash khash P).foldClaim = Connections.packedFold ∧
      (DerivedAcceptance.derivedEngine routedHash khash P).eqEvaluation = Norm.eqEvaluation ∧
      (DerivedAcceptance.derivedEngine routedHash khash P).initialObservation =
        InstalledInitialTranscript.concreteInitialObservation routedHash ∧
      (DerivedAcceptance.derivedEngine routedHash khash P).commitRound =
        InstalledRoundCommit.concreteCommitRound routedHash ∧
      (DerivedAcceptance.derivedEngine routedHash khash P).sampleIndices =
        InstalledIndexSampler.concreteSampleIndices routedHash :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 7. The numeric gates -/

theorem routed_config_envelope : Verifier.envelope routedConfig = true := by decide

theorem routed_round_rows_have_the_pinned_width (n w : Nat) :
    ((List.replicate n (List.replicate w Verifier.zero)).all
      (fun r => decide (r.length = w))) = true := by
  rw [List.all_eq_true]
  intro r hr
  rw [List.eq_of_mem_replicate hr, decide_eq_true_eq]
  exact List.length_replicate _ _

theorem routed_shape_holds (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.shape (routedPin khash) routedConfig routedProof = true := by
  simp only [Verifier.shape, decide_eq_true_eq]
  exact ⟨rfl, by decide, rfl, rfl, rfl, by decide, by decide,
    List.length_replicate _ _, List.length_replicate _ _, List.length_replicate _ _,
    List.length_replicate _ _, List.length_replicate _ _, List.length_replicate _ _,
    List.length_replicate _ _, routed_round_rows_have_the_pinned_width 13 5,
    routed_round_rows_have_the_pinned_width 13 10⟩

theorem routed_config_is_nondegenerate :
    1 < routedConfig.numWires ∧ 0 < routedConfig.numRouted ∧
      1 < routedConfig.numConstants ∧ 1 < routedConfig.degreeBits ∧
      0 < routedConfig.indexBits := by decide

/-- The routed-wire count sits at the ceiling `Verifier.envelope` permits. -/
theorem envelope_caps_the_routed_count (c : Verifier.Config)
    (h : Verifier.envelope c = true) : c.numRouted ≤ 80 := by
  simp only [Verifier.envelope, decide_eq_true_eq] at h
  exact h.2.2.2.2.1

theorem routed_config_sits_at_the_routed_ceiling : routedConfig.numRouted = 80 := rfl

/-! ## 8. The two claims and the three remaining gates -/

theorem routed_claims_vanish (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig routedProof).logClaim = Verifier.zero ∧
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig routedProof).gateClaim = Verifier.zero := by
  refine DerivedAcceptance.run_rounds_keeps_zero_claims _ _ _ ?_ rfl rfl
  intro m hm
  obtain ⟨hl, hg⟩ := List.of_mem_zip hm
  exact ⟨⟨5, List.eq_of_mem_replicate hl⟩, ⟨10, List.eq_of_mem_replicate hg⟩⟩

/-- **GATE 7.**  The installed `Norm.normEvaluation` at `numRouted = 80`, with
the wire loop running eighty times, matches the zero log claim -- because the
DERIVED `rho` is `-1`. -/
theorem routed_log_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine routedHash khash P).logTerminal routedConfig
        ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
          routedConfig routedProof) routedProof
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
          routedConfig routedProof).logPoint =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig routedProof).logClaim := by
  rw [(routed_claims_vanish khash P).1]
  refine norm_terminal_vanishes_at_minus_one_rho routedConfig _
    (Verifier.normTerminalInput routedProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j) rfl ?_
  show (Norm.challengesFromInitial (OuterInitial.toInitial
    (OuterInitial.derive routedHash routedConfig (Verifier.statement routedProof)))).rho = _
  rw [OuterInitial.initial_norm_adapter_is_lossless]
  exact routed_rho_is_minus_one _ _

theorem routed_expected_claims_are_zero (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine routedHash khash P)
      routedConfig routedProof).expectedClaims =
      [some Verifier.zero, some Verifier.zero, some Verifier.zero, some Verifier.zero,
        some Verifier.zero, none] := by
  show Verifier.expectedClaims Connections.packedFold routedConfig routedProof
    (Verifier.derivedIndices (DerivedAcceptance.derivedEngine routedHash khash P)
      routedConfig routedProof) = _
  simp only [Verifier.expectedClaims, List.cons.injEq, Option.some.injEq, and_true]
  exact ⟨DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _⟩

/-- **GATE 8.** -/
theorem routed_whir_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.verifyWhir (DerivedAcceptance.derivedEngine routedHash khash P)
      (Verifier.derivedContext (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig routedProof) routedProof = true := by
  simp only [Verifier.verifyWhir, Verifier.rootsAndClaimsMatch]
  rw [routed_expected_claims_are_zero khash P]
  rfl

theorem routed_gate_claim_columns_are_zero :
    routedProof.used.gateWitness = List.replicate 160 Verifier.zero ∧
      routedProof.used.gatePreprocessed.take routedConfig.numConstants =
        List.replicate 80 Verifier.zero := ⟨rfl, rfl⟩

/-- The gate machinery reads only fields `routedConfig` shares verbatim with the
adopted `DerivedAcceptance.derivedConfig`, so the adopted dispatcher run
transfers unchanged. -/
theorem routed_gate_evaluation_vanishes (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    Integrated.evaluateGate DerivedAcceptance.derivedDecoder routedConfig
        (List.replicate 160 Verifier.zero) (List.replicate 80 Verifier.zero) publicHash alpha =
      some Verifier.zero :=
  DerivedAcceptance.derived_gate_evaluation_vanishes publicHash hp alpha

theorem routed_gate_evaluation_at_the_proof (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    (DerivedAcceptance.derivedEngine routedHash khash P).gateEvaluation routedConfig
        routedProof.used.gateWitness
        (routedProof.used.gatePreprocessed.take routedConfig.numConstants) publicHash alpha =
      Verifier.zero := by
  rw [DerivedAcceptance.derived_gate_evaluation_field]
  simp only []
  rw [routed_gate_claim_columns_are_zero.1, routed_gate_claim_columns_are_zero.2,
    routed_gate_evaluation_vanishes publicHash hp]
  rfl

/-- **GATE 9.** -/
theorem routed_gate_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.gateTerminal (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig routedProof =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig routedProof).gateClaim := by
  rw [(routed_claims_vanish khash P).2, DerivedAcceptance.gate_terminal_unfolds,
    DerivedAcceptance.derived_public_input_hash_field,
    routed_gate_evaluation_at_the_proof khash P _
      (PublicInputHashBinding.hash_no_pad_length routedProof.publicInputs)]
  exact Algebra.vmul_zero _

/-! ## 9. Acceptance -/

/-- **THE ACCEPTANCE, AT EIGHTY ROUTED WIRES.**  The adopted `Verifier.verify`,
at the adopted `DerivedAcceptance.derivedEngine` taken at the tuned outer
transcript hash, for EVERY configuration hash `khash`. -/
theorem routed_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P routedConfig = true) :
    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash P) (routedPin khash) 1
      routedConfig routedProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl routed_config_envelope ?_
    (routed_shape_holds khash)
    (DerivedAcceptance.derived_tau_lengths routedHash khash P routedConfig routedProof).1
    (DerivedAcceptance.derived_tau_lengths routedHash khash P routedConfig routedProof).2
    (DerivedAcceptance.derived_index_lengths routedHash khash P routedConfig routedProof
      (by decide)).1
    (DerivedAcceptance.derived_index_lengths routedHash khash P routedConfig routedProof
      (by decide)).2
    (routed_log_terminal_gate khash P) (routed_whir_gate khash P)
    (routed_gate_terminal_gate khash P)
  show ExplicitEngine.explicitDeployment P DerivedAcceptance.derivedConfig routedConfig = true
  have hw : routedConfig.whirEncoding = DerivedAcceptance.derivedConfig.whirEncoding := rfl
  simp [ExplicitEngine.explicitDeployment, hw, hprofile]

theorem routed_profile_passes_the_canonical_check :
    PinnedWhirProfile.profileOk DerivedAcceptance.derivedProfile routedConfig = true := by rfl

/-- **THE CLOSED ACCEPTANCE.**  No hypothesis at all, for EVERY configuration
hash. -/
theorem routed_acceptance_at_the_profile_witness (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash
        DerivedAcceptance.derivedProfile) (routedPin khash) 1 routedConfig routedProof = .ok () :=
  routed_acceptance khash DerivedAcceptance.derivedProfile
    routed_profile_passes_the_canonical_check

/-- The same instance again at the adopted SHARP profile, whose parameter
decoder rejects every nonempty WHIR encoding and whose digests are non-constant. -/
theorem routed_sharp_profile_passes :
    PinnedWhirProfile.profileOk DerivedAcceptance.probeSharpProfile routedConfig = true := by rfl

theorem routed_acceptance_at_the_sharp_profile (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash
        DerivedAcceptance.probeSharpProfile) (routedPin khash) 1 routedConfig routedProof =
      .ok () :=
  routed_acceptance khash DerivedAcceptance.probeSharpProfile routed_sharp_profile_passes

/-! ## 10. The same instance through the adopted `Integrated.verify` -/

theorem routed_engine_is_its_own_model_engine (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.modelEngine (DerivedAcceptance.derivedEngine routedHash khash P)
      DerivedAcceptance.derivedDecoder = DerivedAcceptance.derivedEngine routedHash khash P := rfl

theorem routed_log_point_length (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P) routedConfig
      routedProof).logPoint.length = 13 := by
  have h := (Verifier.runRounds_lengths (InstalledRoundCommit.concreteCommitRound routedHash)
    (Verifier.start ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
      routedConfig routedProof))
    (routedProof.logRounds.zip routedProof.gateRounds)).2.1
  have hz : (routedProof.logRounds.zip routedProof.gateRounds).length = 13 := rfl
  rw [hz] at h
  exact h

/-- The FULL norm shape predicate of the checked adapter holds -- including the
`c.kIs.length = c.numRouted` conjunct at eighty, which no longer holds
vacuously. -/
theorem routed_norm_shape_valid (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Norm.shapeValid routedConfig
        (Norm.challengesFromInitial
          ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
            routedConfig routedProof))
        (Verifier.normTerminalInput routedProof)
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
          routedConfig routedProof).logPoint = true := by
  have hpt := routed_log_point_length khash P
  have htau := (DerivedAcceptance.derived_tau_lengths routedHash khash P
    routedConfig routedProof).1
  simp only [Norm.shapeValid, decide_eq_true_eq]
  refine ⟨hpt, ?_, ?_, List.length_replicate _ _, by decide, List.length_replicate _ _,
    List.length_replicate _ _, List.length_replicate _ _, rfl, rfl, ?_⟩
  · show ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
      routedConfig routedProof).logTau.length = _
    rw [htau, hpt]
    rfl
  · show (List.replicate 13 (Verifier.base 1)).length = _
    rw [List.length_replicate, hpt]
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)

theorem routed_integrated_norm_result (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.normResult (DerivedAcceptance.derivedEngine routedHash khash P) routedConfig
      routedProof = some Verifier.zero := by
  have hchal : ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
      routedConfig routedProof).logChallenges.length = 7 :=
    (OuterInitial.derived_initial_shape routedHash routedConfig
      (Verifier.statement routedProof)).1
  simp only [Integrated.normResult, Norm.checkedNormEvaluation, Norm.checkedEvaluate,
    hchal, if_pos, routed_norm_shape_valid, ite_true]
  show some (Norm.normEvaluation routedConfig _ _ _) = _
  refine congrArg some ?_
  refine norm_terminal_vanishes_at_minus_one_rho routedConfig _
    (Verifier.normTerminalInput routedProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j) rfl ?_
  show (Norm.challengesFromInitial (OuterInitial.toInitial
    (OuterInitial.derive routedHash routedConfig (Verifier.statement routedProof)))).rho = _
  rw [OuterInitial.initial_norm_adapter_is_lossless]
  exact routed_rho_is_minus_one _ _

theorem routed_integrated_gate_result (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.gateResult (DerivedAcceptance.derivedEngine routedHash khash P)
      DerivedAcceptance.derivedDecoder routedConfig routedProof = some Verifier.zero := by
  show Integrated.evaluateGate DerivedAcceptance.derivedDecoder routedConfig
    routedProof.used.gateWitness
    (routedProof.used.gatePreprocessed.take routedConfig.numConstants)
    ((DerivedAcceptance.derivedEngine routedHash khash P).publicInputsHash
      routedProof.publicInputs) _ = _
  rw [DerivedAcceptance.derived_public_input_hash_field,
    routed_gate_claim_columns_are_zero.1, routed_gate_claim_columns_are_zero.2,
    routed_gate_evaluation_vanishes _
      (PublicInputHashBinding.hash_no_pad_length routedProof.publicInputs)]

/-- **THE INTEGRATED ACCEPTANCE, AT EIGHTY ROUTED WIRES.** -/
theorem routed_integrated_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P routedConfig = true) :
    Integrated.verify (DerivedAcceptance.derivedEngine routedHash khash P)
      DerivedAcceptance.derivedDecoder (routedPin khash) 1 routedConfig routedProof = .ok () := by
  simp only [Integrated.verify, routed_engine_is_its_own_model_engine,
    routed_integrated_norm_result, routed_integrated_gate_result]
  exact routed_acceptance khash P hprofile

theorem routed_integrated_acceptance_at_the_profile_witness
    (khash : Verifier.Bytes → Verifier.Root) :
    Integrated.verify (DerivedAcceptance.derivedEngine routedHash khash
        DerivedAcceptance.derivedProfile) DerivedAcceptance.derivedDecoder (routedPin khash) 1
      routedConfig routedProof = .ok () :=
  routed_integrated_acceptance khash DerivedAcceptance.derivedProfile
    routed_profile_passes_the_canonical_check

/-! ## 11. What gate 7 now carries -/

/-- **THE WIRE LOOP EXECUTES.**  Eighty iterations, not zero. -/
theorem routed_wire_loop_runs_eighty_times (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (sg : Verifier.Ext3) :
    (Norm.runWires routedConfig ch t sg 0 routedConfig.numRouted Norm.wireStart).processed = 80 := by
  rw [Norm.run_wires_exact_count]
  rfl

/-- **THE LAMBDA LADDER EXECUTES.**  Eighty multiplications by the derived
lambda, which at the tuned hash is NOT zero. -/
theorem routed_lambda_ladder_runs (ch : Norm.Challenges) (t : Verifier.NormTerminalInput)
    (sg : Verifier.Ext3) :
    (Norm.runWires routedConfig ch t sg 0 routedConfig.numRouted Norm.wireStart).lambdaPower =
      Norm.multiplyRepeated Norm.one ch.lambda 80 := by
  rw [Norm.run_wires_lambda_power]
  rfl

/-- **WHAT EACH WIRE CONTRIBUTES TO THE HELPER CHECK AT `rho = -1`.**  Exactly
the difference of the two helper-times-formal-norm products: both calls to
`Norm.denominatorTerms` -- hence `denominatorCoordinates`, `formalAdjugate`,
`formalNormFromAdjugate` -- really run, and the proof's norm-inverse entries
really appear. -/
theorem routed_wire_step_helper_check_at_minus_one_rho (c : Verifier.Config)
    (ch : Norm.Challenges) (t : Verifier.NormTerminalInput) (sg : Verifier.Ext3)
    (index : Nat) (s : Norm.WireState)
    (hrho : ch.rho = Verifier.sub Verifier.zero Norm.one) :
    (Norm.wireStep c ch t sg index s).helperChecks =
      Verifier.add s.helperChecks
        (Verifier.mul s.lambdaPower
          (Verifier.sub
            (Verifier.mul (t.normInverse.getD index Verifier.zero)
              (Norm.denominatorTerms (t.witness.getD index Verifier.zero)
                (Verifier.scalar sg (c.kIs.getD index (Verifier.base 0)).val)
                ch.beta ch.gamma).1)
            (Verifier.mul (t.normInverse.getD (c.numRouted + index) Verifier.zero)
              (Norm.denominatorTerms (t.witness.getD index Verifier.zero)
                (t.preprocessed.getD (c.numConstants + index) Verifier.zero)
                ch.beta ch.gamma).1))) := by
  simp only [Norm.wireStep, hrho]
  rw [minus_one_folds_the_wire_pair]

/-- The logup summand of each wire, for the record: the two
`recomposeFormalAdjugate` limbs, again against the proof's helper entries. -/
theorem routed_wire_step_logup_sum (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (sg : Verifier.Ext3) (index : Nat) (s : Norm.WireState) :
    (Norm.wireStep c ch t sg index s).logupSum =
      Verifier.add s.logupSum
        (Verifier.sub
          (Verifier.mul (t.normInverse.getD index Verifier.zero)
            (Norm.denominatorTerms (t.witness.getD index Verifier.zero)
              (Verifier.scalar sg (c.kIs.getD index (Verifier.base 0)).val)
              ch.beta ch.gamma).2)
          (Verifier.mul (t.normInverse.getD (c.numRouted + index) Verifier.zero)
            (Norm.denominatorTerms (t.witness.getD index Verifier.zero)
              (t.preprocessed.getD (c.numConstants + index) Verifier.zero)
              ch.beta ch.gamma).2)) := rfl

/-- The tuned hash is NOT a constant hash. -/
theorem routed_hash_is_not_constant :
    (routedHash (Transcript.challengeInput zeroDigest 3)).bytes ≠
      (routedHash (Transcript.challengeInput zeroDigest 0)).bytes := by
  rw [routed_hash_at_three,
    routed_hash_off_the_tuned_counters zeroDigest 0 (by decide) (by decide) (by decide)]
  decide

/-! ## 12. Relation to the two adopted accepting instances -/

/-- Against the adopted `DerivedAcceptance.derivedConfig`: the routed-wire count
strictly increases and NOTHING else moves. -/
theorem routed_config_strictly_exceeds_the_derived_config_on_the_routed_wires :
    DerivedAcceptance.derivedConfig.numRouted < routedConfig.numRouted := by decide

theorem routed_config_agrees_with_the_derived_config_off_the_routed_wires :
    routedConfig.degreeBits = DerivedAcceptance.derivedConfig.degreeBits ∧
      routedConfig.numConstants = DerivedAcceptance.derivedConfig.numConstants ∧
      routedConfig.numWires = DerivedAcceptance.derivedConfig.numWires ∧
      routedConfig.numPublicInputs = DerivedAcceptance.derivedConfig.numPublicInputs ∧
      routedConfig.numSelectors = DerivedAcceptance.derivedConfig.numSelectors ∧
      routedConfig.numGateConstraints = DerivedAcceptance.derivedConfig.numGateConstraints ∧
      routedConfig.quotientDegree = DerivedAcceptance.derivedConfig.quotientDegree ∧
      routedConfig.gateRows = DerivedAcceptance.derivedConfig.gateRows ∧
      routedConfig.indexBits = DerivedAcceptance.derivedConfig.indexBits := by decide

/-- Against the adopted `NonDegenerateAcceptance.maximalConfig`: six numeric
fields now TIE, the routed-wire count among them. -/
theorem routed_config_ties_the_adopted_maximal_on_six_fields :
    routedConfig.numRouted = NonDegenerateAcceptance.maximalConfig.numRouted ∧
      routedConfig.numWires = NonDegenerateAcceptance.maximalConfig.numWires ∧
      routedConfig.numConstants = NonDegenerateAcceptance.maximalConfig.numConstants ∧
      routedConfig.degreeBits = NonDegenerateAcceptance.maximalConfig.degreeBits ∧
      routedConfig.indexBits = NonDegenerateAcceptance.maximalConfig.indexBits ∧
      routedConfig.quotientDegree = NonDegenerateAcceptance.maximalConfig.quotientDegree := by
  decide

/-- Four numeric fields still sit STRICTLY BELOW the adopted maximal instance --
three of them forced by the stand-in gate decoder, the fourth (`numPublicInputs`)
not forced by anything here.  So the two results remain INCOMPARABLE and neither
subsumes the other. -/
theorem routed_config_is_below_the_adopted_maximal_on_four_fields :
    routedConfig.numPublicInputs < NonDegenerateAcceptance.maximalConfig.numPublicInputs ∧
      routedConfig.numSelectors < NonDegenerateAcceptance.maximalConfig.numSelectors ∧
      routedConfig.numGateConstraints <
        NonDegenerateAcceptance.maximalConfig.numGateConstraints ∧
      routedConfig.gateRows < NonDegenerateAcceptance.maximalConfig.gateRows := by decide

/-- **THE ADOPTED OBSTRUCTION'S CONCLUSION IS REALISED AT THIS HASH.**  The
adopted `DerivedAcceptance.probe_acceptance_at_one_routed_wire_forces_a_challenge_coincidence`
shows that acceptance at a routed wire with an all-zero norm-inverse column is
EQUIVALENT to this coincidence among the derived challenges.  The tuned hash
makes it hold, at EVERY configuration, EVERY proof and EVERY configuration hash
-- by the second factor, not the first.  This is the exact sense in which the
present module takes route (b) of the obstruction and not route (a). -/
theorem routed_hash_realises_the_adopted_challenge_coincidence
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.mul
        (Norm.eqEvaluation
          (Norm.challengesFromInitial
            ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript c p)).tau
          (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
            c p).logPoint)
        (Verifier.add (Verifier.sub Verifier.zero Norm.one)
          (Verifier.mul
            (Norm.challengesFromInitial
              ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript c p)).rho
            (Verifier.sub Verifier.zero Norm.one))) = Verifier.zero := by
  have hrho : (Norm.challengesFromInitial
      ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript c p)).rho =
      Verifier.sub Verifier.zero Norm.one := by
    show (Norm.challengesFromInitial (OuterInitial.toInitial
      (OuterInitial.derive routedHash c (Verifier.statement p)))).rho = _
    rw [OuterInitial.initial_norm_adapter_is_lossless]
    exact routed_rho_is_minus_one _ _
  rw [hrho, minus_one_pair_vanishes, Algebra.vmul_zero]

theorem routed_config_sits_at_the_envelope_ceiling :
    routedConfig.degreeBits = 13 ∧ Verifier.width routedConfig = 160 ∧
      routedConfig.indexBits = 8 ∧ routedConfig.numConstants = 80 ∧
      routedConfig.numRouted = 80 ∧ routedConfig.quotientDegree = 8 := by decide

/-! ## 13. The same instance at three public inputs

With `numRouted = 80` the adopted `probe_shape_valid_forces_no_public_inputs`
no longer bites: public-input target columns below eighty exist, so
`Norm.shapeValid` is satisfiable at a positive public-input count and the
INTEGRATED entry point survives it.  This section carries the whole instance to
`numPublicInputs = 3`, the adopted `NonDegenerateAcceptance.maximalConfig`'s
value. -/

theorem getD_replicate_byte (n i : Nat) :
    (List.replicate n (0 : UInt8)).getD i 0 = 0 := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem target_at_zero_map (n i : Nat) :
    Norm.targetAt (List.replicate n (0 : UInt8)) i = ⟨0, 0⟩ := by
  simp only [Norm.targetAt, getD_replicate_byte]
  rfl

theorem norm_terminal_vanishes_at_minus_one_rho_and_zero_binding (c : Verifier.Config)
    (i : Verifier.Initial) (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3)
    (hz : ∀ j, t.normInverse.getD j Verifier.zero = Verifier.zero)
    (hpi : Norm.publicInputBinding c t point (Norm.challengesFromInitial i).eta =
      Verifier.zero)
    (hrho : (Norm.challengesFromInitial i).rho = Verifier.sub Verifier.zero Norm.one) :
    Norm.normEvaluation c i t point = Verifier.zero := by
  simp only [Norm.normEvaluation, Norm.evaluate,
    permutation_terminal_vanishes_at_minus_one_rho c _ t point hz hrho, hpi,
    Algebra.vmul_zero, Algebra.vadd_zero]

def routedPublicConfig : Verifier.Config :=
  { routedConfig with numPublicInputs := 3, publicInputWireMap := List.replicate 9 (0 : UInt8) }

def routedPublicProof : Verifier.Proof :=
  { routedProof with
      publicInputs := List.replicate 3 (Verifier.base 0),
      used := IndexHalfTransport.matchingClaims routedPublicConfig }

def routedPublicPin (khash : Verifier.Bytes → Verifier.Root) : Verifier.Pinned :=
  ⟨1, ExplicitEngine.concreteConfigurationHash khash routedPublicConfig, Verifier.testRoot⟩

theorem routed_public_config_envelope : Verifier.envelope routedPublicConfig = true := by decide

theorem routed_public_shape_holds (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.shape (routedPublicPin khash) routedPublicConfig routedPublicProof = true := by
  simp only [Verifier.shape, decide_eq_true_eq]
  exact ⟨rfl, by decide, rfl, List.length_replicate _ _, rfl, by decide, by decide,
    List.length_replicate _ _, List.length_replicate _ _, List.length_replicate _ _,
    List.length_replicate _ _, List.length_replicate _ _, List.length_replicate _ _,
    List.length_replicate _ _, routed_round_rows_have_the_pinned_width 13 5,
    routed_round_rows_have_the_pinned_width 13 10⟩

theorem routed_public_claims_vanish (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedPublicConfig routedPublicProof).logClaim = Verifier.zero ∧
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedPublicConfig routedPublicProof).gateClaim = Verifier.zero := by
  refine DerivedAcceptance.run_rounds_keeps_zero_claims _ _ _ ?_ rfl rfl
  intro m hm
  obtain ⟨hl, hg⟩ := List.of_mem_zip hm
  exact ⟨⟨5, List.eq_of_mem_replicate hl⟩, ⟨10, List.eq_of_mem_replicate hg⟩⟩

theorem routed_public_rho_is_minus_one (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (c : Verifier.Config) (p : Verifier.Proof) :
    (Norm.challengesFromInitial
      ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript c p)).rho =
      Verifier.sub Verifier.zero Norm.one := by
  show (Norm.challengesFromInitial (OuterInitial.toInitial
    (OuterInitial.derive routedHash c (Verifier.statement p)))).rho = _
  rw [OuterInitial.initial_norm_adapter_is_lossless]
  exact routed_rho_is_minus_one _ _

theorem routed_public_binding_vanishes (point : List Verifier.Ext3) (eta : Verifier.Ext3) :
    Norm.publicInputBinding routedPublicConfig
      (Verifier.normTerminalInput routedPublicProof) point eta = Verifier.zero :=
  DerivedAcceptance.probe_public_input_binding_vanishes_at_zero_values routedPublicConfig
    (Verifier.normTerminalInput routedPublicProof) point eta 160 3 rfl rfl

theorem routed_public_log_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine routedHash khash P).logTerminal routedPublicConfig
        ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
          routedPublicConfig routedPublicProof) routedPublicProof
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
          routedPublicConfig routedPublicProof).logPoint =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedPublicConfig routedPublicProof).logClaim := by
  rw [(routed_public_claims_vanish khash P).1]
  exact norm_terminal_vanishes_at_minus_one_rho_and_zero_binding routedPublicConfig _
    (Verifier.normTerminalInput routedPublicProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j)
    (routed_public_binding_vanishes _ _)
    (routed_public_rho_is_minus_one khash P routedPublicConfig routedPublicProof)

theorem routed_public_expected_claims_are_zero (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine routedHash khash P)
      routedPublicConfig routedPublicProof).expectedClaims =
      [some Verifier.zero, some Verifier.zero, some Verifier.zero, some Verifier.zero,
        some Verifier.zero, none] := by
  show Verifier.expectedClaims Connections.packedFold routedPublicConfig routedPublicProof
    (Verifier.derivedIndices (DerivedAcceptance.derivedEngine routedHash khash P)
      routedPublicConfig routedPublicProof) = _
  simp only [Verifier.expectedClaims, List.cons.injEq, Option.some.injEq, and_true]
  exact ⟨DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _⟩

theorem routed_public_whir_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.verifyWhir (DerivedAcceptance.derivedEngine routedHash khash P)
      (Verifier.derivedContext (DerivedAcceptance.derivedEngine routedHash khash P)
        routedPublicConfig routedPublicProof) routedPublicProof = true := by
  simp only [Verifier.verifyWhir, Verifier.rootsAndClaimsMatch]
  rw [routed_public_expected_claims_are_zero khash P]
  rfl

theorem routed_public_gate_claim_columns_are_zero :
    routedPublicProof.used.gateWitness = List.replicate 160 Verifier.zero ∧
      routedPublicProof.used.gatePreprocessed.take routedPublicConfig.numConstants =
        List.replicate 80 Verifier.zero := ⟨rfl, rfl⟩

theorem routed_public_gate_evaluation_vanishes (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    Integrated.evaluateGate DerivedAcceptance.derivedDecoder routedPublicConfig
        (List.replicate 160 Verifier.zero) (List.replicate 80 Verifier.zero) publicHash alpha =
      some Verifier.zero :=
  DerivedAcceptance.derived_gate_evaluation_vanishes publicHash hp alpha

theorem routed_public_gate_evaluation_at_the_proof (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    (DerivedAcceptance.derivedEngine routedHash khash P).gateEvaluation routedPublicConfig
        routedPublicProof.used.gateWitness
        (routedPublicProof.used.gatePreprocessed.take routedPublicConfig.numConstants)
        publicHash alpha = Verifier.zero := by
  rw [DerivedAcceptance.derived_gate_evaluation_field]
  simp only []
  rw [routed_public_gate_claim_columns_are_zero.1, routed_public_gate_claim_columns_are_zero.2,
    routed_public_gate_evaluation_vanishes publicHash hp]
  rfl

theorem routed_public_gate_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.gateTerminal (DerivedAcceptance.derivedEngine routedHash khash P)
        routedPublicConfig routedPublicProof =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedPublicConfig routedPublicProof).gateClaim := by
  rw [(routed_public_claims_vanish khash P).2, DerivedAcceptance.gate_terminal_unfolds,
    DerivedAcceptance.derived_public_input_hash_field,
    routed_public_gate_evaluation_at_the_proof khash P _
      (PublicInputHashBinding.hash_no_pad_length routedPublicProof.publicInputs)]
  exact Algebra.vmul_zero _

/-- **THE ACCEPTANCE AT EIGHTY ROUTED WIRES AND THREE PUBLIC INPUTS.** -/
theorem routed_public_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P routedPublicConfig = true) :
    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash P)
      (routedPublicPin khash) 1 routedPublicConfig routedPublicProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl
    routed_public_config_envelope ?_ (routed_public_shape_holds khash)
    (DerivedAcceptance.derived_tau_lengths routedHash khash P routedPublicConfig
      routedPublicProof).1
    (DerivedAcceptance.derived_tau_lengths routedHash khash P routedPublicConfig
      routedPublicProof).2
    (DerivedAcceptance.derived_index_lengths routedHash khash P routedPublicConfig
      routedPublicProof (by decide)).1
    (DerivedAcceptance.derived_index_lengths routedHash khash P routedPublicConfig
      routedPublicProof (by decide)).2
    (routed_public_log_terminal_gate khash P) (routed_public_whir_gate khash P)
    (routed_public_gate_terminal_gate khash P)
  show ExplicitEngine.explicitDeployment P DerivedAcceptance.derivedConfig
    routedPublicConfig = true
  have hw : routedPublicConfig.whirEncoding = DerivedAcceptance.derivedConfig.whirEncoding := rfl
  simp [ExplicitEngine.explicitDeployment, hw, hprofile]

theorem routed_public_profile_passes_the_canonical_check :
    PinnedWhirProfile.profileOk DerivedAcceptance.derivedProfile routedPublicConfig = true := by
  rfl

theorem routed_public_acceptance_at_the_profile_witness
    (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash
        DerivedAcceptance.derivedProfile) (routedPublicPin khash) 1 routedPublicConfig
      routedPublicProof = .ok () :=
  routed_public_acceptance khash DerivedAcceptance.derivedProfile
    routed_public_profile_passes_the_canonical_check

/-! ### 13a. The integrated entry point at three public inputs -/

theorem routed_public_log_point_length (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
      routedPublicConfig routedPublicProof).logPoint.length = 13 := by
  have h := (Verifier.runRounds_lengths (InstalledRoundCommit.concreteCommitRound routedHash)
    (Verifier.start ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
      routedPublicConfig routedPublicProof))
    (routedPublicProof.logRounds.zip routedPublicProof.gateRounds)).2.1
  have hz : (routedPublicProof.logRounds.zip routedPublicProof.gateRounds).length = 13 := rfl
  rw [hz] at h
  exact h

theorem routed_public_wire_map :
    routedPublicConfig.publicInputWireMap = List.replicate 9 (0 : UInt8) := rfl

/-- **THE PUBLIC-INPUT CLAUSE OF `Norm.shapeValid` IS NOW SATISFIABLE.**  Each
declared public input targets column zero, which is below `numRouted = 80`; at
`numRouted = 0` no column at all is below zero. -/
theorem routed_public_targets_are_in_range (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (i : Nat) :
    (Norm.targetAt routedPublicConfig.publicInputWireMap i).column <
        routedPublicConfig.numRouted ∧
      (Norm.targetAt routedPublicConfig.publicInputWireMap i).row <
        2 ^ (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
          routedPublicConfig routedPublicProof).logPoint.length := by
  rw [routed_public_wire_map, target_at_zero_map, routed_public_log_point_length khash P]
  exact ⟨by decide, by decide⟩

theorem routed_public_norm_shape_valid (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Norm.shapeValid routedPublicConfig
        (Norm.challengesFromInitial
          ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
            routedPublicConfig routedPublicProof))
        (Verifier.normTerminalInput routedPublicProof)
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
          routedPublicConfig routedPublicProof).logPoint = true := by
  have hpt := routed_public_log_point_length khash P
  have htau := (DerivedAcceptance.derived_tau_lengths routedHash khash P routedPublicConfig
    routedPublicProof).1
  simp only [Norm.shapeValid, decide_eq_true_eq]
  refine ⟨hpt, ?_, ?_, List.length_replicate _ _, by decide, List.length_replicate _ _,
    List.length_replicate _ _, List.length_replicate _ _, List.length_replicate _ _, ?_, ?_⟩
  · show ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
      routedPublicConfig routedPublicProof).logTau.length = _
    rw [htau, hpt]
    rfl
  · show (List.replicate 13 (Verifier.base 1)).length = _
    rw [List.length_replicate, hpt]
  · show (List.replicate 9 (0 : UInt8)).length =
      3 * (List.replicate 3 (Verifier.base 0)).length
    rw [List.length_replicate, List.length_replicate]
  · intro i _
    exact routed_public_targets_are_in_range khash P i

theorem routed_public_integrated_norm_result (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.normResult (DerivedAcceptance.derivedEngine routedHash khash P)
      routedPublicConfig routedPublicProof = some Verifier.zero := by
  have hchal : ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
      routedPublicConfig routedPublicProof).logChallenges.length = 7 :=
    (OuterInitial.derived_initial_shape routedHash routedPublicConfig
      (Verifier.statement routedPublicProof)).1
  simp only [Integrated.normResult, Norm.checkedNormEvaluation, Norm.checkedEvaluate,
    hchal, if_pos, routed_public_norm_shape_valid, ite_true]
  show some (Norm.normEvaluation routedPublicConfig _ _ _) = _
  refine congrArg some ?_
  exact norm_terminal_vanishes_at_minus_one_rho_and_zero_binding routedPublicConfig _
    (Verifier.normTerminalInput routedPublicProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j)
    (routed_public_binding_vanishes _ _)
    (routed_public_rho_is_minus_one khash P routedPublicConfig routedPublicProof)

theorem routed_public_integrated_gate_result (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.gateResult (DerivedAcceptance.derivedEngine routedHash khash P)
      DerivedAcceptance.derivedDecoder routedPublicConfig routedPublicProof =
      some Verifier.zero := by
  show Integrated.evaluateGate DerivedAcceptance.derivedDecoder routedPublicConfig
    routedPublicProof.used.gateWitness
    (routedPublicProof.used.gatePreprocessed.take routedPublicConfig.numConstants)
    ((DerivedAcceptance.derivedEngine routedHash khash P).publicInputsHash
      routedPublicProof.publicInputs) _ = _
  rw [DerivedAcceptance.derived_public_input_hash_field,
    routed_public_gate_claim_columns_are_zero.1, routed_public_gate_claim_columns_are_zero.2,
    routed_public_gate_evaluation_vanishes _
      (PublicInputHashBinding.hash_no_pad_length routedPublicProof.publicInputs)]

/-- **THE INTEGRATED ACCEPTANCE AT EIGHTY ROUTED WIRES AND THREE PUBLIC
INPUTS.**  Every conjunct of `Norm.shapeValid` is now live, the public-input
clause included. -/
theorem routed_public_integrated_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P routedPublicConfig = true) :
    Integrated.verify (DerivedAcceptance.derivedEngine routedHash khash P)
      DerivedAcceptance.derivedDecoder (routedPublicPin khash) 1 routedPublicConfig
      routedPublicProof = .ok () := by
  simp only [Integrated.verify, routed_engine_is_its_own_model_engine,
    routed_public_integrated_norm_result, routed_public_integrated_gate_result]
  exact routed_public_acceptance khash P hprofile

theorem routed_public_integrated_acceptance_at_the_profile_witness
    (khash : Verifier.Bytes → Verifier.Root) :
    Integrated.verify (DerivedAcceptance.derivedEngine routedHash khash
        DerivedAcceptance.derivedProfile) DerivedAcceptance.derivedDecoder
      (routedPublicPin khash) 1 routedPublicConfig routedPublicProof = .ok () :=
  routed_public_integrated_acceptance khash DerivedAcceptance.derivedProfile
    routed_public_profile_passes_the_canonical_check

/-- **ONLY THE THREE STAND-IN-DECODER FIELDS NOW SIT BELOW THE ADOPTED MAXIMAL
INSTANCE.**  `numPublicInputs` has joined the six fields that tie. -/
theorem routed_public_config_ties_the_adopted_maximal_on_seven_fields :
    routedPublicConfig.numRouted = NonDegenerateAcceptance.maximalConfig.numRouted ∧
      routedPublicConfig.numWires = NonDegenerateAcceptance.maximalConfig.numWires ∧
      routedPublicConfig.numConstants = NonDegenerateAcceptance.maximalConfig.numConstants ∧
      routedPublicConfig.degreeBits = NonDegenerateAcceptance.maximalConfig.degreeBits ∧
      routedPublicConfig.indexBits = NonDegenerateAcceptance.maximalConfig.indexBits ∧
      routedPublicConfig.quotientDegree =
        NonDegenerateAcceptance.maximalConfig.quotientDegree ∧
      routedPublicConfig.numPublicInputs =
        NonDegenerateAcceptance.maximalConfig.numPublicInputs := by decide

theorem routed_public_config_is_below_the_adopted_maximal_on_three_fields :
    routedPublicConfig.numSelectors < NonDegenerateAcceptance.maximalConfig.numSelectors ∧
      routedPublicConfig.numGateConstraints <
        NonDegenerateAcceptance.maximalConfig.numGateConstraints ∧
      routedPublicConfig.gateRows < NonDegenerateAcceptance.maximalConfig.gateRows := by decide

/-! ## 14. The digest-ignoring trade, as theorems

Adopted from the adversarial review.  These make unmissable what the header
now leads with: `routedHash` is a `TranscriptCollision`, relation challenges
ignore the statement, and a second distinct-root proof also accepts. -/

theorem challenge_input_injective_in_the_digest (d e : Transcript.Digest) (k : Nat)
    (h : Transcript.challengeInput d k = Transcript.challengeInput e k) : d = e := by
  simp only [Transcript.challengeInput] at h
  have h1 : Transcript.challengePrefix ++ Transcript.digestBytes d =
      Transcript.challengePrefix ++ Transcript.digestBytes e :=
    List.append_cancel_right h
  have h2 : Transcript.digestBytes d = Transcript.digestBytes e :=
    List.append_cancel_left h1
  cases d
  cases e
  simpa [Transcript.digestBytes] using h2

theorem zero_digest_ne_two_digest : zeroDigest ≠ twoDigest := by
  intro h
  have hb := congrArg (fun d : Transcript.Digest => d.bytes.getD 0 ⟨0, by decide⟩) h
  simp [zeroDigest, twoDigest] at hb

/-- **THE HASH COLLIDES.**  Two challenge-inputs at counter zero, carrying
different digests, are distinct strings that both map to `twoDigest`. -/
theorem routed_hash_is_a_transcript_collision :
    CommitmentOrder.TranscriptCollision routedHash := by
  refine ⟨Transcript.challengeInput zeroDigest 0, Transcript.challengeInput twoDigest 0, ?hne, ?heq⟩
  · intro h
    exact zero_digest_ne_two_digest (challenge_input_injective_in_the_digest _ _ _ h)
  · have h3 : counterTag 0 ≠ counterTag 3 := by decide
    have h4 : counterTag 0 ≠ counterTag 4 := by decide
    have h5 : counterTag 0 ≠ counterTag 5 := by decide
    rw [routed_hash_off_the_tuned_counters zeroDigest 0 h3 h4 h5,
      routed_hash_off_the_tuned_counters twoDigest 0 h3 h4 h5]

def altProof : Verifier.Proof :=
  { routedProof with normInverseRoot := ⟨1, by decide⟩ }

theorem alt_proof_differs_in_a_root :
    routedProof.normInverseRoot ≠ altProof.normInverseRoot := by decide

theorem two_distinct_root_proofs_share_rho (c : Verifier.Config) :
    (OuterInitial.derive routedHash c (Verifier.statement routedProof)).log.rho =
      (OuterInitial.derive routedHash c (Verifier.statement altProof)).log.rho := by
  rw [routed_rho_is_minus_one, routed_rho_is_minus_one]

theorem two_distinct_root_proofs_share_lambda (c : Verifier.Config) :
    (OuterInitial.derive routedHash c (Verifier.statement routedProof)).log.lambda =
      (OuterInitial.derive routedHash c (Verifier.statement altProof)).log.lambda := by
  rw [routed_lambda_is_two_everywhere, routed_lambda_is_two_everywhere]

theorem two_distinct_root_proofs_share_kappa (c : Verifier.Config) :
    (OuterInitial.derive routedHash c (Verifier.statement routedProof)).log.kappa =
      (OuterInitial.derive routedHash c (Verifier.statement altProof)).log.kappa := by
  rw [routed_kappa_is_two_everywhere, routed_kappa_is_two_everywhere]

theorem two_distinct_root_proofs_share_beta (c : Verifier.Config) :
    (OuterInitial.derive routedHash c (Verifier.statement routedProof)).log.beta =
      (OuterInitial.derive routedHash c (Verifier.statement altProof)).log.beta := by
  rw [routed_beta_is_two_everywhere, routed_beta_is_two_everywhere]

/-- Relation challenges at this hash are functions of the counter layout
alone. -/
theorem rho_ignores_the_statement (c : Verifier.Config) (s t : Verifier.Statement) :
    (OuterInitial.derive routedHash c s).log.rho =
      (OuterInitial.derive routedHash c t).log.rho := by
  rw [routed_rho_is_minus_one, routed_rho_is_minus_one]

/-- The adopted dependence implication holds because its collision conclusion
is true.  That is NOT proof-dependent challenges. -/
theorem dependence_implication_holds_because_the_hash_collides
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p q : Verifier.Proof) (hdb : c.degreeBits ≤ 13)
    (hne : p.preprocessedRoot ≠ q.preprocessedRoot ∨ p.witnessRoot ≠ q.witnessRoot ∨
      p.normInverseRoot ≠ q.normInverseRoot)
    (h : ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript c p).transcript =
      ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript c q).transcript) :
    CommitmentOrder.TranscriptCollision routedHash :=
  DerivedAcceptance.derived_transcript_depends_on_the_proof routedHash khash P c p q hdb hne h

theorem alt_shape_holds (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.shape (routedPin khash) routedConfig altProof = true := by
  simpa [altProof] using routed_shape_holds khash

theorem alt_claims_vanish (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig altProof).logClaim = Verifier.zero ∧
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig altProof).gateClaim = Verifier.zero := by
  refine DerivedAcceptance.run_rounds_keeps_zero_claims _ _ _ ?_ rfl rfl
  intro m hm
  obtain ⟨hl, hg⟩ := List.of_mem_zip hm
  exact ⟨⟨5, List.eq_of_mem_replicate hl⟩, ⟨10, List.eq_of_mem_replicate hg⟩⟩

theorem alt_log_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine routedHash khash P).logTerminal routedConfig
        ((DerivedAcceptance.derivedEngine routedHash khash P).initialTranscript
          routedConfig altProof) altProof
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
          routedConfig altProof).logPoint =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig altProof).logClaim := by
  rw [(alt_claims_vanish khash P).1]
  refine norm_terminal_vanishes_at_minus_one_rho routedConfig _
    (Verifier.normTerminalInput altProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j) rfl ?_
  show (Norm.challengesFromInitial (OuterInitial.toInitial
    (OuterInitial.derive routedHash routedConfig (Verifier.statement altProof)))).rho = _
  rw [OuterInitial.initial_norm_adapter_is_lossless]
  exact routed_rho_is_minus_one _ _

theorem alt_expected_claims_are_zero (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine routedHash khash P)
      routedConfig altProof).expectedClaims =
      [some Verifier.zero, some Verifier.zero, some Verifier.zero, some Verifier.zero,
        some Verifier.zero, none] := by
  show Verifier.expectedClaims Connections.packedFold routedConfig altProof
    (Verifier.derivedIndices (DerivedAcceptance.derivedEngine routedHash khash P)
      routedConfig altProof) = _
  simp only [Verifier.expectedClaims, List.cons.injEq, Option.some.injEq, and_true]
  exact ⟨DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _⟩

theorem alt_whir_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.verifyWhir (DerivedAcceptance.derivedEngine routedHash khash P)
      (Verifier.derivedContext (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig altProof) altProof = true := by
  simp only [Verifier.verifyWhir, Verifier.rootsAndClaimsMatch]
  rw [alt_expected_claims_are_zero khash P]
  rfl

theorem alt_gate_claim_columns_are_zero :
    altProof.used.gateWitness = List.replicate 160 Verifier.zero ∧
      altProof.used.gatePreprocessed.take routedConfig.numConstants =
        List.replicate 80 Verifier.zero := ⟨rfl, rfl⟩

theorem alt_gate_evaluation_at_the_proof (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    (DerivedAcceptance.derivedEngine routedHash khash P).gateEvaluation routedConfig
        altProof.used.gateWitness
        (altProof.used.gatePreprocessed.take routedConfig.numConstants) publicHash alpha =
      Verifier.zero := by
  rw [DerivedAcceptance.derived_gate_evaluation_field]
  simp only []
  rw [alt_gate_claim_columns_are_zero.1, alt_gate_claim_columns_are_zero.2,
    routed_gate_evaluation_vanishes publicHash hp]
  rfl

theorem alt_gate_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.gateTerminal (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig altProof =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine routedHash khash P)
        routedConfig altProof).gateClaim := by
  rw [(alt_claims_vanish khash P).2, DerivedAcceptance.gate_terminal_unfolds,
    DerivedAcceptance.derived_public_input_hash_field,
    alt_gate_evaluation_at_the_proof khash P _
      (PublicInputHashBinding.hash_no_pad_length altProof.publicInputs)]
  exact Algebra.vmul_zero _

/-- **GATE 7 DOES NOT SEPARATE THESE TWO PROOFS.**  A second, distinct proof is
also accepted at this hash.  `shape` binds `preprocessedRoot` to the pin and
does not bind the other two roots. -/
theorem alt_proof_is_also_accepted (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P routedConfig = true) :
    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash P) (routedPin khash) 1
      routedConfig altProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl routed_config_envelope ?_
    (alt_shape_holds khash)
    (DerivedAcceptance.derived_tau_lengths routedHash khash P routedConfig altProof).1
    (DerivedAcceptance.derived_tau_lengths routedHash khash P routedConfig altProof).2
    (DerivedAcceptance.derived_index_lengths routedHash khash P routedConfig altProof
      (by decide)).1
    (DerivedAcceptance.derived_index_lengths routedHash khash P routedConfig altProof
      (by decide)).2
    (alt_log_terminal_gate khash P) (alt_whir_gate khash P)
    (alt_gate_terminal_gate khash P)
  show ExplicitEngine.explicitDeployment P DerivedAcceptance.derivedConfig routedConfig = true
  have hw : routedConfig.whirEncoding = DerivedAcceptance.derivedConfig.whirEncoding := rfl
  simp [ExplicitEngine.explicitDeployment, hw, hprofile]

theorem alt_proof_is_also_accepted_at_the_profile_witness
    (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash
        DerivedAcceptance.derivedProfile) (routedPin khash) 1 routedConfig altProof = .ok () :=
  alt_proof_is_also_accepted khash DerivedAcceptance.derivedProfile
    routed_profile_passes_the_canonical_check

end Audit.Wire3.RoutedAcceptance
