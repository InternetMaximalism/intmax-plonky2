import Audit.Wire3.OuterAdapter
import Audit.Wire3.EqTableProvenance
import Audit.Wire3.IntegratedTerminalChain

/-!
# Transcript provenance of the challenges the terminal modules assumed (wire v3)

This module DISCHARGES the transcript-derived hypotheses that the adopted
terminal/glue modules carry: `Audit.Wire3.NormTerminalBinding`'s `hi`
(`Norm.challengesFromInitial i = p.challenges`), `Audit.Wire3.EqTableProvenance`'s
`NormColumnProvenance.tauValues` and the gate `htau` / `hpt` gate, and
`Audit.Wire3.IntegratedTerminalChain`'s `NormTerminalProvenance.challenges`,
`GateChainHypotheses.alphaMatches` and the `logTau` / `gateTau` /
`sevenChallenges` conjuncts of `ObservationOnly`.

## What this module is, and is NOT, about

It is about the ORDER and the PLUMBING of the Fiat--Shamir derivation: that the
challenge values the prover's columns were built from are LITERALLY the values
the verifier recomputes from its own transcript, in the source's frame order and
at the source's counter offsets. `Transcript.Hash` stays an ARBITRARY
deterministic function throughout: nothing here assumes it is injective,
collision-resistant, uniform, or a random oracle, and nothing here is a
distributional, unpredictability or Fiat--Shamir-soundness statement. Every
theorem holds for every `hash`.

Consequently these are not "the challenges are unpredictable" theorems; they are
"the challenges are not a second, independent input" theorems. A model in which
the prover's `tau` were an unrelated list is exactly what the adopted hypotheses
left open, and that is what is closed here.

## Sources reviewed (worktree intmax-plonky2-lean-wire3)

* `mle/contracts/src/MleVerifierV2.sol` 394-456 (`_deriveInitialTranscript`):
  the base frames (401-436), then at 437-455 `eta` after
  `DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2`, `beta`/`gamma` after
  `DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2` and BEFORE the norm-inverse root
  frame `DOMAIN_GROUP_NORM_INVERSE_V2` (443-444), then `xi` after
  `DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2`, `lambda`/`rho`/`kappa` after
  `DOMAIN_OUTER_RELATION_CHALLENGES_V2`, then `degreeBits` log-tau squeezes
  (453), `gateAlpha` (454), `degreeBits` gate-tau squeezes (455).
* `mle/contracts/src/TranscriptV2.sol` 52-62 (`create`, `domainSeparate`,
  `absorbBytes`), 83-135 (the prevalidated vector absorbs), 207-217
  (`bindWhirIdentifiers`, the 64/32-byte identifier guard), 219-247
  (`squeezeChallenge`/`squeezeExt3` and their u64 counter checks).
* `mle/src/prover_v2.rs` 90-142 (`absorb_v2_statement_and_base_roots`: the same
  frames in the same order) and 428-497: the prover squeezes `eta`, `beta`,
  `gamma`, absorbs the norm-inverse root it just committed, squeezes `xi`,
  `lambda`, `rho`, `kappa`, then `tau_log` (472), `gate_alpha` (474) and
  `gate_tau` (475), and PASSES THOSE VERY VALUES into
  `NormLogupProverState::new_with_public_inputs` (477, `&tau_log` at 483) and
  `GateExt3ProverState::new` (490, `gate_alpha` 496, `&gate_tau` 497). That
  pass-through is precisely what `values_log_tau_column`,
  `values_gate_tau_column` and `gate_alpha_element_matches` state in the model.
* `mle/src/verifier_v2.rs` 232-275: the verifier recomputes the identical
  stream (`eta` 254, `beta`/`gamma` 256-257, root absorb 258-259, `xi` 261,
  `lambda`/`rho`/`kappa` 267-269, `tau_log` 273, `gate_alpha` 274,
  `gate_tau` 275) and 386-434 consumes it in the WHIR/norm/gate terminals.
* `mle/src/transcript_v2.rs` 34-134 (the shared sponge: `new`,
  `domain_separate`, `absorb_bytes`, `absorb_field_vec`, `squeeze_challenge`,
  `squeeze_ext3`, `squeeze_ext3_challenges`).

All of the above are already modelled by the adopted
`Audit.Wire3.OuterInitial` (`baseMessages`, `derive`, `checkedDerive`,
`toInitial`, the counter-exact `ext3At` theorems) and
`Audit.Wire3.OuterAdapter` (`execute`,
`execute_matches_existing_derived_context`). This module re-uses that model; it
does not re-derive the transcript.

## Adopted Lean reused, never re-implemented

`Audit.Wire3.OuterInitial` (`derive` 247-254, `checkedDerive` 258-269,
`toInitial` 410-411, `withInitial` 428-429,
`initial_norm_adapter_is_lossless` 417-419, `derived_initial_shape` 421-426,
`derived_tau_lengths` 271-274, `seven_values_have_exact_counter_inputs`
549-557, `log_tau_uses_following_counter_blocks` 559-563,
`gate_alpha_follows_log_tau` 565-571, `gate_tau_follows_gate_alpha` 573-582,
`checked_derive_exact` 292-349, `source_sized_initial_derivation` 516-527),
`Audit.Wire3.OuterAdapter` (`execute` 422-428,
`source_sized_execution_exists` 430-462, `execute_success_uses_same_inputs`
464-486, `execute_matches_existing_derived_context` 511-536, `fixtureConfig`
536-541, `fixtureProof` 544-548, `ordinary_prefix_for_every_hash` 550-556),
`Audit.Wire3.Norm` (`Challenges` 148-156, `challengeList` 158-159,
`challengesFromInitial` 161-165, `challenges_roundtrip` 167-168,
`shapeValid` 311-321, `withNormEvaluation` 369),
`Audit.Wire3.OuterRound` (`lift` 227, `lift_list_roundtrip` 229-230),
`Audit.Wire3.NormDenseRound` (`values` 236),
`Audit.Wire3.NormTerminalBinding` (`fully_bound_target_is_engine_terminal`
578-591), `Audit.Wire3.EqTableProvenance` (`NormColumnProvenance` 620-626,
`fully_bound_target_is_norm_evaluate_of_columns` 631-658,
`honest_prover_terminal_of_columns` 665-696, `GateEqProvenance` 700-702,
`bound_gate_eq_cell` 705-733,
`bound_terminal_is_engine_gate_terminal_of_eq_table` 734-761,
`honest_last_round_is_engine_gate_terminal_of_eq_table` 763-799),
`Audit.Wire3.IntegratedTerminalChain` (`NormTerminalProvenance` 154-161,
`NormChainHypotheses` 169-174, `honest_log_terminal_matches_chain` 204-215,
`GateChainHypotheses` 370-401, `honest_gate_terminal_matches_claim` 403-416,
`ObservationOnly` 632-648, `honest_prover_passes_deterministic_checks`
658-680), `Audit.Wire3.Integrated` (`modelEngine` 43-49).

## What is proved

1. `DerivedInitial hash e c p` names "this engine's initial observation IS the
   source's own derivation on this proof's statement". It holds by `rfl` for
   `OuterInitial.withInitial hash e`, and it is exactly the hypothesis `hi` of
   the adopted `OuterAdapter.execute_matches_existing_derived_context`, so a
   whole checked `execute` run has it (`execute_initial_is_derived`).
2. (1) `challenges_from_initial_is_derived`: under `DerivedInitial`,
   `Norm.challengesFromInitial (e.initialTranscript c p)` is EXACTLY the
   seven-value `Norm.Challenges` record the derivation produced, and
   `derived_challenges_at_source_counters` pins each of the seven to its source
   digest/counter pair.
3. (2) `values_log_tau_column`, `values_gate_tau_column`,
   `gate_alpha_element_matches` and `values_gate_point_column`: the prover-side
   `List Element` columns obtained by lifting the derived lists satisfy
   `NormColumnProvenance.tauValues`, the gate `htau`, `hpt` and
   `GateChainHypotheses.alphaMatches` by computation.
4. (3) `derived_seven_challenges`, `derived_log_tau_length`,
   `derived_gate_tau_length`: three `ObservationOnly` conjuncts fall out of the
   derivation. `derived_norm_shape_valid` additionally removes the
   `ch.tau.length = point.length` conjunct from `Norm.shapeValid` (it is now
   implied by `point.length = c.degreeBits`), so the surviving `normShape`
   obligation is strictly smaller too.
5. (4) Restatements with those hypotheses gone:
   `fully_bound_target_is_engine_terminal_derived`,
   `fully_bound_target_is_norm_evaluate_of_derived_columns`,
   `honest_prover_terminal_of_derived_columns`,
   `bound_terminal_is_engine_gate_terminal_of_derived_transcript`,
   `honest_last_round_is_engine_gate_terminal_of_derived_transcript`,
   `honest_log_terminal_matches_chain_derived`,
   `honest_gate_terminal_matches_claim_derived`,
   `honest_prover_passes_deterministic_checks_derived`. The shrunken hypothesis
   sets are named structures (`NormProvenanceResidue`, `GateChainResidue`,
   `ObservationOnlyDerived`) so the before/after lists can be diffed field by
   field against `NormTerminalProvenance`, `GateChainHypotheses` and
   `ObservationOnly`.
6. (5) `Example`: for EVERY `hash`, `OuterInitial.withInitial hash e` on the
   adopted `OuterAdapter.fixtureConfig` / `fixtureProof` satisfies
   `DerivedInitial`, the checked `OuterAdapter.execute` succeeds on it, and the
   three discharged observation conjuncts and the four discharged column/alpha
   facts hold concretely.

## Boundaries (explicitly NOT proved)

* Nothing about `hash`: no injectivity, collision resistance, uniformity,
  unpredictability, random-oracle or Fiat--Shamir-soundness property. The
  results are pure plumbing identities and hold for every deterministic `hash`.
* `hpt` is NOT discharged. It is RE-EXPRESSED as `hpoint : steps.map Prod.snd =
  gatePointColumn e c p`, an equivalent hypothesis (`Element` is a one-field
  wrapper, so `values_gate_point_column` is only the lift roundtrip), and it
  remains a live hypothesis of every gate-side restatement and a field of
  `GateChainResidue`. It is about the ROUND phase, not the initial derivation:
  it says the gate steps the prover bound are the lifts of the verifier's own
  `derivedRounds ... .gatePoint`, and the coupled-round transcript itself is
  `OuterAdapter.runChecked` / `OuterClaimChain`, not this module.
* The honest-prover corollaries (`honest_*`) stay HONEST-PROVER ONLY, exactly as
  the adopted theorems they restate: they say what an honest prover's tables
  evaluate to, never that a verifier-accepted claim came from such a prover.
* Residues left standing and named: `ObservationOnlyDerived` (nine conjuncts,
  down from twelve), `NormProvenanceResidue` (five fields, down from six),
  `GateChainResidue` (twelve fields, down from thirteen),
  `EqTableProvenance.SubgroupPowersProvenance`, `HonestNormProver.zeroSum`,
  `GateChainHypotheses.grid`, `HonestOpenings.opened`. Config/VK digest
  provenance, the public-input hash, WHIR/PCS soundness and Rust/EVM refinement
  remain outside.
-/

namespace Audit.Wire3.TranscriptProvenance

open Audit.Wire3 GoldilocksExt3Field NormDenseRound NormTerminalBinding

abbrev Hash := Transcript.Hash

/-! ## 1. "The engine's initial observation is the source's own derivation" -/

/-- The source's derivation on this proof's statement (`MleVerifierV2.sol`
394-480 / `prover_v2.rs` 90-165, as modelled by `OuterInitial.derive`). -/
def derived (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) : OuterInitial.Result :=
  OuterInitial.derive hash c (Verifier.statement p)

/-- The single named premise of this module: the engine's initial observation
IS `toInitial` of the source's own derivation. This is not a new assumption
about the hash; it is the identification of the engine hook with the modelled
source function, and it is literally the hypothesis `hi` of the adopted
`OuterAdapter.execute_matches_existing_derived_context`. -/
def DerivedInitial (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) : Prop :=
  e.initialTranscript c p = OuterInitial.toInitial (derived hash c p)

theorem withInitial_derived (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) :
    DerivedInitial hash (OuterInitial.withInitial hash e) c p := rfl

/-- The two adopted engine wrappers do not touch `initialObservation`. -/
theorem derived_initial_withNormEvaluation (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (h : DerivedInitial hash e c p) :
    DerivedInitial hash (Norm.withNormEvaluation e) c p := h

theorem derived_initial_modelEngine (hash : Hash) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (c : Verifier.Config) (p : Verifier.Proof)
    (h : DerivedInitial hash e c p) :
    DerivedInitial hash (Integrated.modelEngine e decode) c p := h

/-- A whole checked `OuterAdapter.execute` run has `DerivedInitial` for its own
initial component: the executed transcript prefix is the derivation. -/
theorem execute_initial_is_derived (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (result : OuterAdapter.Execution) (hd : c.degreeBits ≤ 13)
    (h : OuterAdapter.execute hash c p = some result) :
    result.initial = OuterInitial.toInitial (derived hash c p) := by
  obtain ⟨_, initial, _, hini, hei, _, _, _⟩ :=
    OuterAdapter.execute_success_uses_same_inputs hash c p result h
  have hh : initial = OuterInitial.derive hash c (Verifier.statement p) :=
    Option.some.inj (hini.symm.trans (OuterInitial.checked_derive_exact hash c _ hd))
  rw [hei, hh]
  rfl

/-! ## 2. (1) The seven challenges `Norm.challengesFromInitial` returns -/

/-- The `Norm.Challenges` record the derivation produced. -/
def logChallenges (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) : Norm.Challenges :=
  (derived hash c p).log

/-- (1) DISCHARGES `NormTerminalBinding.fully_bound_target_is_engine_terminal`'s
`hi` and `IntegratedTerminalChain.NormTerminalProvenance.challenges`: for a
proof whose initial transcript is the source's own derivation,
`Norm.challengesFromInitial` returns EXACTLY the seven challenges that
derivation produced. No hash property is used; the content is that the
seven-slot `Initial` layout (`Norm.challengeList`: eta, beta, gamma, xi, lambda,
rho, kappa) and the reader `Norm.challengesFromInitial` (slots 1,2,4,5,6,0,3)
are inverse, applied to the derivation's own output. -/
theorem challenges_from_initial_is_derived (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (h : DerivedInitial hash e c p) :
    Norm.challengesFromInitial (e.initialTranscript c p) = logChallenges hash c p := by
  rw [h]
  exact OuterInitial.initial_norm_adapter_is_lossless (derived hash c p)

/-- The seven values, each pinned to the source digest and counter offset it is
squeezed at (`OuterInitial.seven_values_have_exact_counter_inputs`): eta after
the aggregation domain, beta and gamma after the denominator domain and BEFORE
the norm-inverse root frame, xi after the mix domain, lambda/rho/kappa after the
relation domain at offsets 0/3/6. -/
theorem derived_challenges_at_source_counters (hash : Hash) (c : Verifier.Config)
    (p : Verifier.Proof) :
    (logChallenges hash c p).eta =
        OuterInitial.ext3At hash (OuterInitial.etaState hash c (Verifier.statement p)).digest 0 ∧
    (logChallenges hash c p).beta =
        OuterInitial.ext3At hash (OuterInitial.denominatorState hash c (Verifier.statement p)).digest 0 ∧
    (logChallenges hash c p).gamma =
        OuterInitial.ext3At hash (OuterInitial.denominatorState hash c (Verifier.statement p)).digest 3 ∧
    (logChallenges hash c p).xi =
        OuterInitial.ext3At hash (OuterInitial.mixState hash c (Verifier.statement p)).digest 0 ∧
    (logChallenges hash c p).lambda =
        OuterInitial.ext3At hash (OuterInitial.relationState hash c (Verifier.statement p)).digest 0 ∧
    (logChallenges hash c p).rho =
        OuterInitial.ext3At hash (OuterInitial.relationState hash c (Verifier.statement p)).digest 3 ∧
    (logChallenges hash c p).kappa =
        OuterInitial.ext3At hash (OuterInitial.relationState hash c (Verifier.statement p)).digest 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The derived `tau` of the norm lane is the transcript's `logTau` field. -/
theorem derived_challenges_tau (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    (logChallenges hash c p).tau = (OuterInitial.toInitial (derived hash c p)).logTau := rfl

/-! ## 3. (2) The prover-side columns are the derived lists -/

/-- Lift a verifier-side challenge list to the prover's `Element` column.
`OuterRound.lift a = ⟨a⟩` is the adopted embedding; `NormDenseRound.values` is
its left inverse (`OuterRound.lift_list_roundtrip`). -/
def liftList (xs : List Verifier.Ext3) : List Element := xs.map OuterRound.lift

theorem values_liftList (xs : List Verifier.Ext3) : values (liftList xs) = xs :=
  OuterRound.lift_list_roundtrip xs

theorem liftList_length (xs : List Verifier.Ext3) : (liftList xs).length = xs.length :=
  List.length_map _ _

/-- The norm prover's `tau` column: the derived log-tau list, lifted. -/
def logTauColumn (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) : List Element :=
  liftList (logChallenges hash c p).tau

/-- The gate prover's `tau` column: the derived gate-tau list, lifted. -/
def gateTauColumn (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) : List Element :=
  liftList (derived hash c p).gateTau

/-- The gate prover's alpha: the derived `gateAlpha`, lifted. -/
def gateAlphaElement (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) : Element :=
  OuterRound.lift (derived hash c p).gateAlpha

/-- The gate prover's binding point: the verifier's own `derivedRounds`
gate point, lifted. PLUMBING OF THE ROUND PHASE, not of the initial
derivation — it holds for every engine. -/
def gatePointColumn (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof) : List Element :=
  liftList (Verifier.derivedRounds e c p).gatePoint

/-- (2) DISCHARGES `EqTableProvenance.NormColumnProvenance.tauValues`. -/
theorem values_log_tau_column (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    values (logTauColumn hash c p) = (logChallenges hash c p).tau :=
  values_liftList _

/-- (2) DISCHARGES the gate `htau` of
`EqTableProvenance.bound_terminal_is_engine_gate_terminal_of_eq_table`. -/
theorem values_gate_tau_column (hash : Hash) (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (h : DerivedInitial hash e c p) :
    values (gateTauColumn hash c p) = (e.initialTranscript c p).gateTau := by
  rw [h]
  exact values_liftList (derived hash c p).gateTau

/-- (2) DISCHARGES `IntegratedTerminalChain.GateChainHypotheses.alphaMatches`. -/
theorem gate_alpha_element_matches (hash : Hash) (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (h : DerivedInitial hash e c p) :
    (gateAlphaElement hash c p).toVerifier = (e.initialTranscript c p).gateAlpha := by
  rw [h]
  rfl

/-- (2) DISCHARGES the gate `hpt`. ROUND-PHASE PLUMBING: no `DerivedInitial`
needed, this holds for every engine. -/
theorem values_gate_point_column (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof) :
    values (gatePointColumn e c p) = (Verifier.derivedRounds e c p).gatePoint :=
  values_liftList _

/-- Widths, from the derivation's `degreeBits` squeeze counts. -/
theorem derived_column_lengths (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    (logTauColumn hash c p).length = c.degreeBits ∧
    (gateTauColumn hash c p).length = c.degreeBits := by
  refine ⟨?_, ?_⟩
  · rw [logTauColumn, liftList_length]
    exact (OuterInitial.derived_tau_lengths hash c (Verifier.statement p)).1
  · rw [gateTauColumn, liftList_length]
    exact (OuterInitial.derived_tau_lengths hash c (Verifier.statement p)).2

/-- Each entry of both columns is the source's three consecutive reduced digests
at the exact counter block, after the relation domain separator: log-tau at
`9+3i`, gate alpha at `9+3·degreeBits`, gate tau at `12+3·degreeBits+3i`. -/
theorem derived_columns_at_source_counters (hash : Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (i : Nat) (hi : i < c.degreeBits) :
    (logChallenges hash c p).tau.get? i =
        some (OuterInitial.ext3At hash
          (OuterInitial.relationState hash c (Verifier.statement p)).digest (9 + 3 * i)) ∧
    (derived hash c p).gateAlpha =
        OuterInitial.ext3At hash
          (OuterInitial.relationState hash c (Verifier.statement p)).digest (9 + 3 * c.degreeBits) ∧
    (derived hash c p).gateTau.get? i =
        some (OuterInitial.ext3At hash
          (OuterInitial.relationState hash c (Verifier.statement p)).digest
          (12 + 3 * c.degreeBits + 3 * i)) :=
  ⟨OuterInitial.log_tau_uses_following_counter_blocks hash c (Verifier.statement p) i hi,
   OuterInitial.gate_alpha_follows_log_tau hash c (Verifier.statement p),
   OuterInitial.gate_tau_follows_gate_alpha hash c (Verifier.statement p) i hi⟩

/-! ## 4. (3) Observation conjuncts that the derivation settles -/

/-- (3) DISCHARGES `IntegratedTerminalChain.ObservationOnly.sevenChallenges`. -/
theorem derived_seven_challenges (hash : Hash) (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (h : DerivedInitial hash e c p) :
    (e.initialTranscript c p).logChallenges.length = 7 := by
  rw [h]
  exact (OuterInitial.derived_initial_shape hash c (Verifier.statement p)).1

/-- (3) DISCHARGES `IntegratedTerminalChain.ObservationOnly.logTau`. -/
theorem derived_log_tau_length (hash : Hash) (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (h : DerivedInitial hash e c p) :
    (e.initialTranscript c p).logTau.length = c.degreeBits := by
  rw [h]
  exact (OuterInitial.derived_initial_shape hash c (Verifier.statement p)).2.1

/-- (3) DISCHARGES `IntegratedTerminalChain.ObservationOnly.gateTau`. -/
theorem derived_gate_tau_length (hash : Hash) (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (h : DerivedInitial hash e c p) :
    (e.initialTranscript c p).gateTau.length = c.degreeBits := by
  rw [h]
  exact (OuterInitial.derived_initial_shape hash c (Verifier.statement p)).2.2.1

/-- `Norm.shapeValid` (Norm.lean 311-321) with its `ch.tau.length = point.length`
conjunct REMOVED: under `DerivedInitial` that conjunct follows from
`point.length = c.degreeBits`, which is already the first conjunct. So the
surviving `normShape` observation is strictly smaller. -/
def NormShapeResidue (c : Verifier.Config) (t : Verifier.NormTerminalInput)
    (point : List Verifier.Ext3) : Prop :=
  point.length = c.degreeBits ∧
  c.subgroupPowers.length = point.length ∧ c.kIs.length = c.numRouted ∧
  c.numRouted ≤ c.numWires ∧ t.witness.length = c.numWires ∧
  t.preprocessed.length = c.numConstants + c.numRouted ∧
  t.normInverse.length = 2 * c.numRouted ∧
  t.publicInputs.length = c.numPublicInputs ∧
  c.publicInputWireMap.length = 3 * t.publicInputs.length ∧
  ∀ i, i < t.publicInputs.length →
    (Norm.targetAt c.publicInputWireMap i).column < c.numRouted ∧
    (Norm.targetAt c.publicInputWireMap i).row < 2 ^ point.length

theorem derived_norm_shape_valid (hash : Hash) (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3)
    (h : DerivedInitial hash e c p) (hr : NormShapeResidue c t point) :
    Norm.shapeValid c (Norm.challengesFromInitial (e.initialTranscript c p)) t point = true := by
  have htau : (Norm.challengesFromInitial (e.initialTranscript c p)).tau.length = point.length := by
    rw [show (Norm.challengesFromInitial (e.initialTranscript c p)).tau
        = (e.initialTranscript c p).logTau from rfl,
      derived_log_tau_length hash e c p h, hr.1]
  simp only [Norm.shapeValid, decide_eq_true_eq]
  exact ⟨hr.1, htau, hr.2⟩

/-! ## 5. (4) The adopted theorems restated with those hypotheses gone

### 5.1 `NormTerminalBinding` -/

/-- (4) `NormTerminalBinding.fully_bound_target_is_engine_terminal` (1141-line
module, 578-591) with `hi` DISCHARGED: the prover's challenges are no longer
assumed to be the transcript's, they are supplied BY the transcript. -/
theorem fully_bound_target_is_engine_terminal_derived (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (t : Tables) (pr : Prepared)
    (constants extra : List Verifier.Ext3) (point : List Verifier.Ext3)
    (hd : DerivedInitial hash e c p) (hch : pr.challenges = logChallenges hash c p)
    (h : Shape t pr) (hc : Compatible c t pr constants)
    (hlam : LambdaProvenance pr) (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (heta : EtaProvenance (NormPolynomial.lift pr.challenges.eta) t.bindings)
    (hprefix : PrefixAt point t.bindings)
    (heq : (cell t.eq).toVerifier = Norm.eqEvaluation pr.challenges.tau point)
    (hsub : (cell t.subgroup).toVerifier = Norm.subgroupEvaluation c.subgroupPowers point)
    (hp : Verifier.normTerminalInput p = toTerminalInput t constants extra) :
    terminalTarget t pr =
      some ((Norm.withNormEvaluation e).logTerminal c (e.initialTranscript c p) p point) :=
  NormTerminalBinding.fully_bound_target_is_engine_terminal e (e.initialTranscript c p) p t pr c
    constants extra point h hc hlam hmap heta hprefix heq hsub
    ((challenges_from_initial_is_derived hash e c p hd).trans hch.symm) hp

/-! ### 5.2 `EqTableProvenance`, norm side -/

/-- `EqTableProvenance.NormColumnProvenance` with `tauValues` REMOVED: the tau
column is no longer a free list constrained by a hypothesis, it IS
`logTauColumn`. -/
structure NormColumnResidue (hash : Hash) (t : Tables) (c : Verifier.Config)
    (p : Verifier.Proof) (g : Element) : Prop where
  eqColumn : t.eq = EqTableProvenance.eqTable (logTauColumn hash c p)
  tauWidth : (logTauColumn hash c p).length = t.remaining
  subgroupColumn : t.subgroup = EqTableProvenance.subgroupTable g t.remaining
  powers : EqTableProvenance.SubgroupPowersProvenance c.subgroupPowers g t.remaining

theorem normColumnProvenance_of_derived (hash : Hash) (t : Tables) (c : Verifier.Config)
    (p : Verifier.Proof) (pr : Prepared) (g : Element)
    (hch : pr.challenges = logChallenges hash c p) (hr : NormColumnResidue hash t c p g) :
    EqTableProvenance.NormColumnProvenance t c pr.challenges (logTauColumn hash c p) g :=
  { eqColumn := hr.eqColumn
    tauValues := by rw [values_log_tau_column, hch]
    tauWidth := hr.tauWidth
    subgroupColumn := hr.subgroupColumn
    powers := hr.powers }

/-- (4) `EqTableProvenance.fully_bound_target_is_norm_evaluate_of_columns`
(631-658) with `tauValues` DISCHARGED. -/
theorem fully_bound_target_is_norm_evaluate_of_derived_columns (hash : Hash)
    (t t' : Tables) (c : Verifier.Config) (p : Verifier.Proof) (pr : Prepared)
    (constants extra : List Verifier.Ext3) (point : List Element) (g : Element)
    (hch : pr.challenges = logChallenges hash c p)
    (h : Shape t pr) (hpoint : point.length = t.remaining)
    (hb : bindTablesMany point t = some t')
    (hr : NormColumnResidue hash t c p g)
    (hc : Compatible c t' pr constants) (hlam : LambdaProvenance pr)
    (hmap : WireMapMatches c.publicInputWireMap t'.bindings)
    (heta : EtaProvenance (NormPolynomial.lift pr.challenges.eta) t'.bindings)
    (hprefix : PrefixAt (values point) t'.bindings) :
    Shape t' pr ∧ FullyBound t' ∧
      terminalTarget t' pr
        = some (Norm.evaluate c pr.challenges (toTerminalInput t' constants extra) (values point)) :=
  EqTableProvenance.fully_bound_target_is_norm_evaluate_of_columns t t' pr c constants extra point
    (logTauColumn hash c p) g h hpoint hb
    (normColumnProvenance_of_derived hash t c p pr g hch hr) hc hlam hmap heta hprefix

/-- (4) HONEST PROVER ONLY. `EqTableProvenance.honest_prover_terminal_of_columns`
(665-696) with `tauValues` DISCHARGED. -/
theorem honest_prover_terminal_of_derived_columns (hash : Hash) (t : Tables)
    (c : Verifier.Config) (p : Verifier.Proof) (pr : Prepared)
    (constants extra : List Verifier.Ext3) (point : List Element)
    (pairs : List (Nat × Nat × Verifier.Base)) (g : Element)
    (hch : pr.challenges = logChallenges hash c p)
    (h : Shape t pr) (h0 : t.boundVariables = 0) (hpoint : point.length = t.remaining)
    (hbuild : t.bindings = buildBindings (NormPolynomial.lift pr.challenges.eta) 1 pairs)
    (hc : Compatible c t pr constants) (hlam : LambdaProvenance pr)
    (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (hr : NormColumnResidue hash t c p g) :
    ∃ t', bindTablesMany point t = some t' ∧ FullyBound t' ∧
      PrefixAt (point.map Element.toVerifier) t'.bindings ∧
      terminalTarget t' pr
        = some (Norm.evaluate c pr.challenges (toTerminalInput t' constants extra) (values point)) :=
  EqTableProvenance.honest_prover_terminal_of_columns t pr c constants extra point pairs
    (logTauColumn hash c p) g h h0 hpoint hbuild hc hlam hmap
    (normColumnProvenance_of_derived hash t c p pr g hch hr)

/-! ### 5.3 `EqTableProvenance`, gate side -/

/-- (4) `EqTableProvenance.bound_terminal_is_engine_gate_terminal_of_eq_table`
(734-761) with `halpha` and `htau` DISCHARGED from the derivation. `hpt` is not
discharged: it is re-expressed as the equivalent `hpoint` on the verifier's own
round state and remains a hypothesis. -/
theorem bound_terminal_is_engine_gate_terminal_of_derived_transcript (hash : Hash)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (n : Nat) (s t : GateTerminalBinding.ProverState)
    (steps : List (List Verifier.Ext3 × Element)) (k : GateTerminalBinding.Cells)
    (hderiv : DerivedInitial hash e c p)
    (hd : decode c.gatesEncoding = some gates) (hrows : gates.length = c.gateRows)
    (hp : (e.publicInputsHash p.publicInputs).length = 4)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hk : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p))
    (hw : k.wires.length = c.numWires) (hcst : k.constants.length = c.numConstants)
    (hn : s.eq.numVars = n) (hsteps : steps.length = n)
    (hprov : EqTableProvenance.GateEqProvenance s (gateTauColumn hash c p))
    (hb : GateTerminalBinding.bindAll s steps = some t) (hkt : t.tables = k.tables)
    (hpoint : steps.map Prod.snd = gatePointColumn e c p) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      GateTerminalBinding.boundTerminal (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash c p) k = some (Verifier.mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p
        = Verifier.mul k.eq.toVerifier gate :=
  EqTableProvenance.bound_terminal_is_engine_gate_terminal_of_eq_table e decode c p gates n s t
    steps (gateTauColumn hash c p) k (gateAlphaElement hash c p) hd hrows hp hv hk hw hcst
    (gate_alpha_element_matches hash e c p hderiv) hn hsteps hprov hb hkt
    (values_gate_tau_column hash e c p hderiv)
    (by rw [hpoint]; exact values_gate_point_column e c p)

/-- (4) HONEST PROVER ONLY.
`EqTableProvenance.honest_last_round_is_engine_gate_terminal_of_eq_table`
(763-799) with `halpha` and `htau` DISCHARGED from the derivation; `hpt` is
re-expressed as the equivalent `hpoint` and remains a hypothesis. -/
theorem honest_last_round_is_engine_gate_terminal_of_derived_transcript (hash : Hash)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (n : Nat) (s0 t0 : GateTerminalBinding.ProverState)
    (steps : List (List Verifier.Ext3 × Element))
    (s t : GateTerminalBinding.ProverState) (round : List Verifier.Ext3) (x : Element)
    (k : GateTerminalBinding.Cells)
    (hderiv : DerivedInitial hash e c p)
    (hs : GateTerminalBinding.ProverShape (Integrated.gateConfig c) 1 s)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hbc : GateTerminalBinding.bindChallenge s round x = some t)
    (hkt : t.tables = k.tables)
    (hd : decode c.gatesEncoding = some gates) (hrows : gates.length = c.gateRows)
    (hp : (e.publicInputsHash p.publicInputs).length = 4)
    (hk : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p))
    (hn : s0.eq.numVars = n) (hsteps : steps.length = n)
    (hprov : EqTableProvenance.GateEqProvenance s0 (gateTauColumn hash c p))
    (hb : GateTerminalBinding.bindAll s0 steps = some t0) (hkt0 : t0.tables = k.tables)
    (hpoint : steps.map Prod.snd = gatePointColumn e c p) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash c p) x s.tables 1 = some (Verifier.mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p
        = Verifier.mul k.eq.toVerifier gate :=
  EqTableProvenance.honest_last_round_is_engine_gate_terminal_of_eq_table e decode c p gates n s0 t0
    steps (gateTauColumn hash c p) s t round x k (gateAlphaElement hash c p) hs hv hbc hkt hd hrows
    hp hk (gate_alpha_element_matches hash e c p hderiv) hn hsteps hprov hb hkt0
    (values_gate_tau_column hash e c p hderiv)
    (by rw [hpoint]; exact values_gate_point_column e c p)

/-! ### 5.4 `IntegratedTerminalChain` -/

/-- `IntegratedTerminalChain.NormTerminalProvenance` with the field `challenges`
REMOVED (five fields, down from six). -/
structure NormProvenanceResidue (c : Verifier.Config) (p : Verifier.Proof) (pr : Prepared)
    (gates : List (List Verifier.Ext3)) (constants extra : List Verifier.Ext3)
    (tEnd : Tables) (sent : List (List Element)) (chals : List Element) : Prop where
  eqCell : (cell tEnd.eq).toVerifier =
    Norm.eqEvaluation pr.challenges.tau (chals.map Element.toVerifier)
  subgroupCell : (cell tEnd.subgroup).toVerifier =
    Norm.subgroupEvaluation c.subgroupPowers (chals.map Element.toVerifier)
  logRounds : p.logRounds = sent.map (List.map Element.toVerifier)
  gateRounds : p.gateRounds = gates
  claims : Verifier.normTerminalInput p = toTerminalInput tEnd constants extra

theorem normTerminalProvenance_of_derived (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (pr : Prepared)
    (gates : List (List Verifier.Ext3)) (constants extra : List Verifier.Ext3)
    (tEnd : Tables) (sent : List (List Element)) (chals : List Element)
    (hderiv : DerivedInitial hash e c p) (hch : pr.challenges = logChallenges hash c p)
    (hr : NormProvenanceResidue c p pr gates constants extra tEnd sent chals) :
    IntegratedTerminalChain.NormTerminalProvenance e c p pr gates constants extra tEnd sent chals :=
  { eqCell := hr.eqCell
    subgroupCell := hr.subgroupCell
    challenges := (challenges_from_initial_is_derived hash e c p hderiv).trans hch.symm
    logRounds := hr.logRounds
    gateRounds := hr.gateRounds
    claims := hr.claims }

/-- (4) HONEST PROVER ONLY.
`IntegratedTerminalChain.honest_log_terminal_matches_chain` (204-215) with
`NormTerminalProvenance.challenges` DISCHARGED. -/
theorem honest_log_terminal_matches_chain_derived (hash : Hash) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (c : Verifier.Config) (p : Verifier.Proof)
    (t : Tables) (pr : Prepared) (gates : List (List Verifier.Ext3))
    (constants extra : List Verifier.Ext3) (pairs : List (Nat × Nat × Verifier.Base))
    (v' : Verifier.RoundState) (s' : ProverState)
    (sent : List (List Element)) (chals : List Element)
    (hderiv : DerivedInitial hash e c p) (hch : pr.challenges = logChallenges hash c p)
    (hrun : OuterClaimChain.honestRun e.commitRound (Verifier.start (e.initialTranscript c p))
      (initialState t pr) gates = .ok (v', s'))
    (hext : intoProofAndPoint s' = .ok (sent, chals))
    (hhon : IntegratedTerminalChain.HonestNormProver c t pr gates constants pairs)
    (hr : NormProvenanceResidue c p pr gates constants extra s'.tables sent chals) :
    Verifier.derivedRounds e c p = v' ∧ v'.logPoint = chals.map Element.toVerifier ∧
    bindTablesMany chals t = some s'.tables ∧ FullyBound s'.tables ∧
    terminalTarget s'.tables pr = some v'.logClaim ∧
    v'.logClaim = Norm.evaluate c pr.challenges (toTerminalInput s'.tables constants extra)
      (chals.map Element.toVerifier) ∧
    (Integrated.modelEngine e decode).logTerminal c (e.initialTranscript c p) p
        (Verifier.derivedRounds e c p).logPoint = (Verifier.derivedRounds e c p).logClaim :=
  IntegratedTerminalChain.honest_log_terminal_matches_chain e decode c p t pr gates constants extra
    pairs v' s' sent chals hrun hext
    { toHonestNormProver := hhon
      toNormTerminalProvenance :=
        normTerminalProvenance_of_derived hash e c p pr gates constants extra s'.tables sent chals
          hderiv hch hr }

/-- `IntegratedTerminalChain.GateChainHypotheses` with the field `alphaMatches`
REMOVED and `alpha` fixed to the derived `gateAlphaElement` (twelve fields, down
from thirteen). -/
structure GateChainResidue (hash : Hash) (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (pre : List Verifier.CoupledMessage)
    (mLog gLast : List Verifier.Ext3) (gates : List Gates.GateInfo)
    (s t : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells) : Prop where
  split : p.logRounds.zip p.gateRounds = pre ++ [(mLog, gLast)]
  shape : GateTerminalBinding.ProverShape (Integrated.gateConfig c) 1 s
  bind : GateTerminalBinding.bindChallenge s gLast
    (OuterRound.lift (IntegratedTerminalChain.lastGateChallenge e c p pre mLog gLast)) = some t
  cells : t.tables = k.tables
  decode : decode c.gatesEncoding = some gates
  rows : gates.length = c.gateRows
  valid : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ()
  hashLength : (e.publicInputsHash p.publicInputs).length = 4
  claims : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p)
  eqCell : k.eq.toVerifier =
    Norm.eqEvaluation (e.initialTranscript c p).gateTau (Verifier.derivedRounds e c p).gatePoint
  messageLength : gLast.length ≤ c.quotientDegree + 2
  grid : ∀ i, i ≤ c.quotientDegree + 2 →
    GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash c p)
        (GateSlotRound.gridPoint i) s.tables 1 =
      some (Verifier.evaluateRound (IntegratedTerminalChain.lastState e c p pre).gateClaim gLast
        (Norm.embed i))

theorem gateChainHypotheses_of_derived (hash : Hash) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (c : Verifier.Config) (p : Verifier.Proof)
    (pre : List Verifier.CoupledMessage) (mLog gLast : List Verifier.Ext3)
    (gates : List Gates.GateInfo) (s t : GateTerminalBinding.ProverState)
    (k : GateTerminalBinding.Cells)
    (hderiv : DerivedInitial hash e c p)
    (hr : GateChainResidue hash e decode c p pre mLog gLast gates s t k) :
    IntegratedTerminalChain.GateChainHypotheses e decode c p pre mLog gLast gates s t k
      (gateAlphaElement hash c p) :=
  { split := hr.split, shape := hr.shape, bind := hr.bind, cells := hr.cells,
    decode := hr.decode, rows := hr.rows, valid := hr.valid, hashLength := hr.hashLength,
    claims := hr.claims, alphaMatches := gate_alpha_element_matches hash e c p hderiv,
    eqCell := hr.eqCell, messageLength := hr.messageLength, grid := hr.grid }

/-- The `eqCell` field of `GateChainResidue` derived from the gate prover's own
`ext3_eq_evals(gate_tau)` table, using `EqTableProvenance.bound_gate_eq_cell`
with `htau` / `hpt` discharged. This is the point of (2): the gate eq cell can
now be traced to the transcript instead of being assumed equal to it. -/
theorem gate_eq_cell_of_derived_table (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (n : Nat)
    (s t : GateTerminalBinding.ProverState) (steps : List (List Verifier.Ext3 × Element))
    (k : GateTerminalBinding.Cells)
    (hderiv : DerivedInitial hash e c p)
    (hn : s.eq.numVars = n) (hsteps : steps.length = n)
    (hprov : EqTableProvenance.GateEqProvenance s (gateTauColumn hash c p))
    (hb : GateTerminalBinding.bindAll s steps = some t) (hkt : t.tables = k.tables)
    (hpoint : steps.map Prod.snd = gatePointColumn e c p) :
    k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript c p).gateTau (Verifier.derivedRounds e c p).gatePoint := by
  rw [EqTableProvenance.bound_gate_eq_cell n s t steps (gateTauColumn hash c p) k hn hsteps hprov hb hkt,
    values_gate_tau_column hash e c p hderiv, hpoint, values_gate_point_column e c p]

/-- (4) HONEST PROVER ONLY.
`IntegratedTerminalChain.honest_gate_terminal_matches_claim` (403-416) with
`alphaMatches` DISCHARGED. -/
theorem honest_gate_terminal_matches_claim_derived (hash : Hash) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (c : Verifier.Config) (p : Verifier.Proof)
    (pre : List Verifier.CoupledMessage) (mLog gLast : List Verifier.Ext3)
    (gates : List Gates.GateInfo) (s t : GateTerminalBinding.ProverState)
    (k : GateTerminalBinding.Cells)
    (hderiv : DerivedInitial hash e c p)
    (hr : GateChainResidue hash e decode c p pre mLog gLast gates s t k) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p =
        Verifier.mul k.eq.toVerifier gate ∧
      GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig c) gates
          (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
          (gateAlphaElement hash c p)
          (OuterRound.lift (IntegratedTerminalChain.lastGateChallenge e c p pre mLog gLast))
          s.tables 1 = some (Verifier.derivedRounds e c p).gateClaim ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p =
        (Verifier.derivedRounds e c p).gateClaim :=
  IntegratedTerminalChain.honest_gate_terminal_matches_claim e decode c p pre mLog gLast gates s t k
    (gateAlphaElement hash c p) (gateChainHypotheses_of_derived hash e decode c p pre mLog gLast
      gates s t k hderiv hr)

/-! ### 5.5 The shorter observation list -/

/-- THE NEW OBSERVATION LIST. `IntegratedTerminalChain.ObservationOnly` has
twelve conjuncts:

    chain, configurationHash, envelope, deployment, shape,
    logTau, gateTau, logIndex, gateIndex, whir, sevenChallenges, normShape

This structure is that list with `logTau`, `gateTau` and `sevenChallenges`
DELETED — all three are now consequences of the derivation
(`derived_log_tau_length`, `derived_gate_tau_length`,
`derived_seven_challenges`). Nine conjuncts remain. `normShape` below is still
the FULL `Norm.shapeValid`; its tau-length conjunct is separately available
from `derived_norm_shape_valid` but is not factored out of this structure.
Diff this definition against `ObservationOnly` field by field. -/
structure ObservationOnlyDerived (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) : Prop where
  chain : chain = pin.chainId
  configurationHash : e.configurationHash c = pin.configDigest
  envelope : Verifier.envelope c = true
  deployment : e.deploymentValid c = true
  shape : Verifier.shape pin c p = true
  logIndex : (Verifier.derivedIndices e c p).log.length = c.indexBits
  gateIndex : (Verifier.derivedIndices e c p).gate.length = c.indexBits
  whir : Verifier.verifyWhir (Integrated.modelEngine e decode)
    (Verifier.derivedContext (Integrated.modelEngine e decode) c p) p = true
  normShape : Norm.shapeValid c (Norm.challengesFromInitial (e.initialTranscript c p))
    (Verifier.normTerminalInput p) (Verifier.derivedRounds e c p).logPoint = true

theorem observationOnly_of_derived (hash : Hash) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) (hderiv : DerivedInitial hash e c p)
    (o : ObservationOnlyDerived e decode pin chain c p) :
    IntegratedTerminalChain.ObservationOnly e decode pin chain c p :=
  { chain := o.chain, configurationHash := o.configurationHash, envelope := o.envelope,
    deployment := o.deployment, shape := o.shape,
    logTau := derived_log_tau_length hash e c p hderiv,
    gateTau := derived_gate_tau_length hash e c p hderiv,
    logIndex := o.logIndex, gateIndex := o.gateIndex, whir := o.whir,
    sevenChallenges := derived_seven_challenges hash e c p hderiv,
    normShape := o.normShape }

/-- (4) HONEST PROVER ONLY. The full glue theorem
`IntegratedTerminalChain.honest_prover_passes_deterministic_checks` (658-680)
with `NormTerminalProvenance.challenges`, `GateChainHypotheses.alphaMatches` and
the `logTau` / `gateTau` / `sevenChallenges` observation conjuncts DISCHARGED.
The only transcript premise left is `DerivedInitial` (the engine's initial hook
IS the source derivation) plus the identification of the prover's challenge
record with the derived one. No converse: nothing says an accepted proof came
from such a prover, and nothing here depends on any property of `hash`. -/
theorem honest_prover_passes_deterministic_checks_derived (hash : Hash) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (t : Tables) (pr : Prepared) (gates : List (List Verifier.Ext3))
    (constants extra : List Verifier.Ext3) (pairs : List (Nat × Nat × Verifier.Base))
    (v' : Verifier.RoundState) (s' : ProverState)
    (sent : List (List Element)) (chals : List Element)
    (hderiv : DerivedInitial hash e c p) (hch : pr.challenges = logChallenges hash c p)
    (hrun : OuterClaimChain.honestRun e.commitRound (Verifier.start (e.initialTranscript c p))
      (initialState t pr) gates = .ok (v', s'))
    (hext : intoProofAndPoint s' = .ok (sent, chals))
    (hhon : IntegratedTerminalChain.HonestNormProver c t pr gates constants pairs)
    (hnr : NormProvenanceResidue c p pr gates constants extra s'.tables sent chals)
    (pre : List Verifier.CoupledMessage) (mLog gLast : List Verifier.Ext3)
    (gateInfos : List Gates.GateInfo) (gs gt : GateTerminalBinding.ProverState)
    (k : GateTerminalBinding.Cells)
    (hgr : GateChainResidue hash e decode c p pre mLog gLast gateInfos gs gt k)
    (cols : Fin 5 → List (List Element))
    (ho : IntegratedTerminalChain.HonestOpenings c p (Verifier.derivedRounds e c p)
      (Verifier.derivedIndices e c p) cols)
    (obs : ObservationOnlyDerived e decode pin chain c p) :
    (∃ norm, Integrated.normResult (Integrated.modelEngine e decode) c p = some norm) ∧
    (∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate) ∧
    (∀ i : Fin 5, OpenedClaimFold.CellOpensFullTable
      (Verifier.derivedContext (Integrated.modelEngine e decode) c p) i.val (OpenedClaimFold.cellPoint i)
      (cols i) (OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds e c p) i))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2)) ∧
    IntegratedTerminalChain.solidityOrderChecks (Integrated.modelEngine e decode) pin chain c p ∧
    Verifier.verify (Integrated.modelEngine e decode) pin chain c p = .ok () ∧
    Integrated.verify e decode pin chain c p = .ok () :=
  IntegratedTerminalChain.honest_prover_passes_deterministic_checks e decode pin chain c p t pr
    gates constants extra pairs v' s' sent chals hrun hext
    { toHonestNormProver := hhon
      toNormTerminalProvenance :=
        normTerminalProvenance_of_derived hash e c p pr gates constants extra s'.tables sent chals
          hderiv hch hnr }
    pre mLog gLast gateInfos gs gt k (gateAlphaElement hash c p)
    (gateChainHypotheses_of_derived hash e decode c p pre mLog gLast gateInfos gs gt k hderiv hgr)
    cols ho (observationOnly_of_derived hash e decode pin chain c p hderiv obs)

/-! ## 6. (5) A concrete instance, for every hash

The adopted `Integrated.exampleEngine` uses a constant stand-in
`initialObservation`, so it cannot satisfy `DerivedInitial`; the concrete
instance below therefore uses `OuterInitial.withInitial hash e`, which by
construction does, on the adopted `OuterAdapter.fixtureConfig` /
`fixtureProof` (one coupled round, one index coordinate, `degreeBits = 1`).
Every statement is universally quantified over `hash` and over the engine
whose remaining hooks are unconstrained. -/
namespace Example

open OuterAdapter

def engineOf (hash : Hash) (e : Verifier.Engine) : Verifier.Engine :=
  OuterInitial.withInitial hash e

theorem fixture_derived (hash : Hash) (e : Verifier.Engine) :
    DerivedInitial hash (engineOf hash e) fixtureConfig fixtureProof := rfl

/-- The checked source-order derivation succeeds on the fixture for every hash,
and the executed prefix's initial component is the very transcript
`engineOf hash e` observes. -/
theorem fixture_execution_matches_engine (hash : Hash) (e : Verifier.Engine) :
    ∃ result, execute hash fixtureConfig fixtureProof = some result ∧
      result.initial = (engineOf hash e).initialTranscript fixtureConfig fixtureProof := by
  obtain ⟨result, hres, hini, _, _, _, _⟩ := ordinary_prefix_for_every_hash hash
  exact ⟨result, hres, hini⟩

/-- (1) on the fixture. -/
theorem fixture_challenges (hash : Hash) (e : Verifier.Engine) :
    Norm.challengesFromInitial ((engineOf hash e).initialTranscript fixtureConfig fixtureProof)
      = logChallenges hash fixtureConfig fixtureProof :=
  challenges_from_initial_is_derived hash _ _ _ (fixture_derived hash e)

/-- (2) on the fixture: the three column/alpha discharges. -/
theorem fixture_columns (hash : Hash) (e : Verifier.Engine) :
    values (logTauColumn hash fixtureConfig fixtureProof)
        = (logChallenges hash fixtureConfig fixtureProof).tau ∧
    values (gateTauColumn hash fixtureConfig fixtureProof)
        = ((engineOf hash e).initialTranscript fixtureConfig fixtureProof).gateTau ∧
    (gateAlphaElement hash fixtureConfig fixtureProof).toVerifier
        = ((engineOf hash e).initialTranscript fixtureConfig fixtureProof).gateAlpha ∧
    values (gatePointColumn (engineOf hash e) fixtureConfig fixtureProof)
        = (Verifier.derivedRounds (engineOf hash e) fixtureConfig fixtureProof).gatePoint :=
  ⟨values_log_tau_column hash fixtureConfig fixtureProof,
   values_gate_tau_column hash _ _ _ (fixture_derived hash e),
   gate_alpha_element_matches hash _ _ _ (fixture_derived hash e),
   values_gate_point_column _ _ _⟩

/-- (3) on the fixture: the three deleted observation conjuncts hold. -/
theorem fixture_observations (hash : Hash) (e : Verifier.Engine) :
    ((engineOf hash e).initialTranscript fixtureConfig fixtureProof).logChallenges.length = 7 ∧
    ((engineOf hash e).initialTranscript fixtureConfig fixtureProof).logTau.length = 1 ∧
    ((engineOf hash e).initialTranscript fixtureConfig fixtureProof).gateTau.length = 1 :=
  ⟨derived_seven_challenges hash _ _ _ (fixture_derived hash e),
   derived_log_tau_length hash _ _ _ (fixture_derived hash e),
   derived_gate_tau_length hash _ _ _ (fixture_derived hash e)⟩

/-- Both derived columns have the fixture's `degreeBits = 1` width. -/
theorem fixture_column_widths (hash : Hash) :
    (logTauColumn hash fixtureConfig fixtureProof).length = 1 ∧
    (gateTauColumn hash fixtureConfig fixtureProof).length = 1 :=
  derived_column_lengths hash fixtureConfig fixtureProof

end Example

end Audit.Wire3.TranscriptProvenance
