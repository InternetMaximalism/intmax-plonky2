import Audit.Wire3.InstalledWhirParse
import Audit.Wire3.PinnedWhirProfile
import Audit.Wire3.InstalledWhirTail

/-!
# Concrete SUCCEEDING executions of the installed WHIR parse and tail

## What this module does

Every concrete installed-level evaluation in the adopted tree is NEGATIVE:
`InstalledWhirTail.example_empty_hints_fail_the_concrete_tail` (`tailRun … =
none`), `installed_engine_is_not_blind`, and
`InstalledWhirParse.example_concrete_parse_rejects_the_empty_transcript`.  Every
`tailRun`/`installedTail`/`prefixRun` SUCCESS in those two modules is a
hypothesis, or an existential conclusion gated on acceptance.  This module
supplies concrete successes, at two claim arities:

* THREE claims -- `installed_tail_succeeds_on_a_concrete_transcript`,
  `witness_verify_whir_is_true`;
* SIX claims, the deployed arity of `Verifier.expectedClaims` --
  `configured_six_claim_execution_example`,
  `installed_tail_succeeds_at_a_six_claim_context`, `six_verify_whir_is_true`;
* the six-claim context is a context the outer verifier DERIVES
  (`six_context_is_the_derived_context_of_the_installed_engine`), so
  `installed_whir_gate_is_true_at_its_own_derived_context` is the verifier's own
  WHIR gate returning `true`, not a check at a hand-supplied context;
* and `installed_whir_pair_accepts_a_full_verification` -- `Verifier.verify …
  = .ok ()` with `parseWhir` AND `whirTail` both the adopted concrete installs.

## What it is NOT -- read this before quoting anything above

**The hash is a toy.**  Everything runs at `InstalledWhirTail.exampleHash`, the
constant `fun _ => Spongefish.zeroDigest` (`the_witness_hash_is_constant`,
`the_witness_hash_ignores_every_input`).  At this hash the extra 72 claim bytes
of the six-claim source cannot shift the sponge digest.  The WHIR profile is a
toy too: `WhirConfigured.exampleNoRounds` has no intermediate round and sets
every proof-of-work threshold to `Spongefish.maxCounter`, whereas the deployed
`PinnedWhirProfile.canonicalRow10` / `canonicalRow21` have real rounds and a
real `finalPowThreshold` (`the_witness_profile_is_not_the_deployed_shape`).
Nothing here is a statement about the deployed hash, the deployed profile, or
the deployed system's soundness.

**The accepting configuration is `Verifier.testConfig`, not
`DerivedAcceptance.derivedConfig`.**  `testConfig` packs ONE variable
(`degreeBits = 1`, `indexBits = 0`); `derivedConfig` packs twenty-one
(`the_accepting_configuration_is_not_the_derived_one`).  A witness at the latter
needs a twenty-one-variable WHIR profile and its own transcript, and that is NOT
constructed here.

**The accepting engine is `sixEngine`, NOT `ExplicitEngine.explicitEngine`.**
Four engine fields are still abstract.  `accepting_engine_field_ledger` lists
them: the accepting engine has `parseWhir`, `whirTail`, `commitRound`,
`sampleIndices`, `foldClaim`, `normEvaluation` and `eqEvaluation` concrete, but
`initialObservation`, `publicInputsHash`, `configurationHash` and
`deploymentValid` are `Verifier.testEngine`'s abstract observations.  **This is
the exact COMPLEMENT of the adopted `DerivedAcceptance`**, which has ten of
twelve fields concrete and the WHIR pair as the fixture's.  Neither module has
all twelve.

**The three-claim witness context is not a derived context.**  It carries three
claim cells (`witness_context_has_three_claim_cells`) where every derived
context carries six (`derived_contexts_have_six_claim_cells`), so
`witness_context_is_not_an_outer_derived_context`.  Only the SIX-claim context
is derived.

## A premise this module CORRECTS

It is natural to read `InstalledWhirTail.whirMask = [⟨31⟩]` (five checked cells)
as blocking reuse of the adopted three-claim examples, which run at `[⟨7⟩ ]`.
**It does not.**  `WhirInitial.readClaims` indexes a mask only at `0, …,
expected.length - 1`, and at 0, 1, 2 the bytes 31 and 7 agree bit for bit.
`configured_run_mask_congruent` proves the general fact -- the mask enters
`WhirConfigured.run` ONLY through `WhirParameters.checkBound`'s length guard and
through `readClaims` -- and `the_two_masks_agree_below_three` discharges its
hypothesis.  The real obstruction was the CLAIM ARITY, and
`configured_six_claim_execution_example` removes it by exhibiting a six-claim
source read under the deployed mask with all five bound cells genuinely
compared.

## The `thash` question, decided explicitly

A WHIR-complete instance at a DERIVED context must be `thash`-dependent:
`WhirInitial.readClaims` rejects unless the transcript's encoded claims equal
`OpeningBinding.unmask ctx.expectedClaims`, and those five values are the
`Connections.packedFold` values at `Verifier.derivedIndices`, which depend on
`thash`.  **Both sides of that trade are taken here, in separate theorems, and
each says which.**

* `witness_verify_whir_is_true` and `six_verify_whir_is_true` supply the context
  EXPLICITLY, and so keep a universal quantifier over the base engine `e`, the
  gate decoder `gdec` AND the transcript hash `thash`.
* `six_context_is_the_derived_context_of_the_installed_engine`,
  `installed_whir_gate_is_true_at_its_own_derived_context` and
  `installed_whir_pair_accepts_a_full_verification` buy a DERIVED context and
  pay the quantifier: `thash` is INSTANTIATED at
  `InstalledRoundCommit.toyHash`.  `gdec` stays quantified in the first two.

## Byte-level executions

Two are proved here by `rfl`: the six-claim WHIR run
(`configured_six_claim_execution_example`) and the full verification
(`installed_whir_pair_accepts_a_full_verification`).  Both carry
`set_option maxRecDepth 8192` and `set_option maxHeartbeats 1000000`, the
smallest powers that work, narrowed to the single declaration -- adopted
practice, which uses `maxRecDepth 65536` for the comparable theorems.  The
three-claim results need no `set_option`: they cite the adopted
`WhirConfigured.configured_zero_intermediate_round_execution_example` as a black
box.  No option that weakens checking is used anywhere.
-/

namespace Audit.Wire3.WhirTailWitness

open Spongefish (Hash Digest)

/-! ## The mask is not read beyond the claim list -/

theorem read_claims_mask_congruent (hash : Hash) (source m n : Spongefish.Bytes) :
    ∀ (expected : List Verifier.Ext3) (i : Nat),
      (∀ k, k < expected.length →
        (WhirInitial.isChecked m (i + k) ↔ WhirInitial.isChecked n (i + k))) →
      ∀ s : Spongefish.State,
        WhirInitial.readClaims hash source m i expected s =
          WhirInitial.readClaims hash source n i expected s := by
  intro expected
  induction expected with
  | nil => intro i _ s; rfl
  | cons e rest ih =>
      intro i h s
      have h0 : WhirInitial.isChecked m i ↔ WhirInitial.isChecked n i := by
        simpa using h 0 (by simp)
      have hr : ∀ k, k < rest.length →
          (WhirInitial.isChecked m (i + 1 + k) ↔ WhirInitial.isChecked n (i + 1 + k)) := by
        intro k hk
        have := h (k + 1) (by simpa using Nat.succ_lt_succ hk)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      unfold WhirInitial.readClaims
      cases hp : Spongefish.proverExt3 hash s source with
      | none => simp [hp]
      | some pair =>
          obtain ⟨actual, next⟩ := pair
          simp only [hp, Option.bind_some]
          exact if_congr (and_congr_left' h0) rfl (by rw [ih (i + 1) hr next])

theorem phase_initial_mask_congruent (hash : Hash) (source : Spongefish.Bytes)
    (p : WhirInitial.Params) (roots : List Digest) (expected : List Verifier.Ext3)
    (m n : Spongefish.Bytes)
    (h : ∀ k, k < expected.length → (WhirInitial.isChecked m k ↔ WhirInitial.isChecked n k))
    (s : Spongefish.State) :
    WhirInitial.phaseInitial hash source p roots expected m s =
      WhirInitial.phaseInitial hash source p roots expected n s := by
  unfold WhirInitial.phaseInitial
  simp only [read_claims_mask_congruent hash source m n expected 0 (by simpa using h)]

theorem prefix_run_mask_congruent (hash : Hash) (source : Spongefish.Bytes)
    (p : WhirInitial.Params) (roots : List Digest) (expected : List Verifier.Ext3)
    (m n : Spongefish.Bytes)
    (h : ∀ k, k < expected.length → (WhirInitial.isChecked m k ↔ WhirInitial.isChecked n k))
    (count threshold : Nat) (s : Spongefish.State) :
    WhirPrefix.run hash source p roots expected m count threshold s =
      WhirPrefix.run hash source p roots expected n count threshold s := by
  unfold WhirPrefix.run
  rw [phase_initial_mask_congruent hash source p roots expected m n h s]

theorem run_prefix_mask_congruent (hash : Hash) (source hints : Spongefish.Bytes)
    (p : WhirInitial.Params) (roots : List Digest) (expected : List Verifier.Ext3)
    (m n : Spongefish.Bytes)
    (h : ∀ k, k < expected.length → (WhirInitial.isChecked m k ↔ WhirInitial.isChecked n k))
    (count threshold : Nat) (s : Spongefish.State)
    (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams)) :
    WhirTail.runPrefix hash source hints p roots expected m count threshold s rounds =
      WhirTail.runPrefix hash source hints p roots expected n count threshold s rounds := by
  unfold WhirTail.runPrefix
  rw [prefix_run_mask_congruent hash source p roots expected m n h count threshold s]

theorem whir_tail_run_mask_congruent (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Spongefish.Bytes)
    (initial : WhirInitial.Params) (roots : List Digest) (expected : List Verifier.Ext3)
    (m n : Spongefish.Bytes)
    (h : ∀ k, k < expected.length → (WhirInitial.isChecked m k ↔ WhirInitial.isChecked n k))
    (initialCount initialThreshold : Nat)
    (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams))
    (p : WhirTail.Params) :
    WhirTail.run hash protocolId sessionId instanceBytes source hints initial roots expected m
        initialCount initialThreshold rounds p =
      WhirTail.run hash protocolId sessionId instanceBytes source hints initial roots expected n
        initialCount initialThreshold rounds p := by
  unfold WhirTail.run
  simp only [run_prefix_mask_congruent hash source hints initial roots expected m n h]

/-- **The deployed five-cell mask and a shorter mask agree whenever they agree
on every index the claim list actually reaches.**  `WhirConfigured.run` reads
the mask only through `WhirParameters.checkBound`'s length guard and through
`WhirInitial.readClaims`, and `readClaims` indexes it only at `0, …,
expected.length - 1`. -/
theorem configured_run_mask_congruent (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Spongefish.Bytes)
    (p : WhirParameters.Params) (roots : List Digest) (expected : List Verifier.Ext3)
    (m n : Spongefish.Bytes) (hlen : m.length = n.length)
    (h : ∀ k, k < expected.length → (WhirInitial.isChecked m k ↔ WhirInitial.isChecked n k)) :
    WhirConfigured.run hash protocolId sessionId instanceBytes source hints p roots expected m =
      WhirConfigured.run hash protocolId sessionId instanceBytes source hints p roots expected n := by
  unfold WhirConfigured.run
  rw [hlen]
  cases WhirParameters.checkBound p roots.length expected.length n.length with
  | none => rfl
  | some forms =>
      exact whir_tail_run_mask_congruent hash protocolId sessionId instanceBytes source hints
        (WhirParameters.initialParams p forms) roots expected m n h p.initialSumcheckRounds
        p.initialSumcheckPowThreshold (WhirConfigured.phasePairs (WhirConfigured.initialOpen p) p.rounds)
        (WhirConfigured.finalParams p)

/-! ## The two masks -/

theorem deployed_mask_and_three_cell_mask_have_the_same_length :
    InstalledWhirTail.whirMask.length = ([⟨7, by decide⟩] : Spongefish.Bytes).length := rfl

theorem deployed_mask_checks_two_more_cells :
    WhirInitial.isChecked InstalledWhirTail.whirMask 3 ∧
    WhirInitial.isChecked InstalledWhirTail.whirMask 4 ∧
    ¬ WhirInitial.isChecked ([⟨7, by decide⟩] : Spongefish.Bytes) 3 ∧
    ¬ WhirInitial.isChecked ([⟨7, by decide⟩] : Spongefish.Bytes) 4 := by decide

theorem the_two_masks_agree_below_three (k : Nat) (hk : k < 3) :
    WhirInitial.isChecked InstalledWhirTail.whirMask k ↔
      WhirInitial.isChecked ([⟨7, by decide⟩] : Spongefish.Bytes) k := by
  interval_cases k <;> decide

/-! ## The witness -/

def witnessTranscript : Verifier.Bytes :=
  WhirFinalSpongefish.fromTranscriptBytes (WhirTail.exampleInitialSource ++ WhirTail.exampleExt 1)

def witnessHints : Verifier.Bytes :=
  WhirFinalSpongefish.fromTranscriptBytes WhirTail.exampleBaseHints

def witnessContext : Verifier.WhirContext :=
  { protocolId := []
    sessionId := []
    parameters := []
    numVariables := 1
    roots := [0, 0, 0]
    points := [[Arithmetic.zero]]
    expectedClaims := [some ⟨Arithmetic.one, by decide⟩, some Verifier.zero, some Verifier.zero] }

theorem witness_roots_are_the_three_zero_digests :
    witnessContext.roots.map InstalledWhirTail.rootDigest =
      List.replicate 3 Spongefish.zeroDigest := by rfl

theorem witness_claims_are_the_adopted_example_claims :
    OpeningBinding.unmask witnessContext.expectedClaims = WhirTail.exampleClaims := rfl

theorem witness_context_parameters_are_the_adopted_profile :
    InstalledWhirTail.contextParams WhirConfigured.exampleNoRounds witnessContext =
      WhirConfigured.exampleNoRounds := rfl

theorem witness_tail_run_unfolds :
    InstalledWhirTail.tailRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
        witnessContext witnessTranscript witnessHints =
      WhirConfigured.run InstalledWhirTail.exampleHash [] [] []
        (WhirTail.exampleInitialSource ++ WhirTail.exampleExt 1) WhirTail.exampleBaseHints
        WhirConfigured.exampleNoRounds (List.replicate 3 Spongefish.zeroDigest)
        WhirTail.exampleClaims InstalledWhirTail.whirMask := by
  have h1 : InstalledWhirTail.outerBytes witnessTranscript =
      WhirTail.exampleInitialSource ++ WhirTail.exampleExt 1 :=
    WhirFinalSpongefish.transcript_bytes_roundtrip _
  have h2 : InstalledWhirTail.outerBytes witnessHints = WhirTail.exampleBaseHints :=
    WhirFinalSpongefish.transcript_bytes_roundtrip _
  have h3 : InstalledWhirTail.outerBytes witnessContext.protocolId = [] := rfl
  have h4 : InstalledWhirTail.outerBytes witnessContext.sessionId = [] := rfl
  unfold InstalledWhirTail.tailRun
  rw [h1, h2, h3, h4, witness_roots_are_the_three_zero_digests,
    witness_claims_are_the_adopted_example_claims, witness_context_parameters_are_the_adopted_profile]

theorem witness_tail_run_is_the_adopted_execution :
    InstalledWhirTail.tailRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
        witnessContext witnessTranscript witnessHints =
      WhirConfigured.run (fun _ => Spongefish.zeroDigest) [] [] []
        (WhirTail.exampleInitialSource ++ WhirTail.exampleExt 1) WhirTail.exampleBaseHints
        WhirConfigured.exampleNoRounds (List.replicate 3 Spongefish.zeroDigest)
        WhirTail.exampleClaims [⟨7, by decide⟩] := by
  rw [witness_tail_run_unfolds]
  exact configured_run_mask_congruent InstalledWhirTail.exampleHash [] [] []
    (WhirTail.exampleInitialSource ++ WhirTail.exampleExt 1) WhirTail.exampleBaseHints
    WhirConfigured.exampleNoRounds (List.replicate 3 Spongefish.zeroDigest)
    WhirTail.exampleClaims InstalledWhirTail.whirMask [⟨7, by decide⟩] rfl
    (fun k hk => the_two_masks_agree_below_three k (by simpa using hk))

theorem option_is_some_of_map_eq_some {a b : Type} (o : Option a) (f : a → b) (v : b)
    (h : o.map f = some v) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some x => rfl

/-- **RUNG 1.**  A concrete context, transcript and hint string on which the
installed concrete WHIR tail SUCCEEDS.  This is the POSITIVE counterpart of the
adopted `InstalledWhirTail.example_empty_hints_fail_the_concrete_tail`, not its
exact dual: that theorem runs at a six-cell context derived by the outer
verifier, this one at an explicitly supplied three-cell context
(`witness_context_is_not_an_outer_derived_context`).  The hash is the toy
constant `InstalledWhirTail.exampleHash`, not a deployed hash. -/
theorem installed_tail_succeeds_on_a_concrete_transcript :
    (InstalledWhirTail.tailRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      witnessContext witnessTranscript witnessHints).isSome = true := by
  rw [witness_tail_run_is_the_adopted_execution]
  exact option_is_some_of_map_eq_some _ _ _
    WhirConfigured.configured_zero_intermediate_round_execution_example

/-- The installed `whirTail` engine field returns `true` at the witness. -/
theorem installed_tail_returns_true_on_a_concrete_transcript (parsed : Verifier.ParsedWhir) :
    InstalledWhirTail.installedTail InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      witnessContext witnessTranscript witnessHints parsed = true := by
  rw [InstalledWhirTail.installed_tail_true_iff]
  exact ⟨rfl, installed_tail_succeeds_on_a_concrete_transcript⟩

/-! ## Rung 2: the concrete parse on the same bytes -/

theorem list_of_length_three {a : Type} (xs : List a) (h : xs.length = 3) :
    ∃ x y z, xs = [x, y, z] := by
  match xs, h with
  | [x, y, z], _ => exact ⟨x, y, z, rfl⟩

theorem witness_prefix_bound_is_some :
    (WhirParameters.checkBound
      (InstalledWhirTail.contextParams WhirConfigured.exampleNoRounds witnessContext)
      (InstalledWhirParse.parseRoots witnessContext).length
      (InstalledWhirParse.parseClaims witnessContext).length
      InstalledWhirTail.whirMask.length).isSome = true := by
  rw [witness_context_parameters_are_the_adopted_profile]
  exact WhirConfigured.ordinary_profiles_and_parameter_checks_succeed.2.2.1

theorem witness_prefix_run_is_some :
    (InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      witnessContext witnessTranscript witnessHints).isSome = true := by
  have h := installed_tail_succeeds_on_a_concrete_transcript
  rw [InstalledWhirParse.tail_run_factors_through_prefix_run] at h
  cases hp : InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash
      WhirConfigured.exampleNoRounds witnessContext witnessTranscript witnessHints with
  | none => rw [hp] at h; simp at h
  | some s => rfl

/-- **RUNG 2.**  The installed concrete parse succeeds on the witness bytes and
its projection carries the context's own roots, in both copies, and claims that
satisfy the outer verifier's mask. -/
theorem witness_parse_matches_the_context :
    ∃ s, InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash
        WhirConfigured.exampleNoRounds witnessContext witnessTranscript witnessHints = some s ∧
      (InstalledWhirParse.parsedOf s).actualRoots = witnessContext.roots ∧
      (InstalledWhirParse.parsedOf s).boundRoots = witnessContext.roots ∧
      Verifier.claimsMatch witnessContext.expectedClaims
        (InstalledWhirParse.parsedOf s).claims = true := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp witness_prefix_run_is_some
  obtain ⟨forms, hforms⟩ := Option.isSome_iff_exists.mp witness_prefix_bound_is_some
  refine ⟨s, hs, ?_⟩
  unfold InstalledWhirParse.prefixRun at hs
  rw [hforms] at hs
  have h1 := WhirTail.prefix_success_retains_actual_pair (h := hs)
  obtain ⟨after, hpi, _⟩ := WhirPrefix.successful_prefix_is_one_execution (h := h1.1)
  have hall := WhirInitial.initial_all_roots_and_checked_claims (h := hpi)
  have hroot : (InstalledWhirParse.parsedOf s).actualRoots = witnessContext.roots := by
    show s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.root) = _
    have hm : s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.root) =
        (s.origin.initial.commitments.map (·.root)).map WhirTail.rootWord := by
      simp [List.map_map, Function.comp_def]
    rw [hm, hall.1]
    rfl
  have hbound : (InstalledWhirParse.parsedOf s).boundRoots = witnessContext.roots := by
    show s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.boundRoot) = _
    have hm : s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.boundRoot) =
        (s.origin.initial.commitments.map (·.boundRoot)).map WhirTail.rootWord := by
      simp [List.map_map, Function.comp_def]
    rw [hm, hall.2.1]
    rfl
  refine ⟨hroot, hbound, ?_⟩
  have hlen : s.origin.initial.evaluations.length = 3 := hall.2.2.1
  have hc0 := hall.2.2.2.1 0 (by decide) (by decide)
  have hc1 := hall.2.2.2.1 1 (by decide) (by decide)
  have hc2 := hall.2.2.2.1 2 (by decide) (by decide)
  obtain ⟨x, y, z, hev⟩ := list_of_length_three _ hlen
  rw [hev] at hc0 hc1 hc2
  have hcl : (InstalledWhirParse.parsedOf s).claims =
      InstalledWhirParse.parseClaims witnessContext := by
    show s.origin.initial.evaluations = _
    rw [hev]
    simp only [List.getD] at hc0 hc1 hc2
    simp only [InstalledWhirParse.parseClaims, OpeningBinding.unmask, witnessContext] at hc0 hc1 hc2 ⊢
    simp_all
  rw [hcl]
  exact OpeningBinding.claimsMatch_unmask _

/-! ## Rung 2 at the engine: `verifyWhir` is `true` with both WHIR guards concrete -/

def witnessProof : Verifier.Proof :=
  { Integrated.exampleProof with
      whirTranscript := witnessTranscript, whirHints := witnessHints }

/-- **RUNG 2, AT THE ENGINE.**  `Verifier.verifyWhir` returns `true` for an
engine whose `parseWhir` AND `whirTail` are both the adopted concrete installs,
at the toy constant hash `InstalledWhirTail.exampleHash`.  The base engine, the
gate decoder and the transcript hash are QUANTIFIED: the context is supplied
explicitly, so nothing here depends on them. -/
theorem witness_verify_whir_is_true (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (thash : Transcript.Hash) :
    Verifier.verifyWhir (InstalledWhirParse.installedParseEngine e gdec
      InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds thash)
      witnessContext witnessProof = true := by
  rw [InstalledWhirParse.verify_whir_concrete_iff]
  obtain ⟨s, hs, hr, hb, hc⟩ := witness_parse_matches_the_context
  exact ⟨s, hs, hr, hb, hc, installed_tail_returns_true_on_a_concrete_transcript _⟩

/-! ## Non-vacuity: the accepting execution really reads the bytes -/

/-- The accepting run consumes 336 transcript bytes and 72 hint bytes -- it is
not an empty or short-circuited execution. -/
theorem witness_execution_consumes_the_bytes :
    (InstalledWhirTail.tailRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      witnessContext witnessTranscript witnessHints).map
      (fun r => (r.retained.current.completedRounds, r.rows.vector.length,
        r.finalSumcheck.cursor.transcriptPos, r.rows.afterRows.hintPos)) = some (0, 1, 336, 72) := by
  rw [witness_tail_run_is_the_adopted_execution]
  exact WhirConfigured.configured_zero_intermediate_round_execution_example

theorem witness_transcript_is_not_empty : witnessTranscript  ≠ [] := by
  intro h
  have h1 : InstalledWhirTail.outerBytes witnessTranscript =
      WhirTail.exampleInitialSource ++ WhirTail.exampleExt 1 :=
    WhirFinalSpongefish.transcript_bytes_roundtrip _
  rw [h] at h1
  simp [InstalledWhirTail.outerBytes, WhirFinalSpongefish.toTranscriptBytes,
    WhirTail.exampleInitialSource] at h1

/-! ## The ledger: what this witness is NOT -/

/-- Every context the outer verifier derives carries SIX claim cells, five bound
and one free (`Verifier.expectedClaims`). -/
theorem derived_contexts_have_six_claim_cells (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) :
    (Verifier.derivedContext e c p).expectedClaims.length = 6 := by
  simp [Verifier.derivedContext, Verifier.whirContext, Verifier.expectedClaims]

theorem witness_context_has_three_claim_cells :
    witnessContext.expectedClaims.length = 3 := rfl

/-- **THE OBSTRUCTION TO RUNG 3, AS A THEOREM.**  The witness context is not any
context the outer verifier derives, for any engine, configuration or proof: it
carries three claim cells and every derived context carries six.  So rungs 1 and
2 above do NOT compose with `DerivedAcceptance`'s accepting instance. -/
theorem witness_context_is_not_an_outer_derived_context (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) :
    witnessContext  ≠ Verifier.derivedContext e c p := by
  intro h
  have h6 : witnessContext.expectedClaims.length = 6 := by
    rw [h]; exact derived_contexts_have_six_claim_cells e c p
  rw [witness_context_has_three_claim_cells] at h6
  exact absurd h6 (by decide)

/-- At six claim cells the deployed mask and the three-cell mask genuinely
differ, so `configured_run_mask_congruent` does NOT transport the adopted
three-claim executions to a six-cell context. -/
theorem the_two_masks_do_not_agree_below_six :
    ¬ (∀ k, k < 6 → (WhirInitial.isChecked InstalledWhirTail.whirMask k ↔
      WhirInitial.isChecked ([⟨7, by decide⟩] : Spongefish.Bytes) k)) := by
  intro h
  exact deployed_mask_checks_two_more_cells.2.2.1
    ((h 3 (by decide)).mp deployed_mask_checks_two_more_cells.1)

/-- The zero-intermediate-round profile the witness runs at admits no six-claim
context at all: with one evaluation point it can carry only one linear form, and
`WhirParameters.checkForms` demands a second point at `numForms = 2`.  A
six-claim witness therefore needs a DIFFERENT profile (the adopted
`InstalledWhirTail.exampleVk` is one) and, with it, a different transcript. -/
theorem the_witness_profile_admits_no_six_claim_context :
    WhirParameters.checkBound WhirConfigured.exampleNoRounds 3 6 1 = none := by decide

/-- The adopted six-claim profile does pass parameter admission, so the residue
at six claims is the SOURCE BYTES, not the parameters. -/
theorem the_six_claim_profile_passes_parameter_admission :
    (WhirParameters.checkBound InstalledWhirTail.exampleVk 3 6 1).isSome = true :=
  InstalledWhirTail.example_profile_is_the_split_route.2.2

/-- A toy hash is a toy hash: the witness runs at a CONSTANT `Spongefish.Hash`. -/
theorem the_witness_hash_is_constant :
    InstalledWhirTail.exampleHash = fun _ => Spongefish.zeroDigest := rfl

/-- At this hash every input collides, so absorbing 72 extra zero claim bytes
cannot move the sponge digest. -/
theorem the_witness_hash_ignores_every_input (a b : Spongefish.Bytes) :
    InstalledWhirTail.exampleHash a = InstalledWhirTail.exampleHash b := by
  rw [the_witness_hash_is_constant]

/-- And a toy profile is a toy profile.  The witness profile has no
intermediate round and disables every proof-of-work gate by setting each
threshold to `Spongefish.maxCounter`; the deployed canonical rows have real
rounds and a real `finalPowThreshold`. -/
theorem the_witness_profile_is_not_the_deployed_shape :
    WhirConfigured.exampleNoRounds.numRounds = 0 ∧
    WhirConfigured.exampleNoRounds.finalPowThreshold = Spongefish.maxCounter ∧
    WhirConfigured.exampleNoRounds.initialSumcheckPowThreshold = Spongefish.maxCounter ∧
    WhirConfigured.exampleNoRounds.finalSumcheckPowThreshold = Spongefish.maxCounter ∧
    PinnedWhirProfile.canonicalRow10.numRounds = 1 ∧
    PinnedWhirProfile.canonicalRow10.finalPowThreshold ≠ Spongefish.maxCounter ∧
    PinnedWhirProfile.canonicalRow21.numRounds = 4 ∧
    PinnedWhirProfile.canonicalRow21.finalPowThreshold ≠ Spongefish.maxCounter :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide⟩

/-! ## Rung 1 at SIX claim cells: the deployed claim arity

The three-claim witness above leaves the deployed mask's cells 3 and 4 unread.
This section closes that: a source string carrying SIX claims, read under the
deployed `InstalledWhirTail.whirMask` with cells 0-4 all genuinely compared.
The profile is `WhirConfigured.exampleNoRounds` again -- the context's own second
evaluation point is what lifts it to the two linear forms six claims demand, so
`InstalledWhirTail.contextParams` alone supplies the six-claim profile. -/

def sixVk : WhirParameters.Params :=
  { WhirConfigured.exampleNoRounds with evaluationPoint2 := [Arithmetic.zero] }

theorem six_profile_passes_parameter_admission :
    WhirParameters.checkBound sixVk 3 6 1 =
      some [[Verifier.zero], [Verifier.zero]] := by decide

/-- 192 zero bytes for the three commitments, then SIX zero claims (144 bytes),
then one initial-sumcheck message and the final vector. -/
def sixSource : Spongefish.Bytes :=
  List.replicate 336 Spongefish.zeroByte ++ WhirTail.examplePair 1 0 ++ WhirTail.exampleExt 1

def sixTranscript : Verifier.Bytes := WhirFinalSpongefish.fromTranscriptBytes sixSource

def sixHints : Verifier.Bytes :=
  WhirFinalSpongefish.fromTranscriptBytes WhirTail.exampleBaseHints

/-- Five bound cells and one free cell -- exactly the shape of
`Verifier.expectedClaims`, and with the bound cells all zero, exactly the shape
`DerivedAcceptance.derived_expected_claims_are_zero` produces. -/
def sixContext : Verifier.WhirContext :=
  { protocolId := []
    sessionId := []
    parameters := []
    numVariables := 1
    roots := [0, 0, 0]
    points := [[Arithmetic.zero], [Arithmetic.zero]]
    expectedClaims := [some Verifier.zero, some Verifier.zero, some Verifier.zero,
                       some Verifier.zero, some Verifier.zero, none] }

theorem six_context_has_six_claim_cells : sixContext.expectedClaims.length = 6 := rfl

theorem six_context_claim_cells_are_the_verifier_shape :
    sixContext.expectedClaims.take 5 = List.replicate 5 (some Verifier.zero) ∧
      sixContext.expectedClaims.getLast? = some none := ⟨rfl, rfl⟩

theorem six_context_claims_unmask_to_zero :
    OpeningBinding.unmask sixContext.expectedClaims = List.replicate 6 Verifier.zero := rfl

theorem six_context_roots_are_the_three_zero_digests :
    sixContext.roots.map InstalledWhirTail.rootDigest =
      List.replicate 3 Spongefish.zeroDigest := by rfl

theorem six_context_parameters_are_the_six_claim_profile :
    InstalledWhirTail.contextParams WhirConfigured.exampleNoRounds sixContext = sixVk := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **THE SIX-CLAIM EXECUTION.**  A concrete successful `WhirConfigured.run` at
SIX claims under the deployed five-cell mask, on 408 transcript bytes and 72
hint bytes, with exact EOF on both streams.  The trace matches the adopted
three-claim examples field for field.  Toy constant hash, toy profile. -/
theorem configured_six_claim_execution_example :
    (WhirConfigured.run (fun _ => Spongefish.zeroDigest) [] [] [] sixSource
      WhirTail.exampleBaseHints sixVk (List.replicate 3 Spongefish.zeroDigest)
      (List.replicate 6 Verifier.zero) InstalledWhirTail.whirMask).map
      (fun r => (r.retained.current.completedRounds, r.rows.vector.length,
        r.finalSumcheck.finalRandomness.length, r.finalSumcheck.cursor.transcriptPos,
        r.rows.afterRows.hintPos)) = some (0, 1, 0, 408, 72) := by rfl

theorem six_tail_run_unfolds :
    InstalledWhirTail.tailRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
        sixContext sixTranscript sixHints =
      WhirConfigured.run InstalledWhirTail.exampleHash [] [] [] sixSource
        WhirTail.exampleBaseHints sixVk (List.replicate 3 Spongefish.zeroDigest)
        (List.replicate 6 Verifier.zero) InstalledWhirTail.whirMask := by
  have h1 : InstalledWhirTail.outerBytes sixTranscript = sixSource :=
    WhirFinalSpongefish.transcript_bytes_roundtrip _
  have h2 : InstalledWhirTail.outerBytes sixHints = WhirTail.exampleBaseHints :=
    WhirFinalSpongefish.transcript_bytes_roundtrip _
  have h3 : InstalledWhirTail.outerBytes sixContext.protocolId = [] := rfl
  have h4 : InstalledWhirTail.outerBytes sixContext.sessionId = [] := rfl
  unfold InstalledWhirTail.tailRun
  rw [h1, h2, h3, h4, six_context_roots_are_the_three_zero_digests,
    six_context_claims_unmask_to_zero, six_context_parameters_are_the_six_claim_profile]

/-- **THE HEADLINE.**  The installed concrete WHIR tail SUCCEEDS at a context
with the deployed SIX-cell claim shape, all five bound cells compared against
the transcript under `InstalledWhirTail.whirMask`.  This is the positive
counterpart, at the deployed claim arity, of the adopted
`InstalledWhirTail.example_empty_hints_fail_the_concrete_tail`.  The hash and
the profile are toys; see the module header. -/
theorem installed_tail_succeeds_at_a_six_claim_context :
    (InstalledWhirTail.tailRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      sixContext sixTranscript sixHints).isSome = true := by
  rw [six_tail_run_unfolds]
  exact option_is_some_of_map_eq_some _ _ _ configured_six_claim_execution_example

theorem installed_tail_returns_true_at_a_six_claim_context (parsed : Verifier.ParsedWhir) :
    InstalledWhirTail.installedTail InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      sixContext sixTranscript sixHints parsed = true := by
  rw [InstalledWhirTail.installed_tail_true_iff]
  exact ⟨rfl, installed_tail_succeeds_at_a_six_claim_context⟩

/-! ### The six-claim parse, and `verifyWhir = true` at the deployed claim arity -/

theorem list_of_length_six {a : Type} (xs : List a) (h : xs.length = 6) :
    ∃ x0 x1 x2 x3 x4 x5, xs = [x0, x1, x2, x3, x4, x5] := by
  match xs, h with
  | [x0, x1, x2, x3, x4, x5], _ => exact ⟨x0, x1, x2, x3, x4, x5, rfl⟩

theorem six_prefix_bound_is_some :
    (WhirParameters.checkBound
      (InstalledWhirTail.contextParams WhirConfigured.exampleNoRounds sixContext)
      (InstalledWhirParse.parseRoots sixContext).length
      (InstalledWhirParse.parseClaims sixContext).length
      InstalledWhirTail.whirMask.length).isSome = true := by
  rw [six_context_parameters_are_the_six_claim_profile]
  exact congrArg Option.isSome six_profile_passes_parameter_admission

theorem six_prefix_run_is_some :
    (InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      sixContext sixTranscript sixHints).isSome = true := by
  have h := installed_tail_succeeds_at_a_six_claim_context
  rw [InstalledWhirParse.tail_run_factors_through_prefix_run] at h
  cases hp : InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash
      WhirConfigured.exampleNoRounds sixContext sixTranscript sixHints with
  | none => rw [hp] at h; simp at h
  | some s => rfl

/-- **RUNG 2 AT SIX CLAIMS.**  The installed concrete parse succeeds on the same
bytes and its projection carries the context's own roots in both copies and
claims that satisfy the outer verifier's five-cell mask. -/
theorem six_parse_matches_the_context :
    ∃ s, InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash
        WhirConfigured.exampleNoRounds sixContext sixTranscript sixHints = some s ∧
      (InstalledWhirParse.parsedOf s).actualRoots = sixContext.roots ∧
      (InstalledWhirParse.parsedOf s).boundRoots = sixContext.roots ∧
      Verifier.claimsMatch sixContext.expectedClaims
        (InstalledWhirParse.parsedOf s).claims = true := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp six_prefix_run_is_some
  obtain ⟨forms, hforms⟩ := Option.isSome_iff_exists.mp six_prefix_bound_is_some
  refine ⟨s, hs, ?_⟩
  unfold InstalledWhirParse.prefixRun at hs
  rw [hforms] at hs
  have h1 := WhirTail.prefix_success_retains_actual_pair (h := hs)
  obtain ⟨after, hpi, _⟩ := WhirPrefix.successful_prefix_is_one_execution (h := h1.1)
  have hall := WhirInitial.initial_all_roots_and_checked_claims (h := hpi)
  have hroot : (InstalledWhirParse.parsedOf s).actualRoots = sixContext.roots := by
    show s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.root) = _
    have hm : s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.root) =
        (s.origin.initial.commitments.map (·.root)).map WhirTail.rootWord := by
      simp [List.map_map, Function.comp_def]
    rw [hm, hall.1]
    rfl
  have hbound : (InstalledWhirParse.parsedOf s).boundRoots = sixContext.roots := by
    show s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.boundRoot) = _
    have hm : s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.boundRoot) =
        (s.origin.initial.commitments.map (·.boundRoot)).map WhirTail.rootWord := by
      simp [List.map_map, Function.comp_def]
    rw [hm, hall.2.1]
    rfl
  refine ⟨hroot, hbound, ?_⟩
  have hlen : s.origin.initial.evaluations.length = 6 := hall.2.2.1
  have hc0 := hall.2.2.2.1 0 (by decide) (by decide)
  have hc1 := hall.2.2.2.1 1 (by decide) (by decide)
  have hc2 := hall.2.2.2.1 2 (by decide) (by decide)
  have hc3 := hall.2.2.2.1 3 (by decide) (by decide)
  have hc4 := hall.2.2.2.1 4 (by decide) (by decide)
  obtain ⟨x0, x1, x2, x3, x4, x5, hev⟩ := list_of_length_six _ hlen
  rw [hev] at hc0 hc1 hc2 hc3 hc4
  show Verifier.claimsMatch sixContext.expectedClaims s.origin.initial.evaluations = true
  rw [hev]
  simp only [List.getD] at hc0 hc1 hc2 hc3 hc4
  simp only [InstalledWhirParse.parseClaims, OpeningBinding.unmask, sixContext] at hc0 hc1 hc2 hc3 hc4
  simp_all [Verifier.claimsMatch, sixContext]

def sixProof : Verifier.Proof :=
  { Verifier.testProof with whirTranscript := sixTranscript, whirHints := sixHints }

/-- **RUNG 2 AT THE ENGINE, AT SIX CLAIMS.**  `Verifier.verifyWhir` is `true`
with `parseWhir` ∧ `whirTail` both the adopted concrete installs, at the
deployed six-cell claim shape.  `e`, `gdec` and `thash` remain quantified. -/
theorem six_verify_whir_is_true (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (thash : Transcript.Hash) :
    Verifier.verifyWhir (InstalledWhirParse.installedParseEngine e gdec
      InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds thash)
      sixContext sixProof = true := by
  rw [InstalledWhirParse.verify_whir_concrete_iff]
  obtain ⟨s, hs, hr, hb, hc⟩ := six_parse_matches_the_context
  exact ⟨s, hs, hr, hb, hc, installed_tail_returns_true_at_a_six_claim_context _⟩

theorem six_execution_consumes_the_bytes :
    (InstalledWhirTail.tailRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      sixContext sixTranscript sixHints).map
      (fun r => (r.retained.current.completedRounds, r.rows.vector.length,
        r.finalSumcheck.finalRandomness.length, r.finalSumcheck.cursor.transcriptPos,
        r.rows.afterRows.hintPos)) = some (0, 1, 0, 408, 72) := by
  rw [six_tail_run_unfolds]
  exact configured_six_claim_execution_example

/-! ### Rung 3 step: the six-claim context IS a context the outer verifier derives

`Verifier.testConfig` has `degreeBits = 1`, `indexBits = 0`, empty
`whirProtocolId` / `whirSessionId` / `whirEncoding`, and `Verifier.testProof`
pins all three roots at `Verifier.testRoot = 0`.  At that configuration the
outer verifier derives EXACTLY `sixContext`. -/

def sixEngine (gdec : Integrated.DecodeGates) : Verifier.Engine :=
  InstalledWhirParse.installedParseEngine Verifier.testEngine gdec
    InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds InstalledRoundCommit.toyHash

/-- **THE SIX-CLAIM CONTEXT IS A DERIVED CONTEXT** -- the exact positive
counterpart, at six cells, of `witness_context_is_not_an_outer_derived_context`
for the three-cell witness.  `thash` is INSTANTIATED here at
`InstalledRoundCommit.toyHash`: this is where the universal quantifier over the
transcript hash is spent. -/
theorem six_context_is_the_derived_context_of_the_installed_engine
    (gdec : Integrated.DecodeGates) :
    Verifier.derivedContext (sixEngine gdec) Verifier.testConfig sixProof = sixContext := by rfl

theorem six_context_is_the_derived_context_of_the_abstract_engine :
    Verifier.derivedContext Verifier.testEngine Verifier.testConfig sixProof = sixContext := by rfl

/-- **THE OUTER VERIFIER'S OWN WHIR GATE RETURNS `true`.**  Not at a supplied
context: at the context the engine ITSELF derives from this configuration and
this proof, with `parseWhir` and `whirTail` both the adopted concrete installs.
Toy hash, toy profile, `thash` instantiated -- see the module header. -/
theorem installed_whir_gate_is_true_at_its_own_derived_context
    (gdec : Integrated.DecodeGates) :
    Verifier.verifyWhir (sixEngine gdec)
      (Verifier.derivedContext (sixEngine gdec) Verifier.testConfig sixProof) sixProof = true := by
  rw [six_context_is_the_derived_context_of_the_installed_engine gdec]
  exact six_verify_whir_is_true Verifier.testEngine gdec InstalledRoundCommit.toyHash

/-- The derived context really does carry the outer verifier's six-cell claim
shape, three roots and two packed points. -/
theorem six_derived_context_has_the_verifier_shape (gdec : Integrated.DecodeGates) :
    (Verifier.derivedContext (sixEngine gdec) Verifier.testConfig sixProof).roots.length = 3 ∧
    (Verifier.derivedContext (sixEngine gdec) Verifier.testConfig sixProof).points.length = 2 ∧
    (Verifier.derivedContext (sixEngine gdec) Verifier.testConfig sixProof).expectedClaims.length
      = 6 :=
  Verifier.context_three_roots_two_points_six_claims _ _ _ _ _

/-! ### Rung 3 at `Verifier.testConfig`: a full verification with the WHIR pair concrete -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **NOT `DerivedAcceptance.derivedConfig`, NOT `ExplicitEngine.explicitEngine`.**
`Verifier.verify` accepts at `Verifier.testConfig` (one variable) on `sixEngine`
(four fields still `Verifier.testEngine`'s abstract observations), with
`parseWhir` and `whirTail` BOTH the adopted concrete installs, on a proof whose
WHIR transcript really executes (408 bytes, 72 hint bytes, exact EOF on both).
Toy constant hash, toy no-round profile.  See `accepting_engine_field_ledger`
and `the_accepting_configuration_is_not_the_derived_one` before quoting this
as an explicit-engine result. -/
theorem installed_whir_pair_accepts_a_full_verification :
    Verifier.verify (sixEngine Integrated.exampleDecoder)
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig sixProof = .ok () := by rfl

/-- What the accepting engine actually carries: eight fields concrete, four
still `Verifier.testEngine`'s abstract observations.  This is the COMPLEMENT of
`DerivedAcceptance`, which has ten concrete fields but the fixture WHIR pair. -/
theorem accepting_engine_field_ledger (gdec : Integrated.DecodeGates) :
    (sixEngine gdec).parseWhir = InstalledWhirParse.concreteParseWhir
      InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds ∧
    (sixEngine gdec).whirTail = InstalledWhirTail.installedTail
      InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds ∧
    (sixEngine gdec).commitRound =
      InstalledRoundCommit.concreteCommitRound InstalledRoundCommit.toyHash ∧
    (sixEngine gdec).sampleIndices =
      InstalledIndexSampler.concreteSampleIndices InstalledRoundCommit.toyHash ∧
    (sixEngine gdec).foldClaim = Connections.packedFold ∧
    (sixEngine gdec).normEvaluation = Norm.normEvaluation ∧
    (sixEngine gdec).eqEvaluation = Norm.eqEvaluation ∧
    (sixEngine gdec).initialObservation = Verifier.testEngine.initialObservation ∧
    (sixEngine gdec).publicInputsHash = Verifier.testEngine.publicInputsHash ∧
    (sixEngine gdec).configurationHash = Verifier.testEngine.configurationHash ∧
    (sixEngine gdec).deploymentValid = Verifier.testEngine.deploymentValid :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- And the configuration this runs at is NOT the one `DerivedAcceptance` uses:
`Verifier.testConfig` packs one variable, `DerivedAcceptance.derivedConfig`
packs twenty-one.  A witness at the latter needs a twenty-one-variable WHIR
profile and its own transcript; that is NOT constructed here. -/
theorem the_accepting_configuration_is_not_the_derived_one :
    Verifier.testConfig.degreeBits + Verifier.testConfig.indexBits = 1 ∧
    sixVk.numVariables = 1 ∧
    sixContext.numVariables = 1 :=
  ⟨rfl, rfl, rfl⟩

end Audit.Wire3.WhirTailWitness





