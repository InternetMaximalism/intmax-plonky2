import Audit.Wire3.InstalledIndexSampler

/-!
# Installing the concrete coupled-round transcript commit into the outer engine

## The gap this module closes

`Verifier.Engine.commitRound : Verifier.CommitRound`
(`Bytes -> Nat -> List Ext3 -> List Ext3 -> RoundChallenges`, Verifier.lean 349)
is an OBSERVATION on every installed engine of the adopted tree, and
`Verifier.derivedRounds e c p = runRounds e.commitRound (start (e.initialTranscript c p))
(p.logRounds.zip p.gateRounds)` (Verifier.lean 386-387) is the only place the
coupled outer-sumcheck challenges come from. `InstalledWhirTail.installedEngine`
installs the WHIR tail, `InstalledIndexSampler.installedSamplerEngine` installs
the constituent-index sampler, and BOTH keep `commitRound` abstract -- both
record it in their "still an OBSERVATION" list, and
`InstalledIndexSampler.installed_sampler_keeps_transcript_and_rounds` says
`commitRound = e.commitRound` by `rfl`.

Four adopted residues lean on that field being the REAL commit:

* `OuterAdapter.CommitAgrees thash e.commitRound` is a HYPOTHESIS wherever the
  adopted checked execution is used --
  `OuterAdapter.execute_matches_existing_derived_context` (OuterAdapter.lean
  511-518) and, riding on it, `InstalledIndexSampler`'s
  `installed_sampler_matches_the_checked_execution` and
  `decoded_snapshot_exists_under_checked_execution`. In particular
  `InstalledIndexSampler`'s decode hypothesis
  `OuterAdapter.decode (derivedRounds e c p).transcript = some st` -- carried by
  every one of its section-5 and section-7 statements -- is discharged ONLY
  under `CommitAgrees` plus a successful `OuterAdapter.execute`.
* "the round digests are chained after the prefix" is DOCUMENTED FOR THE
  CONCRETE ENGINE ONLY: `GatePointZeroCheck`'s RES-4 (GatePointZeroCheck.lean
  186-189), `JointChallengeSpace.Draw`'s `outerLog` / `outerGate` constructors
  ("THE LABEL IS DOCUMENTED, NOT DERIVED", JointChallengeSpace.lean 177-190) and
  `JointChallengeSpace.schedule_position_injective`'s own caveat, and
  `InstalledIndexSampler.indexSchedulePosition`'s block label.
* `ConditionalSoundness.logLaneOf` / `gateLaneOf` (ConditionalSoundness.lean
  482-490) take each round's challenge from the ABSTRACT `e.commitRound`, so the
  whole union-bound apparatus above them is about an opaque function.
* `JointChallengeSpace.DrawEncodesRun`'s `logDrawn` / `gateDrawn` fields
  "constrain only the VALUE" (JointChallengeSpace.lean 920-932), because the
  counters `0` and `3` are not derivable for a free `commitRound`.

The adopted model ALREADY carries the concrete commit. `OuterAdapter.commitChecked`
(OuterAdapter.lean 103-109) decodes the 40-byte snapshot and runs
`Transcript.coupledRound` (Transcript.lean 225-230), which is
`Transcript.commitRound` (Transcript.lean 218-223) followed by six squeezes;
`OuterAdapter.roundResult` (OuterAdapter.lean 97-101) is its total form, and
`OuterAdapter.round_result_exact_counter_inputs` (OuterAdapter.lean 136-140)
pins the two challenges at counters `0` and `3` of the round's commit digest --
the same pair the adopted
`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`
(OuterChallenge.lean 301-308) pins. **This module reuses them; it defines no new
serialization.**

## The absorb/squeeze order this installs, with source citations

Rust, `transcript_v2.rs::commit_coupled_outer_round` (transcript_v2.rs 133-147),
called by the VERIFIER once per round at `verifier_v2.rs` 281-302:

1. `domain_separate(DOMAIN_OUTER_SUMCHECK_ROUND_V2)` -- transcript_v2.rs 139;
   the label is `"outer-sumcheck-lockstep-round-v3"`
   (generated/mle_whir_v2.rs 97), framed with `TAG_DOMAIN_V2 = 1`
   (generated/mle_whir_v2.rs 44).
2. `absorb_bytes(&(round_index as u64).to_le_bytes())` -- transcript_v2.rs 140,
   tag `TAG_BYTES_V2 = 2` (generated/mle_whir_v2.rs 45), payload the EIGHT
   little-endian bytes of the round index.
3. `absorb_ext3_vec(log_non_constant)` then `absorb_ext3_vec(gate_non_constant)`
   -- transcript_v2.rs 141-142, tag `TAG_EXT3_VEC_V2 = 6`
   (generated/mle_whir_v2.rs 49), payload `len_u64_le || (c0 || c1 || c2)*`
   (transcript_v2.rs 87-96). BOTH lanes' messages are absorbed before any
   squeeze.
4. `domain_separate(DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2)` -- transcript_v2.rs
   143, label `"outer-sumcheck-lockstep-challenges-v3"`
   (generated/mle_whir_v2.rs 98). This absorb RESETS the squeeze counter to `0`
   (transcript_v2.rs 43-53; `Transcript.absorb`, Transcript.lean 134-135).
5. `squeeze_ext3` for the LOG challenge, then `squeeze_ext3` for the GATE
   challenge -- transcript_v2.rs 144-146. Each is three `squeeze_challenge`
   calls at consecutive counters (transcript_v2.rs 98-121), so the log challenge
   uses counters `0,1,2` and the gate challenge counters `3,4,5` of the digest
   produced by step 4.

Solidity, `TranscriptV2.sol::commitCoupledOuterRound` (TranscriptV2.sol
247-261): the identical five frames (254-258) and the identical two
`squeezeExt3` calls (259-260), preceded by the explicit
`roundIndex > type(uint64).max` rejection (253) that the model's
`Transcript.coupledRound` bound reproduces. It is called once per round from
`OuterLogupExt3Verifier._verifyCoupledSumchecksUnchecked`
(OuterLogupExt3Verifier.sol 274-278), which stores `roundChallenges.log` into
`logPoint[roundIndex]` and `roundChallenges.gate` into `gatePoint[roundIndex]`
(OuterLogupExt3Verifier.sol 280-283) -- the two lists the model's
`Verifier.roundStep` appends to (Verifier.lean 174-178).

## What is installed and what is still an OBSERVATION

INSTALLED (concrete, executable): `foldClaim`, `normEvaluation`, `eqEvaluation`,
`gateEvaluation` (from `Integrated.modelEngine`), `whirTail` (from
`InstalledWhirTail`), `sampleIndices` (from `InstalledIndexSampler`) and, new
here, `commitRound`.

STILL OBSERVATIONS, unchanged and opaque: `initialObservation` (hence
`Engine.initialTranscript`), `publicInputsHash`, `parseWhir`,
`configurationHash` and `deploymentValid`. `deploymentValid` can be made
concrete by composing with `PinnedWhirProfile.pinnedEngine` (PinnedWhirProfile.lean
289-291), which replaces it by `pinnedDeployment`; NOTHING BELOW DEPENDS ON THAT,
and this module does not import it. `initialObservation` is the one that still
matters here: it produces the 40-byte snapshot the FIRST round decodes, so the
statements below carry either
`e.initialTranscript c p = OuterInitial.toInitial (OuterInitial.derive thash c (statement p))`
-- the adopted `TranscriptProvenance.DerivedInitial` shape, and exactly the
hypothesis `OuterAdapter.execute_matches_existing_derived_context` already takes
-- or, more weakly, that the initial snapshot decodes.

## What CHANGES when `commitRound` is installed

`InstalledWhirTail` and `InstalledIndexSampler` could both say
`derivedRounds (installedX e ...) c p = derivedRounds e c p` by `rfl`. **THAT IS
NO LONGER TRUE HERE**, and it is the whole point: `derivedRounds` is
`runRounds e.commitRound ...`, so replacing `commitRound` changes it. Concretely:

* Adopted theorems QUANTIFIED over an arbitrary `Verifier.Engine` -- every
  statement of `InstalledWhirTail`, `InstalledIndexSampler`,
  `ConditionalSoundness`, `JointChallengeSpace`, `TranscriptProvenance`,
  `CommitmentOrder` and `GatePointZeroCheck` -- apply to this engine VERBATIM,
  because `installedRoundEngine e gdec hash wp thash` IS
  `InstalledIndexSampler.installedSamplerEngine (recommitted e thash) gdec hash wp thash`
  (`installed_round_is_installed_sampler_of_recommitted`, `rfl`). Instantiate
  them at `e := recommitted e thash`, never at the original `e`.
* Adopted theorems whose CONTENT is `derivedRounds (installedX e ...) c p =
  derivedRounds e c p` -- the second conjunct of
  `InstalledWhirTail.installed_engine_keeps_transcript` and of
  `InstalledIndexSampler.installed_sampler_keeps_transcript_and_rounds` -- still
  hold, but with `recommitted e thash` on the right-hand side, NOT with `e`; that
  is the fifth conjunct of `installed_round_keeps_initial_transcript`. The
  initial-transcript conjunct of both is unaffected.

## The failure branch of the concrete commit, and what `indexBits = 0` costs

`concreteCommitRound` totalises the adopted checked commit over the snapshot
decode; on a snapshot that does NOT decode it returns `failedRound`. Four facts
about that branch, stated here because the short reading of section 2 oversells
it:

(i) `Verifier.envelope` ADMITS `indexBits = 0`. Its last two lines are
`c.indexBits ≤ 8 ∧ width c ≤ 2 ^ c.indexBits` and
`(c.indexBits = 0 ∨ 2 ^ (c.indexBits - 1) < width c)` (Verifier.lean 104-105),
which together say that `indexBits = 0` holds exactly when `width c = 1`
(`envelope_admits_index_bits_zero_iff_width_one`). The ADOPTED
`Verifier.testConfig` is such a config and PASSES the envelope --
`Verifier.envelope Verifier.testConfig = true`
(`example_test_config_is_admitted_with_zero_index_bits`). `PinnedWhirProfile`
does not exclude the degenerate width either: its
`minProfileVariables = 1` (PinnedWhirProfile.lean 188).

(ii) On an initial snapshot that does NOT decode, the engine still runs one
round per element of `p.logRounds.zip p.gateRounds`, each with challenge
`Verifier.zero`, transcript `[]`, and -- through the installed sampler -- index
lanes `⟨[], []⟩`. `failed_path_pads_points_with_zero` proves the run-level shape:
both point lists are the incoming ones padded with one `Verifier.zero` per
round, and the final snapshot still does not decode. The ONLY rejection route
the adopted tree offers on that path is
`InstalledIndexSampler.malformed_snapshot_fails_the_index_length_guard`
(InstalledIndexSampler.lean 706-720), and it REQUIRES `c.indexBits ≠ 0`. At
`c.indexBits = 0` the verifier's index-length guard (Verifier.lean 420-421) is
SATISFIED by the empty lanes
(`failed_path_passes_index_guard_at_index_bits_zero`), so neither this module nor
`InstalledIndexSampler` rejects the failed path for such a config. Whether
`Verifier.verify` rejects it at some LATER check is not decided here.

(iii) REACHABILITY. Under `hi` -- the initial observation is the adopted
`OuterInitial.derive` -- together with `c.degreeBits ≤ 13`, EVERY snapshot of the
run decodes (`start_snapshot_decodes`, then `concrete_run_snapshot_decodes`), and
acceptance implies `c.degreeBits ≤ 13` because `Verifier.envelope` demands it
(Verifier.lean 98). Every theorem of this module that mentions the installed
engine carries both `hi` and `hdb`, so on every one of them the failure branch is
DEAD. It is live only for an engine whose `initialObservation` is NOT the derived
one -- the adopted `Verifier.testEngine` is exactly such an engine, which is why
the probe of (ii) is stated about it.

(iv) On a non-decoding snapshot `concreteCommitRound thash raw i log gate` is
`failedRound`, which is `Verifier.testEngine.commitRound raw i log gate`
ARGUMENT FOR ARGUMENT. So
`example_concrete_commit_is_not_the_abstract_observation` is a separation on
DECODABLE inputs ONLY; its own docstring repeats this.

## The sibling that removes the remaining initial-transcript observation

The sibling candidate `InstalledInitialTranscript` installs `initialObservation`
(as `fun c s => OuterInitial.toInitial (OuterInitial.derive thash c s)`) and
`publicInputsHash` on the same `InstalledIndexSampler.installedSamplerEngine`
base. Composing the two installers makes the `hi` hypothesis of sections 6-8
hold by `rfl` over that base -- exactly as `exampleBase` already does it here
with the adopted `OuterInitial.withInitial` -- and shrinks the OBSERVATION list
below to `parseWhir`, `configurationHash` and `deploymentValid`. That composition
is NOT performed here: the two candidates are independent, and the one-line glue
statement naming the composed engine is a LATER step.

## What is NOT proved

`hash` and `thash` are arbitrary deterministic functions. No hash security, no
collision resistance (`CommitmentOrder.TranscriptCollision` is always a
CONCLUSION here, never a hypothesis), no random-oracle property, no
Fiat--Shamir soundness, no WHIR/PCS soundness, no Rust/Yul/Solidity refinement.
The model is a manual reading of the sources cited above; `Verifier.verify` is a
manual success-boundary model, not an EVM exception-order refinement.

`JointChallengeSpace.DrawEncodesRun` remains a COORDINATE statement. Section 7
turns its `logDrawn` / `gateDrawn` counter LABELS into theorems for THIS engine
-- the values really are the reductions at counters `0` and `3` of the round's
own commit digest -- but it attaches no law to those reductions, and
`DrawEncodesRun` itself is unchanged: it still says only which point of
`JointSpace` one is looking at.

Half (B) of the Fiat--Shamir reading -- that the actual round draw is
DISTRIBUTED by the uniform law on the digest-triple space -- is NOT formalized,
here or anywhere in the adopted tree. Section 9's non-malleability results are
ORDERING and BINDING facts only.

Nothing here is the deployed system's soundness error. The wire-v3 WHIR profile
this models is the ~100-bit design point. No figure in this module is a security
level, and in particular nothing here says "125".
-/

namespace Audit.Wire3.InstalledRoundCommit

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The five frames of one coupled round -/

/-- The five frames the source absorbs for one coupled round, in source order:
the round domain separator, the eight little-endian bytes of the round index,
the two `TAG_EXT3_VEC_V2` message cells (log first, then gate), and the
challenge domain separator. This is `Transcript.commitRound` written as an
`OuterInitial.Message` list so that the adopted
`CommitmentOrder.absorb_messages_bind_or_collide` applies to it verbatim. -/
def roundFrames (i : Nat) (m : Verifier.CoupledMessage) : List OuterInitial.Message :=
  [OuterInitial.domainMessage "outer-sumcheck-lockstep-round-v3",
   ⟨2, Transcript.le 8 i⟩,
   ⟨6, OuterAdapter.encodedVec m.1⟩,
   ⟨6, OuterAdapter.encodedVec m.2⟩,
   OuterInitial.domainMessage "outer-sumcheck-lockstep-challenges-v3"]

theorem round_frame_count (i : Nat) (m : Verifier.CoupledMessage) :
    (roundFrames i m).length = 5 := rfl

/-- (1) The adopted `OuterAdapter.roundCommitted` IS the fold of those five
frames. Nothing is re-serialized: this is `rfl`. -/
theorem round_committed_is_the_frame_fold (thash : Transcript.Hash) (s : Transcript.State)
    (i : Nat) (m : Verifier.CoupledMessage) :
    OuterAdapter.roundCommitted thash s i m.1 m.2 =
      OuterInitial.absorbMessages thash s (roundFrames i m) := rfl

theorem round_frames_get_index (i : Nat) (m : Verifier.CoupledMessage) :
    (roundFrames i m).get? 1 = some ⟨2, Transcript.le 8 i⟩ := rfl
theorem round_frames_get_log_message (i : Nat) (m : Verifier.CoupledMessage) :
    (roundFrames i m).get? 2 = some ⟨6, OuterAdapter.encodedVec m.1⟩ := rfl
theorem round_frames_get_gate_message (i : Nat) (m : Verifier.CoupledMessage) :
    (roundFrames i m).get? 3 = some ⟨6, OuterAdapter.encodedVec m.2⟩ := rfl

/-- (1) The two domain separators bracket the block: no challenge is squeezed
between them, and the last one resets the squeeze counter to zero. -/
theorem round_frames_brackets (thash : Transcript.Hash) (s : Transcript.State) (i : Nat)
    (m : Verifier.CoupledMessage) :
    (roundFrames i m).get? 0 =
        some (OuterInitial.domainMessage "outer-sumcheck-lockstep-round-v3") ∧
    (roundFrames i m).get? 4 =
        some (OuterInitial.domainMessage "outer-sumcheck-lockstep-challenges-v3") ∧
    (OuterAdapter.roundCommitted thash s i m.1 m.2).counter = 0 :=
  ⟨rfl, rfl, rfl⟩

/-! ## 2. The concrete commit -/

/-- The `RoundChallenges` value the concrete commit returns when the incoming
40-byte snapshot is malformed: an EMPTY transcript snapshot and two ZERO
challenges. The empty snapshot does not decode
(`failed_round_snapshot_does_not_decode`), so every later round of the same run
fails the same way -- `failed_path_pads_points_with_zero` PROVES that, at the run
level: both point lists are padded with one `Verifier.zero` per remaining round
and the final snapshot does not decode either -- which makes the installed
sampler return empty index lanes.

WHAT IS AND IS NOT INVENTED. No fallback transcript STATE and no zero DIGEST is
invented: the snapshot is EMPTY, not a forged forty bytes. Two zero CHALLENGES
are, and they are precisely the pair the abstract
`Verifier.testEngine.commitRound` returns, so on this branch the concrete commit
and that observation agree argument for argument.

WHAT REJECTS IT, AND WHEN IT DOES NOT. `Verifier.verify` rejects with
`.configuration` through
`InstalledIndexSampler.malformed_snapshot_fails_the_index_length_guard`
(InstalledIndexSampler.lean 706-720) ONLY under `c.indexBits ≠ 0`. At
`c.indexBits = 0` -- which `Verifier.envelope` ADMITS, see
`envelope_admits_index_bits_zero_iff_width_one` and the adopted witness
`example_test_config_is_admitted_with_zero_index_bits` -- the empty lanes SATISFY
the guard (`failed_path_passes_index_guard_at_index_bits_zero`). Under the `hi`
and `c.degreeBits ≤ 13` hypotheses that every theorem of this module carries, the
branch is unreachable (`concrete_run_snapshot_decodes`). -/
def failedRound : Verifier.RoundChallenges := ⟨[], Verifier.zero, Verifier.zero⟩

theorem failed_round_snapshot_does_not_decode :
    OuterAdapter.decode failedRound.transcript = none :=
  OuterAdapter.decode_bad_length _ (by decide)

/-- **THE CONCRETE COMMIT.** The adopted checked commit
`OuterAdapter.commitChecked` -- `Transcript.commitRound` on the five frames of
section 1, then the two `OuterInitial.draw`s at counters `0` and `3` -- totalised
over the snapshot decode, exactly as
`InstalledIndexSampler.concreteSampleIndices` totalises the checked sampler.
On a decoding snapshot it is the adopted total `OuterAdapter.roundResult`; on a
malformed one it is `failedRound`. -/
def concreteCommitRound (thash : Transcript.Hash) : Verifier.CommitRound :=
  fun raw i log gate =>
    match OuterAdapter.decode raw with
    | some s => OuterAdapter.roundResult thash s i log gate
    | none => failedRound

theorem concrete_commit_on_decoded_snapshot (thash : Transcript.Hash) (raw : Verifier.Bytes)
    (s : Transcript.State) (i : Nat) (log gate : List Verifier.Ext3)
    (hd : OuterAdapter.decode raw = some s) :
    concreteCommitRound thash raw i log gate = OuterAdapter.roundResult thash s i log gate := by
  simp only [concreteCommitRound, hd]

theorem concrete_commit_rejects_malformed_snapshot (thash : Transcript.Hash)
    (raw : Verifier.Bytes) (i : Nat) (log gate : List Verifier.Ext3)
    (hd : OuterAdapter.decode raw = none) :
    concreteCommitRound thash raw i log gate = failedRound := by
  simp only [concreteCommitRound, hd]

/-- (2) **THE FAILED PATH, AT THE RUN LEVEL.** If the incoming snapshot does not
decode then neither does any later one, so every remaining round takes the
`failedRound` branch: both point lists are the incoming ones with one
`Verifier.zero` appended per round, and the run's final snapshot still does not
decode. This is the proof behind "every later round fails the same way" in the
docstring of `failedRound`, and it is what makes the installed sampler return
empty index lanes. -/
theorem failed_path_pads_points_with_zero (thash : Transcript.Hash) :
    ∀ (ms : List Verifier.CoupledMessage) (s : Verifier.RoundState),
      OuterAdapter.decode s.transcript = none →
      (Verifier.runRounds (concreteCommitRound thash) s ms).logPoint =
          s.logPoint ++ List.replicate ms.length Verifier.zero ∧
      (Verifier.runRounds (concreteCommitRound thash) s ms).gatePoint =
          s.gatePoint ++ List.replicate ms.length Verifier.zero ∧
      OuterAdapter.decode (Verifier.runRounds (concreteCommitRound thash) s ms).transcript = none
  | [], s, hd => ⟨by simp [Verifier.runRounds], by simp [Verifier.runRounds], hd⟩
  | m :: ms, s, hd => by
      have hstep : Verifier.roundStep (concreteCommitRound thash) s m =
          OuterAdapter.advance s m failedRound := by
        rw [← OuterAdapter.advance_is_existing_round_step,
          concrete_commit_rejects_malformed_snapshot thash _ _ _ _ hd]
      have hnext : OuterAdapter.decode
          (Verifier.roundStep (concreteCommitRound thash) s m).transcript = none := by
        rw [hstep]; exact failed_round_snapshot_does_not_decode
      obtain ⟨h1, h2, h3⟩ := failed_path_pads_points_with_zero thash ms _ hnext
      refine ⟨?_, ?_, h3⟩
      · show (Verifier.runRounds (concreteCommitRound thash)
            (Verifier.roundStep (concreteCommitRound thash) s m) ms).logPoint = _
        rw [h1, hstep]
        simp [OuterAdapter.advance, failedRound, List.replicate_succ, List.append_assoc]
      · show (Verifier.runRounds (concreteCommitRound thash)
            (Verifier.roundStep (concreteCommitRound thash) s m) ms).gatePoint = _
        rw [h2, hstep]
        simp [OuterAdapter.advance, failedRound, List.replicate_succ, List.append_assoc]

/-- (2) **THE ADOPTED ENVELOPE ADMITS A DEGENERATE `indexBits`.** Its last two
lines are `c.indexBits ≤ 8 ∧ width c ≤ 2 ^ c.indexBits` and
`(c.indexBits = 0 ∨ 2 ^ (c.indexBits - 1) < width c)` (Verifier.lean 104-105);
together with `0 < width c` they make `indexBits = 0` EQUIVALENT to the
degenerate constituent width `1`. So nothing in `Verifier.envelope` rules
`indexBits = 0` out, and the index-length guard it feeds is vacuous there. -/
theorem envelope_admits_index_bits_zero_iff_width_one (c : Verifier.Config)
    (he : Verifier.envelope c = true) :
    c.indexBits = 0 ↔ Verifier.width c = 1 := by
  simp only [Verifier.envelope, decide_eq_true_eq] at he
  obtain ⟨-, -, hw0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hle, hlast⟩ := he
  constructor
  · intro h0
    rw [h0, pow_zero] at hle
    omega
  · intro h1
    rcases hlast with h | h
    · exact h
    · rw [h1] at h
      have hp : 0 < 2 ^ (c.indexBits - 1) := Nat.pos_pow_of_pos _ (by norm_num)
      omega

/-- (2) The degenerate case is not hypothetical: the ADOPTED `Verifier.testConfig`
has `indexBits = 0`, `width = 1`, and passes `Verifier.envelope`. This is the
witness that makes the limitation recorded in the header's failure-branch section
real rather than notional. -/
theorem example_test_config_is_admitted_with_zero_index_bits :
    Verifier.testConfig.indexBits = 0 ∧ Verifier.envelope Verifier.testConfig = true ∧
    Verifier.width Verifier.testConfig = 1 := ⟨rfl, by decide, rfl⟩

/-- (2) **THE INSTALLED COMMIT IS THE ADOPTED CHECKED COMMIT** wherever the
latter succeeds, so the adopted
`OuterAdapter.execute_matches_existing_derived_context` applies to any engine
carrying it, with its `CommitAgrees` hypothesis DISCHARGED. -/
theorem concrete_commit_agrees (thash : Transcript.Hash) :
    OuterAdapter.CommitAgrees thash (concreteCommitRound thash) := by
  intro raw i log gate r h
  obtain ⟨s, hd, _, _, _, hr, _⟩ := OuterAdapter.commit_success_exact thash raw i log gate r h
  rw [concrete_commit_on_decoded_snapshot thash raw s i log gate hd]
  exact hr.symm

/-- The LOG challenge of a round, as the adopted three-digest reduction of
`OuterChallenge` at counter `0` of that round's commit digest. -/
def logChallengeOf (thash : Transcript.Hash) (d : Transcript.Digest) : Verifier.Ext3 :=
  (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash ⟨d, 0⟩)).toVerifier

/-- The GATE challenge of a round, the same reduction at counter `3`. -/
def gateChallengeOf (thash : Transcript.Hash) (d : Transcript.Digest) : Verifier.Ext3 :=
  (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash ⟨d, 3⟩)).toVerifier

/-- (2) The concrete commit's two challenges ARE those reductions, at counters
`0` and `3` of the digest that absorbed both messages, and the snapshot it
returns decodes back to that digest with counter `6`. -/
theorem concrete_commit_challenges (thash : Transcript.Hash) (raw : Verifier.Bytes)
    (s : Transcript.State) (i : Nat) (log gate : List Verifier.Ext3)
    (hd : OuterAdapter.decode raw = some s) :
    (concreteCommitRound thash raw i log gate).log =
        logChallengeOf thash (OuterAdapter.roundCommitted thash s i log gate).digest ∧
    (concreteCommitRound thash raw i log gate).gate =
        gateChallengeOf thash (OuterAdapter.roundCommitted thash s i log gate).digest ∧
    OuterAdapter.decode (concreteCommitRound thash raw i log gate).transcript =
        some ⟨(OuterAdapter.roundCommitted thash s i log gate).digest, 6⟩ := by
  rw [concrete_commit_on_decoded_snapshot thash raw s i log gate hd]
  exact ⟨rfl, rfl, OuterAdapter.round_result_snapshot_decodes thash s i log gate⟩

/-! ## 3. The engine with the commit installed -/

abbrev VkParams := InstalledIndexSampler.VkParams

/-- The outer engine with only `commitRound` replaced. Used to show that
installing the commit commutes with installing the tail and the sampler. -/
def recommitted (e : Verifier.Engine) (thash : Transcript.Hash) : Verifier.Engine :=
  { e with commitRound := concreteCommitRound thash }

/-- **THE ENGINE OF THIS MODULE.** `InstalledIndexSampler.installedSamplerEngine`
with the concrete coupled-round commit installed. `hash` is the WHIR/Merkle hash
and `thash` the outer transcript hash; in the source both are Keccak, but nothing
in the Lean model ties them, and both are arbitrary deterministic functions. -/
def installedRoundEngine (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) : Verifier.Engine :=
  { InstalledIndexSampler.installedSamplerEngine e gdec hash wp thash with
    commitRound := concreteCommitRound thash }

/-- (3) Installing the commit commutes with installing the tail and the sampler,
so EVERY adopted theorem quantified over an arbitrary `Verifier.Engine` applies
to this engine verbatim, with `e` replaced by `recommitted e thash`. -/
theorem installed_round_is_installed_sampler_of_recommitted (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) :
    installedRoundEngine e gdec hash wp thash =
      InstalledIndexSampler.installedSamplerEngine (recommitted e thash) gdec hash wp thash := rfl

/-- (3) **THE INITIAL TRANSCRIPT IS UNCHANGED, THE ROUNDS ARE NOT.**
`initialObservation` -- hence `Engine.initialTranscript` -- is untouched, so
every adopted statement about the initial challenge block still reads the same
observation. `derivedRounds` DOES change: it is `runRounds e.commitRound ...`,
and the fourth conjunct records what it changes INTO. The adopted
`derivedRounds (installedX e ...) c p = derivedRounds e c p` conjuncts of
`InstalledWhirTail.installed_engine_keeps_transcript` and
`InstalledIndexSampler.installed_sampler_keeps_transcript_and_rounds` therefore
hold for this engine only with `recommitted e thash` in place of `e`, which the
fifth conjunct states. -/
theorem installed_round_keeps_initial_transcript (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    (installedRoundEngine e gdec hash wp thash).initialObservation = e.initialObservation ∧
    (installedRoundEngine e gdec hash wp thash).initialTranscript c p =
      e.initialTranscript c p ∧
    (installedRoundEngine e gdec hash wp thash).commitRound = concreteCommitRound thash ∧
    Verifier.derivedRounds (installedRoundEngine e gdec hash wp thash) c p =
      Verifier.runRounds (concreteCommitRound thash)
        (Verifier.start (e.initialTranscript c p)) (p.logRounds.zip p.gateRounds) ∧
    Verifier.derivedRounds (installedRoundEngine e gdec hash wp thash) c p =
      Verifier.derivedRounds (recommitted e thash) c p :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- (3) The fields installed by the adopted modules are still installed, and the
five that remain OBSERVATIONS are still exactly `e`'s. -/
theorem installed_round_installed_and_observed_fields (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) :
    (installedRoundEngine e gdec hash wp thash).commitRound = concreteCommitRound thash ∧
    (installedRoundEngine e gdec hash wp thash).sampleIndices =
      InstalledIndexSampler.concreteSampleIndices thash ∧
    (installedRoundEngine e gdec hash wp thash).whirTail =
      InstalledWhirTail.installedTail hash wp ∧
    (installedRoundEngine e gdec hash wp thash).foldClaim = Connections.packedFold ∧
    (installedRoundEngine e gdec hash wp thash).initialObservation = e.initialObservation ∧
    (installedRoundEngine e gdec hash wp thash).publicInputsHash = e.publicInputsHash ∧
    (installedRoundEngine e gdec hash wp thash).parseWhir = e.parseWhir ∧
    (installedRoundEngine e gdec hash wp thash).configurationHash = e.configurationHash ∧
    (installedRoundEngine e gdec hash wp thash).deploymentValid = e.deploymentValid :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. The digest chain of a concrete run -/

/-- **THE CHAIN.** The commit digest of each round, in order: round `0`'s is the
five-frame fold onto the incoming state, and round `r + 1`'s is the five-frame
fold onto `⟨d_r, 6⟩` -- round `r`'s own digest, with the counter at `6` because
that round drew six scalars from it. This recursion IS the chaining statement;
`concrete_chain_step` is it as an equation. -/
def concreteChain (thash : Transcript.Hash) :
    Transcript.State → Nat → List Verifier.CoupledMessage → List Transcript.Digest
  | _, _, [] => []
  | st, i, m :: ms =>
      (OuterAdapter.roundCommitted thash st i m.1 m.2).digest ::
        concreteChain thash ⟨(OuterAdapter.roundCommitted thash st i m.1 m.2).digest, 6⟩ (i + 1) ms

/-- The transcript state a concrete run ends in: the incoming state when there
are no rounds, otherwise the last round's digest with counter `6`. -/
def concreteFinal (thash : Transcript.Hash) :
    Transcript.State → Nat → List Verifier.CoupledMessage → Transcript.State
  | st, _, [] => st
  | st, i, m :: ms =>
      concreteFinal thash
        ⟨(OuterAdapter.roundCommitted thash st i m.1 m.2).digest, 6⟩ (i + 1) ms

theorem concrete_chain_step (thash : Transcript.Hash) (st : Transcript.State) (i : Nat)
    (m : Verifier.CoupledMessage) (ms : List Verifier.CoupledMessage) :
    concreteChain thash st i (m :: ms) =
      (OuterAdapter.roundCommitted thash st i m.1 m.2).digest ::
        concreteChain thash
          ⟨(OuterAdapter.roundCommitted thash st i m.1 m.2).digest, 6⟩ (i + 1) ms := rfl

theorem concrete_chain_length (thash : Transcript.Hash) :
    ∀ (ms : List Verifier.CoupledMessage) (st : Transcript.State) (i : Nat),
      (concreteChain thash st i ms).length = ms.length
  | [], _, _ => rfl
  | _ :: ms, _, i => congrArg Nat.succ (concrete_chain_length thash ms _ (i + 1))

/-- (4) Round `r`'s digest, addressed directly: the five-frame fold of round
`r`'s own message pair onto `concreteFinal thash st i (ms.take r)`, the state
left by rounds `< r`. -/
theorem concrete_chain_get (thash : Transcript.Hash) :
    ∀ (ms : List Verifier.CoupledMessage) (st : Transcript.State) (i r : Nat)
      (hr : r < ms.length),
      (concreteChain thash st i ms).get? r =
        some (OuterAdapter.roundCommitted thash (concreteFinal thash st i (ms.take r)) (i + r)
          (ms.get ⟨r, hr⟩).1 (ms.get ⟨r, hr⟩).2).digest
  | [], _, _, _, hr => absurd hr (by simp)
  | _ :: _, _, i, 0, _ => by
      simp only [concreteChain, List.get?_cons_zero, List.take_zero, concreteFinal, Nat.add_zero]
      rfl
  | m :: ms, st, i, r + 1, hr => by
      have hr2 : r < ms.length := by simpa using hr
      have ih := concrete_chain_get thash ms
        ⟨(OuterAdapter.roundCommitted thash st i m.1 m.2).digest, 6⟩ (i + 1) r hr2
      simp only [concreteChain, List.get?_cons_succ, List.take_succ_cons, concreteFinal]
      rw [ih, show i + 1 + r = i + (r + 1) by omega]
      rfl

/-! ## 5. The concrete run: the rounds ARE the chain -/

theorem round_step_on_decoded_snapshot (thash : Transcript.Hash) (s : Verifier.RoundState)
    (st : Transcript.State) (m : Verifier.CoupledMessage)
    (hd : OuterAdapter.decode s.transcript = some st) :
    Verifier.roundStep (concreteCommitRound thash) s m =
      OuterAdapter.advance s m (OuterAdapter.roundResult thash st s.roundIndex m.1 m.2) := by
  rw [← OuterAdapter.advance_is_existing_round_step (concreteCommitRound thash) s m,
    concrete_commit_on_decoded_snapshot thash s.transcript st s.roundIndex m.1 m.2 hd]

theorem round_step_transcript_decodes (thash : Transcript.Hash) (s : Verifier.RoundState)
    (st : Transcript.State) (m : Verifier.CoupledMessage)
    (hd : OuterAdapter.decode s.transcript = some st) :
    OuterAdapter.decode (Verifier.roundStep (concreteCommitRound thash) s m).transcript =
      some ⟨(OuterAdapter.roundCommitted thash st s.roundIndex m.1 m.2).digest, 6⟩ := by
  rw [round_step_on_decoded_snapshot thash s st m hd]
  exact OuterAdapter.round_result_snapshot_decodes thash st s.roundIndex m.1 m.2

theorem round_step_index (thash : Transcript.Hash) (s : Verifier.RoundState)
    (m : Verifier.CoupledMessage) :
    (Verifier.roundStep (concreteCommitRound thash) s m).roundIndex = s.roundIndex + 1 := rfl

/-- (5) **THE FINAL SNAPSHOT OF A CONCRETE RUN DECODES**, and to the exact state
`concreteFinal` names -- with NO `CommitAgrees` hypothesis and NO successful
`OuterAdapter.execute`: only the incoming snapshot has to decode. -/
theorem concrete_run_snapshot_decodes (thash : Transcript.Hash) :
    ∀ (ms : List Verifier.CoupledMessage) (s : Verifier.RoundState) (st : Transcript.State),
      OuterAdapter.decode s.transcript = some st →
      OuterAdapter.decode
          (Verifier.runRounds (concreteCommitRound thash) s ms).transcript =
        some (concreteFinal thash st s.roundIndex ms)
  | [], _, _, hd => hd
  | m :: ms, s, st, hd => by
      have hstep := round_step_transcript_decodes thash s st m hd
      have ih := concrete_run_snapshot_decodes thash ms
        (Verifier.roundStep (concreteCommitRound thash) s m) _ hstep
      rw [round_step_index] at ih
      simpa only [Verifier.runRounds, concreteFinal] using ih

/-- (5) **THE ROUND CHALLENGES OF A CONCRETE RUN ARE THE CHAIN'S REDUCTIONS.**
Both point lists are the coordinatewise reductions of the digest chain, at
counters `0` (log lane) and `3` (gate lane). -/
theorem concrete_run_points (thash : Transcript.Hash) :
    ∀ (ms : List Verifier.CoupledMessage) (s : Verifier.RoundState) (st : Transcript.State),
      OuterAdapter.decode s.transcript = some st →
      (Verifier.runRounds (concreteCommitRound thash) s ms).logPoint =
          s.logPoint ++ (concreteChain thash st s.roundIndex ms).map (logChallengeOf thash) ∧
      (Verifier.runRounds (concreteCommitRound thash) s ms).gatePoint =
          s.gatePoint ++ (concreteChain thash st s.roundIndex ms).map (gateChallengeOf thash)
  | [], _, _, _ => by simp only [Verifier.runRounds, concreteChain, List.map_nil,
      List.append_nil, and_self]
  | m :: ms, s, st, hd => by
      have hstep := round_step_transcript_decodes thash s st m hd
      have ih := concrete_run_points thash ms
        (Verifier.roundStep (concreteCommitRound thash) s m) _ hstep
      have hs := round_step_on_decoded_snapshot thash s st m hd
      have hlog : (Verifier.roundStep (concreteCommitRound thash) s m).logPoint =
          s.logPoint ++ [logChallengeOf thash
            (OuterAdapter.roundCommitted thash st s.roundIndex m.1 m.2).digest] := by
        rw [hs]; rfl
      have hgate : (Verifier.roundStep (concreteCommitRound thash) s m).gatePoint =
          s.gatePoint ++ [gateChallengeOf thash
            (OuterAdapter.roundCommitted thash st s.roundIndex m.1 m.2).digest] := by
        rw [hs]; rfl
      rw [round_step_index] at ih
      refine ⟨?_, ?_⟩
      · rw [show Verifier.runRounds (concreteCommitRound thash) s (m :: ms) =
              Verifier.runRounds (concreteCommitRound thash)
                (Verifier.roundStep (concreteCommitRound thash) s m) ms from rfl,
          ih.1, hlog, concrete_chain_step, List.map_cons, List.append_assoc,
          List.singleton_append]
      · rw [show Verifier.runRounds (concreteCommitRound thash) s (m :: ms) =
              Verifier.runRounds (concreteCommitRound thash)
                (Verifier.roundStep (concreteCommitRound thash) s m) ms from rfl,
          ih.2, hgate, concrete_chain_step, List.map_cons, List.append_assoc,
          List.singleton_append]

/-! ## 6. (3b) The decoded snapshot, unconditionally -/

/-- The initial snapshot of an engine whose `initialObservation` is the adopted
`OuterInitial.derive` decodes, for every hash, once `degreeBits ≤ 13` bounds the
initial block's squeeze counter (`OuterInitial.derived_final_counter` gives
`12 + 6 * degreeBits`). -/
theorem derived_initial_snapshot_decodes (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13) :
    OuterAdapter.decode
        (OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p))).transcript =
      some (OuterInitial.derive thash c (Verifier.statement p)).state := by
  apply OuterAdapter.decode_snapshot
  rw [OuterInitial.derived_final_counter]
  unfold Transcript.u64Limit
  omega

theorem start_snapshot_decodes (e : Verifier.Engine) (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13) :
    OuterAdapter.decode (Verifier.start (e.initialTranscript c p)).transcript =
      some (OuterInitial.derive thash c (Verifier.statement p)).state := by
  rw [show (Verifier.start (e.initialTranscript c p)).transcript =
    (e.initialTranscript c p).transcript from rfl, hi]
  exact derived_initial_snapshot_decodes thash c p hdb

/-- (3b) **THE DECODE HYPOTHESIS IS DISCHARGED.** Every section-5 and section-7
statement of `InstalledIndexSampler` carries
`OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st` as an
explicit hypothesis, and
`InstalledIndexSampler.decoded_snapshot_exists_under_checked_execution`
discharges it only under `OuterAdapter.CommitAgrees thash e.commitRound` AND a
successful `OuterAdapter.execute thash c p`. For the installed round engine BOTH
of those disappear: `CommitAgrees` is now a theorem, and the run itself is the
concrete one, so the snapshot decodes from the initial-transcript observation
alone. `concreteFinal` names the decoded state exactly. -/
theorem decoded_snapshot_unconditional (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13) :
    OuterAdapter.decode
        (Verifier.derivedRounds (installedRoundEngine e gdec hash wp thash) c p).transcript =
      some (concreteFinal thash (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)) := by
  have hd := start_snapshot_decodes e thash c p hi hdb
  have h := concrete_run_snapshot_decodes thash (p.logRounds.zip p.gateRounds)
    (Verifier.start (e.initialTranscript c p)) _ hd
  exact h

/-- (3b) The same statement in the `∃` form the adopted module uses, so that it
is a drop-in for `InstalledIndexSampler`'s hypothesis at
`e := recommitted e thash`. -/
theorem decoded_snapshot_exists (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13) :
    ∃ st, OuterAdapter.decode
      (Verifier.derivedRounds (recommitted e thash) c p).transcript = some st :=
  ⟨_, decoded_snapshot_unconditional e gdec hash wp thash c p hi hdb⟩

/-- (3b) **THE ADOPTED SAMPLER FACTS, NOW UNCONDITIONAL FOR THIS ENGINE.**
`InstalledIndexSampler.sampled_indices_absorb_used_claims` is restated with its
decode hypothesis DISCHARGED: only the initial-transcript observation and
`degreeBits ≤ 13` remain. The claim block is still the eight adopted
`claimFrames`, the two lanes still have length `indexBits`, and the coordinates
are still the reductions at counters `3i, 3i+1, 3i+2` (log) and
`3b+3i, +1, +2` (gate) of the post-claims digest -- all now about the concrete
run's own snapshot. -/
theorem sampled_indices_absorb_used_claims_unconditional (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13) :
    ∃ st, OuterAdapter.decode
        (Verifier.derivedRounds (installedRoundEngine e gdec hash wp thash) c p).transcript =
          some st ∧
      OuterAdapter.claimsCommitted thash st p.used =
        OuterInitial.absorbMessages thash st (InstalledIndexSampler.claimFrames p.used) ∧
      (InstalledIndexSampler.claimFrames p.used).length = 8 ∧
      (Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p).log.length =
        c.indexBits ∧
      (Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p).gate.length =
        c.indexBits ∧
      (∀ i, i < c.indexBits →
        (Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p).log.get? i =
          some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
            ⟨InstalledIndexSampler.indexDigest thash st p.used, 3 * i⟩)).toVerifier) ∧
      (∀ i, i < c.indexBits →
        (Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p).gate.get? i =
          some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
            ⟨InstalledIndexSampler.indexDigest thash st p.used,
              3 * c.indexBits + 3 * i⟩)).toVerifier) := by
  obtain ⟨st, hst⟩ := decoded_snapshot_exists e gdec hash wp thash c p hi hdb
  have hall := InstalledIndexSampler.sampled_indices_absorb_used_claims (recommitted e thash)
    gdec hash wp thash c p st hst
  exact ⟨st, hst, hall.1, hall.2.1, hall.2.2.2.1, hall.2.2.2.2.1, hall.2.2.2.2.2.1,
    hall.2.2.2.2.2.2⟩

/-- (3b) The verifier's own index-length guard, satisfied unconditionally for
this engine: `Verifier.verify` rejects with `.configuration` unless both index
lanes have length `c.indexBits` (Verifier.lean 420-421), and here they do. -/
theorem index_lanes_have_index_bits_length_unconditional (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13) :
    (Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p).log.length =
      c.indexBits ∧
    (Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p).gate.length =
      c.indexBits := by
  obtain ⟨st, hst⟩ := decoded_snapshot_exists e gdec hash wp thash c p hi hdb
  exact (InstalledIndexSampler.index_lanes_have_index_bits_length (recommitted e thash)
    gdec hash wp thash c p st hst).1

/-- (3b) **THE LIMITATION, STATED AS A THEOREM.** The counterpart of
`index_lanes_have_index_bits_length_unconditional` on the OTHER branch. If the
run's snapshot does not decode -- which needs an engine whose
`initialObservation` is not the derived one, so `hi` is NOT available -- the
installed sampler returns EMPTY index lanes, and at `c.indexBits = 0` those lanes
have exactly the configured length, so the verifier's index-length guard
(Verifier.lean 420-421) PASSES. The adopted
`InstalledIndexSampler.malformed_snapshot_fails_the_index_length_guard` is the
only rejection route on this branch and it requires `c.indexBits ≠ 0`; by
`envelope_admits_index_bits_zero_iff_width_one` the adopted envelope does not
supply that. Nothing here says what a later check of `Verifier.verify` does. -/
theorem failed_path_passes_index_guard_at_index_bits_zero (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (hd : OuterAdapter.decode
      (Verifier.derivedRounds (recommitted e thash) c p).transcript = none)
    (hb : c.indexBits = 0) :
    Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p = ⟨[], []⟩ ∧
    (Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p).log.length =
      c.indexBits ∧
    (Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p).gate.length =
      c.indexBits := by
  have hpoints : Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p =
      ⟨[], []⟩ := by
    rw [show Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p =
        Verifier.derivedIndices
          (InstalledIndexSampler.installedSamplerEngine (recommitted e thash) gdec hash wp thash)
          c p from rfl,
      InstalledIndexSampler.installed_sampler_derived_indices,
      InstalledIndexSampler.concrete_sampler_rejects_malformed_snapshot thash _ p.used
        c.indexBits hd]
  refine ⟨hpoints, ?_, ?_⟩
  · rw [hpoints, hb]; rfl
  · rw [hpoints, hb]; rfl

/-! ## 7. (3a) and (3c) THE KEY THEOREMS -/

/-- (3a) **THE INSTALLED ROUNDS ARE THE ADOPTED CHECKED EXECUTION.** The adopted
`OuterAdapter.execute_matches_existing_derived_context` takes four
compatibility hypotheses; for this engine two of them --
`OuterAdapter.CommitAgrees` and `OuterAdapter.SamplesAgree` -- are now THEOREMS,
and `foldClaim = Connections.packedFold` is `rfl`. The only hypotheses that
remain are the initial-transcript OBSERVATION `hi` (the adopted
`TranscriptProvenance.DerivedInitial` shape), the source-sized
`degreeBits ≤ 13`, and success of the checked execution itself. -/
theorem installed_rounds_are_the_checked_execution (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (result : OuterAdapter.Execution)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13)
    (h : OuterAdapter.execute thash c p = some result) :
    result.rounds = Verifier.derivedRounds (installedRoundEngine e gdec hash wp thash) c p ∧
    result.initial = (installedRoundEngine e gdec hash wp thash).initialTranscript c p ∧
    result.indices.points =
      Verifier.derivedIndices (installedRoundEngine e gdec hash wp thash) c p ∧
    result.context = Verifier.derivedContext (installedRoundEngine e gdec hash wp thash) c p := by
  have hall := OuterAdapter.execute_matches_existing_derived_context thash
    (installedRoundEngine e gdec hash wp thash) c p result hi
    (concrete_commit_agrees thash)
    (InstalledIndexSampler.concrete_sampler_agrees_with_checked thash) rfl hdb h
  exact ⟨hall.2.1, hall.1, hall.2.2.1, hall.2.2.2⟩

/-- (3c) **THE ROUND DIGESTS CHAIN AFTER THE TWENTY-TWO-FRAME PREFIX.**
This is `GatePointZeroCheck`'s RES-4 and `JointChallengeSpace.Draw`'s
`outerLog` / `outerGate` counter labels, turned into theorems FOR THIS ENGINE:

1. the state the FIRST round commits onto is the adopted `OuterInitial.derive`
   state, whose digest IS the fold of `CommitmentOrder.gateChallengeFrames` --
   the twenty-two-frame prefix -- over `OuterInitial.startState`, and that prefix
   really has twenty-two frames;
2. each round's commit digest is the FIVE-frame fold `roundFrames` of that
   round's own index and message pair;
3. round `r`'s digest `d_r` is that fold applied to
   `concreteFinal ... (ms.take r)`, the state left by rounds `< r` (whose counter
   is `6` for `r > 0`, since round `r - 1` drew six scalars) --
   `concrete_chain_step` is the same fact as a one-step equation;
4. round `r`'s LOG challenge is
   `(OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash ⟨d_r, 0⟩)).toVerifier`
   and its GATE challenge is the same at counter `3`.

WHAT BECAME A THEOREM AND WHAT IS STILL A LABEL. The COUNTERS `0` and `3`, the
per-round BLOCK (each round squeezes from its OWN commit digest, not from the
prefix), and the CHAINING (block `r + 1`'s state is block `r`'s digest with the
counter at `6`) are all derived here for this engine's `commitRound`.
`JointChallengeSpace.sourceBlock`'s NUMBERING of those blocks -- `0` for the
prefix and `r + 1` for coupled round `r` -- is still a LABEL that module
assigns: conjunct 1 justifies the choice of `0` for the prefix and conjunct 3
the successor structure, but no theorem identifies this module's `concreteChain`
position with that numeral, and nothing forces an abstract `Verifier.Engine` to
number its blocks that way. `InstalledIndexSampler.indexSchedulePosition`'s
`degreeBits + 1` label is likewise untouched.

WHAT THIS IS NOT. `thash` is an arbitrary deterministic function; no
distribution is attached to any reduction, and half (B) is untouched. -/
theorem round_digests_chain_after_prefix (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13) :
    (OuterInitial.derive thash c (Verifier.statement p)).state.digest =
        (OuterInitial.absorbMessages thash OuterInitial.startState
          (CommitmentOrder.gateChallengeFrames c (Verifier.statement p))).digest ∧
    (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).length = 22 ∧
    (∀ (st : Transcript.State) (i : Nat) (m : Verifier.CoupledMessage),
      OuterAdapter.roundCommitted thash st i m.1 m.2 =
          OuterInitial.absorbMessages thash st (roundFrames i m) ∧
        (roundFrames i m).length = 5) ∧
    (∀ (r : Nat) (hr : r < (p.logRounds.zip p.gateRounds).length),
      (concreteChain thash (OuterInitial.derive thash c (Verifier.statement p)).state 0
          (p.logRounds.zip p.gateRounds)).get? r =
        some (OuterAdapter.roundCommitted thash
          (concreteFinal thash (OuterInitial.derive thash c (Verifier.statement p)).state 0
            ((p.logRounds.zip p.gateRounds).take r)) r
          ((p.logRounds.zip p.gateRounds).get ⟨r, hr⟩).1
          ((p.logRounds.zip p.gateRounds).get ⟨r, hr⟩).2).digest) ∧
    (Verifier.derivedRounds (installedRoundEngine e gdec hash wp thash) c p).logPoint =
      (concreteChain thash (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)).map (logChallengeOf thash) ∧
    (Verifier.derivedRounds (installedRoundEngine e gdec hash wp thash) c p).gatePoint =
      (concreteChain thash (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)).map (gateChallengeOf thash) := by
  have hprefix : (OuterInitial.derive thash c (Verifier.statement p)).state.digest =
      (OuterInitial.absorbMessages thash OuterInitial.startState
        (CommitmentOrder.gateChallengeFrames c (Verifier.statement p))).digest := by
    rw [OuterInitial.derived_final_digest]
    exact congrArg Transcript.State.digest
      (CommitmentOrder.prefix_state_is_relation_state thash c (Verifier.statement p)).symm
  have hd := start_snapshot_decodes e thash c p hi hdb
  have hpts := concrete_run_points thash (p.logRounds.zip p.gateRounds)
    (Verifier.start (e.initialTranscript c p)) _ hd
  refine ⟨hprefix, rfl, fun _ _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro r hr
    have h := concrete_chain_get thash (p.logRounds.zip p.gateRounds)
      (OuterInitial.derive thash c (Verifier.statement p)).state 0 r hr
    rwa [Nat.zero_add] at h
  · have h := hpts.1
    rw [show (Verifier.start (e.initialTranscript c p)).logPoint = [] from rfl,
      show (Verifier.start (e.initialTranscript c p)).roundIndex = 0 from rfl,
      List.nil_append] at h
    exact h
  · have h := hpts.2
    rw [show (Verifier.start (e.initialTranscript c p)).gatePoint = [] from rfl,
      show (Verifier.start (e.initialTranscript c p)).roundIndex = 0 from rfl,
      List.nil_append] at h
    exact h

/-! ## 8. (3d) The lanes are concrete -/

/-- The generic lane fact: for a concrete run, the challenge column of
`ConditionalSoundness.lane` is the lifted image of the digest chain under
whichever counter the lane's `pick` selects. -/
theorem lane_challenges_concrete (thash : Transcript.Hash)
    (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3)
    (f : Transcript.Digest → Verifier.Ext3)
    (hpick : ∀ (st : Transcript.State) (i : Nat) (m : Verifier.CoupledMessage),
      pick (OuterAdapter.roundResult thash st i m.1 m.2) =
        f (OuterAdapter.roundCommitted thash st i m.1 m.2).digest) :
    ∀ (ms : List Verifier.CoupledMessage) (truths : List (List Element))
      (s : Verifier.RoundState) (st : Transcript.State),
      OuterAdapter.decode s.transcript = some st →
      (ConditionalSoundness.lane (concreteCommitRound thash) sel pick truths s ms).map
          ConditionalSoundness.LaneRound.challenge =
        (concreteChain thash st s.roundIndex ms).map (fun d => OuterRound.lift (f d))
  | [], _, _, _, _ => rfl
  | m :: ms, truths, s, st, hd => by
      have hstep := round_step_transcript_decodes thash s st m hd
      have ih := lane_challenges_concrete thash sel pick f hpick ms truths.tail
        (Verifier.roundStep (concreteCommitRound thash) s m) _ hstep
      rw [round_step_index] at ih
      have hhead : pick (concreteCommitRound thash s.transcript s.roundIndex m.1 m.2) =
          f (OuterAdapter.roundCommitted thash st s.roundIndex m.1 m.2).digest := by
        rw [concrete_commit_on_decoded_snapshot thash s.transcript st s.roundIndex m.1 m.2 hd]
        exact hpick st s.roundIndex m
      simp only [ConditionalSoundness.lane, List.map_cons, concrete_chain_step, hhead]
      exact congrArg _ ih

/-- (3d) **THE ADOPTED LANES OF THIS ENGINE ARE CONCRETE SQUEEZES.**
`ConditionalSoundness.logLaneOf` and `gateLaneOf` read each round's challenge
from `e.commitRound` (ConditionalSoundness.lean 482-489). With the commit
installed, their challenge columns ARE the coordinatewise
`OuterChallenge.reduceTriple` reductions of the run's own digest chain, at
counters `0` and `3`, lifted by `OuterRound.lift`. Consequently the adopted
`JointChallengeSpace.DrawEncodesRun` is inhabited for this engine at a draw
assembled from the run's OWN digests, not only at the adopted `canonicalDraw`
whose coordinates are the arbitrary `encodeElement` preimages:
`actual_digest_draw_encodes_run` proves it at `actualDigestDraw`, which sends
`Draw.outerLog r` to `OuterChallenge.actualDigests thash ⟨d_r, 0⟩` and
`Draw.outerGate r` to `OuterChallenge.actualDigests thash ⟨d_r, 3⟩` for the run's
own round digest `d_r`, and the alpha and tau coordinates to the actual digests
at counters `9 + 3 * degreeBits` and `12 + 3 * degreeBits + 3 * i` of the
adopted relation state. For this engine the counter labels are therefore matched
by an INSTANCE, not merely documented.

WHAT DOES NOT CHANGE. `DrawEncodesRun` remains a COORDINATE statement, inhabited
for every hash by the adopted `JointChallengeSpace.draw_encodes_run_inhabited`;
nothing here says the draw is uniform, and half (B) is still unformalized. The
lane truth columns are still supplied `truths`, and the bad sets they index are
still the adopted ones. -/
theorem lanes_are_concrete (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (logTruths gateTruths : List (List Element))
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13) :
    (ConditionalSoundness.logLaneOf (installedRoundEngine e gdec hash wp thash) c p logTruths).map
        ConditionalSoundness.LaneRound.challenge =
      (concreteChain thash (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)).map
          (fun d => OuterRound.lift (logChallengeOf thash d)) ∧
    (ConditionalSoundness.gateLaneOf (installedRoundEngine e gdec hash wp thash) c p gateTruths).map
        ConditionalSoundness.LaneRound.challenge =
      (concreteChain thash (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)).map
          (fun d => OuterRound.lift (gateChallengeOf thash d)) := by
  have hd := start_snapshot_decodes e thash c p hi hdb
  refine ⟨?_, ?_⟩
  · have h := lane_challenges_concrete thash Prod.fst Verifier.RoundChallenges.log
      (logChallengeOf thash) (fun _ _ _ => rfl) (p.logRounds.zip p.gateRounds) logTruths
      (Verifier.start (e.initialTranscript c p)) _ hd
    rw [show (Verifier.start (e.initialTranscript c p)).roundIndex = 0 from rfl] at h
    exact h
  · have h := lane_challenges_concrete thash Prod.snd Verifier.RoundChallenges.gate
      (gateChallengeOf thash) (fun _ _ _ => rfl) (p.logRounds.zip p.gateRounds) gateTruths
      (Verifier.start (e.initialTranscript c p)) _ hd
    rw [show (Verifier.start (e.initialTranscript c p)).roundIndex = 0 from rfl] at h
    exact h

/-- (3d) `JointChallengeSpace.DrawnAt` from a lane whose challenge column is
known to be the image of a digest list: the adopted
`JointChallengeSpace.drawnAt_of_pointwise` recursion, with the per-round
coordinate supplied by `hw`. Hash-free and engine-free. -/
theorem drawn_at_of_chain (d : Nat) (w : JointChallengeSpace.JointSpace d)
    (proj : Nat → JointChallengeSpace.Draw d) (chain : List Transcript.Digest)
    (base : Transcript.Digest) (lane : List ConditionalSoundness.LaneRound)
    (g : Transcript.Digest → Element) (hlen : lane.length ≤ d)
    (hmap : lane.map ConditionalSoundness.LaneRound.challenge = chain.map g)
    (hw : ∀ k : Nat, k < d →
      OuterChallenge.reduceTriple (w (proj k)) = g ((chain.get? k).getD base)) :
    JointChallengeSpace.DrawnAt d w proj lane 0 := by
  apply JointChallengeSpace.drawnAt_of_pointwise
  intro j hj
  have hlenEq : lane.length = chain.length := by
    have h := congrArg List.length hmap
    simpa using h
  have hjc : j < chain.length := hlenEq ▸ hj
  have hjd : j < d := lt_of_lt_of_le hj hlen
  rw [Nat.zero_add, hw j hjd, List.get?_eq_get hjc, Option.getD_some]
  have h := congrArg (fun l => l.get? j) hmap
  simp only [List.get?_eq_getElem?, List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hjc, Option.map_some'] at h
  simpa only [List.get_eq_getElem] using Option.some.inj h

/-- The digest chain of the concrete run started from the adopted derived
initial state -- the list whose `r`-th entry is coupled round `r`'s own commit
digest. -/
def actualChain (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    List Transcript.Digest :=
  concreteChain thash (OuterInitial.derive thash c (Verifier.statement p)).state 0
    (p.logRounds.zip p.gateRounds)

/-- The adopted relation-state digest: the state the initial block's squeezes are
taken from, and the one `OuterInitial.gate_alpha_follows_log_tau` and
`OuterInitial.gate_tau_follows_gate_alpha` address. -/
def actualBase (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    Transcript.Digest :=
  (OuterInitial.relationState thash c (Verifier.statement p)).digest

/-- **THE ACTUAL-DIGEST DRAW.** The point of `JointChallengeSpace.JointSpace`
whose coordinates are the run's OWN three-digest triples: coupled round `r`'s
log coordinate is `OuterChallenge.actualDigests thash ⟨d_r, 0⟩` and its gate
coordinate `⟨d_r, 3⟩` for that round's commit digest `d_r`, the alpha coordinate
is the triple at counter `9 + 3 * degreeBits` of the relation state, and tau
coordinate `i` the triple at `12 + 3 * degreeBits + 3 * i`. Contrast the adopted
`JointChallengeSpace.canonicalDraw`, whose coordinates are the arbitrary
`encodeElement` preimages of the same VALUES. -/
def actualDigestDraw (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    JointChallengeSpace.JointSpace c.degreeBits
  | JointChallengeSpace.Draw.gateAlpha =>
      OuterChallenge.actualDigests thash ⟨actualBase thash c p, 9 + 3 * c.degreeBits⟩
  | JointChallengeSpace.Draw.gateTau i =>
      OuterChallenge.actualDigests thash
        ⟨actualBase thash c p, 12 + 3 * c.degreeBits + 3 * i.val⟩
  | JointChallengeSpace.Draw.outerLog r =>
      OuterChallenge.actualDigests thash
        ⟨((actualChain thash c p).get? r.val).getD (actualBase thash c p), 0⟩
  | JointChallengeSpace.Draw.outerGate r =>
      OuterChallenge.actualDigests thash
        ⟨((actualChain thash c p).get? r.val).getD (actualBase thash c p), 3⟩

/-- (3d) **THE SEAM IS INHABITED AT THE RUN'S OWN DIGESTS.** The adopted
`JointChallengeSpace.draw_encodes_run_inhabited` inhabits `DrawEncodesRun` at
`canonicalDraw`, whose coordinates are `encodeElement` preimages chosen only to
reduce to the right values; that is why the adopted `logDrawn` / `gateDrawn`
docstrings say the counter labels are documentation and the field "constrains
only the VALUE". For THIS engine the structure also holds at `actualDigestDraw`,
whose coordinates are the very digest triples the run squeezes: round `r`'s log
coordinate really is `OuterChallenge.actualDigests thash ⟨d_r, 0⟩` and its gate
coordinate `⟨d_r, 3⟩`, and the alpha and tau coordinates are the adopted
`OuterInitial` ones.

WHAT THIS DOES NOT DO. `DrawEncodesRun` is still a COORDINATE statement: no law,
uniform or otherwise, is attached to any coordinate, and half (B) of the
Fiat--Shamir reading is untouched. The `JointChallengeSpace.sourceBlock`
NUMBERING is likewise untouched. The shape hypotheses `hlr` and `hgr` are the
adopted `Verifier.shape` conjuncts (Verifier.lean 142). -/
theorem actual_digest_draw_encodes_run (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (logTruths gateTruths : List (List Element))
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hdb : c.degreeBits ≤ 13) (hlr : p.logRounds.length = c.degreeBits)
    (hgr : p.gateRounds.length = c.degreeBits) :
    JointChallengeSpace.DrawEncodesRun thash (installedRoundEngine e gdec hash wp thash) c p
      logTruths gateTruths (actualDigestDraw thash c p) where
  logDrawn := by
    refine drawn_at_of_chain c.degreeBits _ _ _ (actualBase thash c p) _
      (fun d => OuterRound.lift (logChallengeOf thash d))
      (le_of_eq (ConditionalSoundness.lane_length_of_shape _ c p logTruths hlr hgr).1)
      ((lanes_are_concrete e gdec hash wp thash c p logTruths gateTruths hi hdb).1.trans rfl) ?_
    intro k hk
    rw [JointChallengeSpace.logProj_apply c.degreeBits k hk]
    rfl
  gateDrawn := by
    refine drawn_at_of_chain c.degreeBits _ _ _ (actualBase thash c p) _
      (fun d => OuterRound.lift (gateChallengeOf thash d))
      (le_of_eq (ConditionalSoundness.lane_length_of_shape _ c p gateTruths hlr hgr).2)
      ((lanes_are_concrete e gdec hash wp thash c p logTruths gateTruths hi hdb).2.trans rfl) ?_
    intro k hk
    rw [JointChallengeSpace.gateProj_apply c.degreeBits k hk]
    rfl
  alphaDrawn := by
    show OuterRound.lift (TranscriptProvenance.derived thash c p).gateAlpha = _
    rw [TranscriptProvenance.derived, OuterInitial.gate_alpha_follows_log_tau]
    exact rfl
  tauDrawn := by
    intro i h
    have hg := OuterInitial.gate_tau_follows_gate_alpha thash c (Verifier.statement p) i.val i.isLt
    have hc : (TranscriptProvenance.gateTauColumn thash c p).get? i.val =
        some (OuterRound.lift (OuterInitial.ext3At thash
          (OuterInitial.relationState thash c (Verifier.statement p)).digest
          (12 + 3 * c.degreeBits + 3 * i.val))) := by
      show ((TranscriptProvenance.derived thash c p).gateTau.map OuterRound.lift).get? i.val = _
      rw [List.get?_eq_getElem?, List.getElem?_map, ← List.get?_eq_getElem?,
        TranscriptProvenance.derived, hg]
      rfl
    rw [List.get?_eq_get h] at hc
    rw [Option.some.inj hc]
    exact rfl

/-! ## 9. (3e) Non-malleability of one round's absorbed block -/

/-- (3e) **THE ROUND MESSAGES ARE FIXED BEFORE THE ROUND'S CHALLENGES.**
Two rounds whose commit digests agree had the same incoming state digest, the
same round INDEX and the same PAIR of lane messages -- or a concrete pair of
distinct byte strings with equal hash is EXHIBITED. Collision resistance is a
CONCLUSION, never a hypothesis; the adopted
`CommitmentOrder.absorb_messages_bind_or_collide`, itself built on the adopted
`CommitmentOrder.frame_injective`, does the work, and
`InstalledIndexSampler.encoded_vec_injective` inverts the `TAG_EXT3_VEC_V2`
payloads. This is the round-level twin of
`InstalledIndexSampler.used_claims_fixed_before_index_squeeze`.

WHAT THIS IS NOT. It is stated at the DIGEST the round's challenges are squeezed
from, not at the CHALLENGES: `OuterChallenge.reduceTriple` maps `2^768` digest
triples onto one field element, so equal challenges are strictly weaker than an
equal digest and cannot bind anything on their own. Same convention as
`CommitmentOrder`'s prefix-digest lemmas. The two u64 bounds on the round
indices are the source's own (TranscriptV2.sol 253, and
`Transcript.coupledRound`'s guard). -/
theorem round_message_fixed_before_round_challenges (thash : Transcript.Hash)
    (s t : Transcript.State) (i j : Nat) (m n : Verifier.CoupledMessage)
    (hbi : i < Transcript.u64Limit) (hbj : j < Transcript.u64Limit)
    (h : (OuterAdapter.roundCommitted thash s i m.1 m.2).digest =
      (OuterAdapter.roundCommitted thash t j n.1 n.2).digest) :
    (s.digest = t.digest ∧ i = j ∧ m = n) ∨ CommitmentOrder.TranscriptCollision thash := by
  have hbytes : (256 : Nat) ^ 8 = Transcript.u64Limit := by
    unfold Transcript.u64Limit
    norm_num
  rw [round_committed_is_the_frame_fold, round_committed_is_the_frame_fold] at h
  rcases CommitmentOrder.absorb_messages_bind_or_collide thash (roundFrames i m)
      (roundFrames j n) s t (by rw [round_frame_count, round_frame_count]) h with
      ⟨hdig, hframes⟩ | hcol
  · refine Or.inl ⟨hdig, ?_, ?_⟩
    · have h1 := (round_frames_get_index i m).symm.trans
        ((congrArg (fun l => l.get? 1) hframes).trans (round_frames_get_index j n))
      have hle : Transcript.le 8 i = Transcript.le 8 j :=
        congrArg OuterInitial.Message.payload (Option.some.inj h1)
      exact Transcript.le_injective_bounded 8 i j (by rw [hbytes]; exact hbi)
        (by rw [hbytes]; exact hbj) hle
    · have h2 := (round_frames_get_log_message i m).symm.trans
        ((congrArg (fun l => l.get? 2) hframes).trans (round_frames_get_log_message j n))
      have h3 := (round_frames_get_gate_message i m).symm.trans
        ((congrArg (fun l => l.get? 3) hframes).trans (round_frames_get_gate_message j n))
      have hlog : m.1 = n.1 := InstalledIndexSampler.encoded_vec_injective _ _
        (congrArg OuterInitial.Message.payload (Option.some.inj h2))
      have hgate : m.2 = n.2 := InstalledIndexSampler.encoded_vec_injective _ _
        (congrArg OuterInitial.Message.payload (Option.some.inj h3))
      exact Prod.ext hlog hgate
  · exact Or.inr hcol

/-- (3e) CONTRAPOSITIVE: a prover who changes either lane's round message
CANNOT keep the digest that round's coupled challenges are squeezed from, unless
the hash chain collides. -/
theorem changing_a_round_message_changes_the_round_digest_or_collides
    (thash : Transcript.Hash) (s t : Transcript.State) (i j : Nat)
    (m n : Verifier.CoupledMessage)
    (hbi : i < Transcript.u64Limit) (hbj : j < Transcript.u64Limit) (hne : m ≠ n)
    (h : (OuterAdapter.roundCommitted thash s i m.1 m.2).digest =
      (OuterAdapter.roundCommitted thash t j n.1 n.2).digest) :
    CommitmentOrder.TranscriptCollision thash := by
  rcases round_message_fixed_before_round_challenges thash s t i j m n hbi hbj h with
    ⟨_, _, heq⟩ | hcol
  · exact absurd heq hne
  · exact hcol

/-- (3e) The same statement at the run level: two concrete runs whose round-`r`
commit digests agree used the same round-`r` message pair and reached round `r`
with the same digest, or the outer hash collides. `concreteFinal ... (take r)` is
the state left by rounds `< r`, so this binds the whole prefix of the chain. -/
theorem run_round_digest_binds_the_round_message (thash : Transcript.Hash)
    (s0 t0 : Transcript.State) (ms ns : List Verifier.CoupledMessage) (r : Nat)
    (m n : Verifier.CoupledMessage) (hbr : r < Transcript.u64Limit)
    (h : (OuterAdapter.roundCommitted thash
        (concreteFinal thash s0 0 (ms.take r)) r m.1 m.2).digest =
      (OuterAdapter.roundCommitted thash
        (concreteFinal thash t0 0 (ns.take r)) r n.1 n.2).digest) :
    ((concreteFinal thash s0 0 (ms.take r)).digest =
        (concreteFinal thash t0 0 (ns.take r)).digest ∧ m = n) ∨
      CommitmentOrder.TranscriptCollision thash := by
  rcases round_message_fixed_before_round_challenges thash _ _ r r m n hbr hbr h with
    ⟨hdig, _, heq⟩ | hcol
  · exact Or.inl ⟨hdig, heq⟩
  · exact Or.inr hcol

/-- (3e) The same at a round index that a SHAPED proof actually has, so the u64
bound is discharged instead of assumed. `Verifier.shape` pins
`p.logRounds.length = c.degreeBits` (Verifier.lean 142) and `Verifier.envelope`
pins `c.degreeBits ≤ 13` (Verifier.lean 98); a round index inside
`p.logRounds.zip p.gateRounds` is therefore below `13`, hence below
`Transcript.u64Limit`, and the source's own guard (TranscriptV2.sol 253,
`Transcript.coupledRound`) is never the binding constraint on an accepted
run. -/
theorem run_round_digest_binds_the_round_message_of_a_shaped_proof (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) (s0 t0 : Transcript.State)
    (ms ns : List Verifier.CoupledMessage) (r : Nat) (m n : Verifier.CoupledMessage)
    (hr : r < (p.logRounds.zip p.gateRounds).length)
    (hlr : p.logRounds.length = c.degreeBits) (hdb : c.degreeBits ≤ 13)
    (h : (OuterAdapter.roundCommitted thash
        (concreteFinal thash s0 0 (ms.take r)) r m.1 m.2).digest =
      (OuterAdapter.roundCommitted thash
        (concreteFinal thash t0 0 (ns.take r)) r n.1 n.2).digest) :
    ((concreteFinal thash s0 0 (ms.take r)).digest =
        (concreteFinal thash t0 0 (ns.take r)).digest ∧ m = n) ∨
      CommitmentOrder.TranscriptCollision thash := by
  have hbr : r < Transcript.u64Limit := by
    rw [List.length_zip] at hr
    have h13 : r < 13 := by omega
    unfold Transcript.u64Limit
    omega
  exact run_round_digest_binds_the_round_message thash s0 t0 ms ns r m n hbr h

/-! ## 10. Examples on small data

A CONSTANT toy hash, not Keccak, and the adopted `OuterAdapter.fixtureConfig` /
`fixtureProof`. Nothing below is a fixture of the deployed profile and nothing
computes over the digest space: the only evaluations are `decide` on one 40-byte
snapshot and on one reduced challenge per lane. -/

def toyHash : Transcript.Hash := fun _ => OuterChallenge.ordinaryDigest

/-- The base engine of the examples: the adopted `Verifier.testEngine` with the
adopted `OuterInitial.withInitial` initial observation, so that the
initial-transcript hypothesis of sections 6-8 holds by `rfl`. -/
def exampleBase : Verifier.Engine := OuterInitial.withInitial toyHash Verifier.testEngine

theorem example_base_initial (c : Verifier.Config) (p : Verifier.Proof) :
    exampleBase.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive toyHash c (Verifier.statement p)) := rfl

/-- (10) The adopted fixture has ONE coupled round, so the concrete run's digest
chain has exactly one entry and both point lists have length one. Lengths only;
no digest cardinality is evaluated. -/
theorem example_fixture_round_shape (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) :
    (Verifier.derivedRounds (installedRoundEngine exampleBase gdec hash wp toyHash)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).logPoint.length = 1 ∧
    (Verifier.derivedRounds (installedRoundEngine exampleBase gdec hash wp toyHash)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).gatePoint.length = 1 := by
  have hall := round_digests_chain_after_prefix exampleBase gdec hash wp toyHash
    OuterAdapter.fixtureConfig OuterAdapter.fixtureProof rfl (by decide)
  have hlen : (concreteChain toyHash
      (OuterInitial.derive toyHash OuterAdapter.fixtureConfig
        (Verifier.statement OuterAdapter.fixtureProof)).state 0
      (OuterAdapter.fixtureProof.logRounds.zip
        OuterAdapter.fixtureProof.gateRounds)).length = 1 := by
    rw [concrete_chain_length]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hall.2.2.2.2.1, List.length_map, hlen]
  · rw [hall.2.2.2.2.2, List.length_map, hlen]

/-- (10) The run's final snapshot DECODES -- it is a real 40-byte snapshot
carrying the last round's digest and counter `6` -- so the installed sampler of
`InstalledIndexSampler` is fed a decodable snapshot with no hypothesis left. -/
theorem example_fixture_snapshot_decodes (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) :
    ∃ st, OuterAdapter.decode
      (Verifier.derivedRounds (installedRoundEngine exampleBase gdec hash wp toyHash)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).transcript = some st :=
  ⟨_, decoded_snapshot_unconditional exampleBase gdec hash wp toyHash
    OuterAdapter.fixtureConfig OuterAdapter.fixtureProof rfl (by decide)⟩

/-- (10) Both index lanes of the fixture have the configured length `1`, with no
decode hypothesis and no `CommitAgrees` hypothesis remaining. -/
theorem example_fixture_index_lanes (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) :
    (Verifier.derivedIndices (installedRoundEngine exampleBase gdec hash wp toyHash)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).log.length = 1 ∧
    (Verifier.derivedIndices (installedRoundEngine exampleBase gdec hash wp toyHash)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).gate.length = 1 :=
  index_lanes_have_index_bits_length_unconditional exampleBase gdec hash wp toyHash
    OuterAdapter.fixtureConfig OuterAdapter.fixtureProof rfl (by decide)

/-- (10) Both `ConditionalSoundness` lanes have exactly one round for the
fixture. -/
theorem example_fixture_lane_lengths (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (logTruths gateTruths : List (List Element)) :
    (ConditionalSoundness.logLaneOf (installedRoundEngine exampleBase gdec hash wp toyHash)
      OuterAdapter.fixtureConfig OuterAdapter.fixtureProof logTruths).length = 1 ∧
    (ConditionalSoundness.gateLaneOf (installedRoundEngine exampleBase gdec hash wp toyHash)
      OuterAdapter.fixtureConfig OuterAdapter.fixtureProof gateTruths).length = 1 := by
  have h1 := ConditionalSoundness.lane_length_of_shape
    (installedRoundEngine exampleBase gdec hash wp toyHash) OuterAdapter.fixtureConfig
    OuterAdapter.fixtureProof logTruths rfl rfl
  have h2 := ConditionalSoundness.lane_length_of_shape
    (installedRoundEngine exampleBase gdec hash wp toyHash) OuterAdapter.fixtureConfig
    OuterAdapter.fixtureProof gateTruths rfl rfl
  exact ⟨h1.1, h2.2⟩

/-- (10) On the constant toy hash both coupled challenges reduce to
`(5, 5, 5)`: `fromLe (le 32 5) % p = 5` in each of the three limbs. This is the
only value evaluation in the module. -/
theorem example_toy_round_challenge_values :
    ((logChallengeOf toyHash OuterChallenge.ordinaryDigest).val.c0,
      (logChallengeOf toyHash OuterChallenge.ordinaryDigest).val.c1,
      (logChallengeOf toyHash OuterChallenge.ordinaryDigest).val.c2) = (5, 5, 5) ∧
    ((gateChallengeOf toyHash OuterChallenge.ordinaryDigest).val.c0,
      (gateChallengeOf toyHash OuterChallenge.ordinaryDigest).val.c1,
      (gateChallengeOf toyHash OuterChallenge.ordinaryDigest).val.c2) = (5, 5, 5) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- (10) **THE ABSTRACT OBSERVATION IS NOT THIS FUNCTION, ON DECODABLE INPUTS.**
`Verifier.testEngine.commitRound` returns `⟨[], zero, zero⟩` for every input: an
EMPTY transcript snapshot and two zero challenges, reading none of its
arguments. On the DECODABLE snapshot used below the installed commit differs
from it in SHAPE -- its snapshot is the forty bytes `OuterAdapter.decode`
requires -- and in VALUE, since its challenges reduce to `(5, 5, 5)` on the toy
hash.

THIS IS A DECODABLE-INPUTS-ONLY SEPARATION. On a snapshot that does NOT decode
`concreteCommitRound thash raw i log gate` is `failedRound`, which IS
`Verifier.testEngine.commitRound raw i log gate` argument for argument, so no
separation holds there; see the header's failure-branch section and
`concrete_commit_rejects_malformed_snapshot`. -/
theorem example_concrete_commit_is_not_the_abstract_observation
    (i : Nat) (log gate : List Verifier.Ext3) :
    Verifier.testEngine.commitRound (OuterInitial.snapshot ⟨OuterChallenge.ordinaryDigest, 0⟩)
        i log gate = ⟨[], Verifier.zero, Verifier.zero⟩ ∧
    (concreteCommitRound toyHash (OuterInitial.snapshot ⟨OuterChallenge.ordinaryDigest, 0⟩)
        i log gate).transcript.length = 40 ∧
    (concreteCommitRound toyHash (OuterInitial.snapshot ⟨OuterChallenge.ordinaryDigest, 0⟩)
        i log gate).log ≠ Verifier.zero ∧
    (concreteCommitRound toyHash (OuterInitial.snapshot ⟨OuterChallenge.ordinaryDigest, 0⟩)
        i log gate).gate ≠ Verifier.zero := by
  have hd : OuterAdapter.decode (OuterInitial.snapshot ⟨OuterChallenge.ordinaryDigest, 0⟩) =
      some ⟨OuterChallenge.ordinaryDigest, 0⟩ := OuterAdapter.decode_snapshot _ (by decide)
  have hc := concrete_commit_challenges toyHash
    (OuterInitial.snapshot ⟨OuterChallenge.ordinaryDigest, 0⟩) ⟨OuterChallenge.ordinaryDigest, 0⟩
    i log gate hd
  have hv := example_toy_round_challenge_values
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [concrete_commit_on_decoded_snapshot toyHash _ _ i log gate hd]
    exact OuterInitial.snapshot_length _
  · rw [hc.1]
    intro hzero
    have hlog : logChallengeOf toyHash
        (OuterAdapter.roundCommitted toyHash ⟨OuterChallenge.ordinaryDigest, 0⟩ i log gate).digest
          = logChallengeOf toyHash OuterChallenge.ordinaryDigest := rfl
    rw [hlog] at hzero
    rw [hzero] at hv
    exact absurd hv.1 (by decide)
  · rw [hc.2.1]
    intro hzero
    have hgate : gateChallengeOf toyHash
        (OuterAdapter.roundCommitted toyHash ⟨OuterChallenge.ordinaryDigest, 0⟩ i log gate).digest
          = gateChallengeOf toyHash OuterChallenge.ordinaryDigest := rfl
    rw [hgate] at hzero
    rw [hzero] at hv
    exact absurd hv.2 (by decide)

end Audit.Wire3.InstalledRoundCommit
