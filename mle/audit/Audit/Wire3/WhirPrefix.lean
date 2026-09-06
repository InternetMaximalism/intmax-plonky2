import Audit.Wire3.WhirInitial
import Audit.Wire3.WhirFinalSpongefish

/-!
Concrete execution of WHIR phases 1 and 2 at becfe98e, on ONE byte source.
Initial commitments/claims/OOD/RLC produce the initial sum and sponge used by
the actual quadratic sumcheck engine. No earlier-state or decoder observation
provides that sum. This reuses the same sumcheck loop as the final phase.

Input Params/forms/roots, protocol/session/instance, round count and threshold
must originate at the validated caller boundary. This does not implement their
ABI/protocol derivation or intermediate rounds, and is NOT a full verifier.
Initial-form/constraint projections translate the concrete initial data to the
WhirFinal types; they do not invent the later intermediate constraints or Plan.
Hints are not read by these two phases; the original hint position is retained
separately rather than being accepted by resetting its cursor. Byte conversion
is the proved lossless UInt8/Fin256 adapter, not another transcript.
-/
namespace Audit.Wire3.WhirPrefix
open Spongefish (Hash Bytes Digest Ext3)

structure Result where
  initial : WhirInitial.Result
  sumcheck : WhirFinal.State
  hintPos : Nat

def sumcheckStart (initial : WhirInitial.Result) (afterInitial : Spongefish.State) : WhirFinal.State :=
  ⟨WhirFinalSpongefish.fromSpongefish afterInitial, initial.theSum.val, []⟩

def run (hash : Hash) (source : Bytes) (p : WhirInitial.Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (count threshold : Nat) (start : Spongefish.State) :
    Option Result := do
  let (initial, afterInitial) ← WhirInitial.phaseInitial hash source p roots expected mask start
  let final ← WhirFinal.runRounds (WhirFinalSpongefish.engine hash) threshold
    (WhirFinalSpongefish.fromTranscriptBytes source) count (sumcheckStart initial afterInitial)
  pure ⟨initial, final, afterInitial.hintPos⟩

def initializeAndRun (hash : Hash) (protocolId sessionId publicInstance source : Bytes)
    (p : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (count threshold : Nat) : Option Result :=
  run hash source p roots expected mask count threshold (Spongefish.init hash protocolId sessionId publicInstance)

def initialConstraint (r : Result) : WhirFinal.RoundConstraint :=
  ⟨r.initial.initialRoundConstraint.numVariables,
    r.initial.initialRoundConstraint.rlcCoeffs.map Subtype.val,
    r.initial.initialRoundConstraint.univariatePoints.map Subtype.val⟩

def linearForms (r : Result) : List WhirFinal.LinearForm :=
  r.initial.forms.map fun form => ⟨form.coefficient.val, form.point.map Subtype.val⟩

theorem successful_prefix_is_one_execution (hash : Hash) (source : Bytes) (p : WhirInitial.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (count threshold : Nat)
    (s : Spongefish.State) (r : Result) (h : run hash source p roots expected mask count threshold s = some r) :
    ∃ afterInitial,
      WhirInitial.phaseInitial hash source p roots expected mask s = some (r.initial,afterInitial) ∧
      WhirFinal.runRounds (WhirFinalSpongefish.engine hash) threshold
        (WhirFinalSpongefish.fromTranscriptBytes source) count (sumcheckStart r.initial afterInitial) = some r.sumcheck ∧
      r.hintPos = afterInitial.hintPos := by
  unfold run at h
  cases hi : WhirInitial.phaseInitial hash source p roots expected mask s with
  | none => simp [hi] at h
  | some pair =>
      rcases pair with ⟨initial,next⟩
      cases hr : WhirFinal.runRounds (WhirFinalSpongefish.engine hash) threshold
          (WhirFinalSpongefish.fromTranscriptBytes source) count (sumcheckStart initial next) with
      | none => simp [hi,hr] at h
      | some final =>
          simp only [hi,hr,bind,Option.bind,pure,Option.some.injEq] at h
          subst r
          exact ⟨next,rfl,hr,rfl⟩

theorem successful_prefix_keeps_roots_and_all_checked_claims (hash : Hash) (source : Bytes)
    (p : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (count threshold : Nat) (s : Spongefish.State) (r : Result)
    (h : run hash source p roots expected mask count threshold s = some r) :
    r.initial.commitments.map (·.root) = roots ∧ r.initial.commitments.map (·.boundRoot) = roots ∧
    r.initial.evaluations.length = expected.length ∧
    (∀ i, i < expected.length → WhirInitial.isChecked mask i →
      r.initial.evaluations.getD i Verifier.zero = expected.getD i Verifier.zero) ∧
    WhirInitial.preservesOwn (WhirInitial.matrixSlots p r.initial.commitments) r.initial.oodMatrix := by
  obtain ⟨next,hi,_,_⟩ := successful_prefix_is_one_execution hash source p roots expected mask count threshold s r h
  exact WhirInitial.initial_all_roots_and_checked_claims hash source p roots expected mask s next r.initial hi

theorem successful_prefix_exact_consumption (hash : Hash) (source : Bytes) (p : WhirInitial.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (count threshold : Nat)
    (s : Spongefish.State) (r : Result) (h : run hash source p roots expected mask count threshold s = some r) :
    r.sumcheck.cursor.transcriptPos = s.transcriptPos +
      roots.length * (64 + 24 * (p.outDomainSamples * p.numVectors)) + 24 * expected.length +
      24 * WhirInitial.crossCount (WhirInitial.matrixSlots p r.initial.commitments) +
      count * (48 + WhirFinalSpongefish.powBytes threshold) ∧
    r.sumcheck.finalRandomness.length = count ∧ r.hintPos = s.hintPos := by
  obtain ⟨next,hi,hr,hh⟩ := successful_prefix_is_one_execution hash source p roots expected mask count threshold s r h
  have a := WhirInitial.initial_exact_read_count hash source p roots expected mask s next r.initial hi
  have b := WhirFinalSpongefish.rounds_success_exact_consumption hash threshold
    (WhirFinalSpongefish.fromTranscriptBytes source) count (sumcheckStart r.initial next) r.sumcheck hr
  simp only [sumcheckStart,WhirFinalSpongefish.fromSpongefish,List.length_nil,Nat.zero_add] at b
  exact ⟨by omega,b.2,hh.trans a.2⟩

theorem first_round_starts_from_computed_sum_and_sponge (hash : Hash) (source : Bytes)
    (p : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (count threshold : Nat) (s : Spongefish.State) (r : Result)
    (h : run hash source p roots expected mask (count+1) threshold s = some r) :
    ∃ afterInitial first,
      WhirInitial.phaseInitial hash source p roots expected mask s = some (r.initial,afterInitial) ∧
      WhirFinal.roundStep (WhirFinalSpongefish.engine hash) threshold
        (WhirFinalSpongefish.fromTranscriptBytes source)
        ⟨⟨afterInitial.transcriptPos,afterInitial.sponge⟩,r.initial.theSum.val,[]⟩ = some first := by
  obtain ⟨next,hi,hr,_⟩ := successful_prefix_is_one_execution hash source p roots expected mask (count+1) threshold s r h
  cases hs : WhirFinal.roundStep (WhirFinalSpongefish.engine hash) threshold
      (WhirFinalSpongefish.fromTranscriptBytes source) (sumcheckStart r.initial next) with
  | none => simp [WhirFinal.runRounds,hs] at hr
  | some first => exact ⟨next,first,hi,hs⟩

theorem projected_initial_constraints_have_exact_shape (hash : Hash) (source : Bytes)
    (p : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (count threshold : Nat) (s : Spongefish.State) (r : Result)
    (hp : WhirInitial.validatedParams p roots expected mask)
    (h : run hash source p roots expected mask count threshold s = some r) :
    (initialConstraint r).coefficients.length = WhirInitial.totalOodPoints p ∧
    (initialConstraint r).points.length = WhirInitial.totalOodPoints p ∧
    (initialConstraint r).numVariables = p.initialNumVariables ∧
    (linearForms r).length = p.forms.length := by
  obtain ⟨next,hi,_,_⟩ := successful_prefix_is_one_execution hash source p roots expected mask count threshold s r h
  have a := WhirInitial.initial_output_shapes hash source p roots expected mask s next r.initial hp hi
  have b := WhirInitial.initial_sum_and_constraints_same_data hash source p roots expected mask s next r.initial hi
  simp only [initialConstraint,linearForms,List.length_map]
  exact ⟨a.2.2.2.2.2.2.1,a.2.2.2.2.2.2.2.1,b.2.2.2.1,a.2.2.2.2.2.2.2.2⟩

theorem initialized_prefix_does_not_consume_hints (hash : Hash) (protocolId sessionId publicInstance source : Bytes)
    (p : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (count threshold : Nat) (r : Result)
    (h : initializeAndRun hash protocolId sessionId publicInstance source p roots expected mask count threshold = some r) :
    r.hintPos = 0 :=
  (successful_prefix_exact_consumption hash source p roots expected mask count threshold
    (Spongefish.init hash protocolId sessionId publicInstance) r h).2.2

/-- Ordinary stage example extends the two-commitment initial transcript by an
actual 48-byte round. It is not a cryptographic proof or a production profile. -/
def exampleSource : Bytes := List.replicate 320 Spongefish.zeroByte
def exampleResult : Result :=
  ⟨WhirInitial.exampleResult, ⟨⟨320,⟨Spongefish.zeroDigest,4⟩⟩,Arithmetic.zero,[Arithmetic.zero]⟩,0⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem concrete_initial_and_sumcheck_example :
    run WhirInitial.exampleHash exampleSource WhirInitial.exampleParams WhirInitial.exampleRoots
      WhirInitial.exampleClaims WhirInitial.exampleMask 1 Spongefish.maxCounter WhirInitial.exampleStart =
      some exampleResult := by rfl

end Audit.Wire3.WhirPrefix
