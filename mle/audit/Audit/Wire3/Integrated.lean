import Audit.Wire3.Connections
import Audit.Wire3.Norm
import Audit.Wire3.GatesComplete

/-!
Concrete outer-verifier connections (runtime snapshot becfe98e).

This model substitutes concrete packed folding, norm/logUp including direct PI
binding, equality evaluation, and all fourteen gate evaluators for four Engine
observations. Gate metadata is decoded ONLY from the fixed configuration bytes;
its ABI decoder remains an observation, not prover-supplied metadata.

The wrapper checks the norm adapter's shape/seven-challenge layout and requires
the complete dispatcher to produce a result before calling Verifier.verify.
Thus malformed configuration/decoding cannot become acceptance through a default
zero. `modelEngine` alone is NOT the checked entry point: its zero fallback is
only totalization for the old non-Option Engine interface. Use `verify` below.
These extra checks are MODEL INTERFACE/PREFLIGHT obligations, not a claim that
Solidity performs all constructor checks again on each call.
Preflight failures use the coarse model error `configuration`; production
exception ordering/classification, slashing evidence and gas are NOT refined.
Gates.rustAdmission's separate lookup guard is not installed by this wrapper.

Initial transcript, configuration/hash/deployment, public-input hash, metadata
decoding, and WHIR parsing/tail remain observations. WhirFinal and Merkle are not
silently installed as a complete whirTail. Full source refinement, gate semantic/
degree proofs, probabilistic aggregation, and cryptographic soundness are open.
-/
namespace Audit.Wire3.Integrated
open Verifier

abbrev DecodeGates := Bytes → Option (List Gates.GateInfo)

def gateConfig (c : Config) : Gates.Config :=
  ⟨c.numSelectors, c.numConstants, c.numGateConstraints, c.numWires, c.quotientDegree⟩

def evaluateGate (decode : DecodeGates) (c : Config) (wires constants : List Ext3)
    (publicHash : List Base) (alpha : Ext3) : Option Ext3 := do
  let gates ← decode c.gatesEncoding
  if gates.length ≠ c.gateRows ∨ publicHash.length ≠ 4 then none else
    GatesComplete.evalCombined (gateConfig c) gates wires constants (fun i => publicHash.getD i (base 0)) alpha

def modelEngine (e : Engine) (decode : DecodeGates) : Engine :=
  { e with
    foldClaim := Connections.packedFold,
    normEvaluation := Norm.normEvaluation,
    eqEvaluation := Norm.eqEvaluation,
    gateEvaluation := fun c wires constants publicHash alpha =>
      (evaluateGate decode c wires constants publicHash alpha).getD zero }

def gateResult (e : Engine) (decode : DecodeGates) (c : Config) (p : Proof) : Option Ext3 :=
  evaluateGate decode c p.used.gateWitness (p.used.gatePreprocessed.take c.numConstants)
    (e.publicInputsHash p.publicInputs) (e.initialTranscript c p).gateAlpha

def normResult (e : Engine) (c : Config) (p : Proof) : Option Ext3 :=
  Norm.checkedNormEvaluation c (e.initialTranscript c p)
    (normTerminalInput p) (derivedRounds e c p).logPoint

def verify (e : Engine) (decode : DecodeGates) (pin : Pinned) (chain : Nat)
    (c : Config) (p : Proof) : Except Error Unit :=
  let concrete := modelEngine e decode
  match normResult concrete c p with
  | none => .error .configuration
  | some _ => match gateResult concrete decode c p with
    | none => .error .configuration
    | some _ => Verifier.verify concrete pin chain c p

theorem concrete_engine_keeps_transcript (e : Engine) (decode : DecodeGates) (c : Config) (p : Proof) :
    (modelEngine e decode).initialTranscript c p = e.initialTranscript c p ∧
    derivedRounds (modelEngine e decode) c p = derivedRounds e c p := ⟨rfl, rfl⟩

theorem concrete_engine_uses_packed_fold (e : Engine) (decode : DecodeGates)
    (values point : List Ext3) (width : Nat) :
    ((modelEngine e decode).foldClaim values width point).val =
      Packed.fold (values.map Subtype.val) (point.map Subtype.val) := rfl

theorem gate_evaluation_uses_fixed_config_bytes (decode : DecodeGates) (c : Config)
    (wires constants : List Ext3) (publicHash : List Base) (alpha result : Ext3)
    (h : evaluateGate decode c wires constants publicHash alpha = some result) :
    ∃ gates, decode c.gatesEncoding = some gates ∧ gates.length = c.gateRows ∧
      publicHash.length = 4 ∧
      GatesComplete.evalCombined (gateConfig c) gates wires constants
        (fun i => publicHash.getD i (base 0)) alpha = some result := by
  unfold evaluateGate at h
  cases hd : decode c.gatesEncoding with
  | none => simp [hd] at h
  | some gates =>
      simp only [hd, bind, Option.bind] at h
      split at h
      · contradiction
      · rename_i hs
        exact ⟨gates, rfl, by omega, by omega, h⟩

theorem valid_decoded_gate_configuration_evaluates (decode : DecodeGates) (c : Config)
    (gates : List Gates.GateInfo) (wires constants : List Ext3) (publicHash : List Base) (alpha : Ext3)
    (hd : decode c.gatesEncoding = some gates) (hr : gates.length = c.gateRows)
    (hp : publicHash.length = 4) (hw : wires.length = c.numWires)
    (hc : constants.length = c.numConstants)
    (hv : Gates.validateConfiguration (gateConfig c) gates = some ()) :
    ∃ result, evaluateGate decode c wires constants publicHash alpha = some result := by
  obtain ⟨result, he⟩ := GatesComplete.valid_configuration_always_evaluates (gateConfig c)
    gates wires constants (fun i => publicHash.getD i (base 0)) alpha hv hw hc
  exact ⟨result, by simpa [evaluateGate, hd, hr, hp] using he⟩

theorem successful_gate_evaluation_checks_all_metadata (decode : DecodeGates) (c : Config)
    (wires constants : List Ext3) (publicHash : List Base) (alpha result : Ext3)
    (h : evaluateGate decode c wires constants publicHash alpha = some result) :
    ∃ gates, decode c.gatesEncoding = some gates ∧ gates.length = c.gateRows ∧
      publicHash.length = 4 ∧ wires.length = c.numWires ∧ constants.length = c.numConstants ∧
      Gates.validateConfiguration (gateConfig c) gates = some () := by
  obtain ⟨gates, hd, hr, hp, he⟩ := gate_evaluation_uses_fixed_config_bytes decode c
    wires constants publicHash alpha result h
  have hv := GatesComplete.combined_success_requires_all_configuration (gateConfig c)
    gates wires constants (fun i => publicHash.getD i (base 0)) alpha result he
  exact ⟨gates, hd, hr, hp, hv⟩

theorem accepted_preflights_and_original_verifier (e : Engine) (decode : DecodeGates)
    (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e decode pin chain c p = .ok ()) :
    ∃ norm gate,
      normResult (modelEngine e decode) c p = some norm ∧
      gateResult (modelEngine e decode) decode c p = some gate ∧
      Verifier.verify (modelEngine e decode) pin chain c p = .ok () := by
  unfold verify at h
  cases hn : normResult (modelEngine e decode) c p with
  | none => simp [hn] at h
  | some norm =>
      simp only [hn] at h
      cases hg : gateResult (modelEngine e decode) decode c p with
      | none => simp [hg] at h
      | some gate =>
          simp only [hg] at h
          exact ⟨norm, gate, rfl, rfl, h⟩

theorem unavailable_gate_never_uses_zero_fallback (e : Engine) (decode : DecodeGates)
    (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (hg : gateResult (modelEngine e decode) decode c p = none) :
    verify e decode pin chain c p = .error .configuration := by
  simp only [verify]
  cases normResult (modelEngine e decode) c p <;> simp [hg]

theorem malformed_norm_adapter_rejected (e : Engine) (decode : DecodeGates)
    (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (hn : normResult (modelEngine e decode) c p = none) :
    verify e decode pin chain c p = .error .configuration := by simp [verify, hn]

theorem accepted_norm_shape_and_challenge_layout (e : Engine) (decode : DecodeGates)
    (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e decode pin chain c p = .ok ()) :
    (e.initialTranscript c p).logChallenges.length = 7 ∧
    Norm.shapeValid c (Norm.challengesFromInitial (e.initialTranscript c p))
      (normTerminalInput p) (derivedRounds e c p).logPoint = true := by
  obtain ⟨norm, _, hn, _, _⟩ := accepted_preflights_and_original_verifier e decode pin chain c p h
  have hs := Norm.checked_adapter_success c ((modelEngine e decode).initialTranscript c p)
    (normTerminalInput p) (derivedRounds (modelEngine e decode) c p).logPoint norm hn
  exact ⟨hs.1, hs.2.1⟩

theorem accepted_concrete_terminal_equations (e : Engine) (decode : DecodeGates)
    (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e decode pin chain c p = .ok ()) :
    ∃ norm gate,
      normResult (modelEngine e decode) c p = some norm ∧
      gateResult (modelEngine e decode) decode c p = some gate ∧
      norm = (derivedRounds e c p).logClaim ∧
      mul (Norm.eqEvaluation (e.initialTranscript c p).gateTau (derivedRounds e c p).gatePoint) gate =
        (derivedRounds e c p).gateClaim := by
  obtain ⟨norm, gate, hn, hg, hv⟩ := accepted_preflights_and_original_verifier e decode pin chain c p h
  have hs := verify_success_checks (modelEngine e decode) pin chain c p hv
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, hnorm, _, hgate⟩
  have hcalc := (Norm.checked_adapter_success c ((modelEngine e decode).initialTranscript c p)
    (normTerminalInput p) (derivedRounds (modelEngine e decode) c p).logPoint norm hn).2.2
  refine ⟨norm, gate, hn, hg, hcalc.trans hnorm, ?_⟩
  change mul (Norm.eqEvaluation (e.initialTranscript c p).gateTau (derivedRounds e c p).gatePoint)
    ((gateResult (modelEngine e decode) decode c p).getD zero) = (derivedRounds e c p).gateClaim at hgate
  simpa only [hg, Option.getD_some] using hgate

theorem accepted_retains_whir_root_claim_binding (e : Engine) (decode : DecodeGates)
    (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e decode pin chain c p = .ok ()) :
    verifyWhir (modelEngine e decode) (derivedContext (modelEngine e decode) c p) p = true := by
  obtain ⟨_, _, _, _, hv⟩ := accepted_preflights_and_original_verifier e decode pin chain c p h
  have hs := verify_success_checks (modelEngine e decode) pin chain c p hv
  exact hs.2.2.2.2.2.2.2.2.2.2.1

/-- Nonempty routed-wire and norm-helper example with an actual concrete norm
    evaluation. The initial/WHIR/metadata observations are intentionally test
    stand-ins, not a generated cryptographic proof or main deployment profile. -/
def exampleConfig : Config :=
  { testConfig with
    numRouted := 1, numGateConstraints := 0, indexBits := 1,
    kIs := [base 1], subgroupPowers := [base 1] }

def exampleProof : Proof :=
  { testProof with
    constituentWidth := 2,
    used := ⟨[zero, zero], [zero], [Norm.one, Norm.one], [zero, zero], [zero]⟩ }

def exampleEngine : Engine :=
  { testEngine with
    initialObservation := fun _ _ => ⟨[], [zero, Norm.one, zero, zero, zero, zero, zero], [zero], zero, [zero]⟩,
    sampleIndices := fun _ _ _ => ⟨[zero], [zero]⟩,
    publicInputsHash := fun _ => List.replicate 4 (base 0),
    parseWhir := fun ctx _ _ => some ⟨ctx.roots, ctx.roots, ctx.expectedClaims.map (fun x => x.getD zero)⟩ }

def exampleDecoder : DecodeGates := fun _ => some [⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩]

set_option maxRecDepth 4096 in
theorem positive_integrated_norm_helper_path :
    verify exampleEngine exampleDecoder ⟨1, testRoot, testRoot⟩ 1 exampleConfig exampleProof = .ok () := by
  rfl

end Audit.Wire3.Integrated
