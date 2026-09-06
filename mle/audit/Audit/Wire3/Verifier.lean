import Audit.Wire3.Packed

/-!
# Wire-v3 atomic verifier control flow

Source snapshot: becfe98e (the V2 API names carry wire protocol 3).
Correspondence: verifier_v2.rs; MleVerifierV2._verifyAtomic/_requireCanonicalProof;
OuterLogupExt3Verifier._verifyCoupledSumchecksUnchecked; PinnedMleVerifierV2;
WhirPCS.verify_grouped and SpongefishWhirVerify._phaseInitial.

This is an executable, manually transcribed boundary model, NOT a Rust/Solidity
semantics or cryptographic soundness proof. Canonical field values are a typed
input boundary. Bytes-to-values decoding, hashes/transcript, gate and norm
evaluators, packed constituent fold, canonical deployment validation, and the
WHIR tail are explicit function observations. None asserts a desired safety
conclusion. Equality of configuration hashes is NOT equality of configurations
without a separate collision-resistance/refinement argument. Constructor and
adapter-code-store integrity are outside this module.

The two implementations check the norm terminal at different positions; `verify`
uses Solidity terminal order but denotes a COMBINED DEPLOYMENT + CALL boundary.
Its envelope/deployment checks are call-time Rust checks, but Solidity performs
them in its constructor and subsequently compares the full configuration hash.
They are NOT additional Solidity runtime guards. `verifyCall` omits those two
guards; `checked_boundary_agrees_with_call` relates the boundaries only under
the explicit current-configuration deployment invariant. Establishing that
invariant from immutable configuration storage/hash binding is not proved here.
Exceptions/gas in observed functions are not EVM semantics.

`WhirContext.points` uses native WHIR coordinate order, exactly the complete
reversal performed by Solidity `_packedPoint`: reverse(index) ++ reverse(row).
Rust verifier_v2 initially passes row ++ index to verify_grouped, whose native
MultilinearExtension adapter performs that same complete reversal. The separate
constituent fold continues to use the original LSB-first index point.
-/

namespace Audit.Wire3.Verifier

abbrev modulus : Nat := Arithmetic.modulus
abbrev Base := Fin modulus
abbrev Bytes := List UInt8
abbrev Root := Fin (2 ^ 256)

def base (n : Nat) : Base := ⟨n % modulus, Nat.mod_lt _ (by decide)⟩

abbrev Ext3 := {a : Arithmetic.Ext3 // Arithmetic.Canonical a}

def zero : Ext3 := ⟨Arithmetic.zero, Arithmetic.zero_canonical⟩
def add (a b : Ext3) : Ext3 :=
  ⟨Arithmetic.eadd a.val b.val, Arithmetic.eadd_canonical _ _⟩
def sub (a b : Ext3) : Ext3 :=
  ⟨Arithmetic.esub a.val b.val, Arithmetic.esub_canonical _ _⟩
def mul (a b : Ext3) : Ext3 :=
  ⟨Arithmetic.emul a.val b.val, Arithmetic.emul_canonical _ _⟩
def scalar (a : Ext3) (s : Nat) : Ext3 :=
  ⟨Arithmetic.scalar a.val s, Arithmetic.scalar_canonical _ _⟩

theorem arithmetic_subtype_is_canonical (a : Ext3) : Arithmetic.Canonical a.val := a.property

theorem arithmetic_subtype_multiplication (a b : Ext3) :
    (mul a b).val = Arithmetic.emul a.val b.val := rfl

/-- Exact coefficient reconstruction/Horner algorithm; no sampled evaluations
    or independently supplied constant coefficient are accepted. Algebraic field
    laws and assembly refinement are separate obligations. -/
def evaluateRound (claim : Ext3) (coefficients : List Ext3) (challenge : Ext3) : Ext3 :=
  let a0 := scalar (sub claim (coefficients.foldl add zero)) ((modulus + 1) / 2)
  add (mul (coefficients.reverse.foldl (fun acc c => add (mul acc challenge) c) zero) challenge) a0

structure Config where
  degreeBits : Nat
  numConstants : Nat
  numRouted : Nat
  numWires : Nat
  numPublicInputs : Nat
  numSelectors : Nat
  numGateConstraints : Nat
  quotientDegree : Nat
  gateRows : Nat
  indexBits : Nat
  kIs : List Base
  subgroupPowers : List Base
  publicInputWireMap : Bytes
  gatesEncoding : Bytes
  whirEncoding : Bytes
  circuitDigest : List Base
  circuitConfigDigest : Root
  whirProtocolId : Bytes
  whirSessionId : Bytes
  deriving DecidableEq

def width (c : Config) : Nat := max (c.numConstants + c.numRouted) (max c.numWires (2 * c.numRouted))

/-- Reviewed numeric envelope. The precise metadata, canonical kIs/subgroup
    powers, supported-gate validation, and canonical WHIR profile are checked
    by `deploymentValid`, not postulated from this predicate alone. -/
def envelope (c : Config) : Bool := decide (
  0 < c.degreeBits ∧ c.degreeBits ≤ 13 ∧ 0 < width c ∧ width c ≤ 160 ∧
  c.numRouted ≤ 80 ∧ c.numRouted ≤ c.numWires ∧ c.numPublicInputs ≤ 256 ∧
  0 < c.numSelectors ∧ c.numSelectors ≤ c.numConstants ∧ c.numGateConstraints ≤ 123 ∧
  0 < c.quotientDegree ∧ c.quotientDegree + 2 ≤ 10 ∧ 0 < c.gateRows ∧ c.gateRows ≤ 255 ∧
  c.kIs.length = c.numRouted ∧ c.subgroupPowers.length = c.degreeBits ∧
  c.publicInputWireMap.length = 3 * c.numPublicInputs ∧ c.circuitDigest.length = 4 ∧
  c.indexBits ≤ 8 ∧ width c ≤ 2 ^ c.indexBits ∧
  (c.indexBits = 0 ∨ 2 ^ (c.indexBits - 1) < width c))

structure Pinned where
  chainId : Nat
  configDigest : Root
  preprocessedRoot : Root

structure UsedClaims where
  logPreprocessed : List Ext3
  logWitness : List Ext3
  logNormInverse : List Ext3
  gatePreprocessed : List Ext3
  gateWitness : List Ext3
  deriving DecidableEq

structure Proof where
  protocolVersion : Nat
  constituentWidth : Nat
  circuitDigest : List Base
  publicInputs : List Base
  preprocessedRoot : Root
  witnessRoot : Root
  normInverseRoot : Root
  logRounds : List (List Ext3)
  gateRounds : List (List Ext3)
  used : UsedClaims
  whirTranscript : Bytes
  whirHints : Bytes

def shape (pin : Pinned) (c : Config) (p : Proof) : Bool := decide (
  p.protocolVersion = 3 ∧ p.constituentWidth = width c ∧ p.circuitDigest = c.circuitDigest ∧
  p.publicInputs.length = c.numPublicInputs ∧ p.preprocessedRoot = pin.preprocessedRoot ∧
  p.whirTranscript.length ≤ 1904 ∧ p.whirHints.length ≤ 112408 ∧
  p.used.logPreprocessed.length = c.numConstants + c.numRouted ∧
  p.used.logWitness.length = c.numWires ∧ p.used.logNormInverse.length = 2 * c.numRouted ∧
  p.used.gatePreprocessed.length = c.numConstants + c.numRouted ∧
  p.used.gateWitness.length = c.numWires ∧
  p.logRounds.length = c.degreeBits ∧ p.gateRounds.length = c.degreeBits ∧
  (p.logRounds.all (fun r => decide (r.length = 5))) = true ∧
  (p.gateRounds.all (fun r => decide (r.length = c.quotientDegree + 2))) = true)

structure Initial where
  transcript : Bytes
  logChallenges : List Ext3
  logTau : List Ext3
  gateAlpha : Ext3
  gateTau : List Ext3

structure RoundChallenges where
  transcript : Bytes
  log : Ext3
  gate : Ext3

structure RoundState where
  transcript : Bytes
  roundIndex : Nat
  logClaim : Ext3
  gateClaim : Ext3
  logPoint : List Ext3
  gatePoint : List Ext3
  deriving DecidableEq

abbrev CoupledMessage := List Ext3 × List Ext3
abbrev CommitRound := Bytes → Nat → List Ext3 → List Ext3 → RoundChallenges

def start (i : Initial) : RoundState := ⟨i.transcript, 0, zero, zero, [], []⟩

/-- Both messages are arguments to a single challenge-generating observation.
    The model has no log-only/gate-only transition API. -/
def roundStep (commit : CommitRound) (s : RoundState) (m : CoupledMessage) : RoundState :=
  let r := commit s.transcript s.roundIndex m.1 m.2
  ⟨r.transcript, s.roundIndex + 1,
   evaluateRound s.logClaim m.1 r.log, evaluateRound s.gateClaim m.2 r.gate,
   s.logPoint ++ [r.log], s.gatePoint ++ [r.gate]⟩

def runRounds (commit : CommitRound) : RoundState → List CoupledMessage → RoundState
  | s, [] => s
  | s, m :: ms => runRounds commit (roundStep commit s m) ms

/-- An inductive history of the actual executable transitions, not a record of
    asserted acceptance conclusions. -/
inductive RoundChain (commit : CommitRound) : RoundState → List CoupledMessage → RoundState → Prop
  | nil (s) : RoundChain commit s [] s
  | cons (s m ms t) : RoundChain commit (roundStep commit s m) ms t →
      RoundChain commit s (m :: ms) t

theorem runRounds_has_chain (commit : CommitRound) (s : RoundState) (ms : List CoupledMessage) :
    RoundChain commit s ms (runRounds commit s ms) := by
  induction ms generalizing s with
  | nil => exact .nil s
  | cons m ms ih => exact .cons s m ms _ (ih _)

theorem chain_unique_result (commit : CommitRound) {s t : RoundState} {ms : List CoupledMessage}
    (h : RoundChain commit s ms t) : t = runRounds commit s ms := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ ih => exact ih

theorem runRounds_append (commit : CommitRound) (s : RoundState) (a b : List CoupledMessage) :
    runRounds commit s (a ++ b) = runRounds commit (runRounds commit s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons _ _ ih => exact ih _

theorem runRounds_lengths (commit : CommitRound) (s : RoundState) (ms : List CoupledMessage) :
    (runRounds commit s ms).roundIndex = s.roundIndex + ms.length ∧
    (runRounds commit s ms).logPoint.length = s.logPoint.length + ms.length ∧
    (runRounds commit s ms).gatePoint.length = s.gatePoint.length + ms.length := by
  induction ms generalizing s with
  | nil => simp [runRounds]
  | cons m ms ih =>
      simpa [runRounds, roundStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (roundStep commit s m)

theorem roundStep_uses_both_messages (commit : CommitRound) (s : RoundState) (m : CoupledMessage) :
    (roundStep commit s m).logClaim = evaluateRound s.logClaim m.1
      (commit s.transcript s.roundIndex m.1 m.2).log ∧
    (roundStep commit s m).gateClaim = evaluateRound s.gateClaim m.2
      (commit s.transcript s.roundIndex m.1 m.2).gate := by
  exact ⟨rfl, rfl⟩

structure IndexPoints where
  log : List Ext3
  gate : List Ext3

structure WhirContext where
  protocolId : Bytes
  sessionId : Bytes
  parameters : Bytes
  numVariables : Nat
  roots : List Root
  points : List (List Arithmetic.Ext3)
  expectedClaims : List (Option Ext3)
  deriving DecidableEq

abbrev FoldClaim := List Ext3 → Nat → List Ext3 → Ext3

def expectedClaims (foldClaim : FoldClaim) (c : Config) (p : Proof) (idx : IndexPoints) : List (Option Ext3) :=
  [some (foldClaim p.used.logPreprocessed (width c) idx.log),
   some (foldClaim p.used.logWitness (width c) idx.log),
   some (foldClaim p.used.logNormInverse (width c) idx.log),
   some (foldClaim p.used.gatePreprocessed (width c) idx.gate),
   some (foldClaim p.used.gateWitness (width c) idx.gate), none]

def whirContext (foldClaim : FoldClaim) (c : Config) (p : Proof) (s : RoundState) (idx : IndexPoints) : WhirContext :=
  ⟨c.whirProtocolId, c.whirSessionId, c.whirEncoding, c.degreeBits + c.indexBits,
   [p.preprocessedRoot, p.witnessRoot, p.normInverseRoot],
   [Packed.whirPoint (s.logPoint.map Subtype.val) (idx.log.map Subtype.val),
    Packed.whirPoint (s.gatePoint.map Subtype.val) (idx.gate.map Subtype.val)],
   expectedClaims foldClaim c p idx⟩

theorem context_three_roots_two_points_six_claims (foldClaim : FoldClaim) (c : Config)
    (p : Proof) (s : RoundState) (idx : IndexPoints) :
    (whirContext foldClaim c p s idx).roots.length = 3 ∧
    (whirContext foldClaim c p s idx).points.length = 2 ∧
    (whirContext foldClaim c p s idx).expectedClaims.length = 6 := by
  exact ⟨rfl, rfl, rfl⟩

theorem context_bound_mask_exact (foldClaim : FoldClaim) (c : Config) (p : Proof) (idx : IndexPoints) :
    (expectedClaims foldClaim c p idx).map Option.isSome = [true, true, true, true, true, false] := by
  rfl

theorem context_unused_gate_norm_is_unbound (foldClaim : FoldClaim) (c : Config) (p : Proof)
    (idx : IndexPoints) : (expectedClaims foldClaim c p idx).get? 5 = some none := by
  rfl

theorem context_native_coordinate_order (foldClaim : FoldClaim) (c : Config) (p : Proof)
    (s : RoundState) (idx : IndexPoints) :
    (whirContext foldClaim c p s idx).points =
      [(idx.log.map Subtype.val).reverse ++ (s.logPoint.map Subtype.val).reverse,
       (idx.gate.map Subtype.val).reverse ++ (s.gatePoint.map Subtype.val).reverse] := by
  simp [whirContext, Packed.whirPoint, Packed.packedPoint]

structure ParsedWhir where
  actualRoots : List Root
  boundRoots : List Root
  claims : List Ext3

/-- The initial challenge observation cannot inspect future round messages,
    claimed constituent evaluations, or WHIR proof bytes. Internal ordering of
    the norm-root absorption relative to beta/gamma still requires transcript
    refinement; this type alone does not establish Fiat--Shamir security. -/
structure Statement where
  circuitDigest : List Base
  publicInputs : List Base
  preprocessedRoot : Root
  witnessRoot : Root
  normInverseRoot : Root

def statement (p : Proof) : Statement :=
  ⟨p.circuitDigest, p.publicInputs, p.preprocessedRoot, p.witnessRoot, p.normInverseRoot⟩

structure NormTerminalInput where
  preprocessed : List Ext3
  witness : List Ext3
  normInverse : List Ext3
  publicInputs : List Base

def normTerminalInput (p : Proof) : NormTerminalInput :=
  ⟨p.used.logPreprocessed, p.used.logWitness, p.used.logNormInverse, p.publicInputs⟩

def claimsMatch : List (Option Ext3) → List Ext3 → Bool
  | [], [] => true
  | some x :: xs, y :: ys => decide (x = y) && claimsMatch xs ys
  | none :: xs, _ :: ys => claimsMatch xs ys
  | _, _ => false

def rootsAndClaimsMatch (ctx : WhirContext) (parsed : ParsedWhir) : Bool :=
  decide (parsed.actualRoots = ctx.roots ∧ parsed.boundRoots = ctx.roots) &&
  claimsMatch ctx.expectedClaims parsed.claims

theorem rootsAndClaimsMatch_binds_both_root_copies (ctx : WhirContext) (parsed : ParsedWhir)
    (h : rootsAndClaimsMatch ctx parsed = true) :
    parsed.actualRoots = ctx.roots ∧ parsed.boundRoots = ctx.roots := by
  simp only [rootsAndClaimsMatch, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem claimsMatch_preserves_length {xs : List (Option Ext3)} {ys : List Ext3}
    (h : claimsMatch xs ys = true) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [claimsMatch]
  | cons x xs ih =>
      cases ys with
      | nil => simp [claimsMatch] at h
      | cons y ys =>
          cases x with
          | none => exact congrArg Nat.succ (ih h)
          | some x =>
              simp only [claimsMatch, Bool.and_eq_true, decide_eq_true_eq] at h
              exact congrArg Nat.succ (ih h.2)

theorem claimsMatch_bound_head {x y : Ext3} {xs : List (Option Ext3)} {ys : List Ext3}
    (h : claimsMatch (some x :: xs) (y :: ys) = true) : x = y := by
  simp only [claimsMatch, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Function observations must eventually be refined against their concrete
    implementations. `whirTail` includes OOD checks, Merkle queries, all WHIR
    sumchecks, authenticated terminal-row/final-polynomial consistency, final
    claim and exact EOF. Acceptance here does not prove those internals. -/
structure Engine where
  configurationHash : Config → Root
  deploymentValid : Config → Bool
  initialObservation : Config → Statement → Initial
  commitRound : CommitRound
  sampleIndices : Bytes → UsedClaims → Nat → IndexPoints
  foldClaim : FoldClaim
  normEvaluation : Config → Initial → NormTerminalInput → List Ext3 → Ext3
  publicInputsHash : List Base → List Base
  gateEvaluation : Config → List Ext3 → List Ext3 → List Base → Ext3 → Ext3
  eqEvaluation : List Ext3 → List Ext3 → Ext3
  parseWhir : WhirContext → Bytes → Bytes → Option ParsedWhir
  whirTail : WhirContext → Bytes → Bytes → ParsedWhir → Bool

def Engine.initialTranscript (e : Engine) (c : Config) (p : Proof) : Initial :=
  e.initialObservation c (statement p)

def Engine.logTerminal (e : Engine) (c : Config) (i : Initial) (p : Proof) (point : List Ext3) : Ext3 :=
  e.normEvaluation c i (normTerminalInput p) point

def verifyWhir (e : Engine) (ctx : WhirContext) (p : Proof) : Bool :=
  match e.parseWhir ctx p.whirTranscript p.whirHints with
  | none => false
  | some parsed => rootsAndClaimsMatch ctx parsed && e.whirTail ctx p.whirTranscript p.whirHints parsed

theorem whir_acceptance_requires_bound_statement (e : Engine) (ctx : WhirContext) (p : Proof)
    (h : verifyWhir e ctx p = true) :
    ∃ parsed, e.parseWhir ctx p.whirTranscript p.whirHints = some parsed ∧
      parsed.actualRoots = ctx.roots ∧ parsed.boundRoots = ctx.roots ∧
      claimsMatch ctx.expectedClaims parsed.claims = true ∧
      e.whirTail ctx p.whirTranscript p.whirHints parsed = true := by
  unfold verifyWhir at h
  cases hp : e.parseWhir ctx p.whirTranscript p.whirHints with
  | none => simp [hp] at h
  | some parsed =>
      simp only [hp, Bool.and_eq_true] at h
      have hr := rootsAndClaimsMatch_binds_both_root_copies ctx parsed h.1
      have hc := h.1
      simp only [rootsAndClaimsMatch, Bool.and_eq_true] at hc
      exact ⟨parsed, rfl, hr.1, hr.2, hc.2, h.2⟩

def derivedRounds (e : Engine) (c : Config) (p : Proof) : RoundState :=
  runRounds e.commitRound (start (e.initialTranscript c p)) (p.logRounds.zip p.gateRounds)

def derivedIndices (e : Engine) (c : Config) (p : Proof) : IndexPoints :=
  e.sampleIndices (derivedRounds e c p).transcript p.used c.indexBits

def derivedContext (e : Engine) (c : Config) (p : Proof) : WhirContext :=
  whirContext e.foldClaim c p (derivedRounds e c p) (derivedIndices e c p)

def gateTerminal (e : Engine) (c : Config) (p : Proof) : Ext3 :=
  let i := e.initialTranscript c p
  mul (e.eqEvaluation i.gateTau (derivedRounds e c p).gatePoint)
    (e.gateEvaluation c p.used.gateWitness (p.used.gatePreprocessed.take c.numConstants)
      (e.publicInputsHash p.publicInputs) i.gateAlpha)

inductive Error where
  | unavailable | configuration | invalidProof
  deriving DecidableEq, Repr

/-- Combined successful deployment/context validation and call boundary after
    canonical typed decoding. `envelope` and `deploymentValid` are NOT repeated
    Solidity runtime checks; use `verifyCall` plus an explicit deployment
    invariant when applying these theorems to that path. Fixed deployment state
    has no update operation. No legacy branch or caller-supplied row/index
    point, challenge, public-input hash, or final claim is a proof field. -/
def verify (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof) : Except Error Unit :=
  if chain ≠ pin.chainId then .error .unavailable
  else if e.configurationHash c ≠ pin.configDigest ∨ envelope c = false ∨ e.deploymentValid c = false then
    .error .configuration
  else if shape pin c p = false then .error .invalidProof
  else
    let i := e.initialTranscript c p
    let s := derivedRounds e c p
    let idx := derivedIndices e c p
    if i.logTau.length ≠ c.degreeBits ∨ i.gateTau.length ≠ c.degreeBits ∨
        idx.log.length ≠ c.indexBits ∨ idx.gate.length ≠ c.indexBits then .error .configuration
    else if e.logTerminal c i p s.logPoint ≠ s.logClaim then .error .invalidProof
    else if verifyWhir e (derivedContext e c p) p = false then .error .invalidProof
    else if gateTerminal e c p ≠ s.gateClaim then .error .invalidProof
    else .ok ()

/-- Solidity's modeled call boundary: deployment-only validation is absent.
    The remaining dimension checks on observation outputs model contracts of
    transcript helpers, not separately executed guards. This is still a manual
    success-boundary model, not a bytecode/exception-order refinement. -/
def verifyCall (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof) : Except Error Unit :=
  if chain ≠ pin.chainId then .error .unavailable
  else if e.configurationHash c ≠ pin.configDigest then .error .configuration
  else if shape pin c p = false then .error .invalidProof
  else
    let i := e.initialTranscript c p
    let s := derivedRounds e c p
    let idx := derivedIndices e c p
    if i.logTau.length ≠ c.degreeBits ∨ i.gateTau.length ≠ c.degreeBits ∨
        idx.log.length ≠ c.indexBits ∨ idx.gate.length ≠ c.indexBits then .error .configuration
    else if e.logTerminal c i p s.logPoint ≠ s.logClaim then .error .invalidProof
    else if verifyWhir e (derivedContext e c p) p = false then .error .invalidProof
    else if gateTerminal e c p ≠ s.gateClaim then .error .invalidProof
    else .ok ()

theorem checked_boundary_agrees_with_call (e : Engine) (pin : Pinned) (chain : Nat) (c : Config)
    (p : Proof) (henv : envelope c = true) (hdeployment : e.deploymentValid c = true) :
    verify e pin chain c p = verifyCall e pin chain c p := by
  simp [verify, verifyCall, henv, hdeployment]

/-- The deployment invariant is a visible hypothesis, not obtained from
    configuration-hash equality or smuggled into a Solidity runtime guard. -/
theorem call_acceptance_yields_checked_acceptance (e : Engine) (pin : Pinned) (chain : Nat)
    (c : Config) (p : Proof) (henv : envelope c = true) (hdeployment : e.deploymentValid c = true)
    (hcall : verifyCall e pin chain c p = .ok ()) : verify e pin chain c p = .ok () := by
  rw [checked_boundary_agrees_with_call e pin chain c p henv hdeployment]
  exact hcall

theorem verify_success_checks (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e pin chain c p = .ok ()) :
    chain = pin.chainId ∧ e.configurationHash c = pin.configDigest ∧ envelope c = true ∧
    e.deploymentValid c = true ∧ shape pin c p = true ∧
    (e.initialTranscript c p).logTau.length = c.degreeBits ∧
    (e.initialTranscript c p).gateTau.length = c.degreeBits ∧
    (derivedIndices e c p).log.length = c.indexBits ∧
    (derivedIndices e c p).gate.length = c.indexBits ∧
    e.logTerminal c (e.initialTranscript c p) p (derivedRounds e c p).logPoint =
      (derivedRounds e c p).logClaim ∧
    verifyWhir e (derivedContext e c p) p = true ∧
    gateTerminal e c p = (derivedRounds e c p).gateClaim := by
  simp only [verify] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all

theorem acceptance_protocol_and_pinned_root (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e pin chain c p = .ok ()) :
    p.protocolVersion = 3 ∧ p.preprocessedRoot = pin.preprocessedRoot := by
  have hs := (verify_success_checks e pin chain c p h).2.2.2.2.1
  simp only [shape, decide_eq_true_eq] at hs
  exact ⟨hs.1, hs.2.2.2.2.1⟩

theorem acceptance_has_no_zero_round_bypass (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e pin chain c p = .ok ()) : 0 < c.degreeBits := by
  have he := (verify_success_checks e pin chain c p h).2.2.1
  simp only [envelope, decide_eq_true_eq] at he
  exact he.1

theorem acceptance_exact_round_shapes (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e pin chain c p = .ok ()) :
    p.logRounds.length = c.degreeBits ∧ p.gateRounds.length = c.degreeBits ∧
    p.logRounds.all (fun r => decide (r.length = 5)) = true ∧
    p.gateRounds.all (fun r => decide (r.length = c.quotientDegree + 2)) = true := by
  have hs := (verify_success_checks e pin chain c p h).2.2.2.2.1
  simp only [shape, decide_eq_true_eq] at hs
  exact hs.2.2.2.2.2.2.2.2.2.2.2.2

theorem acceptance_coupled_point_lengths (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : verify e pin chain c p = .ok ()) :
    (derivedRounds e c p).logPoint.length = c.degreeBits ∧
    (derivedRounds e c p).gatePoint.length = c.degreeBits := by
  have hr := acceptance_exact_round_shapes e pin chain c p h
  have hl := runRounds_lengths e.commitRound (start (e.initialTranscript c p))
    (p.logRounds.zip p.gateRounds)
  simpa [derivedRounds, start, List.length_zip, hr.1, hr.2.1] using hl.2

theorem acceptance_has_complete_coupled_history (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (_h : verify e pin chain c p = .ok ()) :
    RoundChain e.commitRound (start (e.initialTranscript c p)) (p.logRounds.zip p.gateRounds)
      (derivedRounds e c p) := by
  exact runRounds_has_chain _ _ _

theorem acceptance_packed_points_have_configured_dimension (e : Engine) (pin : Pinned) (chain : Nat)
    (c : Config) (p : Proof) (h : verify e pin chain c p = .ok ()) :
    (derivedContext e c p).points.map List.length =
      [c.degreeBits + c.indexBits, c.degreeBits + c.indexBits] := by
  have hs := verify_success_checks e pin chain c p h
  have hl := acceptance_coupled_point_lengths e pin chain c p h
  have hiLog := hs.2.2.2.2.2.2.2.1
  have hiGate := hs.2.2.2.2.2.2.2.2.1
  simp [derivedContext, whirContext, Packed.whirPoint, Packed.packedPoint,
    hl.1, hl.2, hiLog, hiGate, Nat.add_comm]

theorem acceptance_exact_whir_and_terminal_binding (e : Engine) (pin : Pinned) (chain : Nat)
    (c : Config) (p : Proof) (h : verify e pin chain c p = .ok ()) :
    ∃ parsed, e.parseWhir (derivedContext e c p) p.whirTranscript p.whirHints = some parsed ∧
      parsed.actualRoots = [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      parsed.boundRoots = [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      claimsMatch (expectedClaims e.foldClaim c p (derivedIndices e c p)) parsed.claims = true ∧
      e.whirTail (derivedContext e c p) p.whirTranscript p.whirHints parsed = true ∧
      e.normEvaluation c (e.initialTranscript c p) (normTerminalInput p)
        (derivedRounds e c p).logPoint = (derivedRounds e c p).logClaim ∧
      gateTerminal e c p = (derivedRounds e c p).gateClaim := by
  have hs := verify_success_checks e pin chain c p h
  have ht := hs.2.2.2.2.2.2.2.2.2
  have hw := whir_acceptance_requires_bound_statement e (derivedContext e c p) p ht.2.1
  obtain ⟨parsed, hp, ha, hb, hc, hw⟩ := hw
  have hr := (acceptance_protocol_and_pinned_root e pin chain c p h).2
  exact ⟨parsed, hp, by simpa [derivedContext, whirContext, hr] using ha,
    by simpa [derivedContext, whirContext, hr] using hb, hc, hw, ht.1, ht.2.2⟩

theorem unavailable_precedes_proof_checks (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (h : chain ≠ pin.chainId) : verify e pin chain c p = .error .unavailable := by
  simp [verify, h]

theorem mismatched_configuration_never_accepts (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (p : Proof)
    (hc : e.configurationHash c ≠ pin.configDigest) : verify e pin chain c p ≠ .ok () := by
  intro h
  exact hc (verify_success_checks e pin chain c p h).2.1

/-- Adapter decoding is observed, but successful returned PIs are from the same
    decoded proof passed to the complete pinned core model. -/
def verifyCompactPublicInputs (decode : Config → Bytes → Except Error Proof) (e : Engine)
    (pin : Pinned) (chain : Nat) (c : Config) (raw : Bytes) : Except Error (List Base) :=
  if chain ≠ pin.chainId then .error .unavailable
  else match decode c raw with
    | .error err => .error err
    | .ok p => match verify e pin chain c p with
      | .error err => .error err
      | .ok () => .ok p.publicInputs

theorem returned_public_inputs_require_full_verification (decode : Config → Bytes → Except Error Proof)
    (e : Engine) (pin : Pinned) (chain : Nat) (c : Config) (raw : Bytes) (pis : List Base)
    (h : verifyCompactPublicInputs decode e pin chain c raw = .ok pis) :
    ∃ p, decode c raw = .ok p ∧ verify e pin chain c p = .ok () ∧ pis = p.publicInputs := by
  unfold verifyCompactPublicInputs at h
  split at h
  · simp_all
  · cases hd : decode c raw with
    | error err => simp [hd] at h
    | ok p =>
        cases hv : verify e pin chain c p with
        | error err => simp [hd, hv] at h
        | ok value =>
            cases value
            simp [hd, hv] at h
            exact ⟨p, rfl, hv, h.symm⟩

/-! Closed positive model test. The observation functions below intentionally
    accept a trivial boundary instance. This establishes non-vacuity of the
    executable control-flow model, NOT existence of a concrete WHIR proof. -/

def testRoot : Root := ⟨0, by decide⟩

def testConfig : Config :=
  { degreeBits := 1, numConstants := 1, numRouted := 0, numWires := 1,
    numPublicInputs := 0, numSelectors := 1, numGateConstraints := 1,
    quotientDegree := 1, gateRows := 1, indexBits := 0,
    kIs := [], subgroupPowers := [base 0], publicInputWireMap := [],
    gatesEncoding := [], whirEncoding := [], circuitDigest := List.replicate 4 (base 0),
    circuitConfigDigest := testRoot, whirProtocolId := [], whirSessionId := [] }

def testProof : Proof :=
  { protocolVersion := 3, constituentWidth := 1, circuitDigest := testConfig.circuitDigest,
    publicInputs := [], preprocessedRoot := testRoot, witnessRoot := testRoot, normInverseRoot := testRoot,
    logRounds := [List.replicate 5 zero], gateRounds := [List.replicate 3 zero],
    used := ⟨[zero], [zero], [], [zero], [zero]⟩, whirTranscript := [], whirHints := [] }

def testEngine : Engine :=
  { configurationHash := fun _ => testRoot, deploymentValid := fun _ => true,
    initialObservation := fun _ _ => ⟨[], [], [zero], zero, [zero]⟩,
    commitRound := fun _ _ _ _ => ⟨[], zero, zero⟩,
    sampleIndices := fun _ _ _ => ⟨[], []⟩, foldClaim := fun _ _ _ => zero,
    normEvaluation := fun _ _ _ _ => zero, publicInputsHash := fun _ => [],
    gateEvaluation := fun _ _ _ _ _ => zero, eqEvaluation := fun _ _ => zero,
    parseWhir := fun ctx _ _ => some ⟨ctx.roots, ctx.roots, List.replicate 6 zero⟩,
    whirTail := fun _ _ _ _ => true }

theorem positive_model_verification :
    verify testEngine ⟨1, testRoot, testRoot⟩ 1 testConfig testProof = .ok () := by
  rfl

theorem positive_model_compact_public_inputs :
    verifyCompactPublicInputs (fun _ _ => .ok testProof) testEngine
      ⟨1, testRoot, testRoot⟩ 1 testConfig [] = .ok [] := by
  rfl

end Audit.Wire3.Verifier
