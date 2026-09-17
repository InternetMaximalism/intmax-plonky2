import Audit.Wire3.WhirTailWitness

/-!
# The first REJECTION of a wrong proof in this tree

## What this module does

Every concrete `Verifier.verify` result adopted so far is an ACCEPTANCE:
`Verifier.positive_model_verification`, `DerivedAcceptance`'s runs,
`DigestRoutedAcceptance.alt_proof_is_still_accepted`, and
`WhirTailWitness.installed_whir_pair_accepts_a_full_verification`.  This module
supplies the missing half of the pair: a proof the SAME verifier, at the SAME
configuration and the SAME engine, REJECTS.

* `wrongRootProof` is `WhirTailWitness.sixProof` with exactly ONE field changed:
  `normInverseRoot`, moved from `Verifier.testRoot = 0` to `wrongRoot = 1`
  (`the_two_proofs_differ_in_exactly_one_field`).
* `installed_engine_rejects_the_wrong_root_proof` --
  `Verifier.verify installedEngine
   ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig wrongRootProof
   = .error .invalidProof`, by `rfl`, exactly as its accepting twin is `rfl`.
* `the_separation_pair` states both halves together.

## WHY `normInverseRoot`, and WHICH gate fires

`Verifier.whirContext` (Verifier.lean:249) builds the WHIR context's root list
as `[p.preprocessedRoot, p.witnessRoot, p.normInverseRoot]` -- straight from the
proof's statement.  `Verifier.shape` (Verifier.lean:134) pins
`p.preprocessedRoot` to `pin.preprocessedRoot`, so changing THAT root is caught
by the shape gate and proves nothing about WHIR.  `witnessRoot` and
`normInverseRoot` are both unpinned and both flow into the context;
`normInverseRoot` is the one chosen here because it mirrors the adopted
`DigestRoutedAcceptance` alt-proof story.  `wrong_root_changes_only_the_third
_context_root` shows precisely what the change does to the derived context.

The gate that fires is the WHIR gate, and `rejection_is_located_at_the_whir
_gate` attributes it: every earlier gate of `Verifier.verify` passes on
`wrongRootProof` (chain id, configuration hash, envelope, deployment validity,
`shape`, the four dimension checks, and the log-terminal binding), the LATER
gate-terminal binding passes too, and `Verifier.verifyWhir` at the derived
context is `false`.  So the rejection is attributable to the WHIR gate alone.

**Inside that gate, the root comparison is what bites, and it bites in the
PARSE.**  `parse_of_the_wrong_root_proof_is_none` shows
`InstalledWhirParse.concreteParseWhir` returns `none` at the wrong-root context:
the installed parse reads the commitment roots from the TRANSCRIPT BYTES and
checks them against `InstalledWhirParse.parseRoots ctx`, so a statement root
that the transcript does not carry kills the parse before
`Verifier.rootsAndClaimsMatch` is reached.  That is the adopted
`InstalledWhirParse.roots_and_claims_match_reduces_to_claims` read from the
other side: on this engine the root binding is not performed by
`rootsAndClaimsMatch`, it is performed by the parse, and
`rootsAndClaimsMatch`'s root half is then redundant.  The check is the same
check; this module records WHERE it lives.

## What this does and does NOT mean

This is the first two-proof separation in the tree: one proof accepted, one
rejected, by one verifier call each, differing in one field.  It is a statement
about the MODEL of the installed parse, not about deployed Solidity.

It runs under exactly the restrictions its accepting twin runs under:

* `Verifier.testConfig`, ONE packed variable, not
  `DerivedAcceptance.derivedConfig`'s twenty-one
  (`WhirTailWitness.the_accepting_configuration_is_not_the_derived_one`);
* `InstalledWhirTail.exampleHash`, the constant toy hash
  (`WhirTailWitness.the_witness_hash_is_constant`);
* `WhirConfigured.exampleNoRounds`, a profile with no intermediate round and
  every proof-of-work threshold disabled
  (`WhirTailWitness.the_witness_profile_is_not_the_deployed_shape`);
* `WhirTailWitness.sixEngine`, whose `initialObservation`, `publicInputsHash`,
  `configurationHash` and `deploymentValid` are still `Verifier.testEngine`'s
  abstract observations (`WhirTailWitness.accepting_engine_field_ledger`), NOT
  `ExplicitEngine.explicitEngine`.

This module proves nothing at `DerivedAcceptance.derivedConfig` and nothing at
`ExplicitEngine.explicitEngine`; every theorem below names the engine and the
configuration it runs at, and none of them names those.

## The contrast that makes the point

`fixtureWhirSixEngine` is `installedEngine` with the WHIR pair put back to the
FIXTURE pair -- `Verifier.testEngine`'s `parseWhir`, which returns the context's
own roots by construction, and its `whirTail`, which is `fun _ _ _ _ => true`.
That is the pre-repair shape, and the shape `DerivedAcceptance` runs at.  At it,
`fixture_whir_pair_accepts_the_wrong_root_proof` -- the SAME wrong proof is
ACCEPTED.  `installing_the_whir_pair_is_what_rejects` puts the two side by side.

**The sharpened attribution.**  EACH HALF OF THE WHIR PAIR ALONE ALREADY
REJECTS, and acceptance of the forgery requires BOTH halves to be the fixture's.
`probe_installed_parse_alone_rejects` runs the installed parse against the
FIXTURE tail and still rejects; `probe_installed_tail_alone_rejects` runs the
FIXTURE parse against the installed tail and still rejects; and each half alone
still accepts the honest proof
(`probe_installed_parse_alone_accepts_the_honest_proof`,
`probe_installed_tail_alone_accepts_the_honest_proof`), so each half alone is a
genuine separation.  Hence the wrong proof is rejected exactly when the parse is
installed -- and equally, exactly when the tail is.  That is why this is the
practically decisive check: only a verifier whose parse echoes the context AND
whose tail is the constant `true` accepts both proofs of this pair, which is the
shape the audit's record attributes the pre-repair forgeries to.

**Confounder elimination.**  `probe_only_the_roots_change` shows that every
other argument `prefixRun` receives -- the context parameters, the parse claims,
the protocol and session identifiers, the variable count, the points, the
expected claims, the root-list LENGTH, and the proof's transcript and hint bytes
-- is LITERALLY the accepting one, while `probe_the_root_list_differs` shows the
root list really differs; `probe_restoring_the_roots_restores_the_parse` puts the
roots back, touching nothing else, and the parse succeeds again.  So the
rejection is attributable to the root bytes and to nothing else.

**Which root.**  `normInverseRoot` is one instance, not the mechanism: the
honest general statement is "the statement roots the parse reads".  The other
unpinned root behaves identically -- `probe_wrong_witness_root_is_also_rejected`
and `probe_fixture_pair_accepts_the_wrong_witness_root_too` repeat the whole
separation with `witnessRoot` forged instead.

## Generality

`acceptance_pins_the_statement_roots_to_the_transcript` is the quantified form
that landed: for EVERY proof `p` this engine accepts, the WHIR prefix executes
on `p`'s own bytes and the commitment roots that execution read are exactly the
digests of `p`'s three statement roots.  It quantifies over all proofs and over
`gdec`, and its hypothesis is satisfied at `WhirTailWitness.sixProof` by the
adopted acceptance theorem (`acceptance_hypothesis_is_satisfiable`), so it is
not vacuous.  The fully quantified INSTANCE form -- "for every root `r ≠ 0`, the
proof carrying `r` is rejected" -- is not shipped: what is shipped instead is
this transcript-binding statement plus two root instances (`normInverseRoot` and
`witnessRoot`).

`probe_root_digest_is_injective` removes one obstacle to the family form:
`Verifier.Root = Fin (2 ^ 256)` and `InstalledWhirTail.rootDigest` is injective
(via `Transcript.le_injective_bounded`), so distinct roots have distinct digests
and the family form has no same-digest edge case.

What still blocks the family form is a NAMED MISSING LEMMA, not an
impossibility: the binding theorem's expected commitment list moves with `r`, so
closing the family needs a local lemma exporting the byte equation from
`WhirInitial.receiveOne` -- its line 59 forces `expected = root`, but the adopted
`receive_one_success` does NOT export that equation -- together with threading
the third commitment's offset through `phase_initial_trace`.  No adopted lemma
exports the byte equation, so the family form is not a one-liner here; it is
estimated at 40-80 lines of new local work and is left to a successor module.
-/

namespace Audit.Wire3.RejectionWitness

open Audit.Wire3

/-! ## 1. The wrong proof -/

/-- A statement root different from `Verifier.testRoot = 0`. -/
def wrongRoot : Verifier.Root := ⟨1, by decide⟩

theorem wrong_root_is_not_the_pinned_root : wrongRoot ≠ Verifier.testRoot := by decide

/-- `WhirTailWitness.sixProof` with exactly ONE field changed: the norm-inverse
statement root.  `Verifier.shape` does not pin this root, so the shape gate
cannot be what rejects it. -/
def wrongRootProof : Verifier.Proof :=
  { WhirTailWitness.sixProof with normInverseRoot := wrongRoot }

/-- The two proofs agree on every field of `Verifier.Proof` except
`normInverseRoot`, where they differ. -/
theorem the_two_proofs_differ_in_exactly_one_field :
    wrongRootProof.protocolVersion = WhirTailWitness.sixProof.protocolVersion ∧
    wrongRootProof.constituentWidth = WhirTailWitness.sixProof.constituentWidth ∧
    wrongRootProof.circuitDigest = WhirTailWitness.sixProof.circuitDigest ∧
    wrongRootProof.publicInputs = WhirTailWitness.sixProof.publicInputs ∧
    wrongRootProof.preprocessedRoot = WhirTailWitness.sixProof.preprocessedRoot ∧
    wrongRootProof.witnessRoot = WhirTailWitness.sixProof.witnessRoot ∧
    wrongRootProof.logRounds = WhirTailWitness.sixProof.logRounds ∧
    wrongRootProof.gateRounds = WhirTailWitness.sixProof.gateRounds ∧
    wrongRootProof.used = WhirTailWitness.sixProof.used ∧
    wrongRootProof.whirTranscript = WhirTailWitness.sixProof.whirTranscript ∧
    wrongRootProof.whirHints = WhirTailWitness.sixProof.whirHints ∧
    wrongRootProof.normInverseRoot ≠ WhirTailWitness.sixProof.normInverseRoot :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

set_option maxRecDepth 2000 in
/-- The shape gate is blind to this change: `wrongRootProof` passes `shape` at
the same pinned tuple its accepting twin passes it at. -/
theorem the_wrong_proof_passes_the_shape_gate :
    Verifier.shape ⟨1, Verifier.testRoot, Verifier.testRoot⟩ Verifier.testConfig
      wrongRootProof = true ∧
    Verifier.shape ⟨1, Verifier.testRoot, Verifier.testRoot⟩ Verifier.testConfig
      WhirTailWitness.sixProof = true := ⟨rfl, rfl⟩

/-! ## 2. What the change does to the derived WHIR context -/

/-- The accepting engine of `WhirTailWitness.installed_whir_pair_accepts_a_full
_verification`, named once: `WhirTailWitness.sixEngine` at the adopted decoder.
Every concrete evaluation below is at THIS engine. -/
def installedEngine : Verifier.Engine :=
  WhirTailWitness.sixEngine Integrated.exampleDecoder

/-- The derived context of the wrong proof is the accepting context with its
THIRD root -- the `normInverseRoot` slot of `Verifier.whirContext` -- replaced.
Everything else in the context is untouched. -/
theorem wrong_root_changes_only_the_third_context_root
    :
    Verifier.derivedContext installedEngine Verifier.testConfig wrongRootProof =
      { WhirTailWitness.sixContext with roots := [Verifier.testRoot, Verifier.testRoot,
          wrongRoot] } := by rfl

theorem the_accepting_context_roots_are_all_zero
    :
    (Verifier.derivedContext installedEngine Verifier.testConfig
      WhirTailWitness.sixProof).roots = [Verifier.testRoot, Verifier.testRoot, Verifier.testRoot] :=
  by rfl

/-! ## 3. The parse fails: the root binding lives inside the installed parse -/

set_option maxRecDepth 2000 in
/-- **THE INSTALLED PARSE REJECTS.**  At the wrong-root context, on the very
bytes that parse successfully at the accepting context
(`WhirTailWitness.six_parse_matches_the_context`), the concrete parse returns
`none`: the transcript's literal commitment bytes are not the digests of the
proof's statement roots any more. -/
theorem parse_of_the_wrong_root_proof_is_none :
    InstalledWhirParse.concreteParseWhir InstalledWhirTail.exampleHash
      WhirConfigured.exampleNoRounds
      (Verifier.derivedContext installedEngine Verifier.testConfig wrongRootProof)
      wrongRootProof.whirTranscript wrongRootProof.whirHints = none := by rfl

set_option maxRecDepth 2000 in
theorem prefix_run_of_the_wrong_root_proof_is_none :
    InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds
      (Verifier.derivedContext installedEngine Verifier.testConfig wrongRootProof)
      wrongRootProof.whirTranscript wrongRootProof.whirHints = none := by rfl

set_option maxRecDepth 2000 in
/-- Consequently the engine's own `parseWhir` field is `none` here. -/
theorem engine_parse_field_is_none_on_the_wrong_root_proof :
    installedEngine.parseWhir
      (Verifier.derivedContext installedEngine Verifier.testConfig wrongRootProof)
      wrongRootProof.whirTranscript wrongRootProof.whirHints = none :=
  parse_of_the_wrong_root_proof_is_none

set_option maxRecDepth 2000 in
/-- **THE WHIR GATE IS FALSE.** -/
theorem whir_gate_is_false_on_the_wrong_root_proof :
    Verifier.verifyWhir installedEngine
      (Verifier.derivedContext installedEngine Verifier.testConfig wrongRootProof)
      wrongRootProof = false := by
  unfold Verifier.verifyWhir
  rw [engine_parse_field_is_none_on_the_wrong_root_proof]

/-! ### 3b. Confounder elimination: only the roots change -/

/-- The wrong proof's derived context, named once. -/
abbrev wrongCtx : Verifier.WhirContext :=
  Verifier.derivedContext installedEngine Verifier.testConfig wrongRootProof

/-- Every argument `prefixRun` feeds on besides `parseRoots` is LITERALLY the
accepting one. -/
theorem probe_only_the_roots_change :
    InstalledWhirTail.contextParams WhirConfigured.exampleNoRounds wrongCtx =
      InstalledWhirTail.contextParams WhirConfigured.exampleNoRounds WhirTailWitness.sixContext ∧
    InstalledWhirParse.parseClaims wrongCtx =
      InstalledWhirParse.parseClaims WhirTailWitness.sixContext ∧
    wrongCtx.protocolId = WhirTailWitness.sixContext.protocolId ∧
    wrongCtx.sessionId = WhirTailWitness.sixContext.sessionId ∧
    wrongCtx.numVariables = WhirTailWitness.sixContext.numVariables ∧
    wrongCtx.points = WhirTailWitness.sixContext.points ∧
    wrongCtx.expectedClaims = WhirTailWitness.sixContext.expectedClaims ∧
    (InstalledWhirParse.parseRoots wrongCtx).length =
      (InstalledWhirParse.parseRoots WhirTailWitness.sixContext).length ∧
    wrongRootProof.whirTranscript = WhirTailWitness.sixProof.whirTranscript ∧
    wrongRootProof.whirHints = WhirTailWitness.sixProof.whirHints :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- And the root list really is different. -/
theorem probe_the_root_list_differs :
    InstalledWhirParse.parseRoots wrongCtx ≠
      InstalledWhirParse.parseRoots WhirTailWitness.sixContext := by decide

/-- Positive control: put the roots back -- every other byte of the context and
of the proof untouched -- and the parse succeeds again.  So the `none` of
`parse_of_the_wrong_root_proof_is_none` is caused by the root list and by
nothing else. -/
theorem probe_restoring_the_roots_restores_the_parse :
    (InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash
      WhirConfigured.exampleNoRounds
      { wrongCtx with roots := [Verifier.testRoot, Verifier.testRoot, Verifier.testRoot] }
      wrongRootProof.whirTranscript wrongRootProof.whirHints).isSome = true := by
  have hctx : ({ wrongCtx with
      roots := [Verifier.testRoot, Verifier.testRoot, Verifier.testRoot] } :
        Verifier.WhirContext) = WhirTailWitness.sixContext := rfl
  have hb : wrongRootProof.whirTranscript = WhirTailWitness.sixTranscript := rfl
  have hh : wrongRootProof.whirHints = WhirTailWitness.sixHints := rfl
  rw [hctx, hb, hh]
  obtain ⟨s, hs, _⟩ := WhirTailWitness.six_parse_matches_the_context
  rw [hs]; rfl

/-! ## 4. The rejection, and its locator -/

set_option maxRecDepth 2000 in
/-- **THE REJECTION.**  The same verifier call that accepts
`WhirTailWitness.sixProof` returns `.error .invalidProof` on `wrongRootProof`.
Toy hash, toy profile, `Verifier.testConfig`, `sixEngine` -- see the module
header before quoting this. -/
theorem installed_engine_rejects_the_wrong_root_proof :
    Verifier.verify installedEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig wrongRootProof
      = .error .invalidProof := by rfl

set_option maxRecDepth 2000 in
/-- **THE LOCATOR.**  Every gate of `Verifier.verify` other than the WHIR gate
passes on `wrongRootProof`: the chain identifier, the configuration hash, the
envelope, the deployment predicate, `shape`, the four dimension checks, the
log-terminal binding, and the LATER gate-terminal binding.  Only
`Verifier.verifyWhir` is `false`.  So `installed_engine_rejects_the_wrong_root
_proof` is attributable to the WHIR gate and to nothing else. -/
theorem rejection_is_located_at_the_whir_gate :
    (1 : Nat) = (⟨1, Verifier.testRoot, Verifier.testRoot⟩ : Verifier.Pinned).chainId ∧
    installedEngine.configurationHash Verifier.testConfig = Verifier.testRoot ∧
    Verifier.envelope Verifier.testConfig = true ∧
    installedEngine.deploymentValid Verifier.testConfig = true ∧
    Verifier.shape ⟨1, Verifier.testRoot, Verifier.testRoot⟩ Verifier.testConfig
      wrongRootProof = true ∧
    (installedEngine.initialTranscript Verifier.testConfig
      wrongRootProof).logTau.length = Verifier.testConfig.degreeBits ∧
    (installedEngine.initialTranscript Verifier.testConfig
      wrongRootProof).gateTau.length = Verifier.testConfig.degreeBits ∧
    (Verifier.derivedIndices installedEngine Verifier.testConfig
      wrongRootProof).log.length = Verifier.testConfig.indexBits ∧
    (Verifier.derivedIndices installedEngine Verifier.testConfig
      wrongRootProof).gate.length = Verifier.testConfig.indexBits ∧
    installedEngine.logTerminal Verifier.testConfig
      (installedEngine.initialTranscript Verifier.testConfig wrongRootProof)
      wrongRootProof
      (Verifier.derivedRounds installedEngine Verifier.testConfig
        wrongRootProof).logPoint =
      (Verifier.derivedRounds installedEngine Verifier.testConfig
        wrongRootProof).logClaim ∧
    Verifier.gateTerminal installedEngine Verifier.testConfig wrongRootProof =
      (Verifier.derivedRounds installedEngine Verifier.testConfig
        wrongRootProof).gateClaim ∧
    Verifier.verifyWhir installedEngine
      (Verifier.derivedContext installedEngine Verifier.testConfig wrongRootProof)
      wrongRootProof = false :=
  by refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_,
      whir_gate_is_false_on_the_wrong_root_proof⟩ <;> rfl

/-! ## 5. The separation pair -/

set_option maxRecDepth 2000 in
/-- **THE HEADLINE: THE FIRST TWO-PROOF SEPARATION.**  One engine, one pinned
tuple, one configuration; `WhirTailWitness.sixProof` accepted (the adopted
`WhirTailWitness.installed_whir_pair_accepts_a_full_verification`) and
`wrongRootProof` rejected, the two differing in exactly one field
(`the_two_proofs_differ_in_exactly_one_field`).  Read the module header for what
this does not mean: `Verifier.testConfig`, a constant toy hash, the
`WhirConfigured.exampleNoRounds` profile, and four still-abstract engine
fields. -/
theorem the_separation_pair :
    Verifier.verify installedEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      WhirTailWitness.sixProof = .ok () ∧
    Verifier.verify installedEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      wrongRootProof = .error .invalidProof ∧
    wrongRootProof.normInverseRoot ≠ WhirTailWitness.sixProof.normInverseRoot :=
  ⟨WhirTailWitness.installed_whir_pair_accepts_a_full_verification,
    installed_engine_rejects_the_wrong_root_proof, by decide⟩

/-! ## 6. Generality: acceptance binds the statement roots to the transcript -/

/-- **THE QUANTIFIED FORM.**  For EVERY proof this engine accepts, the WHIR
prefix executes on that proof's own transcript and hint bytes, and the
commitment roots the execution read are exactly the digests of the proof's three
statement roots -- with `preprocessedRoot` additionally pinned to the deployment
root.  This is what makes a wrong statement root unusable: it is not compared
against an echo of itself.  Non-vacuous: see
`acceptance_hypothesis_is_satisfiable`. -/
theorem acceptance_pins_the_statement_roots_to_the_transcript
    (gdec : Integrated.DecodeGates) (p : Verifier.Proof)
    (h : Verifier.verify (WhirTailWitness.sixEngine gdec)
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig p = .ok ()) :
    ∃ s, InstalledWhirParse.prefixRun InstalledWhirTail.exampleHash
        WhirConfigured.exampleNoRounds
        (Verifier.derivedContext (WhirTailWitness.sixEngine gdec) Verifier.testConfig p)
        p.whirTranscript p.whirHints = some s ∧
      s.origin.initial.commitments.map (·.root) =
        [Verifier.testRoot, p.witnessRoot, p.normInverseRoot].map
          InstalledWhirTail.rootDigest ∧
      s.origin.initial.commitments.map (·.boundRoot) =
        [Verifier.testRoot, p.witnessRoot, p.normInverseRoot].map
          InstalledWhirTail.rootDigest ∧
      (InstalledWhirParse.parsedOf s).actualRoots =
        [Verifier.testRoot, p.witnessRoot, p.normInverseRoot] ∧
      (InstalledWhirParse.parsedOf s).boundRoots =
        [Verifier.testRoot, p.witnessRoot, p.normInverseRoot] := by
  have hw := (Verifier.verify_success_checks _ _ _ _ _ h).2.2.2.2.2.2.2.2.2.2.1
  have hroot := (Verifier.acceptance_protocol_and_pinned_root _ _ _ _ _ h).2
  have hw2 : Verifier.verifyWhir (InstalledWhirParse.installedParseEngine Verifier.testEngine gdec
      InstalledWhirTail.exampleHash WhirConfigured.exampleNoRounds InstalledRoundCommit.toyHash)
      (Verifier.derivedContext (WhirTailWitness.sixEngine gdec) Verifier.testConfig p) p = true := hw
  rw [InstalledWhirParse.verify_whir_concrete_iff] at hw2
  obtain ⟨s, hs, _, _, _, _⟩ := hw2
  have hk := InstalledWhirParse.concrete_parse_roots_are_the_prefix_roots _ _ _ _ _ s hs
  have hctx : (Verifier.derivedContext (WhirTailWitness.sixEngine gdec) Verifier.testConfig p).roots
      = [Verifier.testRoot, p.witnessRoot, p.normInverseRoot] := by
    rw [show (Verifier.derivedContext (WhirTailWitness.sixEngine gdec) Verifier.testConfig p).roots
      = [p.preprocessedRoot, p.witnessRoot, p.normInverseRoot] from rfl, hroot]
  refine ⟨s, hs, ?_, ?_, ?_, ?_⟩
  · rw [hk.1]; unfold InstalledWhirParse.parseRoots; rw [hctx]
  · rw [hk.2.1]; unfold InstalledWhirParse.parseRoots; rw [hctx]
  · rw [hk.2.2.1, hctx]
  · rw [hk.2.2.2.1, hctx]

/-- The hypothesis of `acceptance_pins_the_statement_roots_to_the_transcript` is
satisfied at a shipped witness. -/
theorem acceptance_hypothesis_is_satisfiable :
    Verifier.verify installedEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      WhirTailWitness.sixProof = .ok () :=
  WhirTailWitness.installed_whir_pair_accepts_a_full_verification

/-- **NO SAME-DIGEST EDGE CASE.**  `Verifier.Root` is `Fin (2 ^ 256)` and
`InstalledWhirTail.rootDigest` is injective on it, so distinct statement roots
give distinct commitment digests.  The instance-family form therefore has no
collision case to rule out; what it still lacks is the byte-equation export
described in the module header. -/
theorem probe_root_digest_is_injective (r r2 : Verifier.Root)
    (h : InstalledWhirTail.rootDigest r = InstalledWhirTail.rootDigest r2) : r = r2 := by
  have hv : (Transcript.le 32 r.val).reverse = (Transcript.le 32 r2.val).reverse :=
    congrArg Subtype.val h
  have hle : Transcript.le 32 r.val = Transcript.le 32 r2.val := by
    have := congrArg List.reverse hv
    simpa using this
  have hb : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
  exact Fin.ext (Transcript.le_injective_bounded 32 r.val r2.val
    (by rw [hb]; exact r.isLt) (by rw [hb]; exact r2.isLt) hle)

/-! ## 7. The contrast: the fixture WHIR pair accepts the same wrong proof -/

/-- `WhirTailWitness.sixEngine` with the WHIR pair put back to the FIXTURE pair:
`Verifier.testEngine.parseWhir`, which returns `ctx.roots` for both root copies
by construction, and `Verifier.testEngine.whirTail = fun _ _ _ _ => true`.  Ten
other fields are untouched. -/
def fixtureWhirSixEngine : Verifier.Engine :=
  { installedEngine with
      parseWhir := Verifier.testEngine.parseWhir
      whirTail := Verifier.testEngine.whirTail }

/-- What the contrast engine changes, and what it does not. -/
theorem fixture_engine_differs_only_in_the_whir_pair :
    fixtureWhirSixEngine.parseWhir = Verifier.testEngine.parseWhir ∧
    fixtureWhirSixEngine.whirTail = Verifier.testEngine.whirTail ∧
    fixtureWhirSixEngine.commitRound = installedEngine.commitRound ∧
    fixtureWhirSixEngine.sampleIndices = installedEngine.sampleIndices ∧
    fixtureWhirSixEngine.foldClaim = installedEngine.foldClaim ∧
    fixtureWhirSixEngine.normEvaluation = installedEngine.normEvaluation ∧
    fixtureWhirSixEngine.eqEvaluation = installedEngine.eqEvaluation ∧
    fixtureWhirSixEngine.gateEvaluation = installedEngine.gateEvaluation ∧
    fixtureWhirSixEngine.initialObservation =
      installedEngine.initialObservation ∧
    fixtureWhirSixEngine.publicInputsHash =
      installedEngine.publicInputsHash ∧
    fixtureWhirSixEngine.configurationHash =
      installedEngine.configurationHash ∧
    fixtureWhirSixEngine.deploymentValid =
      installedEngine.deploymentValid :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fixture parse echoes whatever roots the context carries, for BOTH root
copies -- so `Verifier.rootsAndClaimsMatch`'s root half can never fail on it. -/
theorem the_fixture_parse_echoes_the_context_roots (ctx : Verifier.WhirContext)
    (transcript hints : Verifier.Bytes) :
    Verifier.testEngine.parseWhir ctx transcript hints =
      some ⟨ctx.roots, ctx.roots, List.replicate 6 Verifier.zero⟩ := rfl

set_option maxRecDepth 2000 in
/-- **THE PRE-REPAIR BEHAVIOUR.**  The SAME `wrongRootProof` is ACCEPTED once
the WHIR pair is the fixture pair.  Nothing about the proof changed; only the
WHIR pair did -- BOTH halves of it, `parseWhir` and `whirTail`.  Neither half
alone suffices: see `probe_installed_parse_alone_rejects` and
`probe_installed_tail_alone_rejects`. -/
theorem fixture_whir_pair_accepts_the_wrong_root_proof :
    Verifier.verify fixtureWhirSixEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig wrongRootProof
      = .ok () := by rfl

set_option maxRecDepth 2000 in
/-- And it accepts the honest proof too -- so at the fixture pair the two proofs
are INDISTINGUISHABLE, which is exactly why
`DigestRoutedAcceptance.alt_proof_is_still_accepted` could not separate them. -/
theorem fixture_whir_pair_accepts_the_honest_proof :
    Verifier.verify fixtureWhirSixEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      WhirTailWitness.sixProof = .ok () := by rfl

set_option maxRecDepth 2000 in
/-- **THE PRACTICAL PAYLOAD.**  Installed parse: honest accepted, wrong
rejected.  Fixture parse: both accepted.  The binding check installed by
`InstalledWhirParse.concreteParseWhir` is what stands between acceptance and a
forged statement root, in this model.  This is a statement about the MODEL of
the installed parse; it is not a claim about the deployed Solidity. -/
theorem installing_the_whir_pair_is_what_rejects :
    (Verifier.verify installedEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      WhirTailWitness.sixProof = .ok () ∧
     Verifier.verify installedEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      wrongRootProof = .error .invalidProof) ∧
    (Verifier.verify fixtureWhirSixEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      WhirTailWitness.sixProof = .ok () ∧
     Verifier.verify fixtureWhirSixEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      wrongRootProof = .ok ()) :=
  ⟨⟨WhirTailWitness.installed_whir_pair_accepts_a_full_verification,
    installed_engine_rejects_the_wrong_root_proof⟩,
   ⟨fixture_whir_pair_accepts_the_honest_proof,
    fixture_whir_pair_accepts_the_wrong_root_proof⟩⟩

/-! ## 8. The sharpened attribution: each half of the pair alone rejects -/

/-- The installed parse against the FIXTURE tail. -/
def installedParseFixtureTailEngine : Verifier.Engine :=
  { installedEngine with whirTail := Verifier.testEngine.whirTail }

/-- The FIXTURE parse against the installed tail. -/
def fixtureParseInstalledTailEngine : Verifier.Engine :=
  { installedEngine with parseWhir := Verifier.testEngine.parseWhir }

set_option maxRecDepth 2000 in
/-- The PARSE alone already rejects: the fixture tail does not rescue the
forgery. -/
theorem probe_installed_parse_alone_rejects :
    Verifier.verify installedParseFixtureTailEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig wrongRootProof
      = .error .invalidProof := by rfl

set_option maxRecDepth 2000 in
/-- ... and it still accepts the honest proof, so "installed parse + fixture
tail" is a genuine separation on its own. -/
theorem probe_installed_parse_alone_accepts_the_honest_proof :
    Verifier.verify installedParseFixtureTailEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      WhirTailWitness.sixProof = .ok () := by rfl

set_option maxRecDepth 2000 in
/-- The TAIL alone also rejects: `InstalledWhirTail.installedTail` factors
through the same `prefixRun`. -/
theorem probe_installed_tail_alone_rejects :
    Verifier.verify fixtureParseInstalledTailEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig wrongRootProof
      = .error .invalidProof := by rfl

set_option maxRecDepth 2000 in
/-- ... and it too still accepts the honest proof.  Together with the previous
three theorems: EACH HALF ALONE rejects the forgery and accepts the honest
proof, so acceptance of the forgery requires BOTH halves to be the fixture's. -/
theorem probe_installed_tail_alone_accepts_the_honest_proof :
    Verifier.verify fixtureParseInstalledTailEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig
      WhirTailWitness.sixProof = .ok () := by rfl

/-! ## 9. The other unpinned root behaves the same way -/

/-- The SAME forgery applied to the other unpinned statement root. -/
def wrongWitnessProof : Verifier.Proof :=
  { WhirTailWitness.sixProof with witnessRoot := wrongRoot }

set_option maxRecDepth 2000 in
/-- `normInverseRoot` is an INSTANCE, not the mechanism: forging `witnessRoot`
instead is rejected by the installed engine just the same. -/
theorem probe_wrong_witness_root_is_also_rejected :
    Verifier.verify installedEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig wrongWitnessProof
      = .error .invalidProof := by rfl

set_option maxRecDepth 2000 in
/-- ... and the fixture pair accepts THAT forgery too, so the whole separation
repeats verbatim at `witnessRoot`.  The honest general statement is therefore
"the statement roots the parse reads", with `normInverseRoot` as one instance. -/
theorem probe_fixture_pair_accepts_the_wrong_witness_root_too :
    Verifier.verify fixtureWhirSixEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig wrongWitnessProof
      = .ok () := by rfl

end Audit.Wire3.RejectionWitness
