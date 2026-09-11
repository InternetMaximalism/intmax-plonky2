import Audit.Wire3.InstalledRoundCommit

/-!
# Installing the concrete WHIR parse into the outer verifier engine

## The gap this closes

`Verifier.Engine.parseWhir : WhirContext → Bytes → Bytes → Option ParsedWhir`
(Verifier.lean 356) is an OBSERVATION on every engine of the adopted tree, and
`Verifier.verifyWhir` (Verifier.lean 365-368) is

```
match e.parseWhir ctx p.whirTranscript p.whirHints with
| none        => false
| some parsed => rootsAndClaimsMatch ctx parsed && e.whirTail ctx … parsed
```

so the ENTIRE root/claim binding of the outer verifier --
`rootsAndClaimsMatch` (Verifier.lean 312-314), and with it
`whir_acceptance_requires_bound_statement` (370-386) and
`acceptance_exact_whir_and_terminal_binding` (527-543) -- is a statement about a
value the ENGINE supplied, not about the proof's bytes.  The adopted
`Verifier.testEngine` makes this concrete: its parse is
`fun ctx _ _ => some ⟨ctx.roots, ctx.roots, List.replicate 6 zero⟩`
(Verifier.lean 609), which returns the context's own roots for ANY transcript,
including the empty one, so `rootsAndClaimsMatch` holds vacuously.
`Integrated.exampleEngine` does the same with the unmasked claims
(Integrated.lean 203).  `InstalledWhirTail`'s own header says it: "no concrete
`ParsedWhir` parser exists in the adopted tree; only toy stand-ins".

This module installs the parse.  After it, `rootsAndClaimsMatch` is a DERIVED
property of the WHIR transcript bytes.

## What the source parse consists of

`parseWhir`'s three outputs correspond, in the source, to three reads that all
happen in WHIR's initial commitment phase, BEFORE any challenge that depends on
them:

* `actualRoots` -- the Merkle roots the WHIR transcript ACTUALLY carries.  Rust:
  `WhirPCS::verify_grouped` first walks the fixed byte grammar, slicing
  `narg_string[group*stride .. +32]` for each group and comparing it against the
  outer verifier's root (whir_pcs.rs 1527-1542, the preflight loop whose comment
  at 1514-1516 says "Root positions are fixed by the config ... Bind both copies
  before transcript replay so a bad root cannot steer preflight challenges"),
  then replays them through the sponge as `config.receive_commitment`
  (whir_pcs.rs 1586-1588).  Solidity: `SpongefishWhirVerify._receiveCommitmentsAndOod`
  reads `vs.initialRoots[c] = proverMessageHash(ts, transcript)`
  (SpongefishWhirVerify.sol 374).  Lean: the first `Spongefish.proverHash` of
  `WhirInitial.receiveOne` (WhirInitial.lean 52-62).
* `boundRoots` -- the roots the OUTER verifier binds, i.e. the context's
  `[preprocessed, witness, normInverse]`.  Rust: the `expected_roots` array
  `[proof.preprocessed_root, proof.witness_root, proof.norm_inverse_root]` built
  at verifier_v2.rs 381-385 and passed to `verify_grouped` at 386-393; the
  transcript carries a SECOND 32-byte copy after the OOD answers, which is
  compared against it (whir_pcs.rs 1549-1556 in the preflight, 1590-1595 in the
  replay).  Solidity: `roots[0..2]` at MleVerifierV2.sol 360-363, checked as
  `boundRoot != expectedRoots[c] || boundRoot != vs.initialRoots[c]`
  (SpongefishWhirVerify.sol 384-387) -- BOTH copies, in one guard.  Lean: the
  second `proverHash` of `receiveOne` plus its
  `if boundRoot = expected ∧ boundRoot = root` (WhirInitial.lean 59-62).
* `claims` -- the masked expected evaluations.  Rust: the loop at
  whir_pcs.rs 1599-1614, whose comment says "Compare the transcript-bound claims
  byte-for-byte before WHIR draws the vector-combination challenge"; the mask is
  `Option` and only `Some` cells are compared (1606-1611).  Solidity:
  SpongefishWhirVerify.sol 309-318, with the little-endian bitset
  `evaluationMask` and `PACKED_BOUND_CLAIM_MASK_V2 = 0x1f`
  (generated/MleWhirV2.sol 95, `NUM_PCS_CLAIMS_V2 = 6` at 88), enforced at
  MleVerifierV2.sol 352-355 and, on the Rust side, at verifier_v2.rs 364-370.
  Lean: `WhirInitial.readClaims` (WhirInitial.lean 77-84) against the adopted
  `InstalledWhirTail.whirMask = [31]`, whose five-of-six shape is the adopted
  `InstalledWhirTail.mask_is_the_five_bound_cells`.

So the three parsed OUTPUTS are read in the initial phase of the WHIR session,
whose Lean model is already adopted: `WhirInitial.phaseInitial`, wrapped by
`WhirPrefix.run`, wrapped by `WhirTail.runPrefix`.  `concreteParseWhir` is
exactly the projection of that adopted reading -- nothing new is modelled.

What the parse EXECUTES is more than those three reads, and deliberately so.  It
is the adopted tail run truncated at `WhirTail.runPrefix`, i.e. `WhirPrefix.run`
(the initial phase AND the initial sumcheck) followed by
`WhirIntermediate.runRounds` (the intermediate rounds).  So `concreteParseWhir`
returns `none` exactly when THAT prefix fails -- which includes an intermediate
round failing, not only the initial phase.  Acceptance is unaffected (the tail
runs on the same engine and consumes the same prefix state), and truncating at
exactly this point is what makes the factorisation
`tailRun = prefixRun >>= runTail` DEFINITIONAL rather than a re-derivation --
which is what `parse_and_tail_read_the_same_prefix` rests on.

## What is installed here

`prefixRun hash wp ctx transcript hints` is the SAME call
`InstalledWhirTail.tailRun` makes, truncated at `WhirTail.runPrefix`: the same
checked parameter admission (`WhirParameters.checkBound`), the same
`contextParams wp ctx` record, the same `ctx.roots.map rootDigest`, the same
`OpeningBinding.unmask ctx.expectedClaims`, the same `whirMask`, the same
`Spongefish.init` domain separator, the same byte adapters.
`tail_run_factors_through_prefix_run` proves that factorisation, and
`parse_and_tail_read_the_same_prefix` states its consequence: the parse and the
tail are ONE execution, so no divergence between "what was parsed" and "what the
tail authenticated" is representable.  That is the whole point of installing
both on the same engine.

`installedParseEngine e gdec hash wp thash` is
`InstalledRoundCommit.installedRoundEngine e gdec hash wp thash` -- chosen as the
base because it is the deepest adopted engine, already carrying
`InstalledWhirTail.installedTail hash wp` at the SAME `hash` and `wp`, which is
what makes the one-execution statement true -- with `parseWhir` replaced.

## What is still an OBSERVATION after this module

On this engine: `initialObservation` (hence `Engine.initialTranscript`),
`publicInputsHash`, `configurationHash`, `deploymentValid`.  The first two are
installed by the ADOPTED `InstalledInitialTranscript` (adopted at 3efafd4c,
batch 19), which installs `initialObservation` and `publicInputsHash` over the
same `InstalledIndexSampler.installedSamplerEngine` base this module's base is
built on; composing it with this module and with `InstalledRoundCommit` leaves,
on the composed engine, `configurationHash` as the ONLY remaining engine
observation -- plus `deploymentValid`, unless `PinnedWhirProfile.pinnedEngine`
(PinnedWhirProfile.lean 289-291) is also composed, which replaces it by
`pinnedDeployment`.  That composition is NOT performed here (it is the separate
candidate `ComposedEngine`); this module imports neither.

`WhirContext`'s `protocolId` / `sessionId` / `parameters` are still the FREE
`Verifier.Config` fields `whirProtocolId` / `whirSessionId` / `whirEncoding`
(Verifier.lean 88-89), copied into the context by `Verifier.whirContext`
(Verifier.lean 250).  Nothing in the Lean model ties them to the deployment
except the `configurationHash` / `deploymentValid` observations.  In the source
they are `_protocolId()` and `whirSessionId` (MleVerifierV2.sol 366-367;
`_protocolId()` is defined at 735-737 and the immutables it and `whirSessionId`
read are declared at 80-82) and `protocol_id_for_config` / `whir_session_id`
(whir_pcs.rs 476-478, checked at verifier_v2.rs 168-175).  Likewise `wp` is a
FREE argument: in the source it is pinned by the profile digest
(`CanonicalWhirProfileV2.validateCanonical`, MleVerifierV2.sol 151-153), which is
an observation in Lean, not a theorem here.

## What is NOT proved

`hash` and `thash` are arbitrary deterministic functions.  No hash security, no
collision resistance, no random-oracle property, no Fiat--Shamir soundness, no
WHIR/PCS soundness, no Merkle security, no Rust/Yul/Solidity refinement.  The
model is a manual reading of the sources cited above; `Verifier.verify` is a
manual success-boundary model, not an EVM exception-order refinement.

Residue R1b (what the tail's extraction predicates are ASSUMED to deliver), R2
and R3 of `OpeningBinding` are UNCHANGED by this module: installing the parse
removes an observation from the root/claim binding, it does not add any
cryptographic content to the tail.

Nothing here is the deployed system's soundness error.  The wire-v3 WHIR profile
this models is the ~100-bit design point.  No figure in this module is a
security level, and in particular nothing here says "125".
-/

namespace Audit.Wire3.InstalledWhirParse

open Spongefish (Hash Digest)

abbrev VkParams := InstalledWhirTail.VkParams

/-! ## 1. The concrete parse -/

/-- The WHIR-side digests of the outer verifier's pinned root list. -/
def parseRoots (ctx : Verifier.WhirContext) : List Digest :=
  ctx.roots.map InstalledWhirTail.rootDigest

/-- The outer verifier's expected claim vector, with unbound cells filled by
`zero`; the mask `InstalledWhirTail.whirMask` is what decides which cells are
actually compared. -/
def parseClaims (ctx : Verifier.WhirContext) : List Verifier.Ext3 :=
  OpeningBinding.unmask ctx.expectedClaims

/-- The prefix of the SAME WHIR session `InstalledWhirTail.tailRun` runs: checked
parameter admission, then `WhirTail.runPrefix` on the proof's own transcript and
hint bytes under the context's protocol/session separator -- that is, the initial
phase and the initial sumcheck (`WhirPrefix.run`) followed by the intermediate
rounds (`WhirIntermediate.runRounds`). -/
def prefixRun (hash : Hash) (wp : VkParams) (ctx : Verifier.WhirContext)
    (transcript hints : Verifier.Bytes) : Option WhirTail.PrefixState :=
  match WhirParameters.checkBound (InstalledWhirTail.contextParams wp ctx)
      (parseRoots ctx).length (parseClaims ctx).length InstalledWhirTail.whirMask.length with
  | none => none
  | some forms =>
      WhirTail.runPrefix hash (InstalledWhirTail.outerBytes transcript)
        (InstalledWhirTail.outerBytes hints)
        (WhirParameters.initialParams (InstalledWhirTail.contextParams wp ctx) forms)
        (parseRoots ctx) (parseClaims ctx) InstalledWhirTail.whirMask
        (InstalledWhirTail.contextParams wp ctx).initialSumcheckRounds
        (InstalledWhirTail.contextParams wp ctx).initialSumcheckPowThreshold
        (Spongefish.init hash (InstalledWhirTail.outerBytes ctx.protocolId)
          (InstalledWhirTail.outerBytes ctx.sessionId) [])
        (WhirConfigured.phasePairs
          (WhirConfigured.initialOpen (InstalledWhirTail.contextParams wp ctx))
          (InstalledWhirTail.contextParams wp ctx).rounds)

/-- The projection of an executed prefix into the outer verifier's `ParsedWhir`:
the actual commitment roots, the bound commitment roots and the claim values the
transcript carried, in the WHIR session's own order. -/
def parsedOf (s : WhirTail.PrefixState) : Verifier.ParsedWhir :=
  ⟨s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.root),
   s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.boundRoot),
   s.origin.initial.evaluations⟩

/-- **THE INSTALLED PARSE.**  A total function of the context and the proof's
bytes.  The execution it projects is the adopted tail run truncated at
`WhirTail.runPrefix` -- the initial phase, the initial sumcheck
(`WhirPrefix.run`) and the intermediate rounds (`WhirIntermediate.runRounds`) --
so the result is `none` exactly when THAT prefix fails, an intermediate round
included, not only when the initial phase fails. -/
def concreteParseWhir (hash : Hash) (wp : VkParams) :
    Verifier.WhirContext → Verifier.Bytes → Verifier.Bytes → Option Verifier.ParsedWhir :=
  fun ctx transcript hints => (prefixRun hash wp ctx transcript hints).map parsedOf

/-- The fixed byte stride of one initial commitment block: 32 root bytes, the
out-of-domain answers, 32 bound-root bytes.  Source: `commitment_stride` at
whir_pcs.rs 1522-1525. -/
def whirStride (wp : VkParams) : Nat := 64 + 24 * (wp.outDomainSamples * wp.numVectors)

/-! ## 2. The parse and the tail are one execution -/

theorem tail_run_factors_through_prefix_run (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes) :
    InstalledWhirTail.tailRun hash wp ctx transcript hints =
      (prefixRun hash wp ctx transcript hints).bind
        (fun s => WhirTail.runTail hash (InstalledWhirTail.outerBytes transcript)
          (InstalledWhirTail.outerBytes hints)
          (WhirConfigured.finalParams (InstalledWhirTail.contextParams wp ctx)) s) := by
  unfold InstalledWhirTail.tailRun WhirConfigured.run prefixRun parseRoots parseClaims
  cases hb : WhirParameters.checkBound (InstalledWhirTail.contextParams wp ctx)
      (ctx.roots.map InstalledWhirTail.rootDigest).length
      (OpeningBinding.unmask ctx.expectedClaims).length InstalledWhirTail.whirMask.length with
  | none => simp [hb]
  | some forms => simp [hb, WhirTail.run, Option.bind]

/-- (d) **THE PARSE AND THE TAIL READ THE SAME PREFIX.**  Same bytes, same
parameters, same domain separator, same execution.  A proof cannot present one
set of roots/claims to the outer verifier's `rootsAndClaimsMatch` and a different
one to the Merkle/sumcheck machinery of the tail, because there is only ONE
run. -/
theorem parse_and_tail_read_the_same_prefix (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes) :
    (∀ r, InstalledWhirTail.tailRun hash wp ctx transcript hints = some r →
        prefixRun hash wp ctx transcript hints = some r.retained ∧
        concreteParseWhir hash wp ctx transcript hints = some (parsedOf r.retained)) ∧
    (prefixRun hash wp ctx transcript hints = none →
      InstalledWhirTail.tailRun hash wp ctx transcript hints = none) := by
  constructor
  · intro r hr
    rw [tail_run_factors_through_prefix_run] at hr
    cases hs : prefixRun hash wp ctx transcript hints with
    | none => rw [hs] at hr; exact absurd hr (by simp)
    | some s =>
        rw [hs] at hr
        simp only [Option.bind] at hr
        have hret : s = r.retained :=
          (WhirTail.tail_success_same_vector_and_context hash
            (InstalledWhirTail.outerBytes transcript) (InstalledWhirTail.outerBytes hints)
            (WhirConfigured.finalParams (InstalledWhirTail.contextParams wp ctx)) s r hr).1.symm
        exact ⟨congrArg some hret, by simp [concreteParseWhir, hs, hret]⟩
  · intro hs
    rw [tail_run_factors_through_prefix_run, hs]
    rfl

/-! ## 3. What the prefix run proves about the parse -/

theorem prefix_run_success_gives_whir_prefix (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes) (s : WhirTail.PrefixState)
    (h : prefixRun hash wp ctx transcript hints = some s) :
    ∃ forms, WhirParameters.checkBound (InstalledWhirTail.contextParams wp ctx)
        (parseRoots ctx).length (parseClaims ctx).length InstalledWhirTail.whirMask.length =
        some forms ∧
      WhirPrefix.run hash (InstalledWhirTail.outerBytes transcript)
        (WhirParameters.initialParams (InstalledWhirTail.contextParams wp ctx) forms)
        (parseRoots ctx) (parseClaims ctx) InstalledWhirTail.whirMask
        (InstalledWhirTail.contextParams wp ctx).initialSumcheckRounds
        (InstalledWhirTail.contextParams wp ctx).initialSumcheckPowThreshold
        (Spongefish.init hash (InstalledWhirTail.outerBytes ctx.protocolId)
          (InstalledWhirTail.outerBytes ctx.sessionId) []) = some s.origin := by
  unfold prefixRun at h
  cases hb : WhirParameters.checkBound (InstalledWhirTail.contextParams wp ctx)
      (parseRoots ctx).length (parseClaims ctx).length InstalledWhirTail.whirMask.length with
  | none => simp only [hb] at h
  | some forms =>
      simp only [hb] at h
      exact ⟨forms, rfl, (WhirTail.prefix_success_retains_actual_pair hash _ _ _ _ _ _ _ _ _ _ s h).1⟩

/-- `WhirTail.rootWord` inverts `InstalledWhirTail.rootDigest`: the 32 big-endian
bytes a WHIR commitment carries are the outer verifier's root word, losslessly.
This is the adopted `OuterInitial.root_bytes_roundtrip`. -/
theorem root_word_of_root_digest (r : Verifier.Root) :
    WhirTail.rootWord (InstalledWhirTail.rootDigest r) = r := by
  apply Fin.ext
  exact OuterInitial.root_bytes_roundtrip r

theorem map_root_word_of_parse_roots (rs : List Verifier.Root) :
    (rs.map InstalledWhirTail.rootDigest).map WhirTail.rootWord = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [root_word_of_root_digest r, ih]

theorem map_root_word_comp (cs : List WhirInitial.Commitment)
    (f : WhirInitial.Commitment → Digest) (rs : List Verifier.Root)
    (h : cs.map f = rs.map InstalledWhirTail.rootDigest) :
    cs.map (fun cm => WhirTail.rootWord (f cm)) = rs := by
  have hcomp : cs.map (fun cm => WhirTail.rootWord (f cm)) = (cs.map f).map WhirTail.rootWord := by
    simp [List.map_map, Function.comp]
  rw [hcomp, h]
  exact map_root_word_of_parse_roots rs

/-- (1) **THE PARSED ROOTS ARE THE PREFIX'S ROOTS.**  On a successful parse the
actual and bound root lists are exactly the outer verifier's pinned roots, and
they are the `rootWord` images of the commitments the adopted prefix execution
returned -- so `rootsAndClaimsMatch`'s root half is now a THEOREM about the
transcript bytes, not a hypothesis about an observation. -/
theorem concrete_parse_roots_are_the_prefix_roots (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes) (s : WhirTail.PrefixState)
    (h : prefixRun hash wp ctx transcript hints = some s) :
    s.origin.initial.commitments.map (·.root) = parseRoots ctx ∧
    s.origin.initial.commitments.map (·.boundRoot) = parseRoots ctx ∧
    (parsedOf s).actualRoots = ctx.roots ∧
    (parsedOf s).boundRoots = ctx.roots ∧
    (parsedOf s).claims = s.origin.initial.evaluations := by
  obtain ⟨forms, _, hp⟩ := prefix_run_success_gives_whir_prefix hash wp ctx transcript hints s h
  have hk := WhirPrefix.successful_prefix_keeps_roots_and_all_checked_claims hash _ _ _ _ _ _ _ _
    s.origin hp
  exact ⟨hk.1, hk.2.1,
    map_root_word_comp s.origin.initial.commitments (·.root) ctx.roots hk.1,
    map_root_word_comp s.origin.initial.commitments (·.boundRoot) ctx.roots hk.2.1, rfl⟩

/-- (1, corollary) **THE ROOT CONJUNCT OF `rootsAndClaimsMatch` IS REDUNDANT ON
THIS ENGINE.**  Whenever the prefix runs, `Verifier.rootsAndClaimsMatch` reduces
DEFINITIONALLY to its claim half, because the two root lists it compares against
`ctx.roots` are already `ctx.roots`.  This is the precise form of the statement
that installing the parse leaves only the claim comparison with content: the root
comparison is not weakened, it is discharged by the parse itself. -/
theorem roots_and_claims_match_reduces_to_claims (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes)
    (s : WhirTail.PrefixState) (hs : prefixRun hash wp ctx transcript hints = some s) :
    Verifier.rootsAndClaimsMatch ctx (parsedOf s) =
      Verifier.claimsMatch ctx.expectedClaims s.origin.initial.evaluations := by
  obtain ⟨_, _, ha, hb, hc⟩ :=
    concrete_parse_roots_are_the_prefix_roots hash wp ctx transcript hints s hs
  simp [Verifier.rootsAndClaimsMatch, ha, hb, hc]

/-- (1) **THE PARSED CLAIMS ARE THE BOUND CELLS.**  The claim vector has the
outer verifier's own length, and every one of the five MASKED cells equals the
outer verifier's expected claim at that position.  The sixth cell is unmasked --
`InstalledWhirTail.mask_is_the_five_bound_cells`, source
`PACKED_BOUND_CLAIM_MASK_V2 = 0x1f` -- and is NOT constrained, exactly as in the
source. -/
theorem concrete_parse_claims_are_the_bound_cells (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes) (s : WhirTail.PrefixState)
    (h : prefixRun hash wp ctx transcript hints = some s) :
    (parsedOf s).claims.length = ctx.expectedClaims.length ∧
    ∀ i x, i < 5 → ctx.expectedClaims[i]? = some (some x) →
      (parsedOf s).claims.getD i Verifier.zero = x := by
  obtain ⟨forms, _, hp⟩ := prefix_run_success_gives_whir_prefix hash wp ctx transcript hints s h
  have hk := WhirPrefix.successful_prefix_keeps_roots_and_all_checked_claims hash _ _ _ _ _ _ _ _
    s.origin hp
  have hlen : (parseClaims ctx).length = ctx.expectedClaims.length := by
    simp [parseClaims, OpeningBinding.unmask]
  refine ⟨by rw [show (parsedOf s).claims = s.origin.initial.evaluations from rfl, hk.2.2.1, hlen], ?_⟩
  intro i x hi hx
  have hidx : i < (parseClaims ctx).length := by
    rw [hlen]
    rcases Nat.lt_or_ge i ctx.expectedClaims.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at hx
      exact absurd hx (by simp)
  have hc := hk.2.2.2.1 i hidx (InstalledWhirTail.mask_is_the_five_bound_cells.2.1 i hi)
  show s.origin.initial.evaluations.getD i Verifier.zero = x
  rw [hc]
  exact InstalledWhirTail.unmask_get_of_bound ctx.expectedClaims i x hx

/-! ## 4. `claimsMatch` from pointwise data -/

theorem claims_match_of_pointwise :
    ∀ (xs : List (Option Verifier.Ext3)) (ys : List Verifier.Ext3), xs.length = ys.length →
      (∀ i x, xs[i]? = some (some x) → ys.getD i Verifier.zero = x) →
      Verifier.claimsMatch xs ys = true := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlen _
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      intro ys hlen h
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simpa using hlen
          have h' : ∀ i x, xs[i]? = some (some x) → ys.getD i Verifier.zero = x := by
            intro i v hv
            have := h (i + 1) v (by simpa using hv)
            simpa using this
          cases x with
          | none => simpa [Verifier.claimsMatch] using ih ys hlen' h'
          | some a =>
              have ha : y = a := by simpa using h 0 a (by simp)
              simp only [Verifier.claimsMatch, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨ha.symm, ih ys hlen' h'⟩

/-- Every bound cell of the outer verifier's claim vector sits at an index below
five: the sixth cell is `none` and there is no seventh.  Proved here directly
from the shape of `Verifier.expectedClaims`; the adopted
`Verifier.context_bound_mask_exact` and
`Verifier.context_unused_gate_norm_is_unbound` (Verifier.lean 263, 267) are the
SAME fact in adopted form, and are not used in this proof. -/
theorem expected_claims_bound_index_below_five (foldClaim : Verifier.FoldClaim)
    (c : Verifier.Config) (p : Verifier.Proof) (idx : Verifier.IndexPoints) (i : Nat)
    (x : Verifier.Ext3) (h : (Verifier.expectedClaims foldClaim c p idx)[i]? = some (some x)) :
    i < 5 := by
  match i with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | 4 => omega
  | 5 => simp [Verifier.expectedClaims] at h
  | (n + 6) => simp [Verifier.expectedClaims] at h

/-! ## 5. The engine -/

/-- The abstract engine with ONLY the parse migrated; the migration identity
below says installing the parse on the round engine is the same as building the
round engine over this one. -/
def reparsed (e : Verifier.Engine) (hash : Hash) (wp : VkParams) : Verifier.Engine :=
  { e with parseWhir := concreteParseWhir hash wp }

/-- **THE ENGINE OF THIS MODULE.**  `InstalledRoundCommit.installedRoundEngine`
-- the deepest adopted engine, which already carries
`InstalledWhirTail.installedTail hash wp` at the same `hash` and `wp` -- with the
concrete parse installed. -/
def installedParseEngine (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Hash) (wp : VkParams) (thash : Transcript.Hash) : Verifier.Engine :=
  { InstalledRoundCommit.installedRoundEngine e gdec hash wp thash with
    parseWhir := concreteParseWhir hash wp }

/-- Installing the parse commutes with every adopted install, so each adopted
result quantified over an arbitrary `Verifier.Engine` applies to this engine
verbatim, with `e` replaced by `reparsed e hash wp`. -/
theorem installed_parse_is_round_engine_of_reparsed (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (thash : Transcript.Hash) :
    installedParseEngine e gdec hash wp thash =
      InstalledRoundCommit.installedRoundEngine (reparsed e hash wp) gdec hash wp thash := rfl

/-- Field preservation.  `normEvaluation`, `eqEvaluation` and `gateEvaluation`
are inherited unchanged from `Integrated.modelEngine` through the adopted
`InstalledIndexSampler` / `InstalledRoundCommit` bases; they are listed here so
that the record of what this engine carries is complete. -/
theorem installed_parse_keeps_everything_else (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (thash : Transcript.Hash) :
    (installedParseEngine e gdec hash wp thash).parseWhir = concreteParseWhir hash wp ∧
    (installedParseEngine e gdec hash wp thash).whirTail = InstalledWhirTail.installedTail hash wp ∧
    (installedParseEngine e gdec hash wp thash).commitRound =
      InstalledRoundCommit.concreteCommitRound thash ∧
    (installedParseEngine e gdec hash wp thash).sampleIndices =
      InstalledIndexSampler.concreteSampleIndices thash ∧
    (installedParseEngine e gdec hash wp thash).foldClaim = Connections.packedFold ∧
    (installedParseEngine e gdec hash wp thash).normEvaluation = Norm.normEvaluation ∧
    (installedParseEngine e gdec hash wp thash).eqEvaluation = Norm.eqEvaluation ∧
    (installedParseEngine e gdec hash wp thash).gateEvaluation =
      (fun c wires constants publicHash alpha =>
        (Integrated.evaluateGate gdec c wires constants publicHash alpha).getD Verifier.zero) ∧
    (installedParseEngine e gdec hash wp thash).initialObservation = e.initialObservation ∧
    (installedParseEngine e gdec hash wp thash).publicInputsHash = e.publicInputsHash ∧
    (installedParseEngine e gdec hash wp thash).configurationHash = e.configurationHash ∧
    (installedParseEngine e gdec hash wp thash).deploymentValid = e.deploymentValid :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem installed_parse_keeps_transcript (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) :
    (installedParseEngine e gdec hash wp thash).initialTranscript c p = e.initialTranscript c p ∧
    Verifier.derivedRounds (installedParseEngine e gdec hash wp thash) c p =
      Verifier.derivedRounds (InstalledRoundCommit.installedRoundEngine e gdec hash wp thash) c p ∧
    Verifier.derivedIndices (installedParseEngine e gdec hash wp thash) c p =
      Verifier.derivedIndices (InstalledRoundCommit.installedRoundEngine e gdec hash wp thash) c p ∧
    Verifier.derivedContext (installedParseEngine e gdec hash wp thash) c p =
      Verifier.derivedContext (InstalledRoundCommit.installedRoundEngine e gdec hash wp thash) c p :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 6. (a) Acceptance is an exact property of the bytes -/

/-- (a) **`rootsAndClaimsMatch` IS NOW DERIVED FROM THE TRANSCRIPT.**  For the
installed parse engine the WHIR check is: the prefix executes on the proof's own
bytes, its roots are the context's, its claims satisfy the outer verifier's mask,
and the concrete tail accepts.  For an abstract engine none of the middle three
say anything about the proof. -/
theorem verify_whir_concrete_iff (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Hash) (wp : VkParams) (thash : Transcript.Hash) (ctx : Verifier.WhirContext)
    (p : Verifier.Proof) :
    Verifier.verifyWhir (installedParseEngine e gdec hash wp thash) ctx p = true ↔
      ∃ s, prefixRun hash wp ctx p.whirTranscript p.whirHints = some s ∧
        (parsedOf s).actualRoots = ctx.roots ∧
        (parsedOf s).boundRoots = ctx.roots ∧
        Verifier.claimsMatch ctx.expectedClaims (parsedOf s).claims = true ∧
        InstalledWhirTail.installedTail hash wp ctx p.whirTranscript p.whirHints (parsedOf s) =
          true := by
  have hkey : ∀ o : Option WhirTail.PrefixState,
      prefixRun hash wp ctx p.whirTranscript p.whirHints = o →
      Verifier.verifyWhir (installedParseEngine e gdec hash wp thash) ctx p =
        (match o with
         | none => false
         | some s => Verifier.rootsAndClaimsMatch ctx (parsedOf s) &&
             InstalledWhirTail.installedTail hash wp ctx p.whirTranscript p.whirHints
               (parsedOf s)) := by
    intro o ho
    show (match (prefixRun hash wp ctx p.whirTranscript p.whirHints).map parsedOf with
          | none => false
          | some parsed => Verifier.rootsAndClaimsMatch ctx parsed &&
              InstalledWhirTail.installedTail hash wp ctx p.whirTranscript p.whirHints parsed) = _
    rw [ho]
    cases o <;> rfl
  cases hs : prefixRun hash wp ctx p.whirTranscript p.whirHints with
  | none =>
      rw [hkey none hs]
      simp
  | some s =>
      rw [hkey (some s) hs]
      constructor
      · intro hacc
        rw [Bool.and_eq_true] at hacc
        have hr := Verifier.rootsAndClaimsMatch_binds_both_root_copies ctx (parsedOf s) hacc.1
        have hc := hacc.1
        simp only [Verifier.rootsAndClaimsMatch, Bool.and_eq_true] at hc
        exact ⟨s, rfl, hr.1, hr.2, hc.2, hacc.2⟩
      · rintro ⟨s', hs', ha, hb, hc, ht⟩
        cases hs'
        rw [Bool.and_eq_true]
        refine ⟨?_, ht⟩
        simp only [Verifier.rootsAndClaimsMatch, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨ha, hb⟩, hc⟩

/-- (a, refined) The root half of `rootsAndClaimsMatch` is FREE on a successful
parse, so acceptance reduces to three transcript facts: the prefix runs, the
claims it read satisfy the outer mask, and the tail accepts. -/
theorem verify_whir_concrete_iff_roots_are_free (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (thash : Transcript.Hash)
    (ctx : Verifier.WhirContext) (p : Verifier.Proof) :
    Verifier.verifyWhir (installedParseEngine e gdec hash wp thash) ctx p = true ↔
      ∃ s, prefixRun hash wp ctx p.whirTranscript p.whirHints = some s ∧
        Verifier.claimsMatch ctx.expectedClaims s.origin.initial.evaluations = true ∧
        wp.numVariables = ctx.numVariables ∧
        (InstalledWhirTail.tailRun hash wp ctx p.whirTranscript p.whirHints).isSome = true := by
  rw [verify_whir_concrete_iff]
  constructor
  · rintro ⟨s, hs, _, _, hc, ht⟩
    rw [InstalledWhirTail.installed_tail_true_iff] at ht
    exact ⟨s, hs, hc, ht.1, ht.2⟩
  · rintro ⟨s, hs, hc, hv, ht⟩
    obtain ⟨_, _, ha, hb, _⟩ :=
      concrete_parse_roots_are_the_prefix_roots hash wp ctx p.whirTranscript p.whirHints s hs
    exact ⟨s, hs, ha, hb, hc, by rw [InstalledWhirTail.installed_tail_true_iff]; exact ⟨hv, ht⟩⟩

/-- On the outer verifier's own derived context the claim comparison is automatic
too: the five bound cells are forced by `readClaims` and the sixth is unmasked on
both sides.  So for the DERIVED context, acceptance of the installed parse engine
is exactly "the prefix runs and the tail accepts".

The proof runs through `expected_claims_bound_index_below_five` and
`concrete_parse_claims_are_the_bound_cells`, whose adopted content is
`WhirPrefix.successful_prefix_keeps_roots_and_all_checked_claims` (fourth
conjunct), `InstalledWhirTail.mask_is_the_five_bound_cells` and
`InstalledWhirTail.unmask_get_of_bound`.  `Verifier.context_bound_mask_exact` and
`Verifier.context_unused_gate_norm_is_unbound` state the same mask fact in
adopted form and are not invoked. -/
theorem derived_context_claims_match_is_automatic (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) (transcript hints : Verifier.Bytes)
    (s : WhirTail.PrefixState)
    (h : prefixRun hash wp (Verifier.derivedContext (installedParseEngine e gdec hash wp thash) c p)
      transcript hints = some s) :
    Verifier.claimsMatch
      (Verifier.derivedContext (installedParseEngine e gdec hash wp thash) c p).expectedClaims
      (parsedOf s).claims = true := by
  obtain ⟨hlen, hcell⟩ := concrete_parse_claims_are_the_bound_cells hash wp _ transcript hints s h
  refine claims_match_of_pointwise _ _ hlen.symm ?_
  intro i x hx
  exact hcell i x (expected_claims_bound_index_below_five Connections.packedFold c p
    (Verifier.derivedIndices (InstalledRoundCommit.installedRoundEngine e gdec hash wp thash) c p)
    i x hx) hx

/-! ## 7. (b) Acceptance pins the roots at fixed byte positions -/

theorem receive_one_root_bytes (hash : Hash) (source : Spongefish.Bytes)
    (pr : WhirInitial.Params) (expected : Digest) (s t : Spongefish.State)
    (entry : WhirInitial.Commitment)
    (h : WhirInitial.receiveOne hash source pr expected s = some (entry, t)) :
    entry.root.val = (source.drop s.transcriptPos).take 32 ∧
    entry.boundRoot.val =
      (source.drop (s.transcriptPos + 32 + 24 * (pr.outDomainSamples * pr.numVectors))).take 32 := by
  unfold WhirInitial.receiveOne at h
  cases hr : Spongefish.proverHash hash s source with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨root, afterRoot⟩
      cases hp : Spongefish.verifierExt3Many hash pr.outDomainSamples afterRoot with
      | none => simp [hr, hp] at h
      | some pair =>
          rcases pair with ⟨points, afterPoints⟩
          cases ha : Spongefish.proverExt3Many hash source
              (pr.outDomainSamples * pr.numVectors) afterPoints with
          | none => simp [hr, hp, ha] at h
          | some pair =>
              rcases pair with ⟨answers, afterAnswers⟩
              cases hb : Spongefish.proverHash hash afterAnswers source with
              | none => simp [hr, hp, ha, hb] at h
              | some pair =>
                  rcases pair with ⟨boundRoot, next⟩
                  simp only [hr, hp, ha, hb, bind, Option.bind] at h
                  split at h
                  · cases h
                    have hroot := WhirInitial.prover_hash_exact_read hash source s afterRoot root hr
                    have hpoints := Spongefish.verifier_many_exact_count_and_counter hash
                      pr.outDomainSamples afterRoot afterPoints points hp
                    have hanswers := Spongefish.prover_many_exact_count_and_cursor hash source
                      (pr.outDomainSamples * pr.numVectors) afterPoints afterAnswers answers ha
                    have hbound := WhirInitial.prover_hash_exact_read hash source afterAnswers t
                      boundRoot hb
                    have _h1 := hroot.1
                    have _h2 := hpoints.2.1
                    have _h3 := hanswers.2.1
                    have hpos : afterAnswers.transcriptPos =
                        s.transcriptPos + 32 + 24 * (pr.outDomainSamples * pr.numVectors) := by
                      omega
                    exact ⟨hroot.2.2.2, by rw [hbound.2.2.2, hpos]⟩
                  · contradiction

theorem receive_commitments_root_bytes (hash : Hash) (source : Spongefish.Bytes)
    (pr : WhirInitial.Params) :
    ∀ (roots : List Digest) (s t : Spongefish.State) (entries : List WhirInitial.Commitment),
      WhirInitial.receiveCommitments hash source pr roots s = some (entries, t) →
      ∀ k entry, entries.get? k = some entry →
        entry.root.val =
          (source.drop (s.transcriptPos +
            k * (64 + 24 * (pr.outDomainSamples * pr.numVectors)))).take 32 ∧
        entry.boundRoot.val =
          (source.drop (s.transcriptPos +
            k * (64 + 24 * (pr.outDomainSamples * pr.numVectors)) + 32 +
            24 * (pr.outDomainSamples * pr.numVectors))).take 32 := by
  intro roots
  induction roots with
  | nil =>
      intro s t entries h k entry hk
      cases h
      simp at hk
  | cons root rest ih =>
      intro s t entries h k entry hk
      cases ho : WhirInitial.receiveOne hash source pr root s with
      | none => simp [WhirInitial.receiveCommitments, ho] at h
      | some pair =>
          rcases pair with ⟨first, next⟩
          cases hrest : WhirInitial.receiveCommitments hash source pr rest next with
          | none => simp [WhirInitial.receiveCommitments, ho, hrest] at h
          | some pair =>
              rcases pair with ⟨others, last⟩
              simp only [WhirInitial.receiveCommitments, ho, hrest, bind, Option.bind, pure,
                Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              have hone := receive_one_root_bytes hash source pr root s next first ho
              have hstep := WhirInitial.receive_one_success hash source pr root s next first ho
              have _hnext : next.transcriptPos =
                  s.transcriptPos + (64 + 24 * (pr.outDomainSamples * pr.numVectors)) :=
                hstep.2.2.2.2.1
              cases k with
              | zero =>
                  simp only [List.get?] at hk
                  cases hk
                  simpa using hone
              | succ k =>
                  simp only [List.get?] at hk
                  have hih := ih next last others hrest k entry hk
                  have hmul : (k + 1) * (64 + 24 * (pr.outDomainSamples * pr.numVectors)) =
                      k * (64 + 24 * (pr.outDomainSamples * pr.numVectors)) +
                        (64 + 24 * (pr.outDomainSamples * pr.numVectors)) :=
                    Nat.succ_mul _ _
                  have hpos : next.transcriptPos +
                      k * (64 + 24 * (pr.outDomainSamples * pr.numVectors)) =
                      s.transcriptPos + (k + 1) * (64 + 24 * (pr.outDomainSamples * pr.numVectors)) := by
                    omega
                  rw [hpos] at hih
                  exact hih

theorem prefix_run_commitment_bytes (hash : Hash) (wp : VkParams) (ctx : Verifier.WhirContext)
    (transcript hints : Verifier.Bytes) (s : WhirTail.PrefixState)
    (h : prefixRun hash wp ctx transcript hints = some s)
    (k : Nat) (root : Verifier.Root) (hk : ctx.roots.get? k = some root) :
    ((InstalledWhirTail.outerBytes transcript).drop (k * whirStride wp)).take 32 =
      (InstalledWhirTail.rootDigest root).val ∧
    ((InstalledWhirTail.outerBytes transcript).drop
        (k * whirStride wp + 32 + 24 * (wp.outDomainSamples * wp.numVectors))).take 32 =
      (InstalledWhirTail.rootDigest root).val := by
  obtain ⟨forms, _, hp⟩ := prefix_run_success_gives_whir_prefix hash wp ctx transcript hints s h
  obtain ⟨afterInitial, hinit, _, _⟩ :=
    WhirPrefix.successful_prefix_is_one_execution hash _ _ _ _ _ _ _ _ s.origin hp
  obtain ⟨entries, evaluations, oodMatrix, vectorRlc, constraintRlc,
      afterCommitments, afterClaims, afterCross, afterVectorRlc,
      hrecv, _, _, _, _, _⟩ :=
    WhirInitial.phase_initial_trace hash _ _ _ _ _ _ _ s.origin.initial hinit
  have hroots := WhirInitial.receive_commitments_success hash _ _ _ _ _ entries hrecv
  have hmap : (entries.map (·.root)).get? k = some (InstalledWhirTail.rootDigest root) := by
    rw [hroots.1]
    show (ctx.roots.map InstalledWhirTail.rootDigest).get? k = _
    rw [List.get?_eq_getElem?, List.getElem?_map, ← List.get?_eq_getElem?, hk]
    rfl
  rw [List.get?_eq_getElem?, List.getElem?_map, ← List.get?_eq_getElem?] at hmap
  cases he : entries.get? k with
  | none => rw [he] at hmap; exact absurd hmap (by simp)
  | some entry =>
      rw [he] at hmap
      have hentry : entry.root = InstalledWhirTail.rootDigest root := by
        simpa using hmap
      have hbmap : (entries.map (·.boundRoot)).get? k = some (InstalledWhirTail.rootDigest root) := by
        rw [hroots.2.1]
        show (ctx.roots.map InstalledWhirTail.rootDigest).get? k = _
        rw [List.get?_eq_getElem?, List.getElem?_map, ← List.get?_eq_getElem?, hk]
        rfl
      rw [List.get?_eq_getElem?, List.getElem?_map, ← List.get?_eq_getElem?, he] at hbmap
      have hbentry : entry.boundRoot = InstalledWhirTail.rootDigest root := by
        simpa using hbmap
      have hbytes := receive_commitments_root_bytes hash (InstalledWhirTail.outerBytes transcript)
        (WhirParameters.initialParams (InstalledWhirTail.contextParams wp ctx) forms)
        (parseRoots ctx) _ afterCommitments entries hrecv k entry he
      have hzero : (Spongefish.init hash (InstalledWhirTail.outerBytes ctx.protocolId)
          (InstalledWhirTail.outerBytes ctx.sessionId) []).transcriptPos = 0 := rfl
      rw [hzero] at hbytes
      simp only [Nat.zero_add] at hbytes
      rw [hentry] at hbytes
      rw [hbentry] at hbytes
      exact ⟨hbytes.1.symm, hbytes.2.symm⟩

/-- (b) **AN ACCEPTED TRANSCRIPT LITERALLY CARRIES THE PINNED ROOTS.**  At byte
offset `k * whirStride wp` the WHIR transcript holds the 32 big-endian bytes of
the outer verifier's `k`-th pinned root, and at
`k * whirStride wp + 32 + 24 * outDomainSamples * numVectors` it holds them
again as the bound copy.  These are the positions `WhirInitial.receiveOne` reads
(WhirInitial.lean 52-62, via `prover_hash_exact_read` 189-204), and the source's
own fixed-grammar preflight (whir_pcs.rs 1514-1556, stride at 1522-1525;
SpongefishWhirVerify.sol 374 and 384-387). -/
theorem accepted_transcript_carries_the_pinned_roots (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (thash : Transcript.Hash)
    (ctx : Verifier.WhirContext) (p : Verifier.Proof)
    (h : Verifier.verifyWhir (installedParseEngine e gdec hash wp thash) ctx p = true)
    (k : Nat) (root : Verifier.Root) (hk : ctx.roots.get? k = some root) :
    ((InstalledWhirTail.outerBytes p.whirTranscript).drop (k * whirStride wp)).take 32 =
      (Transcript.le 32 root.val).reverse ∧
    ((InstalledWhirTail.outerBytes p.whirTranscript).drop
        (k * whirStride wp + 32 + 24 * (wp.outDomainSamples * wp.numVectors))).take 32 =
      (Transcript.le 32 root.val).reverse := by
  obtain ⟨s, hs, _, _, _, _⟩ :=
    (verify_whir_concrete_iff e gdec hash wp thash ctx p).mp h
  exact prefix_run_commitment_bytes hash wp ctx p.whirTranscript p.whirHints s hs k root hk

/-! ## 8. (c) A wrong root in the transcript is rejected -/

theorem parse_none_rejects (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Hash)
    (wp : VkParams) (thash : Transcript.Hash) (ctx : Verifier.WhirContext) (p : Verifier.Proof)
    (h : prefixRun hash wp ctx p.whirTranscript p.whirHints = none) :
    Verifier.verifyWhir (installedParseEngine e gdec hash wp thash) ctx p = false := by
  cases hv : Verifier.verifyWhir (installedParseEngine e gdec hash wp thash) ctx p with
  | false => rfl
  | true =>
      obtain ⟨s, hs, _, _, _, _⟩ := (verify_whir_concrete_iff e gdec hash wp thash ctx p).mp hv
      rw [h] at hs
      exact absurd hs (by simp)

/-- (c) **A TRANSCRIPT WHOSE FIRST ROOT IS WRONG IS REJECTED.**  This is a
genuine rejection theorem about the BYTES: it has no analogue for the abstract
engine, whose `parseWhir` may return `some ⟨ctx.roots, ctx.roots, …⟩` for any
transcript whatsoever (`Verifier.testEngine`, Verifier.lean 609).

`pre` is the head of `ctx.roots`, which at the outer verifier's own
`derivedContext` is `p.preprocessedRoot`; for the PINNED root at the whole
verifier see `accepted_verify_first_root_is_pinned`.  The hypothesis `hbytes` is
an inequality on `take 32`, so it also covers a transcript SHORTER than 32 bytes:
a missing first root falsifies it just as a wrong one does, and the empty
transcript of section 10 is the extreme case. -/
theorem wrong_root_in_transcript_is_rejected (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (thash : Transcript.Hash)
    (ctx : Verifier.WhirContext) (p : Verifier.Proof) (pre : Verifier.Root)
    (rest : List Verifier.Root) (hroots : ctx.roots = pre :: rest)
    (hbytes : (InstalledWhirTail.outerBytes p.whirTranscript).take 32 ≠
      (Transcript.le 32 pre.val).reverse) :
    concreteParseWhir hash wp ctx p.whirTranscript p.whirHints = none ∧
    Verifier.verifyWhir (installedParseEngine e gdec hash wp thash) ctx p = false := by
  have hnone : prefixRun hash wp ctx p.whirTranscript p.whirHints = none := by
    cases hs : prefixRun hash wp ctx p.whirTranscript p.whirHints with
    | none => rfl
    | some s =>
        have hk : ctx.roots.get? 0 = some pre := by rw [hroots]; rfl
        have hb := prefix_run_commitment_bytes hash wp ctx p.whirTranscript p.whirHints s hs 0 pre hk
        exact absurd (by simpa using hb.1) hbytes
  exact ⟨by simp [concreteParseWhir, hnone],
    parse_none_rejects e gdec hash wp thash ctx p hnone⟩

/-! ## 9. Acceptance of the whole verifier -/

/-- The installed-parse counterpart of
`Verifier.acceptance_exact_whir_and_terminal_binding`: the existential `parsed`
of the adopted statement is no longer an arbitrary engine output, it is the
projection of ONE concrete prefix execution on the proof's own bytes, whose roots
are the pinned roots and whose five bound cells are the outer verifier's expected
claims. -/
theorem accepted_verification_parses_the_concrete_prefix (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (thash : Transcript.Hash)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Verifier.verify (installedParseEngine e gdec hash wp thash) pin chain c p = .ok ()) :
    ∃ s, prefixRun hash wp (Verifier.derivedContext (installedParseEngine e gdec hash wp thash) c p)
          p.whirTranscript p.whirHints = some s ∧
      concreteParseWhir hash wp
          (Verifier.derivedContext (installedParseEngine e gdec hash wp thash) c p)
          p.whirTranscript p.whirHints = some (parsedOf s) ∧
      (parsedOf s).actualRoots = [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      (parsedOf s).boundRoots = [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      (parsedOf s).claims = s.origin.initial.evaluations ∧
      InstalledWhirTail.installedTail hash wp
        (Verifier.derivedContext (installedParseEngine e gdec hash wp thash) c p)
        p.whirTranscript p.whirHints (parsedOf s) = true := by
  have hw := (Verifier.verify_success_checks (installedParseEngine e gdec hash wp thash) pin chain
    c p h).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨s, hs, ha, hb, _, ht⟩ :=
    (verify_whir_concrete_iff e gdec hash wp thash _ p).mp hw
  have hr := (Verifier.acceptance_protocol_and_pinned_root (installedParseEngine e gdec hash wp thash)
    pin chain c p h).2
  refine ⟨s, hs, by simp [concreteParseWhir, hs], ?_, ?_, rfl, ht⟩
  · rw [ha]; simp [Verifier.derivedContext, Verifier.whirContext, hr]
  · rw [hb]; simp [Verifier.derivedContext, Verifier.whirContext, hr]

/-- (b, at the whole verifier) **AN ACCEPTED PROOF'S TRANSCRIPT OPENS WITH THE
PINNED PREPROCESSED ROOT.**  At `Verifier.derivedContext` the root list is
`[p.preprocessedRoot, p.witnessRoot, p.normInverseRoot]` (`Verifier.whirContext`,
Verifier.lean 249-251), i.e. the PROOF's root; the pinned root enters only
through `Verifier.verify`'s own check, whose adopted consequence is
`Verifier.acceptance_protocol_and_pinned_root`.  Combining the two gives the
statement in the pinned root: if the whole verifier accepts, the first 32 bytes
of the WHIR transcript are the big-endian encoding of `pin.preprocessedRoot`. -/
theorem accepted_verify_first_root_is_pinned (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (thash : Transcript.Hash)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Verifier.verify (installedParseEngine e gdec hash wp thash) pin chain c p = .ok ()) :
    (InstalledWhirTail.outerBytes p.whirTranscript).take 32 =
      (Transcript.le 32 pin.preprocessedRoot.val).reverse := by
  have hw := (Verifier.verify_success_checks (installedParseEngine e gdec hash wp thash) pin chain
    c p h).2.2.2.2.2.2.2.2.2.2.1
  have hr := (Verifier.acceptance_protocol_and_pinned_root
    (installedParseEngine e gdec hash wp thash) pin chain c p h).2
  have hk : (Verifier.derivedContext (installedParseEngine e gdec hash wp thash) c p).roots.get? 0 =
      some pin.preprocessedRoot := by
    simp [Verifier.derivedContext, Verifier.whirContext, hr]
  have := (accepted_transcript_carries_the_pinned_roots e gdec hash wp thash _ p hw 0
    pin.preprocessedRoot hk).1
  simpa using this

/-! ## 10. Example: the concrete parser rejects what the abstract one accepted -/

abbrev exampleContext : Verifier.WhirContext :=
  InstalledWhirTail.installedContext Integrated.exampleEngine Integrated.exampleDecoder
    InstalledWhirTail.exampleHash InstalledWhirTail.exampleVk Integrated.exampleConfig
    Integrated.exampleProof

abbrev exampleParseEngine : Verifier.Engine :=
  installedParseEngine Integrated.exampleEngine Integrated.exampleDecoder
    InstalledWhirTail.exampleHash InstalledWhirTail.exampleVk InstalledRoundCommit.toyHash

set_option maxRecDepth 65536 in
/-- The adopted example proof has EMPTY `whirTranscript`, so the concrete prefix
cannot even read the first commitment root: the installed parse returns `none`.
The parameter projection is admissible on this context
(`InstalledWhirTail.example_context_parameters_are_admissible`), so this is a
TRANSCRIPT failure, not a parameter-admission failure. -/
theorem example_concrete_parse_rejects_the_empty_transcript :
    prefixRun InstalledWhirTail.exampleHash InstalledWhirTail.exampleVk exampleContext
      Integrated.exampleProof.whirTranscript Integrated.exampleProof.whirHints = none ∧
    concreteParseWhir InstalledWhirTail.exampleHash InstalledWhirTail.exampleVk exampleContext
      Integrated.exampleProof.whirTranscript Integrated.exampleProof.whirHints = none := by
  refine ⟨rfl, rfl⟩

set_option maxRecDepth 65536 in
/-- **THE ABSTRACT PARSERS ACCEPT THE SAME BYTES.**  `Verifier.testEngine`
returns the context's roots and six zero claims for the EMPTY transcript, and
`Integrated.exampleEngine` returns the context's roots and the unmasked expected
claims -- so for both, `rootsAndClaimsMatch` holds with no transcript content at
all.  That is the observation this module removes. -/
theorem example_abstract_parsers_accept_the_empty_transcript :
    Verifier.testEngine.parseWhir exampleContext Integrated.exampleProof.whirTranscript
        Integrated.exampleProof.whirHints =
      some ⟨exampleContext.roots, exampleContext.roots, List.replicate 6 Verifier.zero⟩ ∧
    Integrated.exampleEngine.parseWhir exampleContext Integrated.exampleProof.whirTranscript
        Integrated.exampleProof.whirHints =
      some ⟨exampleContext.roots, exampleContext.roots,
        OpeningBinding.unmask exampleContext.expectedClaims⟩ ∧
    Verifier.rootsAndClaimsMatch exampleContext
        ⟨exampleContext.roots, exampleContext.roots,
          OpeningBinding.unmask exampleContext.expectedClaims⟩ = true := by
  refine ⟨rfl, rfl, ?_⟩
  have hcm : Verifier.claimsMatch exampleContext.expectedClaims
      (OpeningBinding.unmask exampleContext.expectedClaims) = true :=
    OpeningBinding.claimsMatch_unmask _
  simp [Verifier.rootsAndClaimsMatch, hcm]

set_option maxRecDepth 65536 in
/-- The installed parse engine rejects the call at the PARSE, before the tail is
ever consulted. -/
theorem example_installed_parse_engine_rejects :
    Verifier.verifyWhir exampleParseEngine exampleContext Integrated.exampleProof = false :=
  parse_none_rejects Integrated.exampleEngine Integrated.exampleDecoder
    InstalledWhirTail.exampleHash InstalledWhirTail.exampleVk InstalledRoundCommit.toyHash
    exampleContext Integrated.exampleProof example_concrete_parse_rejects_the_empty_transcript.1

end Audit.Wire3.InstalledWhirParse
