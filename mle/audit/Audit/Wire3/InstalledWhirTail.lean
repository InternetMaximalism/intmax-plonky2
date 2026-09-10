import Audit.Wire3.OpeningBinding
import Audit.Wire3.WhirConfigured

/-!
# Installing the concrete WHIR tail into the outer verifier engine

## What this module does

The adopted `Verifier.Engine` carries the WHIR check as TWO opaque function
observations, `parseWhir` and `whirTail` (Verifier.lean 345-368), and
`Integrated.modelEngine` deliberately leaves both abstract: its own header says
"WhirFinal and Merkle are not silently installed as a complete whirTail".  That
is residue R1 of `OpeningBinding`: `blind_engine_accepts_every_context` exhibits
an engine that agrees with any given one on every derived round, index and
context and whose WHIR check accepts EVERY proof, so no theorem about the
abstract engine can connect acceptance to concrete Merkle/WHIR openings.

`installedEngine e decode hash wp` is `Integrated.modelEngine e decode` with
`whirTail` replaced by the adopted concrete manual model
`WhirConfigured.run` -- one checked `WhirParameters.Params`, its checked
projections into `WhirTail.run`, and thence `WhirPrefix` / `WhirInitial` /
`WhirIntermediate` / `WhirRows` / `Merkle` / `WhirFinal` / `WhirTerminal`.
Nothing in the concrete WHIR model is re-proved here; every result below is a
composition of ADOPTED lemmas across the newly closed interface.

## Which route is covered: finalsplit versus round one

`WhirConfigured` reaches the Merkle openings by two different code paths, and
this module now covers BOTH, under separate and explicitly named hypotheses.

* `wp.numRounds = 0` -- no intermediate round.  `WhirTail`'s finalsplit branch
  (`openSplitGroups`) opens the three pinned roots itself, at
  `(WhirConfigured.finalParams wp).openParams.merkleDepth`.  The theorems whose
  names end in `_finalsplit` are about THIS branch.  It is NOT the deployed
  profile: `SpongefishWhirVerify.sol` 560 takes it only when
  `params.numRounds == 0 && params.numCommitments > 1`, and every v2 fixture has
  `numRounds` in `{1,2,3,4}` (`contracts/test/fixtures/v2_cross_language.json`
  has `whirParams {numVariables 10, numCommitments 3, numRounds 1}`;
  `v2_max_resource.json` has `{21, 3, 4}`), with folding factor 4 on the Rust
  side (`WHIR_FOLDING_FACTOR_V2 = 4`, mle_whir_v2.rs 37 -- line 21 of that file
  is `NUM_PACKED_VECTORS_PER_GROUP_V2`, not the folding factor -- consumed at
  whir_pcs.rs 1196-1200).  `numRounds = 0` is a toy size only.
* `wp.rounds ≠ []` -- at least one intermediate round, i.e. the DEPLOYED v2
  profile.  Then the three pinned roots are opened in ROUND ONE instead:
  `WhirIntermediate.rootsToOpen s = if s.completedRounds = 0 then s.initialRoots
  else [s.previousRoot]` (WhirIntermediate.lean 73-74), fed to
  `WhirRows.openGroups` by `openPrevious`
  (`opening_success_uses_previous_roots`, 244-251), at
  `(WhirConfigured.initialOpen wp).merkleDepth` -- NOT at `finalParams`' depth.
  The theorems whose names end in `_round_one` are about THIS branch.

## How the outer objects are mapped into the WHIR session

* `protocolId` / `sessionId`: `ctx.protocolId` / `ctx.sessionId`.  In Lean these
  are the FREE `Verifier.Config` fields `whirProtocolId` / `whirSessionId`
  (Verifier.lean 88-89), copied into the context by `Verifier.whirContext`
  (Verifier.lean 250); nothing in the Lean model ties them to a profile except
  the `deploymentValid` OBSERVATION.  In the source they are
  `protocol_id_for_config` and `whir_session_id(session_name)` (whir_pcs.rs
  476-478, in the replay preflight's constructor).  `WhirPCS::verify_grouped`
  absorbs them at whir_pcs.rs 1587-1589 --
  `DomainSeparator::protocol(&config).session(&session_name.to_string())
  .instance(&Empty)`, the `.session` line being 1588 -- and `session_name` is
  the caller's `WHIR_SESSION_SPLIT_V2`, which reaches the VK check as
  `whir_session_id(WHIR_SESSION_SPLIT_V2)` at verifier_v2.rs 170 (the
  protocol/session `ensure!` spans verifier_v2.rs 168-175).  whir_pcs.rs
  1557-1559 is NOT the session absorb: it is the head of `verify_grouped`'s
  `expected_roots` preflight loop, which is what the actual/bound root
  comparison below cites.  The pair is pinned on chain as the immutables at
  MleVerifierV2.sol 366-367 and 735-737.  (verifier_v2.rs 244-245, cited by an
  earlier draft of this header, is the OUTER transcript, not the WHIR session.)
* `instanceBytes`: EMPTY.  `WhirPCS::verify_grouped` builds its domain
  separator as `DomainSeparator::protocol(&config).session(&session_name)
  .instance(&Empty)` (whir_pcs.rs 1587-1589), so the WHIR session absorbs no
  public instance.  The binding to the outer transcript is carried entirely by
  the roots and the expected claims, which `verify_grouped` checks against
  `expected_roots` (the loop at whir_pcs.rs 1557-1559, comparing BOTH the actual
  root and the bound root against the outer transcript's) / `expected_evals`
  before replaying -- modelled exactly by
  `WhirInitial.receiveOne` (actual root AND bound root) and
  `WhirInitial.readClaims` (masked claim comparison).  This is a manual reading
  of the source, not a proved refinement.
* `source` / `hints`: `p.whirTranscript` / `p.whirHints` through the adopted
  lossless `WhirFinalSpongefish.toTranscriptBytes` UInt8/Fin 256 adapter.
* `roots`: `ctx.roots` -- the three pinned Merkle roots -- through `rootDigest`,
  the inverse of the adopted lossless `WhirTail.rootWord` projection.
* `expected` / `mask`: `OpeningBinding.unmask ctx.expectedClaims` with the fixed
  protocol mask `whirMask = [31]`, whose bits are proved to be exactly the five
  bound cells of `Verifier.expectedClaims` (`mask_is_the_five_bound_cells`,
  `Verifier.context_bound_mask_exact`).
* evaluation points: `contextParams` overwrites the parameter record's
  `evaluationPoint` / `evaluationPoint2` / `additionalEvaluationPoints` with
  `ctx.points`, so the WHIR points are the outer verifier's own packed points
  and not a free parameter.  The engine additionally checks
  `wp.numVariables = ctx.numVariables`.

## `wp` IS A FREE PARAMETER (what the parameter theorems do and do not say)

Every other WHIR parameter -- the Merkle depth, the domain, the folding
schedule -- is a projection of the RECORD `wp`, unchanged by `contextParams`
(`tail_params_are_wp_projections`).  That is a statement about `contextParams`
only.  `wp` itself is a FREE argument of `installedEngine`: nothing in this
module connects it to `c.whirEncoding`, to `e.configurationHash` or to
`e.deploymentValid`.  In the source it is pinned by the profile digest
(`CanonicalWhirProfileV2.validateCanonical`, MleVerifierV2.sol 151-153); in Lean
that is an OBSERVATION, not a theorem.

The only part of `wp` genuinely derived from acceptance is that
`WhirParameters.checkBound` succeeded -- and `checkBound` does NOT force
`0 < wp.inDomainSamples`.  An adversarial `wp` with `inDomainSamples = 0` passes
admission, samples no query index, and makes every `Merkle.verify … [] [] =
some _` vacuously true.  Every Merkle theorem below therefore carries an
EXPLICIT positivity hypothesis and additionally CONCLUDES that the query-index
list is nonempty, through the adopted
`WhirSampling.reference_nonempty_request_has_nonempty_output`.

## Which engine fields are INSTALLED and which remain OBSERVATIONS

INSTALLED (concrete, executable):
`foldClaim`, `normEvaluation`, `eqEvaluation`, `gateEvaluation` (all four from
the adopted `Integrated.modelEngine`) and, new here, `whirTail`.

STILL OBSERVATIONS (unchanged, opaque):
`configurationHash`, `deploymentValid`, `initialObservation` (hence
`initialTranscript`), `commitRound`, `sampleIndices`, `publicInputsHash`, and
`parseWhir`.  `parseWhir` is deliberately NOT installed: the adopted tree
contains no concrete parser for `Verifier.ParsedWhir`, and the point of this
module is the TAIL.  Consequently `rootsAndClaimsMatch` still compares the
context with an OBSERVED parse; the concrete guarantees below come from the
tail's own execution, not from the parse.

## What is proved, and what is not

The blind-engine counterexample no longer applies to THIS engine
(`installed_engine_is_not_blind`), but every adopted theorem about the abstract
engine is unchanged: `installedEngine` is a new engine, not a repair of the old
ones, and `installed_engine_keeps_transcript` shows it keeps the initial
transcript, derived rounds, derived indices and derived context, so every
adopted theorem quantified over an arbitrary engine applies to it.

NOT proved, and not claimed anywhere below: whole-source (Rust/Yul/Solidity)
equivalence; WHIR / PCS probabilistic soundness; proximity or list-decoding;
query repetition; Merkle collision PROBABILITY (`OpeningBinding.NoCollision`
remains deterministic injectivity on an execution-computed finite list, and
`OpeningBinding.clash_no_collision_fails` shows it can be false); hash security
or Fiat--Shamir independence -- `hash` is an arbitrary deterministic function
throughout, and the examples use a constant toy hash, not Keccak.  Residue R1b
(`TailExtractsCommittedTables`) remains an explicit assumption -- it is WHIR
proximity / list decoding plus sumcheck soundness, probabilistic, and absent
from the adopted tree.

**R1b as formulated subsumes R3 (per-column identification); R2 is untouched.**
`OpeningBinding.OpensCommittedTable` is `IntegratedTerminalChain.HonestOpenings`,
whose `opened` field is PER COLUMN -- it says the proof's opened cells for a
group ARE the per-column row folds of `cols i`.  So assuming R1b uniformly, as
`TailExtractsCommittedTables` does, assumes column identification as well, which
is residue R3.  The WHIR claim itself binds strictly less: only
`Connections.packedFold cells (Verifier.width c) idx`, one field element per
cell.  `TailExtractsFoldLevel` below is that weaker, R3-free shape, and
`tail_extraction_committed_tables_gives_fold_level` proves R1b implies it (the
converse is NOT claimed).  Where per-column identification comes from in the
DEPLOYED protocol is an OBSERVATION here, not a theorem: the index point is
sampled AFTER the cells are committed to the outer transcript
(`derivedIndices e c p = e.sampleIndices (derivedRounds e c p).transcript p.used
c.indexBits`, Verifier.lean 389-390 -- `p.used` is an input to the sampling, so
the fold's evaluation point cannot be chosen with the cells in hand).  Residue
R2 of `OpeningBinding` (binding is not extraction) is untouched by this module.

Nothing here is the deployed system's soundness error.  The wire-v3 WHIR profile
this models is the ~100-bit design point.
-/

namespace Audit.Wire3.InstalledWhirTail
open Spongefish (Hash Digest)

abbrev VkParams := WhirParameters.Params

def outerBytes (b : Verifier.Bytes) : Spongefish.Bytes := WhirFinalSpongefish.toTranscriptBytes b

def rootDigest (r : Verifier.Root) : Digest :=
  ⟨(Transcript.le 32 r.val).reverse, by simp [Transcript.le_length]⟩

theorem root_digest_is_lossless (r : Verifier.Root) :
    WhirTail.rootBytes (WhirTail.rootWord (rootDigest r)) = (rootDigest r).val :=
  WhirTail.root_projection_is_lossless (rootDigest r)

def whirMask : Spongefish.Bytes := [⟨31, by decide⟩]

theorem mask_is_the_five_bound_cells :
    whirMask.length = (6 + 7) / 8 ∧
    (∀ i, i < 5 → WhirInitial.isChecked whirMask i) ∧
    ¬ WhirInitial.isChecked whirMask 5 := by
  refine ⟨rfl, ?_, by decide⟩
  intro i hi
  interval_cases i <;> decide

def contextParams (wp : VkParams) (ctx : Verifier.WhirContext) : VkParams :=
  { wp with
    evaluationPoint := ctx.points.headD [],
    evaluationPoint2 := (ctx.points.drop 1).headD [],
    additionalEvaluationPoints := ctx.points.drop 2 }

def tailRun (hash : Hash) (wp : VkParams) (ctx : Verifier.WhirContext)
    (transcript hints : Verifier.Bytes) : Option WhirTail.Result :=
  WhirConfigured.run hash (outerBytes ctx.protocolId) (outerBytes ctx.sessionId) []
    (outerBytes transcript) (outerBytes hints) (contextParams wp ctx)
    (ctx.roots.map rootDigest) (OpeningBinding.unmask ctx.expectedClaims) whirMask

def installedTail (hash : Hash) (wp : VkParams) :
    Verifier.WhirContext → Verifier.Bytes → Verifier.Bytes → Verifier.ParsedWhir → Bool :=
  fun ctx transcript hints _ =>
    decide (wp.numVariables = ctx.numVariables) && (tailRun hash wp ctx transcript hints).isSome

def installedEngine (e : Verifier.Engine) (decode : Integrated.DecodeGates) (hash : Hash)
    (wp : VkParams) : Verifier.Engine :=
  { Integrated.modelEngine e decode with whirTail := installedTail hash wp }

/-! ## Transcript preservation -/

theorem installed_engine_keeps_transcript (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (hash : Hash) (wp : VkParams) (c : Verifier.Config) (p : Verifier.Proof) :
    (installedEngine e decode hash wp).initialTranscript c p = e.initialTranscript c p ∧
    Verifier.derivedRounds (installedEngine e decode hash wp) c p = Verifier.derivedRounds e c p ∧
    Verifier.derivedIndices (installedEngine e decode hash wp) c p = Verifier.derivedIndices e c p ∧
    Verifier.derivedContext (installedEngine e decode hash wp) c p =
      Verifier.derivedContext (Integrated.modelEngine e decode) c p :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem installed_engine_is_its_own_model_engine (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) :
    Integrated.modelEngine (installedEngine e decode hash wp) decode = installedEngine e decode hash wp :=
  rfl

theorem installed_engine_keeps_every_other_field (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) :
    (installedEngine e decode hash wp).configurationHash = e.configurationHash ∧
    (installedEngine e decode hash wp).deploymentValid = e.deploymentValid ∧
    (installedEngine e decode hash wp).initialObservation = e.initialObservation ∧
    (installedEngine e decode hash wp).commitRound = e.commitRound ∧
    (installedEngine e decode hash wp).sampleIndices = e.sampleIndices ∧
    (installedEngine e decode hash wp).publicInputsHash = e.publicInputsHash ∧
    (installedEngine e decode hash wp).parseWhir = e.parseWhir ∧
    (installedEngine e decode hash wp).foldClaim = Connections.packedFold ∧
    (installedEngine e decode hash wp).whirTail = installedTail hash wp :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Acceptance runs the concrete tail -/

theorem unmask_get_of_bound (xs : List (Option Verifier.Ext3)) (i : Nat) (x : Verifier.Ext3)
    (h : xs[i]? = some (some x)) : (OpeningBinding.unmask xs).getD i Verifier.zero = x := by
  simp [OpeningBinding.unmask, List.getD, List.get?_eq_getElem?, h]

theorem installed_tail_true_iff (hash : Hash) (wp : VkParams) (ctx : Verifier.WhirContext)
    (transcript hints : Verifier.Bytes) (parsed : Verifier.ParsedWhir) :
    installedTail hash wp ctx transcript hints parsed = true ↔
      wp.numVariables = ctx.numVariables ∧ (tailRun hash wp ctx transcript hints).isSome = true := by
  simp [installedTail]

theorem installed_whir_acceptance_runs_the_tail (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (ctx : Verifier.WhirContext)
    (p : Verifier.Proof)
    (h : Verifier.verifyWhir (installedEngine e decode hash wp) ctx p = true) :
    wp.numVariables = ctx.numVariables ∧
      ∃ r, tailRun hash wp ctx p.whirTranscript p.whirHints = some r := by
  obtain ⟨parsed, _, _, _, _, ht⟩ :=
    Verifier.whir_acceptance_requires_bound_statement (installedEngine e decode hash wp) ctx p h
  have ht' : installedTail hash wp ctx p.whirTranscript p.whirHints parsed = true := ht
  rw [installed_tail_true_iff] at ht'
  exact ⟨ht'.1, Option.isSome_iff_exists.mp ht'.2⟩

theorem installed_acceptance_context_is_the_pinned_statement (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Verifier.verify (installedEngine e decode hash wp) pin chain c p = .ok ()) :
    (Verifier.derivedContext (installedEngine e decode hash wp) c p).roots =
      [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
    (Verifier.derivedContext (installedEngine e decode hash wp) c p).numVariables =
      c.degreeBits + c.indexBits ∧
    (Verifier.derivedContext (installedEngine e decode hash wp) c p).expectedClaims =
      Verifier.expectedClaims Connections.packedFold c p (Verifier.derivedIndices e c p) := by
  have hr := (Verifier.acceptance_protocol_and_pinned_root (installedEngine e decode hash wp)
    pin chain c p h).2
  exact ⟨by simp [Verifier.derivedContext, Verifier.whirContext, hr], rfl, rfl⟩

theorem unmask_context_claims_length (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (hash : Hash) (wp : VkParams) (c : Verifier.Config) (p : Verifier.Proof) :
    (OpeningBinding.unmask
      (Verifier.derivedContext (installedEngine e decode hash wp) c p).expectedClaims).length = 6 := by
  simp [OpeningBinding.unmask, Verifier.derivedContext, Verifier.whirContext, Verifier.expectedClaims]

/-- The five bound entries the concrete execution reads are exactly the outer
verifier's five bound expected claims, in the Solidity cell order. -/
theorem unmask_context_claim_cell (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (hash : Hash) (wp : VkParams) (c : Verifier.Config) (p : Verifier.Proof) (i : Fin 5) :
    (OpeningBinding.unmask
        (Verifier.derivedContext (installedEngine e decode hash wp) c p).expectedClaims).getD
      i.val Verifier.zero =
      Connections.packedFold (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).1
        (Verifier.width c) (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2 := by
  refine unmask_get_of_bound _ i.val _ ?_
  exact OpenedClaimFold.expected_claim_cell_exact Connections.packedFold c p
    (Verifier.derivedIndices e c p) i

/-- THE KEY THEOREM.  Acceptance of the installed engine is not an opaque
observation: it exhibits ONE successful concrete execution of the adopted manual
WHIR model on this proof's own transcript and hint bytes, under the WHIR
parameters derived from the record `wp` and the context's own packed points.
That execution absorbed exactly the three pinned Merkle roots, as BOTH the
actual and the bound commitment copies, and read exactly the five bound expected
claims of the outer verifier. -/
theorem installed_acceptance_runs_the_concrete_tail (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ()) :
    ∃ r, tailRun hash wp (Verifier.derivedContext (installedEngine e decode hash wp) c p)
          p.whirTranscript p.whirHints = some r ∧
      wp.numVariables = c.degreeBits + c.indexBits ∧
      (Verifier.derivedContext (installedEngine e decode hash wp) c p).roots =
        [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      r.retained.origin.initial.commitments.map (·.root) =
        [rootDigest pin.preprocessedRoot, rootDigest p.witnessRoot, rootDigest p.normInverseRoot] ∧
      r.retained.origin.initial.commitments.map (·.boundRoot) =
        [rootDigest pin.preprocessedRoot, rootDigest p.witnessRoot, rootDigest p.normInverseRoot] ∧
      ∀ i : Fin 5, r.retained.origin.initial.evaluations.getD i.val Verifier.zero =
        Connections.packedFold (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).1
          (Verifier.width c) (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2 := by
  obtain ⟨_, _, _, _, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier (installedEngine e decode hash wp) decode
      pin chain c p h
  have hv : Verifier.verify (installedEngine e decode hash wp) pin chain c p = .ok () := hv
  have hctx := installed_acceptance_context_is_the_pinned_statement e decode hash wp pin chain c p hv
  have hw := (Verifier.verify_success_checks (installedEngine e decode hash wp) pin chain c p
    hv).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hvars, r, hrun⟩ := installed_whir_acceptance_runs_the_tail e decode hash wp
    (Verifier.derivedContext (installedEngine e decode hash wp) c p) p hw
  obtain ⟨forms, _, hprefix, _, _⟩ :=
    WhirConfigured.configured_success_initial_and_intermediate_provenance hash _ _ _ _ _ _ _ _ _ r hrun
  have hkeep := WhirPrefix.successful_prefix_keeps_roots_and_all_checked_claims hash _ _ _ _ _ _ _ _
    r.retained.origin hprefix
  have hlen := unmask_context_claims_length e decode hash wp c p
  refine ⟨r, hrun, by rw [hvars, hctx.2.1], hctx.1, ?_, ?_, ?_⟩
  · rw [hkeep.1, hctx.1]; rfl
  · rw [hkeep.2.1, hctx.1]; rfl
  · intro i
    have hb : i.val < 5 := i.isLt
    have hi : i.val < (OpeningBinding.unmask
        (Verifier.derivedContext (installedEngine e decode hash wp) c p).expectedClaims).length := by
      omega
    have := hkeep.2.2.2.1 i.val hi ((mask_is_the_five_bound_cells).2.1 i.val hb)
    rw [this]
    exact unmask_context_claim_cell e decode hash wp c p i

/-! ## Acceptance opens Merkle-authenticated rows under the pinned roots -/

abbrev installedContext (e : Verifier.Engine) (decode : Integrated.DecodeGates) (hash : Hash)
    (wp : VkParams) (c : Verifier.Config) (p : Verifier.Proof) : Verifier.WhirContext :=
  Verifier.derivedContext (installedEngine e decode hash wp) c p

/-- Substituting the context's packed points changes NO other field of the
parameter record: the final opening parameters, the round-one opening
parameters, the Merkle depths and the round schedule are all projections of the
record `wp` itself.  This says nothing about where `wp` comes from -- `wp` is a
free argument of `installedEngine`, pinned in the source only by the profile
digest (`CanonicalWhirProfileV2.validateCanonical`, MleVerifierV2.sol 151-153),
which is an observation in Lean and not a theorem here. -/
theorem tail_params_are_wp_projections (wp : VkParams) (ctx : Verifier.WhirContext) :
    WhirConfigured.finalParams (contextParams wp ctx) = WhirConfigured.finalParams wp ∧
    WhirConfigured.initialOpen (contextParams wp ctx) = WhirConfigured.initialOpen wp ∧
    (contextParams wp ctx).rounds = wp.rounds :=
  ⟨rfl, rfl, rfl⟩

/-! ### The finalsplit route (`wp.numRounds = 0`, NOT the deployed profile) -/

/-- On the zero-intermediate-round route (`hnr : wp.numRounds = 0`, which selects
`WhirTail`'s finalsplit branch), a successful concrete tail authenticates, for
EVERY commitment position of the outer verifier's pinned root list, the raw rows
the execution itself returned, against THAT root, at the final Merkle depth and
the executed query indices, over the proof's own hint bytes; and the query-index
list is nonempty.  This is NOT the deployed profile -- every v2 fixture has
`numRounds ≥ 1`, for which see the `_round_one` theorems below.  Composed from
the adopted `WhirTail.accepted_split_tail_each_initial_root_has_actual_merkle`
and `WhirSampling.reference_nonempty_request_has_nonempty_output`; no WHIR
internal is re-proved here. -/
theorem installed_acceptance_group_authentication_finalsplit (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (hnr : wp.numRounds = 0)
    (hsamples : 0 < (WhirConfigured.finalParams wp).openParams.inDomainSamples)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (position : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root)
    (r : WhirTail.Result)
    (hrun : tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints =
      some r) :
    ∃ (rows : List WhirRows.RawRow) (offset next : Nat),
      r.retained.current.completedRounds = 0 ∧
      r.rows.indices ≠ [] ∧
      r.rows.opened.groups.get? position = some rows ∧
      Merkle.verify hash (rootDigest root) (WhirConfigured.finalParams wp).openParams.merkleDepth
        r.rows.indices (WhirRows.rowHashes hash rows) (outerBytes p.whirHints) offset = some next := by
  obtain ⟨r₀, hrun₀, _, _, hcommit, _, _⟩ :=
    installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p h
  have hr : r = r₀ := (Option.some.inj (hrun₀.symm.trans hrun)).symm
  subst hr
  obtain ⟨forms, _, _, hinter, htail⟩ :=
    WhirConfigured.configured_success_initial_and_intermediate_provenance hash _ _ _ _ _ _ _ _ _ r hrun
  have hzero : r.retained.current.completedRounds = 0 := by
    rw [WhirConfigured.configured_success_completed_round_count_exact hash _ _ _ _ _ _ _ _ _ r hrun]
    exact hnr
  have hkeep := (WhirIntermediate.all_rounds_keep_initial_binding_and_constraint_count hash _ _ _
    (WhirIntermediate.fromPrefix r.retained.origin) r.retained.current hinter).1
  have hinit : r.retained.current.initialRoots =
      [rootDigest pin.preprocessedRoot, rootDigest p.witnessRoot, rootDigest p.normInverseRoot] := by
    rw [hkeep]; exact hcommit
  have hget : r.retained.current.initialRoots.get? position = some (rootDigest root) := by
    rw [hinit]
    match position, hpos with
    | 0, hpos => simpa using congrArg (Option.map rootDigest) hpos
    | 1, hpos => simpa using congrArg (Option.map rootDigest) hpos
    | 2, hpos => simpa using congrArg (Option.map rootDigest) hpos
  have hfinal := (WhirTail.tail_success_same_vector_and_context hash _ _ _ _ r htail).2.1
  obtain ⟨_, afterPow, afterSampling, _, _, hsample, _, _⟩ :=
    WhirTail.final_rows_success_is_one_source_execution hash _ _ _ _ r.rows hfinal
  have hne : r.rows.indices ≠ [] :=
    WhirSampling.reference_nonempty_request_has_nonempty_output hash afterPow afterSampling _ _ _
      hsamples.ne' hsample
  obtain ⟨_, _, after, group, _, afterRows, hgroup, _, _, hmerkle⟩ :=
    WhirTail.accepted_split_tail_each_initial_root_has_actual_merkle hash _ _ _ r.retained r
      position (rootDigest root) hzero hget htail
  exact ⟨group.rows, afterRows.hintPos, after.hintPos, hzero, hne, hgroup, hmerkle⟩

/-- The same statement with the concrete execution existentially exhibited from
outer acceptance alone.  Finalsplit route only (`wp.numRounds = 0`). -/
theorem installed_acceptance_opens_authenticated_rows_finalsplit (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (hnr : wp.numRounds = 0)
    (hsamples : 0 < (WhirConfigured.finalParams wp).openParams.inDomainSamples)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (position : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root) :
    ∃ (r : WhirTail.Result) (rows : List WhirRows.RawRow) (offset next : Nat),
      tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints = some r ∧
      r.rows.indices ≠ [] ∧
      r.rows.opened.groups.get? position = some rows ∧
      Merkle.verify hash (rootDigest root) (WhirConfigured.finalParams wp).openParams.merkleDepth
        r.rows.indices (WhirRows.rowHashes hash rows) (outerBytes p.whirHints) offset = some next := by
  obtain ⟨r, hrun, _, _, _, _, _⟩ :=
    installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p h
  obtain ⟨rows, offset, next, _, hne, hgroup, hmerkle⟩ :=
    installed_acceptance_group_authentication_finalsplit e decode hash wp pin chain c p hnr hsamples h
      position root hpos r hrun
  exact ⟨r, rows, offset, next, hrun, hne, hgroup, hmerkle⟩

/-! ### The deployed route: `wp.rounds ≠ []`, the pinned roots opened in round one -/

/-- A round-one opened row block over the execution's own initial state: the
query indices and the raw rows returned by a `WhirIntermediate.openPrevious`
call on `fromPrefix r.retained.origin`, whose `rootsToOpen` is the three pinned
roots (`WhirIntermediate.rootsToOpen`, WhirIntermediate.lean 73-74), at the
round-one opening parameters `initialOpen wp`.

PRECISELY WHAT IS AND IS NOT PINNED HERE.  The opened STATE `r.retained.origin`,
the opening parameters and the hint bytes are the execution's; the starting
sponge cursor `start` is NOT -- it is a free existential.  So this predicate is
a SUPERSET of the run's own round-one opening: the run's opening is a member
(`tail_success_has_round_one_opening`, and in the tied form
`tail_success_has_tied_round_one_opening`), but other members exist, obtained by
starting the index sampling from a different cursor.  That costs the theorems
below nothing, because they take this predicate as a HYPOTHESIS: EVERY member is
Merkle-verified against the same three pinned roots at the same
`(initialOpen wp).merkleDepth` over the same hint bytes, which is all
`installed_acceptance_group_authentication_round_one` and its consumers use.
`RoundOneOpeningTied` below is the tied version, which does pin the cursor to
the execution, and `round_one_opening_tied_is_a_round_one_opening` shows it is
the stronger predicate. -/
def RoundOneOpening (hash : Hash) (wp : VkParams) (hints : Spongefish.Bytes)
    (r : WhirTail.Result) (opening : WhirIntermediate.Opening) : Prop :=
  ∃ start last : Spongefish.State,
    WhirIntermediate.openPrevious hash hints (WhirConfigured.initialOpen wp)
      (WhirIntermediate.fromPrefix r.retained.origin) start = some (opening, last)

/-- The TIED round-one opening: the same block, but with the starting sponge
cursor pinned to the actual execution.  Round one's `openPrevious` is called on
`afterPow` -- the cursor left by that round's own `WhirIntermediate.receive` on
`spongeState (fromPrefix r.retained.origin)` under the FIRST round's parameters
(`WhirIntermediate.round_success_is_one_execution`).  Nothing here is free
except the message and the two cursors, each of which is determined by the
execution. -/
def RoundOneOpeningTied (hash : Hash) (wp : VkParams) (source hints : Spongefish.Bytes)
    (r : WhirTail.Result) (opening : WhirIntermediate.Opening) : Prop :=
  ∃ (first : WhirParameters.Round) (rest : List WhirParameters.Round)
    (message : WhirIntermediate.Message) (afterPow last : Spongefish.State),
    wp.rounds = first :: rest ∧
    WhirIntermediate.receive hash source (WhirConfigured.roundParams first)
      (WhirIntermediate.spongeState (WhirIntermediate.fromPrefix r.retained.origin)) =
        some (message, afterPow) ∧
    WhirIntermediate.openPrevious hash hints (WhirConfigured.initialOpen wp)
      (WhirIntermediate.fromPrefix r.retained.origin) afterPow = some (opening, last)

/-- The tied predicate is the stronger one: forgetting the transcript cursor
gives back `RoundOneOpening`.  Every theorem below that takes `RoundOneOpening`
as a hypothesis therefore applies to the run's own tied opening. -/
theorem round_one_opening_tied_is_a_round_one_opening (hash : Hash) (wp : VkParams)
    (source hints : Spongefish.Bytes) (r : WhirTail.Result)
    (opening : WhirIntermediate.Opening)
    (h : RoundOneOpeningTied hash wp source hints r opening) :
    RoundOneOpening hash wp hints r opening := by
  obtain ⟨_, _, _, afterPow, last, _, _, ho⟩ := h
  exact ⟨afterPow, last, ho⟩

/-- With at least one intermediate round -- the DEPLOYED v2 profile -- every
successful concrete tail performs a round-one opening block, and that block is
TIED to the execution: its starting sponge cursor is the `afterPow` the round's
own `WhirIntermediate.receive` produced on this proof's transcript bytes.
Peeled from `WhirConfigured.configured_success_initial_and_intermediate_provenance`
through `WhirIntermediate.sequence_success_threads_actual_next` and
`round_success_is_one_execution`. -/
theorem tail_success_has_tied_round_one_opening (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes) (hrounds : wp.rounds ≠ [])
    (r : WhirTail.Result) (hrun : tailRun hash wp ctx transcript hints = some r) :
    ∃ opening,
      RoundOneOpeningTied hash wp (outerBytes transcript) (outerBytes hints) r opening := by
  obtain ⟨first, rest, hcase⟩ : ∃ a l, wp.rounds = a :: l := by
    cases hc : wp.rounds with
    | nil => exact absurd hc hrounds
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨_, _, _, hinter, _⟩ :=
    WhirConfigured.configured_success_initial_and_intermediate_provenance hash _ _ _ _ _ _ _ _ _ r hrun
  have hsplit : WhirConfigured.phasePairs (WhirConfigured.initialOpen (contextParams wp ctx))
      (contextParams wp ctx).rounds =
      (WhirConfigured.initialOpen wp, WhirConfigured.roundParams first) ::
        WhirConfigured.phasePairs (WhirConfigured.roundOpen first) rest := by
    show WhirConfigured.phasePairs (WhirConfigured.initialOpen wp) wp.rounds = _
    simp only [hcase, WhirConfigured.phasePairs]
  rw [hsplit] at hinter
  obtain ⟨next, hround, _⟩ :=
    WhirIntermediate.sequence_success_threads_actual_next hash _ _ _ _ _ _ _ hinter
  obtain ⟨message, afterPow, opening, afterMerkle, _, _, hrecv, hopen, _, _⟩ :=
    WhirIntermediate.round_success_is_one_execution hash _ _ _ _ _ _ hround
  exact ⟨opening, first, rest, message, afterPow, afterMerkle, hcase, hrecv, hopen⟩

/-- The same in the weaker, cursor-free form the theorems below take as a
hypothesis: the run's own opening is a member of `RoundOneOpening`. -/
theorem tail_success_has_round_one_opening (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes) (hrounds : wp.rounds ≠ [])
    (r : WhirTail.Result) (hrun : tailRun hash wp ctx transcript hints = some r) :
    ∃ opening, RoundOneOpening hash wp (outerBytes hints) r opening := by
  obtain ⟨opening, htied⟩ :=
    tail_success_has_tied_round_one_opening hash wp ctx transcript hints hrounds r hrun
  exact ⟨opening, round_one_opening_tied_is_a_round_one_opening hash wp _ _ r opening htied⟩

/-- The round-one query-index list is NONEMPTY as soon as the parameter record
asks for a positive number of in-domain samples.  `WhirParameters.checkBound`
does not force this, so it is an explicit hypothesis; the adopted lemma that
supplies the conclusion is
`WhirSampling.reference_nonempty_request_has_nonempty_output`. -/
theorem round_one_indices_are_nonempty (hash : Hash) (wp : VkParams) (hints : Spongefish.Bytes)
    (r : WhirTail.Result) (opening : WhirIntermediate.Opening)
    (hsamples : 0 < wp.inDomainSamples)
    (hopen : RoundOneOpening hash wp hints r opening) : opening.indices ≠ [] := by
  obtain ⟨start, last, ho⟩ := hopen
  obtain ⟨afterSampling, hs, _⟩ := WhirIntermediate.opening_success_uses_previous_roots hash hints
    (WhirConfigured.initialOpen wp) (WhirIntermediate.fromPrefix r.retained.origin) start last
    opening ho
  exact WhirSampling.reference_nonempty_request_has_nonempty_output hash start afterSampling _ _ _
    hsamples.ne' hs

/-- **THE DEPLOYED ROUTE, PER COMMITMENT POSITION.**  For an accepted
verification and its round-one opening block, the raw rows the execution
returned at EVERY commitment position of the outer verifier's pinned root list
are Merkle-authenticated against THAT root, at `(initialOpen wp).merkleDepth`
(the round-one depth, NOT `finalParams`' depth) and the executed query indices,
over the proof's own hint bytes.  Composed from
`WhirIntermediate.opening_each_root_uses_actual_raw_hashes` -- which is the
`WhirRows.openGroups` interface `OpeningBinding` sections 1-3 already expect. -/
theorem installed_acceptance_group_authentication_round_one (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (position : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root)
    (r : WhirTail.Result)
    (hrun : tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints =
      some r)
    (opening : WhirIntermediate.Opening)
    (hopen : RoundOneOpening hash wp (outerBytes p.whirHints) r opening) :
    ∃ (rows : List WhirRows.RawRow) (offset next : Nat),
      opening.groups.get? position = some rows ∧
      Merkle.verify hash (rootDigest root) (WhirConfigured.initialOpen wp).merkleDepth
        opening.indices (WhirRows.rowHashes hash rows) (outerBytes p.whirHints) offset = some next := by
  obtain ⟨r₀, hrun₀, _, _, hcommit, _, _⟩ :=
    installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p h
  have hr : r = r₀ := (Option.some.inj (hrun₀.symm.trans hrun)).symm
  subst hr
  obtain ⟨start, last, ho⟩ := hopen
  have hroots : WhirIntermediate.rootsToOpen (WhirIntermediate.fromPrefix r.retained.origin) =
      [rootDigest pin.preprocessedRoot, rootDigest p.witnessRoot, rootDigest p.normInverseRoot] := by
    rw [show WhirIntermediate.rootsToOpen (WhirIntermediate.fromPrefix r.retained.origin) =
      r.retained.origin.initial.commitments.map (·.root) from by
        simp [WhirIntermediate.rootsToOpen, WhirIntermediate.fromPrefix]]
    exact hcommit
  have hget : (WhirIntermediate.rootsToOpen (WhirIntermediate.fromPrefix r.retained.origin)).get?
      position = some (rootDigest root) := by
    rw [hroots]
    match position, hpos with
    | 0, hpos => simpa using congrArg (Option.map rootDigest) hpos
    | 1, hpos => simpa using congrArg (Option.map rootDigest) hpos
    | 2, hpos => simpa using congrArg (Option.map rootDigest) hpos
  obtain ⟨rows, before, after, hgroup, _, hmerkle⟩ :=
    WhirIntermediate.opening_each_root_uses_actual_raw_hashes hash (outerBytes p.whirHints)
      (WhirConfigured.initialOpen wp) (WhirIntermediate.fromPrefix r.retained.origin) start last
      opening position (rootDigest root) ho hget
  exact ⟨rows, _, after.hintPos, hgroup, hmerkle⟩

/-- The deployed-route statement with the concrete execution AND its round-one
opening block existentially exhibited from outer acceptance alone, and with the
query-index list proved nonempty. -/
theorem installed_acceptance_opens_authenticated_rows_round_one (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (hrounds : wp.rounds ≠ [])
    (hsamples : 0 < wp.inDomainSamples)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (position : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root) :
    ∃ (r : WhirTail.Result) (opening : WhirIntermediate.Opening) (rows : List WhirRows.RawRow)
      (offset next : Nat),
      tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints = some r ∧
      RoundOneOpening hash wp (outerBytes p.whirHints) r opening ∧
      opening.indices ≠ [] ∧
      opening.groups.get? position = some rows ∧
      Merkle.verify hash (rootDigest root) (WhirConfigured.initialOpen wp).merkleDepth
        opening.indices (WhirRows.rowHashes hash rows) (outerBytes p.whirHints) offset = some next := by
  obtain ⟨r, hrun, _, _, _, _, _⟩ :=
    installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p h
  obtain ⟨opening, hopen⟩ := tail_success_has_round_one_opening hash wp _ _ _ hrounds r hrun
  obtain ⟨rows, offset, next, hgroup, hmerkle⟩ :=
    installed_acceptance_group_authentication_round_one e decode hash wp pin chain c p h position
      root hpos r hrun opening hopen
  exact ⟨r, opening, rows, offset, next, hrun,
    hopen, round_one_indices_are_nonempty hash wp _ r opening hsamples hopen, hgroup, hmerkle⟩

/-! ## Attaching the installed engine to the adopted opening-binding results -/

/-- **THE EXECUTED GROUPS ARE NOT FREE (finalsplit route).**  `OpeningBinding`'s
grouped binding results are stated about an arbitrary accepted
`WhirRows.openGroups` block; for the abstract engine nothing supplies one, which
is exactly residue R1.  For the installed engine the block is DISCHARGED from
outer acceptance: the Merkle executions the adopted binding argument needs are
the ones the installed tail itself performed on this proof's hint bytes.  Two
accepted verifications sharing one commitment position's root therefore return
the same raw row at a common query index, or exhibit a concrete
`WhirRowBinding.RowCollision` -- no injectivity assumption and no probability.
Composed from the adopted
`MerkleExtraction.accepted_raw_rows_bind_or_hash_collision`. -/
theorem installed_accepted_rows_bind_or_collision_finalsplit (hash : Hash) (wp : VkParams)
    (hnr : wp.numRounds = 0)
    (hsamples : 0 < (WhirConfigured.finalParams wp).openParams.inDomainSamples)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (e' : Verifier.Engine) (decode' : Integrated.DecodeGates) (pin' : Verifier.Pinned) (chain' : Nat)
    (c' : Verifier.Config) (p' : Verifier.Proof)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (h' : Integrated.verify (installedEngine e' decode' hash wp) decode' pin' chain' c' p' = .ok ())
    (position index : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root)
    (hpos' : [pin'.preprocessedRoot, p'.witnessRoot, p'.normInverseRoot].get? position = some root)
    (r r' : WhirTail.Result) (rows rows' : List WhirRows.RawRow) (row row' : WhirRows.RawRow)
    (hrun : tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints =
      some r)
    (hrun' : tailRun hash wp (installedContext e' decode' hash wp c' p') p'.whirTranscript
      p'.whirHints = some r')
    (hg : r.rows.opened.groups.get? position = some rows)
    (hg' : r'.rows.opened.groups.get? position = some rows')
    (hm : (index, row) ∈ r.rows.indices.zip rows)
    (hm' : (index, row') ∈ r'.rows.indices.zip rows') :
    row.bytes = row'.bytes ∨ WhirRowBinding.RowCollision hash row.bytes row'.bytes := by
  obtain ⟨actual, offset, next, _, _, hga, hmerkle⟩ :=
    installed_acceptance_group_authentication_finalsplit e decode hash wp pin chain c p hnr hsamples h
      position root hpos r hrun
  obtain ⟨actual', offset', next', _, _, hga', hmerkle'⟩ :=
    installed_acceptance_group_authentication_finalsplit e' decode' hash wp pin' chain' c' p' hnr
      hsamples h' position root hpos' r' hrun'
  have ha : rows = actual := Option.some.inj (hg.symm.trans hga)
  have ha' : rows' = actual' := Option.some.inj (hg'.symm.trans hga')
  subst ha
  subst ha'
  rcases MerkleExtraction.accepted_raw_rows_bind_or_hash_collision hash (rootDigest root)
    (WhirConfigured.finalParams wp).openParams.merkleDepth index r.rows.indices r'.rows.indices
    (WhirRows.rowHashes hash rows) (WhirRows.rowHashes hash rows') (outerBytes p.whirHints)
    (outerBytes p'.whirHints) row.bytes row'.bytes offset next offset' next' hmerkle hmerkle'
    (WhirRowBinding.raw_row_membership_gives_actual_hash_membership hash r.rows.indices rows index row hm)
    (WhirRowBinding.raw_row_membership_gives_actual_hash_membership hash r'.rows.indices rows' index row' hm')
    with heq | hleaf | hcomp
  · exact Or.inl heq
  · exact Or.inr (Or.inl hleaf)
  · exact Or.inr (Or.inr hcomp)

/-- **THE EXECUTED GROUPS ARE NOT FREE (deployed route).**  The same discharge
for `wp.rounds ≠ []`: the `WhirRows.openGroups` block that `OpeningBinding`
sections 1-3 quantify over is the one round one of the installed tail itself
performed on the three pinned roots, at `(initialOpen wp).merkleDepth`.  Two
accepted verifications sharing one commitment position's root return the same
raw row at a common query index, or exhibit a concrete
`WhirRowBinding.RowCollision`. -/
theorem installed_accepted_rows_bind_or_collision_round_one (hash : Hash) (wp : VkParams)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (e' : Verifier.Engine) (decode' : Integrated.DecodeGates) (pin' : Verifier.Pinned) (chain' : Nat)
    (c' : Verifier.Config) (p' : Verifier.Proof)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (h' : Integrated.verify (installedEngine e' decode' hash wp) decode' pin' chain' c' p' = .ok ())
    (position index : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root)
    (hpos' : [pin'.preprocessedRoot, p'.witnessRoot, p'.normInverseRoot].get? position = some root)
    (r r' : WhirTail.Result) (opening opening' : WhirIntermediate.Opening)
    (rows rows' : List WhirRows.RawRow) (row row' : WhirRows.RawRow)
    (hrun : tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints =
      some r)
    (hrun' : tailRun hash wp (installedContext e' decode' hash wp c' p') p'.whirTranscript
      p'.whirHints = some r')
    (hopen : RoundOneOpening hash wp (outerBytes p.whirHints) r opening)
    (hopen' : RoundOneOpening hash wp (outerBytes p'.whirHints) r' opening')
    (hg : opening.groups.get? position = some rows)
    (hg' : opening'.groups.get? position = some rows')
    (hm : (index, row) ∈ opening.indices.zip rows)
    (hm' : (index, row') ∈ opening'.indices.zip rows') :
    row.bytes = row'.bytes ∨ WhirRowBinding.RowCollision hash row.bytes row'.bytes := by
  obtain ⟨actual, offset, next, hga, hmerkle⟩ :=
    installed_acceptance_group_authentication_round_one e decode hash wp pin chain c p h position
      root hpos r hrun opening hopen
  obtain ⟨actual', offset', next', hga', hmerkle'⟩ :=
    installed_acceptance_group_authentication_round_one e' decode' hash wp pin' chain' c' p' h'
      position root hpos' r' hrun' opening' hopen'
  have ha : rows = actual := Option.some.inj (hg.symm.trans hga)
  have ha' : rows' = actual' := Option.some.inj (hg'.symm.trans hga')
  subst ha
  subst ha'
  rcases MerkleExtraction.accepted_raw_rows_bind_or_hash_collision hash (rootDigest root)
    (WhirConfigured.initialOpen wp).merkleDepth index opening.indices opening'.indices
    (WhirRows.rowHashes hash rows) (WhirRows.rowHashes hash rows') (outerBytes p.whirHints)
    (outerBytes p'.whirHints) row.bytes row'.bytes offset next offset' next' hmerkle hmerkle'
    (WhirRowBinding.raw_row_membership_gives_actual_hash_membership hash opening.indices rows index row hm)
    (WhirRowBinding.raw_row_membership_gives_actual_hash_membership hash opening'.indices rows' index row' hm')
    with heq | hleaf | hcomp
  · exact Or.inl heq
  · exact Or.inr (Or.inl hleaf)
  · exact Or.inr (Or.inr hcomp)

/-! ## The installed engine is not blind -/

theorem installed_engine_rejects_failed_tail (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (ctx : Verifier.WhirContext)
    (p : Verifier.Proof) (h : tailRun hash wp ctx p.whirTranscript p.whirHints = none) :
    Verifier.verifyWhir (installedEngine e decode hash wp) ctx p = false := by
  unfold Verifier.verifyWhir
  cases (installedEngine e decode hash wp).parseWhir ctx p.whirTranscript p.whirHints with
  | none => rfl
  | some parsed => simp [installedEngine, installedTail, h]

theorem installed_verify_rejects_failed_tail (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints = none) :
    Integrated.verify (installedEngine e decode hash wp) decode pin chain c p ≠ .ok () := by
  intro hok
  obtain ⟨r, hrun, _, _, _, _, _⟩ :=
    installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p hok
  rw [h] at hrun
  exact Option.noConfusion hrun

/-- Hints and transcript that do not carry a commitment for each pinned root
cannot be repaired by the installed tail: the checked parameter projection never
reaches any phase. -/
theorem installed_tail_rejects_root_count_mismatch (hash : Hash) (wp : VkParams)
    (ctx : Verifier.WhirContext) (transcript hints : Verifier.Bytes)
    (h : ctx.roots.length ≠ wp.numCommitments) :
    tailRun hash wp ctx transcript hints = none := by
  refine WhirConfigured.invalid_parameters_do_not_reach_any_phase _ _ _ _ _ _ _ _ _ _ ?_
  simp only [List.length_map, WhirParameters.checkBound]
  have hne : ¬ (ctx.roots.length = (contextParams wp ctx).numCommitments) := h
  split
  · split
    · simp [hne]
    · rfl
  · rfl

def emptyRootContext : Verifier.WhirContext := ⟨[], [], [], 0, [], [], []⟩

/-- **THE BLIND-ENGINE COUNTEREXAMPLE NO LONGER APPLIES TO THIS ENGINE, in the
weakest possible way.**  `OpeningBinding.blind_engine_accepts_every_context`
exhibits an engine whose WHIR check accepts EVERY context and EVERY proof; that
is residue R1.  Here the installed engine rejects a context carrying no
commitment at all -- but that rejection happens at parameter ADMISSION
(`checkBound` fails on the root count), so it exercises nothing of the tail.
The honest version of this claim is `installed_engine_is_not_blind` at the end
of this file, which rejects on a context whose parameters ARE admissible. -/
theorem installed_engine_is_not_blind_degenerate (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (hc : 0 < wp.numCommitments) :
    (∃ ctx p, Verifier.verifyWhir (installedEngine e decode hash wp) ctx p = false) ∧
    (∀ ctx p, Verifier.verifyWhir (OpeningBinding.blindEngine e) ctx p = true) := by
  refine ⟨⟨emptyRootContext, Verifier.testProof, ?_⟩, OpeningBinding.blind_engine_accepts_every_context e⟩
  exact installed_engine_rejects_failed_tail e decode hash wp emptyRootContext Verifier.testProof
    (installed_tail_rejects_root_count_mismatch hash wp emptyRootContext _ _ (by simpa using hc.ne))

/-! ## One execution carries both halves; and what is still free (R1b) -/

/-- **SECTIONS 1-3 AND SECTION 4 OF `OpeningBinding` NOW NAME ONE EXECUTION
(finalsplit route).**  For the abstract engine the opened rows and the bound
expected claims live in disjoint halves of the model.  For the installed engine
a single accepted concrete execution both read the five bound expected claims of
the outer verifier AND authenticated the raw rows it returned under each pinned
root. -/
theorem installed_acceptance_joins_claims_and_openings_finalsplit (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (hnr : wp.numRounds = 0)
    (hsamples : 0 < (WhirConfigured.finalParams wp).openParams.inDomainSamples)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (position : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root) :
    ∃ (r : WhirTail.Result) (rows : List WhirRows.RawRow) (offset next : Nat),
      tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints = some r ∧
      (∀ i : Fin 5, r.retained.origin.initial.evaluations.getD i.val Verifier.zero =
        Connections.packedFold (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).1
          (Verifier.width c) (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2) ∧
      r.rows.indices ≠ [] ∧
      r.rows.opened.groups.get? position = some rows ∧
      Merkle.verify hash (rootDigest root) (WhirConfigured.finalParams wp).openParams.merkleDepth
        r.rows.indices (WhirRows.rowHashes hash rows) (outerBytes p.whirHints) offset = some next := by
  obtain ⟨r, hrun, _, _, _, _, hclaims⟩ :=
    installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p h
  obtain ⟨rows, offset, next, _, hne, hgroup, hmerkle⟩ :=
    installed_acceptance_group_authentication_finalsplit e decode hash wp pin chain c p hnr hsamples h
      position root hpos r hrun
  exact ⟨r, rows, offset, next, hrun, hclaims, hne, hgroup, hmerkle⟩

/-- **SECTIONS 1-3 AND SECTION 4 OF `OpeningBinding` NOW NAME ONE EXECUTION
(deployed route).**  The same join for `wp.rounds ≠ []`: ONE accepted concrete
execution both read the five bound expected claims of the outer verifier AND, in
round one, authenticated the raw rows it returned under each pinned root at
`(initialOpen wp).merkleDepth`, over a nonempty query-index list. -/
theorem installed_acceptance_joins_claims_and_openings_round_one (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (wp : VkParams) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (hrounds : wp.rounds ≠ [])
    (hsamples : 0 < wp.inDomainSamples)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (position : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root) :
    ∃ (r : WhirTail.Result) (opening : WhirIntermediate.Opening) (rows : List WhirRows.RawRow)
      (offset next : Nat),
      tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints = some r ∧
      (∀ i : Fin 5, r.retained.origin.initial.evaluations.getD i.val Verifier.zero =
        Connections.packedFold (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).1
          (Verifier.width c) (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2) ∧
      RoundOneOpening hash wp (outerBytes p.whirHints) r opening ∧
      opening.indices ≠ [] ∧
      opening.groups.get? position = some rows ∧
      Merkle.verify hash (rootDigest root) (WhirConfigured.initialOpen wp).merkleDepth
        opening.indices (WhirRows.rowHashes hash rows) (outerBytes p.whirHints) offset = some next := by
  obtain ⟨r, hrun, _, _, _, _, hclaims⟩ :=
    installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p h
  obtain ⟨opening, hopen⟩ := tail_success_has_round_one_opening hash wp _ _ _ hrounds r hrun
  obtain ⟨rows, offset, next, hgroup, hmerkle⟩ :=
    installed_acceptance_group_authentication_round_one e decode hash wp pin chain c p h position
      root hpos r hrun opening hopen
  exact ⟨r, opening, rows, offset, next, hrun, hclaims, hopen,
    round_one_indices_are_nonempty hash wp _ r opening hsamples hopen, hgroup, hmerkle⟩

/-- **RESIDUE R1b, AS A VISIBLE HYPOTHESIS ABOUT THE EXECUTION RESULT.**
Installing the concrete tail does NOT by itself produce, from an accepted
execution, a committed column family whose row folds are the proof's opened
cells.  The adopted deterministic chain stops in two places that do not meet:

* `WhirTail.accepted_tail_every_sample_compared_with_same_vector` relates the
  Merkle-authenticated rows to the final vector at the QUERIED domain points;
* `WhirTail.accepted_tail_same_vector_nonzero_and_exact_claim` relates the final
  vector, through the sumcheck sum, to `WhirFinal.expectedLinearForm` of the
  initial linear forms -- i.e. to the CLAIMED evaluations at `ctx.points`.

The adopted audit contains NO theorem of the form "`WhirFinal.finalClaim = true`
implies the claimed value is the multilinear evaluation of the authenticated
rows at the evaluation point".  Supplying it is WHIR proximity / list decoding
plus sumcheck soundness: probabilistic, and absent from the adopted tree.  So
this predicate is ASSUMED, never proved here.

It is stated as PCS extraction actually is, and NOT as a bare
`∃ cols, HonestOpenings …`: the extracted column family is the value of ONE
fixed function `extract` of the COMMITMENT ROOTS AND the authenticated
round-one row block -- the three pinned roots the execution absorbed, and the
query indices and raw rows it returned under them.  That is what makes the
predicate bite: a bare `∃ cols, HonestOpenings c p s idx cols` mentions no hash,
no `wp`, no `tailRun`, no root and no row, and is inhabited for every hash and
every `wp`, so assuming it would say nothing about WHIR.  Here the column family
may not depend on `p.used`, on the engine, or on the configuration except
through the roots and the rows, which is exactly the content of
`tail_extraction_binds_opened_cells_to_the_opened_rows` below.

THE ROOTS ARE AN ARGUMENT OF `extract` ON PURPOSE.  An earlier revision let
`extract` see the opening only.  A commitment is a root plus an opening, and an
honest PCS extractor reads both; dropping the root made the predicate force
equal bound cells across two runs with DIFFERENT commitments that merely happen
to share a round-one opening -- and for any FIXED hash such honest pairs exist
by counting, with no collision anywhere, so the predicate was false on honest
runs.  `installed_acceptance_runs_the_concrete_tail` pins the argument supplied
here, `r.retained.origin.initial.commitments.map (·.root)`, to
`[rootDigest pin.preprocessedRoot, rootDigest p.witnessRoot,
rootDigest p.normInverseRoot]`.

NOTE ON RESIDUE R3.  `OpeningBinding.OpensCommittedTable` is
`IntegratedTerminalChain.HonestOpenings`, whose `opened` field is PER COLUMN, so
this predicate assumes column identification -- residue R3 -- along with R1b.
`TailExtractsFoldLevel` below is the strictly R3-free shape, at the level the
WHIR claim actually binds. -/
def TailExtractsCommittedTables (hash : Hash) (wp : VkParams) : Prop :=
  ∃ extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List GoldilocksExt3Field.Element),
    ∀ (e : Verifier.Engine) (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
      (c : Verifier.Config) (p : Verifier.Proof) (r : WhirTail.Result)
      (opening : WhirIntermediate.Opening),
      Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok () →
      tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints = some r →
      RoundOneOpening hash wp (outerBytes p.whirHints) r opening →
      OpeningBinding.OpensCommittedTable c p (Verifier.derivedRounds e c p)
        (Verifier.derivedIndices e c p)
        (extract (r.retained.origin.initial.commitments.map (·.root)) opening)

/-- **THE R1b PREDICATE IS NOT TRIVIALLY INHABITED: it constrains the opened
cells to the pinned roots and the authenticated rows.**  This is the HONEST
binding statement: two accepted verifications that pinned the SAME three roots,
authenticated the SAME round-one row block under them -- same query indices,
same raw rows -- and whose cell row points agree must have the SAME opened claim
cells, for arbitrary engines, configurations, pinned data and proofs.  Nothing
deterministic in the adopted tree gives this, and it fails outright for the bare
`∃ cols, HonestOpenings …` form, in which `cols` may be chosen per proof.

WITHOUT the three root hypotheses NOTHING IS CLAIMED HERE.  Two accepted runs
that share a round-one opening but pin different commitments are not asserted to
have equal cells -- they must not be, since for a fixed hash such honest pairs
exist by counting with no collision anywhere.  What R1b does give in that case
is only the per-run statement of
`tail_extraction_ties_tables_to_the_pinned_roots`: each run's cells are the row
folds of ITS OWN extracted family, and the two families coincide exactly when
the pinned root lists do. -/
theorem tail_extraction_binds_opened_cells_to_the_opened_rows (hash : Hash) (wp : VkParams)
    (hyp : TailExtractsCommittedTables hash wp)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (e' : Verifier.Engine) (decode' : Integrated.DecodeGates) (pin' : Verifier.Pinned) (chain' : Nat)
    (c' : Verifier.Config) (p' : Verifier.Proof)
    (r r' : WhirTail.Result) (opening : WhirIntermediate.Opening)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (h' : Integrated.verify (installedEngine e' decode' hash wp) decode' pin' chain' c' p' = .ok ())
    (hrun : tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints =
      some r)
    (hrun' : tailRun hash wp (installedContext e' decode' hash wp c' p') p'.whirTranscript
      p'.whirHints = some r')
    (hopen : RoundOneOpening hash wp (outerBytes p.whirHints) r opening)
    (hopen' : RoundOneOpening hash wp (outerBytes p'.whirHints) r' opening)
    (hpre : pin.preprocessedRoot = pin'.preprocessedRoot)
    (hwit : p.witnessRoot = p'.witnessRoot)
    (hnorm : p.normInverseRoot = p'.normInverseRoot)
    (hrow : ∀ i : Fin 5, OpenedClaimFold.cellRow (Verifier.derivedRounds e c p) i =
      OpenedClaimFold.cellRow (Verifier.derivedRounds e' c' p') i) :
    ∀ i : Fin 5,
      (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).1.map Subtype.val =
        (OpenedClaimFold.boundCell p'.used (Verifier.derivedIndices e' c' p') i).1.map Subtype.val := by
  obtain ⟨extract, hex⟩ := hyp
  have hroots : r.retained.origin.initial.commitments.map (·.root) =
      r'.retained.origin.initial.commitments.map (·.root) := by
    obtain ⟨r₀, hrun₀, _, _, hcommit, _, _⟩ :=
      installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p h
    obtain ⟨r₁, hrun₁, _, _, hcommit', _, _⟩ :=
      installed_acceptance_runs_the_concrete_tail e' decode' hash wp pin' chain' c' p' h'
    have hr : r = r₀ := (Option.some.inj (hrun₀.symm.trans hrun)).symm
    have hr' : r' = r₁ := (Option.some.inj (hrun₁.symm.trans hrun')).symm
    rw [hr, hr', hcommit, hcommit', hpre, hwit, hnorm]
  intro i
  rw [(hex e decode pin chain c p r opening h hrun hopen).opened i,
    (hex e' decode' pin' chain' c' p' r' opening h' hrun' hopen').opened i, hrow i, hroots]

/-- **WHAT R1b GIVES WITHOUT ROOT AGREEMENT.**  Each accepted run gets its own
extracted column family, and the two families are the SAME as soon as the two
runs pinned the same three commitment roots -- which is the only case
`tail_extraction_binds_opened_cells_to_the_opened_rows` speaks about.  Stated
this way, the extractor's dependence on the roots is visible in the conclusion
rather than hidden in the hypotheses. -/
theorem tail_extraction_ties_tables_to_the_pinned_roots (hash : Hash) (wp : VkParams)
    (hyp : TailExtractsCommittedTables hash wp)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (e' : Verifier.Engine) (decode' : Integrated.DecodeGates) (pin' : Verifier.Pinned) (chain' : Nat)
    (c' : Verifier.Config) (p' : Verifier.Proof)
    (r r' : WhirTail.Result) (opening : WhirIntermediate.Opening)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ())
    (h' : Integrated.verify (installedEngine e' decode' hash wp) decode' pin' chain' c' p' = .ok ())
    (hrun : tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints =
      some r)
    (hrun' : tailRun hash wp (installedContext e' decode' hash wp c' p') p'.whirTranscript
      p'.whirHints = some r')
    (hopen : RoundOneOpening hash wp (outerBytes p.whirHints) r opening)
    (hopen' : RoundOneOpening hash wp (outerBytes p'.whirHints) r' opening) :
    ∃ cols cols' : Fin 5 → List (List GoldilocksExt3Field.Element),
      OpeningBinding.OpensCommittedTable c p (Verifier.derivedRounds e c p)
        (Verifier.derivedIndices e c p) cols ∧
      OpeningBinding.OpensCommittedTable c' p' (Verifier.derivedRounds e' c' p')
        (Verifier.derivedIndices e' c' p') cols' ∧
      (r.retained.origin.initial.commitments.map (·.root) =
        r'.retained.origin.initial.commitments.map (·.root) → cols = cols') := by
  obtain ⟨extract, hex⟩ := hyp
  exact ⟨_, _, hex e decode pin chain c p r opening h hrun hopen,
    hex e' decode' pin' chain' c' p' r' opening h' hrun' hopen', fun heq => by rw [heq]⟩

/-- Under R1b -- and only under it, and only on the DEPLOYED route
(`wp.rounds ≠ []`) where the round-one authenticated row block exists --
acceptance of the installed engine gives the fold half of `OpeningBinding`'s
ASSUMPTION 17: every bound cell of the WHIR context IS the dense evaluation of
the width-padded group table at the packed point, and the sixth cell stays
unopened.  This is the adopted
`OpeningBinding.opens_committed_table_gives_full_table_cells` composed with the
hypothesis; nothing new about WHIR is proved. -/
theorem installed_acceptance_binds_claims (hash : Hash) (wp : VkParams)
    (hyp : TailExtractsCommittedTables hash wp) (hrounds : wp.rounds ≠ []) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (h : Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok ()) :
    ∃ cols : Fin 5 → List (List GoldilocksExt3Field.Element),
      (∀ i : Fin 5, OpenedClaimFold.CellOpensFullTable
        (Verifier.whirContext Connections.packedFold c p (Verifier.derivedRounds e c p)
          (Verifier.derivedIndices e c p)) i.val (OpenedClaimFold.cellPoint i) (cols i)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds e c p) i))
        (OpenedClaimFold.lift
          (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2)) ∧
      (Verifier.expectedClaims Connections.packedFold c p
        (Verifier.derivedIndices e c p)).map Option.isSome = [true, true, true, true, true, false] := by
  obtain ⟨extract, hex⟩ := hyp
  obtain ⟨r, hrun, _, _, _, _, _⟩ :=
    installed_acceptance_runs_the_concrete_tail e decode hash wp pin chain c p h
  obtain ⟨opening, hopen⟩ := tail_success_has_round_one_opening hash wp _ _ _ hrounds r hrun
  have hcols := hex e decode pin chain c p r opening h hrun hopen
  exact ⟨extract (r.retained.origin.initial.commitments.map (·.root)) opening,
    fun i => OpeningBinding.opens_committed_table_gives_full_table_cells c p _ _ _ hcols i,
    Verifier.context_bound_mask_exact _ _ _ _⟩

/-! ## The R3-free, fold-level shape of the same assumption -/

/-- **THE SAME ASSUMPTION AT THE LEVEL THE WHIR CLAIM ACTUALLY BINDS.**
`TailExtractsCommittedTables` concludes `OpeningBinding.OpensCommittedTable`,
i.e. `IntegratedTerminalChain.HonestOpenings`, whose `opened` field is PER
COLUMN: it identifies which committed column each opened cell came from.  That
is residue R3 of `OpeningBinding`, assumed alongside R1b.  The WHIR claim binds
strictly less -- one field element per cell,
`Connections.packedFold cells (Verifier.width c) idx` -- so this variant asks
only for what that claim can carry: the extracted family evaluates, at the
cell's packed point, to the cell's fold, with no per-column decomposition
asserted.  `tail_extraction_committed_tables_gives_fold_level` proves R1b
implies it; the converse is NOT claimed here.  In the DEPLOYED protocol the
per-column identification comes from an OBSERVATION outside this model: the
index point is sampled after the cells are in the outer transcript
(`Verifier.derivedIndices`, Verifier.lean 389-390, takes `p.used` as an input to
`e.sampleIndices`). -/
def TailExtractsFoldLevel (hash : Hash) (wp : VkParams) : Prop :=
  ∃ extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List GoldilocksExt3Field.Element),
    ∀ (e : Verifier.Engine) (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
      (c : Verifier.Config) (p : Verifier.Proof) (r : WhirTail.Result)
      (opening : WhirIntermediate.Opening),
      Integrated.verify (installedEngine e decode hash wp) decode pin chain c p = .ok () →
      tailRun hash wp (installedContext e decode hash wp c p) p.whirTranscript p.whirHints = some r →
      RoundOneOpening hash wp (outerBytes p.whirHints) r opening →
      ∀ i : Fin 5, OpenedClaimFold.CellOpensFullTable
        (Verifier.whirContext Connections.packedFold c p (Verifier.derivedRounds e c p)
          (Verifier.derivedIndices e c p)) i.val (OpenedClaimFold.cellPoint i)
        (extract (r.retained.origin.initial.commitments.map (·.root)) opening i)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds e c p) i))
        (OpenedClaimFold.lift
          (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2)

/-- R1b implies its R3-free, fold-level weakening, with the SAME extractor: the
adopted `OpeningBinding.opens_committed_table_gives_full_table_cells` discards
the per-column identification and keeps the fold.  The converse is not claimed;
nothing here proves the two are inequivalent either. -/
theorem tail_extraction_committed_tables_gives_fold_level (hash : Hash) (wp : VkParams)
    (hyp : TailExtractsCommittedTables hash wp) : TailExtractsFoldLevel hash wp := by
  obtain ⟨extract, hex⟩ := hyp
  exact ⟨extract, fun e decode pin chain c p r opening h hrun hopen i =>
    OpeningBinding.opens_committed_table_gives_full_table_cells c p _ _ _
      (hex e decode pin chain c p r opening h hrun hopen) i⟩

/-! ## A concrete acceptance failure of the installed engine -/

def exampleHash : Hash := fun _ => Spongefish.zeroDigest

/-- The adopted zero-intermediate-round profile, retuned to the two packed
variables of `Integrated.exampleConfig` (`degreeBits + indexBits = 2`).  Its
evaluation points are overwritten by `contextParams` from the context anyway.
Being a `numRounds = 0` profile it is a TOY, not the deployed shape. -/
def exampleVk : VkParams :=
  { WhirConfigured.exampleNoRounds with
    numVariables := 2, initialNumVariables := 2,
    finalSumcheckRounds := 1, finalSize := 2,
    evaluationPoint := List.replicate 2 Arithmetic.zero,
    evaluationPoint2 := List.replicate 2 Arithmetic.zero }

theorem example_profile_is_the_split_route :
    WhirConfigured.CallerProfile exampleVk ∧ exampleVk.numRounds = 0 ∧
      (WhirParameters.checkBound exampleVk 3 6 1).isSome = true := by
  unfold WhirConfigured.CallerProfile
  decide

abbrev exampleInstalled : Verifier.Engine :=
  installedEngine Integrated.exampleEngine Integrated.exampleDecoder exampleHash exampleVk

set_option maxRecDepth 65536 in
/-- The parameter projection really is admissible on this context, so the
rejection below is a TRANSCRIPT/HINT failure of the concrete tail, not a
parameter-admission failure. -/
theorem example_context_parameters_are_admissible :
    (WhirParameters.checkBound
      (contextParams exampleVk
        (installedContext Integrated.exampleEngine Integrated.exampleDecoder exampleHash exampleVk
          Integrated.exampleConfig Integrated.exampleProof)) 3 6 1).isSome = true := by
  rfl

set_option maxRecDepth 65536 in
/-- Empty WHIR hint and transcript bytes cannot be authenticated: the concrete
tail returns `none`. -/
theorem example_empty_hints_fail_the_concrete_tail :
    tailRun exampleHash exampleVk
      (installedContext Integrated.exampleEngine Integrated.exampleDecoder exampleHash exampleVk
        Integrated.exampleConfig Integrated.exampleProof)
      Integrated.exampleProof.whirTranscript Integrated.exampleProof.whirHints = none := by
  rfl

set_option maxRecDepth 65536 in
/-- **THE INSTALLED ENGINE REJECTS A PROOF THE ABSTRACT MODEL ACCEPTED.**  The
adopted `Integrated.positive_integrated_norm_helper_path` accepts exactly this
configuration and proof with the observation-only WHIR tail.  With the concrete
tail installed, the same call is rejected. -/
theorem example_installed_engine_rejects_empty_whir_hints :
    Integrated.verify exampleInstalled Integrated.exampleDecoder
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Integrated.exampleConfig Integrated.exampleProof =
      .error .invalidProof := by
  rfl

theorem example_abstract_model_accepted_the_same_call :
    Integrated.verify Integrated.exampleEngine Integrated.exampleDecoder
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Integrated.exampleConfig Integrated.exampleProof =
      .ok () :=
  Integrated.positive_integrated_norm_helper_path

/-- **THE BLIND-ENGINE COUNTEREXAMPLE NO LONGER APPLIES TO THIS ENGINE.**
`OpeningBinding.blind_engine_accepts_every_context` exhibits an engine whose
WHIR check accepts EVERY context and EVERY proof; that is residue R1.  The
installed engine rejects concretely, and on a context whose WHIR parameters PASS
admission (`example_context_parameters_are_admissible`, restated as the second
conjunct), so the rejection happens INSIDE the tail on this proof's own
transcript and hint bytes -- not at the parameter gate, as in
`installed_engine_is_not_blind_degenerate`.  Every adopted result about the
abstract engine is unchanged: this is a NEW engine, not a repair of the old
ones. -/
theorem installed_engine_is_not_blind :
    Verifier.verifyWhir exampleInstalled
        (installedContext Integrated.exampleEngine Integrated.exampleDecoder exampleHash exampleVk
          Integrated.exampleConfig Integrated.exampleProof) Integrated.exampleProof = false ∧
    (WhirParameters.checkBound
      (contextParams exampleVk
        (installedContext Integrated.exampleEngine Integrated.exampleDecoder exampleHash exampleVk
          Integrated.exampleConfig Integrated.exampleProof)) 3 6 1).isSome = true ∧
    (∀ (e : Verifier.Engine) (ctx : Verifier.WhirContext) (p : Verifier.Proof),
      Verifier.verifyWhir (OpeningBinding.blindEngine e) ctx p = true) :=
  ⟨installed_engine_rejects_failed_tail Integrated.exampleEngine Integrated.exampleDecoder
      exampleHash exampleVk _ Integrated.exampleProof example_empty_hints_fail_the_concrete_tail,
    example_context_parameters_are_admissible,
    fun e => OpeningBinding.blind_engine_accepts_every_context e⟩

end Audit.Wire3.InstalledWhirTail
