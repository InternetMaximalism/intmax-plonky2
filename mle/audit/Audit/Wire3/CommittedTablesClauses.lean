import Audit.Wire3.CommitmentOrderSurvey
import Audit.Wire3.LocalizedCollisions
import Audit.Wire3.OpenedDotBinding
import Audit.Wire3.InstalledWhirTail

/-!
# Audit.Wire3.CommittedTablesClauses -- the three clauses of `CommittedTablesJoin`,
one at a time: which are theorems, which is the residue

## HONESTY HEADER

`CommitmentOrderSurvey.CommittedTablesJoin` is the adopted name for the open
`CommittedTables` residue.  It has three clauses, and the adopted tree records
them as one undifferentiated assumption, satisfiable so far only at the
CONSTANT extractor (`CommitmentOrderSurvey.committed_tables_join_is_satisfiable`).
This module separates them.  Clause by clause:

* `configDeployed` (`ExplicitEngine.core c = ExplicitEngine.core c₀`) -- **DERIVED**
  on the Solidity route, on every accepted call, UP TO A LOCALIZED COLLISION.
  `config_deployed_of_acceptance_or_collision` below is
  `LocalizedCollisions.accepted_configuration_is_the_deployment_localized`
  projected onto `core`.  The disjunct is
  `LocalizedCollisions.ConfigEncodingCollision khash c c₀` -- the two
  configuration ENCODINGS are distinct and `khash` agrees on them -- NOT the
  pigeonhole `ExplicitEngine.KhashCollision`, which
  `LocalizedCollisions.khash_collision_is_a_tautology` proves holds for every
  `khash` with no hypothesis at all.  That is the lesson of `LocalizedCollisions`
  and it is respected throughout: every disjunct below names its two inputs.
* `preprocessedPinned` (`p.preprocessedRoot = pin.preprocessedRoot`) -- **DERIVED**
  on every accepted call with NO collision disjunct whatsoever.  It is a conjunct
  of `Verifier.shape`, which `Verifier.verify_success_checks` returns.
  `preprocessed_pinned_of_shape` and `preprocessed_pinned_of_acceptance` below.
  What `Verifier.shape` does NOT pin is stated too: the witness root and the
  norm-inverse root are absent from it
  (`shape_ignores_the_witness_root`, `shape_ignores_the_norm_inverse_root`, both
  `rfl`), and its circuit-digest conjunct pins the PROOF to the CALLED
  configuration, not to the deployment -- that last step is `configDeployed`'s
  job, which is why the two clauses are not interchangeable.
* `rootDetermined` (`CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
  (extractedState … extract roots opening).tables`) -- **ASSUMED.  THIS IS R1b,
  AND NOTHING BELOW PROVES IT.**  Section 3 determines exactly how much of it the
  adopted binding lemmas reach.

## What section 3 finds, precisely

`InstalledWhirTail.TailExtractsCommittedTables` (R1b) posits an extractor from
(commitment roots, ROUND-ONE OPENING).  Having such an extractor does NOT make
the columns a function of the roots: the opening is adversary-chosen, and
`CommitmentOrderSurvey.extracted_state_moves_with_the_opening` already exhibits a
deterministic `extract` whose extracted state moves with it at FIXED roots.  This
module sharpens that into the statement the join actually needs:

* `root_determined_clause_has_no_tables_map_for_the_reading_extractor` -- for
  the adopted opening-reading `CommitmentOrderSurvey.demoExtract`, NO `tablesOf`
  satisfies `rootDetermined` at BOTH of `demoOpeningA` and `demoOpeningB`.  So the
  clause is not merely unproved: at that extractor it is FALSE as a uniform
  statement, and `CommitmentOrderSurvey`'s degenerate witness is not an artefact
  of taste.
* `root_determined_of_opening_free_extractor` -- and it becomes true exactly when
  the extractor is opening-free.  Root-determination IS opening-independence.

Opening-independence of the OPENED cells is the commitment BINDING property, and
the adopted tree has it, localized:

* `opened_cells_root_determined_or_collision` -- two accepted `WhirRows.openGroup`
  executions against the SAME root, depth and layout, sharing a query index,
  return the same row bytes or a `LocalizedCollisions.LeafCollision` on those two
  rows.  This is `OpenedDotBinding.opened_rows_bind_or_leaf_collision`, restated
  in the clause vocabulary; the Merkle-path side condition is
  `OpeningBinding.NoCollision` on the executed compression inputs, which
  `root_determination_hypotheses_hold_at_the_fixture` discharges at the adopted
  `WhirRows` fixture, and which `OpenedDotBinding.clash_no_collision_among_fails`
  shows can fail.
* `opened_dot_root_determined_or_collision` -- the same at dot-value level.

**AND THAT IS ALL IT GIVES.**  A group opening touches the QUERIED rows only; the
full committed column has `2 ^ m` cells and the sixth claim slot is never opened
at all (`unopened_cells_are_outside_every_binding_argument`).  Worse, the opening
relation itself is root-blind: `OpeningBinding.opening_relation_ignores_the_commitment`
survives replacing all three Merkle roots by arbitrary ones
(`opening_relation_is_root_blind`).  So root-determination of the FULL
columns is not binding at all -- it is WHIR proximity / list decoding, i.e. R1b
proper, and `full_columns_root_determined_follows_from_r1b` states exactly what
R1b buys and nothing more.

## What is NOT here

* **NO PROOF OF R1b**, and no part of one.  `TailExtractsCommittedTables` appears
  only as a hypothesis, exactly as in the adopted tree.
* **NO ROM MASSES.**  The two collision events this module localizes --
  `ConfigEncodingCollision` on the configuration encoding and `LeafCollision` on
  the two opened leaf rows -- are DETERMINISTIC predicates about two named byte
  strings.  Bounding their probability in the random-oracle model is a birthday
  term on frame inputs and belongs to `BirthdayClashBound`; NOTHING of the kind is
  proved, cited numerically, or implied below.
* **NO SOUNDNESS ERROR.**  Nothing here is the deployed system's security level.
  The wire-v3 WHIR profile this tree models is the approximately 100-bit design
  point.
* No Fiat--Shamir property, no hash assumption, no probability, no Rust/Yul/
  Solidity refinement.  `hash` and `khash` are arbitrary deterministic functions.

## Satisfiability of the hypotheses

Every composite hypothesis that this module introduces is exhibited:
`CanonicalProofCheck.DeployedFacts` and the two word bounds together at
`deployment_hypotheses_are_inhabited`; `RustCallBoundary.rustDeployment` at
`rust_deployment_hypothesis_is_inhabited`; the opening side conditions at
`root_determination_hypotheses_hold_at_the_fixture`.  That last one is OFF THE
DIAGONAL IN THE BUFFER ARGUMENT ONLY: `paddedFixtureHints` is
`WhirRows.exampleBaseHints` with one extra trailing byte, both openings stop at
`hintPos := 16` and return the same row, so the extra byte is never consumed and
the two executions are byte-identical over everything they read.  It is NOT a
genuinely different execution, and nothing below claims that it is.  The one
hypothesis NOT exhibited anywhere -- here or in the adopted tree -- is
`Integrated.verify … = .ok ()` itself, inherited verbatim from
`CanonicalProofCheck` and `LocalizedCollisions`, together with R1b; the adopted
`CommitmentOrderSurvey` header records the same gap ("No acceptance is
exhibited").  That is stated, not hidden.

## Adopted material used

`Audit.Wire3.CommitmentOrderSurvey` (`CommittedTablesJoin`, `demoExtract`,
`demoOpeningA`, `demoOpeningB`, `demo_extract_moves_with_the_opening`,
`fit_column_head`, `prefixTauTable`, `committed_tables_join_fixes_the_tau_table`,
`prefix_tau_table_depends_only_on_wires_and_constants`),
`Audit.Wire3.LocalizedCollisions` (`ConfigEncodingCollision`, `LeafCollision`,
`khash_collision_is_a_tautology`, `config_encoding_collision_fails_for_a_separating_khash`,
`config_encoding_collision_fails_on_equal_configurations`,
`separatingKhash`, `accepted_configuration_is_the_deployment_localized`,
`accepted_call_is_a_deployed_call_localized`,
`rust_checks_are_consequences_of_solidity_acceptance_up_to_localized`,
`no_collision_holds_on_the_empty_list`),
`Audit.Wire3.CanonicalProofCheck` (`DeployedFacts`, `pinnedProofEngine`,
`example_deployed_facts_inhabited`, `exampleDeployedConfig`, `examplePinned`,
`exampleSyntheticProfile`, `exampleDecodeGates`),
`Audit.Wire3.RustCallBoundary` (`RustDeployedFacts`, `rustDeployment`,
`rust_deployment_of_deployed_facts`, `exampleDecodeGates`, `exampleRustConfig`,
`example_rust_deployed_facts_inhabited`, `solidity_pins_are_not_implied_by_rust_checks`),
`Audit.Wire3.ExplicitEngine` (`core`, `Core.whirEncoding`, `encodeConfig`,
`explicitDeployment`, `residueVariant`, `KhashCollision`, `wordBound`),
`Audit.Wire3.OpenedDotBinding` (`executedMerkleInputs`, `executedMerkleInputs_success`,
`opened_rows_bind_or_leaf_collision`, `opened_dot_binds_or_leaf_collision`,
`clash_leaf_collision_holds`, `leaf_collision_fails_on_equal_rows`,
`example_row_membership`),
`Audit.Wire3.OpeningBinding` (`NoCollision`, `OpensCommittedTable`,
`opening_relation_ignores_the_commitment`, `mask_leaves_sixth_cell_unopened`,
`clashHash`, `clashRowA`, `clashRowB`, `clash_rows_differ`),
`Audit.Wire3.InstalledWhirTail` (`TailExtractsCommittedTables`, `VkParams`,
`installedEngine`, `installedContext`, `tailRun`, `RoundOneOpening`, `outerBytes`,
`tail_extraction_ties_tables_to_the_pinned_roots`),
`Audit.Wire3.ExtractorConstruction` (`extractedState`, `extractedColumns`,
`fitColumn`, `extracted_columns_evals_map`),
`Audit.Wire3.WhirRows` (`exampleHash`, `exampleBaseRoot`, `exampleBaseRow`,
`exampleBaseHints`, `exampleStart`, `openGroup`, `Layout`, `RawRow`,
`base_row_open_example`),
`Audit.Wire3.WhirRowBinding` (`decodedDot`),
`Audit.Wire3.OuterAdapter` (`fixtureConfig`),
`Audit.Wire3.Verifier` (`shape`, `verify_success_checks`, `statement`,
`expectedClaims`, `derivedRounds`, `derivedIndices`, `Config`, `Proof`, `Pinned`,
`Root`, `Engine`, `RoundState`, `IndexPoints`, `FoldClaim`),
`Audit.Wire3.Integrated` (`verify`, `DecodeGates`,
`accepted_preflights_and_original_verifier`),
`Audit.Wire3.CommitmentOrder` (`CommittedTables`).

NOTHING ABOVE IS RE-PROVED.  Five results below ARE re-exports of adopted
statements under clause vocabulary, and they are named here rather than left for
the reader to discover: `opened_cells_root_determined_or_collision` and
`opened_dot_root_determined_or_collision` are type-identical to
`OpenedDotBinding.opened_rows_bind_or_leaf_collision` and
`OpenedDotBinding.opened_dot_binds_or_leaf_collision`;
`opening_relation_is_root_blind` is type-identical to
`OpeningBinding.opening_relation_ignores_the_commitment`;
`full_columns_root_determined_follows_from_r1b` is type-identical to
`InstalledWhirTail.tail_extraction_ties_tables_to_the_pinned_roots`; and
`unopened_cells_are_outside_every_binding_argument` is a projection of
`OpeningBinding.mask_leaves_sixth_cell_unopened`.  Each is a renaming, not new
content.
-/

namespace Audit.Wire3.CommittedTablesClauses

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. Clause `configDeployed`: DERIVED on the Solidity route, up to a
LOCALIZED configuration-encoding collision -/

/-- **CLAUSE 1 IS A THEOREM ON EVERY ACCEPTED CALL.**  The called configuration's
`ExplicitEngine.core` IS the deployed one's -- which is literally the
`configDeployed` field of `CommitmentOrderSurvey.CommittedTablesJoin` -- unless
`khash` collides ON PRECISELY THE TWO CONFIGURATION ENCODINGS
`ExplicitEngine.encodeConfig c` and `ExplicitEngine.encodeConfig c₀`.

THE DISJUNCT IS LOCALIZED.  `LocalizedCollisions.khash_collision_is_a_tautology`
shows the adopted `ExplicitEngine.KhashCollision khash` holds for EVERY `khash`,
so a statement carrying it says nothing; `ConfigEncodingCollision` names its two
inputs and is refutable (`config_deployed_collision_disjunct_is_falsifiable`). -/
theorem config_deployed_of_acceptance_or_collision (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    ExplicitEngine.core c = ExplicitEngine.core c₀ ∨
      LocalizedCollisions.ConfigEncodingCollision khash c c₀ := by
  rcases LocalizedCollisions.accepted_configuration_is_the_deployment_localized gdec hash thash
    khash P c₀ pin chain c p hd hg hw hacc with heq | hcol
  · exact Or.inl (congrArg ExplicitEngine.core heq)
  · exact Or.inr hcol

/-- **CLAUSES 1 AND 2 TOGETHER, FROM ONE ACCEPTED CALL.**  The two deployment
clauses of `CommittedTablesJoin` in one conclusion.  Clause 2 needs no collision
disjunct of its own (section 2); it inherits the disjunction only because it is
stated here alongside clause 1. -/
theorem config_deployed_and_preprocessed_pinned_of_acceptance_or_collision
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    (ExplicitEngine.core c = ExplicitEngine.core c₀ ∧
        p.preprocessedRoot = pin.preprocessedRoot) ∨
      LocalizedCollisions.ConfigEncodingCollision khash c c₀ := by
  rcases LocalizedCollisions.accepted_call_is_a_deployed_call_localized gdec hash thash khash P c₀
    pin chain c p hd hg hw hacc with ⟨heq, -, -, hpre, -⟩ | hcol
  · exact Or.inl ⟨congrArg ExplicitEngine.core heq, hpre⟩
  · exact Or.inr hcol

/-- **THE DISJUNCT IS A LOCALIZED EVENT, NOT A PIGEONHOLE TAUTOLOGY.**  Side by
side: the adopted global predicate holds for every `khash` with no hypothesis,
while the localized one fails outright on equal configurations and fails, for
distinct configurations, under an explicit two-valued `khash`.  This is
`LocalizedCollisions`' lesson applied to clause 1, and it is why the disjunct
above is written the way it is. -/
theorem config_deployed_collision_disjunct_is_falsifiable (c c2 : Verifier.Config)
    (hne : ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c2) :
    (∀ khash : Verifier.Bytes → Verifier.Root, ExplicitEngine.KhashCollision khash) ∧
    (∀ khash : Verifier.Bytes → Verifier.Root,
      ¬ LocalizedCollisions.ConfigEncodingCollision khash c c) ∧
    ¬ LocalizedCollisions.ConfigEncodingCollision
      (LocalizedCollisions.separatingKhash (ExplicitEngine.encodeConfig c)) c c2 :=
  ⟨LocalizedCollisions.khash_collision_is_a_tautology,
   fun khash => LocalizedCollisions.config_encoding_collision_fails_on_equal_configurations khash c,
   LocalizedCollisions.config_encoding_collision_fails_for_a_separating_khash c c2 hne⟩

/-- **THE DEPLOYMENT HYPOTHESES OF CLAUSE 1 ARE JOINTLY SATISFIABLE.**  The five
`DeployedFacts` fields and the two word bounds at once, at the adopted
`OuterAdapter` fixture deployment and for every `khash`.  So
`config_deployed_of_acceptance_or_collision` is not a statement whose hypothesis
bundle is empty; the only hypothesis it carries that is exhibited NOWHERE in the
adopted tree is acceptance itself. -/
theorem deployment_hypotheses_are_inhabited (khash : Verifier.Bytes → Verifier.Root) :
    CanonicalProofCheck.DeployedFacts CanonicalProofCheck.exampleDecodeGates khash
      CanonicalProofCheck.exampleSyntheticProfile (CanonicalProofCheck.examplePinned khash)
      CanonicalProofCheck.exampleDeployedConfig ∧
    CanonicalProofCheck.exampleDeployedConfig.gatesEncoding.length < ExplicitEngine.wordBound ∧
    CanonicalProofCheck.exampleDeployedConfig.whirEncoding.length < ExplicitEngine.wordBound := by
  refine ⟨CanonicalProofCheck.example_deployed_facts_inhabited khash, ?_, ?_⟩
  · exact Nat.lt_of_lt_of_le (by decide) (Nat.one_le_iff_ne_zero.mpr
      (by norm_num [ExplicitEngine.wordBound]))
  · exact Nat.lt_of_lt_of_le (by decide) (Nat.one_le_iff_ne_zero.mpr
      (by norm_num [ExplicitEngine.wordBound]))

/-- **WHAT CLAUSE 1 DOES NOT SAY.**  `configDeployed` is an equality of
`ExplicitEngine.core`, and `core` is blind to the six residue fields
`gateRows`, `indexBits`, `circuitDigest`, `circuitConfigDigest`,
`whirProtocolId`, `whirSessionId`: moving all six at once changes neither the
encoding nor the core, by `rfl` on both.  Those six are pinned by OTHER
mechanisms (the envelope, the gate preflight, the canonical profile table and
`CanonicalProofCheck`'s two-digit pin), and
`LocalizedCollisions.accepted_configuration_is_the_deployment_localized` --
which is what the theorems above call -- reaches FULL configuration equality by
combining them.  Clause 1 as the survey states it is strictly weaker than that. -/
theorem config_deployed_is_blind_to_the_six_residue_fields (c : Verifier.Config) (gr ib : Nat)
    (cd : List Verifier.Base) (ccd : Verifier.Root) (pid sid : Verifier.Bytes) :
    ExplicitEngine.encodeConfig (ExplicitEngine.residueVariant c gr ib cd ccd pid sid)
        = ExplicitEngine.encodeConfig c ∧
      ExplicitEngine.core (ExplicitEngine.residueVariant c gr ib cd ccd pid sid)
        = ExplicitEngine.core c :=
  ⟨rfl, rfl⟩

/-! ### 1b. The Rust boundary: clause 1 is a SOLIDITY-side fact -/

/-- **WHAT THE RUST BOUNDARY GIVES.**  Solidity acceptance implies the Rust
per-call deployment predicate on the called configuration, up to the SAME
localized configuration-encoding collision.  The implication runs one way: the
VK's provenance on the Rust route is the deployment, and this is the transfer of
it. -/
theorem rust_deployment_of_solidity_acceptance_or_collision (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hr : RustCallBoundary.RustDeployedFacts gdec khash2 P c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    RustCallBoundary.rustDeployment gdec khash2 P c = true ∨
      LocalizedCollisions.ConfigEncodingCollision khash c c₀ :=
  LocalizedCollisions.rust_checks_are_consequences_of_solidity_acceptance_up_to_localized gdec
    hash thash khash khash2 P c₀ pin chain c p hd hr hg hw hacc

/-- **AND THE CONVERSE FAILS, SO CLAUSE 1 IS A SOLIDITY-SIDE FACT.**  From one
configuration passing every Rust check, two configurations passing every Rust
check whose `whirEncoding` differs and one of which the Solidity deployment
predicate rejects.  `ExplicitEngine.core` READS `whirEncoding`, so the pair also
separates `configDeployed`: no Rust-side check can deliver clause 1. -/
theorem config_deployed_is_not_implied_by_the_rust_checks (gdec : Integrated.DecodeGates)
    (khash2 : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ c : Verifier.Config) (we : Verifier.Bytes) (hne : we ≠ c₀.whirEncoding)
    (h : RustCallBoundary.rustDeployment gdec khash2 P c = true) :
    RustCallBoundary.rustDeployment gdec khash2 P { c with whirEncoding := we } = true ∧
    RustCallBoundary.rustDeployment gdec khash2 P { c with whirEncoding := c₀.whirEncoding }
      = true ∧
    ExplicitEngine.core ({ c with whirEncoding := we } : Verifier.Config)
      ≠ ExplicitEngine.core ({ c with whirEncoding := c₀.whirEncoding } : Verifier.Config) ∧
    ExplicitEngine.explicitDeployment P c₀ { c with whirEncoding := we } = false := by
  obtain ⟨h1, h2, h3, h4⟩ := RustCallBoundary.solidity_pins_are_not_implied_by_rust_checks gdec
    khash2 P c₀ c we hne h
  exact ⟨h1, h2, fun hcore => h3 (congrArg ExplicitEngine.Core.whirEncoding hcore), h4⟩

/-- The hypothesis of the previous theorem is satisfiable: the adopted Rust
example deployment passes every Rust check, for every `khash2` and profile. -/
theorem rust_deployment_hypothesis_is_inhabited (khash2 : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    RustCallBoundary.rustDeployment RustCallBoundary.exampleDecodeGates khash2 P
      (RustCallBoundary.exampleRustConfig khash2 P) = true :=
  RustCallBoundary.rust_deployment_of_deployed_facts RustCallBoundary.exampleDecodeGates khash2 P
    (RustCallBoundary.exampleRustConfig khash2 P)
    (RustCallBoundary.example_rust_deployed_facts_inhabited khash2 P)

/-! ## 2. Clause `preprocessedPinned`: DERIVED, with NO collision disjunct -/

/-- **CLAUSE 2 FOLLOWS FROM `Verifier.shape` ALONE.**  The run's preprocessed
root is the constructor-pinned one.  This is the model's stand-in for Rust's
`vk.preprocessed_commitment_root` comparison and for the Solidity immutable; it
is a decidable conjunct of the per-call shape guard, so it needs no hash, no
deployment invariant and no collision disjunct. -/
theorem preprocessed_pinned_of_shape (pin : Verifier.Pinned) (c : Verifier.Config)
    (p : Verifier.Proof) (h : Verifier.shape pin c p = true) :
    p.preprocessedRoot = pin.preprocessedRoot := by
  simp only [Verifier.shape, decide_eq_true_eq] at h
  exact h.2.2.2.2.1

/-- **CLAUSE 2 ON EVERY ACCEPTED CALL, FOR AN ARBITRARY ENGINE.**  No deployed
configuration, no `DeployedFacts`, no word bounds, no `khash` -- and no
disjunct.  Contrast `config_deployed_of_acceptance_or_collision`, which cannot
avoid one: clause 1 travels through the configuration digest and clause 2 does
not. -/
theorem preprocessed_pinned_of_acceptance (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify e gdec pin chain c p = .ok ()) :
    p.preprocessedRoot = pin.preprocessedRoot := by
  obtain ⟨-, -, -, -, hv⟩ := Integrated.accepted_preflights_and_original_verifier e gdec pin
    chain c p hacc
  exact preprocessed_pinned_of_shape pin c p
    (Verifier.verify_success_checks _ pin chain c p hv).2.2.2.2.1

/-- **WHICH ROOT IS NOT PINNED, (i).**  `Verifier.shape` does not mention the
witness root: replacing it by an arbitrary root leaves the guard definitionally
unchanged.  The witness root is the SECOND argument of the survey's `tablesOf`,
so this is exactly the half of the statement that clause 2 leaves to
`rootDetermined`. -/
theorem shape_ignores_the_witness_root (pin : Verifier.Pinned) (c : Verifier.Config)
    (p : Verifier.Proof) (r : Verifier.Root) :
    Verifier.shape pin c { p with witnessRoot := r } = Verifier.shape pin c p := rfl

/-- **WHICH ROOT IS NOT PINNED, (ii).**  The same for the norm-inverse root. -/
theorem shape_ignores_the_norm_inverse_root (pin : Verifier.Pinned) (c : Verifier.Config)
    (p : Verifier.Proof) (r : Verifier.Root) :
    Verifier.shape pin c { p with normInverseRoot := r } = Verifier.shape pin c p := rfl

/-- **AND THE CIRCUIT-DIGEST CONJUNCT POINTS AT THE CALLED CONFIGURATION.**
`Verifier.shape` ties `p.circuitDigest` to `c.circuitDigest`, not to `c₀`'s.
Closing that last step is `configDeployed`'s work
(`CanonicalProofCheck.accepted_proof_circuit_digest_is_deployed` performs the
composition).  Stated so that the division of labour between clauses 1 and 2 is
visible. -/
theorem shape_pins_the_circuit_digest_to_the_called_configuration (pin : Verifier.Pinned)
    (c : Verifier.Config) (p : Verifier.Proof) (h : Verifier.shape pin c p = true) :
    p.circuitDigest = c.circuitDigest ∧ p.preprocessedRoot = pin.preprocessedRoot := by
  simp only [Verifier.shape, decide_eq_true_eq] at h
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

/-! ## 3. Clause `rootDetermined`: this is R1b

### 3a. Root-determination IS opening-independence -/

/-- An extractor is OPENING-FREE when its output at fixed commitment roots does
not move with the round-one opening.  This is the property `rootDetermined`
demands and that `InstalledWhirTail.TailExtractsCommittedTables` does NOT supply:
R1b hands `extract` both arguments. -/
def OpeningFreeExtractor
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element)) : Prop :=
  ∀ (roots : List Spongefish.Digest) (o1 o2 : WhirIntermediate.Opening),
    extract roots o1 = extract roots o2

/-- An opening-free extractor produces a root-determined extracted state: the
whole `GateTerminalBinding.ProverState` is a function of the roots. -/
theorem opening_free_extraction_is_root_determined (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element)) (hfree : OpeningFreeExtractor extract)
    (roots : List Spongefish.Digest) (o1 o2 : WhirIntermediate.Opening) :
    ExtractorConstruction.extractedState thash c p extract roots o1
      = ExtractorConstruction.extractedState thash c p extract roots o2 := by
  unfold ExtractorConstruction.extractedState
  rw [hfree roots o1 o2]

/-- **AND THEN CLAUSE 3 HOLDS, UNIFORMLY IN THE OPENING.**  For an opening-free
extractor there is a `tablesOf` satisfying `rootDetermined` at EVERY opening at
once.

READ THE SCOPE EXACTLY.  The `tablesOf` exhibited ignores its two root arguments,
so this says root-determination is available as soon as opening-dependence is
gone -- it does NOT say the columns are the ones the roots NAME.  That further
step has no predicate in this model at all
(`opening_relation_is_root_blind`). -/
theorem root_determined_of_opening_free_extractor (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element)) (hfree : OpeningFreeExtractor extract)
    (roots : List Spongefish.Digest) :
    ∃ tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables,
      ∀ opening : WhirIntermediate.Opening,
        CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
          (ExtractorConstruction.extractedState thash c p extract roots opening).tables := by
  refine ⟨fun _ _ => (ExtractorConstruction.extractedState thash c p extract roots
    ⟨[], []⟩).tables, fun opening => ⟨?_, ?_⟩⟩
  · exact congrArg (fun s => (GateTerminalBinding.ProverState.tables s).wires)
      (opening_free_extraction_is_root_determined thash c p extract hfree roots opening ⟨[], []⟩)
  · exact congrArg (fun s => (GateTerminalBinding.ProverState.tables s).constants)
      (opening_free_extraction_is_root_determined thash c p extract hfree roots opening ⟨[], []⟩)

/-- The adopted opening-reading demo extractor is not opening-free -- one
`rfl`-level separation at the two adopted openings. -/
theorem demo_extractor_is_not_opening_free :
    ¬ OpeningFreeExtractor CommitmentOrderSurvey.demoExtract := by
  intro h
  exact CommitmentOrderSurvey.demo_extract_moves_with_the_opening []
    (⟨0, by decide⟩ : Fin 5)
    (congrFun (h [] CommitmentOrderSurvey.demoOpeningA CommitmentOrderSurvey.demoOpeningB)
      (⟨0, by decide⟩ : Fin 5))

/-! ### 3b. Clause 3 is FALSE, not merely unproved, at an opening-reading
extractor -/

/-- The head cell of the extracted wire TABLE, for a positive wire width. -/
theorem extracted_wire_table_head (n w : Nat) (cols : List (List Element)) (hw : 0 < w) :
    (((ExtractorConstruction.extractedColumns n w cols).map
        DenseMleIndexed.State.evaluations).getD 0 [])
      = ExtractorConstruction.fitColumn n (cols.getD 0 []) := by
  rw [ExtractorConstruction.extracted_columns_evals_map]
  have hlen : 0 < ((List.range w).map
      (fun i => ExtractorConstruction.fitColumn n (cols.getD i []))).length := by
    rw [List.length_map, List.length_range]
    exact hw
  rw [List.getD_eq_get _ _ hlen, List.get_eq_getElem, List.getElem_map, List.getElem_range]

/-- **THE EXTRACTED WIRE TABLES THEMSELVES MOVE WITH THE OPENING.**  The adopted
`CommitmentOrderSurvey.extracted_state_moves_with_the_opening` separates the
prover STATES; `CommittedTables` constrains only `.tables.wires` and
`.tables.constants`, so the separation is carried down to the wire TABLE here,
which is what clause 3 actually speaks about. -/
theorem demo_extracted_wire_tables_move_with_the_opening (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) (roots : List Spongefish.Digest)
    (hw : 0 < c.numWires) :
    (ExtractorConstruction.extractedState thash c p CommitmentOrderSurvey.demoExtract roots
        CommitmentOrderSurvey.demoOpeningA).tables.wires
      ≠ (ExtractorConstruction.extractedState thash c p CommitmentOrderSurvey.demoExtract roots
        CommitmentOrderSurvey.demoOpeningB).tables.wires := by
  intro h
  have hhead := congrArg (fun l => (l.getD 0 []).getD 0 (0 : Element)) h
  rw [show ((fun (l : List (List Element)) => (l.getD 0 []).getD 0 (0 : Element))
      (ExtractorConstruction.extractedState thash c p CommitmentOrderSurvey.demoExtract roots
        CommitmentOrderSurvey.demoOpeningA).tables.wires) = (0 : Element) from by
        show (((ExtractorConstruction.extractedColumns
          (TranscriptProvenance.gateTauColumn thash c p).length c.numWires
          [[(0 : Element)]]).map DenseMleIndexed.State.evaluations).getD 0 []).getD 0 (0 : Element)
          = 0
        rw [extracted_wire_table_head _ _ _ hw]
        exact CommitmentOrderSurvey.fit_column_head _ _,
    show ((fun (l : List (List Element)) => (l.getD 0 []).getD 0 (0 : Element))
      (ExtractorConstruction.extractedState thash c p CommitmentOrderSurvey.demoExtract roots
        CommitmentOrderSurvey.demoOpeningB).tables.wires) = (1 : Element) from by
        show (((ExtractorConstruction.extractedColumns
          (TranscriptProvenance.gateTauColumn thash c p).length c.numWires
          [[(1 : Element)]]).map DenseMleIndexed.State.evaluations).getD 0 []).getD 0 (0 : Element)
          = 1
        rw [extracted_wire_table_head _ _ _ hw]
        exact CommitmentOrderSurvey.fit_column_head _ _] at hhead
  exact zero_ne_one hhead

/-- **CLAUSE 3 IS NOT SATISFIABLE AT THE READING EXTRACTOR.**  There is NO
`tablesOf` whatsoever -- not merely none that the audit can name -- for which
`rootDetermined` holds at both of the two adopted openings, at the same
commitment roots and the same proof.

THIS IS THE PRECISE SENSE IN WHICH R1b IS MISSING.  `CommitmentOrderSurvey`'s
satisfiability witness uses a CONSTANT extractor; this theorem shows that is
forced: the moment the extractor reads the round-one opening -- as the R1b
extractor of `InstalledWhirTail.TailExtractsCommittedTables` does, by its very
type -- the clause fails.  Root-determination is exactly opening-independence
(`root_determined_of_opening_free_extractor` is the converse half). -/
theorem root_determined_clause_has_no_tables_map_for_the_reading_extractor
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (roots : List Spongefish.Digest) (hw : 0 < c.numWires) :
    ¬ ∃ tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables,
        CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
          (ExtractorConstruction.extractedState thash c p CommitmentOrderSurvey.demoExtract roots
            CommitmentOrderSurvey.demoOpeningA).tables ∧
        CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
          (ExtractorConstruction.extractedState thash c p CommitmentOrderSurvey.demoExtract roots
            CommitmentOrderSurvey.demoOpeningB).tables := by
  rintro ⟨tablesOf, hA, hB⟩
  exact demo_extracted_wire_tables_move_with_the_opening thash c p roots hw
    (hA.wires.trans hB.wires.symm)

/-- The side condition of the two previous theorems is satisfiable at a real
configuration: the adopted `OuterAdapter` fixture has two wire columns. -/
theorem positive_wire_width_at_the_fixture : 0 < OuterAdapter.fixtureConfig.numWires := by decide

/-! ### 3c. What the adopted binding lemmas DO give: the OPENED cells, up to a
LOCALIZED leaf collision -/

/-- At depth zero a group opening performs no Merkle compression, so the executed
compression-input list is empty.  Used to discharge the localized side condition
at the adopted fixture. -/
theorem executed_merkle_inputs_empty_at_depth_zero (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (indices : List Nat) (layout : WhirRows.Layout)
    (hints : Spongefish.Bytes) (s t : Spongefish.State) (rows : List WhirRows.RawRow)
    (h : WhirRows.openGroup hash root 0 indices layout hints s = some (rows, t)) :
    OpenedDotBinding.executedMerkleInputs hash root 0 indices layout hints s = [] := by
  rw [OpenedDotBinding.executedMerkleInputs_success hash root 0 indices layout hints s t rows h]
  rfl

/-- **ROOT-DETERMINATION OF THE OPENED CELLS, PROVED.**  Two accepted group
openings against the SAME commitment root, at the same depth and layout, sharing
a query index, return the SAME row bytes -- or a
`LocalizedCollisions.LeafCollision` on exactly those two rows.

This is the commitment BINDING property, and it is the whole of what
root-determination can be had from the adopted tree.  The hypotheses are
`OpenedDotBinding.opened_rows_bind_or_leaf_collision`'s: a
`OpeningBinding.NoCollision` over the two executions' MERKLE COMPRESSION inputs
only, which says nothing about the rows.  The right disjunct names both rows and
is therefore refutable; no probability is attached to it anywhere. -/
theorem opened_cells_root_determined_or_collision (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth index : Nat) (indices otherIndices : List Nat)
    (layout : WhirRows.Layout) (hints otherHints : Spongefish.Bytes)
    (s t otherS otherT : Spongefish.State) (rows otherRows : List WhirRows.RawRow)
    (row otherRow : WhirRows.RawRow)
    (hpath : OpeningBinding.NoCollision hash
      (OpenedDotBinding.executedMerkleInputs hash root depth indices layout hints s ++
        OpenedDotBinding.executedMerkleInputs hash root depth otherIndices layout otherHints
          otherS))
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h2 : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS
      = some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows)
    (hm2 : (index, otherRow) ∈ otherIndices.zip otherRows) :
    row.bytes = otherRow.bytes ∨
      LocalizedCollisions.LeafCollision hash row.bytes otherRow.bytes :=
  OpenedDotBinding.opened_rows_bind_or_leaf_collision hash root depth index indices otherIndices
    layout hints otherHints s t otherS otherT rows otherRows row otherRow hpath h h2 hm hm2

/-- The same at the level the engine consumes: the decoded dot value of an opened
row is determined by the root, up to the same localized leaf collision. -/
theorem opened_dot_root_determined_or_collision (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth index : Nat) (indices otherIndices : List Nat)
    (layout : WhirRows.Layout) (hints otherHints : Spongefish.Bytes)
    (s t otherS otherT : Spongefish.State) (rows otherRows : List WhirRows.RawRow)
    (row otherRow : WhirRows.RawRow) (weights : List Arithmetic.Ext3)
    (value otherValue : Arithmetic.Ext3)
    (hpath : OpeningBinding.NoCollision hash
      (OpenedDotBinding.executedMerkleInputs hash root depth indices layout hints s ++
        OpenedDotBinding.executedMerkleInputs hash root depth otherIndices layout otherHints
          otherS))
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h2 : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS
      = some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows)
    (hm2 : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRowBinding.decodedDot weights layout row = some value)
    (hd2 : WhirRowBinding.decodedDot weights layout otherRow = some otherValue) :
    value = otherValue ∨ LocalizedCollisions.LeafCollision hash row.bytes otherRow.bytes :=
  OpenedDotBinding.opened_dot_binds_or_leaf_collision hash root depth index indices otherIndices
    layout hints otherHints s t otherS otherT rows otherRows row otherRow weights value otherValue
    hpath h h2 hm hm2 hd hd2

/-- The adopted one-leaf fixture's hint buffer with one trailing byte appended.
The two buffers are DISTINCT LISTS, and that is the whole of the difference: the
opening stops at `hintPos := 16`, so the appended byte is never consumed and the
second execution reads exactly the same sixteen bytes as the first. -/
def paddedFixtureHints : Spongefish.Bytes :=
  WhirRows.exampleBaseHints ++ [Spongefish.zeroByte]

/-- **THE HYPOTHESES OF `opened_cells_root_determined_or_collision` ARE
SATISFIABLE, OFF THE DIAGONAL IN THE BUFFER ARGUMENT.**  Two accepted openings of
the adopted `WhirRows` base-row fixture against the same root, from two DISTINCT
hint buffers (third conjunct), together with the localized Merkle side condition
on their concatenated executed inputs.  Nothing is assumed; every conjunct is
discharged.

HONEST SCOPE, TWICE OVER.

* The fixture tree has depth zero, so the compression-input list is empty and the
  side condition holds for that reason
  (`executed_merkle_inputs_empty_at_depth_zero`).  The predicate is not vacuous in
  general: `OpenedDotBinding.clash_no_collision_among_fails` exhibits an execution
  pair at which it FAILS, and `opened_cells_root_determination_can_fail` records
  that the conclusion then fails with it.
* The two buffers differ only in a TRAILING BYTE THAT IS NEVER CONSUMED.  Both
  openings stop at `hintPos := 16` and return the same row, so the two executions
  are byte-identical over everything they read.  This defeats only the objection
  that the instantiation is literally diagonal in its buffer argument; it does NOT
  exhibit two genuinely different executions, and no claim below rests on its
  doing so. -/
theorem root_determination_hypotheses_hold_at_the_fixture :
    WhirRows.openGroup WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] ⟨.base, 1⟩
        WhirRows.exampleBaseHints WhirRows.exampleStart
      = some ([WhirRows.exampleBaseRow], { WhirRows.exampleStart with hintPos := 16 }) ∧
    WhirRows.openGroup WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] ⟨.base, 1⟩
        paddedFixtureHints WhirRows.exampleStart
      = some ([WhirRows.exampleBaseRow], { WhirRows.exampleStart with hintPos := 16 }) ∧
    WhirRows.exampleBaseHints ≠ paddedFixtureHints ∧
    OpeningBinding.NoCollision WhirRows.exampleHash
      (OpenedDotBinding.executedMerkleInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0]
          ⟨.base, 1⟩ WhirRows.exampleBaseHints WhirRows.exampleStart ++
        OpenedDotBinding.executedMerkleInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0]
          ⟨.base, 1⟩ paddedFixtureHints WhirRows.exampleStart) := by
  have hpad : WhirRows.openGroup WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] ⟨.base, 1⟩
      paddedFixtureHints WhirRows.exampleStart
        = some ([WhirRows.exampleBaseRow], { WhirRows.exampleStart with hintPos := 16 }) := by
    decide
  refine ⟨WhirRows.base_row_open_example, hpad, by decide, ?_⟩
  rw [executed_merkle_inputs_empty_at_depth_zero WhirRows.exampleHash WhirRows.exampleBaseRoot
      [0] ⟨.base, 1⟩ WhirRows.exampleBaseHints WhirRows.exampleStart
      { WhirRows.exampleStart with hintPos := 16 } [WhirRows.exampleBaseRow]
      WhirRows.base_row_open_example,
    executed_merkle_inputs_empty_at_depth_zero WhirRows.exampleHash WhirRows.exampleBaseRoot
      [0] ⟨.base, 1⟩ paddedFixtureHints WhirRows.exampleStart
      { WhirRows.exampleStart with hintPos := 16 } [WhirRows.exampleBaseRow] hpad]
  exact LocalizedCollisions.no_collision_holds_on_the_empty_list WhirRows.exampleHash

/-- The remaining hypothesis of the fully discharged instance below -- that the
row decodes to a dot value at all -- is satisfiable on the fixture row. -/
theorem fixture_decoded_dot_is_defined :
    (WhirRowBinding.decodedDot [⟨1, 0, 0⟩] ⟨.base, 1⟩ WhirRows.exampleBaseRow).isSome = true := by
  decide

/-- **A SMOKE TEST, NOT EVIDENCE OF BINDING.**  This is
`opened_dot_root_determined_or_collision` with every hypothesis supplied from the
fixture and none assumed, the localized disjunct refuted outright because the two
rows are equal and `LocalizedCollisions.LeafCollision` is false on an equal pair.

READ THE STATEMENT, NOT THE PROOF.  **The conclusion here is TRIVIALLY TRUE.**
Both `hd` and `hd2` decode the SAME literal row `WhirRows.exampleBaseRow` -- the
fixture's two executions return the same row, as
`root_determination_hypotheses_hold_at_the_fixture` itself says -- so `value =
otherValue` follows from `Option.some.inj` alone, with no opening, no root, no
`NoCollision` and no collision refutation.  That shorter proof is recorded
immediately below as `fixture_dot_equality_needs_no_binding_lemma`, so the point
is machine-checked and not merely conceded.  What this theorem establishes is
therefore ONLY that the binding lemma's hypothesis bundle can be instantiated and
discharged end to end at the adopted fixture; it establishes NOTHING about
binding, because at this fixture there is no second row for binding to constrain. -/
theorem opened_dot_root_determination_instantiates_at_the_fixture
    (weights : List Arithmetic.Ext3)
    (value otherValue : Arithmetic.Ext3)
    (hd : WhirRowBinding.decodedDot weights ⟨.base, 1⟩ WhirRows.exampleBaseRow = some value)
    (hd2 : WhirRowBinding.decodedDot weights ⟨.base, 1⟩ WhirRows.exampleBaseRow
      = some otherValue) :
    value = otherValue := by
  obtain ⟨h1, h2, -, hpath⟩ := root_determination_hypotheses_hold_at_the_fixture
  rcases opened_dot_root_determined_or_collision WhirRows.exampleHash WhirRows.exampleBaseRoot
    0 0 [0] [0] ⟨.base, 1⟩ WhirRows.exampleBaseHints paddedFixtureHints WhirRows.exampleStart
    { WhirRows.exampleStart with hintPos := 16 } WhirRows.exampleStart
    { WhirRows.exampleStart with hintPos := 16 } [WhirRows.exampleBaseRow]
    [WhirRows.exampleBaseRow] WhirRows.exampleBaseRow WhirRows.exampleBaseRow weights value
    otherValue hpath h1 h2 OpenedDotBinding.example_row_membership
    OpenedDotBinding.example_row_membership hd hd2 with heq | hleaf
  · exact heq
  · exact absurd hleaf (OpenedDotBinding.leaf_collision_fails_on_equal_rows _ _)

/-- **THE SAME CONCLUSION IN ONE STEP, WITH NO BINDING LEMMA AT ALL.**  Exactly
the statement above, proved from `Option.some.inj`: the fixture's two openings
decode the same literal row, so nothing in section 3c is doing any work there.
Stated so that the triviality admitted in the previous docstring is checked by
Lean rather than asserted in prose. -/
theorem fixture_dot_equality_needs_no_binding_lemma (weights : List Arithmetic.Ext3)
    (value otherValue : Arithmetic.Ext3)
    (hd : WhirRowBinding.decodedDot weights ⟨.base, 1⟩ WhirRows.exampleBaseRow = some value)
    (hd2 : WhirRowBinding.decodedDot weights ⟨.base, 1⟩ WhirRows.exampleBaseRow
      = some otherValue) :
    value = otherValue :=
  Option.some.inj (hd.symm.trans hd2)

/-- **AND IT CAN FAIL, WHICH IS WHY THE DISJUNCT IS NOT DECORATION.**  On the
adopted clash fixture two openings of the same root at the same index return
DIFFERENT rows, so the left disjunct of
`opened_cells_root_determined_or_collision` is false and the localized leaf
collision is ACHIEVED.  A localized predicate that can both hold and fail is what
`LocalizedCollisions` asks for; the global disjuncts -- `KhashCollision`, which
holds for every `khash` with no hypothesis, and the second, row-blind disjunct of
`WhirRowBinding.RowCollision`, which the adopted header calls HALF localized --
cannot do this. -/
theorem opened_cells_root_determination_can_fail :
    OpeningBinding.clashRowA.bytes ≠ OpeningBinding.clashRowB.bytes ∧
    LocalizedCollisions.LeafCollision OpeningBinding.clashHash OpeningBinding.clashRowA.bytes
      OpeningBinding.clashRowB.bytes ∧
    (∀ (hash : Spongefish.Hash) (row : Spongefish.Bytes),
      ¬ LocalizedCollisions.LeafCollision hash row row) :=
  ⟨OpeningBinding.clash_rows_differ, OpenedDotBinding.clash_leaf_collision_holds,
   OpenedDotBinding.leaf_collision_fails_on_equal_rows⟩

/-! ### 3d. The FULL columns: what remains is R1b proper -/

/-- **THE OPENING RELATION IS ROOT-BLIND, SO BINDING CANNOT REACH THE FULL
COLUMNS.**  Replacing all three of the proof's Merkle roots by arbitrary ones
preserves `OpeningBinding.OpensCommittedTable` exactly.  No reduction from
same-root binding -- which is all section 3c gives -- can therefore produce a map
from a `Verifier.Root` to a column list, and `rootDetermined` asks for precisely
such a map (`tablesOf`).  This is the adopted residue R2, restated as the
obstruction to clause 3.

NAME.  What is proved is ROOT-INVARIANCE of the opening relation, which is what
this name says; the stronger gloss "no root-to-column map is definable" is the
INFORMAL reading of it and is not itself a Lean statement here.  This is a
type-identical re-export of
`OpeningBinding.opening_relation_ignores_the_commitment`. -/
theorem opening_relation_is_root_blind (c : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints)
    (cols : Fin 5 → List (List Element)) (r1 r2 r3 : Verifier.Root)
    (h : OpeningBinding.OpensCommittedTable c p s idx cols) :
    OpeningBinding.OpensCommittedTable c
      { p with preprocessedRoot := r1, witnessRoot := r2, normInverseRoot := r3 } s idx cols :=
  OpeningBinding.opening_relation_ignores_the_commitment c p s idx cols r1 r2 r3 h

/-- **THE UNOPENED CELLS ARE OUTSIDE EVERY BINDING ARGUMENT.**  The sixth claim
slot is unopened for every proof, so nothing about it follows from any opening.
Section 3c binds the QUERIED rows; the committed column has `2 ^ m` cells and the
queries touch a bounded subset of them. -/
theorem unopened_cells_are_outside_every_binding_argument (foldClaim : Verifier.FoldClaim)
    (c : Verifier.Config) (p : Verifier.Proof) (idx : Verifier.IndexPoints) :
    (Verifier.expectedClaims foldClaim c p idx).map Option.isSome
      = [true, true, true, true, true, false] :=
  (OpeningBinding.mask_leaves_sixth_cell_unopened foldClaim c p idx).2.2

/-- **WHAT REMAINS, STATED HONESTLY: FULL-COLUMN ROOT-DETERMINATION IS R1b.**
Under `InstalledWhirTail.TailExtractsCommittedTables`, and only under it, each
accepted run gets a committed column family opening its claims, and the two
families COINCIDE exactly when the two runs pinned the same commitment roots.
That is root-determination of the full columns, and it is an ASSUMPTION here as
it is in the adopted tree: R1b is WHIR proximity / list decoding plus sumcheck
soundness, probabilistic, and absent from the audit.

Nothing in section 3c approaches it -- section 3c is same-root binding on the
opened rows, and `opening_relation_is_root_blind` shows that route is closed.

NAME AND DIRECTION.  This proves ONE DIRECTION: R1b gives full-column
root-determination.  It does not prove the converse, and the name says so.  It is
a type-identical re-export of
`InstalledWhirTail.tail_extraction_ties_tables_to_the_pinned_roots`. -/
theorem full_columns_root_determined_follows_from_r1b (hash : Spongefish.Hash)
    (wp : InstalledWhirTail.VkParams)
    (hyp : InstalledWhirTail.TailExtractsCommittedTables hash wp)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (e2 : Verifier.Engine) (decode2 : Integrated.DecodeGates) (pin2 : Verifier.Pinned)
    (chain2 : Nat) (c2 : Verifier.Config) (p2 : Verifier.Proof)
    (r r2 : WhirTail.Result) (opening : WhirIntermediate.Opening)
    (h : Integrated.verify (InstalledWhirTail.installedEngine e decode hash wp) decode pin chain
      c p = .ok ())
    (h2 : Integrated.verify (InstalledWhirTail.installedEngine e2 decode2 hash wp) decode2 pin2
      chain2 c2 p2 = .ok ())
    (hrun : InstalledWhirTail.tailRun hash wp
      (InstalledWhirTail.installedContext e decode hash wp c p) p.whirTranscript p.whirHints
      = some r)
    (hrun2 : InstalledWhirTail.tailRun hash wp
      (InstalledWhirTail.installedContext e2 decode2 hash wp c2 p2) p2.whirTranscript
      p2.whirHints = some r2)
    (hopen : InstalledWhirTail.RoundOneOpening hash wp
      (InstalledWhirTail.outerBytes p.whirHints) r opening)
    (hopen2 : InstalledWhirTail.RoundOneOpening hash wp
      (InstalledWhirTail.outerBytes p2.whirHints) r2 opening) :
    ∃ cols cols2 : Fin 5 → List (List Element),
      OpeningBinding.OpensCommittedTable c p (Verifier.derivedRounds e c p)
        (Verifier.derivedIndices e c p) cols ∧
      OpeningBinding.OpensCommittedTable c2 p2 (Verifier.derivedRounds e2 c2 p2)
        (Verifier.derivedIndices e2 c2 p2) cols2 ∧
      (r.retained.origin.initial.commitments.map (·.root) =
        r2.retained.origin.initial.commitments.map (·.root) → cols = cols2) :=
  InstalledWhirTail.tail_extraction_ties_tables_to_the_pinned_roots hash wp hyp e decode pin
    chain c p e2 decode2 pin2 chain2 c2 p2 r r2 opening h h2 hrun hrun2 hopen hopen2

/-! ## 4. The join at a non-degenerate instance, up to two localized events -/

/-- **THE HEADLINE.**  On every accepted Solidity call, `CommittedTablesJoin`
holds as soon as its `rootDetermined` clause is supplied -- or `khash` collides
on the two named configuration encodings.

READ THE SCOPE EXACTLY.

* Clauses 1 and 2 are DISCHARGED here from acceptance.  Clause 2 carries no
  collision disjunct at all (`preprocessed_pinned_of_acceptance`); the disjunct
  belongs entirely to clause 1 and is LOCALIZED to
  `ExplicitEngine.encodeConfig c` versus `ExplicitEngine.encodeConfig c₀`.
* Clause 3 is a HYPOTHESIS, and it is R1b.  Section 3 shows it is not decoration:
  at the adopted opening-reading extractor it is outright FALSE as a uniform
  statement (`root_determined_clause_has_no_tables_map_for_the_reading_extractor`),
  so this theorem is a reduction of the join to R1b, not a proof of the join.
* The instance is NOT the degenerate one of
  `CommitmentOrderSurvey.committed_tables_join_is_satisfiable`: `extract`,
  `tablesOf`, `roots` and `opening` are arbitrary, and the configuration is the
  ACCEPTED one rather than the called one taken as deployed. -/
theorem committed_tables_join_up_to_collisions
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening)
    (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ())
    (hr1b : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract roots opening).tables) :
    CommitmentOrderSurvey.CommittedTablesJoin tablesOf thash c c₀ pin extract p roots opening ∨
      LocalizedCollisions.ConfigEncodingCollision khash c c₀ := by
  rcases config_deployed_and_preprocessed_pinned_of_acceptance_or_collision gdec hash thash khash
    P c₀ pin chain c p hd hg hw hacc with ⟨hcore, hpre⟩ | hcol
  · exact Or.inl ⟨hr1b, hpre, hcore⟩
  · exact Or.inr hcol

/-- **R1b AT THE TWO RUNS IS ALREADY ENOUGH FOR THE TABLE.**  No acceptance, no
`DeployedFacts`, no word bounds, no engine, no `khash`, no deployed configuration
and NO COLLISION DISJUNCT: two runs of the same proof, at different roots and
different round-one openings, give the SAME assembly tau table as soon as R1b
holds at both AT THE SAME `tablesOf`.

WHY.  `hr1bOne` and `hr1bTwo` pin both extracted table pairs to the same
`tablesOf` applied to the same `Verifier.statement p`, so the wire and constant
columns are equal by transitivity, and
`CommitmentOrderSurvey.prefix_tau_table_depends_only_on_wires_and_constants`
closes it.  The clause-1 apparatus that
`tau_table_is_fixed_data_up_to_r1b_and_one_localized_collision` carries is INERT
for this conclusion; that theorem keeps it only for uniformity with
`committed_tables_join_up_to_collisions`. -/
theorem tau_table_is_fixed_data_from_r1b_at_the_two_runs_alone
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (rootsOne rootsTwo : List Spongefish.Digest)
    (openingOne openingTwo : WhirIntermediate.Opening)
    (hr1bOne : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract rootsOne openingOne).tables)
    (hr1bTwo : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract rootsTwo openingTwo).tables) :
    CommitmentOrderSurvey.prefixTauTable thash c gates publicHash (Verifier.statement p)
        (ExtractorConstruction.extractedState thash c p extract rootsOne openingOne).tables
      = CommitmentOrderSurvey.prefixTauTable thash c gates publicHash (Verifier.statement p)
        (ExtractorConstruction.extractedState thash c p extract rootsTwo openingTwo).tables :=
  CommitmentOrderSurvey.prefix_tau_table_depends_only_on_wires_and_constants thash c gates
    publicHash (Verifier.statement p) _ _ (hr1bOne.wires.trans hr1bTwo.wires.symm)
    (hr1bOne.constants.trans hr1bTwo.constants.symm)

/-- **THE CONSEQUENCE FOR THE ROM LINE, IN THE JOIN'S OWN VOCABULARY.**  The
sentence the ROM modules repeat -- "the zero-check table `g` is FIXED DATA, equal
to the deployed circuit's" -- is, for its TABLE argument, reduced to exactly two
things: R1b at each of the two runs, and one localized configuration-encoding
collision.  Two accepted runs of the same proof at different roots and different
round-one openings give the SAME assembly tau table.

WHAT IS AND IS NOT LOAD-BEARING HERE.  Only the two R1b hypotheses are.  The
acceptance hypothesis, `DeployedFacts`, both word bounds AND THE COLLISION
DISJUNCT ITSELF are INERT: `tau_table_is_fixed_data_from_r1b_at_the_two_runs_alone`
proves the left disjunct from `hr1bOne` and `hr1bTwo` alone, because the two
hypotheses pin the tables to the SAME `tablesOf (Verifier.statement p)`.  They are
carried here SOLELY so that this statement reads uniformly with
`committed_tables_join_up_to_collisions`, whose clause-1 half genuinely needs all
of them.  The localized LEAF collision is not among them either: it belongs to
section 3c (the opened cells) and plays no part in this theorem.

WHAT THIS DOES NOT DO.  It does not make `g` fixed data: even here `g` remains a
function of the block-0 gate alpha coordinate, which is a squeezed CHALLENGE (the
adopted `CommitmentOrderSurvey` category (e) correction), and the diagonal
argument for that is `EngineTauDiagonal`'s, not this module's.  It adds no
probability: the two events this development localizes -- the configuration
encoding collision here and the leaf collision of section 3c -- are deterministic
predicates on named byte strings, and their ROM masses are birthday terms on
frame inputs that `BirthdayClashBound` would have to supply.  NONE IS COMPUTED
HERE. -/
theorem tau_table_is_fixed_data_up_to_r1b_and_one_localized_collision
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (rootsOne rootsTwo : List Spongefish.Digest)
    (openingOne openingTwo : WhirIntermediate.Opening)
    (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ())
    (hr1bOne : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract rootsOne openingOne).tables)
    (hr1bTwo : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract rootsTwo openingTwo).tables) :
    CommitmentOrderSurvey.prefixTauTable thash c gates publicHash (Verifier.statement p)
        (ExtractorConstruction.extractedState thash c p extract rootsOne openingOne).tables
      = CommitmentOrderSurvey.prefixTauTable thash c gates publicHash (Verifier.statement p)
        (ExtractorConstruction.extractedState thash c p extract rootsTwo openingTwo).tables ∨
    LocalizedCollisions.ConfigEncodingCollision khash c c₀ := by
  rcases committed_tables_join_up_to_collisions tablesOf gdec hash thash khash P c₀ pin chain c p
    extract rootsOne openingOne hd hg hw hacc hr1bOne with h1 | hcol
  · rcases committed_tables_join_up_to_collisions tablesOf gdec hash thash khash P c₀ pin chain c
      p extract rootsTwo openingTwo hd hg hw hacc hr1bTwo with h2 | hcol
    · exact Or.inl (CommitmentOrderSurvey.committed_tables_join_fixes_the_tau_table tablesOf thash
        c c₀ pin gates publicHash extract p rootsOne rootsTwo openingOne openingTwo h1 h2)
    · exact Or.inr hcol
  · exact Or.inr hcol

/-- **THE CLAUSE-BY-CLAUSE VERDICT IN ONE STATEMENT.**  Clause 2 unconditionally
from acceptance; clause 1 from acceptance up to ONE localized collision naming
its two configuration encodings; clause 3 not merely open but FALSE at an
opening-reading extractor, hence the residue.  Read the three conjuncts as the
summary of this module. -/
theorem committed_tables_clauses_verdict (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (roots : List Spongefish.Digest)
    (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hnw : 0 < c.numWires)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ())
    (haccE : Integrated.verify e gdec pin chain c p = .ok ()) :
    p.preprocessedRoot = pin.preprocessedRoot ∧
    (ExplicitEngine.core c = ExplicitEngine.core c₀ ∨
      LocalizedCollisions.ConfigEncodingCollision khash c c₀) ∧
    ¬ ∃ tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables,
        CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
          (ExtractorConstruction.extractedState thash c p CommitmentOrderSurvey.demoExtract roots
            CommitmentOrderSurvey.demoOpeningA).tables ∧
        CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
          (ExtractorConstruction.extractedState thash c p CommitmentOrderSurvey.demoExtract roots
            CommitmentOrderSurvey.demoOpeningB).tables :=
  ⟨preprocessed_pinned_of_acceptance e gdec pin chain c p haccE,
   config_deployed_of_acceptance_or_collision gdec hash thash khash P c₀ pin chain c p hd hg hw
     hacc,
   root_determined_clause_has_no_tables_map_for_the_reading_extractor thash c p roots hnw⟩

end Audit.Wire3.CommittedTablesClauses
