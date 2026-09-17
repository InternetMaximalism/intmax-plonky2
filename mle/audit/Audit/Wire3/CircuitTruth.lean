import Audit.Wire3.SoundnessAssembly
import Audit.Wire3.GateEvaluatorCoverage
import Audit.Wire3.R1bBridge
import Audit.Wire3.ConstantsProvenance

/-!
# `Audit.Wire3.CircuitTruth` — the audit's target sentence, conditionally

This module turns the adopted **good-draw constraint vanishing** of
`SoundnessAssembly.explicit_good_draw_assembly` into the semantic sentence

> the extracted witness tables satisfy the circuit's selected-gate constraints
> on every row, and are pairwise run-independent under the per-pair ROM binding
> event — which is what "the commitment determines them" means computationally

as a **conditional** theorem chained through the new `R1bBridge`.  Nothing here
is unconditional, and nothing here is a statement-truth claim: read §0.

## What is new here, in four rungs

1. **WHOLE-CIRCUIT PACKAGING** (§2).  The adopted theorem is stated at ONE gate,
   the middle of a `pre ++ gate :: post` decomposition.  `selected_gate_terms_vanish`
   quantifies it over EVERY gate of the decoded list.  The quantifier is free:
   `AssemblyResidue`, the outer-draw hypothesis and the index hypothesis all
   mention the gate list only as the single list `gates`, never as a
   decomposition, so ONE `AssemblyResidue` and ONE draw hypothesis serve every
   gate simultaneously.  The packaged theorem carries no family of hypotheses.

2. **UNIQUE SELECTION, PROVED FROM THE TREE'S OWN SELECTOR SEMANTICS** (§1).
   The adopted single-gate theorem asks the caller to supply "every other gate's
   filter vanishes at this row".  `unique_selection_of_plonky2_selector_row`
   DERIVES that from plonky2's selector construction as this tree already models
   it: `Gates.other_row_zero_filter` (a gate whose group's selector column holds
   another row index of the same group has zero filter) and
   `Gates.unused_selector_zero_filter` (a gate whose own selector column holds
   the `4294967295` UNUSED marker has zero filter when `1 < numSelectors`).
   What must still be SUPPLIED is the description of the row's selector VALUES —
   `SelectorRowIsPlonky2`, §1 — which is a statement about the constants columns,
   not about the gate metadata.  Its provenance is `ConstantsProvenance`: that
   module's chain identifies the constants cells the filters read with claimed,
   committed cells up to a collision, and `ConstantsProvenance.pinned_filters_transfer`
   moves every filter to the pinned columns under
   `ConstantsProvenance.SuppliedConstantsAreCommitted`.  **Column identification
   itself remains undischarged there, and so remains undischarged here.**

3. **SEMANTICS** (§3).  `∀ y ∈ terms, y = 0` is a statement about the output of
   the adopted DISPATCHER.  §3 moves it, via
   `GateEvaluatorCoverage.validated_full_evaluator_agrees`, onto
   `GateEvaluatorCoverage.evaluateGateFull` — the shape-checked per-family
   evaluator whose fourteen branches are the per-family formulas transcribed
   from the audited Rust — and then unfolds four families into their real
   plonky2 relations.  Coverage and caveats: §5 of this docstring.

4. **THE CONDITIONAL CIRCUIT-TRUTH SENTENCE** (§4),
   `extracted_tables_satisfy_the_selected_gate_constraints_and_are_pairwise_run_independent`.
   One theorem, every assumption visible, with the assumption ledger in its own
   docstring.  §5 adopts the adversarial review's counter-probes as recorded
   honest negatives, including the two that forced §4's restatement.

## §0. WHAT THIS IS NOT

* **NOT** a proof that the deployed system is sound, and **NOT** a proof that an
  accepted proof implies a satisfying assignment exists.  Acceptance is a
  HYPOTHESIS here, never an exhibit, at the explicit engine (`§5` ledger item 5),
  and `{hacc, AssemblyResidue, hdraw, hidx}` HAVE NEVER BEEN JOINTLY INHABITED
  (ledger item 5); the sentence may be vacuous at that engine for all this tree
  knows.
* **NOT** a statement about the prover's witness.  The tables are the
  EXTRACTOR's.  What the R1b bridge adds is PAIRWISE RUN-INDEPENDENCE of those
  tables under the per-pair ROM binding event — that is the honest reading of
  "the commitment determines them".  It is NOT "the columns the root NAMES": the
  bridge's `tablesOf` route ignores its root arguments
  (`CommitmentOrderSurvey.opening_relation_is_root_blind`, quoted by
  `R1bBridge`), and the `∃ tablesOf, CommitmentOrder.CommittedTables …` shape is
  an UNCONDITIONAL TAUTOLOGY (`committed_tables_existential_is_a_tautology`, §5),
  so no sentence carrying it says anything about the commitment.
* **NOT** end-to-end statement truth.  §5 is the ledger of what is missing.

## §5. COVERAGE AND THE LEDGER — see `REPORT.md` for the prose

Families with a FULL semantic unfolding here: ids `0` (`NoopGate`), `1`
(`ConstantGate`), `2` (`PublicInputGate`), `3` (`ArithmeticGate`).  Every one of
the fourteen gets the `evaluateGateFull` form, which IS the per-family formula;
the four above are additionally restated as their field equations.  The caveats
of `GateEvaluatorCoverage` are inherited VERBATIM: the per-family formulas are
transcribed from the audited Rust with file and line cited per family and are
not themselves verified against Plonky2's own gate implementations; `LookupGate`
and `LookupTableGate` have no id at all (`GateEvaluatorCoverage.lookup_families_have_no_evaluator`).

**THE LEDGER, EVERY NAMED ITEM.**

1. **COPY / ROUTING CONSTRAINTS.**  This module says NOTHING about them.  The
   precise missing statement is: *THE COMMITTED TABLES ARE CONSTANT ON EACH
   PERMUTATION ORBIT OF THE CIRCUIT'S ROUTING.*  The adopted norm/logUp line
   (`NormTerminalBinding.fully_bound_round_target_is_norm_evaluate`,
   `NormDenseRound`, `NormPolynomial`, `NormIdentity`) gives an EQUATION BETWEEN
   TWO EVALUATIONS at the terminal; the wiring semantics behind it — that
   equation transported to a statement about routed cells — is stated nowhere
   reached from here.  `NormIdentity`'s own header disclaims primality,
   irreducibility, nonzero norm for every nonzero input, Fermat inversion and
   PCS/FS soundness.
2. **PUBLIC-INPUT BINDING.**  ONLY the `PublicInputGate` ROW EQUATION is reached
   (`public_input_gate_semantics`: the row's first four wires are the four limbs
   of `publicHashFunction (engine.publicInputsHash p.publicInputs)`).  That the
   hash function is the RIGHT one and that it BINDS the statement's public inputs
   is NOT closed here; `PublicInputHashBinding` and the norm terminal's
   `publicInputBinding` term are the adopted material a later module would use.
3. **THE TRUTH COLUMNS AND `coeffsOf` PROVENANCE.**  `logTruths` and `gateTruths`
   enter as FREE lists; `AssemblyResidue.extractedTruthChain` constrains the gate
   side only through `GateClaimChain.TruthChain` at the derived alpha, and
   nothing here pins either list to anything a verifier observes.  `coeffsOf` is
   a FREE function, constrained only by `AssemblyResidue.slotCoefficients`
   (existence of alpha-side slot coefficients per Boolean row) and carrying NO
   width bound in the deterministic half used here.
4. **ROOT-BLINDNESS.**  The bridge's `tablesOf` route ignores both root
   arguments, so "the columns the ROOT NAMES" is not said, and item 1 cannot be
   repaired through the bridge.  §4 therefore states RUN-INDEPENDENCE, not
   root-naming.
5. **ACCEPTANCE AND THE RESIDUE ARE NEVER JOINTLY INHABITED.**  No
   `AssemblyResidue` INSTANCE exists in this tree.  The nearest is
   `ExtractorConstruction` §8 (`:733-745`): 10 of 19 fields discharged, with the
   two keccak fields, four deployment/ABI fields, `gatesDecode`,
   `gateConstraintsPositive`, `activeFilter` and the fold-level R1b field left
   assumed.  `SoundnessAssembly.lean:749-752` states that nothing shows `hacc`
   and `AssemblyResidue` can hold TOGETHER.  This is the sentence's DEEPEST
   CONDITIONAL LAYER.  The one positive: `hdraw` is SATISFIED BY EVERY HONEST
   EXTRACTION (`outerBadEvent` is empty on honest extraction data), which that
   block itself says is not joint satisfiability.
6. **THE SELECTOR COLUMNS' CONTENT.**  `SelectorRowIsPlonky2` is hypothesized per
   row; `ConstantsProvenance`'s column identification
   (`residue_columns_share_bound_cell`, `bound_cell_agreement_is_not_column_equality`)
   is undischarged and stays so.  The `4294967295` UNUSED marker used by the
   structure's fifth field is cross-checked against `u32::MAX` in the audited
   Rust (`mle/src/gate_ext3.rs:33`, `:629-647`) and its two Solidity mirrors.
   `sameGroupRange` is a SUFFICIENT but NON-CANONICAL encoding of plonky2's
   one-group-one-range condition: it constrains every gate sharing the active
   column, which implies what the filters need without being that source's own
   phrasing.
7. **THE TRANSCRIPTION CAVEAT.**  The fourteen per-family formulas are
   TRANSCRIBED from the audited Rust with file and line cited per family, and are
   NOT verified against Plonky2's own gate implementations.
8. **THE COSET FAMILY IS LAYOUT-SHAPE-GATED.**  Id `13`
   (`CosetInterpolationGate`) evaluates only under
   `GatesAdditionalCoset.layoutValid`, so `evaluateGateFull` CAN RETURN `none`
   there and the sentence is silent at such a row.
9. **ROWS WHERE NO GATE IS SELECTED.**  §4's ∀-row quantifier is GATED on the
   nonzero-filter hypothesis `hnz`.  Rows at which EVERY filter vanishes are
   WHOLLY UNCONSTRAINED by this module; `AssemblyResidue.activeFilter` asserts
   only that SOME row selects SOME gate.  `GateRejectionPower.AllFiltersZero` is
   that regime and `ConstantsProvenance`'s partial-zeroing attack theorems are
   what speak about it.
10. **THE MASS SIDE IS NOT USED.**  `hdraw` and `hidx` are facts about two fixed
    points of two explicit finite spaces; nothing in the adopted tree says the
    run's draws are distributed by either law, and the masses of
    `bad_event_mass_le` / `index_bad_event_mass_le` exclude the dominant
    WHIR/Merkle term.
11. **`hdec` IS ASSUMED.**  WHIR decode uniqueness is cited to the literature at
    the deployed parameters and proven NOWHERE in this tree; the per-pair ROM
    event is a computational assumption, and its ∀-quantified and uniform-family
    variants are both REFUTED (`R1bBridge` §7 and §5 here).
12. **`Nodup` IS A REAL ADDED DEPLOYMENT ASSUMPTION.**  `Gates.validateConfiguration`
    contains NO distinctness check, and `Nodup` appears nowhere in `Gates`,
    `ConstantsProvenance` or `GateClaimChain`.  It is imposed here and discharged
    by nobody.  The honest WEAKENING a later module should take is
    `gates.count gate = 1` at the selected gate only.  §5a records that
    `distinctRows` does NOT subsume it: on a duplicated list that field is
    VACUOUS and every other hypothesis still holds.

Naming: no `?`, no primes, no dots inside identifiers; no `Finset.univ` in any
statement; no numeric evaluation of any `Fintype.card`.
-/

namespace Audit.Wire3.CircuitTruth

open Audit.Wire3

/-! ## §1. UNIQUE SELECTION, FROM PLONKY2'S SELECTOR CONSTRUCTION -/

/-- The value the gate lane reads out of constants column `j` at Boolean row
`row`.  This is literally the read `GateRejectionPower.rowFilter` performs,
factored out so that two gates sharing a selector column visibly share a value. -/
def rowSelectorAt (t : GateSuffixPolynomial.Tables) (row j : Nat) : Verifier.Ext3 :=
  Gates.readValue (AlphaZeroCheck.rowConstants t row) j

/-- `rowFilter` is `computeFilter` at that read.  Definitional. -/
theorem row_filter_via_row_selector (c : Gates.Config) (g : Gates.GateInfo)
    (t : GateSuffixPolynomial.Tables) (row : Nat) :
    GateRejectionPower.rowFilter c g t row
      = Gates.computeFilter g (rowSelectorAt t row g.selectorIndex)
        (decide (1 < c.numSelectors)) := rfl

/-- **PLONKY2'S SELECTOR CONSTRUCTION AT ONE ROW, AS A NAMED HYPOTHESIS.**

In plonky2 the gates are partitioned into selector GROUPS, one constants column
per group; at each row the column of the group containing the active gate holds
that gate's row index inside the group, and every OTHER group's column holds the
`UNUSED_SELECTOR` marker `4294967295`.  These five fields are that sentence, and
nothing more.  They are statements about the CONSTANTS COLUMNS of `t` at `row`
(fields 2 and 5) and about the decoded gate METADATA (fields 3 and 4).

**PROVENANCE, STATED HONESTLY.**  `ConstantsProvenance` is the adopted module
that speaks about exactly these reads: `rowFilter_reads_one_constants_entry` and
`rowFilter_depends_only_on_constants` pin the read;
`selector_source_is_a_claimed_constants_column` chains it to a claimed constants
column; `gate_preprocessed_claims_are_committed_cells` and
`forged_constants_cell_is_the_committed_cell` carry it to the committed cell up
to a collision; and under the named column identification
`ConstantsProvenance.SuppliedConstantsAreCommitted`,
`ConstantsProvenance.pinned_filters_transfer` moves EVERY filter at EVERY gate
and EVERY row to the pinned columns.  That column identification is the residue
`ConstantsProvenance` itself exhibits as undischarged
(`ConstantsProvenance.residue_columns_share_bound_cell`,
`bound_cell_agreement_is_not_column_equality`), so this structure is supplied by
the caller here, exactly as that module leaves it.

`manySelectors` is `1 < c.numSelectors`, which is the condition under which the
adopted `Gates.unused_selector_zero_filter` applies; it is implied by nothing
here and is carried as a field. -/
structure SelectorRowIsPlonky2 (c : Gates.Config) (gates : List Gates.GateInfo)
    (t : GateSuffixPolynomial.Tables) (row : Nat) (active : Gates.GateInfo) : Prop where
  /-- The active gate is one of the decoded gates. -/
  activeMem : active ∈ gates
  /-- Its own group's selector column holds its row index inside the group. -/
  activeSelector : rowSelectorAt t row active.selectorIndex = Gates.embed active.gateRowIndex
  /-- Every gate sharing the active gate's selector column declares a group that
  contains the active gate's row index. -/
  sameGroupRange : ∀ g ∈ gates, g.selectorIndex = active.selectorIndex →
    g.groupStart ≤ active.gateRowIndex ∧ active.gateRowIndex < g.groupEnd
  /-- Distinct gates of one group sit at distinct row indices. -/
  distinctRows : ∀ g ∈ gates, g.selectorIndex = active.selectorIndex → g ≠ active →
    g.gateRowIndex ≠ active.gateRowIndex
  /-- Every other group's column holds the UNUSED marker at this row. -/
  otherGroupsUnused : ∀ g ∈ gates, g.selectorIndex ≠ active.selectorIndex →
    rowSelectorAt t row g.selectorIndex = Gates.embed 4294967295
  /-- More than one selector column, the regime `unused_selector_zero_filter`
  covers. -/
  manySelectors : 1 < c.numSelectors

/-- **UNIQUE SELECTION, PROVED.**  Under plonky2's selector construction at a
row, every gate other than the active one has a VANISHING filter there.  Both
branches are adopted lemmas of `Gates`; nothing is assumed about the field beyond
them. -/
theorem unique_selection_of_plonky2_selector_row (c : Gates.Config)
    (gates : List Gates.GateInfo) (t : GateSuffixPolynomial.Tables) (row : Nat)
    (active : Gates.GateInfo) (hsel : SelectorRowIsPlonky2 c gates t row active) :
    ∀ g ∈ gates, g ≠ active → GateRejectionPower.rowFilter c g t row = Verifier.zero := by
  intro g hg hne
  rw [row_filter_via_row_selector]
  by_cases hidx : g.selectorIndex = active.selectorIndex
  · rw [hidx, hsel.activeSelector]
    exact Gates.other_row_zero_filter g active.gateRowIndex _
      (hsel.sameGroupRange g hg hidx).1 (hsel.sameGroupRange g hg hidx).2
      (fun hcontra => hsel.distinctRows g hg hidx hne hcontra.symm)
  · rw [hsel.otherGroupsUnused g hg hidx]
    have hmany : decide (1 < c.numSelectors) = true := by
      simpa using hsel.manySelectors
    rw [hmany]
    exact Gates.unused_selector_zero_filter g

/-! ### §1a. SATISFIABILITY OF `SelectorRowIsPlonky2`

The vacuity policy demands the hypothesis be inhabitable.  It is, at an explicit
three-gate two-group fixture below.  **THIS IS NOT EVIDENCE ABOUT THE DEPLOYED
CIRCUIT'S SELECTOR COLUMNS**; it establishes only that §1's hypothesis is
satisfiable, so `unique_selection_of_plonky2_selector_row` is not vacuous. -/

/-- A two-selector configuration. -/
def fixtureConfig : Gates.Config := ⟨2, 2, 1, 1, 1⟩

/-- Group `0` holds two gates, at group rows `0` and `1`; group `1` holds one. -/
def fixtureGateA : Gates.GateInfo := ⟨0, 0, 0, 2, 0, 0, 0, 0, 0⟩
/-- The other gate of group `0`. -/
def fixtureGateB : Gates.GateInfo := ⟨0, 0, 0, 2, 1, 0, 0, 0, 0⟩
/-- The single gate of group `1`. -/
def fixtureGateC : Gates.GateInfo := ⟨0, 1, 0, 1, 0, 0, 0, 0, 0⟩

/-- The three decoded gates. -/
def fixtureGates : List Gates.GateInfo := [fixtureGateA, fixtureGateB, fixtureGateC]

/-- The constants columns of one Boolean row: group `0` selects its row `0`,
group `1` carries the UNUSED marker. -/
def fixtureTables : GateSuffixPolynomial.Tables :=
  ⟨[], [[⟨Gates.embed 0⟩], [⟨Gates.embed 4294967295⟩]], []⟩

/-- **THE FIXTURE INHABITS `SelectorRowIsPlonky2`.** -/
theorem fixture_selector_row_is_plonky2 :
    SelectorRowIsPlonky2 fixtureConfig fixtureGates fixtureTables 0 fixtureGateA where
  activeMem := by simp [fixtureGates]
  activeSelector := rfl
  sameGroupRange := by
    intro g hg _
    fin_cases hg <;> exact ⟨by decide, by decide⟩
  distinctRows := by
    intro g hg hidx hne
    fin_cases hg
    · exact absurd rfl hne
    · decide
    · exact absurd hidx (by decide)
  otherGroupsUnused := by
    intro g hg hidx
    fin_cases hg
    · exact absurd rfl hidx
    · exact absurd rfl hidx
    · rfl
  manySelectors := by decide

/-- At the fixture, unique selection really eliminates the other two gates. -/
theorem fixture_other_gates_have_zero_filter :
    ∀ g ∈ fixtureGates, g ≠ fixtureGateA →
      GateRejectionPower.rowFilter fixtureConfig g fixtureTables 0 = Verifier.zero :=
  unique_selection_of_plonky2_selector_row fixtureConfig fixtureGates fixtureTables 0
    fixtureGateA fixture_selector_row_is_plonky2

/-- The fixture list also inhabits the `Nodup` hypothesis §2 carries. -/
theorem fixture_gates_nodup : fixtureGates.Nodup := by decide

/-- **THE SELECTION HYPOTHESIS IS INHABITABLE TOO.**  At the fixture the active
gate's own filter is NONZERO, so the `rowFilter … ≠ 0` hypothesis of §2 and §4 is
not an empty one.  (It is carried as a hypothesis in those theorems because it is
the DEFINITION of "this gate is selected at this row", not because it is
unreachable.) -/
theorem fixture_active_filter_nonzero :
    GateRejectionPower.rowFilter fixtureConfig fixtureGateA fixtureTables 0 ≠ Verifier.zero := by
  decide

/-! ## §2. WHOLE-CIRCUIT PACKAGING

`SoundnessAssembly.explicit_good_draw_assembly` is stated at `pre ++ gate :: post`.
`AssemblyResidue`, `outerBadEvent` and the index hypothesis take the gate list as
ONE argument, so instantiating them at `gates` and splitting `gates` for each
member is a pure `List` rewrite: **one** residue and **one** draw hypothesis serve
every gate of the list at once.  That is what §2 records. -/

/-- **EVERY GATE, NOT ONE.**  Under the SAME acceptance, the SAME
`AssemblyResidue` at the decoded list `gates`, and the SAME two draw hypotheses,
the adopted good-draw conclusion holds at EVERY gate of `gates` and every Boolean
row at which that gate is the selected one.

The hypothesis list is byte-for-byte the adopted theorem's, with `pre ++ gate ::
post` replaced by `gates`; no hypothesis is duplicated per gate. -/
theorem selected_gate_terms_vanish (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (gates : List Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState)
    (xg : GoldilocksExt3Field.Element) (cells : GateTerminalBinding.Cells)
    (logTruths gateTruths : List (List GoldilocksExt3Field.Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List GoldilocksExt3Field.Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List GoldilocksExt3Field.Element))
    (hacc : Integrated.verify (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin chain
      c p = .ok ())
    (H : SoundnessAssembly.AssemblyResidue gdec hash thash khash P c₀ pin c p wq gates s0 sLast
      xg cells gateTruths coeffsOf cellIndex cols)
    (hdraw : SoundnessAssembly.actualDigestDraw thash c p ∉ SoundnessAssembly.outerBadEvent thash
      (SoundnessAssembly.engine gdec hash thash khash P c₀) c p gates s0 logTruths gateTruths t pr
      coeffsOf)
    (hidx : SoundnessAssembly.actualIndexDraw thash c p ∉ SoundnessAssembly.indexBadEvent
      c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
        cellIndex).1)
      (IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
          cellIndex))))
    (hnodup : gates.Nodup) :
    ∀ row, row < 2 ^ c.degreeBits → ∀ gate ∈ gates,
      (∀ g ∈ gates, g ≠ gate →
        GateRejectionPower.rowFilter (Integrated.gateConfig c) g s0.tables row = Verifier.zero) →
      GateRejectionPower.rowFilter (Integrated.gateConfig c) gate s0.tables row ≠ Verifier.zero →
      ∃ terms, GatesComplete.evaluateUnfiltered gate (AlphaZeroCheck.rowWires s0.tables row)
          (AlphaZeroCheck.rowConstants s0.tables row)
          (GateTerminalBinding.publicHashFunction
            ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash
              p.publicInputs))
          (Integrated.gateConfig c).numSelectors = some terms ∧
        ∀ y ∈ terms, y = Verifier.zero := by
  intro row hrow gate hgate hothers hactive
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hgate
  subst hsplit
  obtain ⟨-, hcons, hdisj⟩ := List.nodup_append.mp hnodup
  have hnotpre : gate ∉ pre := fun hm => hdisj hm (List.mem_cons_self _ _)
  have hnotpost : gate ∉ post := (List.nodup_cons.mp hcons).1
  refine (SoundnessAssembly.explicit_good_draw_assembly gdec hash thash khash P c₀ pin chain c p
    wq pre post gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols hacc H
    hdraw hidx).1 row hrow ?_ ?_ hactive
  · exact fun g hg => hothers g (by simp [hg]) (fun hcontra => hnotpre (hcontra ▸ hg))
  · exact fun g hg => hothers g (by simp [hg]) (fun hcontra => hnotpost (hcontra ▸ hg))

/-- **§2 COMPOSED WITH §1.**  The caller no longer supplies "the other gates
vanish"; it supplies plonky2's selector construction at the row, and §1 produces
the vanishing.  Everything else is unchanged. -/
theorem selected_gate_terms_vanish_under_plonky2_selectors (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams) (gates : List Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : GoldilocksExt3Field.Element)
    (cells : GateTerminalBinding.Cells)
    (logTruths gateTruths : List (List GoldilocksExt3Field.Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List GoldilocksExt3Field.Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List GoldilocksExt3Field.Element))
    (hacc : Integrated.verify (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin chain
      c p = .ok ())
    (H : SoundnessAssembly.AssemblyResidue gdec hash thash khash P c₀ pin c p wq gates s0 sLast
      xg cells gateTruths coeffsOf cellIndex cols)
    (hdraw : SoundnessAssembly.actualDigestDraw thash c p ∉ SoundnessAssembly.outerBadEvent thash
      (SoundnessAssembly.engine gdec hash thash khash P c₀) c p gates s0 logTruths gateTruths t pr
      coeffsOf)
    (hidx : SoundnessAssembly.actualIndexDraw thash c p ∉ SoundnessAssembly.indexBadEvent
      c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
        cellIndex).1)
      (IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
          cellIndex))))
    (hnodup : gates.Nodup) :
    ∀ row, row < 2 ^ c.degreeBits → ∀ active,
      SelectorRowIsPlonky2 (Integrated.gateConfig c) gates s0.tables row active →
      GateRejectionPower.rowFilter (Integrated.gateConfig c) active s0.tables row ≠ Verifier.zero →
      ∃ terms, GatesComplete.evaluateUnfiltered active (AlphaZeroCheck.rowWires s0.tables row)
          (AlphaZeroCheck.rowConstants s0.tables row)
          (GateTerminalBinding.publicHashFunction
            ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash
              p.publicInputs))
          (Integrated.gateConfig c).numSelectors = some terms ∧
        ∀ y ∈ terms, y = Verifier.zero := by
  intro row hrow active hplonky hnz
  exact selected_gate_terms_vanish gdec hash thash khash P c₀ pin chain c p wq gates s0 sLast xg
    cells logTruths gateTruths t pr coeffsOf cellIndex cols hacc H hdraw hidx hnodup row hrow
    active hplonky.activeMem
    (unique_selection_of_plonky2_selector_row (Integrated.gateConfig c) gates s0.tables row active
      hplonky) hnz

/-! ## §3. SEMANTICS: FROM THE DISPATCHER'S TERMS TO THE REAL FORMULAS -/

/-- The row widths the semantic bridge needs, read off the adopted
`GateDenseRound.Consistent` field of `AssemblyResidue`. -/
theorem row_widths_of_consistent (c : Gates.Config) (s : GateTerminalBinding.ProverState)
    (hc : GateDenseRound.Consistent c s) (row : Nat) :
    (AlphaZeroCheck.rowWires s.tables row).length = c.numWires ∧
      (AlphaZeroCheck.rowConstants s.tables row).length = c.numConstants := by
  refine ⟨?_, ?_⟩
  · rw [AlphaZeroCheck.rowWires_length]
    simpa [GateTerminalBinding.ProverState.tables, GateSlotRound.tablesOf] using hc.1.1
  · rw [AlphaZeroCheck.rowConstants_length]
    simpa [GateTerminalBinding.ProverState.tables, GateSlotRound.tablesOf] using hc.1.2.1

/-- A configured gate of a validated configuration passes `Gates.validateGate`.
Membership form of `Gates.every_configured_gate_checked`. -/
theorem validate_gate_of_mem (c : Gates.Config) (gates : List Gates.GateInfo)
    (hv : Gates.validateConfiguration c gates = some ()) (g : Gates.GateInfo) (hg : g ∈ gates) :
    ∃ i r, Gates.validateGate c i gates.length g = some r := by
  obtain ⟨n, hn⟩ := List.get_of_mem hg
  obtain ⟨r, hr, -⟩ := Gates.every_configured_gate_checked c gates hv n.val g
    (by rw [List.get?_eq_get n.isLt]; exact congrArg some hn)
  exact ⟨n.val, r, hr⟩

/-- `numSelectors ≤ numConstants` is part of the adopted configuration envelope. -/
theorem selectors_within_constants (c : Gates.Config) (gates : List Gates.GateInfo)
    (hv : Gates.validateConfiguration c gates = some ()) : c.numSelectors ≤ c.numConstants :=
  (Gates.validate_configuration_success c gates hv).1.2.2.2.2.1

/-- **THE SEMANTIC BRIDGE, ONE GATE.**  A vanishing family of dispatcher terms at
a configured gate and configured widths is a vanishing family of terms of the
SHAPE-CHECKED PER-FAMILY EVALUATOR `GateEvaluatorCoverage.evaluateGateFull`,
whose fourteen branches ARE the per-family formulas.  This is the point at which
"the dispatcher returned zeros" becomes "the gate's own relation holds". -/
theorem evaluate_gate_full_terms_vanish (c : Gates.Config) (gates : List Gates.GateInfo)
    (g : Gates.GateInfo) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (terms : List Verifier.Ext3)
    (hv : Gates.validateConfiguration c gates = some ()) (hg : g ∈ gates)
    (hw : wires.length = c.numWires) (hcst : constants.length = c.numConstants)
    (hterms : GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors
      = some terms) :
    GateEvaluatorCoverage.evaluateGateFull c g wires constants publicHash = some terms := by
  obtain ⟨i, r, hr⟩ := validate_gate_of_mem c gates hv g hg
  rw [GateEvaluatorCoverage.validated_full_evaluator_agrees c i gates.length g r wires constants
    publicHash hr (selectors_within_constants c gates hv) hw hcst]
  exact hterms

/-! ### §3a. FOUR FAMILIES, UNFOLDED INTO THEIR FIELD EQUATIONS

Ids `0`, `1`, `2`, `3`.  Every other family keeps the `evaluateGateFull` form of
§3, which is that family's transcribed formula; the caveat of
`GateEvaluatorCoverage` — the transcriptions are cited to the audited Rust and
are not verified against Plonky2's own gate implementations — is inherited
verbatim for all fourteen. -/

/-- Id `0`, `NoopGate`: the family emits no constraints at all. -/
theorem noop_gate_semantics (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants terms : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (hid : g.gateId = 0)
    (hfull : GateEvaluatorCoverage.evaluateGateFull c g wires constants publicHash = some terms) :
    terms = [] := by
  rw [GateEvaluatorCoverage.evaluateGateFull, hid] at hfull
  exact (GateEvaluatorCoverage.guarded_output c g wires constants [] terms hfull)

/-- Id `1`, `ConstantGate`: **the real relation.**  Each declared constant of the
row equals the corresponding wire. -/
theorem constant_gate_semantics (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants terms : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (hid : g.gateId = 1)
    (hfull : GateEvaluatorCoverage.evaluateGateFull c g wires constants publicHash = some terms)
    (hzero : ∀ y ∈ terms, y = Verifier.zero) :
    ∀ i < g.numOrConsts,
      Gates.readValue constants (c.numSelectors + i) = Gates.readValue wires i := by
  rw [GateEvaluatorCoverage.evaluateGateFull, hid] at hfull
  have hterms := GateEvaluatorCoverage.guarded_output c g wires constants _ terms hfull
  intro i hi
  refine (Algebra.vsub_eq_zero_iff _ _).mp (hzero _ ?_)
  rw [hterms]
  refine List.mem_map.mpr ⟨i, ?_, rfl⟩
  exact (Gates.range_membership _ _).mpr hi

/-- Id `2`, `PublicInputGate`: **the real relation.**  The first four wires of the
row are the four limbs of the public-input hash. -/
theorem public_input_gate_semantics (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants terms : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (hid : g.gateId = 2)
    (hfull : GateEvaluatorCoverage.evaluateGateFull c g wires constants publicHash = some terms)
    (hzero : ∀ y ∈ terms, y = Verifier.zero) :
    ∀ i < 4, Gates.readValue wires i = Gates.embed (publicHash i).val := by
  rw [GateEvaluatorCoverage.evaluateGateFull, hid] at hfull
  have hterms := GateEvaluatorCoverage.guarded_output c g wires constants _ terms hfull
  intro i hi
  refine (Algebra.vsub_eq_zero_iff _ _).mp (hzero _ ?_)
  rw [hterms]
  refine List.mem_map.mpr ⟨i, ?_, rfl⟩
  exact (Gates.range_membership _ _).mpr hi

/-- Id `3`, `ArithmeticGate`: **the real relation.**  For each of the
`numOrConsts` operations the four-wire slot satisfies the gate's arithmetic
constraint at the row's two local constants. -/
theorem arithmetic_gate_semantics (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants terms : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (hid : g.gateId = 3)
    (hfull : GateEvaluatorCoverage.evaluateGateFull c g wires constants publicHash = some terms)
    (hzero : ∀ y ∈ terms, y = Verifier.zero) :
    ∀ i < g.numOrConsts,
      Gates.arithmeticConstraint (Gates.readValue constants c.numSelectors)
        (Gates.readValue constants (c.numSelectors + 1)) (Gates.readValue wires (4 * i))
        (Gates.readValue wires (4 * i + 1)) (Gates.readValue wires (4 * i + 2))
        (Gates.readValue wires (4 * i + 3)) = Verifier.zero := by
  rw [GateEvaluatorCoverage.evaluateGateFull, hid] at hfull
  have hterms := GateEvaluatorCoverage.guarded_output c g wires constants _ terms hfull
  intro i hi
  refine hzero _ ?_
  rw [hterms]
  refine List.mem_map.mpr ⟨i, ?_, rfl⟩
  exact (Gates.range_membership _ _).mpr hi

/-! ## §4. THE CONDITIONAL CIRCUIT-TRUTH SENTENCE -/

/-- **THE SENTENCE.**

Under

1. `hacc` — the accepted Solidity-route call at the pinned-proof engine;
2. `H` — the adopted `SoundnessAssembly.AssemblyResidue` at the decoded gate list
   `gates`, taken AT THE EXTRACTED STATE OF THE RUN `r` (its `s0` argument is the
   bridge's own `ExtractorConstruction.extractedState` at `runOpening r`);
3. `hdraw`, `hidx` — the two good-draw hypotheses of the adopted theorem, at that
   same state;
4. `hdec` — `R1bBridge.WhirDecodeUniqueness`, the named, cited, never-proven WHIR
   decode assumption;

the EXTRACTED tables of the accepted run `r`

* satisfy, at EVERY Boolean row and for the gate plonky2's selector construction
  selects at that row, the SELECTED GATE'S OWN PER-FAMILY FORMULA, every
  constraint term vanishing; **and**
* are PAIRWISE RUN-INDEPENDENT under the per-pair ROM binding event: for EVERY
  second accepted group run `rp` of the SAME root at the SAME query indices whose
  executed compression inputs are collision-free against `r`'s
  (`R1bBridge.RunPairNoCollision r rp`), the extracted tables of `rp` are the
  SAME tables — or `R1bBridge.OpenedLeafCollision hash` names two rows the two
  runs actually opened, the one priced localized event, which
  `R1bBridge.bridge_leaf_disjunct_is_priced` and
  `bridge_leaf_disjunct_is_priced_at_the_bounded_queries` carry.

**WHY THIS SHAPE AND NOT THE OLD ONE.**  The previous form of this theorem
carried the conjunct `∃ tablesOf, CommitmentOrder.CommittedTables tablesOf s t`.
That structure has only two fields, both of the form "`t` equals `tablesOf _ _`",
so the existential is provable WITH NO HYPOTHESES AT ALL by the constant map
(`committed_tables_existential_is_a_tautology`, §5), and the whole old conclusion
is derivable with the entire `R1bBridge` chain deleted
(`the_former_conclusion_shape_holds_without_the_bridge`, §5).  It recorded the
bridge's SHAPE, not any fact about the commitment.  The pairwise conjunct above
is the bridge's REAL content — `R1bBridge.extract_agrees_on_the_two_runs`, which
consumes `hdec` and the per-pair ROM event — and "the commitment determines the
tables" means exactly this run-independence, computationally.

**THE PER-PAIR SCOPE IS DELIBERATE.**  The uniform alternative — ONE `tablesOf`
for every run via `R1bBridge.root_determined_of_pairwise_no_collision` — costs
`∀ r, RunPairNoCollision r r₀`, and that family is REFUTED at this tree's only
non-degenerate fixture (`the_uniform_no_collision_family_fails_at_the_depth_one_fixture`,
§5), exactly as the ∀-field of `R1bBridge` §7 was.  So it is not shipped.

## ASSUMPTION LEDGER, EVERY ITEM

* **UNPROVED AND ASSUMED HERE:** `hdec` (WHIR decode uniqueness — assumed, cited
  to the WHIR literature at the deployed parameters, proven nowhere in this
  tree); the per-pair ROM event `R1bBridge.RunPairNoCollision r rp`, which is now
  an ANTECEDENT inside the conclusion rather than a hypothesis (`R1bBridge` §7
  records that the ∀-quantified variant is FALSE at that module's own depth-one
  fixture, so the per-pair form is the only one taken, and §5 here records that
  the same refutation kills the uniform family); every undischarged field of
  `AssemblyResidue` as that structure's own field docstrings record them
  (the profile table's canonicity, the canonical row, the deployment digest, the
  two byte-length bounds, R1b at the fold level, the extracted column height and
  committed width, the gate-list pinning, the extracted state's consistency, the
  extracted truth chain, positivity of `numGateConstraints`, the cells join, the
  eq-table provenance and cell binding, the active filter, the slot
  coefficients); `hnodup` (an ADDED DEPLOYMENT ASSUMPTION — §5, item 12);
  `hplonky` per row (plonky2's selector construction at that row —
  §1, with its `ConstantsProvenance` provenance and that module's own
  undischarged column identification); `hnz` per row (that the named gate IS
  selected there).
* **HYPOTHESIS, NOT EXHIBIT — AND NEVER JOINTLY INHABITED:** `hacc`.  No
  `AssemblyResidue` INSTANCE has ever been exhibited in this tree; the nearest is
  `ExtractorConstruction` §8 (`:733-745`), which discharges 10 of the 19 fields
  and leaves the two keccak fields, the four deployment/ABI fields, `gatesDecode`,
  `gateConstraintsPositive`, `activeFilter` and the fold-level R1b field assumed.
  `SoundnessAssembly.lean:749-752` states outright that nothing in this tree shows
  `hacc` and `AssemblyResidue` can hold TOGETHER.  Therefore `{hacc, H, hdraw,
  hidx}` have NEVER BEEN JOINTLY INHABITED, and that is this sentence's DEEPEST
  CONDITIONAL LAYER: the whole theorem could in principle be vacuous at the
  explicit engine, and nothing here excludes it.  The one positive on that side is
  `SoundnessAssembly`'s own non-vacuity block for `hdraw` (`hdraw` is SATISFIED BY
  EVERY HONEST EXTRACTION, since `outerBadEvent` is empty on honest extraction
  data); that block itself says it is NOT joint satisfiability.  Separately, §1a
  inhabits `SelectorRowIsPlonky2` and `hnz`, `fixture_gates_nodup` inhabits
  `hnodup`, and `R1bBridge.whir_decode_uniqueness_is_satisfiable` inhabits `hdec`.
* **NOT CLAIMED:** that the columns are the ones the ROOT NAMES (the bridge's
  `tablesOf` route is root-blind); that the deployed system is sound; that an
  accepted proof implies the statement is true.  See §5 of the module docstring
  and `REPORT.md` for the remaining ledger. -/
theorem extracted_tables_satisfy_the_selected_gate_constraints_and_are_pairwise_run_independent
    (hash : Spongefish.Hash) (root : Spongefish.Digest) (depth : Nat)
    (layout : WhirRows.Layout) (indices : List Nat) (gdec : Integrated.DecodeGates)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List GoldilocksExt3Field.Element))
    (roots : List Spongefish.Digest)
    (hdec : R1bBridge.WhirDecodeUniqueness hash root depth layout indices extract roots)
    (r : R1bBridge.Run hash root depth layout indices)
    (wq : SoundnessAssembly.VkParams) (gates : List Gates.GateInfo)
    (sLast : GateTerminalBinding.ProverState) (xg : GoldilocksExt3Field.Element)
    (cells : GateTerminalBinding.Cells)
    (logTruths gateTruths : List (List GoldilocksExt3Field.Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List GoldilocksExt3Field.Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List GoldilocksExt3Field.Element))
    (hacc : Integrated.verify (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin chain
      c p = .ok ())
    (H : SoundnessAssembly.AssemblyResidue gdec hash thash khash P c₀ pin c p wq gates
      (ExtractorConstruction.extractedState thash c p extract roots (R1bBridge.runOpening r))
      sLast xg cells gateTruths coeffsOf cellIndex cols)
    (hdraw : SoundnessAssembly.actualDigestDraw thash c p ∉ SoundnessAssembly.outerBadEvent thash
      (SoundnessAssembly.engine gdec hash thash khash P c₀) c p gates
      (ExtractorConstruction.extractedState thash c p extract roots (R1bBridge.runOpening r))
      logTruths gateTruths t pr coeffsOf)
    (hidx : SoundnessAssembly.actualIndexDraw thash c p ∉ SoundnessAssembly.indexBadEvent
      c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
        cellIndex).1)
      (IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
          cellIndex))))
    (hnodup : gates.Nodup) :
    (∀ rp : R1bBridge.Run hash root depth layout indices,
        R1bBridge.RunPairNoCollision r rp →
        (ExtractorConstruction.extractedState thash c p extract roots
            (R1bBridge.runOpening rp)).tables
          = (ExtractorConstruction.extractedState thash c p extract roots
            (R1bBridge.runOpening r)).tables ∨
        R1bBridge.OpenedLeafCollision hash (R1bBridge.runOpening r)
          (R1bBridge.runOpening rp)) ∧
        ∀ row, row < 2 ^ c.degreeBits → ∀ active,
          SelectorRowIsPlonky2 (Integrated.gateConfig c) gates
            (ExtractorConstruction.extractedState thash c p extract roots
              (R1bBridge.runOpening r)).tables row active →
          GateRejectionPower.rowFilter (Integrated.gateConfig c) active
            (ExtractorConstruction.extractedState thash c p extract roots
              (R1bBridge.runOpening r)).tables row ≠ Verifier.zero →
          ∃ terms, GateEvaluatorCoverage.evaluateGateFull (Integrated.gateConfig c) active
              (AlphaZeroCheck.rowWires (ExtractorConstruction.extractedState thash c p extract
                roots (R1bBridge.runOpening r)).tables row)
              (AlphaZeroCheck.rowConstants (ExtractorConstruction.extractedState thash c p extract
                roots (R1bBridge.runOpening r)).tables row)
              (GateTerminalBinding.publicHashFunction
                ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash
                  p.publicInputs)) = some terms ∧
            ∀ y ∈ terms, y = Verifier.zero := by
  refine ⟨?_, ?_⟩
  · intro rp hnc
    rcases R1bBridge.extract_agrees_on_the_two_runs hash root depth layout indices extract roots
      hdec r rp hnc with hag | hcol
    · exact Or.inl (congrArg GateTerminalBinding.ProverState.tables
        (R1bBridge.extracted_state_congr_of_extract thash c p extract roots
          (R1bBridge.runOpening rp) (R1bBridge.runOpening r) hag.symm))
    · exact Or.inr hcol
  · intro row hrow active hplonky hnz
    obtain ⟨terms, hterms, hzero⟩ :=
      selected_gate_terms_vanish_under_plonky2_selectors gdec hash thash khash P c₀ pin chain c p
        wq gates _ sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols hacc H hdraw
        hidx hnodup row hrow active hplonky hnz
    have hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some () :=
      GateClaimChain.accepted_gate_configuration_valid
        (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin chain c p gates hacc
        H.gatesDecode
    have hwidth := row_widths_of_consistent (Integrated.gateConfig c) _ H.extractedStateConsistent
      row
    exact ⟨terms, evaluate_gate_full_terms_vanish (Integrated.gateConfig c) gates active _ _ _
      terms hv hplonky.activeMem hwidth.1 hwidth.2 hterms, hzero⟩

/-! ## §5. THE HONEST NEGATIVES

The tree's practice is to keep refuted and empty shapes as RECORDED THEOREMS.
These five are the adversarial review's own counter-probes, adopted verbatim in
content. -/

/-- **THE OLD COMMITTED-TABLES CONJUNCT WAS AN UNCONDITIONAL TAUTOLOGY.**
`CommitmentOrder.CommittedTables` has exactly two fields, `t.wires =
(tablesOf _ _).wires` and `t.constants = (tablesOf _ _).constants`, so the
existential over `tablesOf` is discharged by the CONSTANT map for ANY statement
and ANY table pair, with no hypothesis at all.  Wherever that shape survives — in
`R1bBridge.r1b_clause_of_the_two_runs`'s own left disjunct, and in the previous
form of §4 — it records the bridge's SHAPE, NOT ANY FACT ABOUT THE COMMITMENT,
and the content of the sentence carrying it lies entirely elsewhere. -/
theorem committed_tables_existential_is_a_tautology (s : Verifier.Statement)
    (t : GateSuffixPolynomial.Tables) :
    ∃ tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables,
      CommitmentOrder.CommittedTables tablesOf s t :=
  ⟨fun _ _ => t, rfl, rfl⟩

/-- **THE FORMER CONCLUSION SHAPE NEEDS NO BRIDGE AT ALL.**  The exact conclusion
the previous headline carried — committed-tables conjunct included — is derivable
at an ARBITRARY prover state `s0`, with `hdec`, the per-pair ROM event, both runs
and the WHOLE `R1bBridge` chain ABSENT.  Only `hacc`, `H`, `hdraw`, `hidx` and
`hnodup` are used.  This is why §4 was restated: the old form bought nothing over
`selected_gate_terms_vanish_under_plonky2_selectors` plus §3. -/
theorem the_former_conclusion_shape_holds_without_the_bridge (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams) (gates : List Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : GoldilocksExt3Field.Element)
    (cells : GateTerminalBinding.Cells)
    (logTruths gateTruths : List (List GoldilocksExt3Field.Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List GoldilocksExt3Field.Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List GoldilocksExt3Field.Element))
    (hacc : Integrated.verify (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin chain
      c p = .ok ())
    (H : SoundnessAssembly.AssemblyResidue gdec hash thash khash P c₀ pin c p wq gates s0 sLast
      xg cells gateTruths coeffsOf cellIndex cols)
    (hdraw : SoundnessAssembly.actualDigestDraw thash c p ∉ SoundnessAssembly.outerBadEvent thash
      (SoundnessAssembly.engine gdec hash thash khash P c₀) c p gates s0 logTruths gateTruths t pr
      coeffsOf)
    (hidx : SoundnessAssembly.actualIndexDraw thash c p ∉ SoundnessAssembly.indexBadEvent
      c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
        cellIndex).1)
      (IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
          cellIndex))))
    (hnodup : gates.Nodup) :
    ∃ tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables,
      CommitmentOrder.CommittedTables tablesOf (Verifier.statement p) s0.tables ∧
      ∀ row, row < 2 ^ c.degreeBits → ∀ active,
        SelectorRowIsPlonky2 (Integrated.gateConfig c) gates s0.tables row active →
        GateRejectionPower.rowFilter (Integrated.gateConfig c) active s0.tables row
            ≠ Verifier.zero →
        ∃ terms, GateEvaluatorCoverage.evaluateGateFull (Integrated.gateConfig c) active
            (AlphaZeroCheck.rowWires s0.tables row)
            (AlphaZeroCheck.rowConstants s0.tables row)
            (GateTerminalBinding.publicHashFunction
              ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash
                p.publicInputs)) = some terms ∧
          ∀ y ∈ terms, y = Verifier.zero := by
  obtain ⟨tablesOf, hct⟩ :=
    committed_tables_existential_is_a_tautology (Verifier.statement p) s0.tables
  refine ⟨tablesOf, hct, ?_⟩
  intro row hrow active hplonky hnz
  obtain ⟨terms, hterms, hzero⟩ :=
    selected_gate_terms_vanish_under_plonky2_selectors gdec hash thash khash P c₀ pin chain c p
      wq gates s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols hacc H hdraw
      hidx hnodup row hrow active hplonky hnz
  have hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some () :=
    GateClaimChain.accepted_gate_configuration_valid
      (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin chain c p gates hacc
      H.gatesDecode
  have hwidth := row_widths_of_consistent (Integrated.gateConfig c) _ H.extractedStateConsistent row
  exact ⟨terms, evaluate_gate_full_terms_vanish (Integrated.gateConfig c) gates active _ _ _
    terms hv hplonky.activeMem hwidth.1 hwidth.2 hterms, hzero⟩

/-- **THE UNIFORM `tablesOf` IS NOT AVAILABLE.**  `R1bBridge.root_determined_of_pairwise_no_collision`
would give ONE `tablesOf` for every run of the commitment, at the price of the
FAMILY `∀ r, RunPairNoCollision r r₀`.  Instantiating that family at the tree's
depth-one fixture pair reproduces exactly the per-pair statement `R1bBridge` §7
REFUTES, so the family is false at every hash that collides there — the same
pigeonhole failure that killed the ∀-field of the earlier draft.  Hence the
uniform option was checked and NOT shipped; §4 is the per-pair form. -/
theorem the_uniform_no_collision_family_fails_at_the_depth_one_fixture :
    ¬ ∀ r : R1bBridge.Run WhirRows.exampleHash R1bBridge.depthOneRoot 1 ⟨.base, 1⟩ [1],
        R1bBridge.RunPairNoCollision r R1bBridge.depthOneRunB := fun h =>
  R1bBridge.run_pair_no_collision_fails_at_the_depth_one_fixture (h R1bBridge.depthOneRunA)

/-! ### §5a. `Nodup` IS A GENUINE ADDED ASSUMPTION

A DUPLICATED gate list satisfies every OTHER hypothesis §2 and §4 impose at the
row — all five fields of `SelectorRowIsPlonky2`, whose `distinctRows` field is
VACUOUS on a duplicate (`g ≠ active` is false when `g` IS `active`), and the
nonzero active filter — while failing `Nodup`.  So `distinctRows` does not
subsume the duplicate case, and nothing else here implies `Nodup`. -/

/-- The same gate twice. -/
def duplicatedGates : List Gates.GateInfo := [fixtureGateA, fixtureGateA]

/-- Every field of §1's structure holds on the duplicated list. -/
theorem duplicated_gates_selector_row_is_plonky2 :
    SelectorRowIsPlonky2 fixtureConfig duplicatedGates fixtureTables 0 fixtureGateA where
  activeMem := by simp [duplicatedGates]
  activeSelector := rfl
  sameGroupRange := by intro g hg _; fin_cases hg <;> exact ⟨by decide, by decide⟩
  distinctRows := by intro g hg _ hne; fin_cases hg <;> exact absurd rfl hne
  otherGroupsUnused := by intro g hg hidx; fin_cases hg <;> exact absurd rfl hidx
  manySelectors := by decide

/-- And the selection hypothesis holds there too. -/
theorem duplicated_gates_active_filter_nonzero :
    GateRejectionPower.rowFilter fixtureConfig fixtureGateA fixtureTables 0 ≠ Verifier.zero := by
  decide

/-- Yet `Nodup` fails: the added hypothesis is not implied by the others. -/
theorem duplicated_gates_are_not_nodup : ¬ duplicatedGates.Nodup := by decide

/-! ### §5b. `manySelectors` EARNS ITS KEEP

At a ONE-selector configuration every other field of `SelectorRowIsPlonky2` still
holds at the same tables, yet the other group's gate has a NONZERO filter.  So
`unique_selection_of_plonky2_selector_row` is not smuggled: the fifth field is
load-bearing and the conclusion is not an artefact of the structure alone. -/

/-- One selector column only. -/
def singleSelectorConfig : Gates.Config := ⟨1, 2, 1, 1, 1⟩

/-- Two gates in two groups, at that configuration. -/
def singleSelectorGates : List Gates.GateInfo := [fixtureGateA, fixtureGateC]

/-- The other group still carries the UNUSED marker. -/
theorem single_selector_other_group_unused :
    ∀ g ∈ singleSelectorGates, g.selectorIndex ≠ fixtureGateA.selectorIndex →
      rowSelectorAt fixtureTables 0 g.selectorIndex = Gates.embed 4294967295 := by
  intro g hg hidx
  fin_cases hg
  · exact absurd rfl hidx
  · rfl

/-- **AND UNIQUE SELECTION FAILS THERE.**  A gate other than the active one keeps
a NONZERO filter once `1 < numSelectors` is dropped. -/
theorem single_selector_unique_selection_fails :
    fixtureGateC ∈ singleSelectorGates ∧ fixtureGateC ≠ fixtureGateA ∧
      GateRejectionPower.rowFilter singleSelectorConfig fixtureGateC fixtureTables 0
        ≠ Verifier.zero :=
  ⟨by simp [singleSelectorGates], by decide, by decide⟩

end Audit.Wire3.CircuitTruth
