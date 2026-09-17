import Audit.Wire3.CommittedTablesClauses
import Audit.Wire3.LocalizedCollisionMasses

/-!
# Audit.Wire3.R1bBridge -- R1b as a BRIDGE from a named, PER-PAIR WHIR assumption

## HONESTY HEADER

R1b (`InstalledWhirTail.TailExtractsCommittedTables`; equivalently the
`rootDetermined` clause of `CommitmentOrderSurvey.CommittedTablesJoin`, which
`CommittedTablesClauses` §3 identifies as R1b) is the one hypothesis the ROM line
carries as inherited and unexhibited.  **THIS MODULE DOES NOT PROVE IT.**  It
builds the bridge the audit actually wants:

> for any two ACCEPTED group runs of one commitment whose EXECUTED compression
> inputs are collision-free under the hash -- the per-execution binding event,
> the shape the computational assumption actually prices -- together with an
> explicitly named DECODE-UNIQUENESS assumption `WhirDecodeUniqueness`,
> JUSTIFIED BY THE WHIR LITERATURE AT THE DEPLOYED PARAMETERS, **ASSUMED HERE AND
> NEVER PROVEN**, the `rootDetermined` clause the adopted line consumes holds --
> up to a collision disjunct that lands on the ADOPTED localized predicate
> `LocalizedCollisions.LeafCollision`, in the shape `LocalizedCollisionMasses`
> prices at `1 / |Block|` per named pair.

Nothing below asserts that WHIR is binding.  `WhirDecodeUniqueness` is a Lean
structure used only as a HYPOTHESIS; it is never an `axiom`, never an `instance`,
and every theorem that consumes it, or the per-pair no-collision hypothesis,
carries it visibly in its statement.

## WHY THE ASSUMPTION IS PER-PAIR: A REFUTED EARLIER SHAPE

An earlier draft of this module put the no-collision requirement INSIDE the
assumption structure, quantified over all index lists, hint buffers and sponge
states at a fixed hash/root/depth/layout.  **THAT SHAPE IS FALSE**, and §7 proves
it false at this tree's own depth-one fixture: `Merkle.exampleHash` is
`take 32`, and at the odd index `1` the compression input is `sibling ++ current`,
so the depth-one root does not depend on the leaf at all; a second row opens
against the same root (`other_base_row_opens_at_the_depth_one_root`), and the two
runs' executed compression inputs are two distinct 64-byte strings with equal
hash (`merkle_no_collision_for_all_executions_fails_at_depth_one`).  The
quantified form is an information-theoretic injectivity postulate, not the
per-execution computational one; the per-pair form used here is the computational
event, and it too is refuted AT THAT PARTICULAR PAIR -- as it should be, since
that fixture's commitment really is not binding.

## The shape of the bridge, and why it is the only available one

`CommittedTablesClauses` §3 fixes the geometry:

* `root_determined_clause_has_no_tables_map_for_the_reading_extractor` (:512):
  at the adopted opening-READING extractor NO `tablesOf` satisfies the clause at
  two different openings.  So any bridge must land on an extractor whose output
  at fixed roots does not move with the opening.
* `root_determined_of_opening_free_extractor` (:426): and for such an extractor a
  `tablesOf` exists.  Root-determination IS opening-independence.
* `opened_cells_root_determined_or_collision` (:555): the adopted binding lemmas
  already deliver opening-independence OF THE OPENED CELLS, up to a
  `LocalizedCollisions.LeafCollision` on the two named rows, given
  `OpeningBinding.NoCollision` over the two executions' executed Merkle inputs.

So the gap is not the opened cells; it is (a) closing the per-cell agreement into
agreement of the whole opened row list, and (b) transporting that agreement
through the extractor's decoding step to its COLUMNS.  Section 3 PROVES (a) from
the per-pair no-collision hypothesis; `WhirDecodeUniqueness` assumes only (b),
and only at RUNS.

## What this module does NOT claim

It does not claim that the columns are the ones the roots NAME -- the adopted
`CommitmentOrderSurvey.opening_relation_is_root_blind` records that the model has
no predicate for that at all, and the bridge inherits that scope verbatim.  It
does not claim acceptance is exhibited at the explicit engine, nor anything about
circuit truth, nor that the WHIR execution witnesses leave their toy scope.  It
makes no statement about `AdaptiveAssemblyFailure` or `IndexHalfTransport`, and
nothing here speaks about more than ONE commitment root at a time.
-/

namespace Audit.Wire3.R1bBridge

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The run: one executed WHIR group opening -/

/-- The opened row BYTES of an opening, group by group.  This is the data the
adopted binding lemmas speak about (`opened_cells_root_determined_or_collision`
concludes `row.bytes = otherRow.bytes`), and it is the interface between the
binding side and the decoding side of the bridge. -/
def rowBytesOf (o : WhirIntermediate.Opening) : List (List Spongefish.Bytes) :=
  o.groups.map (fun g => g.map (fun row : WhirRows.RawRow => row.bytes))

/-- An opening is OPENED BY A GROUP RUN at `(root, depth, layout, indices)` when
its single group is literally the output of an accepted `WhirRows.openGroup`
call against that root at those query indices.  The hint buffer and the ambient
sponge state are existentially quantified HERE, which is why this predicate alone
cannot carry the ROM hypothesis: see `Run`. -/
def OpenedByGroupRun (hash : Spongefish.Hash) (root : Spongefish.Digest) (depth : Nat)
    (layout : WhirRows.Layout) (indices : List Nat) (o : WhirIntermediate.Opening) : Prop :=
  o.indices = indices ∧
    ∃ (hints : Spongefish.Bytes) (s t : Spongefish.State) (rows : List WhirRows.RawRow),
      WhirRows.openGroup hash root depth indices layout hints s = some (rows, t) ∧
      o.groups = [rows]

/-- **A RUN WITH ITS HINT BUFFER AND START STATE EXPOSED.**  `OpenedByGroupRun`
hides them existentially, and that hiding is exactly what forced the refuted
∀-quantified no-collision field: to state the ROM hypothesis AT THE TWO
EXECUTIONS UNDER COMPARISON the executions must be named.  `Run` names them. -/
structure Run (hash : Spongefish.Hash) (root : Spongefish.Digest) (depth : Nat)
    (layout : WhirRows.Layout) (indices : List Nat) where
  hints : Spongefish.Bytes
  start : Spongefish.State
  final : Spongefish.State
  rows : List WhirRows.RawRow
  run : WhirRows.openGroup hash root depth indices layout hints start = some (rows, final)

/-- The opening a run produces. -/
def runOpening {hash : Spongefish.Hash} {root : Spongefish.Digest} {depth : Nat}
    {layout : WhirRows.Layout} {indices : List Nat}
    (r : Run hash root depth layout indices) : WhirIntermediate.Opening :=
  ⟨indices, [r.rows]⟩

/-- The byte strings a run actually compresses. -/
def runExecutedInputs {hash : Spongefish.Hash} {root : Spongefish.Digest} {depth : Nat}
    {layout : WhirRows.Layout} {indices : List Nat}
    (r : Run hash root depth layout indices) : List Spongefish.Bytes :=
  OpenedDotBinding.executedMerkleInputs hash root depth indices layout r.hints r.start

/-- **THE PER-PAIR ROM HYPOTHESIS.**  Injectivity of `hash` restricted to the
byte strings THESE TWO EXECUTIONS hash -- the per-execution binding event, the
one a computational collision-resistance assumption actually prices.  It is NOT
an unquantified collision-resistance postulate, and it is NOT the ∀-form §7
refutes. -/
def RunPairNoCollision {hash : Spongefish.Hash} {root : Spongefish.Digest} {depth : Nat}
    {layout : WhirRows.Layout} {indices : List Nat}
    (r1 r2 : Run hash root depth layout indices) : Prop :=
  OpeningBinding.NoCollision hash (runExecutedInputs r1 ++ runExecutedInputs r2)

/-- A run's opening is an `OpenedByGroupRun`: `Run` is a refinement, not a
different class of executions. -/
theorem run_is_group_run {hash : Spongefish.Hash} {root : Spongefish.Digest} {depth : Nat}
    {layout : WhirRows.Layout} {indices : List Nat} (r : Run hash root depth layout indices) :
    OpenedByGroupRun hash root depth layout indices (runOpening r) :=
  ⟨rfl, r.hints, r.start, r.final, r.rows, r.run, rfl⟩

/-- And conversely every `OpenedByGroupRun` opening IS a run's opening, so the
rescoping loses no openings: it only exposes the data the ROM hypothesis needs. -/
theorem run_of_opened_by_group_run (hash : Spongefish.Hash) (root : Spongefish.Digest)
    (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (o : WhirIntermediate.Opening) (h : OpenedByGroupRun hash root depth layout indices o) :
    ∃ r : Run hash root depth layout indices, runOpening r = o := by
  obtain ⟨hi, hints, s, t, rows, hrun, hg⟩ := h
  refine ⟨⟨hints, s, t, rows, hrun⟩, ?_⟩
  cases o
  simp only [runOpening] at *
  rw [hi, hg]

/-- The localized failure disjunct of the bridge: a
`LocalizedCollisions.LeafCollision` **on two rows the two runs actually opened**.
Both byte strings are named and drawn from the runs' own opened data, so the
predicate is refutable and `LocalizedCollisionMasses.leaf_collision_mass_le`
prices it in that shape; it is not the unlocalized "some collision exists
somewhere". -/
def OpenedLeafCollision (hash : Spongefish.Hash) (o1 o2 : WhirIntermediate.Opening) : Prop :=
  ∃ a b : Spongefish.Bytes, LocalizedCollisions.LeafCollision hash a b ∧
    (∃ g ∈ rowBytesOf o1, a ∈ g) ∧ (∃ g ∈ rowBytesOf o2, b ∈ g)

/-- The localized disjunct names two DISTINCT byte strings, so it is refutable --
the lesson of `LocalizedCollisions.khash_collision_is_a_tautology` applied here. -/
theorem opened_leaf_collision_names_distinct_rows (hash : Spongefish.Hash)
    (o1 o2 : WhirIntermediate.Opening) (h : OpenedLeafCollision hash o1 o2) :
    ∃ a b : Spongefish.Bytes, a ≠ b ∧ hash a = hash b := by
  obtain ⟨a, b, hc, _, _⟩ := h
  exact ⟨a, b, hc.1, hc.2⟩

/-- An opening cannot be a group run at two different index lists. -/
theorem opened_by_group_run_indices (hash : Spongefish.Hash) (root : Spongefish.Digest)
    (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (o : WhirIntermediate.Opening) (h : OpenedByGroupRun hash root depth layout indices o) :
    o.indices = indices := h.1

/-! ## 2. THE ASSUMPTION -/

/-- **THE WHIR DECODE-UNIQUENESS ASSUMPTION, STATED ONCE AND NAMED.**

This is the decoding half of PCS binding as the WHIR literature proves it for the
deployed parameters: the opened leaves of the committed Reed--Solomon codeword
determine the decoded (folded) columns.  **IT IS ASSUMED HERE, CITED TO THAT
LITERATURE, AND NEVER PROVEN ANYWHERE IN THIS TREE.**  It is carried as a Lean
structure so that it appears in the statement of every theorem that uses it; it
is not a Lean `axiom`, so `#print axioms` on those theorems shows only the ambient
three, and the reader must supply this hypothesis by hand to obtain any
conclusion below.

The ROM half is NOT a field here.  It is a PER-PAIR HYPOTHESIS of each bridge
theorem, `RunPairNoCollision`, at the two runs being compared -- see the honesty
header and §7 for why the quantified field shape was abandoned.

The single field is quantified over RUNS, not over all openings: the bridge only
ever applies it at runs, and the all-openings form is strictly stronger than any
use made of it.

Note what is NOT assumed: root-determination of the columns is not a field.  It
is the CONCLUSION, proved in section 4; and §7 keeps the demonstration that this
field alone does NOT deliver it. -/
structure WhirDecodeUniqueness (hash : Spongefish.Hash) (root : Spongefish.Digest) (depth : Nat)
    (layout : WhirRows.Layout) (indices : List Nat)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) : Prop where
  /-- Unique decoding: the extracted columns at `roots` depend on a RUN's opening
  only through its opened row bytes.  Assumed; justified by the WHIR literature
  at the deployed parameters. -/
  rowsDetermineColumns : ∀ r1 r2 : Run hash root depth layout indices,
    rowBytesOf (runOpening r1) = rowBytesOf (runOpening r2) →
      extract roots (runOpening r1) = extract roots (runOpening r2)

/-! ### 2a. SATISFIABILITY: DEGENERATE-BY-EMPTINESS AT DEPTH ZERO

The vacuity policy demands the interface be inhabitable.  It is, and the witness
is **DEGENERATE BY EMPTINESS AT DEPTH ZERO**: a depth-zero tree performs no
Merkle compression, so the executed input list is empty and the per-pair
`RunPairNoCollision` holds by emptiness (the same route the adopted
`CommittedTablesClauses.executed_merkle_inputs_empty_at_depth_zero` takes); and
the constant extractor decodes nothing, so unique decoding is `rfl`.  **THIS
WITNESS IS NOT EVIDENCE THAT WHIR IS BINDING.**  It establishes only that the
hypotheses are satisfiable, so that the bridge theorems of sections 3-5 are not
vacuously true.  §7 proves that at `Merkle.exampleHash` NO depth ≥ 1 witness of
the per-pair hypothesis exists at the fixture pair, and states what a real
witness would need. -/

/-- At depth zero a group opening compresses nothing, whether or not it succeeds. -/
theorem executed_merkle_inputs_empty_at_depth_zero (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (indices : List Nat) (layout : WhirRows.Layout)
    (hints : Spongefish.Bytes) (s : Spongefish.State) :
    OpenedDotBinding.executedMerkleInputs hash root 0 indices layout hints s = [] := by
  unfold OpenedDotBinding.executedMerkleInputs
  cases WhirRows.openGroup hash root 0 indices layout hints s with
  | none => rfl
  | some pair => rfl

/-- The degenerate extractor: no columns at all, at every root list and opening. -/
def trivialExtract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
    List (List Element) := fun _ _ _ => []

/-- **THE PER-PAIR ROM HYPOTHESIS IS INHABITABLE, DEGENERATELY, AT DEPTH ZERO.**
Every pair of depth-zero runs satisfies it, by emptiness of the executed input
list -- at an arbitrary hash, root, layout and index list.  Read the scope
exactly: this is a satisfiability check, not a binding claim. -/
theorem run_pair_no_collision_at_depth_zero (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (layout : WhirRows.Layout) (indices : List Nat)
    (r1 r2 : Run hash root 0 layout indices) : RunPairNoCollision r1 r2 := by
  unfold RunPairNoCollision runExecutedInputs
  rw [executed_merkle_inputs_empty_at_depth_zero, executed_merkle_inputs_empty_at_depth_zero]
  exact LocalizedCollisions.no_collision_holds_on_the_empty_list hash

/-- **THE DECODE-UNIQUENESS ASSUMPTION IS INHABITABLE.**  The constant extractor
satisfies it at an arbitrary hash, root, depth, layout, index list and root list.
Again: a satisfiability check of the interface, not a binding claim. -/
theorem whir_decode_uniqueness_is_satisfiable (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (roots : List Spongefish.Digest) :
    WhirDecodeUniqueness hash root depth layout indices trivialExtract roots :=
  ⟨fun _ _ _ => rfl⟩

/-- **AND THE RUN PREDICATE IS INHABITED AT THE SAME DEPTH**, so the bridge
theorems below are not conditioned on an empty class of runs: the adopted
`WhirRows.base_row_open_example` fixture is a group run. -/
theorem base_row_fixture_is_a_group_run :
    OpenedByGroupRun WhirRows.exampleHash WhirRows.exampleBaseRoot 0 ⟨.base, 1⟩ [0]
      ⟨[0], [[WhirRows.exampleBaseRow]]⟩ :=
  ⟨rfl, WhirRows.exampleBaseHints, WhirRows.exampleStart,
    {WhirRows.exampleStart with hintPos := 16}, [WhirRows.exampleBaseRow],
    WhirRows.base_row_open_example, rfl⟩

/-! ## 3. From the per-pair ROM hypothesis to agreement of the whole opened row list

This section is PROVED, not assumed: it closes the adopted per-cell statement
`opened_cells_root_determined_or_collision` into agreement of the two runs'
entire opened row lists.  The step that makes it work is
`WhirRows.group_success_contiguous_rows`, which pins `rows.length` to
`indices.length`, so two runs at the SAME query indices return row lists of the
same length and can be compared position by position. -/

/-- One position of two group runs at the same indices: the rows agree, or the
adopted localized leaf collision holds on exactly those two rows.  A direct
instance of `CommittedTablesClauses.opened_cells_root_determined_or_collision`. -/
theorem opened_row_agrees_or_leaf_collision (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (hints otherHints : Spongefish.Bytes) (s t otherS otherT : Spongefish.State)
    (rows otherRows : List WhirRows.RawRow)
    (hnc : OpeningBinding.NoCollision hash
      (OpenedDotBinding.executedMerkleInputs hash root depth indices layout hints s ++
        OpenedDotBinding.executedMerkleInputs hash root depth indices layout otherHints otherS))
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h2 : WhirRows.openGroup hash root depth indices layout otherHints otherS
      = some (otherRows, otherT))
    (k : Nat) (hk : k < indices.length)
    (hk1 : k < rows.length) (hk2 : k < otherRows.length) :
    rows[k].bytes = otherRows[k].bytes ∨
      LocalizedCollisions.LeafCollision hash rows[k].bytes otherRows[k].bytes := by
  have hm : (indices[k], rows[k]) ∈ indices.zip rows := by
    have hlt : k < (indices.zip rows).length := by
      rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hk, hk1⟩
    have := List.getElem_mem _ _ hlt
    rwa [List.getElem_zip] at this
  have hm2 : (indices[k], otherRows[k]) ∈ indices.zip otherRows := by
    have hlt : k < (indices.zip otherRows).length := by
      rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hk, hk2⟩
    have := List.getElem_mem _ _ hlt
    rwa [List.getElem_zip] at this
  exact CommittedTablesClauses.opened_cells_root_determined_or_collision hash root depth
    indices[k] indices indices layout hints otherHints s t otherS otherT rows otherRows
    rows[k] otherRows[k] hnc h h2 hm hm2

/-- **THE WHOLE OPENED ROW LIST IS ROOT-DETERMINED, UP TO ONE LOCALIZED LEAF
COLLISION.**  Two accepted runs of the same commitment root at the same query
indices, WHOSE OWN EXECUTED COMPRESSION INPUTS ARE COLLISION-FREE, open the SAME
row bytes -- or `OpenedLeafCollision` names two rows they actually opened on
which `hash` collides.

No assumption structure is used: the only hypothesis is the per-pair ROM event at
these two executions.  This is the list-level closure of the adopted per-cell
lemma, and it is where the gap the adopted tree records (the opened cells are
covered, their JOIN is not) is closed. -/
theorem opened_rows_determined_of_pairwise_no_collision (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (r1 r2 : Run hash root depth layout indices) (hnc : RunPairNoCollision r1 r2) :
    rowBytesOf (runOpening r1) = rowBytesOf (runOpening r2) ∨
      OpenedLeafCollision hash (runOpening r1) (runOpening r2) := by
  simp only [RunPairNoCollision, runExecutedInputs] at hnc
  obtain ⟨hints, s, t, rows, hrun⟩ := r1
  obtain ⟨otherHints, otherS, otherT, otherRows, hrun2⟩ := r2
  have hlen1 : rows.length = indices.length :=
    (WhirRows.group_success_contiguous_rows hash root depth indices layout hints s t rows hrun).1
  have hlen2 : otherRows.length = indices.length :=
    (WhirRows.group_success_contiguous_rows hash root depth indices layout otherHints otherS
      otherT otherRows hrun2).1
  by_cases heq : rows.map (fun r : WhirRows.RawRow => r.bytes)
      = otherRows.map (fun r : WhirRows.RawRow => r.bytes)
  · left
    simp only [runOpening, rowBytesOf, List.map_cons, List.map_nil, heq]
  · right
    have hmaplen : (rows.map (fun r : WhirRows.RawRow => r.bytes)).length
        = (otherRows.map (fun r : WhirRows.RawRow => r.bytes)).length := by
      rw [List.length_map, List.length_map, hlen1, hlen2]
    have hex : ∃ k, ∃ hk1 : k < rows.length, ∃ hk2 : k < otherRows.length,
        rows[k].bytes ≠ otherRows[k].bytes := by
      by_contra hcon
      push_neg at hcon
      refine heq (List.ext_getElem hmaplen ?_)
      intro k hka hkb
      rw [List.length_map] at hka hkb
      rw [List.getElem_map, List.getElem_map]
      exact hcon k hka hkb
    obtain ⟨k, hk1, hk2, hne⟩ := hex
    have hk : k < indices.length := hlen1 ▸ hk1
    rcases opened_row_agrees_or_leaf_collision hash root depth layout indices hints otherHints
      s t otherS otherT rows otherRows hnc hrun hrun2 k hk hk1 hk2 with hag | hcol
    · exact absurd hag hne
    · refine ⟨rows[k].bytes, otherRows[k].bytes, hcol, ?_, ?_⟩
      · exact ⟨rows.map (fun r : WhirRows.RawRow => r.bytes), List.mem_singleton_self _,
          List.mem_map_of_mem _ (List.getElem_mem _ _ hk1)⟩
      · exact ⟨otherRows.map (fun r : WhirRows.RawRow => r.bytes), List.mem_singleton_self _,
          List.mem_map_of_mem _ (List.getElem_mem _ _ hk2)⟩

/-- **THE EXTRACTOR AGREES ON THE TWO RUNS**, up to the same localized leaf
collision.  The per-pair ROM hypothesis and the decode-uniqueness assumption are
both used here, and this is exactly the property
`CommittedTablesClauses.root_determined_of_opening_free_extractor` (:426)
identifies as equivalent to root-determination -- but only AT THE TWO RUNS. -/
theorem extract_agrees_on_the_two_runs (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest)
    (hdec : WhirDecodeUniqueness hash root depth layout indices extract roots)
    (r1 r2 : Run hash root depth layout indices) (hnc : RunPairNoCollision r1 r2) :
    extract roots (runOpening r1) = extract roots (runOpening r2) ∨
      OpenedLeafCollision hash (runOpening r1) (runOpening r2) := by
  rcases opened_rows_determined_of_pairwise_no_collision hash root depth layout indices r1 r2 hnc
    with hrows | hcol
  · exact Or.inl (hdec.rowsDetermineColumns r1 r2 hrows)
  · exact Or.inr hcol

/-! ## 4. THE BRIDGE THEOREM -/

/-- The extracted prover state depends on the opening only through the extractor's
output at that opening -- a `congrArg` on
`ExtractorConstruction.extractedState`'s definition. -/
theorem extracted_state_congr_of_extract (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (o1 o2 : WhirIntermediate.Opening)
    (h : extract roots o1 = extract roots o2) :
    ExtractorConstruction.extractedState thash c p extract roots o1
      = ExtractorConstruction.extractedState thash c p extract roots o2 := by
  unfold ExtractorConstruction.extractedState
  rw [h]

/-- From extractor agreement with a reference opening, the `rootDetermined` clause
holds at the OPENING-FREE `tablesOf` that ignores both root arguments -- the
adopted route of `root_determined_of_opening_free_extractor`. -/
theorem committed_tables_of_extract_agreement (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (o o₀ : WhirIntermediate.Opening)
    (h : extract roots o = extract roots o₀) :
    CommitmentOrder.CommittedTables
      (fun _ _ => (ExtractorConstruction.extractedState thash c p extract roots o₀).tables)
      (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract roots o).tables :=
  ⟨congrArg (fun s => (GateTerminalBinding.ProverState.tables s).wires)
      (extracted_state_congr_of_extract thash c p extract roots o o₀ h),
    congrArg (fun s => (GateTerminalBinding.ProverState.tables s).constants)
      (extracted_state_congr_of_extract thash c p extract roots o o₀ h)⟩

/-- **THE BRIDGE, AT ONE PAIR OF RUNS**, in exactly the shape
`CommittedTablesClauses.committed_tables_join_up_to_collisions` consumes its
`hr1b` hypothesis: one `tablesOf`, one opening.  This is the form section 5
plugs in.

READ THE SCOPE EXACTLY.

* The exhibited `tablesOf` ignores its two root arguments, exactly as the adopted
  `root_determined_of_opening_free_extractor` does.  This says root-determination
  is AVAILABLE; it does NOT say the columns are the ones the roots NAME, for
  which the model has no predicate at all
  (`CommitmentOrderSurvey.opening_relation_is_root_blind`).
* The hypotheses are at TWO NAMED ACCEPTED RUNS of ONE root: an opening that is
  not the output of an accepted `openGroup` call is outside every binding
  argument, and nothing here speaks about a second commitment root.
* The right disjunct is `OpenedLeafCollision`, which names two byte strings the
  runs opened; §6 records exactly what is and is not established about pricing
  it. -/
theorem r1b_clause_of_the_two_runs (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest)
    (hdec : WhirDecodeUniqueness hash root depth layout indices extract roots)
    (r r₀ : Run hash root depth layout indices) (hnc : RunPairNoCollision r r₀) :
    (∃ tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables,
        CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
          (ExtractorConstruction.extractedState thash c p extract roots (runOpening r)).tables) ∨
      OpenedLeafCollision hash (runOpening r) (runOpening r₀) := by
  rcases extract_agrees_on_the_two_runs hash root depth layout indices extract roots hdec r r₀ hnc
    with hag | hcol
  · exact Or.inl ⟨_, committed_tables_of_extract_agreement thash c p extract roots
      (runOpening r) (runOpening r₀) hag⟩
  · exact Or.inr hcol

/-- **THE BRIDGE, UNIFORMLY OVER THE RUNS OF ONE COMMITMENT.**  The uniform
`tablesOf` costs exactly what it should: the per-pair ROM hypothesis taken at
EVERY run paired with the reference run.  That is a family of per-execution
events, one per accepted run -- not the refuted ∀-form over all hint buffers at a
fixed root, which is an information-theoretic injectivity postulate. -/
theorem root_determined_of_pairwise_no_collision (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest)
    (hdec : WhirDecodeUniqueness hash root depth layout indices extract roots)
    (r₀ : Run hash root depth layout indices)
    (hnc : ∀ r : Run hash root depth layout indices, RunPairNoCollision r r₀) :
    (∃ tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables,
        ∀ r : Run hash root depth layout indices,
          CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
            (ExtractorConstruction.extractedState thash c p extract roots (runOpening r)).tables) ∨
      ∃ r : Run hash root depth layout indices,
        OpenedLeafCollision hash (runOpening r) (runOpening r₀) := by
  by_cases hall : ∀ r : Run hash root depth layout indices,
      extract roots (runOpening r) = extract roots (runOpening r₀)
  · exact Or.inl ⟨_, fun r => committed_tables_of_extract_agreement thash c p extract roots
      (runOpening r) (runOpening r₀) (hall r)⟩
  · right
    push_neg at hall
    obtain ⟨r, hne⟩ := hall
    rcases extract_agrees_on_the_two_runs hash root depth layout indices extract roots hdec r r₀
      (hnc r) with hag | hcol
    · exact absurd hag hne
    · exact ⟨r, hcol⟩

/-! ## 5. THE CONSUMPTION COROLLARY -/

/-- **THE HEADLINE.**  For any two accepted group runs of one commitment whose
executed compression inputs are collision-free under the hash, and under the named
decode-uniqueness assumption, the audit's committed-tables residue reduces on an
accepted Solidity call to localized collision events:
`CommitmentOrderSurvey.CommittedTablesJoin` holds at some `tablesOf` -- or
`LocalizedCollisions.ConfigEncodingCollision khash c c₀` holds, or
`OpenedLeafCollision hash` names two rows the two runs actually opened.

The two unproved inputs are exactly the per-pair ROM hypothesis and
`WhirDecodeUniqueness`: clauses 1 and 2 come from acceptance
(`committed_tables_join_up_to_collisions`), and clause 3 -- R1b -- comes from
section 4.

WHAT THIS DOES NOT DO.  It does not exhibit acceptance at the explicit engine, it
says nothing about circuit truth, and it does not make the zero-check table `g`
fixed data (that remains a function of a squeezed challenge; the diagonal
argument is `EngineTauDiagonal`'s).  And it does not prove WHIR binding: read the
hypotheses. -/
theorem committed_tables_join_of_the_two_runs (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (gdec : Integrated.DecodeGates) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest)
    (hdec : WhirDecodeUniqueness hash root depth layout indices extract roots)
    (r r₀ : Run hash root depth layout indices) (hnc : RunPairNoCollision r r₀)
    (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    (∃ tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables,
        CommitmentOrderSurvey.CommittedTablesJoin tablesOf thash c c₀ pin extract p roots
          (runOpening r)) ∨
      LocalizedCollisions.ConfigEncodingCollision khash c c₀ ∨
      OpenedLeafCollision hash (runOpening r) (runOpening r₀) := by
  rcases r1b_clause_of_the_two_runs hash root depth layout indices thash c p extract roots hdec
    r r₀ hnc with ⟨tablesOf, hr1b⟩ | hcol
  · rcases CommittedTablesClauses.committed_tables_join_up_to_collisions tablesOf gdec hash thash
      khash P c₀ pin chain c p extract roots (runOpening r) hd hg hw hacc hr1b with hjoin | hccol
    · exact Or.inl ⟨tablesOf, hjoin⟩
    · exact Or.inr (Or.inl hccol)
  · exact Or.inr (Or.inr hcol)

/-- **THE TAU-TABLE SENTENCE, REACHED.**  The sentence the ROM modules repeat --
"the zero-check table's TABLE argument is fixed data" -- holds for two group runs
of the same commitment at different round-one openings, under the two runs' own
per-pair ROM hypotheses against a reference run plus decode uniqueness, up to the
one localized leaf event.  No acceptance, no `DeployedFacts`, no word bounds, no
`khash` and NO CONFIGURATION-ENCODING COLLISION appear: exactly as the adopted
`CommittedTablesClauses.tau_table_is_fixed_data_from_r1b_at_the_two_runs_alone`
records, only the two R1b hypotheses are load-bearing, and section 4 supplies
both from ONE `tablesOf`. -/
theorem tau_table_is_fixed_data_of_the_two_runs (hash : Spongefish.Hash)
    (root : Spongefish.Digest) (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest)
    (hdec : WhirDecodeUniqueness hash root depth layout indices extract roots)
    (r₀ r1 r2 : Run hash root depth layout indices)
    (hnc1 : RunPairNoCollision r1 r₀) (hnc2 : RunPairNoCollision r2 r₀) :
    CommitmentOrderSurvey.prefixTauTable thash c gates publicHash (Verifier.statement p)
        (ExtractorConstruction.extractedState thash c p extract roots (runOpening r1)).tables
      = CommitmentOrderSurvey.prefixTauTable thash c gates publicHash (Verifier.statement p)
        (ExtractorConstruction.extractedState thash c p extract roots (runOpening r2)).tables ∨
      OpenedLeafCollision hash (runOpening r1) (runOpening r₀) ∨
      OpenedLeafCollision hash (runOpening r2) (runOpening r₀) := by
  rcases extract_agrees_on_the_two_runs hash root depth layout indices extract roots hdec r1 r₀
    hnc1 with hag1 | hcol1
  · rcases extract_agrees_on_the_two_runs hash root depth layout indices extract roots hdec r2 r₀
      hnc2 with hag2 | hcol2
    · exact Or.inl (CommittedTablesClauses.tau_table_is_fixed_data_from_r1b_at_the_two_runs_alone
        (fun _ _ => (ExtractorConstruction.extractedState thash c p extract roots
          (runOpening r₀)).tables)
        thash c p gates publicHash extract roots roots (runOpening r1) (runOpening r2)
        (committed_tables_of_extract_agreement thash c p extract roots (runOpening r1)
          (runOpening r₀) hag1)
        (committed_tables_of_extract_agreement thash c p extract roots (runOpening r2)
          (runOpening r₀) hag2))
    · exact Or.inr (Or.inr hcol2)
  · exact Or.inr (Or.inl hcol1)

/-! ## 6. The localized disjunct and the adopted price -- WHAT IS AND IS NOT ESTABLISHED

The bridge's failure disjunct is `LocalizedCollisions.LeafCollision` on two named
byte strings, which is the SHAPE the adopted `LocalizedCollisionMasses` masses
price.  **THE FULL PLUMBING IS NOT ESTABLISHED IN GENERAL.**  Two gaps, named:

* HASH IDENTIFICATION.  `LocalizedCollisionMasses.leafCollisionEvent` filters on
  `LocalizedCollisions.LeafCollision (leafHashOf Q T) …` -- the SAMPLED ORACLE
  TABLE's hash -- whereas the bridge's `OpenedLeafCollision hash` is at whatever
  `hash` the theorem is instantiated at.  Because `hash` is a PARAMETER of every
  bridge theorem above, an instantiation at `leafHashOf Q T` is legitimate, and
  the theorem below takes exactly that instantiation.  Nothing identifies the
  DEPLOYED Lean hash with any sampled table's hash, and no adopted lemma gives
  that.
* QUERY MEMBERSHIP.  The masses need the named row to lie in the query set `Q`.
  At the adopted `BirthdayClashBound.boundedQueries L` this follows from a LENGTH
  BOUND on the opened rows, which is supplied below as a HYPOTHESIS (the route
  with precedent in `LocalizedCollisionMasses.rows_subset_bounded_queries`).
  Nothing here proves the deployed rows satisfy it.

So: at the bounded query set, and at a table's own hash, the bridge's disjunct
does carry the adopted `1 / |Block|` per-pair price; outside those two
identifications it is the SHAPE, not a quantified error term for the deployed
system. -/

/-- The adopted per-pair bound, restated at the module's names: for any two named
opened rows in the query set, the ROM mass of the leaf collision is at most
`1 / |Block|`.  At the SAMPLED TABLE's hash, not at any fixed Lean function. -/
theorem bridge_leaf_disjunct_is_priced (Q : Finset Transcript.Bytes)
    (row other : Spongefish.Bytes) (hmem : row ∈ Q ∨ other ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q
        (LocalizedCollisionMasses.leafCollisionEvent Q row other)
      ≤ 1 / (Fintype.card LocalizedCollisionMasses.Block : ℚ) :=
  LocalizedCollisionMasses.leaf_collision_mass_le Q row other hmem

/-- **THE PLUMBING, WHERE IT LANDS.**  Instantiate the bridge at a sampled table's
own leaf hash and at the adopted bounded query set; assume a LENGTH BOUND on the
first run's opened rows.  Then the bridge's disjunct exhibits a NAMED pair whose
adopted ROM mass is at most `1 / |Block|`.  This is the whole of what is
established: the hash is the table's, and the membership comes from the assumed
length bound. -/
theorem bridge_leaf_disjunct_is_priced_at_the_bounded_queries (L : Nat)
    (T : LocalizedCollisionMasses.OracleTable (BirthdayClashBound.boundedQueries L))
    (o1 o2 : WhirIntermediate.Opening)
    (hlen : ∀ g ∈ rowBytesOf o1, ∀ x ∈ g, x.length ≤ L)
    (hcol : OpenedLeafCollision
      (LocalizedCollisionMasses.leafHashOf (BirthdayClashBound.boundedQueries L) T) o1 o2) :
    ∃ a b : Spongefish.Bytes,
      LocalizedCollisions.LeafCollision
        (LocalizedCollisionMasses.leafHashOf (BirthdayClashBound.boundedQueries L) T) a b ∧
      RandomOracleSqueezes.oracleProbability (BirthdayClashBound.boundedQueries L)
          (LocalizedCollisionMasses.leafCollisionEvent
            (BirthdayClashBound.boundedQueries L) a b)
        ≤ 1 / (Fintype.card LocalizedCollisionMasses.Block : ℚ) := by
  obtain ⟨a, b, hc, ⟨g, hg, ha⟩, -⟩ := hcol
  have hmem : a ∈ BirthdayClashBound.boundedQueries L :=
    (BirthdayClashBound.mem_bounded_queries L a).mpr (hlen g hg a ha)
  exact ⟨a, b, hc, LocalizedCollisionMasses.leaf_collision_mass_le _ a b (Or.inl hmem)⟩

/-- The configuration-encoding disjunct that survives in the consumption
corollary carries the same adopted per-pair price, with the same two caveats
(sampled hash, query membership -- here the membership is the adopted
`configQuery` hypothesis). -/
theorem bridge_config_disjunct_is_priced (Q : Finset Transcript.Bytes)
    (c c₀ : Verifier.Config) (hmem : LocalizedCollisionMasses.configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q
        (LocalizedCollisionMasses.configCollisionEvent Q c c₀)
      ≤ 1 / (Fintype.card LocalizedCollisionMasses.Block : ℚ) :=
  LocalizedCollisionMasses.config_encoding_collision_mass_le Q c c₀ hmem

/-! ## 7. HONEST NEGATIVE RESULTS

Three things are recorded here as THEOREMS rather than prose: (a) the ∀-quantified
no-collision shape an earlier draft used is REFUTED at this tree's own depth-one
fixture, which is WHY the assumption is per-pair; (b) the per-pair hypothesis
itself fails at that fixture pair, so the depth-zero witness is the only one this
hash supplies; (c) the decode-uniqueness field does NOT smuggle in the
conclusion. -/

/-- The adopted depth-one fixture root. -/
def depthOneRoot : Spongefish.Digest :=
  Merkle.parent WhirRows.exampleHash 1 WhirRows.exampleBaseRoot WhirRows.exampleSibling

/-- A second base row, differing from the adopted fixture row only in payload. -/
def otherBaseRow : WhirRows.RawRow := ⟨8, Transcript.le 8 9⟩

/-- The adopted fixture's hint buffer at depth one. -/
def depthOneHintsA : Spongefish.Bytes :=
  WhirRows.exampleBaseHints ++ WhirRows.exampleSibling.val

/-- The second run's hint buffer at depth one. -/
def depthOneHintsB : Spongefish.Bytes :=
  Transcript.le 8 1 ++ otherBaseRow.bytes ++ WhirRows.exampleSibling.val

set_option maxRecDepth 20000 in
/-- The adopted depth-one fixture, restated as a group run. -/
theorem base_row_opens_at_the_depth_one_root :
    WhirRows.openGroup WhirRows.exampleHash depthOneRoot 1 [1] ⟨.base, 1⟩ depthOneHintsA
        WhirRows.exampleStart
      = some ([WhirRows.exampleBaseRow], {WhirRows.exampleStart with hintPos := 48}) :=
  WhirRows.lone_leaf_sibling_cursor_example

set_option maxRecDepth 20000 in
/-- **A DIFFERENT ROW, ACCEPTED AGAINST THE SAME ROOT.**  `Merkle.exampleHash` is
`take 32 (bytes ++ zeros)`, and at the ODD index `1` the compression input is
`sibling ++ current`, so the depth-one root does not depend on the leaf at all:
the fixture commitment is not binding and a second row opens at the same root. -/
theorem other_base_row_opens_at_the_depth_one_root :
    WhirRows.openGroup WhirRows.exampleHash depthOneRoot 1 [1] ⟨.base, 1⟩ depthOneHintsB
        WhirRows.exampleStart
      = some ([otherBaseRow], {WhirRows.exampleStart with hintPos := 48}) := by
  simp [WhirRows.openGroup, Spongefish.consumeVecPrefix, Spongefish.proverHint,
    Spongefish.readSlice, WhirRows.readRows, WhirRows.authenticateRows, WhirRows.rowHashes,
    Merkle.verify, Merkle.runLayers, Merkle.processLayer, Merkle.readDigest, Merkle.ascending,
    depthOneHintsB, otherBaseRow, WhirRows.exampleStart, WhirRows.rowBytes, WhirRows.elementBytes,
    Transcript.le, Transcript.fromLe, WhirRows.exampleSibling, Merkle.exampleDigest,
    Merkle.merged, depthOneRoot, WhirRows.exampleBaseRoot, WhirRows.exampleHash,
    Merkle.exampleHash, Merkle.parent, Merkle.parentInput, WhirRows.exampleBaseRow]
  decide

/-- The two depth-one runs, as `Run`s. -/
def depthOneRunA : Run WhirRows.exampleHash depthOneRoot 1 ⟨.base, 1⟩ [1] :=
  ⟨depthOneHintsA, WhirRows.exampleStart, {WhirRows.exampleStart with hintPos := 48},
    [WhirRows.exampleBaseRow], base_row_opens_at_the_depth_one_root⟩

/-- The second depth-one run. -/
def depthOneRunB : Run WhirRows.exampleHash depthOneRoot 1 ⟨.base, 1⟩ [1] :=
  ⟨depthOneHintsB, WhirRows.exampleStart, {WhirRows.exampleStart with hintPos := 48},
    [otherBaseRow], other_base_row_opens_at_the_depth_one_root⟩

set_option maxRecDepth 100000 in
/-- **THE PER-PAIR HYPOTHESIS IS FALSE AT THE DEPTH-ONE FIXTURE PAIR.**  The two
accepted runs compress `sibling ++ leaf` with DIFFERENT leaves, and both
compressions hash to the SAME root, so `OpeningBinding.NoCollision` over the
appended executed-input lists is refuted outright.  This is not a defect of the
per-pair form: that fixture's commitment genuinely is not binding, and the
hypothesis correctly reports it. -/
theorem run_pair_no_collision_fails_at_the_depth_one_fixture :
    ¬ RunPairNoCollision depthOneRunA depthOneRunB := by
  simp only [RunPairNoCollision, runExecutedInputs, depthOneRunA, depthOneRunB]
  rw [OpenedDotBinding.executedMerkleInputs_success _ _ _ _ _ _ _ _ _
      base_row_opens_at_the_depth_one_root,
    OpenedDotBinding.executedMerkleInputs_success _ _ _ _ _ _ _ _ _
      other_base_row_opens_at_the_depth_one_root]
  intro hnc
  have hmem : ∀ x ∈ ([Merkle.parentInput 1 (WhirRows.exampleHash WhirRows.exampleBaseRow.bytes)
      WhirRows.exampleSibling] : List Spongefish.Bytes) ++
      [Merkle.parentInput 1 (WhirRows.exampleHash otherBaseRow.bytes) WhirRows.exampleSibling],
      x ∈ OpeningBinding.merkleInputs WhirRows.exampleHash depthOneHintsA 1 [1]
          (WhirRows.rowHashes WhirRows.exampleHash [WhirRows.exampleBaseRow])
          (WhirRows.exampleStart.hintPos + 8 + [1].length * WhirRows.rowBytes ⟨.base, 1⟩) ++
        OpeningBinding.merkleInputs WhirRows.exampleHash depthOneHintsB 1 [1]
          (WhirRows.rowHashes WhirRows.exampleHash [otherBaseRow])
          (WhirRows.exampleStart.hintPos + 8 + [1].length * WhirRows.rowBytes ⟨.base, 1⟩) := by
    simp [OpeningBinding.merkleInputs, OpeningBinding.layersInputs, OpeningBinding.layerInputs,
      WhirRows.rowHashes, WhirRows.exampleStart, WhirRows.rowBytes, WhirRows.elementBytes,
      Merkle.processLayer, Merkle.readDigest, Merkle.merged, Merkle.ascending, depthOneHintsA,
      depthOneHintsB, WhirRows.exampleBaseHints, WhirRows.exampleBaseRow, otherBaseRow,
      Transcript.le, WhirRows.exampleSibling, Merkle.exampleDigest, WhirRows.exampleHash,
      Merkle.exampleHash, Merkle.parentInput]
  have hA := hmem (Merkle.parentInput 1 (WhirRows.exampleHash WhirRows.exampleBaseRow.bytes)
    WhirRows.exampleSibling) (by simp)
  have hB := hmem (Merkle.parentInput 1 (WhirRows.exampleHash otherBaseRow.bytes)
    WhirRows.exampleSibling) (by simp)
  have := hnc _ hA _ hB (by decide)
  exact absurd this (by decide)

/-- **THE REFUTED SHAPE**, written out: injectivity of `hash` over ALL accepting
executions at a fixed root/depth/layout -- all index lists, all hint buffers, all
sponge states.  This is an information-theoretic postulate, and it was a FIELD of
an earlier draft's assumption structure. -/
def MerkleNoCollisionAtAllExecutions (hash : Spongefish.Hash) (root : Spongefish.Digest)
    (depth : Nat) (layout : WhirRows.Layout) : Prop :=
  ∀ (i1 i2 : List Nat) (h1 h2 : Spongefish.Bytes) (s1 s2 : Spongefish.State),
    OpeningBinding.NoCollision hash
      (OpenedDotBinding.executedMerkleInputs hash root depth i1 layout h1 s1 ++
        OpenedDotBinding.executedMerkleInputs hash root depth i2 layout h2 s2)

/-- **AND IT IS REFUTED AT THE TREE'S OWN DEPTH-ONE FIXTURE.**  This is the
finding that forced the redesign: the ∀-form is not a stronger version of the
computational assumption, it is a FALSE sentence at the only non-degenerate
fixture this tree has. -/
theorem merkle_no_collision_for_all_executions_fails_at_depth_one :
    ¬ MerkleNoCollisionAtAllExecutions WhirRows.exampleHash depthOneRoot 1 ⟨.base, 1⟩ := by
  intro h
  exact run_pair_no_collision_fails_at_the_depth_one_fixture
    (h [1] [1] depthOneHintsA depthOneHintsB WhirRows.exampleStart WhirRows.exampleStart)

/-- **THE TWO DEPTH-ONE RUNS REALLY DO DISAGREE ON THEIR OPENED ROW BYTES**, so
decode uniqueness alone is powerless at this instance: it is the ROM side that
would have to do the work, and that side is false here.  Confirms the
architecture claim -- the bridge's real content is the ROW-BYTE agreement -- and
simultaneously that the content is unavailable at this depth-one fixture.

WHAT A REAL WITNESS WOULD NEED: a hash injective on the reachable accepting
compression inputs of ONE root at depth ≥ 1.  No toy in this tree supplies one,
and NO ADOPTED LEMMA GIVES ONE.  That is a statement about this tree's fixtures,
not an impossibility claim. -/
theorem the_two_depth_one_runs_open_different_rows :
    rowBytesOf (runOpening depthOneRunA) ≠ rowBytesOf (runOpening depthOneRunB) := by
  simp [runOpening, rowBytesOf, depthOneRunA, depthOneRunB, WhirRows.exampleBaseRow,
    otherBaseRow, Transcript.le]

/-! ### 7a. The decode-uniqueness field is not the conclusion renamed -/

/-- An extractor that reads the opened ROW BYTES (and nothing else). -/
def rowsExtract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
    List (List Element) :=
  fun _ o _ => (rowBytesOf o).map (fun _ => [])

/-- It satisfies the decode-uniqueness field at every instance, by construction. -/
theorem rows_extract_is_decode_unique (hash : Spongefish.Hash) (root : Spongefish.Digest)
    (depth : Nat) (layout : WhirRows.Layout) (indices : List Nat)
    (roots : List Spongefish.Digest) :
    WhirDecodeUniqueness hash root depth layout indices rowsExtract roots :=
  ⟨fun _ _ h => by unfold rowsExtract; rw [h]⟩

/-- **AND IT IS NOT OPENING-FREE.**  So the decode-uniqueness field alone does NOT
deliver the opening-independence that
`CommittedTablesClauses.root_determined_of_opening_free_extractor` turns into the
`rootDetermined` clause: the field is a genuine restriction on the extractor, not
the conclusion renamed. -/
theorem rows_extract_is_not_opening_free :
    ¬ CommittedTablesClauses.OpeningFreeExtractor rowsExtract := by
  intro h
  have := congrFun (h [] ⟨[], []⟩ ⟨[], [[]]⟩) (⟨0, by decide⟩ : Fin 5)
  simp [rowsExtract, rowBytesOf] at this

/-- The field genuinely excludes the adopted opening-READING extractor: the two
adopted demo openings have the SAME opened row bytes (both have no groups) yet
`CommitmentOrderSurvey.demoExtract` separates them. -/
theorem demo_extract_violates_rows_determine_columns :
    ¬ (∀ o1 o2 : WhirIntermediate.Opening, rowBytesOf o1 = rowBytesOf o2 →
        CommitmentOrderSurvey.demoExtract [] o1 = CommitmentOrderSurvey.demoExtract [] o2) := by
  intro h
  exact CommitmentOrderSurvey.demo_extract_moves_with_the_opening [] (⟨0, by decide⟩ : Fin 5)
    (congrFun (h CommitmentOrderSurvey.demoOpeningA CommitmentOrderSurvey.demoOpeningB rfl)
      (⟨0, by decide⟩ : Fin 5))

end Audit.Wire3.R1bBridge
