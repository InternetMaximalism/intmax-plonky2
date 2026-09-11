import Audit.Wire3.ConditionalSoundness
import Audit.Wire3.OpeningBinding
import Audit.Wire3.LocalizedCollisions

/-!
# Repair of the one VACUOUS adopted theorem: opened-dot binding

## What was wrong

`ConditionalSoundness.no_row_collision_binds_opened_dot` (ConditionalSoundness
line 723, which is where the declaration stands; the adopted documents cite it as
line 728) concludes that two accepted openings of the same WHIR Merkle root, at
the same depth and the same query index, decode to the SAME dot value.  Its
cryptographic hypothesis is

  `hfree : ¬ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes`.

`WhirRowBinding.RowCollision hash row other` is a DISJUNCTION.  Its first
disjunct, `row ≠ other ∧ hash row = hash other`, is localized to the two rows.
Its second disjunct, `∃ a b, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧
hash a = hash b`, mentions neither row and is a FINITE pigeonhole: two hundred
fifty-six to the sixty-fourth inputs map into two hundred fifty-six to the
thirty-second digests.  `LocalizedCollisions.compression_collision_is_a_tautology`
proves that disjunct outright for EVERY `hash`, so
`LocalizedCollisions.row_collision_is_a_tautology` gives `RowCollision hash row
other` for every hash and every pair, and the hypothesis `¬ RowCollision …` is
UNSATISFIABLE.

The adopted theorem is therefore TRUE but UNUSABLE: no execution, honest or
adversarial, can ever discharge its hypothesis, so it constrains nothing.  A
result with an unsatisfiable hypothesis also implies every other statement of
the same shape (`vacuous_hypothesis_proves_anything` below), which is the
precise sense in which its conclusion carries no information.  This is strictly
worse than the sixteen statement-trivial `P ∨ Collision` results tabulated in
`LocalizedCollisions`, because there the constructive proof term still exhibits
a concrete pair; here the proof term is only `absurd`-shaped.

This is a DEFECT OF THE STATEMENT, not a soundness error of the verifier and
not an error in the system being audited.  Nothing about the deployed contracts
changes.

## What replaces it

`opened_dot_binds_under_no_collision_among` below: the SAME conclusion, with the
hypothesis replaced by

  `ConditionalSoundness.NoCollisionAmong hash (openedDotInputs …)`,

injectivity of `hash` on the FINITE list of byte strings THESE TWO EXECUTIONS
ACTUALLY HASH.  That list is computed from the calls' own arguments by
`OpeningBinding.executedGroupInputs`, which the adopted development already
defines: the raw rows the two `WhirRows.openGroup` calls returned, together with
the Merkle compression inputs of the layered runs they actually performed, at the
cursor `WhirRows.group_success_same_merkle_inputs` proves is used.  Nothing is a
free parameter and nothing is quantified over all byte strings.

Which pairs does the vacuous hypothesis have to exclude, exactly?  Unwinding
`opened_dot_binds_or_row_collision` (ConditionalSoundness line 716) through
`WhirRowBinding.accepted_decoded_dots_bind_or_collision`,
`WhirRowBinding.accepted_raw_rows_bind_or_collision` and
`MerkleExtraction.accepted_raw_rows_bind_or_hash_collision`, the proof exhibits a
collision at exactly TWO places:

* the two RAW ROW BYTE STRINGS `row.bytes` and `otherRow.bytes`, whose leaf
  digests `WhirRows.rowHashes` computes — these are the first disjunct;
* two sixty-four-byte `Merkle.parentInput` compression inputs lying on the two
  paths that `MerkleExtraction.accepted_nonempty_opening_extracts_paths`
  extracts from the two accepted multiproofs — these are what the second,
  unlocalized disjunct erases, and `OpeningBinding.path_collision_recorded`
  shows both of them lie on the extracted paths.

`openedDotInputs` contains both rows (`openedDotInputs_contains_both_rows`) and
both families of compression inputs, so injectivity on it excludes every pair the
proof can produce (and, for multi-index openings, also the other rows and paths
of the same two runs); the tight leaf-free version is the localized form in
section 4.  It is neither a leaf-only assumption (that would leave the Merkle
layer open) nor a global one.

## Two points of notation

`root` is declared here at type `Spongefish.Digest`, while the adopted statement
at ConditionalSoundness 723 writes `Merkle.Digest`; `Spongefish.Digest` is an
`abbrev` for `Merkle.Digest`, so the two types are definitionally equal and the
binder lists match up to unfolding.  And `opened_rows_bind_under_no_collision_among`
is the ONE-LAYOUT specialization of the adopted two-layout
`OpeningBinding.accepted_group_rows_bind_under_no_collision`, whose `layout` and
`otherLayout` are here both instantiated at the single `layout` the opened-dot
statement fixes.

## Downstream inventory of the vacuous theorem

A repository-wide grep for `no_row_collision_binds_opened_dot` over
`Audit/Wire3/*.lean`, `Audit.lean`, `HistoricalAudit.lean`, `REPORT.md`,
`SCOPE.md` and `README.md` of the adopted tree at 917e2cde returns EIGHT hits,
four in Lean and four in prose, and NO Lean CONSUMER:

* `ConditionalSoundness` 723 — the declaration itself, and the ONLY occurrence
  of the name in that file, so nothing below it applies it;
* `LocalizedCollisions` 164, 208, 256 — prose, the defect table row, and the
  recommendation, all inside the module that found the defect; all three are
  docstring text, not applications;
* `SCOPE.md` 667, `REPORT.md` 1328 and 1341, `README.md` 120 — the same finding
  in prose.

No theorem, in any module, applies it.  `Audit.lean` does not re-export it.  It
is a LEAF of the dependency graph.  Consequently:

* the set of AFFECTED downstream theorems is EMPTY;
* no adopted conclusion — `ConditionalSoundness`'s capstone, `SoundnessAssembly`,
  `ExtractorConstruction`, `Integrated`, `CanonicalProofCheck` — was ever derived
  through it, so no adopted conclusion inherits an unsatisfiable hypothesis;
* the work the capstone actually uses for opened-row binding is
  `OpeningBinding.accepted_group_rows_bind_under_no_collision` and
  `OpeningBinding.accepted_group_dot_binds_under_no_collision`, which already
  carry the execution-computed hypothesis.  The defect is confined to one
  unused statement.

Had there been a consumer, its hypothesis set would contain an unsatisfiable
conjunct and would itself be vacuous; `vacuous_hypothesis_proves_anything`
records that implication in general, so the check is mechanical for any future
consumer.

## Recommendation for the adopted tree

1. Amend the docstring of `ConditionalSoundness.no_row_collision_binds_opened_dot`
   to say that its hypothesis is unsatisfiable and that the theorem is retained
   only for continuity, pointing here.  Do not delete it silently: the existing
   documents cite it.
2. State the replacement in the adopted tree as
   `opened_dot_binds_under_no_collision_among`, with `NoCollisionAmong`
   instantiated at `openedDotInputs`.  The adopted file already defines
   `NoCollisionAmong` and already says, at lines 685-692 and 1349-1357, that this
   is the shape a hash assumption must take; the repair makes the file consistent
   with its own remark.
3. Keep `opened_dot_binds_or_row_collision` as is, with the
   `LocalizedCollisions` statement-triviality caveat attached, and add the
   localized `opened_dot_binds_or_leaf_collision` beside it.
4. `SCOPE.md` 667 and `REPORT.md` 1328/1341 should record that the vacuous
   theorem has no consumers, which is the load-bearing fact for the reader.

## What is proved here

* vacuity, mechanically: `no_row_collision_binds_opened_dot_is_vacuous`;
* the replacement, derived from adopted results:
  `opened_dot_binds_under_no_collision_among`;
* that it is STRICTLY MORE USEFUL: it yields the vacuous theorem's conclusion
  (`replacement_yields_the_vacuous_conclusion`) from a hypothesis that a real
  execution discharges;
* the localized disjunction `opened_dot_binds_or_leaf_collision`, whose right
  disjunct names the two rows and is falsifiable, and which recovers the adopted
  `P ∨ RowCollision` shape;
* SATISFIABILITY of the new hypothesis on the adopted base-row execution, with
  two fully discharged instances of the replacement — a degenerate one where the
  two openings coincide and a NON-identical one where the second run reads a
  longer hint buffer — plus a separating-hash witness on a list with two DISTINCT
  entries;
* FALSIFIABILITY on the adopted `clashHash` execution, where the hypothesis fails
  and the conclusion is FALSE, so the hypothesis is load-bearing.

## What is NOT proved here

No hash security, no collision resistance, no random-oracle property, no
probability bound, and no claim that any deployed hash is injective on any list.
`NoCollisionAmong` is a deterministic, execution-relative injectivity statement
used only as a HYPOTHESIS.  No new soundness claim about the verifier is made,
and the repair changes no adopted conclusion.
-/
namespace Audit.Wire3.OpenedDotBinding

open Spongefish (Bytes Hash Digest State)

/-! ## 1. The defect, mechanically -/

/-- The hypothesis of the adopted theorem is the negation of a statement that
`LocalizedCollisions.row_collision_is_a_tautology` proves for every hash and
every pair of byte strings, hence unsatisfiable. -/
theorem no_row_collision_binds_opened_dot_is_vacuous (hash : Hash)
    (row otherRow : WhirRows.RawRow) :
    ¬ ¬ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  LocalizedCollisions.no_row_collision_hypothesis_is_unsatisfiable hash row otherRow

/-- The same statement in the form a caller meets it: there is no way to supply
the adopted theorem's cryptographic argument. -/
theorem vacuous_hypothesis_has_no_instance (hash : Hash) (row otherRow : WhirRows.RawRow)
    (hfree : ¬ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes) : False :=
  no_row_collision_binds_opened_dot_is_vacuous hash row otherRow hfree

/-- Why an unsatisfiable hypothesis makes the conclusion uninformative: the same
hypothesis proves EVERY proposition, so the adopted conclusion `value = otherValue`
is not distinguished by it.  Any future consumer of the vacuous theorem inherits
this, so its own hypothesis set is unsatisfiable too. -/
theorem vacuous_hypothesis_proves_anything (hash : Hash) (row otherRow : WhirRows.RawRow)
    (P : Prop) (hfree : ¬ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes) : P :=
  absurd hfree (no_row_collision_binds_opened_dot_is_vacuous hash row otherRow)

/-- The adopted disjunctive form at line 716 is not vacuous, only trivial as a
statement: its right disjunct is provable outright. -/
theorem opened_dot_disjunction_is_trivial_not_vacuous (hash : Hash)
    (row otherRow : WhirRows.RawRow) (value otherValue : Arithmetic.Ext3) :
    value = otherValue ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (LocalizedCollisions.row_collision_is_a_tautology hash row.bytes otherRow.bytes)

/-! ## 2. The execution-computed list of hash inputs -/

/-- **The list the repaired hypothesis is about.**  Every byte string the two
`WhirRows.openGroup` calls of the opened-dot statement actually hand to `hash`:
the raw rows they returned, and the Merkle compression inputs of the layered runs
they performed.  This is a function of those calls' own arguments; a failing call
contributes the empty list. -/
def openedDotInputs (hash : Hash) (root : Digest) (depth : Nat)
    (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s otherS : State) : List Bytes :=
  OpeningBinding.executedGroupInputs hash root depth indices layout hints s ++
    OpeningBinding.executedGroupInputs hash root depth otherIndices layout otherHints otherS

/-- The adopted `NoCollisionAmong` of `ConditionalSoundness` and the adopted
`NoCollision` of `OpeningBinding` are the same predicate, so the repaired
hypothesis is literally the one the adopted binding theorems already consume. -/
theorem no_collision_among_is_no_collision (hash : Hash) (inputs : List Bytes) :
    ConditionalSoundness.NoCollisionAmong hash inputs ↔ OpeningBinding.NoCollision hash inputs :=
  Iff.rfl

/-- Both opened rows are members of the executed list, so injectivity on it does
exclude the localized leaf pair the adopted proof can exhibit. -/
theorem openedDotInputs_contains_both_rows (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s t otherS otherT : State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows) :
    row.bytes ∈ openedDotInputs hash root depth indices otherIndices layout hints otherHints s otherS ∧
      otherRow.bytes ∈
        openedDotInputs hash root depth indices otherIndices layout hints otherHints s otherS := by
  constructor
  · exact List.mem_append_left _ (OpeningBinding.row_bytes_recorded hash root depth indices layout
      hints s t rows row h (List.of_mem_zip hm).2)
  · exact List.mem_append_right _ (OpeningBinding.row_bytes_recorded hash root depth otherIndices
      layout otherHints otherS otherT otherRows otherRow h' (List.of_mem_zip hm').2)

/-! ## 3. THE REPLACEMENT -/

/-- **THE REPAIR.**  The conclusion of the vacuous adopted theorem, under a
SATISFIABLE hypothesis: `hash` injective on the finite list of byte strings the
two openings actually hash.  Two accepted openings of the same root, at the same
depth, layout and query index, decode to the same `WhirTerminal.dot` value.

Derived from the adopted `OpeningBinding.accepted_group_dot_binds_under_no_collision`,
whose hypothesis is the same list by definition of `openedDotInputs`.  Query
lists, hint buffers, cursors and post-opening states may still differ. -/
theorem opened_dot_binds_under_no_collision_among (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s t otherS otherT : State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (weights : List Arithmetic.Ext3) (value otherValue : Arithmetic.Ext3)
    (hfree : ConditionalSoundness.NoCollisionAmong hash
      (openedDotInputs hash root depth indices otherIndices layout hints otherHints s otherS))
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRowBinding.decodedDot weights layout row = some value)
    (hd' : WhirRowBinding.decodedDot weights layout otherRow = some otherValue) :
    value = otherValue :=
  OpeningBinding.accepted_group_dot_binds_under_no_collision hash root depth index indices
    otherIndices layout hints otherHints s t otherS otherT rows otherRows row otherRow weights
    value otherValue h h' hm hm' hd hd' hfree

/-- The raw-byte level of the same repair, for callers that want the rows rather
than the dot value.  This is the one-layout specialization of the adopted
two-layout `OpeningBinding.accepted_group_rows_bind_under_no_collision`: both its
`layout` and `otherLayout` arguments are instantiated at the single `layout` that
the opened-dot statement fixes. -/
theorem opened_rows_bind_under_no_collision_among (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s t otherS otherT : State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (hfree : ConditionalSoundness.NoCollisionAmong hash
      (openedDotInputs hash root depth indices otherIndices layout hints otherHints s otherS))
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows) :
    row.bytes = otherRow.bytes :=
  OpeningBinding.accepted_group_rows_bind_under_no_collision hash root depth index indices
    otherIndices layout layout hints otherHints s t otherS otherT rows otherRows row otherRow
    h h' hm hm' hfree

/-- **The replacement is strictly more useful.**  It delivers exactly the
conclusion the vacuous theorem states, so every reader of that theorem is served,
while its hypothesis is one a concrete execution discharges (section 5). -/
theorem replacement_yields_the_vacuous_conclusion (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s t otherS otherT : State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (weights : List Arithmetic.Ext3) (value otherValue : Arithmetic.Ext3)
    (hfree : ConditionalSoundness.NoCollisionAmong hash
      (openedDotInputs hash root depth indices otherIndices layout hints otherHints s otherS))
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRowBinding.decodedDot weights layout row = some value)
    (hd' : WhirRowBinding.decodedDot weights layout otherRow = some otherValue) :
    value = otherValue ∧ WhirRowBinding.decodedDot weights layout row = some otherValue :=
  have heq := opened_dot_binds_under_no_collision_among hash root depth index indices otherIndices
    layout hints otherHints s t otherS otherT rows otherRows row otherRow weights value otherValue
    hfree h h' hm hm' hd hd'
  ⟨heq, heq ▸ hd⟩

/-! ## 4. The localized disjunction -/

/-- The Merkle compression inputs alone, separated from the row inputs, so the
leaf pair can be left OUT of the hypothesis and exposed in the conclusion. -/
def executedMerkleInputs (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : WhirRows.Layout) (hints : Bytes) (s : State) : List Bytes :=
  match WhirRows.openGroup hash root depth indices layout hints s with
  | none => []
  | some (rows, _) =>
      OpeningBinding.merkleInputs hash hints depth indices (WhirRows.rowHashes hash rows)
        (s.hintPos + 8 + indices.length * WhirRows.rowBytes layout)

theorem executedMerkleInputs_success (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (layout : WhirRows.Layout) (hints : Bytes) (s t : State)
    (rows : List WhirRows.RawRow)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t)) :
    executedMerkleInputs hash root depth indices layout hints s =
      OpeningBinding.merkleInputs hash hints depth indices (WhirRows.rowHashes hash rows)
        (s.hintPos + 8 + indices.length * WhirRows.rowBytes layout) := by
  unfold executedMerkleInputs
  rw [h]

theorem executedMerkleInputs_subset (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (layout : WhirRows.Layout) (hints : Bytes) (s : State) :
    ∀ x ∈ executedMerkleInputs hash root depth indices layout hints s,
      x ∈ OpeningBinding.executedGroupInputs hash root depth indices layout hints s := by
  unfold executedMerkleInputs OpeningBinding.executedGroupInputs
  cases WhirRows.openGroup hash root depth indices layout hints s with
  | none => intro x hx; exact absurd hx (by simp)
  | some pair => intro x hx; exact List.mem_append_right _ hx

/-- **LOCALIZED FORM.**  Assuming only that the two executions' MERKLE
COMPRESSION inputs do not collide — a strictly weaker, satisfiable hypothesis
that says nothing about the rows — the two accepted openings return the same row
bytes, or a `LocalizedCollisions.LeafCollision` on the two rows is exhibited.
The right disjunct names both rows, so it is refutable for a given pair, unlike
the adopted `RowCollision`. -/
theorem opened_rows_bind_or_leaf_collision (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s t otherS otherT : State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (hpath : OpeningBinding.NoCollision hash
      (executedMerkleInputs hash root depth indices layout hints s ++
        executedMerkleInputs hash root depth otherIndices layout otherHints otherS))
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows) :
    row.bytes = otherRow.bytes ∨
      LocalizedCollisions.LeafCollision hash row.bytes otherRow.bytes := by
  have hne : indices.isEmpty = false := by
    cases indices with
    | nil => simp at hm
    | cons _ _ => rfl
  have hne' : otherIndices.isEmpty = false := by
    cases otherIndices with
    | nil => simp at hm'
    | cons _ _ => rfl
  have hv := WhirRows.group_success_same_merkle_inputs hash root depth indices layout hints s t rows h
  have hv' := WhirRows.group_success_same_merkle_inputs hash root depth otherIndices layout
    otherHints otherS otherT otherRows h'
  have hz := WhirRowBinding.raw_row_membership_gives_actual_hash_membership hash indices rows
    index row hm
  have hz' := WhirRowBinding.raw_row_membership_gives_actual_hash_membership hash otherIndices
    otherRows index otherRow hm'
  obtain ⟨ss, hlen, hroot, hrec⟩ := OpeningBinding.accepted_opening_extracts_recorded_path hash root
    depth indices (WhirRows.rowHashes hash rows) hints _ t.hintPos hne hv (index, hash row.bytes) hz
  obtain ⟨ts, tlen, troot, trec⟩ := OpeningBinding.accepted_opening_extracts_recorded_path hash root
    depth otherIndices (WhirRows.rowHashes hash otherRows) otherHints _ otherT.hintPos hne' hv'
    (index, hash otherRow.bytes) hz'
  rcases Merkle.same_root_same_leaf_or_path_collision hash ss index (hash row.bytes)
    (hash otherRow.bytes) ts (hlen.trans tlen.symm) (hroot.trans troot.symm) with heq | hc
  · by_cases hb : row.bytes = otherRow.bytes
    · exact Or.inl hb
    · exact Or.inr ⟨hb, heq⟩
  · obtain ⟨a, b, ha, hb, _, _, hab, hcol⟩ := OpeningBinding.path_collision_recorded hash ss index
      (hash row.bytes) (hash otherRow.bytes) ts hc
    refine absurd (hpath a (List.mem_append_left _ ?_) b (List.mem_append_right _ ?_) hcol) hab
    · rw [executedMerkleInputs_success hash root depth indices layout hints s t rows h]
      exact hrec a ha
    · rw [executedMerkleInputs_success hash root depth otherIndices layout otherHints otherS otherT
        otherRows h']
      exact trec b hb

/-- The dot-value level of the localized disjunction: the conclusion of the
vacuous adopted theorem, or a leaf collision on the two rows it names. -/
theorem opened_dot_binds_or_leaf_collision (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s t otherS otherT : State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (weights : List Arithmetic.Ext3) (value otherValue : Arithmetic.Ext3)
    (hpath : OpeningBinding.NoCollision hash
      (executedMerkleInputs hash root depth indices layout hints s ++
        executedMerkleInputs hash root depth otherIndices layout otherHints otherS))
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRowBinding.decodedDot weights layout row = some value)
    (hd' : WhirRowBinding.decodedDot weights layout otherRow = some otherValue) :
    value = otherValue ∨ LocalizedCollisions.LeafCollision hash row.bytes otherRow.bytes := by
  rcases opened_rows_bind_or_leaf_collision hash root depth index indices otherIndices layout hints
    otherHints s t otherS otherT rows otherRows row otherRow hpath h h' hm hm' with hb | hleaf
  · obtain ⟨vals, hvals, hval⟩ :=
      WhirRowBinding.decoded_dot_success_extracts_actual_decoder weights layout row value hd
    obtain ⟨others, hothers, hother⟩ :=
      WhirRowBinding.decoded_dot_success_extracts_actual_decoder weights layout otherRow otherValue hd'
    have heq := WhirRowBinding.successful_same_bytes_same_values layout row otherRow vals others hb
      hvals hothers
    rw [hval, hother, heq]
    exact Or.inl rfl
  · exact Or.inr hleaf

/-- The localized disjunction implies the adopted one, so nothing that reads
`opened_dot_binds_or_row_collision` is lost by localizing. -/
theorem localized_recovers_the_adopted_row_disjunction (hash : Hash)
    (row otherRow : Bytes) (value otherValue : Arithmetic.Ext3)
    (h : value = otherValue ∨ LocalizedCollisions.LeafCollision hash row otherRow) :
    value = otherValue ∨ WhirRowBinding.RowCollision hash row otherRow := by
  rcases h with heq | hleaf
  · exact Or.inl heq
  · exact Or.inr (LocalizedCollisions.leaf_collision_implies_row_collision hash row otherRow hleaf)

/-- Under the repaired hypothesis the localized right disjunct is refuted, so the
replacement subsumes the localized form as well. -/
theorem no_collision_among_refutes_the_leaf_disjunct (hash : Hash) (inputs : List Bytes)
    (row otherRow : Bytes) (hrow : row ∈ inputs) (hother : otherRow ∈ inputs)
    (hfree : ConditionalSoundness.NoCollisionAmong hash inputs) :
    ¬ LocalizedCollisions.LeafCollision hash row otherRow :=
  fun hleaf => hleaf.1 (hfree row hrow otherRow hother hleaf.2)

/-! ## 5. SATISFIABILITY of the repaired hypothesis -/

/-- The executed list of the adopted one-leaf base-row opening, taken twice: a
depth-zero tree performs no compression, so the list is the returned row alone,
once per execution. -/
theorem example_opened_dot_inputs :
    openedDotInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] [0] ⟨.base, 1⟩
      WhirRows.exampleBaseHints WhirRows.exampleBaseHints WhirRows.exampleStart
      WhirRows.exampleStart =
      [WhirRows.exampleBaseRow.bytes, WhirRows.exampleBaseRow.bytes] := by
  unfold openedDotInputs
  rw [OpeningBinding.example_executed_inputs_base_row]
  rfl

/-- **THE HYPOTHESIS IS SATISFIABLE.**  On a real accepted execution of the
adopted fixture the repaired hypothesis holds, so instances of the replacement
can be discharged — exactly what the vacuous hypothesis can never be. -/
theorem example_no_collision_among_holds :
    ConditionalSoundness.NoCollisionAmong WhirRows.exampleHash
      (openedDotInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] [0] ⟨.base, 1⟩
        WhirRows.exampleBaseHints WhirRows.exampleBaseHints WhirRows.exampleStart
        WhirRows.exampleStart) := by
  rw [example_opened_dot_inputs]
  intro a ha b hb _
  rcases List.mem_cons.mp ha with rfl | ha
  · rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · rw [List.mem_singleton.mp hb]
  · rw [List.mem_singleton.mp ha]
    rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · rw [List.mem_singleton.mp hb]

theorem example_row_membership :
    (0, WhirRows.exampleBaseRow) ∈ ([0] : List Nat).zip [WhirRows.exampleBaseRow] := by
  simp

/-- **A FULLY DISCHARGED INSTANCE.**  Every hypothesis of the replacement is
supplied from the adopted fixture, none assumed: the two openings are the adopted
`WhirRows.base_row_open_example`, and the collision hypothesis is
`example_no_collision_among_holds`.  The vacuous theorem admits no such
instantiation at all.

This instance is DEGENERATE: the two openings are literally the same execution,
so the binding conclusion is not surprising on its own.  The NON-degenerate
companion `example_replacement_instance_nonidentical` below discharges the same
hypotheses with two genuinely different executions — different hint buffers — and
is the witness that the repaired hypothesis is satisfiable off the diagonal. -/
theorem example_replacement_instance (weights : List Arithmetic.Ext3)
    (value otherValue : Arithmetic.Ext3)
    (hd : WhirRowBinding.decodedDot weights ⟨.base, 1⟩ WhirRows.exampleBaseRow = some value)
    (hd' : WhirRowBinding.decodedDot weights ⟨.base, 1⟩ WhirRows.exampleBaseRow = some otherValue) :
    value = otherValue :=
  opened_dot_binds_under_no_collision_among WhirRows.exampleHash WhirRows.exampleBaseRoot 0 0
    [0] [0] ⟨.base, 1⟩ WhirRows.exampleBaseHints WhirRows.exampleBaseHints WhirRows.exampleStart
    { WhirRows.exampleStart with hintPos := 16 } WhirRows.exampleStart
    { WhirRows.exampleStart with hintPos := 16 } [WhirRows.exampleBaseRow]
    [WhirRows.exampleBaseRow] WhirRows.exampleBaseRow WhirRows.exampleBaseRow weights value
    otherValue example_no_collision_among_holds WhirRows.base_row_open_example
    WhirRows.base_row_open_example example_row_membership example_row_membership hd hd'

/-- **A FULLY DISCHARGED NON-IDENTICAL INSTANCE.**  The same replacement, again
with every hypothesis supplied from the adopted fixture and none assumed, but now
the two runs are NOT the same execution: the second reads the hint buffer
`WhirRows.exampleBaseHints ++ [Spongefish.zeroByte]`, one trailing byte longer
than the first.  Both openings are still accepted, and the repaired hypothesis
still holds on the concatenated executed list, so satisfiability is not an
artefact of the diagonal `hints = otherHints` case of
`example_replacement_instance`. -/
theorem example_replacement_instance_nonidentical (weights : List Arithmetic.Ext3)
    (value otherValue : Arithmetic.Ext3)
    (hd : WhirRowBinding.decodedDot weights ⟨.base, 1⟩ WhirRows.exampleBaseRow = some value)
    (hd' : WhirRowBinding.decodedDot weights ⟨.base, 1⟩ WhirRows.exampleBaseRow = some otherValue) :
    value = otherValue := by
  have hpad : WhirRows.openGroup WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] ⟨.base, 1⟩
      (WhirRows.exampleBaseHints ++ [Spongefish.zeroByte]) WhirRows.exampleStart =
        some ([WhirRows.exampleBaseRow], { WhirRows.exampleStart with hintPos := 16 }) := by decide
  have hexec : OpeningBinding.executedGroupInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0]
      ⟨.base, 1⟩ (WhirRows.exampleBaseHints ++ [Spongefish.zeroByte]) WhirRows.exampleStart =
        [WhirRows.exampleBaseRow.bytes] := by
    rw [OpeningBinding.executedGroupInputs_success _ _ _ _ _ _ _ _ _ hpad]
    rfl
  have hfree : ConditionalSoundness.NoCollisionAmong WhirRows.exampleHash
      (openedDotInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] [0] ⟨.base, 1⟩
        WhirRows.exampleBaseHints (WhirRows.exampleBaseHints ++ [Spongefish.zeroByte])
        WhirRows.exampleStart WhirRows.exampleStart) := by
    unfold openedDotInputs
    rw [OpeningBinding.example_executed_inputs_base_row, hexec]
    intro a ha b hb _
    simp only [List.mem_cons, List.mem_singleton, List.cons_append, List.nil_append,
      List.mem_nil_iff, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl
  exact opened_dot_binds_under_no_collision_among WhirRows.exampleHash WhirRows.exampleBaseRoot 0 0
    [0] [0] ⟨.base, 1⟩ WhirRows.exampleBaseHints
    (WhirRows.exampleBaseHints ++ [Spongefish.zeroByte]) WhirRows.exampleStart
    { WhirRows.exampleStart with hintPos := 16 } WhirRows.exampleStart
    { WhirRows.exampleStart with hintPos := 16 } [WhirRows.exampleBaseRow]
    [WhirRows.exampleBaseRow] WhirRows.exampleBaseRow WhirRows.exampleBaseRow weights value
    otherValue hfree WhirRows.base_row_open_example hpad example_row_membership
    example_row_membership hd hd'

/-- A hash that separates one designated input from everything else. -/
def separatingHash (target : Bytes) : Hash :=
  fun bytes => if bytes = target then Spongefish.zeroDigest else Merkle.exampleHash bytes

theorem separating_hash_at_target (target : Bytes) :
    separatingHash target target = Spongefish.zeroDigest := by
  simp [separatingHash]

/-- Satisfiability is not an artefact of the fixture's repeated entry: the
predicate also holds on a list whose two entries are DISTINCT, under a hash that
separates them.  So the repaired hypothesis is not merely satisfiable on
singletons. -/
theorem separating_hash_no_collision_among_two (a b : Bytes) (hne : a ≠ b)
    (hb : Merkle.exampleHash b ≠ Spongefish.zeroDigest) :
    ConditionalSoundness.NoCollisionAmong (separatingHash a) [a, b] := by
  intro x hx y hy hxy
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases List.mem_cons.mp hy with rfl | hy
    · rfl
    · rw [List.mem_singleton.mp hy] at hxy ⊢
      rw [separating_hash_at_target] at hxy
      simp only [separatingHash, if_neg (Ne.symm hne)] at hxy
      exact absurd hxy.symm hb
  · rw [List.mem_singleton.mp hx] at hxy ⊢
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [separating_hash_at_target] at hxy
      simp only [separatingHash, if_neg (Ne.symm hne)] at hxy
      exact absurd hxy hb
    · rw [List.mem_singleton.mp hy]

/-- A concrete pair for the previous lemma, so the separating witness is not
merely hypothetical. -/
theorem separating_hash_concrete_pair :
    ConditionalSoundness.NoCollisionAmong (separatingHash (Transcript.le 8 7))
      [Transcript.le 8 7, Transcript.le 8 9] :=
  separating_hash_no_collision_among_two (Transcript.le 8 7) (Transcript.le 8 9)
    (by decide) (by decide)

/-! ## 6. FALSIFIABILITY: the repaired hypothesis is load-bearing -/

/-- **THE HYPOTHESIS CAN FAIL, AND WHEN IT DOES THE CONCLUSION IS FALSE.**  On
the adopted `OpeningBinding.clashHash` fixture two openings of the SAME root at
the SAME index, depth and layout are both accepted, return DIFFERENT rows, and
their `WhirTerminal.dot` values against the same weights DIFFER.  The repaired
hypothesis is exactly what fails.  A hypothesis that cannot fail — the adopted
`¬ RowCollision` — cannot have this property. -/
theorem clash_no_collision_among_fails :
    ¬ ConditionalSoundness.NoCollisionAmong OpeningBinding.clashHash
      (openedDotInputs OpeningBinding.clashHash OpeningBinding.clashRoot 0 [0] [0]
        OpeningBinding.clashLayout OpeningBinding.clashHintsA OpeningBinding.clashHintsB
        WhirRows.exampleStart WhirRows.exampleStart) :=
  OpeningBinding.clash_no_collision_fails

theorem clash_conclusion_is_false :
    WhirRowBinding.decodedDot [⟨0, 0, 0⟩, ⟨1, 0, 0⟩] OpeningBinding.clashLayout
        OpeningBinding.clashRowA = some ⟨1, 0, 0⟩ ∧
      WhirRowBinding.decodedDot [⟨0, 0, 0⟩, ⟨1, 0, 0⟩] OpeningBinding.clashLayout
        OpeningBinding.clashRowB = some ⟨2, 0, 0⟩ ∧
      (⟨1, 0, 0⟩ : Arithmetic.Ext3) ≠ ⟨2, 0, 0⟩ :=
  ⟨OpeningBinding.clash_dots_differ.1, OpeningBinding.clash_dots_differ.2, by decide⟩

/-- The localized right disjunct is ACHIEVED on that fixture: the two rows really
are a leaf collision.  So `LeafCollision` is a predicate with content in both
directions. -/
theorem clash_leaf_collision_holds :
    LocalizedCollisions.LeafCollision OpeningBinding.clashHash OpeningBinding.clashRowA.bytes
      OpeningBinding.clashRowB.bytes :=
  ⟨OpeningBinding.clash_rows_differ, OpeningBinding.clash_same_leaf_hash⟩

/-- And it FAILS on an equal pair, which is what `RowCollision` cannot do. -/
theorem leaf_collision_fails_on_equal_rows (hash : Hash) (row : Bytes) :
    ¬ LocalizedCollisions.LeafCollision hash row row :=
  fun h => h.1 rfl

/-- The contrast in one statement: the adopted hypothesis is unsatisfiable while
the repaired one both holds on an accepted execution and fails on another. -/
theorem repair_summary :
    (∀ (hash : Hash) (row otherRow : WhirRows.RawRow),
        ¬ ¬ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes) ∧
      ConditionalSoundness.NoCollisionAmong WhirRows.exampleHash
        (openedDotInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] [0] ⟨.base, 1⟩
          WhirRows.exampleBaseHints WhirRows.exampleBaseHints WhirRows.exampleStart
          WhirRows.exampleStart) ∧
      ¬ ConditionalSoundness.NoCollisionAmong OpeningBinding.clashHash
        (openedDotInputs OpeningBinding.clashHash OpeningBinding.clashRoot 0 [0] [0]
          OpeningBinding.clashLayout OpeningBinding.clashHintsA OpeningBinding.clashHintsB
          WhirRows.exampleStart WhirRows.exampleStart) :=
  ⟨no_row_collision_binds_opened_dot_is_vacuous, example_no_collision_among_holds,
    clash_no_collision_among_fails⟩

end Audit.Wire3.OpenedDotBinding
