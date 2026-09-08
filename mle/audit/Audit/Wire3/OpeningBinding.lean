import Audit.Wire3.WhirRowBinding
import Audit.Wire3.OpenedClaimFold
import Audit.Wire3.IntegratedTerminalChain

/-!
# Opening binding: how much of the wire-v3 extraction join is provable

This module attacks ASSUMPTION 17 (`normClaims`) of the adopted
`Audit.Wire3.ConditionalSoundness.Assumptions`, whose own docstring says that
"no assumption in this structure, and no theorem in this file, connects the
values the WHIR/Merkle check actually bound to the cells of `tLast`", and that
"an adversary who can open the WHIR commitment to something other than `tLast`
is not excluded by anything below -- only by fiat".

Source correspondence (at the pinned submodule revision):
* `mle/src/verifier_v2.rs` 313-395: five `fold_ext3_claim` calls, the bound-cell
  mask, the two packed points `packed_ext3_point = row ++ index`, and
  `pcs.verify_grouped`.
* `mle/contracts/src/PackedClaimExt3.sol` 107-125: cells 0-2 are the log-point
  folds of preprocessed / witness / normInverse, cells 3-4 the gate-point folds
  of preprocessed / witness, cell 5 stays the canonical zero.
* `mle/contracts/src/spongefish/SpongefishWhirVerify.sol`: the raw-row loops of
  `_openAndVerifyCommitment` / `_openSplitCommitments`, modelled by the adopted
  `WhirRows.openGroup` / `openGroups`, and `SpongefishMerkle.verify` /
  `_processLayerInto`, modelled by the adopted `Merkle.verify`.

## What is proved

1. **The statement** (section 4).  `OpensCommittedTable` names, for this
   protocol, what "the opened values are the committed table's evaluations"
   asserts: per group, at the two index points, with the mask.  It is the
   adopted `IntegratedTerminalChain.HonestOpenings`.  Under it, every bound cell
   of the WHIR context IS the dense evaluation of the width-padded group table
   at the packed point, and the sixth slot is unopened
   (`opens_committed_table_gives_full_table_cells`,
   `mask_leaves_sixth_cell_unopened`).
2. **Assumption-free binding** (sections 1-3, 5).  Two accepted openings of the
   same root at the same index and depth agree or exhibit a concrete pair of
   unequal actual hash inputs -- lifted from one tree
   (`WhirRowBinding`) to the sequential three-commitment block the outer verifier
   opens (`accepted_groups_position_rows_bind_or_collision`).  The expected-claim
   folds are determined by the opened cells alone
   (`expected_claims_determined_by_opened_values`), and an accepted WHIR check
   carries each bound fold into the parsed claims
   (`accepted_claims_are_folds_of_opened_values`).
3. **The smallest cryptographic residue** (sections 2-3).  `NoCollision hash L`
   is injectivity of `hash` on a FINITE list `L`.  `executedGroupInputs` and
   `executedGroupsInputs` compute that list FROM THE EXECUTION ITSELF -- the raw
   rows it returned plus the 64-byte compression inputs its layered Merkle run
   performs, at the cursor `WhirRows.group_success_same_merkle_inputs` proves it
   uses.  `layer_parent_input_recorded` / `layers_path_inputs_recorded` are the
   adopted extraction theorems strengthened so that every input a path collision
   could name is a member of that list.  Then accepted opening + `NoCollision`
   over exactly those inputs forces the rows, their canonical decodings and
   their `WhirTerminal.dot` values to agree
   (`accepted_group_rows_bind_under_no_collision` and its consequences).  The
   list is not a free parameter: `example_executed_inputs_base_row` computes it,
   `example_no_collision_holds` decides it on a real execution, and
   `example_layer_input_is_the_actual_compression` shows the compression part is
   genuinely nonempty at depth one.
4. **Partial discharge of ASSUMPTION 17** (section 7).  The opened cells of a
   group, under the opening relation, ARE the fully bound cells of that group's
   committed columns (`row_openings_are_fully_bound_cells`,
   `opened_cells_are_bound_cells`).  Hence
   `norm_claims_from_openings_and_column_identification`, which is a
   BICONDITIONAL rewrite: given the opening relation, `normClaims` holds iff
   `CommittedColumnsAreExtractedTables` does.  Its mathematical content is the
   single definitional identity `row_openings_are_fully_bound_cells`; the
   residual structure is doing most of the work, and that residue is at
   FOLD level (bound cell values at the point), which is strictly weaker than
   identifying the columns themselves.

## BINDING IS NOT EXTRACTION

Binding says: two accepted openings of the SAME root at the SAME index agree.
Extraction says: there EXISTS a committed table whose evaluations the opened
values are.  The second does not follow from the first and is NOT proved here.
It generally requires an extractor, which this model has no notion of.
Concretely, in this model:

* **R1 (a modelling gap, before any cryptography).**  The outer verifier's whole
  WHIR check is the pair of opaque `Verifier.Engine` observations `parseWhir` /
  `whirTail`.  Nothing relates them to `WhirRows.openGroup` or `Merkle.verify`:
  `blind_engine_accepts_every_context` exhibits an engine, agreeing with any
  given one on every derived round, index and context, whose WHIR check accepts
  EVERY proof.  Sections 1-3 therefore do not yet reach the outer soundness
  chain.
* **R2 (binding cannot supply the relation).**
  `opening_relation_ignores_the_commitment`: the opening relation is preserved
  when all three Merkle roots of the proof are replaced by arbitrary ones, so no
  reduction from same-root binding can produce it.
  `example_two_committed_tables_open_the_same_proof` exhibits one proof, one
  context and two DIFFERENT committed column families both satisfying it with
  the same expected claim.
* **R3 (the column identification).**  `CommittedColumnsAreExtractedTables` is
  assumed, not proved; the adopted audit contains no map from a `Verifier.Root`
  to a column list.

## Not claimed

No WHIR proximity, list-decoding, query-repetition or Fiat--Shamir property; no
collision PROBABILITY (`NoCollision` is a deterministic injectivity statement
about a specific finite list, and `clash_no_collision_fails` shows it can be
false); no soundness of the deployed system; no Rust/Yul/Solidity refinement; no
statement about the gate lane.  `hash` remains an arbitrary deterministic
function throughout.  The counterexample section uses byte-projection fixtures,
not Keccak.
-/

namespace Audit.Wire3.OpeningBinding
open Spongefish (Bytes Hash Digest State Ext3)
open Audit.Wire3.GoldilocksExt3Field (Element)

/-! ## 1. The hash inputs one Merkle execution actually performs -/

/-- The 64-byte compression inputs of ONE executed `Merkle.processLayer`, in
execution order.  The branch structure mirrors `Merkle.processLayer` exactly:
the paired branch consumes no hint and compresses the two adjacent nodes, the
lone/unpaired branch reads its sibling from the SAME hint cursor.  A failing
read contributes nothing, exactly as a failing layer performs no further
hashing. -/
def layerInputs (hints : Bytes) : List Merkle.Node → Nat → List Bytes
  | [], _ => []
  | [a], offset =>
      match Merkle.readDigest hints offset with
      | none => []
      | some (sibling, _) => [Merkle.parentInput a.index a.digest sibling]
  | a :: b :: tail, offset =>
      if b.index = Nat.xor a.index 1 then
        Merkle.parentInput a.index a.digest b.digest ::
          Merkle.parentInput b.index b.digest a.digest :: layerInputs hints tail offset
      else
        match Merkle.readDigest hints offset with
        | none => []
        | some (sibling, afterRead) =>
            Merkle.parentInput a.index a.digest sibling :: layerInputs hints (b :: tail) afterRead
termination_by nodes _ => nodes.length

/-- The compression inputs of a whole executed `Merkle.runLayers`, threading the
SAME cursor the execution threads. -/
def layersInputs (hash : Hash) (hints : Bytes) : Nat → List Merkle.Node → Nat → List Bytes
  | 0, _, _ => []
  | depth + 1, nodes, offset =>
      match Merkle.processLayer hash hints nodes offset with
      | none => []
      | some (parents, next) =>
          layerInputs hints nodes offset ++ layersInputs hash hints depth parents next

/-- The compression inputs of an executed `Merkle.verify` on these leaves. -/
def merkleInputs (hash : Hash) (hints : Bytes) (depth : Nat) (indices : List Nat)
    (leaves : List Digest) (offset : Nat) : List Bytes :=
  layersInputs hash hints depth ((indices.zip leaves).map fun p => Merkle.Node.mk p.1 p.2) offset

/-- The compression inputs along one extracted path. -/
def pathInputs (hash : Hash) : Nat → Digest → List Digest → List Bytes
  | _, _, [] => []
  | i, leaf, s :: rest =>
      Merkle.parentInput i leaf s :: pathInputs hash (i / 2) (Merkle.parent hash i leaf s) rest

theorem layerInputs_paired (hints : Bytes) (a b : Merkle.Node) (tail : List Merkle.Node)
    (offset : Nat) (h : b.index = Nat.xor a.index 1) :
    layerInputs hints (a :: b :: tail) offset =
      Merkle.parentInput a.index a.digest b.digest ::
        Merkle.parentInput b.index b.digest a.digest :: layerInputs hints tail offset := by
  rw [layerInputs]
  simp [h]

theorem layerInputs_unpaired (hints : Bytes) (a b : Merkle.Node) (tail : List Merkle.Node)
    (offset : Nat) (sibling : Digest) (afterRead : Nat)
    (h : ¬ b.index = Nat.xor a.index 1)
    (hr : Merkle.readDigest hints offset = some (sibling, afterRead)) :
    layerInputs hints (a :: b :: tail) offset =
      Merkle.parentInput a.index a.digest sibling :: layerInputs hints (b :: tail) afterRead := by
  rw [layerInputs]
  simp [h, hr]

theorem layerInputs_lone (hints : Bytes) (a : Merkle.Node) (offset : Nat) (sibling : Digest)
    (afterRead : Nat) (hr : Merkle.readDigest hints offset = some (sibling, afterRead)) :
    layerInputs hints [a] offset = [Merkle.parentInput a.index a.digest sibling] := by
  rw [layerInputs]
  simp [hr]

/-- **Every parent edge the layer creates was actually hashed by that layer.**
This is `MerkleExtraction.successful_layer_gives_each_parent` strengthened so
the compression input is recorded in the FINITE list this execution performs. -/
theorem layer_parent_input_recorded (hash : Hash) (hints : Bytes)
    (nodes parents : List Merkle.Node) (offset next : Nat)
    (h : Merkle.processLayer hash hints nodes offset = some (parents, next)) :
    ∀ node ∈ nodes, ∃ p ∈ parents, ∃ sibling : Digest,
      p.index = node.index / 2 ∧ p.digest = Merkle.parent hash node.index node.digest sibling ∧
      Merkle.parentInput node.index node.digest sibling ∈ layerInputs hints nodes offset := by
  cases nodes with
  | nil => simp
  | cons a rest =>
      cases rest with
      | nil =>
          cases hr : Merkle.readDigest hints offset with
          | none => simp [Merkle.processLayer, hr] at h
          | some pair =>
              rcases pair with ⟨sibling, afterRead⟩
              simp only [Merkle.processLayer, hr, bind, Option.bind, pure, Option.some.injEq,
                Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              intro node hn
              have hn : node = a := by simpa using hn
              subst node
              refine ⟨Merkle.merged hash a sibling, by simp, sibling, rfl, rfl, ?_⟩
              rw [layerInputs_lone hints a offset sibling afterRead hr]
              simp
      | cons b tail =>
          by_cases hp : b.index = Nat.xor a.index 1
          · cases ht : Merkle.processLayer hash hints tail offset with
            | none => simp [Merkle.processLayer, hp, ht] at h
            | some pair =>
                rcases pair with ⟨remaining, afterLayer⟩
                simp only [Merkle.processLayer, hp, ↓reduceIte, ht, bind, Option.bind, pure,
                  Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                intro node hn
                rw [layerInputs_paired hints a b tail offset hp]
                rcases List.mem_cons.mp hn with heq | hn
                · subst node
                  exact ⟨Merkle.merged hash a b.digest, by simp, b.digest, rfl, rfl, by simp⟩
                rcases List.mem_cons.mp hn with heq | hn
                · subst node
                  refine ⟨Merkle.merged hash a b.digest, by simp, a.digest, ?_, ?_, by simp⟩
                  · simp only [Merkle.merged, hp, MerkleExtraction.sibling_index_same_parent]
                  · simp only [Merkle.merged, hp, MerkleExtraction.paired_parent_digest]
                obtain ⟨p, hp', s, hi, hd, hmem⟩ :=
                  layer_parent_input_recorded hash hints tail remaining offset afterLayer ht node hn
                exact ⟨p, List.mem_cons_of_mem _ hp', s, hi, hd,
                  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)⟩
          · cases hr : Merkle.readDigest hints offset with
            | none => simp [Merkle.processLayer, hp, hr] at h
            | some pair =>
                rcases pair with ⟨sibling, afterRead⟩
                cases ht : Merkle.processLayer hash hints (b :: tail) afterRead with
                | none => simp [Merkle.processLayer, hp, hr, ht] at h
                | some pair =>
                    rcases pair with ⟨remaining, afterLayer⟩
                    simp only [Merkle.processLayer, hp, ↓reduceIte, hr, ht, bind, Option.bind, pure,
                      Option.some.injEq, Prod.mk.injEq] at h
                    rcases h with ⟨rfl, rfl⟩
                    intro node hn
                    rw [layerInputs_unpaired hints a b tail offset sibling afterRead hp hr]
                    rcases List.mem_cons.mp hn with heq | hn
                    · subst node
                      exact ⟨Merkle.merged hash a sibling, by simp, sibling, rfl, rfl, by simp⟩
                    obtain ⟨p, hp', s, hi, hd, hmem⟩ := layer_parent_input_recorded hash hints
                      (b :: tail) remaining afterRead afterLayer ht node hn
                    exact ⟨p, List.mem_cons_of_mem _ hp', s, hi, hd, List.mem_cons_of_mem _ hmem⟩
termination_by nodes.length

/-- **Every compression along an extracted path was actually performed.**
`MerkleExtraction.successful_layers_extract_paths` with the recorded-input
conclusion added. -/
theorem layers_path_inputs_recorded (hash : Hash) (hints : Bytes) (depth : Nat)
    (nodes finalNodes : List Merkle.Node) (offset next : Nat)
    (h : Merkle.runLayers hash hints depth nodes offset = some (finalNodes, next)) :
    ∀ node ∈ nodes, ∃ last ∈ finalNodes, ∃ siblings : List Digest,
      siblings.length = depth ∧
      Merkle.pathRoot hash node.index node.digest siblings = last.digest ∧
      ∀ input ∈ pathInputs hash node.index node.digest siblings,
        input ∈ layersInputs hash hints depth nodes offset := by
  induction depth generalizing nodes offset with
  | zero =>
      cases h
      intro node hn
      exact ⟨node, hn, [], rfl, rfl, by simp [pathInputs]⟩
  | succ depth ih =>
      cases hl : Merkle.processLayer hash hints nodes offset with
      | none => simp [Merkle.runLayers, hl] at h
      | some pair =>
          rcases pair with ⟨parents, afterLayer⟩
          simp only [Merkle.runLayers, hl, bind, Option.bind] at h
          intro node hn
          obtain ⟨p, hp, s, hi, hd, hmem⟩ :=
            layer_parent_input_recorded hash hints nodes parents offset afterLayer hl node hn
          obtain ⟨last, hlast, ss, hlen, hroot, hrec⟩ := ih parents afterLayer h p hp
          have hsplit : layersInputs hash hints (depth + 1) nodes offset =
              layerInputs hints nodes offset ++ layersInputs hash hints depth parents afterLayer := by
            rw [layersInputs]; simp [hl]
          refine ⟨last, hlast, s :: ss, by simp [hlen], ?_, ?_⟩
          · simpa only [Merkle.pathRoot, ← hi, ← hd] using hroot
          · intro input hinput
            rw [hsplit]
            rcases List.mem_cons.mp hinput with rfl | hinput
            · exact List.mem_append_left _ hmem
            · refine List.mem_append_right _ (hrec input ?_)
              simpa only [← hi, ← hd] using hinput

/-- Path extraction from an accepted multiproof, with every compression input
recorded in the finite list THIS execution performs. -/
theorem accepted_opening_extracts_recorded_path (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (leaves : List Digest) (hints : Bytes) (offset next : Nat)
    (hne : indices.isEmpty = false)
    (h : Merkle.verify hash root depth indices leaves hints offset = some next) :
    ∀ pair ∈ indices.zip leaves, ∃ siblings : List Digest,
      siblings.length = depth ∧ Merkle.pathRoot hash pair.1 pair.2 siblings = root ∧
      ∀ input ∈ pathInputs hash pair.1 pair.2 siblings,
        input ∈ merkleInputs hash hints depth indices leaves offset := by
  have hs := Merkle.nonempty_acceptance_requires_computed_root hash root depth indices leaves hints
    offset next hne h
  intro pair hp
  have hn : Merkle.Node.mk pair.1 pair.2 ∈ (indices.zip leaves).map (fun p => Merkle.Node.mk p.1 p.2) :=
    List.mem_map_of_mem (fun p : Nat × Digest => Merkle.Node.mk p.1 p.2) hp
  obtain ⟨last, hlast, ss, hlen, hroot, hrec⟩ := layers_path_inputs_recorded hash hints depth _ _
    offset next hs.2.2 _ hn
  have hlast : last = Merkle.Node.mk 0 root := by simpa using hlast
  subst last
  exact ⟨ss, hlen, hroot, hrec⟩

/-- A path collision names two inputs that lie ON the two extracted paths. -/
theorem path_collision_recorded (hash : Hash) (siblings : List Digest) (index : Nat)
    (leaf other : Digest) (otherSiblings : List Digest)
    (h : Merkle.PathCollision hash index leaf siblings other otherSiblings) :
    ∃ a b : Bytes, a ∈ pathInputs hash index leaf siblings ∧
      b ∈ pathInputs hash index other otherSiblings ∧
      a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b := by
  induction siblings generalizing index leaf other otherSiblings with
  | nil => simp [Merkle.PathCollision] at h
  | cons s ss ih =>
      cases otherSiblings with
      | nil => exact absurd h (by simp [Merkle.PathCollision])
      | cons t ts =>
          rcases h with h | h
          · exact ⟨Merkle.parentInput index leaf s, Merkle.parentInput index other t,
              by simp [pathInputs], by simp [pathInputs],
              Merkle.parent_input_length _ _ _, Merkle.parent_input_length _ _ _, h.1, h.2⟩
          · obtain ⟨a, b, ha, hb, hla, hlb, hne, heq⟩ := ih (index / 2)
              (Merkle.parent hash index leaf s) (Merkle.parent hash index other t) ts h
            exact ⟨a, b, by simp [pathInputs, ha], by simp [pathInputs, hb], hla, hlb, hne, heq⟩

/-! ## 2. The hash inputs one WHIR group opening actually performs -/

/-- Every byte string THIS `WhirRows.openGroup` call hands to `hash`: the raw
rows it actually returned (whose leaf hashes `authenticateRows` computes) and
the compression inputs of the layered Merkle run it actually performs, at the
cursor `group_success_same_merkle_inputs` proves it uses.  This is a function of
the call's own arguments, not a free parameter: a failing call performs no
authentication hashing and contributes the empty list. -/
def executedGroupInputs (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : WhirRows.Layout) (hints : Bytes) (s : State) : List Bytes :=
  match WhirRows.openGroup hash root depth indices layout hints s with
  | none => []
  | some (rows, _) =>
      rows.map (fun row => row.bytes) ++
        merkleInputs hash hints depth indices (WhirRows.rowHashes hash rows)
          (s.hintPos + 8 + indices.length * WhirRows.rowBytes layout)

/-- The same, for the sequential three-commitment group block the outer verifier
opens (`WhirRows.openGroups`, `WhirIntermediate.openPrevious`). -/
def executedGroupsInputs (hash : Hash) (depth : Nat) (indices : List Nat)
    (layout : WhirRows.Layout) (hints : Bytes) : List Digest → State → List Bytes
  | [], _ => []
  | root :: roots, s =>
      match WhirRows.openGroup hash root depth indices layout hints s with
      | none => []
      | some (_, next) =>
          executedGroupInputs hash root depth indices layout hints s ++
            executedGroupsInputs hash depth indices layout hints roots next

/-- Injectivity of `hash` RESTRICTED to a finite list of inputs.  Every use
below instantiates `inputs` with the executed lists above, so this is a
statement about the byte strings a particular execution hashes, not an
unquantified collision-resistance assumption and not a free parameter. -/
def NoCollision (hash : Hash) (inputs : List Bytes) : Prop :=
  ∀ a ∈ inputs, ∀ b ∈ inputs, hash a = hash b → a = b

theorem noCollision_of_subset (hash : Hash) (small big : List Bytes)
    (hsub : ∀ x ∈ small, x ∈ big) (h : NoCollision hash big) : NoCollision hash small :=
  fun a ha b hb heq => h a (hsub a ha) b (hsub b hb) heq

theorem executedGroupInputs_success (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (layout : WhirRows.Layout) (hints : Bytes) (s t : State)
    (rows : List WhirRows.RawRow)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t)) :
    executedGroupInputs hash root depth indices layout hints s =
      rows.map (fun row => row.bytes) ++
        merkleInputs hash hints depth indices (WhirRows.rowHashes hash rows)
          (s.hintPos + 8 + indices.length * WhirRows.rowBytes layout) := by
  unfold executedGroupInputs
  rw [h]

theorem row_bytes_recorded (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : WhirRows.Layout) (hints : Bytes) (s t : State) (rows : List WhirRows.RawRow)
    (row : WhirRows.RawRow) (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (hrow : row ∈ rows) : row.bytes ∈ executedGroupInputs hash root depth indices layout hints s := by
  rw [executedGroupInputs_success hash root depth indices layout hints s t rows h]
  exact List.mem_append_left _ (List.mem_map_of_mem (fun r : WhirRows.RawRow => r.bytes) hrow)

theorem merkle_input_recorded (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : WhirRows.Layout) (hints : Bytes) (s t : State) (rows : List WhirRows.RawRow)
    (input : Bytes) (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (hin : input ∈ merkleInputs hash hints depth indices (WhirRows.rowHashes hash rows)
      (s.hintPos + 8 + indices.length * WhirRows.rowBytes layout)) :
    input ∈ executedGroupInputs hash root depth indices layout hints s := by
  rw [executedGroupInputs_success hash root depth indices layout hints s t rows h]
  exact List.mem_append_right _ hin

theorem executedGroupsInputs_cons (hash : Hash) (depth : Nat) (indices : List Nat)
    (layout : WhirRows.Layout) (hints : Bytes) (root : Digest) (roots : List Digest)
    (s next : State) (rows : List WhirRows.RawRow)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, next)) :
    executedGroupsInputs hash depth indices layout hints (root :: roots) s =
      executedGroupInputs hash root depth indices layout hints s ++
        executedGroupsInputs hash depth indices layout hints roots next := by
  rw [executedGroupsInputs]
  simp [h]

/-- Each commitment's own executed inputs are part of the whole block's executed
inputs, traversed through the SAME sequential execution (no independently
supplied per-group cursor). -/
theorem groups_position_inputs_recorded (hash : Hash) (depth : Nat) (indices : List Nat)
    (layout : WhirRows.Layout) (hints : Bytes) :
    ∀ (roots : List Digest) (s t : State) (groups : List (List WhirRows.RawRow))
      (position : Nat) (root : Digest),
      WhirRows.openGroups hash depth indices layout hints roots s = some (groups, t) →
      roots.get? position = some root →
      ∃ rows before after, groups.get? position = some rows ∧
        WhirRows.openGroup hash root depth indices layout hints before = some (rows, after) ∧
        ∀ x ∈ executedGroupInputs hash root depth indices layout hints before,
          x ∈ executedGroupsInputs hash depth indices layout hints roots s := by
  intro roots
  induction roots with
  | nil => intro _ _ _ position _ _ hr; simp at hr
  | cons first rest ih =>
      intro s t groups position root h hr
      obtain ⟨rows, tail, next, rfl, hg, ht⟩ :=
        WhirRows.groups_success_next_is_actual_returned_cursor hash depth indices layout hints
          first rest s t groups h
      have hsplit := executedGroupsInputs_cons hash depth indices layout hints first rest s next rows hg
      cases position with
      | zero =>
          have hroot : first = root := by simpa using hr
          subst hroot
          exact ⟨rows, s, next, rfl, hg, fun x hx => by rw [hsplit]; exact List.mem_append_left _ hx⟩
      | succ position =>
          obtain ⟨selected, before, after, hi, ho, hmem⟩ := ih next t tail position root ht (by simpa using hr)
          exact ⟨selected, before, after, hi, ho,
            fun x hx => by rw [hsplit]; exact List.mem_append_right _ (hmem x hx)⟩

/-! ## 3. Binding of the opened rows under execution-bound collision freedom -/

/-- **RAW-BYTE BINDING, NO CRYPTOGRAPHIC ASSUMPTION LEFT FREE.**  Two accepted
openings of the SAME root at the SAME depth and the SAME index return the same
raw row bytes, PROVIDED `hash` is injective on the FINITE list of inputs these
two executions actually hash.  Query lists, layouts, hint buffers, cursors and
post-opening states may differ.

This is `WhirRowBinding.accepted_raw_rows_bind_or_collision` with the
existentially quantified collision replaced by injectivity on the executed
inputs; the collision alternative of that theorem names inputs which this proof
shows are members of the executed lists. -/
theorem accepted_group_rows_bind_under_no_collision (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat)
    (layout otherLayout : WhirRows.Layout) (hints otherHints : Bytes)
    (s t otherS otherT : State) (rows otherRows : List WhirRows.RawRow)
    (row otherRow : WhirRows.RawRow)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices otherLayout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hno : NoCollision hash (executedGroupInputs hash root depth indices layout hints s ++
      executedGroupInputs hash root depth otherIndices otherLayout otherHints otherS)) :
    row.bytes = otherRow.bytes := by
  have hne : indices.isEmpty = false := by cases indices <;> simp_all
  have hne' : otherIndices.isEmpty = false := by cases otherIndices <;> simp_all
  have hv := WhirRows.group_success_same_merkle_inputs hash root depth indices layout hints s t rows h
  have hv' := WhirRows.group_success_same_merkle_inputs hash root depth otherIndices otherLayout
    otherHints otherS otherT otherRows h'
  have hz := WhirRowBinding.raw_row_membership_gives_actual_hash_membership hash indices rows index row hm
  have hz' := WhirRowBinding.raw_row_membership_gives_actual_hash_membership hash otherIndices
    otherRows index otherRow hm'
  obtain ⟨ss, hlen, hroot, hrec⟩ := accepted_opening_extracts_recorded_path hash root depth indices
    (WhirRows.rowHashes hash rows) hints _ t.hintPos hne hv (index, hash row.bytes) hz
  obtain ⟨ts, tlen, troot, trec⟩ := accepted_opening_extracts_recorded_path hash root depth
    otherIndices (WhirRows.rowHashes hash otherRows) otherHints _ otherT.hintPos hne' hv'
    (index, hash otherRow.bytes) hz'
  rcases Merkle.same_root_same_leaf_or_path_collision hash ss index (hash row.bytes)
    (hash otherRow.bytes) ts (hlen.trans tlen.symm) (hroot.trans troot.symm) with heq | hc
  · refine hno row.bytes ?_ otherRow.bytes ?_ heq
    · exact List.mem_append_left _ (row_bytes_recorded hash root depth indices layout hints s t rows
        row h (by
          have := List.of_mem_zip hm
          exact this.2))
    · exact List.mem_append_right _ (row_bytes_recorded hash root depth otherIndices otherLayout
        otherHints otherS otherT otherRows otherRow h' (List.of_mem_zip hm').2)
  · obtain ⟨a, b, ha, hb, _, _, hab, heq⟩ := path_collision_recorded hash ss index (hash row.bytes)
      (hash otherRow.bytes) ts hc
    exact absurd (hno a (List.mem_append_left _ (merkle_input_recorded hash root depth indices layout
      hints s t rows a h (hrec a ha))) b (List.mem_append_right _ (merkle_input_recorded hash root
      depth otherIndices otherLayout otherHints otherS otherT otherRows b h' (trec b hb))) heq) hab

/-- Canonical decoded values bind under the same execution-bound hypothesis.
Equal bytes give equal values by decoder determinism (`same_bytes_same_decoder`),
NOT by an assumed serialization injectivity. -/
theorem accepted_group_values_bind_under_no_collision (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s t otherS otherT : State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (values otherValues : List Ext3)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRows.decodeRow layout row = some values)
    (hd' : WhirRows.decodeRow layout otherRow = some otherValues)
    (hno : NoCollision hash (executedGroupInputs hash root depth indices layout hints s ++
      executedGroupInputs hash root depth otherIndices layout otherHints otherS)) :
    values = otherValues :=
  WhirRowBinding.successful_same_bytes_same_values layout row otherRow values otherValues
    (accepted_group_rows_bind_under_no_collision hash root depth index indices otherIndices layout
      layout hints otherHints s t otherS otherT rows otherRows row otherRow h h' hm hm' hno) hd hd'

/-- The concrete `WhirTerminal.dot` of the opened row against the SAME weights
binds.  This is the value the WHIR terminal row check consumes; the weights and
layout are caller context, derived nowhere here. -/
theorem accepted_group_dot_binds_under_no_collision (hash : Hash) (root : Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Bytes) (s t otherS otherT : State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (weights : List Arithmetic.Ext3) (value otherValue : Arithmetic.Ext3)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hv : WhirRowBinding.decodedDot weights layout row = some value)
    (hv' : WhirRowBinding.decodedDot weights layout otherRow = some otherValue)
    (hno : NoCollision hash (executedGroupInputs hash root depth indices layout hints s ++
      executedGroupInputs hash root depth otherIndices layout otherHints otherS)) :
    value = otherValue := by
  obtain ⟨vals, hvals, hval⟩ :=
    WhirRowBinding.decoded_dot_success_extracts_actual_decoder weights layout row value hv
  obtain ⟨others, hothers, hother⟩ :=
    WhirRowBinding.decoded_dot_success_extracts_actual_decoder weights layout otherRow otherValue hv'
  have heq := accepted_group_values_bind_under_no_collision hash root depth index indices
    otherIndices layout hints otherHints s t otherS otherT rows otherRows row otherRow vals others
    h h' hm hm' hvals hothers hno
  rw [hval, hother, heq]

/-- **Grouped binding.**  The outer verifier opens THREE commitments at the same
query list in one sequential block (`WhirRows.openGroups`, the
`WhirIntermediate.openPrevious` / `rootsToOpen` structure, `CallerProfile`'s
`numCommitments = 3`).  This theorem is stated for an ARBITRARY root list at an
arbitrary position, which the outer verifier instantiates at length three; that
instantiation is not made here.  For any commitment position of two accepted
blocks over the SAME root list, the rows at a common index agree, under
collision freedom on the inputs the two BLOCKS actually hash. -/
theorem accepted_groups_position_rows_bind_under_no_collision (hash : Hash) (depth index : Nat)
    (indices otherIndices : List Nat) (layout : WhirRows.Layout) (hints otherHints : Bytes)
    (roots : List Digest) (s t otherS otherT : State)
    (groups otherGroups : List (List WhirRows.RawRow)) (position : Nat) (root : Digest)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (h : WhirRows.openGroups hash depth indices layout hints roots s = some (groups, t))
    (h' : WhirRows.openGroups hash depth otherIndices layout otherHints roots otherS =
      some (otherGroups, otherT))
    (hr : roots.get? position = some root)
    (hg : groups.get? position = some rows) (hg' : otherGroups.get? position = some otherRows)
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hno : NoCollision hash
      (executedGroupsInputs hash depth indices layout hints roots s ++
        executedGroupsInputs hash depth otherIndices layout otherHints roots otherS)) :
    row.bytes = otherRow.bytes := by
  obtain ⟨rows', before, after, hi, ho, hsub⟩ := groups_position_inputs_recorded hash depth indices
    layout hints roots s t groups position root h hr
  obtain ⟨others', before', after', hi', ho', hsub'⟩ := groups_position_inputs_recorded hash depth
    otherIndices layout otherHints roots otherS otherT otherGroups position root h' hr
  rw [Option.some.inj (hi.symm.trans hg)] at ho
  rw [Option.some.inj (hi'.symm.trans hg')] at ho'
  refine accepted_group_rows_bind_under_no_collision hash root depth index indices otherIndices
    layout layout hints otherHints before after before' after' rows otherRows row otherRow ho ho'
    hm hm' (noCollision_of_subset hash _ _ ?_ hno)
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ (hsub x hx)
  · exact List.mem_append_right _ (hsub' x hx)

/-- **The assumption-free grouped shape.**  Same root list, same commitment
position, same index: the rows agree OR a concrete unequal pair of actual hash
inputs is exhibited (the two raw rows, or two 64-byte compression inputs from
the extracted paths).  This is `WhirRowBinding.accepted_raw_rows_bind_or_collision`
lifted from a single tree to the sequential three-commitment block; no injectivity
and no probability is used. -/
theorem accepted_groups_position_rows_bind_or_collision (hash : Hash) (depth index : Nat)
    (indices otherIndices : List Nat) (layout otherLayout : WhirRows.Layout)
    (hints otherHints : Bytes) (roots : List Digest) (s t otherS otherT : State)
    (groups otherGroups : List (List WhirRows.RawRow)) (position : Nat) (root : Digest)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (h : WhirRows.openGroups hash depth indices layout hints roots s = some (groups, t))
    (h' : WhirRows.openGroups hash depth otherIndices otherLayout otherHints roots otherS =
      some (otherGroups, otherT))
    (hr : roots.get? position = some root)
    (hg : groups.get? position = some rows) (hg' : otherGroups.get? position = some otherRows)
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows) :
    row.bytes = otherRow.bytes ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes := by
  obtain ⟨rows', before, after, hi, ho, _⟩ := groups_position_inputs_recorded hash depth indices
    layout hints roots s t groups position root h hr
  obtain ⟨others', before', after', hi', ho', _⟩ := groups_position_inputs_recorded hash depth
    otherIndices otherLayout otherHints roots otherS otherT otherGroups position root h' hr
  rw [Option.some.inj (hi.symm.trans hg)] at ho
  rw [Option.some.inj (hi'.symm.trans hg')] at ho'
  exact WhirRowBinding.accepted_raw_rows_bind_or_collision hash root depth index indices otherIndices
    layout otherLayout hints otherHints before after before' after' rows otherRows row otherRow
    ho ho' hm hm'

/-! ## 4. What "the opened values are the committed table's evaluations" says -/

/-- **The opening relation of THIS protocol, per group, at the two index points,
with the mask.**  This is the adopted `IntegratedTerminalChain.HonestOpenings`,
named here for what it asserts:

* five bound cells, `Fin 5`, in the Solidity `_foldV2UsedCellsUnchecked` order
  (`PackedClaimExt3.sol` 107-125): cells 0-2 are the log-point groups
  preprocessed / witness / normInverse, cells 3-4 the gate-point groups
  preprocessed / witness (`verifier_v2.rs` 313-375, `bind_expected` slot
  `point * NUM_PCS_GROUPS_V2 + group`);
* `cols i` are the constituent columns the commitment of that group is supposed
  to cover, each a FULL table for that cell's sumcheck row point (`full`);
* the group fits its width capacity `2 ^ indexBits` (`capacity`), i.e.
  `pack_mles`'s zero-padding to `width.next_power_of_two()`;
* `opened`: the proof's opened cells for that group ARE the per-column row folds
  at that cell's row point.

The mask is NOT part of this relation: cell 5, the norm-inverse group at the
gate point, is `none` for every proof and every index point, so no opening is
claimed there (`mask_leaves_sixth_cell_unopened`). -/
abbrev OpensCommittedTable (c : Verifier.Config) (p : Verifier.Proof) (s : Verifier.RoundState)
    (idx : Verifier.IndexPoints) (cols : Fin 5 → List (List Element)) : Prop :=
  IntegratedTerminalChain.HonestOpenings c p s idx cols

/-- The mask half of the statement: the sixth slot is unopened for every proof,
so the opening relation has nothing to say there. -/
theorem mask_leaves_sixth_cell_unopened (foldClaim : Verifier.FoldClaim) (c : Verifier.Config)
    (p : Verifier.Proof) (idx : Verifier.IndexPoints) :
    OpenedClaimFold.rustSlot OpenedClaimFold.pointGate OpenedClaimFold.groupNormInverse = 5 ∧
    (Verifier.expectedClaims foldClaim c p idx)[5]? = some none ∧
    (Verifier.expectedClaims foldClaim c p idx).map Option.isSome =
      [true, true, true, true, true, false] :=
  ⟨rfl, rfl, rfl⟩

/-- Under the opening relation, every bound cell of the WHIR context IS the dense
evaluation of the width-padded group table at the packed point `row ++ index`,
and the context's native point is that packed point's complete reversal.  This is
the adopted `OpenedClaimFold.expected_claim_cell_is_full_table_evaluation`, in
the `Fin 5` form the outer verifier uses. -/
theorem opens_committed_table_gives_full_table_cells (c : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints) (cols : Fin 5 → List (List Element))
    (hyp : OpensCommittedTable c p s idx cols) (i : Fin 5) :
    OpenedClaimFold.CellOpensFullTable (Verifier.whirContext Connections.packedFold c p s idx)
      i.val (OpenedClaimFold.cellPoint i) (cols i)
      (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).2) :=
  OpenedClaimFold.expected_claim_cell_is_full_table_evaluation c p s idx i (cols i)
    (hyp.full i) (hyp.capacity i) (hyp.opened i)

/-! ## 5. The expected-claim folds are determined by the opened values -/

/-- `Verifier.expectedClaims` reads NOTHING of the proof but its opened cells:
two proofs with the same `used` cells have the same expected claims at the same
index points.  Deterministic; no acceptance and no assumption. -/
theorem expected_claims_determined_by_opened_values (foldClaim : Verifier.FoldClaim)
    (c : Verifier.Config) (p q : Verifier.Proof) (idx : Verifier.IndexPoints)
    (h : p.used = q.used) :
    Verifier.expectedClaims foldClaim c p idx = Verifier.expectedClaims foldClaim c q idx := by
  unfold Verifier.expectedClaims
  rw [h]

/-- An accepted WHIR check carries every bound expected claim into the parsed
claim list unchanged: position `i < 5` of the parsed claims IS the fold of the
opened cells of that group at that group's index point.  Deterministic
consequence of `claimsMatch`; nothing about WHIR internals. -/
theorem accepted_claims_are_folds_of_opened_values (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (h : Verifier.verifyWhir e (Verifier.derivedContext e c p) p = true) :
    ∃ parsed, e.parseWhir (Verifier.derivedContext e c p) p.whirTranscript p.whirHints = some parsed ∧
      ∀ i : Fin 5, parsed.claims[i.val]? =
        some (e.foldClaim (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).1
          (Verifier.width c)
          (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2) := by
  obtain ⟨parsed, hp, _, _, hc, _⟩ := Verifier.whir_acceptance_requires_bound_statement e _ p h
  refine ⟨parsed, hp, fun i => ?_⟩
  refine IntegratedTerminalChain.claims_match_bound_entry hc i.val _ ?_
  show (Verifier.expectedClaims e.foldClaim c p (Verifier.derivedIndices e c p))[i.val]? = _
  exact OpenedClaimFold.expected_claim_cell_exact e.foldClaim c p (Verifier.derivedIndices e c p) i

/-! ## 6. Binding is not extraction: the irreducible residue, exhibited -/

/-- Fill the masked slots of an expected-claim list with an arbitrary value.
`Verifier.claimsMatch` still CONSUMES one parsed claim at a masked position, so
a parsed list must supply something there. -/
def unmask (claims : List (Option Verifier.Ext3)) : List Verifier.Ext3 :=
  claims.map (fun x => x.getD Verifier.zero)

theorem claimsMatch_unmask (claims : List (Option Verifier.Ext3)) :
    Verifier.claimsMatch claims (unmask claims) = true := by
  induction claims with
  | nil => rfl
  | cons a as ih =>
      cases a with
      | none => simpa [unmask, Verifier.claimsMatch] using ih
      | some x => simpa [unmask, Verifier.claimsMatch] using ih

/-- An engine identical to `e` except that its two WHIR observations
(`parseWhir`, `whirTail`) are replaced by ones that always succeed and always
report exactly the roots and claims the context asked for. -/
def blindEngine (e : Verifier.Engine) : Verifier.Engine :=
  { e with
    parseWhir := fun ctx _ _ => some ⟨ctx.roots, ctx.roots, unmask ctx.expectedClaims⟩,
    whirTail := fun _ _ _ _ => true }

theorem blind_engine_same_derived_data (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) :
    Verifier.derivedRounds (blindEngine e) c p = Verifier.derivedRounds e c p ∧
    Verifier.derivedIndices (blindEngine e) c p = Verifier.derivedIndices e c p ∧
    Verifier.derivedContext (blindEngine e) c p = Verifier.derivedContext e c p :=
  ⟨rfl, rfl, rfl⟩

/-- **RESIDUE R1 (a MODELLING gap, prior to any cryptography).**  In the adopted
outer verifier the whole WHIR check is the pair of opaque `Engine` observations
`parseWhir` / `whirTail` (`Verifier.lean` 345-368).  Nothing in the adopted
model relates them to `WhirRows.openGroup`, `Merkle.verify`, or any object of
sections 1-3: the WHIR check of `blindEngine e` accepts EVERY context and EVERY
proof, while agreeing with `e` on all the derived rounds, indices and context.
So nothing derived from the outer verifier's acceptance mentions the concrete
opening execution until those two engine fields are replaced by the concrete
WHIR verifier: no result about the outer verifier is strengthened by Merkle
binding before that.  A SEPARATE gap survives even then: no theorem in this
module relates a decoded `RawRow` or `decodedDot` to any field of `p.used`, so
sections 1-3 and section 4 remain disjoint halves.  This is the boundary the
adopted `Engine` docstring records; it is not repaired here. -/
theorem blind_engine_accepts_every_context (e : Verifier.Engine) (ctx : Verifier.WhirContext)
    (p : Verifier.Proof) : Verifier.verifyWhir (blindEngine e) ctx p = true := by
  simp [Verifier.verifyWhir, blindEngine, Verifier.rootsAndClaimsMatch, claimsMatch_unmask]

/-- **RESIDUE R2 (BINDING is not EXTRACTION).**  The opening relation of section
4 — the premise `normClaims` needs — never mentions the commitment.  Replacing
all three of the proof's Merkle roots by arbitrary ones preserves it exactly.
Consequently no reduction from Merkle binding can produce it: binding says two
openings of the SAME root agree, while this relation asserts the EXISTENCE of a
table whose evaluations the opened cells are, with no root involved.  Producing
such a table is the job of an extractor, which the adopted model does not have
and which is not definable from the deterministic objects here. -/
theorem opening_relation_ignores_the_commitment (c : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints) (cols : Fin 5 → List (List Element))
    (r1 r2 r3 : Verifier.Root) (h : OpensCommittedTable c p s idx cols) :
    OpensCommittedTable c
      { p with preprocessedRoot := r1, witnessRoot := r2, normInverseRoot := r3 } s idx cols :=
  ⟨h.full, h.capacity, h.opened⟩

/-! ## 7. How much of ASSUMPTION 17 (`normClaims`) this discharges -/

theorem ext3_list_val_injective : ∀ xs ys : List Verifier.Ext3,
    xs.map Subtype.val = ys.map Subtype.val → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      exact congrArg₂ List.cons (Subtype.eq h.1) (ext3_list_val_injective xs ys h.2)

/-- **The per-column row folds ARE the fully bound cells.**  The opened cells of
a group, under the opening relation, are exactly the cells the adopted
`NormTerminalBinding.bindColumn` leaves after binding every variable of those
columns at the point (`NormTerminalBinding.bound_column_is_packed_fold`).  This
is a deterministic identity between two adopted models, with no assumption. -/
theorem row_openings_are_fully_bound_cells (cols : List (List Element)) (point : List Element)
    (h : ∀ col ∈ cols, col.length = 2 ^ point.length) :
    OpenedClaimFold.rowOpenings cols point =
      (NormTerminalBinding.cellValues
        (cols.map (fun col => NormTerminalBinding.bindColumn col point))).map Subtype.val := by
  unfold OpenedClaimFold.rowOpenings NormTerminalBinding.cellValues NormDenseRound.values
    NormTerminalBinding.cells
  simp only [List.map_map, Function.comp]
  refine List.map_congr_left (fun col hcol => ?_)
  exact ((NormTerminalBinding.bound_column_is_packed_fold col point point.length
    (h col hcol) rfl).2.2).symm

/-- The opened cells of one group, as `Verifier.Ext3`, are the fully bound cells
of that group's committed columns. -/
theorem opened_cells_are_bound_cells (opened : List Verifier.Ext3) (cols : List (List Element))
    (point : List Element) (hfull : ∀ col ∈ cols, col.length = 2 ^ point.length)
    (hopen : opened.map Subtype.val = OpenedClaimFold.rowOpenings cols point) :
    opened = NormTerminalBinding.cellValues
      (cols.map (fun col => NormTerminalBinding.bindColumn col point)) := by
  refine ext3_list_val_injective _ _ ?_
  rw [hopen, row_openings_are_fully_bound_cells cols point hfull]

/-- **What is LEFT of ASSUMPTION 17 after the identity above.**  Three fields
equate the terminal values with `cellValues ((cols i).map (bindColumn . point))`,
i.e. with FOLDED values at the point -- not with the columns themselves, so this
residue is strictly weaker than column identification (see `exampleColumnsAlt`).
A fourth field is about `publicInputs` and is not about columns at all.
Nothing in the adopted audit proves any of them, and
`opening_relation_ignores_the_commitment` shows why: the model never connects a
`Verifier.Root` to a column list.  The name says "extracted tables" for
continuity with ASSUMPTION 17; it is NOT a PCS extraction statement. -/
structure CommittedColumnsAreExtractedTables (p : Verifier.Proof) (t : NormDenseRound.Tables)
    (constants extra : List Verifier.Ext3) (cols : Fin 5 → List (List Element))
    (point : List Element) : Prop where
  preprocessed : NormTerminalBinding.cellValues
      ((cols 0).map (fun col => NormTerminalBinding.bindColumn col point)) =
    constants ++ NormTerminalBinding.cellValues t.sigmas
  witness : NormTerminalBinding.cellValues
      ((cols 1).map (fun col => NormTerminalBinding.bindColumn col point)) =
    NormTerminalBinding.cellValues t.wires ++ extra
  normInverse : NormTerminalBinding.cellValues
      ((cols 2).map (fun col => NormTerminalBinding.bindColumn col point)) =
    NormTerminalBinding.cellValues t.identityHelpers ++ NormTerminalBinding.cellValues t.sigmaHelpers
  publicInputs : p.publicInputs = t.bindings.map NormDenseRound.Binding.publicValue

/-- **ASSUMPTION 17, RESTATED WITH THE FOLD HALF DISCHARGED.**
`ConditionalSoundness.Assumptions.normClaims` postulates outright that
`Verifier.normTerminalInput p = NormTerminalBinding.toTerminalInput (boundTables tLast x)
constants extra`.  Given the opening relation of section 4 at the log point, that
postulate is EQUIVALENT to the column identification above — i.e. everything
about folding, binding and evaluation is now proved, and the residue is purely
"the commitment covers these columns".

This is a reduction of the assumption, NOT a proof of it: `OpensCommittedTable`
is itself still assumed (R2), and R1 says the outer verifier's WHIR check does
not even mention the concrete opening execution. -/
theorem norm_claims_from_openings_and_column_identification (c : Verifier.Config)
    (p : Verifier.Proof) (s : Verifier.RoundState) (idx : Verifier.IndexPoints)
    (cols : Fin 5 → List (List Element)) (t : NormDenseRound.Tables)
    (constants extra : List Verifier.Ext3)
    (hyp : OpensCommittedTable c p s idx cols)
    (hid : CommittedColumnsAreExtractedTables p t constants extra cols
      (OpenedClaimFold.lift s.logPoint)) :
    Verifier.normTerminalInput p = NormTerminalBinding.toTerminalInput t constants extra := by
  have hlen : (OpenedClaimFold.lift s.logPoint).length = s.logPoint.length := List.length_map _ _
  have h0 : p.used.logPreprocessed = NormTerminalBinding.cellValues
      ((cols 0).map (fun col => NormTerminalBinding.bindColumn col (OpenedClaimFold.lift s.logPoint))) :=
    opened_cells_are_bound_cells _ _ _
      (by show ∀ col ∈ cols 0, col.length = 2 ^ (OpenedClaimFold.lift s.logPoint).length
          rw [hlen]; exact hyp.full 0) (hyp.opened 0)
  have h1 : p.used.logWitness = NormTerminalBinding.cellValues
      ((cols 1).map (fun col => NormTerminalBinding.bindColumn col (OpenedClaimFold.lift s.logPoint))) :=
    opened_cells_are_bound_cells _ _ _
      (by show ∀ col ∈ cols 1, col.length = 2 ^ (OpenedClaimFold.lift s.logPoint).length
          rw [hlen]; exact hyp.full 1) (hyp.opened 1)
  have h2 : p.used.logNormInverse = NormTerminalBinding.cellValues
      ((cols 2).map (fun col => NormTerminalBinding.bindColumn col (OpenedClaimFold.lift s.logPoint))) :=
    opened_cells_are_bound_cells _ _ _
      (by show ∀ col ∈ cols 2, col.length = 2 ^ (OpenedClaimFold.lift s.logPoint).length
          rw [hlen]; exact hyp.full 2) (hyp.opened 2)
  show Verifier.NormTerminalInput.mk _ _ _ _ = Verifier.NormTerminalInput.mk _ _ _ _
  rw [h0, h1, h2, hid.preprocessed, hid.witness, hid.normInverse, hid.publicInputs]

/-! ## 8. Concrete instances -/

/-- The executed input list of the adopted one-leaf base-row opening is exactly
the raw row it returned: a depth-0 tree performs no compression at all. -/
theorem example_executed_inputs_base_row :
    executedGroupInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] ⟨.base, 1⟩
      WhirRows.exampleBaseHints WhirRows.exampleStart = [WhirRows.exampleBaseRow.bytes] := by
  rw [executedGroupInputs_success WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] ⟨.base, 1⟩
    WhirRows.exampleBaseHints WhirRows.exampleStart _ _ WhirRows.base_row_open_example]
  rfl

/-- Non-vacuity of the hypothesis: on a real execution, `NoCollision` over the
inputs THAT execution performs is a decidable, true statement. -/
theorem example_no_collision_holds :
    NoCollision WhirRows.exampleHash
      (executedGroupInputs WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0] ⟨.base, 1⟩
        WhirRows.exampleBaseHints WhirRows.exampleStart) := by
  rw [example_executed_inputs_base_row]
  intro a ha b hb _
  rw [List.mem_singleton.mp ha, List.mem_singleton.mp hb]

/-- A depth-1 execution really does record a 64-byte compression input: the
lone leaf at index 1 reads its sibling from the hint cursor the row loop left,
and the recorded input is the SAME `Merkle.parentInput` the layer hashes. -/
theorem example_layer_input_is_the_actual_compression :
    layerInputs (WhirRows.exampleBaseHints ++ WhirRows.exampleSibling.val)
      [⟨1, WhirRows.exampleBaseRoot⟩] 16 =
      [Merkle.parentInput 1 WhirRows.exampleBaseRoot WhirRows.exampleSibling] ∧
    (Merkle.parentInput 1 WhirRows.exampleBaseRoot WhirRows.exampleSibling).length = 64 := by
  refine ⟨?_, Merkle.parent_input_length _ _ _⟩
  exact layerInputs_lone _ ⟨1, WhirRows.exampleBaseRoot⟩ 16 WhirRows.exampleSibling 48 (by decide)

/-- A deterministic 8-byte projection.  Like the adopted `Merkle.exampleHash`
this is a byte fixture, not Keccak; it is used below precisely BECAUSE it has
collisions on inputs longer than eight bytes. -/
def clashHash : Hash := fun bytes =>
  ⟨(bytes.take 8 ++ List.replicate 32 Spongefish.zeroByte).take 32, by
    simp only [List.length_take, List.length_append, List.length_replicate]
    omega⟩

def clashLayout : WhirRows.Layout := ⟨.base, 2⟩
def clashRowA : WhirRows.RawRow := ⟨8, Transcript.le 8 7 ++ Transcript.le 8 1⟩
def clashRowB : WhirRows.RawRow := ⟨8, Transcript.le 8 7 ++ Transcript.le 8 2⟩
def clashRoot : Digest := clashHash clashRowA.bytes
def clashHintsA : Bytes := Transcript.le 8 2 ++ clashRowA.bytes
def clashHintsB : Bytes := Transcript.le 8 2 ++ clashRowB.bytes

theorem clash_rows_differ : clashRowA.bytes ≠ clashRowB.bytes := by decide

theorem clash_same_leaf_hash : clashHash clashRowA.bytes = clashHash clashRowB.bytes := by decide

theorem clash_open_a :
    WhirRows.openGroup clashHash clashRoot 0 [0] clashLayout clashHintsA WhirRows.exampleStart =
      some ([clashRowA], { WhirRows.exampleStart with hintPos := 24 }) := by decide

theorem clash_open_b :
    WhirRows.openGroup clashHash clashRoot 0 [0] clashLayout clashHintsB WhirRows.exampleStart =
      some ([clashRowB], { WhirRows.exampleStart with hintPos := 24 }) := by decide

theorem clash_values_differ :
    (WhirRows.decodeRow clashLayout clashRowA).map (List.map Subtype.val) =
      some [⟨7, 0, 0⟩, ⟨1, 0, 0⟩] ∧
    (WhirRows.decodeRow clashLayout clashRowB).map (List.map Subtype.val) =
      some [⟨7, 0, 0⟩, ⟨2, 0, 0⟩] := by decide

theorem clash_dots_differ :
    WhirRowBinding.decodedDot [⟨0, 0, 0⟩, ⟨1, 0, 0⟩] clashLayout clashRowA = some ⟨1, 0, 0⟩ ∧
    WhirRowBinding.decodedDot [⟨0, 0, 0⟩, ⟨1, 0, 0⟩] clashLayout clashRowB = some ⟨2, 0, 0⟩ := by
  decide

theorem clash_executed_inputs_a :
    executedGroupInputs clashHash clashRoot 0 [0] clashLayout clashHintsA WhirRows.exampleStart =
      [clashRowA.bytes] := by
  rw [executedGroupInputs_success clashHash clashRoot 0 [0] clashLayout clashHintsA
    WhirRows.exampleStart _ _ clash_open_a]
  rfl

theorem clash_executed_inputs_b :
    executedGroupInputs clashHash clashRoot 0 [0] clashLayout clashHintsB WhirRows.exampleStart =
      [clashRowB.bytes] := by
  rw [executedGroupInputs_success clashHash clashRoot 0 [0] clashLayout clashHintsB
    WhirRows.exampleStart _ _ clash_open_b]
  rfl

/-- **THE COLLISION HYPOTHESIS IS LOAD-BEARING.**  Two openings of the SAME root
at the SAME index, depth and layout are both accepted and return DIFFERENT rows,
whose canonical decodings and whose `WhirTerminal.dot` values against the same
weights differ.  The prover therefore chooses which value the terminal row check
consumes.  The only hypothesis of
`accepted_group_rows_bind_under_no_collision` that fails here is `NoCollision`
over the inputs these two executions actually hash. -/
theorem clash_no_collision_fails :
    ¬ NoCollision clashHash
      (executedGroupInputs clashHash clashRoot 0 [0] clashLayout clashHintsA WhirRows.exampleStart ++
        executedGroupInputs clashHash clashRoot 0 [0] clashLayout clashHintsB
          WhirRows.exampleStart) := by
  rw [clash_executed_inputs_a, clash_executed_inputs_b]
  intro h
  exact clash_rows_differ
    (h clashRowA.bytes (by simp) clashRowB.bytes (by simp) clash_same_leaf_hash)

/-- A second committed column family with the SAME row folds as the adopted
`OpenedClaimFold.exampleColumns`: column `[11,10]` folds to `11 + 5*(10-11) = 6`,
exactly like `[1,2]`. -/
def exampleColumnsAlt : List (List Element) := [[11, 10], [3, 4]]

def exampleFamily (base : List (List Element)) : Fin 5 → List (List Element)
  | 0 => base
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []

/-- **RESIDUE R2, CONCRETELY.**  One proof, one context, TWO different committed
column families, both satisfying the opening relation, both giving the same
expected claim.  So the relation `normClaims` needs does not determine a table:
"there EXISTS a committed table whose evaluations these are" is a statement an
extractor would have to establish, and it is not a consequence of anything the
verifier checks in this model. -/
theorem example_two_committed_tables_open_the_same_proof :
    OpensCommittedTable OpenedClaimFold.exampleConfig OpenedClaimFold.exampleProof
      OpenedClaimFold.exampleRounds OpenedClaimFold.exampleIndex
      (exampleFamily OpenedClaimFold.exampleColumns) ∧
    OpensCommittedTable OpenedClaimFold.exampleConfig OpenedClaimFold.exampleProof
      OpenedClaimFold.exampleRounds OpenedClaimFold.exampleIndex
      (exampleFamily exampleColumnsAlt) ∧
    OpenedClaimFold.exampleColumns ≠ exampleColumnsAlt ∧
    DenseMleIndexed.evaluate (OpenedClaimFold.paddedTable exampleColumnsAlt 1 1) [5, 7] =
      some (20 : Element) ∧
    DenseMleIndexed.evaluate (OpenedClaimFold.paddedTable OpenedClaimFold.exampleColumns 1 1)
      [5, 7] = some (20 : Element) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide,
    by decide⟩

end Audit.Wire3.OpeningBinding
