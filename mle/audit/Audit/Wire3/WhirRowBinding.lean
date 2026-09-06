import Audit.Wire3.WhirRows
import Audit.Wire3.MerkleExtraction
import Audit.Wire3.WhirTerminal

/-!
# Binding of actually opened raw rows and their canonical decoded dot values

This module joins the existing executable WhirRows.openGroup to the existing
MerkleExtraction proof. Leaf membership is DERIVED from (index,row) membership
in the actual returned rows zipped with the caller's indices. No separately
supplied leaf hashes or single-path witnesses replace that execution.

Two successful openings at the same root, depth and index either contain the
same raw row bytes, or expose an unequal pair of actual hash inputs: the two
raw rows themselves, or two 64-byte Merkle compression inputs. Hash remains an
arbitrary deterministic function; the alternatives do not assume injectivity
or bound the probability of a collision.

With the SAME Layout and successful explicit decodeRow calls, equal bytes give
equal canonical values by decoder determinism, NOT by an assumed serialization
injectivity theorem. Row offsets may differ. The concrete WhirTerminal.dot is
then applied to those values with the SAME weights; a length precondition is
explicit where the theorem identifies every decoded column with a weight.
No theorem establishes that weights or Layout came from earlier WHIR rounds.

This is a deterministic bridge between manually translated Lean models, not
Solidity/Yul/Rust refinement or a complete WHIR verifier. openGroup is still
only the raw-read/authentication stage; field decoding is not moved before
Merkle or transcript challenges. Sampling, full final-split ordering, final
claim, cryptographic hash security, and PCS soundness remain separate.
-/
namespace Audit.Wire3.WhirRowBinding
open Spongefish (Bytes Hash Digest State Ext3)
open WhirRows (RawRow Layout)

/-- A concrete leaf collision on the selected raw rows, or an actual pair of
64-byte compression inputs obtained from the two extracted paths. -/
def RowCollision (hash : Hash) (row other : Bytes) : Prop :=
  (row ≠ other ∧ hash row = hash other) ∨
    ∃ a b : Bytes, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b

def HashCollision (hash : Hash) : Prop := ∃ a b : Bytes, a ≠ b ∧ hash a = hash b

theorem row_collision_exposes_actual_hash_inputs (hash : Hash) (row other : Bytes)
    (h : RowCollision hash row other) : HashCollision hash := by
  rcases h with hleaf | ⟨a,b,_,_,hne,heq⟩
  · exact ⟨row,other,hleaf⟩
  · exact ⟨a,b,hne,heq⟩

theorem get_some_same_position_mem_zip {α β : Type} (as : List α) (bs : List β)
    (position : Nat) (a : α) (b : β)
    (ha : as.get? position = some a) (hb : bs.get? position = some b) :
    (a,b) ∈ as.zip bs := by
  induction as generalizing position bs with
  | nil => simp at ha
  | cons x xs ih =>
      cases bs with
      | nil => simp at hb
      | cons y ys =>
          cases position with
          | zero => cases ha; cases hb; simp
          | succ position =>
              exact List.mem_cons_of_mem _ (ih ys position ha hb)

theorem raw_row_membership_gives_actual_hash_membership (hash : Hash) (indices : List Nat)
    (rows : List RawRow) (index : Nat) (row : RawRow)
    (h : (index,row) ∈ indices.zip rows) :
    (index,hash row.bytes) ∈ indices.zip (WhirRows.rowHashes hash rows) := by
  induction indices generalizing rows with
  | nil => simp at h
  | cons i rest ih =>
      cases rows with
      | nil => simp at h
      | cons r tail =>
          rcases List.mem_cons.mp h with heq | ht
          · cases heq
            exact List.mem_cons_self _ _
          · exact List.mem_cons_of_mem _ (ih tail ht)

/-- The path starts at the hash of this actual returned row, has the exact
verified tree depth, and ends at the same caller-supplied raw digest. -/
theorem accepted_group_row_extracts_same_hash_path (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (index : Nat) (row : RawRow)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (hm : (index,row) ∈ indices.zip rows) :
    ∃ siblings : List Digest, siblings.length = depth ∧
      Merkle.pathRoot hash index (hash row.bytes) siblings = root := by
  have hm' := raw_row_membership_gives_actual_hash_membership hash indices rows index row hm
  have hne : indices.isEmpty = false := by cases indices <;> simp_all
  have hv := WhirRows.group_success_same_merkle_inputs hash root depth indices layout hints s t rows h
  exact MerkleExtraction.accepted_nonempty_opening_extracts_paths hash root depth indices
    (WhirRows.rowHashes hash rows) hints _ t.hintPos hne hv (index,hash row.bytes) hm'

theorem accepted_group_position_extracts_same_hash_path (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (position index : Nat) (row : RawRow)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (hi : indices.get? position = some index) (hr : rows.get? position = some row) :
    ∃ siblings : List Digest, siblings.length = depth ∧
      Merkle.pathRoot hash index (hash row.bytes) siblings = root :=
  accepted_group_row_extracts_same_hash_path hash root depth indices layout hints s t rows index row h
    (get_some_same_position_mem_zip indices rows position index row hi hr)

/-- Unlike decoded binding, raw-byte binding does not require equal layouts.
Offsets, query-list positions, hint buffers and post-opening states may differ. -/
theorem accepted_raw_rows_bind_or_collision (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (layout otherLayout : Layout) (hints otherHints : Bytes)
    (s t otherS otherT : State) (rows otherRows : List RawRow) (row otherRow : RawRow)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (h' : WhirRows.openGroup hash root depth otherIndices otherLayout otherHints otherS = some (otherRows,otherT))
    (hm : (index,row) ∈ indices.zip rows) (hm' : (index,otherRow) ∈ otherIndices.zip otherRows) :
    row.bytes = otherRow.bytes ∨ RowCollision hash row.bytes otherRow.bytes := by
  have hv := WhirRows.group_success_same_merkle_inputs hash root depth indices layout hints s t rows h
  have hv' := WhirRows.group_success_same_merkle_inputs hash root depth otherIndices otherLayout otherHints
    otherS otherT otherRows h'
  exact MerkleExtraction.accepted_raw_rows_bind_or_hash_collision hash root depth index indices otherIndices
    (WhirRows.rowHashes hash rows) (WhirRows.rowHashes hash otherRows) hints otherHints row.bytes otherRow.bytes
    _ t.hintPos _ otherT.hintPos hv hv'
    (raw_row_membership_gives_actual_hash_membership hash indices rows index row hm)
    (raw_row_membership_gives_actual_hash_membership hash otherIndices otherRows index otherRow hm')

theorem accepted_positions_bind_or_collision (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (layout otherLayout : Layout) (hints otherHints : Bytes)
    (s t otherS otherT : State) (rows otherRows : List RawRow) (row otherRow : RawRow)
    (position otherPosition : Nat)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (h' : WhirRows.openGroup hash root depth otherIndices otherLayout otherHints otherS = some (otherRows,otherT))
    (hi : indices.get? position = some index) (hr : rows.get? position = some row)
    (hi' : otherIndices.get? otherPosition = some index) (hr' : otherRows.get? otherPosition = some otherRow) :
    row.bytes = otherRow.bytes ∨ RowCollision hash row.bytes otherRow.bytes :=
  accepted_raw_rows_bind_or_collision hash root depth index indices otherIndices layout otherLayout hints otherHints
    s t otherS otherT rows otherRows row otherRow h h'
    (get_some_same_position_mem_zip indices rows position index row hi hr)
    (get_some_same_position_mem_zip otherIndices otherRows otherPosition index otherRow hi' hr')

theorem same_bytes_same_decoder (layout : Layout) (row other : RawRow) (h : row.bytes = other.bytes) :
    WhirRows.decodeRow layout row = WhirRows.decodeRow layout other :=
  congrArg (WhirRows.decodeFields layout.encoding layout.columns) h

theorem successful_same_bytes_same_values (layout : Layout) (row other : RawRow)
    (values otherValues : List Ext3) (hb : row.bytes = other.bytes)
    (h : WhirRows.decodeRow layout row = some values)
    (h' : WhirRows.decodeRow layout other = some otherValues) : values = otherValues :=
  Option.some.inj (h.symm.trans ((same_bytes_same_decoder layout row other hb).trans h'))

theorem accepted_decoded_rows_bind_or_collision (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (layout : Layout) (hints otherHints : Bytes)
    (s t otherS otherT : State) (rows otherRows : List RawRow) (row otherRow : RawRow)
    (values otherValues : List Ext3)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS = some (otherRows,otherT))
    (hm : (index,row) ∈ indices.zip rows) (hm' : (index,otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRows.decodeRow layout row = some values)
    (hd' : WhirRows.decodeRow layout otherRow = some otherValues) :
    values = otherValues ∨ RowCollision hash row.bytes otherRow.bytes := by
  rcases accepted_raw_rows_bind_or_collision hash root depth index indices otherIndices layout layout hints otherHints
    s t otherS otherT rows otherRows row otherRow h h' hm hm' with hb | hc
  · exact Or.inl (successful_same_bytes_same_values layout row otherRow values otherValues hb hd hd')
  · exact Or.inr hc

theorem distinct_accepted_decoded_rows_expose_hash_collision (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (layout : Layout) (hints otherHints : Bytes)
    (s t otherS otherT : State) (rows otherRows : List RawRow) (row otherRow : RawRow)
    (values otherValues : List Ext3)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS = some (otherRows,otherT))
    (hm : (index,row) ∈ indices.zip rows) (hm' : (index,otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRows.decodeRow layout row = some values)
    (hd' : WhirRows.decodeRow layout otherRow = some otherValues) (hne : values ≠ otherValues) :
    HashCollision hash := by
  have hc := (accepted_decoded_rows_bind_or_collision hash root depth index indices otherIndices layout hints otherHints
    s t otherS otherT rows otherRows row otherRow values otherValues h h' hm hm' hd hd').resolve_left hne
  exact row_collision_exposes_actual_hash_inputs hash row.bytes otherRow.bytes hc

/-- Explicit later decoder-and-dot operation. It does not authenticate or
alter cursors. Source's full-column dot needs weights.length = layout.columns;
without that precondition this is merely the existing zip-totalized dot model. -/
def decodedDot (weights : List Arithmetic.Ext3) (layout : Layout) (row : RawRow) : Option Arithmetic.Ext3 :=
  (WhirRows.decodeRow layout row).map fun values => WhirTerminal.dot weights (values.map Subtype.val)

theorem decoded_dot_uses_same_values (weights : List Arithmetic.Ext3) (layout : Layout) (row : RawRow)
    (values : List Ext3) (h : WhirRows.decodeRow layout row = some values) :
    decodedDot weights layout row = some (WhirTerminal.dot weights (values.map Subtype.val)) := by
  simp [decodedDot,h]

theorem decoded_dot_success_extracts_actual_decoder (weights : List Arithmetic.Ext3) (layout : Layout)
    (row : RawRow) (value : Arithmetic.Ext3) (h : decodedDot weights layout row = some value) :
    ∃ values : List Ext3, WhirRows.decodeRow layout row = some values ∧
      value = WhirTerminal.dot weights (values.map Subtype.val) := by
  unfold decodedDot at h
  cases hd : WhirRows.decodeRow layout row with
  | none => simp [hd] at h
  | some values =>
      simp only [hd,Option.map,Option.some.injEq] at h
      exact ⟨values,rfl,h.symm⟩

theorem successful_dot_has_exact_weight_count (weights : List Arithmetic.Ext3) (layout : Layout)
    (row : RawRow) (values : List Ext3) (hw : weights.length = layout.columns)
    (h : WhirRows.decodeRow layout row = some values) :
    weights.length = (values.map Subtype.val).length := by
  rw [List.length_map,(WhirRows.decoded_row_exact_columns_and_bytes layout row values h).1,hw]

theorem accepted_decoded_dots_bind_or_collision (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (layout : Layout) (hints otherHints : Bytes)
    (s t otherS otherT : State) (rows otherRows : List RawRow) (row otherRow : RawRow)
    (weights : List Arithmetic.Ext3) (value otherValue : Arithmetic.Ext3)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS = some (otherRows,otherT))
    (hm : (index,row) ∈ indices.zip rows) (hm' : (index,otherRow) ∈ otherIndices.zip otherRows)
    (hd : decodedDot weights layout row = some value)
    (hd' : decodedDot weights layout otherRow = some otherValue) :
    value = otherValue ∨ RowCollision hash row.bytes otherRow.bytes := by
  obtain ⟨values,hvalues,hvalue⟩ := decoded_dot_success_extracts_actual_decoder weights layout row value hd
  obtain ⟨otherValues,hotherValues,hotherValue⟩ :=
    decoded_dot_success_extracts_actual_decoder weights layout otherRow otherValue hd'
  rcases accepted_decoded_rows_bind_or_collision hash root depth index indices otherIndices layout hints otherHints
    s t otherS otherT rows otherRows row otherRow values otherValues h h' hm hm' hvalues hotherValues with heq | hc
  · exact Or.inl (hvalue.trans (by simpa [heq] using hotherValue.symm))
  · exact Or.inr hc

/-- Full-column specialization: every canonical decoded value has a weight,
and the actual WhirTerminal.dot result binds under the same explicit collision
alternative. The weights themselves are caller context, not derived here. -/
theorem accepted_full_column_dot_binding (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (layout : Layout) (hints otherHints : Bytes)
    (s t otherS otherT : State) (rows otherRows : List RawRow) (row otherRow : RawRow)
    (weights : List Arithmetic.Ext3) (values otherValues : List Ext3)
    (hw : weights.length = layout.columns)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS = some (otherRows,otherT))
    (hm : (index,row) ∈ indices.zip rows) (hm' : (index,otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRows.decodeRow layout row = some values)
    (hd' : WhirRows.decodeRow layout otherRow = some otherValues) :
    weights.length = (values.map Subtype.val).length ∧
      weights.length = (otherValues.map Subtype.val).length ∧
      (WhirTerminal.dot weights (values.map Subtype.val) =
        WhirTerminal.dot weights (otherValues.map Subtype.val) ∨ RowCollision hash row.bytes otherRow.bytes) :=
  ⟨successful_dot_has_exact_weight_count weights layout row values hw hd,
   successful_dot_has_exact_weight_count weights layout otherRow otherValues hw hd',
   accepted_decoded_dots_bind_or_collision hash root depth index indices otherIndices layout hints otherHints
     s t otherS otherT rows otherRows row otherRow weights _ _ h h' hm hm'
     (decoded_dot_uses_same_values weights layout row values hd)
     (decoded_dot_uses_same_values weights layout otherRow otherValues hd')⟩

theorem distinct_accepted_dot_values_expose_hash_collision (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (layout : Layout) (hints otherHints : Bytes)
    (s t otherS otherT : State) (rows otherRows : List RawRow) (row otherRow : RawRow)
    (weights : List Arithmetic.Ext3) (value otherValue : Arithmetic.Ext3)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows,t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS = some (otherRows,otherT))
    (hm : (index,row) ∈ indices.zip rows) (hm' : (index,otherRow) ∈ otherIndices.zip otherRows)
    (hd : decodedDot weights layout row = some value)
    (hd' : decodedDot weights layout otherRow = some otherValue) (hne : value ≠ otherValue) :
    HashCollision hash :=
  row_collision_exposes_actual_hash_inputs hash row.bytes otherRow.bytes
    ((accepted_decoded_dots_bind_or_collision hash root depth index indices otherIndices layout hints otherHints
      s t otherS otherT rows otherRows row otherRow weights value otherValue h h' hm hm' hd hd').resolve_left hne)

/-- Ordinary positive fixture from WhirRows, now with a path derived from its
real openGroup success rather than assumed leaf membership. -/
theorem ordinary_opened_row_path_example :
    ∃ siblings : List Digest, siblings.length = 0 ∧
      Merkle.pathRoot WhirRows.exampleHash 0 (WhirRows.exampleHash WhirRows.exampleBaseRow.bytes) siblings =
        WhirRows.exampleBaseRoot :=
  accepted_group_row_extracts_same_hash_path WhirRows.exampleHash WhirRows.exampleBaseRoot 0 [0]
    ⟨.base,1⟩ WhirRows.exampleBaseHints WhirRows.exampleStart
    {WhirRows.exampleStart with hintPos := 16} [WhirRows.exampleBaseRow] 0 WhirRows.exampleBaseRow
    WhirRows.base_row_open_example (by simp)

theorem unequal_offsets_do_not_change_decoded_values :
    WhirRows.exampleBaseRow.offset ≠ (24 : Nat) ∧
      WhirRows.decodeRow ⟨.base,1⟩ WhirRows.exampleBaseRow =
        WhirRows.decodeRow ⟨.base,1⟩ ⟨24,WhirRows.exampleBaseRow.bytes⟩ := by
  exact ⟨by decide,rfl⟩

theorem ordinary_dot_example :
    decodedDot [⟨2,0,0⟩] ⟨.base,1⟩ WhirRows.exampleBaseRow = some ⟨14,0,0⟩ := by decide

end Audit.Wire3.WhirRowBinding
