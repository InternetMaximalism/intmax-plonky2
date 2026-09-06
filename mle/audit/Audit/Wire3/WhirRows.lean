import Audit.Wire3.Spongefish

/-!
# WHIR raw hint rows, canonical decoding, and layered Merkle connection

Manual executable slice at 4422b4c7 of SpongefishWhirVerify._consumeVecPrefix,
_keccak256At, the raw-row loops in _openAndVerifyCommitment /
_openSplitCommitments / _phaseFinalVectorAndMerkle, and _dotEqWithRow's
base8/Ext3-24 canonical decoding. Merkle.verify is reused, not observed.

RawRow stores the ORIGINAL contiguous hint bytes and their offset. Leaf hashes
are computed from those bytes, not from reduced or re-encoded field values.
Decoding is a separate explicit operation: openGroup never decodes. Thus this
module does not commute the source's later canonical checks across Merkle or
challenge operations. The final split branch additionally decodes/accumulates
inside its row loop; its complete execution order is NOT modeled by openGroup.
Successful openGroup alone therefore does not assert canonical row values;
the separate decodeRow success supplies that property.

The one Spongefish.State carries the exact hint cursor; raw hint reads do not
absorb anything or alter transcript position/counter. Empty query groups still
consume an eight-byte zero Vec prefix. The layered sibling stream has no extra
Vec prefix. Digests stay as 32 raw bytes throughout; no Root/Nat cast is used.

Layout MUST be derived from validated caller parameters (initial rows: base field,
columns=interleavingDepth*numVectors; later rows: Ext3, columns=interleavingDepth).
That parameter projection is not implemented by this module.
List/Nat operations do not prove calldata/Yul, uint256 overflow, allocation or
Rust/Arkworks refinement. Hash is only a deterministic function, not collision
resistance. Sampling, row dot-products, final-vector equality, EOF equality,
and full WHIR/PCS soundness are separate obligations.
-/
namespace Audit.Wire3.WhirRows
open Spongefish (Bytes Hash Digest State Ext3)

inductive Encoding where
  | base
  | ext3
  deriving DecidableEq

def elementBytes : Encoding → Nat
  | .base => 8
  | .ext3 => 24

structure Layout where
  encoding : Encoding
  columns : Nat
  deriving DecidableEq

def rowBytes (layout : Layout) : Nat := layout.columns * elementBytes layout.encoding

structure RawRow where
  offset : Nat
  bytes : Bytes
  deriving DecidableEq

def readRows (hints : Bytes) (size : Nat) : Nat → State → Option (List RawRow × State)
  | 0, s => some ([],s)
  | count+1, s => do
      let (bytes,next) ← Spongefish.proverHint s hints size
      let (rows,last) ← readRows hints size count next
      pure (⟨s.hintPos,bytes⟩ :: rows,last)

def rowHashes (hash : Hash) (rows : List RawRow) : List Digest :=
  rows.map fun row => hash row.bytes

/-- Pure raw hashing is separated from reading; no source sponge transition
occurs between either operation. No field decoding occurs here. -/
def authenticateRows (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (rows : List RawRow) (hints : Bytes) (s : State) : Option State := do
  let offset ← Merkle.verify hash root depth indices (rowHashes hash rows) hints s.hintPos
  pure { s with hintPos := offset }

def openGroup (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (s : State) : Option (List RawRow × State) := do
  let afterPrefix ← Spongefish.consumeVecPrefix s hints (indices.length * layout.columns)
  let (rows,afterRows) ← readRows hints (rowBytes layout) indices.length afterPrefix
  let afterMerkle ← authenticateRows hash root depth indices rows hints afterRows
  pure (rows,afterMerkle)

def decodeBase (data : Bytes) : Option Ext3 :=
  let value := Transcript.fromLe data
  if h : data.length = 8 ∧ value < Arithmetic.modulus then
    some ⟨⟨value,0,0⟩,h.2,Arithmetic.modulus_positive,Arithmetic.modulus_positive⟩
  else none

def decodeElement : Encoding → Bytes → Option Ext3
  | .base, data => decodeBase data
  | .ext3, data => Spongefish.decodeCanonicalExt3 data

def decodeFields (encoding : Encoding) : Nat → Bytes → Option (List Ext3)
  | 0, data => if data.isEmpty then some [] else none
  | count+1, data => do
      let value ← decodeElement encoding (data.take (elementBytes encoding))
      let values ← decodeFields encoding count (data.drop (elementBytes encoding))
      pure (value :: values)

def decodeRow (layout : Layout) (row : RawRow) : Option (List Ext3) :=
  decodeFields layout.encoding layout.columns row.bytes

/-- Proven relation of actual row-loop output to successive source slices. -/
def contiguousSlices (hints : Bytes) (size : Nat) : Nat → List RawRow → Prop
  | _, [] => True
  | offset, row :: rows => row.offset = offset ∧
      row.bytes = (hints.drop offset).take size ∧ row.bytes.length = size ∧
      offset + size ≤ hints.length ∧ contiguousSlices hints size (offset+size) rows

theorem row_hashes_length (hash : Hash) (rows : List RawRow) :
    (rowHashes hash rows).length = rows.length := by simp [rowHashes]

theorem hash_uses_unchanged_raw_bytes (hash : Hash) (row : RawRow) (rows : List RawRow) :
    rowHashes hash (row :: rows) = hash row.bytes :: rowHashes hash rows := rfl

theorem row_hash_at_same_position (hash : Hash) (rows : List RawRow) (index : Nat) (row : RawRow)
    (h : rows.get? index = some row) : (rowHashes hash rows).get? index = some (hash row.bytes) := by
  induction rows generalizing index with
  | nil => simp at h
  | cons head tail ih =>
      cases index with
      | zero => cases h; rfl
      | succ index => exact ih index h

theorem decode_base_exact (data : Bytes) (value : Ext3) (h : decodeBase data = some value) :
    data.length = 8 ∧ value.val.c0 = Transcript.fromLe data ∧
      value.val.c1 = 0 ∧ value.val.c2 = 0 := by
  unfold decodeBase at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨‹_ ∧ _›.1,rfl,rfl,rfl⟩
  · contradiction

theorem decode_base_rejects_noncanonical (data : Bytes)
    (h : Arithmetic.modulus ≤ Transcript.fromLe data) : decodeBase data = none := by
  simp [decodeBase, Nat.not_lt.mpr h]

theorem decode_element_exact_length (encoding : Encoding) (data : Bytes) (value : Ext3)
    (h : decodeElement encoding data = some value) : data.length = elementBytes encoding := by
  cases encoding with
  | base => exact (decode_base_exact data value h).1
  | ext3 => exact (Spongefish.canonical_decode_preserves_raw_limbs data value h).1

theorem decode_ext3_keeps_all_three_raw_limbs (data : Bytes) (value : Ext3)
    (h : decodeElement .ext3 data = some value) :
    data.length = 24 ∧ value.val.c0 = Transcript.fromLe (data.take 8) ∧
      value.val.c1 = Transcript.fromLe ((data.drop 8).take 8) ∧
      value.val.c2 = Transcript.fromLe ((data.drop 16).take 8) :=
  Spongefish.canonical_decode_preserves_raw_limbs data value h

theorem decoded_elements_are_canonical (encoding : Encoding) (data : Bytes) (value : Ext3)
    (_h : decodeElement encoding data = some value) : Arithmetic.Canonical value.val := value.property

theorem decode_fields_exact_shape (encoding : Encoding) (count : Nat) (data : Bytes) (values : List Ext3)
    (h : decodeFields encoding count data = some values) :
    values.length = count ∧ data.length = count * elementBytes encoding := by
  induction count generalizing data values with
  | zero =>
      simp only [decodeFields] at h
      split at h
      · cases h
        have hn : data = [] := by cases data <;> simp_all
        simp [hn]
      · contradiction
  | succ count ih =>
      cases he : decodeElement encoding (data.take (elementBytes encoding)) with
      | none => simp [decodeFields,he] at h
      | some value =>
          cases ht : decodeFields encoding count (data.drop (elementBytes encoding)) with
          | none => simp [decodeFields,he,ht] at h
          | some tail =>
              simp only [decodeFields,he,ht,bind,Option.bind,pure,Option.some.injEq] at h
              subst values
              have hh := ih _ _ ht
              have hl := decode_element_exact_length encoding _ value he
              simp only [List.length_take,List.length_drop] at hl hh
              constructor
              · simp [hh.1]
              · rw [Nat.succ_mul]
                omega

theorem decoded_row_exact_columns_and_bytes (layout : Layout) (row : RawRow) (values : List Ext3)
    (h : decodeRow layout row = some values) :
    values.length = layout.columns ∧ row.bytes.length = rowBytes layout :=
  decode_fields_exact_shape layout.encoding layout.columns row.bytes values h

theorem decoded_row_all_canonical (layout : Layout) (row : RawRow) (values : List Ext3)
    (_h : decodeRow layout row = some values) : ∀ value ∈ values, Arithmetic.Canonical value.val :=
  fun value _ => value.property

theorem hint_read_same_slice (s t : State) (hints bytes : Bytes) (count : Nat)
    (h : Spongefish.proverHint s hints count = some (bytes,t)) :
    bytes = (hints.drop s.hintPos).take count := by
  unfold Spongefish.proverHint at h
  cases hr : Spongefish.readSlice hints s.hintPos count with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨data,pos⟩
      simp only [hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact (Spongefish.read_slice_success hints data s.hintPos count pos hr).2.1

theorem rows_success_exact (hints : Bytes) (size count : Nat) (s t : State) (rows : List RawRow)
    (hb : s.hintPos ≤ hints.length) (h : readRows hints size count s = some (rows,t)) :
    rows.length = count ∧ t.hintPos = s.hintPos + count * size ∧ t.hintPos ≤ hints.length ∧
      t.sponge = s.sponge ∧ t.transcriptPos = s.transcriptPos ∧ contiguousSlices hints size s.hintPos rows := by
  induction count generalizing s t rows with
  | zero =>
      cases h
      exact ⟨rfl,by simp,hb,rfl,rfl,True.intro⟩
  | succ count ih =>
      cases hr : Spongefish.proverHint s hints size with
      | none => simp [readRows,hr] at h
      | some pair =>
          rcases pair with ⟨bytes,next⟩
          cases ht : readRows hints size count next with
          | none => simp [readRows,hr,ht] at h
          | some pair =>
              rcases pair with ⟨tail,last⟩
              simp only [readRows,hr,ht,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              obtain ⟨hlen,hpos,hbound,htrans,hsponge⟩ := Spongefish.hint_is_not_absorbed s next hints bytes size hr
              have b := ih next last tail hbound ht
              refine ⟨by simp [b.1],?_,b.2.2.1,?_,?_,?_⟩
              · rw [b.2.1,hpos,Nat.succ_mul]
                omega
              · exact b.2.2.2.1.trans hsponge
              · exact b.2.2.2.2.1.trans htrans
              · exact ⟨rfl,hint_read_same_slice s next hints bytes size hr,hlen,by omega,
                  by simpa [hpos] using b.2.2.2.2.2⟩

theorem authentication_has_same_merkle_call (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (rows : List RawRow) (hints : Bytes) (s t : State)
    (h : authenticateRows hash root depth indices rows hints s = some t) :
    Merkle.verify hash root depth indices (rowHashes hash rows) hints s.hintPos = some t.hintPos ∧
      t.sponge = s.sponge ∧ t.transcriptPos = s.transcriptPos := by
  unfold authenticateRows at h
  cases hm : Merkle.verify hash root depth indices (rowHashes hash rows) hints s.hintPos with
  | none => simp [hm] at h
  | some offset =>
      simp only [hm,bind,Option.bind,pure,Option.some.injEq] at h
      subst t
      exact ⟨rfl,rfl,rfl⟩

theorem group_success_actual_sequence (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (h : openGroup hash root depth indices layout hints s = some (rows,t)) :
    ∃ afterPrefix afterRows,
      Spongefish.consumeVecPrefix s hints (indices.length * layout.columns) = some afterPrefix ∧
      readRows hints (rowBytes layout) indices.length afterPrefix = some (rows,afterRows) ∧
      authenticateRows hash root depth indices rows hints afterRows = some t := by
  unfold openGroup at h
  cases hp : Spongefish.consumeVecPrefix s hints (indices.length * layout.columns) with
  | none => simp [hp] at h
  | some prefState =>
      cases hr : readRows hints (rowBytes layout) indices.length prefState with
      | none => simp [hp,hr] at h
      | some pair =>
          rcases pair with ⟨actual,afterRows⟩
          cases hm : authenticateRows hash root depth indices actual hints afterRows with
          | none => simp [hp,hr,hm] at h
          | some last =>
              simp only [hp,hr,hm,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              exact ⟨prefState,afterRows,rfl,hr,hm⟩

theorem group_success_prefix_value (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (h : openGroup hash root depth indices layout hints s = some (rows,t)) :
    Transcript.fromLe ((hints.drop s.hintPos).take 8) = indices.length * layout.columns := by
  obtain ⟨prefState,_,hp,_,_⟩ := group_success_actual_sequence hash root depth indices layout hints s t rows h
  exact (Spongefish.vec_prefix_success_exact s prefState hints _ hp).2.2.2.2

theorem group_success_contiguous_rows (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (h : openGroup hash root depth indices layout hints s = some (rows,t)) :
    rows.length = indices.length ∧ contiguousSlices hints (rowBytes layout) (s.hintPos+8) rows := by
  obtain ⟨prefState,afterRows,hp,hr,_⟩ := group_success_actual_sequence hash root depth indices layout hints s t rows h
  have a := Spongefish.vec_prefix_success_exact s prefState hints _ hp
  have b := rows_success_exact hints (rowBytes layout) indices.length prefState afterRows rows a.2.1 hr
  exact ⟨b.1,by simpa [a.1] using b.2.2.2.2.2⟩

/-- The exact SAME caller root and query list reach the existing Merkle loop;
its leaves are hashes of the returned original row bytes. -/
theorem group_success_same_merkle_inputs (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (h : openGroup hash root depth indices layout hints s = some (rows,t)) :
    Merkle.verify hash root depth indices (rowHashes hash rows) hints
      (s.hintPos + 8 + indices.length * rowBytes layout) = some t.hintPos := by
  obtain ⟨prefState,afterRows,hp,hr,hm⟩ := group_success_actual_sequence hash root depth indices layout hints s t rows h
  have a := Spongefish.vec_prefix_success_exact s prefState hints _ hp
  have b := rows_success_exact hints (rowBytes layout) indices.length prefState afterRows rows a.2.1 hr
  have c := (authentication_has_same_merkle_call hash root depth indices rows hints afterRows t hm).1
  simpa [b.2.1,a.1] using c

/-- A nonempty opening computes the requested raw root at index zero. This is
execution of the existing layered verifier, not an assumption of hash binding. -/
theorem nonempty_group_requires_computed_root (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (hne : indices.isEmpty = false)
    (h : openGroup hash root depth indices layout hints s = some (rows,t)) :
    Merkle.ascending indices = true ∧
      Merkle.runLayers hash hints depth
        ((indices.zip (rowHashes hash rows)).map fun p => Merkle.Node.mk p.1 p.2)
        (s.hintPos + 8 + indices.length * rowBytes layout) = some ([⟨0,root⟩],t.hintPos) := by
  have hm := group_success_same_merkle_inputs hash root depth indices layout hints s t rows h
  exact (Merkle.nonempty_acceptance_requires_computed_root hash root depth indices
    (rowHashes hash rows) hints _ t.hintPos hne hm).2

theorem group_success_cursor_bounds (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (h : openGroup hash root depth indices layout hints s = some (rows,t)) :
    s.hintPos + 8 + indices.length * rowBytes layout ≤ t.hintPos ∧ t.hintPos ≤ hints.length ∧
      t.sponge = s.sponge ∧ t.transcriptPos = s.transcriptPos := by
  obtain ⟨prefState,afterRows,hp,hr,hm⟩ := group_success_actual_sequence hash root depth indices layout hints s t rows h
  have a := Spongefish.vec_prefix_success_exact s prefState hints _ hp
  have b := rows_success_exact hints (rowBytes layout) indices.length prefState afterRows rows a.2.1 hr
  have c := authentication_has_same_merkle_call hash root depth indices rows hints afterRows t hm
  have d := Merkle.accepted_opening_stays_in_slice hash root depth indices (rowHashes hash rows)
    hints afterRows.hintPos t.hintPos b.2.2.1 c.1
  exact ⟨by simpa [b.2.1,a.1] using d.1,d.2,
    c.2.1.trans (b.2.2.2.1.trans a.2.2.2.1),c.2.2.trans (b.2.2.2.2.1.trans a.2.2.1)⟩

theorem contiguous_slice_at (hints : Bytes) (size offset index : Nat) (rows : List RawRow) (row : RawRow)
    (hc : contiguousSlices hints size offset rows) (hi : rows.get? index = some row) :
    row.offset = offset + index * size ∧ row.bytes = (hints.drop row.offset).take size ∧
      row.bytes.length = size ∧ row.offset + size ≤ hints.length := by
  induction rows generalizing offset index with
  | nil => simp at hi
  | cons head tail ih =>
      rcases hc with ⟨hoff,hbytes,hlen,hbound,hrest⟩
      cases index with
      | zero =>
          cases hi
          simpa only [Nat.zero_mul,Nat.add_zero,hoff] using And.intro hoff (And.intro hbytes (And.intro hlen hbound))
      | succ index =>
          have ht := ih (offset+size) index hrest hi
          refine ⟨?_,ht.2⟩
          rw [ht.1,Nat.succ_mul]
          omega

theorem successful_row_is_original_hint_slice (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow) (index : Nat) (row : RawRow)
    (h : openGroup hash root depth indices layout hints s = some (rows,t)) (hi : rows.get? index = some row) :
    row.offset = s.hintPos + 8 + index * rowBytes layout ∧
      row.bytes = (hints.drop row.offset).take (rowBytes layout) ∧
      row.bytes.length = rowBytes layout ∧ row.offset + rowBytes layout ≤ hints.length :=
  contiguous_slice_at hints (rowBytes layout) (s.hintPos+8) index rows row
    (group_success_contiguous_rows hash root depth indices layout hints s t rows h).2 hi

/-- Decoding and leaf hashing are linked to the same original bytes without
assuming that equal hashes imply equal bytes. -/
theorem successful_decode_and_hash_same_slice (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (layout : Layout) (hints : Bytes) (s t : State)
    (rows : List RawRow) (index : Nat) (row : RawRow) (values : List Ext3)
    (h : openGroup hash root depth indices layout hints s = some (rows,t))
    (hi : rows.get? index = some row) (hd : decodeRow layout row = some values) :
    hash row.bytes = hash ((hints.drop row.offset).take (rowBytes layout)) ∧
      decodeFields layout.encoding layout.columns ((hints.drop row.offset).take (rowBytes layout)) = some values := by
  have hs := (successful_row_is_original_hint_slice hash root depth indices layout hints s t rows index row h hi).2.1
  exact ⟨congrArg hash hs,by simpa only [decodeRow,hs] using hd⟩

theorem successful_leaf_hash_is_original_slice_hash (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (index : Nat) (row : RawRow)
    (h : openGroup hash root depth indices layout hints s = some (rows,t)) (hi : rows.get? index = some row) :
    (rowHashes hash rows).get? index = some (hash ((hints.drop row.offset).take (rowBytes layout))) := by
  have hr := row_hash_at_same_position hash rows index row hi
  rw [(successful_row_is_original_hint_slice hash root depth indices layout hints s t rows index row h hi).2.1] at hr
  exact hr

theorem empty_group_is_only_vec_prefix (hash : Hash) (root : Digest) (depth : Nat)
    (layout : Layout) (hints : Bytes) (s : State) :
    openGroup hash root depth [] layout hints s =
      (Spongefish.consumeVecPrefix s hints 0).map (fun next => ([],next)) := by
  unfold openGroup
  simp only [List.length_nil,Nat.zero_mul]
  cases Spongefish.consumeVecPrefix s hints 0 <;>
    simp [readRows,authenticateRows,rowHashes,Merkle.verify]

theorem empty_group_consumes_exactly_eight (hash : Hash) (root : Digest) (depth : Nat)
    (layout : Layout) (hints : Bytes) (s t : State) (rows : List RawRow)
    (h : openGroup hash root depth [] layout hints s = some (rows,t)) :
    rows = [] ∧ t.hintPos = s.hintPos + 8 ∧ t.hintPos ≤ hints.length ∧
      t.sponge = s.sponge ∧ t.transcriptPos = s.transcriptPos := by
  rw [empty_group_is_only_vec_prefix] at h
  cases hp : Spongefish.consumeVecPrefix s hints 0 with
  | none => simp [hp] at h
  | some next =>
      simp only [hp,Option.map,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have a := Spongefish.vec_prefix_success_exact s next hints 0 hp
      exact ⟨rfl,a.1,a.2.1,a.2.2.2.1,a.2.2.1⟩

/-- Sequential raw group blocks for the split intermediate path. The immutable
query list is reused for each tree; only the returned state is threaded onward.
No round-RLC or field decoder is inserted between these groups. -/
def openGroups (hash : Hash) (depth : Nat) (indices : List Nat) (layout : Layout) (hints : Bytes) :
    List Digest → State → Option (List (List RawRow) × State)
  | [],s => some ([],s)
  | root :: roots,s => do
      let (rows,next) ← openGroup hash root depth indices layout hints s
      let (groups,last) ← openGroups hash depth indices layout hints roots next
      pure (rows::groups,last)

theorem groups_success_next_is_actual_returned_cursor (hash : Hash) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (root : Digest) (roots : List Digest) (s t : State)
    (groups : List (List RawRow))
    (h : openGroups hash depth indices layout hints (root::roots) s = some (groups,t)) :
    ∃ rows rest next, groups = rows::rest ∧
      openGroup hash root depth indices layout hints s = some (rows,next) ∧
      openGroups hash depth indices layout hints roots next = some (rest,t) := by
  cases hg : openGroup hash root depth indices layout hints s with
  | none => simp [openGroups,hg] at h
  | some pair =>
      rcases pair with ⟨rows,next⟩
      cases ht : openGroups hash depth indices layout hints roots next with
      | none => simp [openGroups,hg,ht] at h
      | some pair =>
          rcases pair with ⟨rest,last⟩
          simp only [openGroups,hg,ht,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          exact ⟨rows,rest,next,rfl,rfl,ht⟩

theorem groups_success_count_and_cursor (hash : Hash) (depth : Nat) (indices : List Nat)
    (layout : Layout) (hints : Bytes) (roots : List Digest) (s t : State) (groups : List (List RawRow))
    (hb : s.hintPos ≤ hints.length)
    (h : openGroups hash depth indices layout hints roots s = some (groups,t)) :
    groups.length = roots.length ∧ s.hintPos ≤ t.hintPos ∧ t.hintPos ≤ hints.length ∧
      t.sponge = s.sponge ∧ t.transcriptPos = s.transcriptPos := by
  induction roots generalizing s t groups with
  | nil =>
      cases h
      exact ⟨rfl,Nat.le_refl _,hb,rfl,rfl⟩
  | cons root roots ih =>
      obtain ⟨rows,rest,next,rfl,hg,ht⟩ :=
        groups_success_next_is_actual_returned_cursor hash depth indices layout hints root roots s t groups h
      have a := group_success_cursor_bounds hash root depth indices layout hints s next rows hg
      have b := ih next t rest a.2.1 ht
      have hs : s.hintPos ≤ next.hintPos :=
        Nat.le_trans (Nat.le_add_right s.hintPos 8)
          (Nat.le_trans (Nat.le_add_right (s.hintPos+8) (indices.length * rowBytes layout)) a.1)
      exact ⟨by simp [b.1],Nat.le_trans hs b.2.1,b.2.2.1,b.2.2.2.1.trans a.2.2.1,b.2.2.2.2.trans a.2.2.2⟩

/-- Nonconstant byte-projection fixture, not Keccak or a cryptographic proof. -/
def exampleHash : Hash := Merkle.exampleHash
def exampleStart : State := ⟨⟨Spongefish.zeroDigest,5⟩,13,0⟩
def exampleBaseRow : RawRow := ⟨8,Transcript.le 8 7⟩
def exampleBaseHints : Bytes := Transcript.le 8 1 ++ exampleBaseRow.bytes
def exampleBaseRoot : Digest := exampleHash exampleBaseRow.bytes

/-- A one-leaf tree with one ordinary canonical base-field row. -/
theorem base_row_open_example :
    openGroup exampleHash exampleBaseRoot 0 [0] ⟨.base,1⟩ exampleBaseHints exampleStart =
      some ([exampleBaseRow],{exampleStart with hintPos := 16}) := by decide

theorem base_row_decode_example :
    (decodeRow ⟨.base,1⟩ exampleBaseRow).map (List.map Subtype.val) = some [⟨7,0,0⟩] := by decide

def exampleExtRow : RawRow := ⟨8,Transcript.le 8 3 ++ Transcript.le 8 5 ++ Transcript.le 8 9⟩
def exampleExtHints : Bytes := Transcript.le 8 1 ++ exampleExtRow.bytes

theorem ext3_row_open_example :
    openGroup exampleHash (exampleHash exampleExtRow.bytes) 0 [0] ⟨.ext3,1⟩ exampleExtHints exampleStart =
      some ([exampleExtRow],{exampleStart with hintPos := 32}) := by decide

theorem ext3_three_limbs_decode_example :
    (decodeRow ⟨.ext3,1⟩ exampleExtRow).map (List.map Subtype.val) = some [⟨3,5,9⟩] := by decide

theorem empty_query_prefix_example :
    openGroup exampleHash exampleBaseRoot 4 [] ⟨.base,8⟩ (Transcript.le 8 0) exampleStart =
      some ([],{exampleStart with hintPos := 8}) := by decide

theorem two_groups_cursor_example :
    openGroups exampleHash 0 [0] ⟨.base,1⟩ (exampleBaseHints ++ exampleBaseHints)
      [exampleBaseRoot,exampleBaseRoot] exampleStart =
      some ([[exampleBaseRow],[⟨24,exampleBaseRow.bytes⟩]],{exampleStart with hintPos := 32}) := by decide

def exampleSibling : Digest := Merkle.exampleDigest ⟨11,by decide⟩

set_option maxRecDepth 4096 in
/-- The unpaired leaf consumes its sibling immediately after the row payload,
without an invented multiproof Vec header. -/
theorem lone_leaf_sibling_cursor_example :
    openGroup exampleHash (Merkle.parent exampleHash 1 exampleBaseRoot exampleSibling) 1 [1]
      ⟨.base,1⟩ (exampleBaseHints ++ exampleSibling.val) exampleStart =
      some ([exampleBaseRow],{exampleStart with hintPos := 48}) := by
  simp [openGroup,Spongefish.consumeVecPrefix,Spongefish.proverHint,Spongefish.readSlice,
    readRows,authenticateRows,rowHashes,Merkle.verify,Merkle.runLayers,Merkle.processLayer,
    Merkle.readDigest,Merkle.ascending,exampleBaseHints,exampleBaseRow,exampleStart,
    rowBytes,elementBytes,Transcript.le,Transcript.fromLe,exampleSibling,
    Merkle.exampleDigest,Merkle.merged,exampleBaseRoot,exampleHash,Merkle.exampleHash,
    Merkle.parent,Merkle.parentInput]

end Audit.Wire3.WhirRows
