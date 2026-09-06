import Audit.Wire3.Transcript

/-!
Executable layered decommitment model at becfe98e.
Source: SpongefishMerkle.verify/_processLayerInto. Digests retain their 32 raw
bytes (no little-endian reinterpretation of bytes32). Parent hashing uses the
ordered 64 bytes left || right. Hints are a bounded byte slice, and each lone
node consumes exactly 32 bytes. Paired adjacent siblings consume no hint.
Indices are mathematical naturals; the production boundary additionally gives
uint256 indices/depths. Functional lists replace the alternating in-place arrays.
The empty opening returns its input offset, exactly like the source helper;
WHIR sampling/nonempty-query guarantees are NOT inferred here.

The path collision reduction below needs NO injectivity axiom for Keccak: two
same-index, same-depth paths with the same root either have the same leaf hash,
or exhibit an unequal pair of 64-byte inputs hashing equally along those paths.
This is a deterministic conditional reduction, not a collision probability,
leaf-preimage binding, full multiproof path-extraction theorem, or PCS soundness
within THIS foundational module. MerkleExtraction now derives paths from this
same layered execution; WhirRows/WhirRowBinding connect actual raw row reads and
decoding to it. Yul/bytecode refinement, complete WHIR integration and replacement
of WhirTerminal.authenticate in a full verifier remain separate obligations.
-/
namespace Audit.Wire3.Merkle

abbrev Bytes := Transcript.Bytes
abbrev Digest := { bytes : Bytes // bytes.length = 32 }
abbrev Hash := Bytes → Digest

def parentInput (index : Nat) (current sibling : Digest) : Bytes :=
  if index % 2 = 0 then current.val ++ sibling.val else sibling.val ++ current.val

def parent (hash : Hash) (index : Nat) (current sibling : Digest) : Digest :=
  hash (parentInput index current sibling)

theorem parent_input_length (i : Nat) (a b : Digest) :
    (parentInput i a b).length = 64 := by
  unfold parentInput
  split <;> simp [a.property, b.property]

theorem parent_input_binds_current (i : Nat) (a b s t : Digest)
    (h : parentInput i a s = parentInput i b t) : a = b := by
  apply Subtype.eq
  unfold parentInput at h
  split at h
  · exact List.append_inj_left h (a.property.trans b.property.symm)
  · exact List.append_inj_right h (s.property.trans t.property.symm)

theorem parent_input_binds_sibling (i : Nat) (a b s t : Digest)
    (h : parentInput i a s = parentInput i b t) : s = t := by
  apply Subtype.eq
  unfold parentInput at h
  split at h
  · exact List.append_inj_right h (a.property.trans b.property.symm)
  · exact List.append_inj_left h (s.property.trans t.property.symm)

def readDigest (hints : Bytes) (offset : Nat) : Option (Digest × Nat) :=
  if h : offset ≤ hints.length ∧ 32 ≤ hints.length - offset then
    some (⟨(hints.drop offset).take 32, by
      rw [List.length_take, List.length_drop]
      exact Nat.min_eq_left h.2⟩, offset + 32)
  else none

theorem read_success_exact (hints : Bytes) (offset next : Nat) (d : Digest)
    (h : readDigest hints offset = some (d, next)) :
    next = offset + 32 ∧ offset ≤ next ∧ next ≤ hints.length ∧
      d.val = (hints.drop offset).take 32 := by
  unfold readDigest at h
  split at h
  · cases h
    exact ⟨rfl, by omega, by omega, rfl⟩
  · contradiction

theorem insufficient_hint_rejected (hints : Bytes) (offset : Nat)
    (h : hints.length < offset + 32) : readDigest hints offset = none := by
  simp only [readDigest]
  split
  · omega
  · rfl

structure Node where
  index : Nat
  digest : Digest
  deriving DecidableEq

def merged (hash : Hash) (a : Node) (sibling : Digest) : Node :=
  ⟨a.index / 2, parent hash a.index a.digest sibling⟩

def ascending : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && ascending (b :: rest)

def processLayer (hash : Hash) (hints : Bytes) : List Node → Nat → Option (List Node × Nat)
  | [], offset => some ([], offset)
  | [a], offset => do
      let (sibling, next) ← readDigest hints offset
      pure ([merged hash a sibling], next)
  | a :: b :: tail, offset =>
      if b.index = Nat.xor a.index 1 then do
        let (parents, next) ← processLayer hash hints tail offset
        pure (merged hash a b.digest :: parents, next)
      else do
        let (sibling, afterRead) ← readDigest hints offset
        let (parents, next) ← processLayer hash hints (b :: tail) afterRead
        pure (merged hash a sibling :: parents, next)
termination_by nodes _ => nodes.length

def runLayers (hash : Hash) (hints : Bytes) : Nat → List Node → Nat → Option (List Node × Nat)
  | 0, nodes, offset => some (nodes, offset)
  | depth + 1, nodes, offset => do
      let (parents, next) ← processLayer hash hints nodes offset
      runLayers hash hints depth parents next

def verify (hash : Hash) (root : Digest) (depth : Nat) (indices : List Nat)
    (leaves : List Digest) (hints : Bytes) (offset : Nat) : Option Nat :=
  if indices.length ≠ leaves.length then none
  else if indices.isEmpty then some offset
  else if ascending indices = false then none
  else do
    let (nodes, next) ← runLayers hash hints depth
      ((indices.zip leaves).map fun p => Node.mk p.1 p.2) offset
    if nodes = [⟨0, root⟩] then some next else none

theorem mismatched_lengths_rejected (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (leaves : List Digest) (hints : Bytes) (offset : Nat)
    (h : indices.length ≠ leaves.length) :
    verify hash root depth indices leaves hints offset = none := by simp [verify, h]

theorem empty_opening_preserves_offset (hash : Hash) (root : Digest) (depth : Nat)
    (hints : Bytes) (offset : Nat) :
    verify hash root depth [] [] hints offset = some offset := by simp [verify]

theorem adjacent_nonascending_rejected (a b : Nat) (rest : List Nat) (h : b ≤ a) :
    ascending (a :: b :: rest) = false := by simp [ascending, Nat.not_lt.mpr h]

theorem paired_nodes_read_no_hint (hash : Hash) (hints : Bytes) (a b : Node) (offset : Nat)
    (h : b.index = Nat.xor a.index 1) :
    processLayer hash hints [a, b] offset = some ([merged hash a b.digest], offset) := by
  simp [processLayer, h]

theorem lone_node_reads_exact_digest (hash : Hash) (hints : Bytes) (a : Node)
    (offset next : Nat) (sibling : Digest)
    (h : readDigest hints offset = some (sibling, next)) :
    processLayer hash hints [a] offset = some ([merged hash a sibling], next) := by
  simp [processLayer, h]

theorem zero_layers_unchanged (hash : Hash) (hints : Bytes) (nodes : List Node) (offset : Nat) :
    runLayers hash hints 0 nodes offset = some (nodes, offset) := rfl

/-- No successful step moves backwards; if it consumes bytes, it stays in the
    supplied hints slice. The no-read case preserves even an arbitrary offset. -/
def CursorProgress (length before after : Nat) : Prop :=
  before ≤ after ∧ (after = before ∨ after ≤ length)

theorem cursor_progress_trans (length a b c : Nat)
    (hab : CursorProgress length a b) (hbc : CursorProgress length b c) :
    CursorProgress length a c := by
  rcases hab with ⟨hab, rfl | hb⟩ <;> rcases hbc with ⟨hbc, rfl | hc⟩ <;>
    constructor <;> omega

theorem read_cursor_progress (hints : Bytes) (offset next : Nat) (d : Digest)
    (h : readDigest hints offset = some (d, next)) : CursorProgress hints.length offset next := by
  have hr := read_success_exact hints offset next d h
  exact ⟨hr.2.1, Or.inr hr.2.2.1⟩

theorem layer_cursor_progress (hash : Hash) (hints : Bytes) (nodes parents : List Node)
    (offset next : Nat) (h : processLayer hash hints nodes offset = some (parents, next)) :
    CursorProgress hints.length offset next := by
  cases nodes with
  | nil =>
      simp [processLayer] at h
      rw [← h.2]
      exact ⟨Nat.le_refl _, Or.inl rfl⟩
  | cons a rest =>
      cases rest with
      | nil =>
          cases hr : readDigest hints offset with
          | none => simp [processLayer, hr] at h
          | some result =>
              rcases result with ⟨d, afterRead⟩
              simp [processLayer, hr] at h
              rw [← h.2]
              exact read_cursor_progress hints offset afterRead d hr
      | cons b tail =>
          by_cases paired : b.index = Nat.xor a.index 1
          · cases hp : processLayer hash hints tail offset with
            | none => simp [processLayer, paired, hp] at h
            | some result =>
                rcases result with ⟨remaining, afterLayer⟩
                simp [processLayer, paired, hp] at h
                rw [← h.2]
                exact layer_cursor_progress hash hints tail remaining offset afterLayer hp
          · cases hr : readDigest hints offset with
            | none => simp [processLayer, paired, hr] at h
            | some result =>
                rcases result with ⟨d, afterRead⟩
                cases hp : processLayer hash hints (b :: tail) afterRead with
                | none => simp [processLayer, paired, hr, hp] at h
                | some result =>
                    rcases result with ⟨remaining, afterLayer⟩
                    simp [processLayer, paired, hr, hp] at h
                    rw [← h.2]
                    exact cursor_progress_trans hints.length offset afterRead afterLayer
                      (read_cursor_progress hints offset afterRead d hr)
                      (layer_cursor_progress hash hints (b :: tail) remaining afterRead afterLayer hp)
termination_by nodes.length

theorem all_layers_cursor_progress (hash : Hash) (hints : Bytes) (depth : Nat)
    (nodes parents : List Node) (offset next : Nat)
    (h : runLayers hash hints depth nodes offset = some (parents, next)) :
    CursorProgress hints.length offset next := by
  induction depth generalizing nodes offset with
  | zero =>
      cases h
      exact ⟨Nat.le_refl _, Or.inl rfl⟩
  | succ depth ih =>
      cases hp : processLayer hash hints nodes offset with
      | none => simp [runLayers, hp] at h
      | some result =>
          rcases result with ⟨remaining, afterLayer⟩
          simp only [runLayers, hp, bind, Option.bind] at h
          exact cursor_progress_trans hints.length offset afterLayer next
            (layer_cursor_progress hash hints nodes remaining offset afterLayer hp)
            (ih remaining afterLayer h)

theorem nonempty_acceptance_requires_computed_root (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (leaves : List Digest) (hints : Bytes) (offset next : Nat)
    (hne : indices.isEmpty = false)
    (h : verify hash root depth indices leaves hints offset = some next) :
    indices.length = leaves.length ∧ ascending indices = true ∧
    runLayers hash hints depth ((indices.zip leaves).map fun p => Node.mk p.1 p.2) offset =
      some ([⟨0, root⟩], next) := by
  unfold verify at h
  split at h
  · contradiction
  next lengths =>
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · contradiction
    next ordered =>
      cases he : runLayers hash hints depth
          ((indices.zip leaves).map fun p => Node.mk p.1 p.2) offset with
      | none => simp [he] at h
      | some result =>
        rcases result with ⟨nodes, afterLayers⟩
        simp only [he, bind, Option.bind] at h
        split at h
        · cases h
          exact ⟨by simpa using lengths, by simpa using ordered, by
            simp only [‹nodes = [⟨0, root⟩]›]⟩
        · contradiction

theorem accepted_opening_cursor_progress (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (leaves : List Digest) (hints : Bytes) (offset next : Nat)
    (h : verify hash root depth indices leaves hints offset = some next) :
    CursorProgress hints.length offset next := by
  by_cases empty : indices.isEmpty = true
  · have nil : indices = [] := by cases indices <;> simp_all
    subst indices
    cases leaves with
    | nil =>
        simp [verify] at h
        subst next
        exact ⟨Nat.le_refl _, Or.inl rfl⟩
    | cons _ _ => simp [verify] at h
  · have hr := nonempty_acceptance_requires_computed_root hash root depth indices leaves hints
      offset next (by simpa using empty) h
    exact all_layers_cursor_progress hash hints depth _ _ offset next hr.2.2

theorem accepted_opening_stays_in_slice (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (leaves : List Digest) (hints : Bytes) (offset next : Nat)
    (hoff : offset ≤ hints.length)
    (h : verify hash root depth indices leaves hints offset = some next) :
    offset ≤ next ∧ next ≤ hints.length := by
  rcases accepted_opening_cursor_progress hash root depth indices leaves hints offset next h with ⟨h1, h2⟩
  exact ⟨h1, by rcases h2 with rfl | h2; exact hoff; exact h2⟩

def pathRoot (hash : Hash) : Nat → Digest → List Digest → Digest
  | _, leaf, [] => leaf
  | index, leaf, sibling :: rest =>
      pathRoot hash (index / 2) (parent hash index leaf sibling) rest

/-- Only compression inputs actually compared along these two paths. -/
def PathCollision (hash : Hash) : Nat → Digest → List Digest → Digest → List Digest → Prop
  | _, _, [], _, _ => False
  | _, _, _, _, [] => False
  | i, a, s :: ss, b, t :: ts =>
      (parentInput i a s ≠ parentInput i b t ∧ parent hash i a s = parent hash i b t) ∨
        PathCollision hash (i / 2) (parent hash i a s) ss (parent hash i b t) ts

theorem same_root_same_leaf_or_path_collision (hash : Hash) (siblings : List Digest)
    (index : Nat) (leaf other : Digest) (otherSiblings : List Digest)
    (hlen : siblings.length = otherSiblings.length)
    (hroot : pathRoot hash index leaf siblings = pathRoot hash index other otherSiblings) :
    leaf = other ∨ PathCollision hash index leaf siblings other otherSiblings := by
  induction siblings generalizing index leaf other otherSiblings with
  | nil =>
      cases otherSiblings with
      | nil => exact Or.inl hroot
      | cons _ _ => simp at hlen
  | cons s ss ih =>
      cases otherSiblings with
      | nil => simp at hlen
      | cons t ts =>
          by_cases leaves : leaf = other
          · exact Or.inl leaves
          · right
            have result := ih (index / 2) (parent hash index leaf s)
              (parent hash index other t) ts (by simpa using hlen) hroot
            rcases result with parents | collision
            · exact Or.inl ⟨fun inputs => leaves (parent_input_binds_current index leaf other s t inputs), parents⟩
            · exact Or.inr collision

theorem no_path_collision_forces_same_leaf (hash : Hash) (siblings : List Digest)
    (index : Nat) (leaf other : Digest) (otherSiblings : List Digest)
    (hlen : siblings.length = otherSiblings.length)
    (hroot : pathRoot hash index leaf siblings = pathRoot hash index other otherSiblings)
    (hno : ¬ PathCollision hash index leaf siblings other otherSiblings) : leaf = other := by
  exact (same_root_same_leaf_or_path_collision hash siblings index leaf other otherSiblings hlen hroot).resolve_right hno

theorem path_collision_exposes_hash_collision (hash : Hash) (siblings : List Digest)
    (index : Nat) (leaf other : Digest) (otherSiblings : List Digest)
    (h : PathCollision hash index leaf siblings other otherSiblings) :
    ∃ a b : Bytes, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b := by
  induction siblings generalizing index leaf other otherSiblings with
  | nil => simp [PathCollision] at h
  | cons s ss ih =>
      cases otherSiblings with
      | nil => contradiction
      | cons t ts =>
          rcases h with h | h
          · exact ⟨parentInput index leaf s, parentInput index other t,
              parent_input_length _ _ _, parent_input_length _ _ _, h.1, h.2⟩
          · exact ih (index / 2) (parent hash index leaf s) (parent hash index other t) ts h

/-- A ordinary adjacent pair uses a nonconstant projection hash to exercise
    the concrete 64-byte compression and root path; not a cryptographic fixture. -/
def exampleDigest (byte : Transcript.Byte) : Digest :=
  ⟨List.replicate 32 byte, by simp⟩

def exampleHash : Hash := fun bytes =>
  ⟨(bytes ++ (exampleDigest ⟨0, by decide⟩).val).take 32, by
    simp only [List.length_take, List.length_append, (exampleDigest ⟨0, by decide⟩).property]
    omega⟩

theorem positive_adjacent_pair :
    let a := exampleDigest ⟨3, by decide⟩
    let b := exampleDigest ⟨7, by decide⟩
    verify exampleHash (parent exampleHash 0 a b) 1 [0, 1] [a, b] [] 0 = some 0 := by
  have hx : Nat.xor 0 1 = 1 := by decide
  simp [verify, runLayers, processLayer, ascending, merged, hx]

theorem positive_lone_node :
    let a := exampleDigest ⟨3, by decide⟩
    let b := exampleDigest ⟨7, by decide⟩
    verify exampleHash (parent exampleHash 1 a b) 1 [1] [a] b.val 0 = some 32 := by
  simp [verify, runLayers, processLayer, ascending, merged, readDigest, exampleDigest]

end Audit.Wire3.Merkle
