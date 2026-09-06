import Audit.Wire3.Transcript

/-!
Executable wire-v3 compact *framing validator*, not a full MleProof verifier.
Source: `src/compact_v2.rs::{Reader,decode_compact_v2}` and
`contracts/src/CompactMleProofV2.sol`. This models actual byte consumption,
little-endian headers, canonical limbs (strict mode), opaque stream limits,
trusted-dimension vector layout, and exact exhaustion. The result is a list of
decoded chunks rather than Rust structs or EVM memory pointers. The trusted
Shape must be validated by its caller: this file does not duplicate all circuit
configuration validity or WHIR interaction-pattern reconstruction.

`canonical = false` models the core-bound decoder's deferred limb comparison;
it deliberately does not imply canonical fields or proof validity. The caller
must run the current core before using that result. Nat arithmetic plus an
explicit 64-bit cursor bound models successful host reads; actual Solidity
assembly instruction/memory safety and cross-language refinement remain open.
-/
namespace Audit.Wire3.Compact
open Audit.Wire3.Transcript

def maxProofBytes : Nat := 253921
def maxNargBytes : Nat := 1904
def maxHintBytes : Nat := 112408
def magic : Bytes := ascii "MLEWHIR3"

def take (encoded : Bytes) (offset count : Nat) : Option (Bytes × Nat) :=
  if offset + count ≤ encoded.length ∧ offset + count < u64Limit then
    some ((encoded.drop offset).take count, offset + count)
  else none

theorem take_success (encoded data : Bytes) (offset count next : Nat)
    (h : take encoded offset count = some (data, next)) :
    next = offset + count ∧ offset ≤ next ∧ next ≤ encoded.length ∧
      next < u64Limit ∧ data.length = count ∧ data = (encoded.drop offset).take count := by
  unfold take at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have havail : count ≤ (encoded.drop offset).length := by
      simp only [List.length_drop]
      omega
    exact ⟨rfl, by omega, hb.1, hb.2, List.length_take_of_le havail, rfl⟩
  · simp at h

theorem take_rejects_truncation (encoded : Bytes) (offset count : Nat)
    (h : encoded.length < offset + count) : take encoded offset count = none := by
  simp [take, show ¬offset + count ≤ encoded.length by omega]

def readUInt (encoded : Bytes) (offset width : Nat) : Option (Nat × Nat) := do
  let (bytes, next) ← take encoded offset width
  pure (fromLe bytes, next)

theorem read_uint_success (encoded : Bytes) (offset width value next : Nat)
    (h : readUInt encoded offset width = some (value, next)) :
    next = offset + width ∧ next ≤ encoded.length ∧ next < u64Limit ∧
      value = fromLe ((encoded.drop offset).take width) := by
  unfold readUInt at h
  cases ht : take encoded offset width with
  | none => simp [ht] at h
  | some pair =>
    rcases pair with ⟨bytes, endOffset⟩
    simp [ht] at h
    rcases h with ⟨rfl, rfl⟩
    have a := take_success encoded bytes offset width endOffset ht
    exact ⟨a.1, a.2.2.1, a.2.2.2.1, by rw [a.2.2.2.2.2]⟩

def readField (canonical : Bool) (encoded : Bytes) (offset : Nat) : Option (Nat × Nat) := do
  let (x, next) ← readUInt encoded offset 8
  if !canonical || decide (x < modulus) then pure (x, next) else none

theorem read_field_success (canonical : Bool) (encoded : Bytes) (offset value next : Nat)
    (h : readField canonical encoded offset = some (value, next)) :
    next = offset + 8 ∧ next ≤ encoded.length ∧
      (canonical = true → value < modulus) := by
  unfold readField at h
  cases hr : readUInt encoded offset 8 with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨x, endOffset⟩
    simp only [Option.bind_eq_bind, hr, Option.bind] at h
    split at h
    · rename_i hc
      change some (x, endOffset) = some (value, next) at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have a := read_uint_success encoded offset 8 x endOffset hr
      exact ⟨a.1, a.2.1, by intro hcanon; simpa [hcanon] using hc⟩
    · simp at h

def readFields (canonical : Bool) (encoded : Bytes) : Nat → Nat → Option (List Nat × Nat)
  | 0, offset => some ([], offset)
  | n + 1, offset => do
    let (x, mid) ← readField canonical encoded offset
    let (xs, next) ← readFields canonical encoded n mid
    pure (x :: xs, next)

theorem read_fields_success (canonical : Bool) (encoded : Bytes) (count offset next : Nat)
    (values : List Nat) (h : readFields canonical encoded count offset = some (values, next)) :
    values.length = count ∧ next = offset + 8 * count ∧
      (canonical = true → ∀ x ∈ values, x < modulus) := by
  induction count generalizing offset next values with
  | zero => simp [readFields] at h; rcases h with ⟨rfl, rfl⟩; simp
  | succ count ih =>
    unfold readFields at h
    cases hf : readField canonical encoded offset with
    | none => simp [hf] at h
    | some pair =>
      rcases pair with ⟨x, mid⟩
      cases hs : readFields canonical encoded count mid with
      | none => simp [hf, hs] at h
      | some pair =>
        rcases pair with ⟨xs, endOffset⟩
        simp [hf, hs] at h
        rcases h with ⟨rfl, rfl⟩
        have a := read_field_success canonical encoded offset x mid hf
        have b := ih mid endOffset xs hs
        refine ⟨by simp [b.1], by omega, ?_⟩
        intro hc y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact a.2.2 hc
        · exact b.2.2 hc y hy

def readBlob (encoded : Bytes) (offset maximum : Nat) : Option (Bytes × Nat) := do
  let (length, mid) ← readUInt encoded offset 4
  if length ≤ maximum then take encoded mid length else none

theorem read_blob_success (encoded blob : Bytes) (offset maximum next : Nat)
    (h : readBlob encoded offset maximum = some (blob, next)) :
    blob.length ≤ maximum ∧ next = offset + 4 + blob.length ∧ next ≤ encoded.length := by
  unfold readBlob at h
  cases hr : readUInt encoded offset 4 with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨length, mid⟩
    simp only [Option.bind_eq_bind, hr, Option.bind] at h
    split at h
    · rename_i hc
      have a := read_uint_success encoded offset 4 length mid hr
      have b := take_success encoded blob mid length next h
      exact ⟨by omega, by omega, b.2.2.1⟩
    · simp at h

inductive Command where
  | raw (count : Nat)
  | fields (count : Nat)
  | blob (maximum : Nat)

inductive Chunk where
  | bytes (value : Bytes)
  | fields (value : List Nat)

def runCommand (canonical : Bool) (encoded : Bytes) (offset : Nat) : Command → Option (Chunk × Nat)
  | .raw count => do
      let (bs, next) ← take encoded offset count
      pure (.bytes bs, next)
  | .fields count => do
      let (xs, next) ← readFields canonical encoded count offset
      pure (.fields xs, next)
  | .blob maximum => do
      let (bs, next) ← readBlob encoded offset maximum
      pure (.bytes bs, next)

def runCommands (canonical : Bool) (encoded : Bytes) : List Command → Nat → Option (List Chunk × Nat)
  | [], offset => some ([], offset)
  | cmd :: cmds, offset => do
      let (x, mid) ← runCommand canonical encoded offset cmd
      let (xs, next) ← runCommands canonical encoded cmds mid
      pure (x :: xs, next)

def CanonicalChunk : Chunk → Prop
  | .bytes _ => True
  | .fields xs => ∀ x ∈ xs, x < modulus

theorem command_strict_fields_canonical (encoded : Bytes) (offset next : Nat)
    (cmd : Command) (chunk : Chunk) (h : runCommand true encoded offset cmd = some (chunk, next)) :
    CanonicalChunk chunk := by
  cases cmd with
  | raw count =>
    unfold runCommand at h
    cases hr : take encoded offset count with
    | none => simp [hr] at h
    | some pair =>
      rcases pair with ⟨bs, endOffset⟩
      simp [hr] at h
      rcases h with ⟨rfl, rfl⟩
      trivial
  | fields count =>
    unfold runCommand at h
    cases hr : readFields true encoded count offset with
    | none => simp [hr] at h
    | some pair =>
      rcases pair with ⟨xs, endOffset⟩
      simp [hr] at h
      rcases h with ⟨rfl, rfl⟩
      exact (read_fields_success true encoded count offset endOffset xs hr).2.2 rfl
  | blob maximum =>
    unfold runCommand at h
    cases hr : readBlob encoded offset maximum with
    | none => simp [hr] at h
    | some pair =>
      rcases pair with ⟨bs, endOffset⟩
      simp [hr] at h
      rcases h with ⟨rfl, rfl⟩
      trivial

theorem commands_strict_fields_canonical (encoded : Bytes) (offset next : Nat)
    (cmds : List Command) (chunks : List Chunk)
    (h : runCommands true encoded cmds offset = some (chunks, next)) :
    ∀ chunk ∈ chunks, CanonicalChunk chunk := by
  induction cmds generalizing offset next chunks with
  | nil => simp [runCommands] at h; rcases h with ⟨rfl, rfl⟩; simp
  | cons cmd cmds ih =>
    unfold runCommands at h
    cases hr : runCommand true encoded offset cmd with
    | none => simp [hr] at h
    | some pair =>
      rcases pair with ⟨x, mid⟩
      cases hs : runCommands true encoded cmds mid with
      | none => simp [hr, hs] at h
      | some pair =>
        rcases pair with ⟨xs, endOffset⟩
        simp [hr, hs] at h
        rcases h with ⟨rfl, rfl⟩
        intro chunk hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact command_strict_fields_canonical encoded offset mid cmd chunk hr
        · exact ih mid endOffset xs hs chunk hc

structure Shape where
  degreeBits : Nat
  numConstants : Nat
  numRoutedWires : Nat
  numWires : Nat
  numPublicInputs : Nat
  gateRoundDegree : Nat

def width (s : Shape) : Nat := max (max (s.numConstants + s.numRoutedWires) s.numWires) (2 * s.numRoutedWires)

/-- Root/blob order and flattened c0,c1,c2 limb counts are the current grammar. -/
def bodyCommands (s : Shape) : List Command :=
  [.fields 4, .fields s.numPublicInputs, .raw 32, .raw 32, .raw 32,
   .blob maxNargBytes, .blob maxHintBytes,
   .fields (3 * (s.degreeBits * 5)),
   .fields (3 * (s.numConstants + s.numRoutedWires)), .fields (3 * s.numWires),
   .fields (3 * (2 * s.numRoutedWires)),
   .fields (3 * (s.degreeBits * s.gateRoundDegree)),
   .fields (3 * (s.numConstants + s.numRoutedWires)), .fields (3 * s.numWires)]

def header (encoded : Bytes) (s : Shape) : Option Nat := do
  if encoded.length > maxProofBytes then none else do
    let (m, afterMagic) ← take encoded 0 8
    if m ≠ magic then none else do
      let (version, afterVersion) ← readUInt encoded afterMagic 8
      if version ≠ 3 then none else do
        let (w, afterWidth) ← readUInt encoded afterVersion 4
        if w ≠ width s then none else pure afterWidth

def finish (encoded : Bytes) (offset : Nat) : Option Unit :=
  if offset = encoded.length then some () else none

theorem header_success (encoded : Bytes) (s : Shape) (next : Nat)
    (h : header encoded s = some next) :
    encoded.length ≤ maxProofBytes ∧ next = 20 ∧
      encoded.take 8 = magic ∧ fromLe ((encoded.drop 8).take 8) = 3 ∧
      fromLe ((encoded.drop 16).take 4) = width s := by
  unfold header at h
  split at h
  · simp at h
  · rename_i hcap
    cases ht : take encoded 0 8 with
    | none => simp [ht] at h
    | some pair =>
      rcases pair with ⟨m, afterMagic⟩
      simp only [Option.bind_eq_bind, ht, Option.bind] at h
      split at h
      · simp at h
      · rename_i hm
        have am := take_success encoded m 0 8 afterMagic ht
        have ha : afterMagic = 8 := by omega
        subst afterMagic
        cases hv : readUInt encoded 8 8 with
        | none => simp [hv] at h
        | some pair =>
          rcases pair with ⟨version, afterVersion⟩
          simp only [hv, Option.bind] at h
          split at h
          · simp at h
          · rename_i hver
            have av := read_uint_success encoded 8 8 version afterVersion hv
            have hav : afterVersion = 16 := by omega
            subst afterVersion
            cases hw : readUInt encoded 16 4 with
            | none => simp [hw] at h
            | some pair =>
              rcases pair with ⟨w, afterWidth⟩
              simp only [hw, Option.bind] at h
              split at h
              · simp at h
              · rename_i hwidth
                change some afterWidth = some next at h
                simp only [Option.some.injEq] at h
                subst afterWidth
                have aw := read_uint_success encoded 16 4 w next hw
                refine ⟨by omega, by omega, ?_, ?_, ?_⟩
                · have hm' : m = magic := by simpa using hm
                  simpa only [List.drop_zero, hm'] using am.2.2.2.2.2.symm
                · exact av.2.2.2.symm.trans (by simpa using hver)
                · exact aw.2.2.2.symm.trans (by simpa using hwidth)

def validate (canonical : Bool) (encoded : Bytes) (s : Shape) : Option (List Chunk) := do
  let start ← header encoded s
  let (chunks, next) ← runCommands canonical encoded (bodyCommands s) start
  let _ ← finish encoded next
  pure chunks

theorem finish_iff_exact_exhaustion (encoded : Bytes) (offset : Nat) :
    finish encoded offset = some () ↔ offset = encoded.length := by
  simp [finish]

theorem validation_requires_exact_exhaustion (canonical : Bool) (encoded : Bytes)
    (s : Shape) (chunks : List Chunk) (h : validate canonical encoded s = some chunks) :
    ∃ start, header encoded s = some start ∧
      runCommands canonical encoded (bodyCommands s) start = some (chunks, encoded.length) := by
  unfold validate at h
  cases hh : header encoded s with
  | none => simp [hh] at h
  | some start =>
    cases hr : runCommands canonical encoded (bodyCommands s) start with
    | none => simp [hh, hr] at h
    | some pair =>
      rcases pair with ⟨xs, next⟩
      cases hf : finish encoded next with
      | none => simp [hh, hr, hf] at h
      | some resultUnit =>
        cases resultUnit
        have heq := (finish_iff_exact_exhaustion encoded next).mp hf
        simp [hh, hr, hf] at h
        subst next
        subst xs
        exact ⟨start, rfl, hr⟩

theorem trailing_bytes_rejected_at_finish (encoded : Bytes) (offset : Nat)
    (h : offset < encoded.length) : finish encoded offset = none := by
  simp [finish, show offset ≠ encoded.length by omega]

theorem current_header_required_for_validation (canonical : Bool) (encoded : Bytes)
    (s : Shape) (chunks : List Chunk) (h : validate canonical encoded s = some chunks) :
    encoded.length ≤ maxProofBytes ∧ encoded.take 8 = magic ∧
      fromLe ((encoded.drop 8).take 8) = 3 ∧
      fromLe ((encoded.drop 16).take 4) = width s := by
  rcases validation_requires_exact_exhaustion canonical encoded s chunks h with ⟨start, hh, _⟩
  have a := header_success encoded s start hh
  exact ⟨a.1, a.2.2⟩

theorem strict_validation_all_fields_canonical (encoded : Bytes) (s : Shape) (chunks : List Chunk)
    (h : validate true encoded s = some chunks) : ∀ chunk ∈ chunks, CanonicalChunk chunk := by
  rcases validation_requires_exact_exhaustion true encoded s chunks h with ⟨start, _, hr⟩
  exact commands_strict_fields_canonical encoded start encoded.length (bodyCommands s) chunks hr

theorem wrong_version_rejected (canonical : Bool) (encoded : Bytes) (s : Shape)
    (hversion : fromLe ((encoded.drop 8).take 8) ≠ 3) : validate canonical encoded s = none := by
  cases hv : validate canonical encoded s with
  | none => rfl
  | some chunks =>
    have a := current_header_required_for_validation canonical encoded s chunks hv
    exact False.elim (hversion a.2.2.1)

/-- A successful ordinary header, not a cryptographic proof fixture. -/
theorem current_header_positive :
    header (magic ++ le 8 3 ++ le 4 1) ⟨1, 1, 0, 1, 0, 3⟩ = some 20 := by decide

theorem canonical_limb_positive : readField true (le 8 7) 0 = some (7, 8) := by decide

theorem noncanonical_limb_rejected : readField true (le 8 modulus) 0 = none := by decide

/-- Deferral is intentional: compact framing alone is not the core verifier. -/
theorem core_bound_limb_deferral_is_not_canonical_validation :
    readField false (le 8 modulus) 0 = some (modulus, 8) := by decide

end Audit.Wire3.Compact
