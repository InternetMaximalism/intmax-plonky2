import Audit.Wire3.Spongefish

/-!
# WHIR bytewise sampling and an explicitly separate sorting reference

Raw generation transcribes SpongefishWhirVerify._challengeIndices at 4422b4c7:
count=0 first, numLeaves=1 second, ceil(log2(numLeaves)/8) bytes per query,
ONE 47-byte hash input per entropy byte, BE shift/or, and numLeaves-1 mask.
Zero leaves on the remaining branch rejects the source checked subtraction.
The aggregate counter guard is equivalent on the source uint64 cursor boundary.
`ValidDomain` is the _validateDomain power-of-two precondition, NOT a new guard.

Hash is an arbitrary deterministic Bytes -> 32-byte digest. The output head
byte comes from each successive counter; it is not a slice of one big squeeze.
No uniformity, entropy, random oracle, collision resistance or PCS result is
inferred. Nat indices/counts model bounded source unsigned integers only; ABI,
overflow/allocation, Yul word accesses and source execution refinement remain.

`dedupAdjacent` transcribes the sorted array's adjacent compaction. For useful
sortedness/membership results, `sortReference` is a concrete insertion sort.
IT IS NOT the source's in-place quicksort. This module alone does not prove
quicksort correspondence. WhirQuicksortCorrectness separately proves the actual
indexed Nat/List runner's termination, sortedness, multiplicities and equality
to this reference. WhirSamplingExecution connects indexed compaction and both
whole-WHIR sampler sites. Scratch memory, uint256, gas and source/compiler
refinement remain separate; the reference alone is not whole-source certified.
-/
namespace Audit.Wire3.WhirSampling
open Spongefish (Hash Bytes Byte Digest State)

def ValidDomain (numLeaves : Nat) : Prop := ∃ depth, depth < 256 ∧ numLeaves = 2 ^ depth

def sizeBytes (numLeaves : Nat) : Nat := (Nat.log2 numLeaves + 7) / 8

def hashByte (hash : Hash) (digest : Digest) (counter : Nat) : Byte :=
  (hash (Spongefish.challengeInput digest counter)).val.getD 0 Spongefish.zeroByte

def entropyBytes (hash : Hash) (digest : Digest) : Nat → Nat → Bytes
  | _, 0 => []
  | counter, count+1 => hashByte hash digest counter :: entropyBytes hash digest (counter+1) count

def appendBE (value : Nat) (byte : Byte) : Nat := (value <<< 8) ||| byte.val

def queryLoop (hash : Hash) (digest : Digest) : Nat → Nat → Nat → Nat
  | _, 0, value => value
  | counter, count+1, value => queryLoop hash digest (counter+1) count
      (appendBE value (hashByte hash digest counter))

def rawQueries (hash : Hash) (digest : Digest) (mask bytesPerQuery : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | counter, count+1 =>
      (queryLoop hash digest counter bytesPerQuery 0 &&& mask) ::
      rawQueries hash digest mask bytesPerQuery (counter+bytesPerQuery) count

def advanceCounter (s : State) (count : Nat) : State :=
  ⟨⟨s.sponge.digest,s.sponge.counter+count⟩,s.transcriptPos,s.hintPos⟩

def sampleBytes (hash : Hash) (s : State) (count : Nat) : Option (Bytes × State) :=
  if s.sponge.counter+count ≤ Spongefish.maxCounter then
    some (entropyBytes hash s.sponge.digest s.sponge.counter count,advanceCounter s count)
  else none

/-- This is the concrete UNSORTED generation prefix. No sorting callback. -/
def challengeRaw (hash : Hash) (s : State) (numLeaves count : Nat) : Option (List Nat × State) :=
  if count = 0 then some ([],s) else
  if numLeaves = 1 then some ([0],s) else
  if numLeaves = 0 then none else
  let total := count * sizeBytes numLeaves
  if s.sponge.counter+total ≤ Spongefish.maxCounter then
    some (rawQueries hash s.sponge.digest (numLeaves-1) (sizeBytes numLeaves) s.sponge.counter count,
      advanceCounter s total)
  else none

def insertReference (value : Nat) : List Nat → List Nat
  | [] => [value]
  | x :: rest => if value ≤ x then value :: x :: rest else x :: insertReference value rest

def sortReference : List Nat → List Nat
  | [] => []
  | x :: rest => insertReference x (sortReference rest)

def dedupFrom (previous : Nat) : List Nat → List Nat
  | [] => []
  | x :: rest => if x = previous then dedupFrom x rest else x :: dedupFrom x rest

def dedupAdjacent : List Nat → List Nat
  | [] => []
  | x :: rest => x :: dedupFrom x rest

def sortedUniqueReference (values : List Nat) : List Nat := dedupAdjacent (sortReference values)

/-- Reference output ordering only; source quicksort refinement is not proved. -/
def challengeIndicesReference (hash : Hash) (s : State) (numLeaves count : Nat) :
    Option (List Nat × State) := do
  let (raw,next) ← challengeRaw hash s numLeaves count
  pure (sortedUniqueReference raw,next)

def Nondecreasing : List Nat → Prop
  | [] => True
  | x :: rest => (∀ y ∈ rest, x ≤ y) ∧ Nondecreasing rest

def StrictAscending : List Nat → Prop
  | [] => True
  | x :: rest => (∀ y ∈ rest, x < y) ∧ StrictAscending rest

def NoDuplicates : List Nat → Prop
  | [] => True
  | x :: rest => x ∉ rest ∧ NoDuplicates rest

theorem logarithm_source_recurrence (n : Nat) :
    Nat.log2 n = if 1 < n then Nat.log2 (n/2)+1 else 0 := by
  rw [Nat.log2]
  by_cases h : 1 < n
  · simp [h,show n ≥ 2 by omega]
  · simp [h,show ¬n ≥ 2 by omega]

theorem logarithm_of_power_two (depth : Nat) : Nat.log2 (2 ^ depth) = depth := by
  induction depth with
  | zero => rw [Nat.pow_zero,logarithm_source_recurrence]; simp
  | succ depth ih =>
      rw [logarithm_source_recurrence]
      have hp := Nat.two_pow_pos depth
      have hh : 1 < 2^(depth+1) := by rw [Nat.pow_succ]; omega
      rw [if_pos hh,Nat.pow_succ,Nat.mul_div_cancel _ (by decide),ih]

theorem power_two_query_width (depth : Nat) : sizeBytes (2^depth) = (depth+7)/8 := by
  rw [sizeBytes,logarithm_of_power_two]

theorem source_query_width_bounded (numLeaves : Nat) (h : ValidDomain numLeaves) : sizeBytes numLeaves ≤ 32 := by
  rcases h with ⟨depth,hd,rfl⟩
  rw [power_two_query_width]
  omega

theorem hash_byte_is_actual_first_byte (hash : Hash) (digest : Digest) (counter : Nat) :
    ∃ rest, (hash (Spongefish.challengeInput digest counter)).val = hashByte hash digest counter :: rest ∧
      rest.length = 31 := by
  have hl := (hash (Spongefish.challengeInput digest counter)).property
  cases he : (hash (Spongefish.challengeInput digest counter)).val with
  | nil => simp [he] at hl
  | cons byte rest =>
      refine ⟨rest,?_,?_⟩
      · simp [hashByte,he]
      · simp only [he,List.length_cons] at hl; omega

theorem entropy_byte_count (hash : Hash) (digest : Digest) (counter count : Nat) :
    (entropyBytes hash digest counter count).length = count := by
  induction count generalizing counter with
  | zero => rfl
  | succ count ih => simp [entropyBytes,ih]

theorem entropy_byte_at_counter (hash : Hash) (digest : Digest) (counter count i : Nat) (hi : i < count) :
    (entropyBytes hash digest counter count).get? i = some (hashByte hash digest (counter+i)) := by
  induction count generalizing counter i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => simp [entropyBytes]
      | succ i =>
          simpa only [entropyBytes,List.get?_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using
            ih (counter+1) i (by omega)

theorem bytewise_squeeze_one_matches_existing_sponge (hash : Hash) (s : State) :
    sampleBytes hash s 1 = Spongefish.verifierMessage hash s 1 := by
  obtain ⟨rest,hr,_⟩ := hash_byte_is_actual_first_byte hash s.sponge.digest s.sponge.counter
  by_cases hb : s.sponge.counter+1 ≤ Spongefish.maxCounter <;>
    simp [sampleBytes,entropyBytes,Spongefish.verifierMessage,Spongefish.squeeze,
      Spongefish.blocksNeeded,Spongefish.blockStream,hr,advanceCounter,hb]

theorem sample_bytes_success (hash : Hash) (s t : State) (count : Nat) (bytes : Bytes)
    (h : sampleBytes hash s count = some (bytes,t)) :
    bytes = entropyBytes hash s.sponge.digest s.sponge.counter count ∧ bytes.length = count ∧
    t.sponge.counter = s.sponge.counter+count ∧ t.sponge.counter ≤ Spongefish.maxCounter ∧
    t.sponge.digest = s.sponge.digest ∧ t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos := by
  unfold sampleBytes at h
  split at h
  · cases h
    exact ⟨rfl,entropy_byte_count _ _ _ _,rfl,‹_ ≤ _›,rfl,rfl,rfl⟩
  · contradiction

theorem distinct_byte_positions_use_distinct_hash_inputs (digest : Digest) (counter count i j : Nat)
    (hb : counter+count ≤ Spongefish.maxCounter) (hi : i < count) (hj : j < count) (hne : i ≠ j) :
    Spongefish.challengeInput digest (counter+i) ≠ Spongefish.challengeInput digest (counter+j) := by
  intro he
  have hc := Spongefish.counter_input_injective_bounded digest (counter+i) (counter+j)
    (by omega) (by omega) he
  exact hne (by omega)

theorem append_be_arithmetic (value : Nat) (byte : Byte) : appendBE value byte = 256*value+byte.val := by
  unfold appendBE
  rw [Nat.shiftLeft_eq,Nat.mul_comm value]
  exact (Nat.mul_add_lt_is_or (i:=8) byte.isLt value).symm

theorem query_loop_is_ordered_be_fold (hash : Hash) (digest : Digest) (counter count initial : Nat) :
    queryLoop hash digest counter count initial =
      (entropyBytes hash digest counter count).foldl appendBE initial := by
  induction count generalizing counter initial with
  | zero => rfl
  | succ count ih => simpa only [queryLoop,entropyBytes,List.foldl_cons] using ih (counter+1) _

theorem query_two_bytes_big_endian (hash : Hash) (digest : Digest) (counter : Nat) :
    queryLoop hash digest counter 2 0 =
      256*(hashByte hash digest counter).val + (hashByte hash digest (counter+1)).val := by
  simp only [queryLoop,append_be_arithmetic,Nat.mul_zero,Nat.zero_add]

theorem power_two_mask_is_remainder (value depth : Nat) : value &&& (2^depth-1) = value % 2^depth :=
  Nat.and_pow_two_is_mod value depth

theorem power_two_mask_range (value depth : Nat) : value &&& (2^depth-1) < 2^depth := by
  rw [power_two_mask_is_remainder]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem raw_queries_length (hash : Hash) (digest : Digest) (mask width counter count : Nat) :
    (rawQueries hash digest mask width counter count).length = count := by
  induction count generalizing counter with
  | zero => rfl
  | succ count ih => simp [rawQueries,ih]

theorem raw_query_at_index (hash : Hash) (digest : Digest) (mask width counter count i : Nat) (hi : i < count) :
    (rawQueries hash digest mask width counter count).get? i =
      some (queryLoop hash digest (counter+i*width) width 0 &&& mask) := by
  induction count generalizing counter i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => simp [rawQueries]
      | succ i =>
          simpa only [rawQueries,List.get?_cons_succ,Nat.succ_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
            ih (counter+width) i (by omega)

theorem raw_queries_in_domain (hash : Hash) (digest : Digest) (depth width counter count : Nat) :
    ∀ value ∈ rawQueries hash digest (2^depth-1) width counter count, value < 2^depth := by
  induction count generalizing counter with
  | zero => simp [rawQueries]
  | succ count ih =>
      intro value hm
      rcases List.mem_cons.mp hm with he | hm
      · subst value; exact power_two_mask_range _ _
      · exact ih (counter+width) value hm

theorem zero_count_does_not_squeeze (hash : Hash) (s : State) (numLeaves : Nat) :
    challengeRaw hash s numLeaves 0 = some ([],s) := by simp [challengeRaw]

theorem singleton_domain_does_not_squeeze (hash : Hash) (s : State) (count : Nat) (hc : count ≠ 0) :
    challengeRaw hash s 1 count = some ([0],s) := by simp [challengeRaw,hc]

theorem empty_domain_nonempty_request_rejected (hash : Hash) (s : State) (count : Nat) (hc : count ≠ 0) :
    challengeRaw hash s 0 count = none := by simp [challengeRaw,hc]

theorem raw_nontrivial_success (hash : Hash) (s t : State) (numLeaves count : Nat) (values : List Nat)
    (hc : count ≠ 0) (hl : numLeaves ≠ 1)
    (h : challengeRaw hash s numLeaves count = some (values,t)) :
    numLeaves ≠ 0 ∧ values = rawQueries hash s.sponge.digest (numLeaves-1) (sizeBytes numLeaves) s.sponge.counter count ∧
    values.length = count ∧ t.sponge.counter = s.sponge.counter+count*sizeBytes numLeaves ∧
    t.sponge.counter ≤ Spongefish.maxCounter ∧ t.sponge.digest = s.sponge.digest ∧
    t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos := by
  simp only [challengeRaw,hc,hl,↓reduceIte] at h
  split at h
  · contradiction
  · rename_i hn
    split at h
    · cases h
      exact ⟨hn,rfl,raw_queries_length _ _ _ _ _ _,rfl,‹_ ≤ _›,rfl,rfl,rfl⟩
    · contradiction

theorem raw_success_preserves_state_and_range (hash : Hash) (s t : State) (numLeaves count : Nat)
    (values : List Nat) (hv : ValidDomain numLeaves)
    (h : challengeRaw hash s numLeaves count = some (values,t)) :
    values.length ≤ count ∧ (∀ value ∈ values, value < numLeaves) ∧
    t.sponge.digest = s.sponge.digest ∧ t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos := by
  by_cases hc : count = 0
  · subst count
    rw [zero_count_does_not_squeeze] at h
    cases h
    simp
  · by_cases hl : numLeaves = 1
    · subst numLeaves
      rw [singleton_domain_does_not_squeeze hash s count hc] at h
      cases h
      simp
      omega
    · obtain ⟨_,he,hcount,_,_,hd,hp,hh⟩ := raw_nontrivial_success hash s t numLeaves count values hc hl h
      refine ⟨by omega,?_,hd,hp,hh⟩
      rw [he]
      rcases hv with ⟨depth,_,rfl⟩
      exact raw_queries_in_domain _ _ _ _ _ _

theorem insert_reference_membership (value query : Nat) (xs : List Nat) :
    query ∈ insertReference value xs ↔ query = value ∨ query ∈ xs := by
  induction xs with
  | nil => simp [insertReference]
  | cons x xs ih =>
      unfold insertReference
      split
      · simp
      · simp [ih,or_comm,or_left_comm]

theorem insert_reference_length (value : Nat) (xs : List Nat) :
    (insertReference value xs).length = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      unfold insertReference
      split <;> simp [ih]

theorem insert_reference_sorted (value : Nat) (xs : List Nat) (hs : Nondecreasing xs) :
    Nondecreasing (insertReference value xs) := by
  induction xs with
  | nil => simp [insertReference,Nondecreasing]
  | cons x xs ih =>
      unfold insertReference
      split
      · rename_i hv
        refine ⟨?_,hs⟩
        intro y hy
        rcases List.mem_cons.mp hy with he | hy
        · subst y; exact hv
        · exact Nat.le_trans hv (hs.1 y hy)
      · rename_i hv
        refine ⟨?_,ih hs.2⟩
        intro y hy
        rcases (insert_reference_membership value y xs).mp hy with he | hy
        · subst y; omega
        · exact hs.1 y hy

theorem sort_reference_membership (xs : List Nat) (query : Nat) :
    query ∈ sortReference xs ↔ query ∈ xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sortReference,insert_reference_membership,ih,List.mem_cons]

theorem sort_reference_length (xs : List Nat) : (sortReference xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sortReference,insert_reference_length,ih]

theorem sort_reference_sorted (xs : List Nat) : Nondecreasing (sortReference xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact insert_reference_sorted x _ ih

theorem dedup_from_preserves_membership_with_previous (previous query : Nat) (xs : List Nat) :
    query = previous ∨ query ∈ dedupFrom previous xs ↔ query = previous ∨ query ∈ xs := by
  induction xs generalizing previous with
  | nil => simp [dedupFrom]
  | cons x xs ih =>
      unfold dedupFrom
      split
      · rename_i hx
        subst previous
        simpa only [List.mem_cons,or_self_left] using ih x
      · simp only [List.mem_cons,or_assoc,ih]

theorem adjacent_dedup_membership (xs : List Nat) (query : Nat) :
    query ∈ dedupAdjacent xs ↔ query ∈ xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      simpa only [dedupAdjacent,List.mem_cons] using dedup_from_preserves_membership_with_previous x query xs

theorem dedup_from_length (previous : Nat) (xs : List Nat) : (dedupFrom previous xs).length ≤ xs.length := by
  induction xs generalizing previous with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      unfold dedupFrom
      split
      · have h := ih x; simp only [List.length_cons]; omega
      · simp only [List.length_cons]; exact Nat.add_le_add_right (ih x) 1

theorem adjacent_dedup_length (xs : List Nat) : (dedupAdjacent xs).length ≤ xs.length := by
  cases xs with
  | nil => exact Nat.le_refl _
  | cons x xs => exact Nat.add_le_add_right (dedup_from_length x xs) 1

theorem dedup_from_strict_and_above (previous : Nat) (xs : List Nat)
    (hs : Nondecreasing xs) (hb : ∀ x ∈ xs, previous ≤ x) :
    StrictAscending (dedupFrom previous xs) ∧ ∀ x ∈ dedupFrom previous xs, previous < x := by
  induction xs generalizing previous with
  | nil => simp [dedupFrom,StrictAscending]
  | cons x xs ih =>
      have ht := ih x hs.2 hs.1
      have hx : previous ≤ x := hb x (by simp)
      unfold dedupFrom
      split
      · rename_i he
        subst previous
        exact ht
      · rename_i he
        refine ⟨⟨ht.2,ht.1⟩,?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with heq | hy
        · subst y; omega
        · have hy' := ht.2 y hy; omega

theorem adjacent_dedup_of_sorted_is_strict (xs : List Nat) (hs : Nondecreasing xs) :
    StrictAscending (dedupAdjacent xs) := by
  cases xs with
  | nil => trivial
  | cons x xs =>
      have ht := dedup_from_strict_and_above x xs hs.2 hs.1
      exact ⟨ht.2,ht.1⟩

theorem sorted_unique_reference_membership (xs : List Nat) (value : Nat) :
    value ∈ sortedUniqueReference xs ↔ value ∈ xs := by
  rw [sortedUniqueReference,adjacent_dedup_membership,sort_reference_membership]

theorem sorted_unique_reference_length (xs : List Nat) : (sortedUniqueReference xs).length ≤ xs.length := by
  have h := adjacent_dedup_length (sortReference xs)
  simpa only [sort_reference_length] using h

theorem sorted_unique_reference_strict (xs : List Nat) : StrictAscending (sortedUniqueReference xs) :=
  adjacent_dedup_of_sorted_is_strict _ (sort_reference_sorted xs)

theorem strict_ascending_has_no_duplicates (xs : List Nat) (hs : StrictAscending xs) : NoDuplicates xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
      refine ⟨?_,ih hs.2⟩
      intro hx
      have hh := hs.1 x hx
      omega

theorem sorted_unique_reference_nonempty (xs : List Nat) (hn : xs ≠ []) : sortedUniqueReference xs ≠ [] := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      have hx := (sorted_unique_reference_membership (x::xs) x).mpr (by simp)
      intro he
      simp [he] at hx

theorem reference_success_has_same_raw_execution (hash : Hash) (s t : State) (numLeaves count : Nat)
    (values : List Nat) (h : challengeIndicesReference hash s numLeaves count = some (values,t)) :
    ∃ raw, challengeRaw hash s numLeaves count = some (raw,t) ∧ values = sortedUniqueReference raw := by
  unfold challengeIndicesReference at h
  cases hr : challengeRaw hash s numLeaves count with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨raw,next⟩
      simp only [hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨raw,rfl,rfl⟩

theorem reference_sampling_output_properties (hash : Hash) (s t : State) (numLeaves count : Nat)
    (values : List Nat) (hv : ValidDomain numLeaves)
    (h : challengeIndicesReference hash s numLeaves count = some (values,t)) :
    values.length ≤ count ∧ (∀ value ∈ values, value < numLeaves) ∧ StrictAscending values ∧ NoDuplicates values ∧
    t.sponge.digest = s.sponge.digest ∧ t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos := by
  obtain ⟨raw,hr,rfl⟩ := reference_success_has_same_raw_execution hash s t numLeaves count values h
  have hs := raw_success_preserves_state_and_range hash s t numLeaves count raw hv hr
  refine ⟨Nat.le_trans (sorted_unique_reference_length raw) hs.1,?_,sorted_unique_reference_strict raw,
    strict_ascending_has_no_duplicates _ (sorted_unique_reference_strict raw),hs.2.2⟩
  intro x hx
  exact hs.2.1 x ((sorted_unique_reference_membership raw x).mp hx)

theorem reference_sampling_membership_exact (hash : Hash) (s t : State) (numLeaves count : Nat)
    (values : List Nat) (hc : count ≠ 0) (hl : numLeaves ≠ 1)
    (h : challengeIndicesReference hash s numLeaves count = some (values,t)) (value : Nat) :
    value ∈ values ↔ value ∈ rawQueries hash s.sponge.digest (numLeaves-1)
      (sizeBytes numLeaves) s.sponge.counter count := by
  obtain ⟨raw,hr,rfl⟩ := reference_success_has_same_raw_execution hash s t numLeaves count values h
  have he := (raw_nontrivial_success hash s t numLeaves count raw hc hl hr).2.1
  rw [sorted_unique_reference_membership,he]

theorem reference_sampling_counter_exact (hash : Hash) (s t : State) (numLeaves count : Nat)
    (values : List Nat) (hc : count ≠ 0) (hl : numLeaves ≠ 1)
    (h : challengeIndicesReference hash s numLeaves count = some (values,t)) :
    t.sponge.counter = s.sponge.counter+count*sizeBytes numLeaves ∧ t.sponge.counter ≤ Spongefish.maxCounter := by
  obtain ⟨raw,hr,_⟩ := reference_success_has_same_raw_execution hash s t numLeaves count values h
  have hs := raw_nontrivial_success hash s t numLeaves count raw hc hl hr
  exact ⟨hs.2.2.2.1,hs.2.2.2.2.1⟩

theorem source_counter_guard_equivalent (counter total : Nat) (hc : counter ≤ Spongefish.maxCounter) :
    total ≤ Spongefish.maxCounter-counter ↔ counter+total ≤ Spongefish.maxCounter := by omega

theorem query_loop_numeric_bound (hash : Hash) (digest : Digest) (counter count initial : Nat) :
    queryLoop hash digest counter count initial < 256^count*(initial+1) := by
  induction count generalizing counter initial with
  | zero => simp [queryLoop]
  | succ count ih =>
      rw [queryLoop,append_be_arithmetic]
      have hi := ih (counter+1) (appendBE initial (hashByte hash digest counter))
      have hb := (hashByte hash digest counter).isLt
      rw [append_be_arithmetic] at hi
      have hm := Nat.mul_le_mul_left (256^count)
        (show 256*initial+(hashByte hash digest counter).val+1 ≤ 256*(initial+1) by omega)
      rw [←Nat.mul_assoc,←Nat.pow_succ] at hm
      exact Nat.lt_of_lt_of_le hi hm

theorem query_word_bound (hash : Hash) (digest : Digest) (counter count : Nat) (hc : count ≤ 32) :
    queryLoop hash digest counter count 0 < 2^256 := by
  have hq := query_loop_numeric_bound hash digest counter count 0
  simp only [Nat.zero_add,Nat.mul_one] at hq
  have hp := Nat.pow_le_pow_of_le_right (show 0 < 256 by decide) hc
  have he : 256^32 = 2^256 := by decide
  rw [he] at hp
  exact Nat.lt_of_lt_of_le hq hp

theorem all_query_counters_bounded (counter count width query byte : Nat)
    (hc : counter+count*width ≤ Spongefish.maxCounter) (hq : query < count) (hb : byte < width) :
    counter+query*width+byte < Spongefish.maxCounter := by
  have hm := Nat.mul_le_mul_right width (show query+1 ≤ count by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  omega

theorem strict_ascending_length_within_interval (xs : List Nat) (lower upper : Nat)
    (hs : StrictAscending xs) (hb : ∀ x ∈ xs, lower ≤ x ∧ x < upper) : xs.length ≤ upper-lower := by
  induction xs generalizing lower with
  | nil => simp
  | cons x xs ih =>
      have hx := hb x (by simp)
      have ht : ∀ y ∈ xs, x+1 ≤ y ∧ y < upper := by
        intro y hy
        have hh := hs.1 y hy
        have hu := hb y (by simp [hy])
        exact ⟨by omega,hu.2⟩
      have hh := ih (x+1) hs.2 ht
      simp only [List.length_cons]
      omega

theorem reference_distinct_count_bounded_by_leaves (hash : Hash) (s t : State) (numLeaves count : Nat)
    (values : List Nat) (hv : ValidDomain numLeaves)
    (h : challengeIndicesReference hash s numLeaves count = some (values,t)) : values.length ≤ numLeaves := by
  have hs := reference_sampling_output_properties hash s t numLeaves count values hv h
  have hl := strict_ascending_length_within_interval values 0 numLeaves hs.2.2.1
    (by intro x hx; exact ⟨Nat.zero_le _,hs.2.1 x hx⟩)
  simpa only [Nat.sub_zero] using hl

theorem reference_zero_request_exact (hash : Hash) (s : State) (numLeaves : Nat) :
    challengeIndicesReference hash s numLeaves 0 = some ([],s) := by
  simp [challengeIndicesReference,zero_count_does_not_squeeze,sortedUniqueReference,sortReference,dedupAdjacent]

theorem reference_singleton_domain_exact (hash : Hash) (s : State) (count : Nat) (hc : count ≠ 0) :
    challengeIndicesReference hash s 1 count = some ([0],s) := by
  simp [challengeIndicesReference,singleton_domain_does_not_squeeze hash s count hc,
    sortedUniqueReference,sortReference,insertReference,dedupAdjacent,dedupFrom]

theorem reference_nonempty_request_has_nonempty_output (hash : Hash) (s t : State) (numLeaves count : Nat)
    (values : List Nat) (hc : count ≠ 0)
    (h : challengeIndicesReference hash s numLeaves count = some (values,t)) : values ≠ [] := by
  by_cases hl : numLeaves = 1
  · subst numLeaves
    rw [reference_singleton_domain_exact hash s count hc] at h
    cases h
    simp
  · obtain ⟨raw,hr,rfl⟩ := reference_success_has_same_raw_execution hash s t numLeaves count values h
    have hn := (raw_nontrivial_success hash s t numLeaves count raw hc hl hr).2.2.1
    apply sorted_unique_reference_nonempty raw
    intro he
    simp [he] at hn
    exact hc hn.symm

/-- A deterministic test hash exposes the last byte of its actual 47-byte
input. It is only an executable sampling example, not a cryptographic hash. -/
def exampleHash : Hash := fun input =>
  ⟨input.getD 46 Spongefish.zeroByte :: List.replicate 31 Spongefish.zeroByte,by simp⟩
def exampleState : State := ⟨⟨Spongefish.zeroDigest,5⟩,17,9⟩

theorem example_individual_entropy_bytes :
    sampleBytes exampleHash exampleState 3 =
      some ([⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩],advanceCounter exampleState 3) := by decide

theorem example_raw_repeated_queries :
    challengeRaw exampleHash exampleState 4 6 = some ([1,2,3,0,1,2],advanceCounter exampleState 6) := by
  have hw : sizeBytes 4 = 1 := by
    change sizeBytes (2^2) = 1
    rw [power_two_query_width]
  simp only [challengeRaw,show (6:Nat) ≠ 0 by decide,show (4:Nat) ≠ 1 by decide,
    show (4:Nat) ≠ 0 by decide,↓reduceIte,hw]
  decide

theorem example_sorted_deduplicated_queries :
    challengeIndicesReference exampleHash exampleState 4 6 =
      some ([0,1,2,3],advanceCounter exampleState 6) := by
  rw [challengeIndicesReference,example_raw_repeated_queries]
  decide

theorem example_two_byte_query_is_big_endian :
    queryLoop exampleHash Spongefish.zeroDigest 1 2 0 = 258 := by decide

theorem example_source_adjacent_dedup_preserves_order :
    dedupAdjacent [0,0,1,2,2,3,3] = [0,1,2,3] := by decide

end Audit.Wire3.WhirSampling
