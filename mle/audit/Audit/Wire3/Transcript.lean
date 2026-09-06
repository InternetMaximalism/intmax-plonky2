import Std

/-!
Wire-v3 byte framing and transcript transition model, reviewed at becfe98e.
Source correspondence: `src/transcript_v2.rs`, `contracts/src/TranscriptV2.sol`,
`src/prover_v2.rs::absorb_v2_claims_and_sample_indices`, and
`protocol/mle_whir_v2.json`. The V2 filenames implement protocol version 3.

Bytes and little-endian serialization are executable. Keccak is an explicit
function parameter, NOT an injective function, random oracle, or security axiom.
Thus different framed inputs need not produce different hashes/challenges.
The model proves pre-hash framing, canonical ranges, and actual ordering and
counter transitions. It does not prove Keccak, Rust/EVM instruction refinement,
assembly allocation safety, entropy, Fiat--Shamir soundness, or PCS soundness.
The checked counter model captures successful non-overflowing production calls;
it intentionally makes no assertion about a Rust u64 overflow build mode.
-/
namespace Audit.Wire3.Transcript

abbrev Byte := Fin 256
abbrev Bytes := List Byte
structure Digest where
  bytes : Bytes
  length_eq : bytes.length = 32

def modulus : Nat := 18446744069414584321
def u64Limit : Nat := 18446744073709551616
abbrev Field := Fin modulus

def ascii (s : String) : Bytes :=
  s.toUTF8.data.toList.map fun x => ⟨x.toNat % 256, Nat.mod_lt _ (by decide)⟩

def le : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, x => ⟨x % 256, Nat.mod_lt _ (by decide)⟩ :: le n (x / 256)

def fromLe : Bytes → Nat
  | [] => 0
  | b :: bs => b.val + 256 * fromLe bs

theorem le_length (n x : Nat) : (le n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [le, ih]

theorem fromLe_le_roundtrip (n x : Nat) (h : x < 256 ^ n) : fromLe (le n x) = x := by
  induction n generalizing x with
  | zero => simp [le, fromLe] at *; omega
  | succ n ih =>
    have hdiv : x / 256 < 256 ^ n := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr
      simpa [Nat.pow_succ, Nat.mul_comm] using h
    simp only [le, fromLe, ih _ hdiv]
    exact Nat.mod_add_div x 256

theorem le_injective_bounded (n x y : Nat) (hx : x < 256 ^ n) (hy : y < 256 ^ n)
    (h : le n x = le n y) : x = y := by
  have hh := congrArg fromLe h
  simpa [fromLe_le_roundtrip n x hx, fromLe_le_roundtrip n y hy] using hh

def fieldBytes (x : Field) : Bytes := le 8 x.val

theorem field_encoding_roundtrip (x : Field) : fromLe (fieldBytes x) = x.val := by
  apply fromLe_le_roundtrip
  have := x.isLt
  unfold modulus at this
  change x.val < 18446744073709551616
  omega

theorem field_encoding_injective (x y : Field) (h : fieldBytes x = fieldBytes y) : x = y := by
  apply Fin.ext
  have hh := congrArg fromLe h
  simpa [field_encoding_roundtrip] using hh

structure Ext3 where
  c0 : Field
  c1 : Field
  c2 : Field
  deriving DecidableEq

def ext3Bytes (x : Ext3) : Bytes := fieldBytes x.c0 ++ fieldBytes x.c1 ++ fieldBytes x.c2
def fieldVecBytes (xs : List Field) : Bytes := le 8 xs.length ++ xs.bind fieldBytes
def ext3VecBytes (xs : List Ext3) : Bytes := le 8 xs.length ++ xs.bind ext3Bytes

theorem field_bytes_length (x : Field) : (fieldBytes x).length = 8 := le_length _ _
theorem ext3_bytes_length (x : Ext3) : (ext3Bytes x).length = 24 := by
  simp [ext3Bytes, field_bytes_length]

theorem field_vector_length (xs : List Field) : (fieldVecBytes xs).length = 8 + 8 * xs.length := by
  have h : (xs.bind fieldBytes).length = 8 * xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.bind_cons, field_bytes_length, ih, Nat.mul_add, Nat.add_comm]
  simp [fieldVecBytes, le_length, h]

theorem ext3_vector_length (xs : List Ext3) : (ext3VecBytes xs).length = 8 + 24 * xs.length := by
  have h : (xs.bind ext3Bytes).length = 24 * xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.bind_cons, ext3_bytes_length, ih, Nat.mul_add, Nat.add_comm]
  simp [ext3VecBytes, le_length, h]

def framePrefix := ascii "plonky2-mle-v3-frame"
def challengePrefix := ascii "plonky2-mle-v3-challenge"
def digestBytes (d : Digest) : Bytes := d.bytes

def frame (state : Digest) (tag : Byte) (payload : Bytes) : Bytes :=
  framePrefix ++ digestBytes state ++ [tag] ++ le 8 payload.length ++ payload

def challengeInput (state : Digest) (counter : Nat) : Bytes :=
  challengePrefix ++ digestBytes state ++ le 8 counter

theorem frame_length (d : Digest) (tag : Byte) (payload : Bytes) :
    (frame d tag payload).length = framePrefix.length + 41 + payload.length := by
  simp only [frame, List.length_append, digestBytes, d.length_eq, List.length_singleton, le_length]

theorem frame_tag_and_payload_are_unambiguous (d : Digest) (t u : Byte) (p q : Bytes)
    (h : frame d t p = frame d u q) : t = u ∧ p = q := by
  have hlen := congrArg List.length h
  simp only [frame_length] at hlen
  have hpq : p.length = q.length := by omega
  simp only [frame, List.append_assoc] at h
  have h := List.append_cancel_left h
  have h := List.append_cancel_left h
  simp only [List.singleton_append, List.cons.injEq] at h
  exact ⟨h.1, by simpa [hpq] using h.2⟩

structure State where
  digest : Digest
  counter : Nat

abbrev Hash := Bytes → Digest

def absorb (hash : Hash) (s : State) (tag : Byte) (payload : Bytes) : State :=
  ⟨hash (frame s.digest tag payload), 0⟩

/-- Production rejection for a nonrepresentable u64 payload length. -/
def absorbChecked (hash : Hash) (s : State) (tag : Byte) (payload : Bytes) : Option State :=
  if payload.length < u64Limit then some (absorb hash s tag payload) else none

def domain (hash : Hash) (s : State) (label : String) : State := absorb hash s 1 (ascii label)
def absorbExt3Vec (hash : Hash) (s : State) (xs : List Ext3) : State :=
  absorb hash s 6 (ext3VecBytes xs)

def challengeAt (hash : Hash) (d : Digest) (counter : Nat) : Field :=
  ⟨fromLe (digestBytes (hash (challengeInput d counter))) % modulus,
    Nat.mod_lt _ (by decide)⟩

def squeeze (hash : Hash) (s : State) : Option (Field × State) :=
  if s.counter + 1 < u64Limit then
    some (challengeAt hash s.digest s.counter, ⟨s.digest, s.counter + 1⟩)
  else none

def squeezeMany (hash : Hash) : Nat → State → Option (List Field × State)
  | 0, s => some ([], s)
  | n + 1, s => do
    let (x, t) ← squeeze hash s
    let (xs, u) ← squeezeMany hash n t
    pure (x :: xs, u)

theorem absorb_resets_counter (hash : Hash) (s : State) (tag : Byte) (p : Bytes) :
    (absorb hash s tag p).counter = 0 := rfl

theorem checked_absorb_bounds (hash : Hash) (s t : State) (tag : Byte) (p : Bytes)
    (h : absorbChecked hash s tag p = some t) :
    p.length < u64Limit ∧ t = absorb hash s tag p := by
  unfold absorbChecked at h
  split at h <;> simp_all

theorem squeeze_success (hash : Hash) (s t : State) (x : Field)
    (h : squeeze hash s = some (x, t)) :
    t.digest = s.digest ∧ t.counter = s.counter + 1 ∧
      t.counter < u64Limit ∧ x = challengeAt hash s.digest s.counter := by
  unfold squeeze at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp_all
  · simp at h

theorem squeeze_many_success (hash : Hash) (n : Nat) (s t : State) (xs : List Field)
    (h : squeezeMany hash n s = some (xs, t)) :
    xs.length = n ∧ t.digest = s.digest ∧ t.counter = s.counter + n := by
  induction n generalizing s xs t with
  | zero => simp [squeezeMany] at h; rcases h with ⟨rfl, rfl⟩; simp
  | succ n ih =>
    simp only [squeezeMany, Option.bind_eq_bind] at h
    cases hs : squeeze hash s with
    | none => simp [hs] at h
    | some pair =>
      rcases pair with ⟨x, mid⟩
      cases hm : squeezeMany hash n mid with
      | none => simp [hs, hm] at h
      | some pair =>
        rcases pair with ⟨ys, u⟩
        simp [hs, hm] at h
        rcases h with ⟨rfl, rfl⟩
        have a := squeeze_success hash s mid x hs
        have b := ih mid u ys hm
        simp only [List.length_cons]
        exact ⟨by omega, b.2.1.trans a.1, by omega⟩

theorem six_squeezes_use_consecutive_inputs (hash : Hash) (d : Digest) :
    squeezeMany hash 6 ⟨d, 0⟩ = some
      ([challengeAt hash d 0, challengeAt hash d 1, challengeAt hash d 2,
        challengeAt hash d 3, challengeAt hash d 4, challengeAt hash d 5], ⟨d, 6⟩) := by
  simp [squeezeMany, squeeze, u64Limit]

theorem challenge_inputs_distinguish_bounded_counters (d : Digest) (i j : Nat)
    (hi : i < u64Limit) (hj : j < u64Limit)
    (h : challengeInput d i = challengeInput d j) : i = j := by
  simp only [challengeInput, List.append_assoc, List.append_cancel_left_eq] at h
  apply le_injective_bounded 8 i j _ _ h
  · exact hi
  · exact hj

/-- Exact production commit order, including the domain reset before sampling. -/
def commitRound (hash : Hash) (s : State) (round : Nat) (log gate : List Ext3) : State :=
  let s := domain hash s "outer-sumcheck-lockstep-round-v3"
  let s := absorb hash s 2 (le 8 round)
  let s := absorbExt3Vec hash s log
  let s := absorbExt3Vec hash s gate
  domain hash s "outer-sumcheck-lockstep-challenges-v3"

def coupledRound (hash : Hash) (s : State) (round : Nat) (log gate : List Ext3) :
    Option (List Field × State) :=
  if round < u64Limit ∧ (ext3VecBytes log).length < u64Limit ∧
      (ext3VecBytes gate).length < u64Limit then
    squeezeMany hash 6 (commitRound hash s round log gate)
  else none

theorem commit_round_resets_counter (hash : Hash) (s : State) (round : Nat)
    (log gate : List Ext3) : (commitRound hash s round log gate).counter = 0 := rfl

theorem coupled_round_all_messages_before_sampling (hash : Hash) (s t : State)
    (round : Nat) (log gate : List Ext3) (xs : List Field)
    (h : coupledRound hash s round log gate = some (xs, t)) :
    xs.length = 6 ∧ t.counter = 6 ∧
      t.digest = (commitRound hash s round log gate).digest := by
  unfold coupledRound at h
  split at h
  · have a := squeeze_many_success hash 6 (commitRound hash s round log gate) t xs h
    exact ⟨a.1, by simpa [commit_round_resets_counter] using a.2.2, a.2.1⟩
  · simp at h

/-- Six claim cells: the last is an explicitly empty gate/norm-inverse cell. -/
def commitClaims (hash : Hash) (s : State)
    (lp lw ln gp gw : List Ext3) : State :=
  let s := domain hash s "pcs-constituent-claims-v3"
  let s := absorbExt3Vec hash s lp
  let s := absorbExt3Vec hash s lw
  let s := absorbExt3Vec hash s ln
  let s := absorbExt3Vec hash s gp
  let s := absorbExt3Vec hash s gw
  let s := absorbExt3Vec hash s []
  domain hash s "pcs-constituent-index-v3"

def constituentIndices (hash : Hash) (s : State) (lp lw ln gp gw : List Ext3)
    (indexBits : Nat) : Option (List Field × State) :=
  squeezeMany hash (6 * indexBits) (commitClaims hash s lp lw ln gp gw)

theorem constituent_indices_after_all_cells (hash : Hash) (s t : State)
    (lp lw ln gp gw : List Ext3) (bits : Nat) (xs : List Field)
    (h : constituentIndices hash s lp lw ln gp gw bits = some (xs, t)) :
    xs.length = 6 * bits ∧ t.counter = 6 * bits ∧
      t.digest = (commitClaims hash s lp lw ln gp gw).digest := by
  have a := squeeze_many_success hash (6 * bits) (commitClaims hash s lp lw ln gp gw) t xs h
  exact ⟨a.1, by simpa [commitClaims, domain, absorb] using a.2.2, a.2.1⟩

end Audit.Wire3.Transcript
