import Audit.Wire3.Merkle
import Audit.Wire3.Verifier

/-!
WHIR inner transcript bytes, hash chain, canonical field reads and PoW.
Runtime snapshot becfe98e: Keccak256Chain.sol; SpongefishWhir.sol transcript
operations/geometricChallenge; SpongefishWhirVerify._verifyPow/_consumeVecPrefix.
This is the INNER WHIR chain, not TranscriptV2's tagged outer protocol.

Hash is a deterministic Bytes -> raw 32-byte digest parameter. No injectivity,
random-oracle distribution, or collision-resistance premise is hidden in it.
Squeeze uses state || ASCII squeeze || u64 BIG-ENDIAN counter. Field challenges
use one 120-byte squeeze split into three 40-byte LITTLE-ENDIAN reductions, not
three separate calls (which would consume different blocks). Prover Ext3 values
are read as 24 raw bytes and range-checked BEFORE any modular reduction.

The PoW digest hashes 32 challenge bytes || 8 raw nonce bytes || 24 zero bytes;
its first 8 bytes are decoded LE without field reduction. Max u64 threshold is
the source's no-work sentinel. Counts/cursors are mathematical naturals; source
ABI bounds, allocation/uint256 overflow, word-load refinement, native spongefish
IO-pattern semantics, and cryptographic probability remain separate obligations.
-/
namespace Audit.Wire3.Spongefish

abbrev Byte := Transcript.Byte
abbrev Bytes := Transcript.Bytes
abbrev Digest := Merkle.Digest
abbrev Hash := Merkle.Hash
abbrev Ext3 := Verifier.Ext3

def zeroByte : Byte := ⟨0, by decide⟩
def zeroDigest : Digest := ⟨List.replicate 32 zeroByte, by simp⟩
def maxCounter : Nat := 2 ^ 64 - 1

structure Sponge where
  digest : Digest
  counter : Nat
  deriving DecidableEq

structure State where
  sponge : Sponge
  transcriptPos : Nat
  hintPos : Nat
  deriving DecidableEq

def absorb (hash : Hash) (s : Sponge) (data : Bytes) : Sponge :=
  ⟨hash (s.digest.val ++ data), 0⟩

def ratchet (hash : Hash) (s : Sponge) : Sponge :=
  ⟨hash (s.digest.val ++ Transcript.ascii "ratchet"), 0⟩

def challengeInput (digest : Digest) (counter : Nat) : Bytes :=
  digest.val ++ Transcript.ascii "squeeze" ++ (Transcript.le 8 counter).reverse

def blockStream (hash : Hash) (digest : Digest) : Nat → Nat → Bytes
  | _, 0 => []
  | counter, count + 1 => (hash (challengeInput digest counter)).val ++
      blockStream hash digest (counter + 1) count

def blocksNeeded (count : Nat) : Nat := (count + 31) / 32

def squeeze (hash : Hash) (s : Sponge) (count : Nat) : Option (Bytes × Sponge) :=
  if s.counter + blocksNeeded count ≤ maxCounter then
    some ((blockStream hash s.digest s.counter (blocksNeeded count)).take count,
      ⟨s.digest, s.counter + blocksNeeded count⟩)
  else none

def init (hash : Hash) (protocolId sessionId publicInstance : Bytes) : State :=
  ⟨absorb hash (absorb hash (absorb hash ⟨zeroDigest, 0⟩ protocolId) sessionId) publicInstance, 0, 0⟩

def readSlice (source : Bytes) (offset count : Nat) : Option (Bytes × Nat) :=
  if offset ≤ source.length ∧ count ≤ source.length - offset then
    some ((source.drop offset).take count, offset + count)
  else none

def proverMessage (hash : Hash) (s : State) (transcript : Bytes) (count : Nat) : Option (Bytes × State) := do
  let (data, next) ← readSlice transcript s.transcriptPos count
  pure (data, ⟨absorb hash s.sponge data, next, s.hintPos⟩)

def proverHint (s : State) (hints : Bytes) (count : Nat) : Option (Bytes × State) := do
  let (data, next) ← readSlice hints s.hintPos count
  pure (data, ⟨s.sponge, s.transcriptPos, next⟩)

def verifierMessage (hash : Hash) (s : State) (count : Nat) : Option (Bytes × State) := do
  let (data, sponge) ← squeeze hash s.sponge count
  pure (data, ⟨sponge, s.transcriptPos, s.hintPos⟩)

def decodeCanonicalExt3 (data : Bytes) : Option Ext3 :=
  let a := Transcript.fromLe (data.take 8)
  let b := Transcript.fromLe ((data.drop 8).take 8)
  let c := Transcript.fromLe ((data.drop 16).take 8)
  if h : data.length = 24 ∧ a < Arithmetic.modulus ∧ b < Arithmetic.modulus ∧ c < Arithmetic.modulus then
    some ⟨⟨a,b,c⟩, h.2⟩
  else none

def proverExt3 (hash : Hash) (s : State) (transcript : Bytes) : Option (Ext3 × State) := do
  let (data, next) ← proverMessage hash s transcript 24
  let value ← decodeCanonicalExt3 data
  pure (value, next)

def proverHash (hash : Hash) (s : State) (transcript : Bytes) : Option (Digest × State) := do
  let (data, next) ← proverMessage hash s transcript 32
  if h : data.length = 32 then pure (⟨data,h⟩,next) else none

def reduceChallenge (data : Bytes) : Ext3 :=
  ⟨⟨Arithmetic.reduce (Transcript.fromLe (data.take 40)),
     Arithmetic.reduce (Transcript.fromLe ((data.drop 40).take 40)),
     Arithmetic.reduce (Transcript.fromLe ((data.drop 80).take 40))⟩,
   Arithmetic.reduce_canonical _, Arithmetic.reduce_canonical _, Arithmetic.reduce_canonical _⟩

def verifierExt3 (hash : Hash) (s : State) : Option (Ext3 × State) := do
  let (data, next) ← verifierMessage hash s 120
  pure (reduceChallenge data, next)

def proverExt3Many (hash : Hash) (source : Bytes) : Nat → State → Option (List Ext3 × State)
  | 0,s => some ([],s)
  | n+1,s => do
      let (x,t) ← proverExt3 hash s source
      let (xs,u) ← proverExt3Many hash source n t
      pure (x::xs,u)

def verifierExt3Many (hash : Hash) : Nat → State → Option (List Ext3 × State)
  | 0,s => some ([],s)
  | n+1,s => do
      let (x,t) ← verifierExt3 hash s
      let (xs,u) ← verifierExt3Many hash n t
      pure (x::xs,u)

def geometricPowers (x : Ext3) : Nat → Ext3 → List Ext3
  | 0, _ => []
  | n + 1, previous => previous :: geometricPowers x n (Verifier.mul previous x)

def one : Ext3 := ⟨Arithmetic.one, ⟨by decide,by decide,by decide⟩⟩

def geometricChallenge (hash : Hash) (s : State) (count : Nat) : Option (List Ext3 × State) :=
  match count with
  | 0 => some ([],s)
  | 1 => some ([one],s)
  | n + 2 => do
      let (x,next) ← verifierExt3 hash s
      pure (geometricPowers x (n+2) one,next)

def powInput (challenge nonce : Bytes) : Bytes := challenge ++ nonce ++ List.replicate 24 zeroByte
def powValue (hash : Hash) (challenge nonce : Bytes) : Nat :=
  Transcript.fromLe ((hash (powInput challenge nonce)).val.take 8)

def verifyPow (hash : Hash) (s : State) (transcript : Bytes) (threshold : Nat) : Option State :=
  if maxCounter < threshold then none else
  if threshold = maxCounter then some s else do
    let (challenge, afterChallenge) ← verifierMessage hash s 32
    let (nonce, afterNonce) ← proverMessage hash afterChallenge transcript 8
    if powValue hash challenge nonce ≤ threshold then some afterNonce else none

def consumeVecPrefix (s : State) (hints : Bytes) (expectedElements : Nat) : Option State := do
  let (data,next) ← proverHint s hints 8
  if Transcript.fromLe data = expectedElements then some next else none

theorem absorb_resets_counter (hash : Hash) (s : Sponge) (data : Bytes) :
    (absorb hash s data).counter = 0 := rfl

theorem ratchet_resets_counter (hash : Hash) (s : Sponge) : (ratchet hash s).counter = 0 := rfl

theorem challenge_input_length (digest : Digest) (counter : Nat) :
    (challengeInput digest counter).length = 47 := by
  have hl : (Transcript.ascii "squeeze").length = 7 := rfl
  simp [challengeInput, digest.property, Transcript.le_length, hl]

theorem block_stream_length (hash : Hash) (digest : Digest) (counter count : Nat) :
    (blockStream hash digest counter count).length = 32 * count := by
  induction count generalizing counter with
  | zero => rfl
  | succ count ih => simp [blockStream, ih, (hash (challengeInput digest counter)).property]; omega

theorem enough_blocks (count : Nat) : count ≤ 32 * blocksNeeded count := by
  unfold blocksNeeded
  omega

theorem squeeze_success_exact (hash : Hash) (s t : Sponge) (count : Nat) (data : Bytes)
    (h : squeeze hash s count = some (data,t)) :
    data.length = count ∧ t.digest = s.digest ∧
      t.counter = s.counter + blocksNeeded count ∧ t.counter ≤ maxCounter ∧
      data = (blockStream hash s.digest s.counter (blocksNeeded count)).take count := by
  unfold squeeze at h
  split at h
  · cases h
    exact ⟨by rw [List.length_take, block_stream_length]; exact Nat.min_eq_left (enough_blocks count),
      rfl, rfl, ‹s.counter + blocksNeeded count ≤ maxCounter›, rfl⟩
  · contradiction

theorem ext3_challenge_uses_four_blocks : blocksNeeded 120 = 4 := by decide

theorem counter_input_injective_bounded (digest : Digest) (a b : Nat)
    (ha : a ≤ maxCounter) (hb : b ≤ maxCounter)
    (h : challengeInput digest a = challengeInput digest b) : a = b := by
  unfold challengeInput at h
  have h := List.append_cancel_left h
  have h := congrArg List.reverse h
  simp only [List.reverse_reverse] at h
  apply Transcript.le_injective_bounded 8 a b _ _ h
  · change a < 18446744073709551616
    change a ≤ 18446744073709551615 at ha
    omega
  · change b < 18446744073709551616
    change b ≤ 18446744073709551615 at hb
    omega

theorem read_slice_success (source data : Bytes) (offset count next : Nat)
    (h : readSlice source offset count = some (data,next)) :
    data.length = count ∧ data = (source.drop offset).take count ∧
      next = offset + count ∧ offset ≤ next ∧ next ≤ source.length := by
  unfold readSlice at h
  split at h
  · cases h
    exact ⟨by rw [List.length_take, List.length_drop]; exact Nat.min_eq_left ‹_ ∧ _›.2,
      rfl, rfl, by omega, by omega⟩
  · contradiction

theorem prover_message_reads_then_absorbs (hash : Hash) (s t : State) (source data : Bytes) (count : Nat)
    (h : proverMessage hash s source count = some (data,t)) :
    data.length = count ∧ t.transcriptPos = s.transcriptPos + count ∧ t.transcriptPos ≤ source.length ∧
      t.hintPos = s.hintPos ∧ t.sponge = absorb hash s.sponge data ∧
      data = (source.drop s.transcriptPos).take count := by
  unfold proverMessage at h
  cases hr : readSlice source s.transcriptPos count with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨bytes,next⟩
      simp only [hr, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := read_slice_success source bytes s.transcriptPos count next hr
      exact ⟨hs.1, hs.2.2.1, hs.2.2.2.2, rfl, rfl, hs.2.1⟩

theorem hint_is_not_absorbed (s t : State) (source data : Bytes) (count : Nat)
    (h : proverHint s source count = some (data,t)) :
    data.length = count ∧ t.hintPos = s.hintPos + count ∧ t.hintPos ≤ source.length ∧
      t.transcriptPos = s.transcriptPos ∧ t.sponge = s.sponge := by
  unfold proverHint at h
  cases hr : readSlice source s.hintPos count with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨bytes,next⟩
      simp only [hr, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := read_slice_success source bytes s.hintPos count next hr
      exact ⟨hs.1, hs.2.2.1, hs.2.2.2.2, rfl, rfl⟩

theorem verifier_message_preserves_read_cursors (hash : Hash) (s t : State) (data : Bytes) (count : Nat)
    (h : verifierMessage hash s count = some (data,t)) :
    data.length = count ∧ t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos ∧
      t.sponge.digest = s.sponge.digest ∧ t.sponge.counter = s.sponge.counter + blocksNeeded count := by
  unfold verifierMessage at h
  cases hr : squeeze hash s.sponge count with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨bytes,next⟩
      simp only [hr, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := squeeze_success_exact hash s.sponge next count bytes hr
      exact ⟨hs.1,rfl,rfl,hs.2.1,hs.2.2.1⟩

theorem canonical_decode_preserves_raw_limbs (data : Bytes) (x : Ext3)
    (h : decodeCanonicalExt3 data = some x) :
    data.length = 24 ∧ x.val.c0 = Transcript.fromLe (data.take 8) ∧
      x.val.c1 = Transcript.fromLe ((data.drop 8).take 8) ∧
      x.val.c2 = Transcript.fromLe ((data.drop 16).take 8) := by
  unfold decodeCanonicalExt3 at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨‹_ ∧ _ ∧ _ ∧ _›.1,rfl,rfl,rfl⟩
  · contradiction

theorem prover_ext3_consumes_exact_canonical_bytes (hash : Hash) (s t : State) (source : Bytes) (x : Ext3)
    (h : proverExt3 hash s source = some (x,t)) :
    t.transcriptPos = s.transcriptPos + 24 ∧ t.transcriptPos ≤ source.length ∧
      t.hintPos = s.hintPos ∧ t.sponge.counter = 0 ∧
      decodeCanonicalExt3 ((source.drop s.transcriptPos).take 24) = some x := by
  unfold proverExt3 at h
  cases hm : proverMessage hash s source 24 with
  | none => simp [hm] at h
  | some pair =>
      rcases pair with ⟨bytes,next⟩
      cases hd : decodeCanonicalExt3 bytes with
      | none => simp [hm,hd] at h
      | some value =>
          simp only [hm,hd,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          have hs := prover_message_reads_then_absorbs hash s next source bytes 24 hm
          exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,by rw [hs.2.2.2.2.1]; rfl,
            by rw [←hs.2.2.2.2.2]; exact hd⟩

theorem verifier_ext3_exact_cursor_and_bytes (hash : Hash) (s t : State) (x : Ext3)
    (h : verifierExt3 hash s = some (x,t)) :
    t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos ∧
      t.sponge.digest = s.sponge.digest ∧ t.sponge.counter = s.sponge.counter + 4 ∧
      x = reduceChallenge ((blockStream hash s.sponge.digest s.sponge.counter 4).take 120) := by
  unfold verifierExt3 at h
  cases hv : verifierMessage hash s 120 with
  | none => simp [hv] at h
  | some pair =>
      rcases pair with ⟨bytes,next⟩
      simp only [hv,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hc := verifier_message_preserves_read_cursors hash s next bytes 120 hv
      have hb : bytes = (blockStream hash s.sponge.digest s.sponge.counter 4).take 120 := by
        unfold verifierMessage at hv
        cases hs : squeeze hash s.sponge 120 with
        | none => simp [hs] at hv
        | some pair =>
            rcases pair with ⟨data,sp⟩
            simp only [hs,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at hv
            have he := (squeeze_success_exact hash s.sponge sp 120 data hs).2.2.2.2
            simpa only [←hv.1,ext3_challenge_uses_four_blocks] using he
      exact ⟨hc.2.1,hc.2.2.1,hc.2.2.2.1,by simpa only [ext3_challenge_uses_four_blocks] using hc.2.2.2.2,
        by rw [hb]⟩

theorem prover_many_exact_count_and_cursor (hash : Hash) (source : Bytes) (count : Nat)
    (s t : State) (xs : List Ext3) (h : proverExt3Many hash source count s = some (xs,t)) :
    xs.length = count ∧ t.transcriptPos = s.transcriptPos + 24 * count ∧ t.hintPos = s.hintPos := by
  induction count generalizing s xs with
  | zero =>
      cases h
      simp
  | succ n ih =>
      cases hp : proverExt3 hash s source with
      | none => simp [proverExt3Many,hp] at h
      | some pair =>
          rcases pair with ⟨x,next⟩
          cases hm : proverExt3Many hash source n next with
          | none => simp [proverExt3Many,hp,hm] at h
          | some pair =>
              rcases pair with ⟨values,last⟩
              simp only [proverExt3Many,hp,hm,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              have hc := prover_ext3_consumes_exact_canonical_bytes hash s next source x hp
              have ht := ih next values hm
              exact ⟨by simp [ht.1],by omega,ht.2.2.trans hc.2.2.1⟩

theorem verifier_many_exact_count_and_counter (hash : Hash) (count : Nat) (s t : State) (xs : List Ext3)
    (h : verifierExt3Many hash count s = some (xs,t)) :
    xs.length = count ∧ t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos ∧
      t.sponge.digest = s.sponge.digest ∧ t.sponge.counter = s.sponge.counter + 4 * count := by
  induction count generalizing s xs with
  | zero => cases h; simp
  | succ n ih =>
      cases hp : verifierExt3 hash s with
      | none => simp [verifierExt3Many,hp] at h
      | some pair =>
          rcases pair with ⟨x,next⟩
          cases hm : verifierExt3Many hash n next with
          | none => simp [verifierExt3Many,hp,hm] at h
          | some pair =>
              rcases pair with ⟨values,last⟩
              simp only [verifierExt3Many,hp,hm,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              have hc := verifier_ext3_exact_cursor_and_bytes hash s next x hp
              have ht := ih next values hm
              exact ⟨by simp [ht.1],ht.2.1.trans hc.1,ht.2.2.1.trans hc.2.1,
                ht.2.2.2.1.trans hc.2.2.1,by omega⟩

theorem geometric_powers_length (x : Ext3) (count : Nat) (previous : Ext3) :
    (geometricPowers x count previous).length = count := by
  induction count generalizing previous with
  | zero => rfl
  | succ n ih => simp [geometricPowers,ih]

theorem geometric_zero_does_not_squeeze (hash : Hash) (s : State) :
    geometricChallenge hash s 0 = some ([],s) := rfl

theorem geometric_one_does_not_squeeze (hash : Hash) (s : State) :
    geometricChallenge hash s 1 = some ([one],s) := rfl

theorem pow_input_exact_length (challenge nonce : Bytes)
    (hc : challenge.length = 32) (hn : nonce.length = 8) :
    (powInput challenge nonce).length = 64 := by simp [powInput,hc,hn]

theorem pow_sentinel_consumes_nothing (hash : Hash) (s : State) (source : Bytes) :
    verifyPow hash s source maxCounter = some s := by simp [verifyPow]

theorem pow_success_checks_actual_digest (hash : Hash) (s t : State) (source : Bytes) (threshold : Nat)
    (hn : threshold ≠ maxCounter) (h : verifyPow hash s source threshold = some t) :
    ∃ challenge afterChallenge nonce,
      verifierMessage hash s 32 = some (challenge,afterChallenge) ∧
      proverMessage hash afterChallenge source 8 = some (nonce,t) ∧
      challenge.length = 32 ∧ nonce.length = 8 ∧ powValue hash challenge nonce ≤ threshold := by
  unfold verifyPow at h
  split at h
  · contradiction
  simp only [hn,↓reduceIte] at h
  cases hc : verifierMessage hash s 32 with
  | none => simp [hc] at h
  | some pair =>
      rcases pair with ⟨challenge,afterChallenge⟩
      cases hp : proverMessage hash afterChallenge source 8 with
      | none => simp [hc,hp] at h
      | some pair =>
          rcases pair with ⟨nonce,afterNonce⟩
          simp only [hc,hp,bind,Option.bind] at h
          split at h
          · cases h
            exact ⟨challenge,afterChallenge,nonce,rfl,hp,
              (verifier_message_preserves_read_cursors hash s afterChallenge challenge 32 hc).1,
              (prover_message_reads_then_absorbs hash afterChallenge t source nonce 8 hp).1,
              ‹powValue hash challenge nonce ≤ threshold›⟩
          · contradiction

theorem vec_prefix_success_exact (s t : State) (hints : Bytes) (count : Nat)
    (h : consumeVecPrefix s hints count = some t) :
    t.hintPos = s.hintPos + 8 ∧ t.hintPos ≤ hints.length ∧
      t.transcriptPos = s.transcriptPos ∧ t.sponge = s.sponge ∧
      Transcript.fromLe ((hints.drop s.hintPos).take 8) = count := by
  unfold consumeVecPrefix at h
  cases hp : proverHint s hints 8 with
  | none => simp [hp] at h
  | some pair =>
      rcases pair with ⟨bytes,next⟩
      simp only [hp,bind,Option.bind] at h
      split at h
      · cases h
        have hs := hint_is_not_absorbed s t hints bytes 8 hp
        have hr : bytes = (hints.drop s.hintPos).take 8 := by
          unfold proverHint at hp
          cases he : readSlice hints s.hintPos 8 with
          | none => simp [he] at hp
          | some pair =>
              rcases pair with ⟨data,pos⟩
              simp only [he,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at hp
              exact hp.1.symm.trans (read_slice_success hints data s.hintPos 8 pos he).2.1
        exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,by rw [←hr]; assumption⟩
      · contradiction

end Audit.Wire3.Spongefish
