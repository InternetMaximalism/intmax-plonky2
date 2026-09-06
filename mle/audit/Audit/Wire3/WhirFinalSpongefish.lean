import Audit.Wire3.WhirFinal

/-!
# Concrete byte-reading engine for the WHIR final sumcheck

This instantiates ALL three WhirFinal.Engine observations with Spongefish's
executable operations: two canonical 24-byte prover Ext3 reads, optional PoW,
then one 120-byte verifier Ext3 challenge (four hash blocks). The recurrence,
randomness accumulation, final-vector fold, and EOF checks remain the SAME
WhirFinal functions, not a second independently accepting verifier.

The UInt8/Fin 256 adapter is lossless. Round operations never read hints, so the
local Spongefish hint cursor is zero; Context.hintPos remains separately fixed
for the final EOF check. No previously consumed hints are forgotten or accepted
by these round operations. The incoming Context and its afterRows sponge must
still be derived by earlier WHIR phases, which are not connected here. Neither
Authenticate nor final-row byte/Merkle parsing is instantiated by this module.

Hash remains an arbitrary deterministic 32-byte-output function, NOT an assumed
random oracle, collision-resistant hash, or entropy source. This connects Lean
models and proves exact successful byte consumption; it does not certify EVM
assembly, Keccak implementation, Rust IO patterns, probability, or PCS soundness.
-/
namespace Audit.Wire3.WhirFinalSpongefish

abbrev Bytes := WhirFinal.Bytes
abbrev Cursor := WhirFinal.Cursor
abbrev Hash := Spongefish.Hash

def toTranscriptBytes (bytes : Bytes) : Transcript.Bytes := bytes.map UInt8.val
def fromTranscriptBytes (bytes : Transcript.Bytes) : Bytes := bytes.map UInt8.mk

theorem bytes_roundtrip (bytes : Bytes) : fromTranscriptBytes (toTranscriptBytes bytes) = bytes := by
  simp only [fromTranscriptBytes, toTranscriptBytes, List.map_map]
  change List.map (fun b => b) bytes = bytes
  exact List.map_id bytes

theorem transcript_bytes_roundtrip (bytes : Transcript.Bytes) :
    toTranscriptBytes (fromTranscriptBytes bytes) = bytes := by
  simp only [fromTranscriptBytes, toTranscriptBytes, List.map_map]
  change List.map (fun b => b) bytes = bytes
  exact List.map_id bytes

theorem byte_conversion_length (bytes : Bytes) : (toTranscriptBytes bytes).length = bytes.length := by
  simp [toTranscriptBytes]

def toSpongefish (cursor : Cursor) : Spongefish.State := ⟨cursor.spongeState, cursor.transcriptPos, 0⟩
def fromSpongefish (state : Spongefish.State) : Cursor := ⟨state.transcriptPos, state.sponge⟩

theorem cursor_roundtrip (cursor : Cursor) : fromSpongefish (toSpongefish cursor) = cursor := rfl

theorem hint_free_state_roundtrip (state : Spongefish.State) (h : state.hintPos = 0) :
    toSpongefish (fromSpongefish state) = state := by
  cases state
  simp_all [toSpongefish, fromSpongefish]

def readMessage (hash : Hash) (bytes : Bytes) (cursor : Cursor) :
    Option (WhirFinal.RoundMessage × Cursor) := do
  let (c0, first) ← Spongefish.proverExt3 hash (toSpongefish cursor) (toTranscriptBytes bytes)
  let (c2, last) ← Spongefish.proverExt3 hash first (toTranscriptBytes bytes)
  pure (⟨c0.val, c2.val⟩, fromSpongefish last)

def checkPow (hash : Hash) (threshold : Nat) (bytes : Bytes) (cursor : Cursor) : Option Cursor :=
  (Spongefish.verifyPow hash (toSpongefish cursor) (toTranscriptBytes bytes) threshold).map fromSpongefish

def challenge (hash : Hash) (cursor : Cursor) : Option (Arithmetic.Ext3 × Cursor) := do
  let (r, next) ← Spongefish.verifierExt3 hash (toSpongefish cursor)
  pure (r.val, fromSpongefish next)

def engine (hash : Hash) : WhirFinal.Engine :=
  ⟨readMessage hash, checkPow hash, challenge hash⟩

theorem read_message_has_two_actual_reads (hash : Hash) (bytes : Bytes) (cursor next : Cursor)
    (message : WhirFinal.RoundMessage) (h : readMessage hash bytes cursor = some (message,next)) :
    ∃ c0 first c2 last,
      Spongefish.proverExt3 hash (toSpongefish cursor) (toTranscriptBytes bytes) = some (c0,first) ∧
      Spongefish.proverExt3 hash first (toTranscriptBytes bytes) = some (c2,last) ∧
      message.c0 = c0.val ∧ message.c2 = c2.val ∧ next = fromSpongefish last := by
  unfold readMessage at h
  cases h0 : Spongefish.proverExt3 hash (toSpongefish cursor) (toTranscriptBytes bytes) with
  | none => simp [h0] at h
  | some pair =>
      rcases pair with ⟨c0,first⟩
      cases h2 : Spongefish.proverExt3 hash first (toTranscriptBytes bytes) with
      | none => simp [h0,h2] at h
      | some pair =>
          rcases pair with ⟨c2,last⟩
          simp only [h0,h2,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          exact ⟨c0,first,c2,last,rfl,h2,rfl,rfl,rfl⟩

theorem read_message_exact_bytes_and_canonical (hash : Hash) (bytes : Bytes) (cursor next : Cursor)
    (message : WhirFinal.RoundMessage) (h : readMessage hash bytes cursor = some (message,next)) :
    next.transcriptPos = cursor.transcriptPos + 48 ∧ next.transcriptPos ≤ bytes.length ∧
      next.spongeState.counter = 0 ∧ Arithmetic.Canonical message.c0 ∧ Arithmetic.Canonical message.c2 := by
  obtain ⟨c0,first,c2,last,h0,h2,hm0,hm2,hn⟩ := read_message_has_two_actual_reads hash bytes cursor next message h
  have a := Spongefish.prover_ext3_consumes_exact_canonical_bytes hash (toSpongefish cursor) first
    (toTranscriptBytes bytes) c0 h0
  have b := Spongefish.prover_ext3_consumes_exact_canonical_bytes hash first last
    (toTranscriptBytes bytes) c2 h2
  rw [hn,hm0,hm2]
  exact ⟨by change last.transcriptPos = cursor.transcriptPos + 48; dsimp [toSpongefish] at a; omega,
    by simpa only [fromSpongefish,byte_conversion_length] using b.2.1,
    b.2.2.2.1,c0.property,c2.property⟩

theorem pow_success_has_actual_execution (hash : Hash) (threshold : Nat) (bytes : Bytes)
    (cursor next : Cursor) (h : checkPow hash threshold bytes cursor = some next) :
    ∃ state, Spongefish.verifyPow hash (toSpongefish cursor) (toTranscriptBytes bytes) threshold = some state ∧
      next = fromSpongefish state := by
  unfold checkPow at h
  cases hp : Spongefish.verifyPow hash (toSpongefish cursor) (toTranscriptBytes bytes) threshold with
  | none => simp [hp] at h
  | some state =>
      simp only [hp,Option.map,Option.some.injEq] at h
      exact ⟨state,rfl,h.symm⟩

def powBytes (threshold : Nat) : Nat := if threshold = Spongefish.maxCounter then 0 else 8

theorem pow_sentinel_exact (hash : Hash) (bytes : Bytes) (cursor : Cursor) :
    checkPow hash Spongefish.maxCounter bytes cursor = some cursor := by
  simp [checkPow,Spongefish.pow_sentinel_consumes_nothing,cursor_roundtrip]

theorem pow_success_cursor_exact (hash : Hash) (threshold : Nat) (bytes : Bytes) (cursor next : Cursor)
    (h : checkPow hash threshold bytes cursor = some next) :
    next.transcriptPos = cursor.transcriptPos + powBytes threshold := by
  by_cases hs : threshold = Spongefish.maxCounter
  · subst threshold
    rw [pow_sentinel_exact] at h
    cases h
    simp [powBytes]
  · obtain ⟨state,hp,hn⟩ := pow_success_has_actual_execution hash threshold bytes cursor next h
    obtain ⟨data,afterChallenge,nonce,hc,hm,_,_,_⟩ :=
      Spongefish.pow_success_checks_actual_digest hash (toSpongefish cursor) state (toTranscriptBytes bytes) threshold hs hp
    have a := Spongefish.verifier_message_preserves_read_cursors hash (toSpongefish cursor) afterChallenge data 32 hc
    have b := Spongefish.prover_message_reads_then_absorbs hash afterChallenge state (toTranscriptBytes bytes) nonce 8 hm
    simp only [powBytes,hs,↓reduceIte,hn,fromSpongefish]
    dsimp [toSpongefish] at a
    omega

theorem challenge_has_actual_squeeze (hash : Hash) (cursor next : Cursor) (r : Arithmetic.Ext3)
    (h : challenge hash cursor = some (r,next)) :
    ∃ value state, Spongefish.verifierExt3 hash (toSpongefish cursor) = some (value,state) ∧
      r = value.val ∧ next = fromSpongefish state := by
  unfold challenge at h
  cases hc : Spongefish.verifierExt3 hash (toSpongefish cursor) with
  | none => simp [hc] at h
  | some pair =>
      rcases pair with ⟨value,state⟩
      simp only [hc,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨value,state,rfl,rfl,rfl⟩

theorem challenge_exact_bytes_and_counter (hash : Hash) (cursor next : Cursor) (r : Arithmetic.Ext3)
    (h : challenge hash cursor = some (r,next)) :
    next.transcriptPos = cursor.transcriptPos ∧ next.spongeState.digest = cursor.spongeState.digest ∧
      next.spongeState.counter = cursor.spongeState.counter + 4 ∧ Arithmetic.Canonical r ∧
      r = (Spongefish.reduceChallenge ((Spongefish.blockStream hash cursor.spongeState.digest
        cursor.spongeState.counter 4).take 120)).val := by
  obtain ⟨value,state,hc,hr,hn⟩ := challenge_has_actual_squeeze hash cursor next r h
  have a := Spongefish.verifier_ext3_exact_cursor_and_bytes hash (toSpongefish cursor) state value hc
  rw [hn,hr]
  exact ⟨a.1,a.2.2.1,a.2.2.2.1,value.property,congrArg Subtype.val a.2.2.2.2⟩

theorem pow_execution_preserves_hint_cursor (hash : Hash) (threshold : Nat) (bytes : Transcript.Bytes)
    (before after : Spongefish.State) (h : Spongefish.verifyPow hash before bytes threshold = some after) :
    after.hintPos = before.hintPos := by
  by_cases hs : threshold = Spongefish.maxCounter
  · subst threshold
    rw [Spongefish.pow_sentinel_consumes_nothing] at h
    cases h
    rfl
  · obtain ⟨data,middle,nonce,hc,hm,_,_,_⟩ :=
      Spongefish.pow_success_checks_actual_digest hash before after bytes threshold hs h
    have a := Spongefish.verifier_message_preserves_read_cursors hash before middle data 32 hc
    have b := Spongefish.prover_message_reads_then_absorbs hash middle after bytes nonce 8 hm
    exact b.2.2.2.1.trans a.2.2.1

theorem pow_success_preserves_bound_and_zero_counter (hash : Hash) (threshold : Nat) (bytes : Bytes)
    (cursor next : Cursor) (hb : cursor.transcriptPos ≤ bytes.length) (hz : cursor.spongeState.counter = 0)
    (h : checkPow hash threshold bytes cursor = some next) :
    next.transcriptPos ≤ bytes.length ∧ next.spongeState.counter = 0 := by
  by_cases hs : threshold = Spongefish.maxCounter
  · subst threshold
    rw [pow_sentinel_exact] at h
    cases h
    exact ⟨hb,hz⟩
  · obtain ⟨state,hp,hn⟩ := pow_success_has_actual_execution hash threshold bytes cursor next h
    obtain ⟨data,middle,nonce,_,hm,_,_,_⟩ :=
      Spongefish.pow_success_checks_actual_digest hash (toSpongefish cursor) state (toTranscriptBytes bytes) threshold hs hp
    have b := Spongefish.prover_message_reads_then_absorbs hash middle state (toTranscriptBytes bytes) nonce 8 hm
    rw [hn]
    exact ⟨by simpa only [fromSpongefish,byte_conversion_length] using b.2.2.1,
      by change state.sponge.counter = 0; rw [b.2.2.2.2.1]; rfl⟩

/-- Every successful abstract round with this engine has exactly these concrete
    calls, in source order. Intermediate hint cursors are proved zero, so the
    adapter cannot reset or discard any hint consumption. -/
theorem round_success_actual_sequence (hash : Hash) (threshold : Nat) (bytes : Bytes)
    (s t : WhirFinal.State) (h : WhirFinal.roundStep (engine hash) threshold bytes s = some t) :
    ∃ c0 first c2 last afterPow r next,
      Spongefish.proverExt3 hash (toSpongefish s.cursor) (toTranscriptBytes bytes) = some (c0,first) ∧
      Spongefish.proverExt3 hash first (toTranscriptBytes bytes) = some (c2,last) ∧
      Spongefish.verifyPow hash last (toTranscriptBytes bytes) threshold = some afterPow ∧
      Spongefish.verifierExt3 hash afterPow = some (r,next) ∧
      first.hintPos = 0 ∧ last.hintPos = 0 ∧ afterPow.hintPos = 0 ∧ next.hintPos = 0 ∧
      t = WhirFinal.advance s ⟨c0.val,c2.val⟩ r.val (fromSpongefish next) := by
  obtain ⟨message,am,ap,r,nxt,hm,_,_,hp,hr,_,ht⟩ :=
    WhirFinal.round_step_success (engine hash) threshold bytes s t h
  obtain ⟨c0,first,c2,last,h0,h2,hm0,hm2,ham⟩ :=
    read_message_has_two_actual_reads hash bytes s.cursor am message hm
  have hfirst : first.hintPos = 0 :=
    (Spongefish.prover_ext3_consumes_exact_canonical_bytes hash (toSpongefish s.cursor) first
      (toTranscriptBytes bytes) c0 h0).2.2.1
  have hlast : last.hintPos = 0 :=
    ((Spongefish.prover_ext3_consumes_exact_canonical_bytes hash first last
      (toTranscriptBytes bytes) c2 h2).2.2.1).trans hfirst
  obtain ⟨powState,hpow,hap⟩ := pow_success_has_actual_execution hash threshold bytes am ap hp
  rw [ham,hint_free_state_roundtrip last hlast] at hpow
  have hpowHint := (pow_execution_preserves_hint_cursor hash threshold (toTranscriptBytes bytes) last powState hpow).trans hlast
  obtain ⟨value,final,hchallenge,hrv,hnxt⟩ := challenge_has_actual_squeeze hash ap nxt r hr
  rw [hap,hint_free_state_roundtrip powState hpowHint] at hchallenge
  have hfinal := (Spongefish.verifier_ext3_exact_cursor_and_bytes hash powState final value hchallenge).2.1.trans hpowHint
  refine ⟨c0,first,c2,last,powState,value,final,h0,h2,hpow,hchallenge,hfirst,hlast,hpowHint,hfinal,?_⟩
  rw [ht,hrv,hnxt]
  have hm : message = ⟨c0.val,c2.val⟩ := by cases message; simp_all
  rw [hm]

theorem round_success_exact_consumption (hash : Hash) (threshold : Nat) (bytes : Bytes)
    (s t : WhirFinal.State) (h : WhirFinal.roundStep (engine hash) threshold bytes s = some t) :
    t.cursor.transcriptPos = s.cursor.transcriptPos + 48 + powBytes threshold ∧
      t.cursor.transcriptPos ≤ bytes.length ∧ t.cursor.spongeState.counter = 4 ∧
      t.finalRandomness.length = s.finalRandomness.length + 1 := by
  obtain ⟨message,am,ap,r,nxt,hm,_,_,hp,hr,_,ht⟩ :=
    WhirFinal.round_step_success (engine hash) threshold bytes s t h
  have a := read_message_exact_bytes_and_canonical hash bytes s.cursor am message hm
  have b := pow_success_cursor_exact hash threshold bytes am ap hp
  have bz := pow_success_preserves_bound_and_zero_counter hash threshold bytes am ap a.2.1 a.2.2.1 hp
  have c := challenge_exact_bytes_and_counter hash ap nxt r hr
  have hl := WhirFinal.round_step_adds_one_challenge (engine hash) threshold bytes s t h
  refine ⟨?_,?_,?_,hl⟩
  · change t.cursor.transcriptPos = _
    rw [ht]
    change nxt.transcriptPos = _
    omega
  · rw [ht]
    change nxt.transcriptPos ≤ _
    omega
  · rw [ht]
    change nxt.spongeState.counter = 4
    omega

theorem rounds_success_exact_consumption (hash : Hash) (threshold : Nat) (bytes : Bytes)
    (count : Nat) (s t : WhirFinal.State)
    (h : WhirFinal.runRounds (engine hash) threshold bytes count s = some t) :
    t.cursor.transcriptPos = s.cursor.transcriptPos + count * (48 + powBytes threshold) ∧
      t.finalRandomness.length = s.finalRandomness.length + count := by
  have hl := WhirFinal.completed_round_count_exact (engine hash) threshold bytes count s t h
  refine ⟨?_,hl⟩
  induction count generalizing s with
  | zero =>
      have hs : s = t := by simpa [WhirFinal.runRounds] using h
      simp [hs]
  | succ n ih =>
      cases hs : WhirFinal.roundStep (engine hash) threshold bytes s with
      | none => simp [WhirFinal.runRounds,hs] at h
      | some middle =>
          simp only [WhirFinal.runRounds,hs] at h
          have a := round_success_exact_consumption hash threshold bytes s middle hs
          have b := ih middle h (by omega)
          rw [Nat.succ_mul]
          omega

/-- Exact transcript suffix length, from the SAME final verifier's acceptance.
    Earlier bytes and already consumed hints are represented only by Context. -/
theorem end_success_exact_transcript_and_hint_eof (hash : Hash) (auth : WhirTerminal.Authenticate)
    (context : WhirFinal.Context) (bytes hints : Bytes) (vector : List Arithmetic.Ext3)
    (rows : List WhirTerminal.GroupRows)
    (h : WhirFinal.verifyEnd auth (engine hash) context bytes hints vector rows = true) :
    bytes.length = context.afterRows.transcriptPos + context.rowPlan.finalRounds * (48 + powBytes context.powThreshold) ∧
      context.hintPos = hints.length := by
  obtain ⟨result,hr,_,_,ht,hh⟩ := WhirFinal.end_success_has_nonzero_same_vector_fold_and_exact_eof
    auth (engine hash) context bytes hints vector rows h
  have hc := (rounds_success_exact_consumption hash context.powThreshold bytes context.rowPlan.finalRounds
    (WhirFinal.start context) result hr).1
  exact ⟨ht.symm.trans hc,hh⟩

theorem end_with_round_requires_actual_reads (hash : Hash) (auth : WhirTerminal.Authenticate)
    (context : WhirFinal.Context) (bytes hints : Bytes) (vector : List Arithmetic.Ext3)
    (rows : List WhirTerminal.GroupRows) (count : Nat) (hn : context.rowPlan.finalRounds = count + 1)
    (h : WhirFinal.verifyEnd auth (engine hash) context bytes hints vector rows = true) :
    ∃ c0 first c2 last,
      Spongefish.proverExt3 hash (toSpongefish context.afterRows) (toTranscriptBytes bytes) = some (c0,first) ∧
      Spongefish.proverExt3 hash first (toTranscriptBytes bytes) = some (c2,last) := by
  obtain ⟨_,_,result,hr,_,_⟩ := WhirFinal.end_success_same_vector_and_all_checks
    auth (engine hash) context bytes hints vector rows h
  rw [hn] at hr
  cases hs : WhirFinal.roundStep (engine hash) context.powThreshold bytes (WhirFinal.start context) with
  | none => simp [WhirFinal.runRounds,hs] at hr
  | some next =>
      obtain ⟨c0,first,c2,last,_,_,_,h0,h2,_⟩ := round_success_actual_sequence
        hash context.powThreshold bytes (WhirFinal.start context) next hs
      exact ⟨c0,first,c2,last,h0,h2⟩

theorem successful_byte_operations_execute_round (hash : Hash) (threshold : Nat) (bytes : Bytes)
    (s : WhirFinal.State) (message : WhirFinal.RoundMessage) (am ap next : Cursor) (r : Arithmetic.Ext3)
    (hm : readMessage hash bytes s.cursor = some (message,am))
    (hp : checkPow hash threshold bytes am = some ap)
    (hr : challenge hash ap = some (r,next)) :
    WhirFinal.roundStep (engine hash) threshold bytes s = some (WhirFinal.advance s message r next) := by
  have hc := read_message_exact_bytes_and_canonical hash bytes s.cursor am message hm
  have hrc := (challenge_exact_bytes_and_counter hash ap next r hr).2.2.2.1
  simp [WhirFinal.roundStep,engine,hm,hp,hr,hc.2.2.2.1,hc.2.2.2.2,hrc]

theorem round_without_pow_consumes_48 (hash : Hash) (bytes : Bytes) (s t : WhirFinal.State)
    (h : WhirFinal.roundStep (engine hash) Spongefish.maxCounter bytes s = some t) :
    t.cursor.transcriptPos = s.cursor.transcriptPos + 48 := by
  simpa only [powBytes,↓reduceIte,Nat.add_zero] using (round_success_exact_consumption hash
    Spongefish.maxCounter bytes s t h).1

theorem round_with_pow_consumes_56 (hash : Hash) (threshold : Nat) (bytes : Bytes) (s t : WhirFinal.State)
    (hp : threshold ≠ Spongefish.maxCounter)
    (h : WhirFinal.roundStep (engine hash) threshold bytes s = some t) :
    t.cursor.transcriptPos = s.cursor.transcriptPos + 56 := by
  have hc := (round_success_exact_consumption hash threshold bytes s t h).1
  simp only [powBytes,hp,↓reduceIte] at hc
  omega

/-- A local execution example with two zero coefficients. Every hash is allowed:
    the challenge is genuinely squeezed from that hash, not fixed by this test.
    This is one syntactically valid round, not a PCS proof or a valid Context. -/
def zeroMessageBytes : Bytes := List.replicate 48 0

def afterZeroMessages (hash : Hash) (initial : Spongefish.Sponge) : Cursor :=
  ⟨48, Spongefish.absorb hash (Spongefish.absorb hash initial (List.replicate 24 Spongefish.zeroByte))
    (List.replicate 24 Spongefish.zeroByte)⟩

theorem zero_messages_read_two_canonical_values (hash : Hash) (initial : Spongefish.Sponge) :
    readMessage hash zeroMessageBytes ⟨0,initial⟩ =
      some (⟨Arithmetic.zero,Arithmetic.zero⟩,afterZeroMessages hash initial) := by
  have hz : (UInt8.val (0 : UInt8)) = (0 : Fin 256) := rfl
  simp [readMessage,zeroMessageBytes,toSpongefish,toTranscriptBytes,Spongefish.proverExt3,
    Spongefish.proverMessage,Spongefish.readSlice,Spongefish.decodeCanonicalExt3,
    Transcript.fromLe,Arithmetic.modulus,fromSpongefish,afterZeroMessages,
    Spongefish.zeroByte,Arithmetic.zero,Spongefish.absorb,hz,Nat.min_def]

theorem zero_message_round_executes (hash : Hash) (initial : Spongefish.Sponge) (sum : Arithmetic.Ext3) :
    ∃ result, WhirFinal.roundStep (engine hash) Spongefish.maxCounter zeroMessageBytes
      ⟨⟨0,initial⟩,sum,[]⟩ = some result ∧ result.cursor.transcriptPos = 48 ∧
      result.finalRandomness.length = 1 := by
  let am := afterZeroMessages hash initial
  let r := Spongefish.reduceChallenge ((Spongefish.blockStream hash am.spongeState.digest 0 4).take 120)
  let next : Cursor := ⟨48,⟨am.spongeState.digest,4⟩⟩
  have hr : challenge hash am = some (r.val,next) := by
    simp [challenge,Spongefish.verifierExt3,Spongefish.verifierMessage,Spongefish.squeeze,
      toSpongefish,fromSpongefish,Spongefish.blocksNeeded,Spongefish.maxCounter,
      am,afterZeroMessages,Spongefish.absorb,r,next]
  have h := successful_byte_operations_execute_round hash Spongefish.maxCounter zeroMessageBytes
    ⟨⟨0,initial⟩,sum,[]⟩ ⟨Arithmetic.zero,Arithmetic.zero⟩ am am next r.val
    (zero_messages_read_two_canonical_values hash initial) (pow_sentinel_exact hash zeroMessageBytes am) hr
  exact ⟨_,h,rfl,rfl⟩

end Audit.Wire3.WhirFinalSpongefish
