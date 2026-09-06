import Audit.Wire3.OuterInitial

/-!
Checked outer transcript adapters, using the frozen Audit.Wire3.OuterInitial snapshot.
The snapshot is INTERNAL digest[32] || counterLE[8], not proof-wire data.
Malformed snapshots return none: no zero/default state or successful fallback.
Actual coupled-round and constituent-index frames follow TranscriptV2 and
MleVerifierV2. Root absorption belongs to Audit.Wire3.OuterInitial, not a new terminal step;
expected packed claims are constructed AFTER index challenges for WHIR context.

Verifier.Engine's hooks are total, while these adapters are deliberately Option.
Compatibility theorems below only connect successful calls to a total Engine
that agrees on those same calls; no unconditional complete Engine is claimed.
Canonical field inputs, physical sizes, deployment/config meaning, source/Yul
refinement, hash security, adaptive fixedness and complete PCS soundness remain
separate boundaries. Hash is only an arbitrary deterministic function.
-/
namespace Audit.Wire3.OuterAdapter
open Audit.Wire3
open Audit.Wire3.OuterInitial

theorem from_le_bound (bs : Transcript.Bytes) : Transcript.fromLe bs < 256^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    have hb := b.isLt
    simp only [Transcript.fromLe,List.length_cons,Nat.pow_succ]
    omega

theorem le_from_le (bs : Transcript.Bytes) :
    Transcript.le bs.length (Transcript.fromLe bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hm : (b.val+256*Transcript.fromLe bs)%256 = b.val := by omega
    have hd : (b.val+256*Transcript.fromLe bs)/256 = Transcript.fromLe bs := by omega
    simp only [List.length_cons,Transcript.fromLe,Transcript.le,hm,hd,ih]

def decode (raw : Verifier.Bytes) : Option Transcript.State :=
  if h : raw.length=40 then
    some ⟨⟨(bytes raw).take 32,by simp [bytes_length,h,Nat.min_def]⟩,
      Transcript.fromLe ((bytes raw).drop 32)⟩
  else none

theorem decode_bad_length (raw : Verifier.Bytes) (h : raw.length≠40) : decode raw=none := by
  simp [decode,h]

theorem decode_success (raw : Verifier.Bytes) (s : Transcript.State) (h : decode raw=some s) :
    raw.length=40 ∧ s.digest.bytes=(bytes raw).take 32 ∧
      s.counter=Transcript.fromLe ((bytes raw).drop 32) ∧ s.counter<Transcript.u64Limit := by
  unfold decode at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq] at h
    subst s
    refine ⟨hl,rfl,rfl,?_⟩
    have hb := from_le_bound ((bytes raw).drop 32)
    simpa only [List.length_drop,bytes_length,hl,Transcript.u64Limit] using hb
  · simp at h

theorem decode_snapshot (s : Transcript.State) (hc : s.counter<Transcript.u64Limit) :
    decode (snapshot s)=some s := by
  simp only [decode,snapshot_length,↓reduceDIte]
  congr 1
  have hd := snapshot_retains_digest s
  have hn := snapshot_retains_counter s hc
  cases s with
  | mk d n =>
    cases d
    simp only [Transcript.State.mk.injEq,Transcript.Digest.mk.injEq]
    exact ⟨hd,hn⟩

theorem snapshot_decoded (raw : Verifier.Bytes) (s : Transcript.State) (h : decode raw=some s) :
    snapshot s=raw := by
  have hs := decode_success raw s h
  unfold snapshot
  rw [hs.2.1,hs.2.2.1]
  have hl : ((bytes raw).drop 32).length=8 := by simp [bytes_length,hs.1]
  rw [←hl,le_from_le,List.take_append_drop,bytes_roundtrip]

theorem decode_has_value_iff_length (raw : Verifier.Bytes) :
    (∃ s,decode raw=some s) ↔ raw.length=40 := by
  constructor
  · rintro ⟨s,hs⟩; exact (decode_success raw s hs).1
  · intro h; simp [decode,h]

def encodedVec (xs : List Verifier.Ext3) : Transcript.Bytes :=
  Transcript.ext3VecBytes (xs.map Connections.toTranscript)
def VecFits (xs : List Verifier.Ext3) : Prop := (encodedVec xs).length < Transcript.u64Limit
instance (xs : List Verifier.Ext3) : Decidable (VecFits xs) := inferInstanceAs (Decidable (_<_))
theorem encoded_vector_length (xs : List Verifier.Ext3) : (encodedVec xs).length=8+24*xs.length := by
  simp only [encodedVec,Transcript.ext3_vector_length,List.length_map]

def roundCommitted (hash : Hash) (s : Transcript.State) (i : Nat) (log gate : List Verifier.Ext3) : Transcript.State :=
  Transcript.commitRound hash s i (log.map Connections.toTranscript) (gate.map Connections.toTranscript)

def roundResult (hash : Hash) (s : Transcript.State) (i : Nat) (log gate : List Verifier.Ext3) : Verifier.RoundChallenges :=
  let committed := roundCommitted hash s i log gate
  let (log,t) := draw hash committed
  let (gate,u) := draw hash t
  ⟨snapshot u,log,gate⟩

def commitChecked (hash : Hash) (raw : Verifier.Bytes) (i : Nat) (log gate : List Verifier.Ext3) :
    Option Verifier.RoundChallenges := do
  let s ← decode raw
  let (xs,t) ← Transcript.coupledRound hash s i (log.map Connections.toTranscript) (gate.map Connections.toTranscript)
  match xs with
  | [a,b,c,d,e,f] => pure ⟨snapshot t,Connections.fromTranscript ⟨a,b,c⟩,Connections.fromTranscript ⟨d,e,f⟩⟩
  | _ => none

theorem commit_decode_failure (hash : Hash) (raw : Verifier.Bytes) (i : Nat) (log gate : List Verifier.Ext3)
    (h : decode raw=none) : commitChecked hash raw i log gate=none := by simp [commitChecked,h]

theorem commit_checked_exact (hash : Hash) (raw : Verifier.Bytes) (s : Transcript.State)
    (i : Nat) (log gate : List Verifier.Ext3) (hd : decode raw=some s)
    (hi : i<Transcript.u64Limit) (hl : VecFits log) (hg : VecFits gate) :
    commitChecked hash raw i log gate=some (roundResult hash s i log gate) := by
  have hh : i<Transcript.u64Limit ∧
      (Transcript.ext3VecBytes (log.map Connections.toTranscript)).length<Transcript.u64Limit ∧
      (Transcript.ext3VecBytes (gate.map Connections.toTranscript)).length<Transcript.u64Limit := ⟨hi,hl,hg⟩
  simp only [commitChecked,hd,bind,Option.bind,Transcript.coupledRound,hh,↓reduceIte]
  change (do
    let (xs,t) ← Transcript.squeezeMany hash 6 ⟨(roundCommitted hash s i log gate).digest,0⟩
    match xs with
    | [a,b,c,d,e,f] => pure (⟨snapshot t,Connections.fromTranscript ⟨a,b,c⟩,Connections.fromTranscript ⟨d,e,f⟩⟩ : Verifier.RoundChallenges)
    | _ => none) = _
  rw [Transcript.six_squeezes_use_consecutive_inputs]
  rfl

theorem round_result_snapshot_decodes (hash : Hash) (s : Transcript.State)
    (i : Nat) (log gate : List Verifier.Ext3) :
    decode (roundResult hash s i log gate).transcript =
      some ⟨(roundCommitted hash s i log gate).digest,6⟩ := by
  exact decode_snapshot ⟨(roundCommitted hash s i log gate).digest,6⟩ (by change 6 < Transcript.u64Limit; decide)

theorem round_result_exact_counter_inputs (hash : Hash) (s : Transcript.State)
    (i : Nat) (log gate : List Verifier.Ext3) :
    (roundResult hash s i log gate).log=ext3At hash (roundCommitted hash s i log gate).digest 0 ∧
    (roundResult hash s i log gate).gate=ext3At hash (roundCommitted hash s i log gate).digest 3 := by
  exact ⟨rfl,rfl⟩

theorem commit_success_exact (hash : Hash) (raw : Verifier.Bytes) (i : Nat)
    (log gate : List Verifier.Ext3) (r : Verifier.RoundChallenges)
    (h : commitChecked hash raw i log gate=some r) :
    ∃ s,decode raw=some s ∧ i<Transcript.u64Limit ∧ VecFits log ∧ VecFits gate ∧
      r=roundResult hash s i log gate ∧
      decode r.transcript=some ⟨(roundCommitted hash s i log gate).digest,6⟩ := by
  cases hd : decode raw with
  | none => simp [commitChecked,hd] at h
  | some s =>
    have hf : i<Transcript.u64Limit ∧ VecFits log ∧ VecFits gate := by
      apply Decidable.byContradiction
      intro hn
      simp only [VecFits,encodedVec] at hn
      simp [commitChecked,hd,Transcript.coupledRound,hn] at h
    have he := commit_checked_exact hash raw s i log gate hd hf.1 hf.2.1 hf.2.2
    have hr := Option.some.inj (h.symm.trans he)
    refine ⟨s,rfl,hf.1,hf.2.1,hf.2.2,hr,?_⟩
    rw [hr]
    exact round_result_snapshot_decodes hash s i log gate

def claimCells (u : Verifier.UsedClaims) : List (List Verifier.Ext3) :=
  [u.logPreprocessed,u.logWitness,u.logNormInverse,u.gatePreprocessed,u.gateWitness,[]]
def ClaimsFit (u : Verifier.UsedClaims) : Prop :=
  (claimCells u).all (fun xs => decide (VecFits xs))=true
instance (u : Verifier.UsedClaims) : Decidable (ClaimsFit u) := inferInstanceAs (Decidable (_=_))

theorem claims_fit_iff (u : Verifier.UsedClaims) : ClaimsFit u ↔ ∀ xs∈claimCells u,VecFits xs := by
  simp only [ClaimsFit,List.all_eq_true,decide_eq_true_eq]
theorem six_claim_cells_last_empty (u : Verifier.UsedClaims) :
    (claimCells u).length=6 ∧ (claimCells u).get? 5=some [] := ⟨rfl,rfl⟩

def claimsCommitted (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims) : Transcript.State :=
  Transcript.commitClaims hash s (u.logPreprocessed.map Connections.toTranscript)
    (u.logWitness.map Connections.toTranscript) (u.logNormInverse.map Connections.toTranscript)
    (u.gatePreprocessed.map Connections.toTranscript) (u.gateWitness.map Connections.toTranscript)

theorem claims_commit_counter_zero (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims) :
    (claimsCommitted hash s u).counter=0 := rfl

theorem claims_commit_all_cells_in_order (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims) :
    claimsCommitted hash s u = Transcript.domain hash
      ((claimCells u).foldl (fun t xs => Transcript.absorb hash t 6 (encodedVec xs))
        (Transcript.domain hash s "pcs-constituent-claims-v3")) "pcs-constituent-index-v3" := rfl

structure SampleResult where
  points : Verifier.IndexPoints
  transcript : Verifier.Bytes

def sampleResult (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims) (bits : Nat) : SampleResult :=
  let (log,t) := drawMany hash bits (claimsCommitted hash s u)
  let (gate,last) := drawMany hash bits t
  ⟨⟨log,gate⟩,snapshot last⟩

def sampleChecked (hash : Hash) (raw : Verifier.Bytes) (u : Verifier.UsedClaims) (bits : Nat) : Option SampleResult := do
  let s ← decode raw
  if ¬ClaimsFit u then none else do
    let (log,t) ← squeezeExt3Many hash bits (claimsCommitted hash s u)
    let (gate,last) ← squeezeExt3Many hash bits t
    pure ⟨⟨log,gate⟩,snapshot last⟩

theorem sample_decode_failure (hash : Hash) (raw : Verifier.Bytes) (u : Verifier.UsedClaims) (bits : Nat)
    (h : decode raw=none) : sampleChecked hash raw u bits=none := by simp [sampleChecked,h]

theorem sample_checked_exact (hash : Hash) (raw : Verifier.Bytes) (s : Transcript.State)
    (u : Verifier.UsedClaims) (bits : Nat) (hd : decode raw=some s)
    (hf : ClaimsFit u) (hb : 6*bits<Transcript.u64Limit) :
    sampleChecked hash raw u bits=some (sampleResult hash s u bits) := by
  have hl := draw_many_matches_checked_squeezes hash bits (claimsCommitted hash s u)
    (by change 0+3*bits<Transcript.u64Limit; omega)
  have hg := draw_many_matches_checked_squeezes hash bits (drawMany hash bits (claimsCommitted hash s u)).2
    (by rw [(draw_many_shape hash bits (claimsCommitted hash s u)).2.2];
        change 0+3*bits+3*bits<Transcript.u64Limit; omega)
  simp only [sampleChecked,hd,hf,not_true_eq_false,↓reduceIte,bind,Option.bind,hl,hg,sampleResult,pure]

theorem sample_result_shape (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims) (bits : Nat) :
    (sampleResult hash s u bits).points.log.length=bits ∧
    (sampleResult hash s u bits).points.gate.length=bits ∧
    (sampleResult hash s u bits).transcript=
      snapshot ⟨(claimsCommitted hash s u).digest,6*bits⟩ := by
  have hl := draw_many_shape hash bits (claimsCommitted hash s u)
  have hg := draw_many_shape hash bits (drawMany hash bits (claimsCommitted hash s u)).2
  refine ⟨hl.1,hg.1,?_⟩
  change snapshot (drawMany hash bits (drawMany hash bits (claimsCommitted hash s u)).2).2 = _
  congr 1
  cases h : (drawMany hash bits (drawMany hash bits (claimsCommitted hash s u)).2).2 with
  | mk d n =>
    simp only [Transcript.State.mk.injEq]
    have hd : d=(claimsCommitted hash s u).digest := by simpa only [h] using hg.2.1.trans hl.2.1
    refine ⟨hd,?_⟩
    have hn := hg.2.2
    rw [hl.2.2] at hn
    change _=0+3*bits+3*bits at hn
    simp only [h] at hn
    omega

theorem sample_result_decodes (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims) (bits : Nat)
    (hb : 6*bits<Transcript.u64Limit) :
    decode (sampleResult hash s u bits).transcript=some ⟨(claimsCommitted hash s u).digest,6*bits⟩ := by
  rw [(sample_result_shape hash s u bits).2.2]
  exact decode_snapshot _ hb

theorem sampled_log_index_counter (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims)
    (bits i : Nat) (hi : i<bits) :
    (sampleResult hash s u bits).points.log.get? i=some (ext3At hash (claimsCommitted hash s u).digest (3*i)) := by
  simpa only [sampleResult,claims_commit_counter_zero,Nat.zero_add] using
    draw_many_at hash bits (claimsCommitted hash s u) i hi

theorem sampled_gate_index_counter (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims)
    (bits i : Nat) (hi : i<bits) :
    (sampleResult hash s u bits).points.gate.get? i=
      some (ext3At hash (claimsCommitted hash s u).digest (3*bits+3*i)) := by
  have h := draw_many_at hash bits (drawMany hash bits (claimsCommitted hash s u)).2 i hi
  rw [(draw_many_shape hash bits (claimsCommitted hash s u)).2.1,
      (draw_many_shape hash bits (claimsCommitted hash s u)).2.2] at h
  simpa only [sampleResult,claims_commit_counter_zero,Nat.zero_add] using h

theorem zero_index_bits_still_absorb_claims (hash : Hash) (s : Transcript.State) (u : Verifier.UsedClaims) :
    (sampleResult hash s u 0).points.log=[] ∧ (sampleResult hash s u 0).points.gate=[] ∧
    (sampleResult hash s u 0).transcript=snapshot (claimsCommitted hash s u) := ⟨rfl,rfl,rfl⟩

def advance (s : Verifier.RoundState) (m : Verifier.CoupledMessage) (r : Verifier.RoundChallenges) : Verifier.RoundState :=
  ⟨r.transcript,s.roundIndex+1,Verifier.evaluateRound s.logClaim m.1 r.log,
    Verifier.evaluateRound s.gateClaim m.2 r.gate,s.logPoint++[r.log],s.gatePoint++[r.gate]⟩

theorem advance_is_existing_round_step (commit : Verifier.CommitRound) (s : Verifier.RoundState)
    (m : Verifier.CoupledMessage) :
    advance s m (commit s.transcript s.roundIndex m.1 m.2)=Verifier.roundStep commit s m := rfl

def stepChecked (hash : Hash) (s : Verifier.RoundState) (m : Verifier.CoupledMessage) : Option Verifier.RoundState := do
  let r ← commitChecked hash s.transcript s.roundIndex m.1 m.2
  pure (advance s m r)

def runLoop (hash : Hash) : Verifier.RoundState → List Verifier.CoupledMessage → Option Verifier.RoundState
  | s,[] => some s
  | s,m::ms => do
    let t ← stepChecked hash s m
    runLoop hash t ms

/-- The public checked loop also validates the snapshot for an empty message
list. Proof round-vector shape is a separate source preflight, not zip magic. -/
def runChecked (hash : Hash) (s : Verifier.RoundState) (ms : List Verifier.CoupledMessage) : Option Verifier.RoundState := do
  let _ ← decode s.transcript
  runLoop hash s ms

theorem checked_loop_bad_snapshot_rejected (hash : Hash) (s : Verifier.RoundState)
    (ms : List Verifier.CoupledMessage) (h : decode s.transcript=none) : runChecked hash s ms=none := by
  simp [runChecked,h]

theorem step_success_same_actual_inputs (hash : Hash) (s t : Verifier.RoundState) (m : Verifier.CoupledMessage)
    (h : stepChecked hash s m=some t) :
    ∃ r,commitChecked hash s.transcript s.roundIndex m.1 m.2=some r ∧ t=advance s m r := by
  cases hr : commitChecked hash s.transcript s.roundIndex m.1 m.2 with
  | none => simp [stepChecked,hr] at h
  | some r => exact ⟨r,rfl,by simpa [stepChecked,hr] using h.symm⟩

/-- Explicit conditional compatibility, not a claim that an arbitrary total
Engine computes this transcript. No failure is converted to a total result. -/
def CommitAgrees (hash : Hash) (commit : Verifier.CommitRound) : Prop :=
  ∀ raw i log gate r,commitChecked hash raw i log gate=some r → commit raw i log gate=r

theorem loop_success_matches_existing (hash : Hash) (commit : Verifier.CommitRound)
    (hc : CommitAgrees hash commit) (s t : Verifier.RoundState) (ms : List Verifier.CoupledMessage)
    (h : runLoop hash s ms=some t) : t=Verifier.runRounds commit s ms := by
  induction ms generalizing s with
  | nil => simpa [runLoop,Verifier.runRounds] using h.symm
  | cons m ms ih =>
    cases hs : stepChecked hash s m with
    | none => simp [runLoop,hs] at h
    | some mid =>
      obtain ⟨r,hr,hm⟩ := step_success_same_actual_inputs hash s mid m hs
      have hh : mid=Verifier.roundStep commit s m := by
        rw [hm,←hc _ _ _ _ _ hr,advance_is_existing_round_step]
      simp only [runLoop,hs,bind,Option.bind] at h
      simpa only [Verifier.runRounds,hh] using ih mid h

theorem checked_success_matches_existing (hash : Hash) (commit : Verifier.CommitRound)
    (hc : CommitAgrees hash commit) (s t : Verifier.RoundState) (ms : List Verifier.CoupledMessage)
    (h : runChecked hash s ms=some t) : t=Verifier.runRounds commit s ms := by
  cases hd : decode s.transcript with
  | none => simp [runChecked,hd] at h
  | some d => exact loop_success_matches_existing hash commit hc s t ms (by simpa [runChecked,hd] using h)

theorem advance_lengths (s : Verifier.RoundState) (m : Verifier.CoupledMessage) (r : Verifier.RoundChallenges) :
    (advance s m r).roundIndex=s.roundIndex+1 ∧
    (advance s m r).logPoint.length=s.logPoint.length+1 ∧
    (advance s m r).gatePoint.length=s.gatePoint.length+1 := by simp [advance]

theorem loop_success_lengths (hash : Hash) (s t : Verifier.RoundState) (ms : List Verifier.CoupledMessage)
    (h : runLoop hash s ms=some t) :
    t.roundIndex=s.roundIndex+ms.length ∧ t.logPoint.length=s.logPoint.length+ms.length ∧
    t.gatePoint.length=s.gatePoint.length+ms.length := by
  induction ms generalizing s with
  | nil =>
    simp only [runLoop,Option.some.injEq] at h
    subst t
    simp
  | cons m ms ih =>
    cases hs : stepChecked hash s m with
    | none => simp [runLoop,hs] at h
    | some mid =>
      obtain ⟨r,hr,hm⟩ := step_success_same_actual_inputs hash s mid m hs
      clear hr
      have hh := ih mid (by simpa [runLoop,hs] using h)
      have hl := advance_lengths s m r
      rw [hm] at hh
      simp only [List.length_cons]
      exact ⟨by omega,by omega,by omega⟩

theorem bounded_loop_exists (hash : Hash) (s : Verifier.RoundState) (d : Transcript.State)
    (ms : List Verifier.CoupledMessage) (hd : decode s.transcript=some d)
    (hb : s.roundIndex+ms.length<Transcript.u64Limit)
    (hm : ∀ m∈ms,VecFits m.1 ∧ VecFits m.2) :
    ∃ t last,runLoop hash s ms=some t ∧ decode t.transcript=some last := by
  induction ms generalizing s d with
  | nil => exact ⟨s,d,rfl,hd⟩
  | cons m ms ih =>
    have hf := hm m (by simp)
    let r := roundResult hash d s.roundIndex m.1 m.2
    have hr : commitChecked hash s.transcript s.roundIndex m.1 m.2=some r :=
      commit_checked_exact hash _ d _ _ _ hd (by simp only [List.length_cons] at hb; omega) hf.1 hf.2
    let mid := advance s m r
    have hs : stepChecked hash s m=some mid := by simp only [stepChecked,hr,bind,Option.bind,pure,mid]
    have hdecode : decode mid.transcript=some ⟨(roundCommitted hash d s.roundIndex m.1 m.2).digest,6⟩ :=
      round_result_snapshot_decodes hash d s.roundIndex m.1 m.2
    obtain ⟨t,last,ht,hl⟩ := ih mid _ hdecode
      (by change s.roundIndex+1+ms.length<Transcript.u64Limit; simp only [List.length_cons] at hb; omega)
      (fun m hh => hm m (by simp [hh]))
    exact ⟨t,last,by simp only [runLoop,hs,bind,Option.bind,ht],hl⟩

theorem bounded_checked_run_exists (hash : Hash) (s : Verifier.RoundState) (d : Transcript.State)
    (ms : List Verifier.CoupledMessage) (hd : decode s.transcript=some d)
    (hb : s.roundIndex+ms.length<Transcript.u64Limit)
    (hm : ∀ m∈ms,VecFits m.1 ∧ VecFits m.2) :
    ∃ t last,runChecked hash s ms=some t ∧ decode t.transcript=some last ∧
      t.roundIndex=s.roundIndex+ms.length ∧ t.logPoint.length=s.logPoint.length+ms.length ∧
      t.gatePoint.length=s.gatePoint.length+ms.length := by
  obtain ⟨t,last,ht,hl⟩ := bounded_loop_exists hash s d ms hd hb hm
  exact ⟨t,last,by simp [runChecked,hd,ht],hl,loop_success_lengths hash s t ms ht⟩

theorem small_vector_fits (xs : List Verifier.Ext3) (h : xs.length≤160) : VecFits xs := by
  unfold VecFits
  rw [encoded_vector_length]
  unfold Transcript.u64Limit
  omega

theorem shape_supplies_all_claim_sizes (pin : Verifier.Pinned) (c : Verifier.Config) (p : Verifier.Proof)
    (he : Verifier.envelope c=true) (hs : Verifier.shape pin c p=true) : ClaimsFit p.used := by
  have hw : Verifier.width c≤160 := by simp only [Verifier.envelope,decide_eq_true_eq] at he; exact he.2.2.2.1
  have hpre : c.numConstants+c.numRouted≤160 := by unfold Verifier.width at hw; omega
  have hwit : c.numWires≤160 := by unfold Verifier.width at hw; omega
  have hnorm : 2*c.numRouted≤160 := by unfold Verifier.width at hw; omega
  simp only [Verifier.shape,decide_eq_true_eq] at hs
  apply (claims_fit_iff _).mpr
  intro xs hx
  simp only [claimCells,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals apply small_vector_fits; simp_all

theorem shape_supplies_coupled_sizes (pin : Verifier.Pinned) (c : Verifier.Config) (p : Verifier.Proof)
    (he : Verifier.envelope c=true) (hs : Verifier.shape pin c p=true) :
    (p.logRounds.zip p.gateRounds).length=c.degreeBits ∧
    ∀ m∈p.logRounds.zip p.gateRounds,VecFits m.1 ∧ VecFits m.2 := by
  simp only [Verifier.shape,decide_eq_true_eq] at hs
  have hl := hs.2.2.2.2.2.2.2.2.2.2.2.2
  have hq : c.quotientDegree+2≤10 := by simp only [Verifier.envelope,decide_eq_true_eq] at he; exact he.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨by simp only [List.length_zip,hl.1,hl.2.1,Nat.min_self],?_⟩
  intro m hm
  have ha := List.of_mem_zip hm
  have hp := of_decide_eq_true (List.all_eq_true.mp hl.2.2.1 m.1 ha.1)
  have hg := of_decide_eq_true (List.all_eq_true.mp hl.2.2.2 m.2 ha.2)
  exact ⟨small_vector_fits _ (by omega),small_vector_fits _ (by omega)⟩

structure Execution where
  initial : Verifier.Initial
  rounds : Verifier.RoundState
  indices : SampleResult
  context : Verifier.WhirContext

/-- Complete checked outer-transcript prefix only. No terminal, WHIR verifier
or cryptographic acceptance predicate is silently added to this result. -/
def execute (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof) : Option Execution := do
  let _ ← checkedBaseState hash c (Verifier.statement p)
  let initial ← checkedDerive hash c (Verifier.statement p)
  let rounds ← runChecked hash (Verifier.start (toInitial initial)) (p.logRounds.zip p.gateRounds)
  let indices ← sampleChecked hash rounds.transcript p.used c.indexBits
  pure ⟨toInitial initial,rounds,indices,
    Verifier.whirContext Connections.packedFold c p rounds indices.points⟩

theorem source_sized_execution_exists (hash : Hash) (pin : Verifier.Pinned) (c : Verifier.Config) (p : Verifier.Proof)
    (he : Verifier.envelope c=true) (hs : Verifier.shape pin c p=true)
    (hi : InputSizes c (Verifier.statement p)) :
    ∃ result,execute hash c p=some result ∧
      result.initial=toInitial (derive hash c (Verifier.statement p)) ∧
      result.rounds.logPoint.length=c.degreeBits ∧ result.rounds.gatePoint.length=c.degreeBits ∧
      result.indices.points.log.length=c.indexBits ∧ result.indices.points.gate.length=c.indexBits := by
  have hen := he
  simp only [Verifier.envelope,decide_eq_true_eq] at hen
  have hd : c.degreeBits≤13 := hen.2.1
  have hb : c.indexBits≤8 := hen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hen
  have hbase := (source_sized_initial_derivation hash c (Verifier.statement p) he hi).1
  have hini := checked_derive_exact hash c (Verifier.statement p) hd
  have hcounter : (derive hash c (Verifier.statement p)).state.counter<Transcript.u64Limit := by
    rw [derived_final_counter]
    unfold Transcript.u64Limit
    omega
  have hdecode : decode (Verifier.start (toInitial (derive hash c (Verifier.statement p)))).transcript=
      some (derive hash c (Verifier.statement p)).state := decode_snapshot _ hcounter
  have hshape := shape_supplies_coupled_sizes pin c p he hs
  obtain ⟨rounds,last,hr,hl,_hidx,hlog,hgate⟩ := bounded_checked_run_exists hash _ _ _ hdecode
    (by change 0+_ < Transcript.u64Limit; rw [hshape.1]; unfold Transcript.u64Limit; omega) hshape.2
  have hsample := sample_checked_exact hash rounds.transcript last p.used c.indexBits hl
    (shape_supplies_all_claim_sizes pin c p he hs) (by unfold Transcript.u64Limit; omega)
  let sampled := sampleResult hash last p.used c.indexBits
  refine ⟨⟨toInitial (derive hash c (Verifier.statement p)),rounds,sampled,
      Verifier.whirContext Connections.packedFold c p rounds sampled.points⟩,?_,rfl,?_,?_,?_,?_⟩
  · simp only [execute,hbase,hini,hr,hsample,bind,Option.bind,pure,sampled]
  · simpa only [Verifier.start,List.length_nil,Nat.zero_add,hshape.1] using hlog
  · simpa only [Verifier.start,List.length_nil,Nat.zero_add,hshape.1] using hgate
  · exact (sample_result_shape hash last p.used c.indexBits).1
  · exact (sample_result_shape hash last p.used c.indexBits).2.1

theorem execute_success_uses_same_inputs (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (result : Execution) (h : execute hash c p=some result) :
    ∃ base initial,checkedBaseState hash c (Verifier.statement p)=some base ∧
      checkedDerive hash c (Verifier.statement p)=some initial ∧
      result.initial=toInitial initial ∧
      runChecked hash (Verifier.start (toInitial initial)) (p.logRounds.zip p.gateRounds)=some result.rounds ∧
      sampleChecked hash result.rounds.transcript p.used c.indexBits=some result.indices ∧
      result.context=Verifier.whirContext Connections.packedFold c p result.rounds result.indices.points := by
  cases hb : checkedBaseState hash c (Verifier.statement p) with
  | none => simp [execute,hb] at h
  | some base =>
    cases hi : checkedDerive hash c (Verifier.statement p) with
    | none => simp [execute,hb,hi] at h
    | some initial =>
      cases hr : runChecked hash (Verifier.start (toInitial initial)) (p.logRounds.zip p.gateRounds) with
      | none => simp [execute,hb,hi,hr] at h
      | some rounds =>
        cases hs : sampleChecked hash rounds.transcript p.used c.indexBits with
        | none => simp [execute,hb,hi,hr,hs] at h
        | some indices =>
          simp only [execute,hb,hi,hr,hs,bind,Option.bind,pure,Option.some.injEq] at h
          subst result
          exact ⟨base,initial,rfl,rfl,rfl,hr,hs,rfl⟩

theorem execute_same_roots_and_mask (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (result : Execution) (h : execute hash c p=some result) :
    result.context.roots=[p.preprocessedRoot,p.witnessRoot,p.normInverseRoot] ∧
      result.context.expectedClaims.map Option.isSome=[true,true,true,true,true,false] ∧
      result.context.expectedClaims=Verifier.expectedClaims Connections.packedFold c p result.indices.points := by
  obtain ⟨_,_,_,_,_,_,_,hc⟩ := execute_success_uses_same_inputs hash c p result h
  rw [hc]
  exact ⟨rfl,Verifier.context_bound_mask_exact _ _ _ _,rfl⟩

theorem execute_native_points_from_same_rounds_and_indices (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (result : Execution) (h : execute hash c p=some result) :
    result.context.points=
      [(result.indices.points.log.map Subtype.val).reverse++(result.rounds.logPoint.map Subtype.val).reverse,
       (result.indices.points.gate.map Subtype.val).reverse++(result.rounds.gatePoint.map Subtype.val).reverse] := by
  obtain ⟨_,_,_,_,_,_,_,hc⟩ := execute_success_uses_same_inputs hash c p result h
  rw [hc]
  exact Verifier.context_native_coordinate_order _ _ _ _ _

def SamplesAgree (hash : Hash) (sample : Verifier.Bytes → Verifier.UsedClaims → Nat → Verifier.IndexPoints) : Prop :=
  ∀ raw u bits r,sampleChecked hash raw u bits=some r → sample raw u bits=r.points

/-- All compatibility assumptions remain visible. This theorem neither
constructs nor certifies an arbitrary total Engine or its remaining hooks. -/
theorem execute_matches_existing_derived_context (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (result : Execution)
    (hi : e.initialTranscript c p=toInitial (derive hash c (Verifier.statement p)))
    (hc : CommitAgrees hash e.commitRound) (hs : SamplesAgree hash e.sampleIndices)
    (hf : e.foldClaim=Connections.packedFold) (hd : c.degreeBits≤13)
    (h : execute hash c p=some result) :
    result.initial=e.initialTranscript c p ∧ result.rounds=Verifier.derivedRounds e c p ∧
      result.indices.points=Verifier.derivedIndices e c p ∧ result.context=Verifier.derivedContext e c p := by
  obtain ⟨_,initial,_,hini,hei,hr,hsample,hcontext⟩ := execute_success_uses_same_inputs hash c p result h
  have hh : initial=derive hash c (Verifier.statement p) :=
    Option.some.inj (hini.symm.trans (checked_derive_exact hash c (Verifier.statement p) hd))
  subst initial
  have hrounds : result.rounds=Verifier.derivedRounds e c p := by
    unfold Verifier.derivedRounds
    rw [hi]
    exact checked_success_matches_existing hash e.commitRound hc _ _ _ hr
  have hindices : result.indices.points=Verifier.derivedIndices e c p := by
    unfold Verifier.derivedIndices
    rw [←hrounds]
    exact (hs _ _ _ _ hsample).symm
  refine ⟨hei.trans hi.symm,hrounds,hindices,?_⟩
  rw [hcontext,Verifier.derivedContext,hf,hrounds,hindices]

/-- Ordinary prefix inputs with one coupled round and one index coordinate.
This is NOT a valid gate/WHIR deployment or an accepting complete proof. -/
def fixtureConfig : Verifier.Config :=
  { Verifier.testConfig with
    numWires := 2
    indexBits := 1
    whirProtocolId := List.replicate 64 0
    whirSessionId := List.replicate 32 0 }
def fixtureNonbase : Verifier.Ext3 := Connections.fromTranscript
  ⟨⟨0,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩⟩
def fixtureProof : Verifier.Proof :=
  { Verifier.testProof with
    constituentWidth := 2
    logRounds := [[fixtureNonbase,Verifier.zero,Verifier.zero,Verifier.zero,Verifier.zero]]
    used := ⟨[Verifier.zero],[fixtureNonbase,Verifier.zero],[],[Verifier.zero],[Verifier.zero,fixtureNonbase]⟩ }

theorem ordinary_prefix_for_every_hash (hash : Hash) :
    ∃ result,execute hash fixtureConfig fixtureProof=some result ∧
      result.initial=toInitial (derive hash fixtureConfig (Verifier.statement fixtureProof)) ∧
      result.rounds.logPoint.length=1 ∧ result.rounds.gatePoint.length=1 ∧
      result.indices.points.log.length=1 ∧ result.indices.points.gate.length=1 := by
  exact source_sized_execution_exists hash ⟨1,Verifier.testRoot,Verifier.testRoot⟩ fixtureConfig fixtureProof
    (by decide) (by decide) ⟨by decide,by decide,by decide,by decide⟩

theorem malformed_snapshot_rejected_with_no_rounds (hash : Hash) :
    runChecked hash ⟨[],0,Verifier.zero,Verifier.zero,[],[]⟩ []=none := rfl

def scalarLimbs (x : Verifier.Ext3) : List Transcript.Field :=
  let t := Connections.toTranscript x
  [t.c0,t.c1,t.c2]
def flattenValues (xs : List Verifier.Ext3) : List Transcript.Field := xs.bind scalarLimbs

theorem flatten_values_length (xs : List Verifier.Ext3) : (flattenValues xs).length=3*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (scalarLimbs x++flattenValues xs).length=3*(xs.length+1)
    rw [List.length_append,ih]
    change 3+3*xs.length=3*(xs.length+1)
    omega

theorem flatten_values_append (xs ys : List Verifier.Ext3) :
    flattenValues (xs++ys)=flattenValues xs++flattenValues ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change scalarLimbs x++flattenValues (xs++ys)=(scalarLimbs x++flattenValues xs)++flattenValues ys
    rw [ih,List.append_assoc]

theorem squeeze_many_split (hash : Hash) (a b : Nat) (s : Transcript.State) :
    Transcript.squeezeMany hash (a+b) s = (do
      let (xs,t) ← Transcript.squeezeMany hash a s
      let (ys,u) ← Transcript.squeezeMany hash b t
      pure (xs++ys,u)) := by
  induction a generalizing s with
  | zero =>
    cases hh : Transcript.squeezeMany hash b s with
    | none => simp [Transcript.squeezeMany,hh]
    | some pair => rcases pair with ⟨xs,t⟩; simp [Transcript.squeezeMany,hh]
  | succ a ih =>
    rw [Nat.succ_add]
    cases hh : Transcript.squeeze hash s with
    | none => simp [Transcript.squeezeMany,hh]
    | some pair =>
      rcases pair with ⟨x,t⟩
      rw [Transcript.squeezeMany,hh]
      simp only [bind,Option.bind]
      rw [ih]
      cases ha : Transcript.squeezeMany hash a t with
      | none => simp [Transcript.squeezeMany,hh,ha]
      | some pair =>
        rcases pair with ⟨xs,u⟩
        cases hb : Transcript.squeezeMany hash b u with
        | none => simp [Transcript.squeezeMany,hh,ha,hb]
        | some pair => rcases pair with ⟨ys,v⟩; simp [Transcript.squeezeMany,hh,ha,hb]

theorem three_scalars_are_same_ext3 (hash : Hash) (s : Transcript.State)
    (hb : s.counter+3<Transcript.u64Limit) :
    Transcript.squeezeMany hash 3 s=some (scalarLimbs (draw hash s).1,(draw hash s).2) := by
  have h1 : s.counter+1<Transcript.u64Limit := by omega
  have h2 : s.counter+1+1<Transcript.u64Limit := by omega
  have h3 : s.counter+1+1+1<Transcript.u64Limit := by omega
  simp [Transcript.squeezeMany,Transcript.squeeze,h1,h2,h3,draw,scalarLimbs,
    Connections.transcript_verifier_roundtrip,Nat.add_assoc]

theorem ext3_vector_matches_scalar_squeezes (hash : Hash) (n : Nat) (s : Transcript.State)
    (hb : s.counter+3*n<Transcript.u64Limit) :
    Transcript.squeezeMany hash (3*n) s=
      some (flattenValues (drawMany hash n s).1,(drawMany hash n s).2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,squeeze_many_split]
    have hh := three_scalars_are_same_ext3 hash s (by omega)
    have ht := ih (draw hash s).2 (by rw [draw_counter]; omega)
    simp only [hh,ht,bind,Option.bind,pure,drawMany,flattenValues,List.bind_cons]

/-- Exact compatibility with the pre-existing Transcript.constituentIndices:
not just point lengths, but all scalar outputs and the final state coincide. -/
theorem index_sampling_matches_existing_flat_model (hash : Hash) (s : Transcript.State)
    (u : Verifier.UsedClaims) (bits : Nat) (hb : 6*bits<Transcript.u64Limit) :
    Transcript.constituentIndices hash s (u.logPreprocessed.map Connections.toTranscript)
      (u.logWitness.map Connections.toTranscript) (u.logNormInverse.map Connections.toTranscript)
      (u.gatePreprocessed.map Connections.toTranscript) (u.gateWitness.map Connections.toTranscript) bits =
      some (flattenValues ((sampleResult hash s u bits).points.log++(sampleResult hash s u bits).points.gate),
        ⟨(claimsCommitted hash s u).digest,6*bits⟩) := by
  have hl := ext3_vector_matches_scalar_squeezes hash bits (claimsCommitted hash s u)
    (by rw [claims_commit_counter_zero]; omega)
  have hg := ext3_vector_matches_scalar_squeezes hash bits (drawMany hash bits (claimsCommitted hash s u)).2
    (by rw [(draw_many_shape hash bits (claimsCommitted hash s u)).2.2,claims_commit_counter_zero]; omega)
  have hs := sample_result_shape hash s u bits
  have he : (drawMany hash bits (drawMany hash bits (claimsCommitted hash s u)).2).2=
      (⟨(claimsCommitted hash s u).digest,6*bits⟩ : Transcript.State) := by
    apply snapshot_is_injective_bounded
    · rw [(draw_many_shape hash bits (drawMany hash bits (claimsCommitted hash s u)).2).2.2,
        (draw_many_shape hash bits (claimsCommitted hash s u)).2.2,claims_commit_counter_zero]
      omega
    · exact hb
    · exact hs.2.2
  change Transcript.squeezeMany hash (6*bits) (claimsCommitted hash s u)=_
  rw [show 6*bits=3*bits+3*bits by omega,squeeze_many_split,hl]
  simp only [bind,Option.bind]
  rw [hg]
  simp only [pure,Option.bind,flatten_values_append,sampleResult,he]
  rw [show 3*bits+3*bits=6*bits by omega]

end Audit.Wire3.OuterAdapter
