import Audit.Wire3.Connections
import Audit.Wire3.Norm

/-!
# Concrete outer initial transcript, wire v3

Manual scalar/list model of MleVerifierV2._deriveInitialTranscript and
prover_v2.absorb_v2_statement_and_base_roots / verifier_v2. Seven relation
challenges are NOT all sampled after all roots: eta, beta, gamma precede the
norm-inverse root; xi, lambda, rho, kappa follow it. Raw PIs, not their Poseidon
hash, enter this transcript. Config digest and WHIR identifiers are the supplied
fixed configuration fields; their derivation/validation is a separate boundary.

Hash is deterministic only, never assumed injective, uniform or collision-free.
This is not a config/ABI decoder, public-input hash computation, source/compiler
refinement, adaptive fixedness argument or PCS soundness proof. State snapshots
below are internal model adapters, not additional proof-wire transcript fields.
-/
namespace Audit.Wire3.OuterInitial
open Audit.Wire3
abbrev State := Transcript.State
abbrev Hash := Transcript.Hash
abbrev Bytes := Transcript.Bytes
abbrev Ext3 := Verifier.Ext3

def byte (b : UInt8) : Transcript.Byte := b.val
def bytes (bs : Verifier.Bytes) : Bytes := bs.map byte
def bytesBack (bs : Bytes) : Verifier.Bytes := bs.map (fun b => UInt8.ofNat b.val)

theorem bytes_length (bs : Verifier.Bytes) : (bytes bs).length = bs.length := List.length_map _ _
theorem bytes_back_length (bs : Bytes) : (bytesBack bs).length = bs.length := List.length_map _ _

def rootBytes (r : Verifier.Root) : Bytes := (Transcript.le 32 r.val).reverse

theorem root_bytes_length (r : Verifier.Root) : (rootBytes r).length = 32 := by
  simp [rootBytes,Transcript.le_length]

theorem root_bytes_roundtrip (r : Verifier.Root) :
    Transcript.fromLe (rootBytes r).reverse = r.val := by
  rw [rootBytes,List.reverse_reverse]
  exact Transcript.fromLe_le_roundtrip 32 r.val (by
    have := r.isLt
    simpa only [] using this)

theorem root_bytes_injective (r s : Verifier.Root) (he : rootBytes r = rootBytes s) : r = s := by
  apply Fin.ext
  have h := congrArg (fun bs => Transcript.fromLe bs.reverse) he
  simpa only [root_bytes_roundtrip] using h

def metadataWords (c : Verifier.Config) : List Nat :=
  [3,3,2,6,c.numConstants,c.numRouted,c.numWires,c.degreeBits,Verifier.width c,c.indexBits,1,3,0,1,5]
def metadata (c : Verifier.Config) : Bytes := (metadataWords c).bind (Transcript.le 8)

theorem metadata_has_fifteen_words (c : Verifier.Config) : (metadataWords c).length = 15 := rfl
theorem metadata_has_exact_120_bytes (c : Verifier.Config) : (metadata c).length = 120 := by
  simp [metadata,metadataWords,Transcript.le_length]

structure Message where
  tag : Transcript.Byte
  payload : Bytes

def domainMessage (s : String) : Message := ⟨1,Transcript.ascii s⟩
def byteMessage (bs : Bytes) : Message := ⟨2,bs⟩
def fieldVecMessage (xs : List Verifier.Base) : Message := ⟨4,Transcript.fieldVecBytes xs⟩

/-- Exactly sixteen actual frames, including mandatory initialization.
No gate/WHIR encoding, public-input hash, or norm-inverse root is added here. -/
def baseMessages (c : Verifier.Config) (s : Verifier.Statement) : List Message :=
  [domainMessage "plonky2-mle-outer-v3",
   domainMessage "circuit-statement-v3",
   fieldVecMessage s.circuitDigest,
   fieldVecMessage s.publicInputs,
   domainMessage "mle-whir-packed-schema-v3",
   byteMessage (metadata c),
   domainMessage "circuit-config-digest-v3",
   byteMessage (rootBytes c.circuitConfigDigest),
   domainMessage "whir-protocol-id-v3",
   byteMessage (bytes c.whirProtocolId),
   domainMessage "whir-session-id-v3",
   byteMessage (bytes c.whirSessionId),
   domainMessage "pcs-group-preprocessed-v3",
   byteMessage (rootBytes s.preprocessedRoot),
   domainMessage "pcs-group-witness-v3",
   byteMessage (rootBytes s.witnessRoot)]

def zeroDigest : Transcript.Digest := ⟨List.replicate 32 0,by simp⟩
def startState : State := ⟨zeroDigest,0⟩
def absorbMessage (hash : Hash) (s : State) (m : Message) : State := Transcript.absorb hash s m.tag m.payload
def absorbMessages (hash : Hash) (s : State) (ms : List Message) : State := ms.foldl (absorbMessage hash) s
def baseState (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : State :=
  absorbMessages hash startState (baseMessages c s)

theorem base_message_count (c : Verifier.Config) (s : Verifier.Statement) :
    (baseMessages c s).length = 16 := rfl
theorem circuit_digest_is_actual_field_vector (c : Verifier.Config) (s : Verifier.Statement) :
    (baseMessages c s).get? 2 = some ⟨4,Transcript.fieldVecBytes s.circuitDigest⟩ := rfl
theorem raw_public_inputs_are_absorbed (c : Verifier.Config) (s : Verifier.Statement) :
    (baseMessages c s).get? 3 = some ⟨4,Transcript.fieldVecBytes s.publicInputs⟩ := rfl
theorem config_digest_frame_uses_fixed_config (c : Verifier.Config) (s : Verifier.Statement) :
    (baseMessages c s).get? 7 = some ⟨2,rootBytes c.circuitConfigDigest⟩ := rfl
theorem whir_identifiers_are_actual_config_bytes (c : Verifier.Config) (s : Verifier.Statement) :
    (baseMessages c s).get? 9 = some ⟨2,bytes c.whirProtocolId⟩ ∧
    (baseMessages c s).get? 11 = some ⟨2,bytes c.whirSessionId⟩ := ⟨rfl,rfl⟩
theorem two_base_roots_in_order (c : Verifier.Config) (s : Verifier.Statement) :
    (baseMessages c s).get? 13 = some ⟨2,rootBytes s.preprocessedRoot⟩ ∧
    (baseMessages c s).get? 15 = some ⟨2,rootBytes s.witnessRoot⟩ := ⟨rfl,rfl⟩

theorem base_frames_ignore_future_norm_root (c : Verifier.Config) (s : Verifier.Statement) (root : Verifier.Root) :
    baseMessages c {s with normInverseRoot := root} = baseMessages c s := rfl

theorem base_state_counter_zero (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (baseState hash c s).counter = 0 := rfl

/-- Total scalar projection, with a checked-squeeze correspondence proved
below. Its bounded callers satisfy all three source u64 counter checks. -/
def draw (hash : Hash) (s : State) : Ext3 × State :=
  (Connections.fromTranscript ⟨Transcript.challengeAt hash s.digest s.counter,
    Transcript.challengeAt hash s.digest (s.counter+1),
    Transcript.challengeAt hash s.digest (s.counter+2)⟩,⟨s.digest,s.counter+3⟩)

def squeezeExt3 (hash : Hash) (s : State) : Option (Ext3 × State) := do
  let (a,s) ← Transcript.squeeze hash s
  let (b,s) ← Transcript.squeeze hash s
  let (c,s) ← Transcript.squeeze hash s
  pure (Connections.fromTranscript ⟨a,b,c⟩,s)

theorem draw_counter (hash : Hash) (s : State) : (draw hash s).2.counter = s.counter+3 := rfl
theorem draw_digest (hash : Hash) (s : State) : (draw hash s).2.digest = s.digest := rfl

theorem draw_matches_three_checked_squeezes (hash : Hash) (s : State)
    (h : s.counter+3 < Transcript.u64Limit) : squeezeExt3 hash s = some (draw hash s) := by
  have h1 : s.counter+1 < Transcript.u64Limit := by omega
  have h2 : s.counter+1+1 < Transcript.u64Limit := by omega
  have h3 : s.counter+1+1+1 < Transcript.u64Limit := by omega
  simp [squeezeExt3,Transcript.squeeze,h1,h2,h3,draw,Nat.add_assoc]

def drawMany (hash : Hash) : Nat → State → List Ext3 × State
  | 0,s => ([],s)
  | n+1,s =>
      let (x,t) := draw hash s
      let (xs,u) := drawMany hash n t
      (x::xs,u)

def squeezeExt3Many (hash : Hash) : Nat → State → Option (List Ext3 × State)
  | 0,s => some ([],s)
  | n+1,s => do
      let (x,t) ← squeezeExt3 hash s
      let (xs,u) ← squeezeExt3Many hash n t
      pure (x::xs,u)

theorem draw_many_shape (hash : Hash) (n : Nat) (s : State) :
    (drawMany hash n s).1.length = n ∧ (drawMany hash n s).2.digest = s.digest ∧
    (drawMany hash n s).2.counter = s.counter+3*n := by
  induction n generalizing s with
  | zero => simp [drawMany]
  | succ n ih =>
      have h := ih (draw hash s).2
      simp only [drawMany,List.length_cons]
      exact ⟨congrArg Nat.succ h.1,h.2.1,by rw [h.2.2,draw_counter]; omega⟩

theorem draw_many_matches_checked_squeezes (hash : Hash) (n : Nat) (s : State)
    (h : s.counter+3*n < Transcript.u64Limit) :
    squeezeExt3Many hash n s = some (drawMany hash n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have hd := draw_matches_three_checked_squeezes hash s (by omega)
      have hm := ih (draw hash s).2 (by rw [draw_counter]; omega)
      simp only [squeezeExt3Many,drawMany,hd,hm,bind,Option.bind,pure]

def etaState (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : State :=
  Transcript.domain hash (baseState hash c s) "public-input-aggregation-challenge-v3"
def denominatorState (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : State :=
  Transcript.domain hash (draw hash (etaState hash c s)).2 "norm-denominator-challenges-v3"

structure Prefix where
  eta : Ext3
  beta : Ext3
  gamma : Ext3
  afterGamma : State

def preRoot (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : Prefix :=
  let (eta,_) := draw hash (etaState hash c s)
  let (beta,t) := draw hash (denominatorState hash c s)
  let (gamma,u) := draw hash t
  ⟨eta,beta,gamma,u⟩

def checkedPreRoot (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : Option Prefix := do
  let (eta,t) ← squeezeExt3 hash (etaState hash c s)
  let (beta,u) ← squeezeExt3 hash (Transcript.domain hash t "norm-denominator-challenges-v3")
  let (gamma,v) ← squeezeExt3 hash u
  pure ⟨eta,beta,gamma,v⟩

theorem pre_root_challenges_ignore_norm_root (hash : Hash) (c : Verifier.Config)
    (s : Verifier.Statement) (root : Verifier.Root) :
    preRoot hash c {s with normInverseRoot := root} = preRoot hash c s := rfl

theorem pre_root_counter (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (preRoot hash c s).afterGamma.counter = 6 := rfl

theorem checked_pre_root_exact (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    checkedPreRoot hash c s = some (preRoot hash c s) := by
  have he := draw_matches_three_checked_squeezes hash (etaState hash c s) (by change 3 < Transcript.u64Limit; decide)
  have hb := draw_matches_three_checked_squeezes hash (denominatorState hash c s) (by change 3 < Transcript.u64Limit; decide)
  have hg := draw_matches_three_checked_squeezes hash (draw hash (denominatorState hash c s)).2 (by change 6 < Transcript.u64Limit; decide)
  simp only [checkedPreRoot,he,bind,Option.bind,denominatorState] at *
  simp only [hb,hg,pure,preRoot]
  rfl

/-- The root frame is hashed from the digest AFTER beta and gamma calls.
Absorb then resets the counter; no dependency on a future proof field appears. -/
def normRootState (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : State :=
  Transcript.absorb hash
    (Transcript.domain hash (preRoot hash c s).afterGamma "pcs-group-norm-inverse-v3")
    2 (rootBytes s.normInverseRoot)
def mixState (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : State :=
  Transcript.domain hash (normRootState hash c s) "public-input-mix-challenge-v3"
def relationState (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : State :=
  Transcript.domain hash (draw hash (mixState hash c s)).2 "outer-relation-challenges-v3"

theorem norm_root_has_actual_post_gamma_frame (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (normRootState hash c s).digest = hash (Transcript.frame
      (Transcript.domain hash (preRoot hash c s).afterGamma "pcs-group-norm-inverse-v3").digest
      2 (rootBytes s.normInverseRoot)) := rfl

structure Relations where
  lambda : Ext3
  rho : Ext3
  kappa : Ext3
  afterKappa : State

def relations (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : Relations :=
  let (lambda,t) := draw hash (relationState hash c s)
  let (rho,u) := draw hash t
  let (kappa,v) := draw hash u
  ⟨lambda,rho,kappa,v⟩

theorem relation_counter (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (relations hash c s).afterKappa.counter = 9 := rfl

structure Result where
  log : Norm.Challenges
  gateAlpha : Ext3
  gateTau : List Ext3
  state : State

def derive (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : Result :=
  let pfx := preRoot hash c s
  let xi := (draw hash (mixState hash c s)).1
  let rel := relations hash c s
  let (tau,t) := drawMany hash c.degreeBits rel.afterKappa
  let (alpha,u) := draw hash t
  let (gateTau,v) := drawMany hash c.degreeBits u
  ⟨⟨pfx.beta,pfx.gamma,rel.lambda,rel.rho,rel.kappa,pfx.eta,xi,tau⟩,alpha,gateTau,v⟩

/-- Literal checked source call order. Byte absorptions retain source's
prevalidated interface; finite payload/ABI bounds remain caller obligations. -/
def checkedDerive (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : Option Result := do
  let pfx ← checkedPreRoot hash c s
  let afterRoot := Transcript.absorb hash
    (Transcript.domain hash pfx.afterGamma "pcs-group-norm-inverse-v3") 2 (rootBytes s.normInverseRoot)
  let (xi,t) ← squeezeExt3 hash (Transcript.domain hash afterRoot "public-input-mix-challenge-v3")
  let (lambda,u) ← squeezeExt3 hash (Transcript.domain hash t "outer-relation-challenges-v3")
  let (rho,v) ← squeezeExt3 hash u
  let (kappa,w) ← squeezeExt3 hash v
  let (tau,a) ← squeezeExt3Many hash c.degreeBits w
  let (alpha,b) ← squeezeExt3 hash a
  let (gateTau,last) ← squeezeExt3Many hash c.degreeBits b
  pure ⟨⟨pfx.beta,pfx.gamma,lambda,rho,kappa,pfx.eta,xi,tau⟩,alpha,gateTau,last⟩

theorem derived_tau_lengths (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (derive hash c s).log.tau.length = c.degreeBits ∧
    (derive hash c s).gateTau.length = c.degreeBits := by
  exact ⟨(draw_many_shape hash c.degreeBits _).1,(draw_many_shape hash c.degreeBits _).1⟩

theorem derived_final_counter (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (derive hash c s).state.counter = 12+6*c.degreeBits := by
  change (drawMany hash c.degreeBits (draw hash
    (drawMany hash c.degreeBits (relations hash c s).afterKappa).2).2).2.counter = _
  rw [(draw_many_shape hash c.degreeBits _).2.2,draw_counter,
    (draw_many_shape hash c.degreeBits _).2.2,relation_counter]
  omega

theorem derived_final_digest (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (derive hash c s).state.digest = (relationState hash c s).digest := by
  change (drawMany hash c.degreeBits (draw hash
    (drawMany hash c.degreeBits (relations hash c s).afterKappa).2).2).2.digest = _
  rw [(draw_many_shape hash c.degreeBits _).2.1,draw_digest,
    (draw_many_shape hash c.degreeBits _).2.1]
  rfl

theorem checked_derive_exact (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement)
    (hd : c.degreeBits ≤ 13) : checkedDerive hash c s = some (derive hash c s) := by
  have hx := draw_matches_three_checked_squeezes hash (mixState hash c s) (by change 3 < Transcript.u64Limit; decide)
  have hl := draw_matches_three_checked_squeezes hash (relationState hash c s) (by change 3 < Transcript.u64Limit; decide)
  have hr := draw_matches_three_checked_squeezes hash (draw hash (relationState hash c s)).2 (by change 6 < Transcript.u64Limit; decide)
  have hk := draw_matches_three_checked_squeezes hash
    (draw hash (draw hash (relationState hash c s)).2).2 (by change 9 < Transcript.u64Limit; decide)
  have ht := draw_many_matches_checked_squeezes hash c.degreeBits (relations hash c s).afterKappa (by
    rw [relation_counter]; change 9+3*c.degreeBits < 18446744073709551616; omega)
  have ha := draw_matches_three_checked_squeezes hash
    (drawMany hash c.degreeBits (relations hash c s).afterKappa).2 (by
      rw [(draw_many_shape hash c.degreeBits _).2.2,relation_counter]
      change 9+3*c.degreeBits+3 < 18446744073709551616; omega)
  have hg := draw_many_matches_checked_squeezes hash c.degreeBits
    (draw hash (drawMany hash c.degreeBits (relations hash c s).afterKappa).2).2 (by
      rw [draw_counter,(draw_many_shape hash c.degreeBits _).2.2,relation_counter]
      change 9+3*c.degreeBits+3+3*c.degreeBits < 18446744073709551616; omega)
  simp only [checkedDerive,checked_pre_root_exact,bind,Option.bind]
  change (do
    let (xi,t) ← squeezeExt3 hash (mixState hash c s)
    let (lambda,u) ← squeezeExt3 hash (Transcript.domain hash t "outer-relation-challenges-v3")
    let (rho,v) ← squeezeExt3 hash u
    let (kappa,w) ← squeezeExt3 hash v
    let (tau,a) ← squeezeExt3Many hash c.degreeBits w
    let (alpha,b) ← squeezeExt3 hash a
    let (gateTau,last) ← squeezeExt3Many hash c.degreeBits b
    pure (⟨⟨(preRoot hash c s).beta,(preRoot hash c s).gamma,lambda,rho,kappa,
      (preRoot hash c s).eta,xi,tau⟩,alpha,gateTau,last⟩ : Result)) = _
  rw [hx]
  simp only [bind,Option.bind]
  change (do
    let (lambda,u) ← squeezeExt3 hash (relationState hash c s)
    let (rho,v) ← squeezeExt3 hash u
    let (kappa,w) ← squeezeExt3 hash v
    let (tau,a) ← squeezeExt3Many hash c.degreeBits w
    let (alpha,b) ← squeezeExt3 hash a
    let (gateTau,last) ← squeezeExt3Many hash c.degreeBits b
    pure (⟨⟨(preRoot hash c s).beta,(preRoot hash c s).gamma,lambda,rho,kappa,
      (preRoot hash c s).eta,(draw hash (mixState hash c s)).1,tau⟩,alpha,gateTau,last⟩ : Result)) = _
  rw [hl]
  simp only [bind,Option.bind]
  rw [hr]
  simp only [bind,Option.bind]
  rw [hk]
  simp only [bind,Option.bind]
  change (do
    let (tau,a) ← squeezeExt3Many hash c.degreeBits (relations hash c s).afterKappa
    let (alpha,b) ← squeezeExt3 hash a
    let (gateTau,last) ← squeezeExt3Many hash c.degreeBits b
    pure (⟨⟨(preRoot hash c s).beta,(preRoot hash c s).gamma,(relations hash c s).lambda,
      (relations hash c s).rho,(relations hash c s).kappa,(preRoot hash c s).eta,
      (draw hash (mixState hash c s)).1,tau⟩,alpha,gateTau,last⟩ : Result)) = _
  rw [ht]
  simp only [bind,Option.bind]
  rw [ha]
  simp only [bind,Option.bind]
  rw [hg]
  rfl

theorem bytes_roundtrip (bs : Verifier.Bytes) : bytesBack (bytes bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [bytes,bytesBack,List.map_cons] at *
      rw [ih]
      congr 1
      cases b with
      | mk b =>
          apply congrArg UInt8.mk
          apply Fin.ext
          exact Nat.mod_eq_of_lt b.isLt

theorem bytes_back_roundtrip (bs : Bytes) : bytes (bytesBack bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [bytes,bytesBack,List.map_cons] at *
      rw [ih]
      congr 1
      apply Fin.ext
      exact Nat.mod_eq_of_lt b.isLt

/-- INTERNAL lossless adapter for Verifier.Initial's opaque Bytes field:
digest bytes followed by a u64-LE counter. It is not a new wire-format field. -/
def snapshot (s : State) : Verifier.Bytes := bytesBack (s.digest.bytes ++ Transcript.le 8 s.counter)

theorem snapshot_length (s : State) : (snapshot s).length = 40 := by
  simp only [snapshot,bytes_back_length,List.length_append,s.digest.length_eq,Transcript.le_length]

theorem snapshot_retains_digest (s : State) : (bytes (snapshot s)).take 32 = s.digest.bytes := by
  rw [snapshot,bytes_back_roundtrip]
  simpa only [s.digest.length_eq] using List.take_left s.digest.bytes (Transcript.le 8 s.counter)

theorem snapshot_retains_counter (s : State) (hc : s.counter < Transcript.u64Limit) :
    Transcript.fromLe ((bytes (snapshot s)).drop 32) = s.counter := by
  rw [snapshot,bytes_back_roundtrip]
  rw [show (s.digest.bytes ++ Transcript.le 8 s.counter).drop 32 = Transcript.le 8 s.counter from
    by simpa only [s.digest.length_eq] using List.drop_left s.digest.bytes (Transcript.le 8 s.counter)]
  exact Transcript.fromLe_le_roundtrip 8 s.counter hc

theorem snapshot_is_injective_bounded (s t : State)
    (hs : s.counter < Transcript.u64Limit) (ht : t.counter < Transcript.u64Limit)
    (h : snapshot s = snapshot t) : s = t := by
  have hd := congrArg (fun bs => (bytes bs).take 32) h
  dsimp only at hd
  rw [snapshot_retains_digest,snapshot_retains_digest] at hd
  have hc := congrArg (fun bs => Transcript.fromLe ((bytes bs).drop 32)) h
  dsimp only at hc
  rw [snapshot_retains_counter s hs,snapshot_retains_counter t ht] at hc
  cases s with
  | mk sd sc =>
    cases t with
    | mk td tc =>
      cases sd
      cases td
      simp only [Transcript.State.mk.injEq,Transcript.Digest.mk.injEq]
      exact ⟨hd,hc⟩

def toInitial (r : Result) : Verifier.Initial :=
  ⟨snapshot r.state,Norm.challengeList r.log,r.log.tau,r.gateAlpha,r.gateTau⟩

theorem initial_has_exact_seven_challenge_layout (r : Result) :
    (toInitial r).logChallenges = [r.log.eta,r.log.beta,r.log.gamma,r.log.xi,
      r.log.lambda,r.log.rho,r.log.kappa] := rfl

theorem initial_norm_adapter_is_lossless (r : Result) :
    Norm.challengesFromInitial (toInitial r) = r.log := by
  exact Norm.challenges_roundtrip r.log (snapshot r.state) r.gateAlpha r.gateTau

theorem derived_initial_shape (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (toInitial (derive hash c s)).logChallenges.length = 7 ∧
    (toInitial (derive hash c s)).logTau.length = c.degreeBits ∧
    (toInitial (derive hash c s)).gateTau.length = c.degreeBits ∧
    (toInitial (derive hash c s)).transcript.length = 40 :=
  ⟨rfl,(derived_tau_lengths hash c s).1,(derived_tau_lengths hash c s).2,snapshot_length _⟩

def withInitial (hash : Hash) (e : Verifier.Engine) : Verifier.Engine :=
  {e with initialObservation := fun c s => toInitial (derive hash c s)}

theorem engine_initial_is_same_statement (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) :
    (withInitial hash e).initialTranscript c p = toInitial (derive hash c (Verifier.statement p)) := rfl

/-- No caller/proof hash echo replaces the PI hash: this adapter does not
implement or alter that separate remaining Engine observation at all. -/
theorem engine_keeps_public_input_hash_observation (hash : Hash) (e : Verifier.Engine)
    (pis : List Verifier.Base) : (withInitial hash e).publicInputsHash pis = e.publicInputsHash pis := rfl

theorem bounded_engine_initial_has_checked_derivation (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (hd : c.degreeBits ≤ 13) :
    ∃ r, checkedDerive hash c (Verifier.statement p) = some r ∧
      (withInitial hash e).initialTranscript c p = toInitial r ∧
      r.state.counter < Transcript.u64Limit := by
  exact ⟨derive hash c (Verifier.statement p),checked_derive_exact hash c (Verifier.statement p) hd,rfl,
    by rw [derived_final_counter]; change 12+6*c.degreeBits < 18446744073709551616; omega⟩

/-- This replaces only initialObservation, NOT the downstream decoder for
the internal state snapshot or commitRound/sampleIndices. Their connection
must be supplied separately before interpreting a whole verifier run. -/
theorem same_statement_cannot_read_later_proof_bytes (hash : Hash) (e : Verifier.Engine)
    (c : Verifier.Config) (p q : Verifier.Proof) (h : Verifier.statement p = Verifier.statement q) :
    (withInitial hash e).initialTranscript c p = (withInitial hash e).initialTranscript c q := by
  simp only [engine_initial_is_same_statement,h]

/-- Physical identifier guard actually present in bindWhirIdentifiers.
The constructor's bytes32[2]/bytes32 fields satisfy it; generic Config.Bytes
are not silently assumed to do so. This does not validate identifier meaning. -/
def bindWhirIdentifiersChecked (hash : Hash) (s : State) (c : Verifier.Config) : Option State :=
  if c.whirProtocolId.length = 64 ∧ c.whirSessionId.length = 32 then
    some (absorbMessages hash s
      [domainMessage "whir-protocol-id-v3",byteMessage (bytes c.whirProtocolId),
       domainMessage "whir-session-id-v3",byteMessage (bytes c.whirSessionId)])
  else none

def checkedBaseState (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : Option State := do
  let beforeIdentifiers := absorbMessages hash startState ((baseMessages c s).take 8)
  let afterIdentifiers ← bindWhirIdentifiersChecked hash beforeIdentifiers c
  pure (absorbMessages hash afterIdentifiers ((baseMessages c s).drop 12))

theorem checked_base_state_exact (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement)
    (hp : c.whirProtocolId.length = 64) (hs : c.whirSessionId.length = 32) :
    checkedBaseState hash c s = some (baseState hash c s) := by
  simp only [checkedBaseState,bindWhirIdentifiersChecked,hp,hs,and_self,↓reduceIte,
    bind,Option.bind,pure,baseState,baseMessages,absorbMessages,List.take,List.drop,
    List.foldl_cons,List.foldl_nil]

theorem malformed_identifiers_rejected (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement)
    (h : c.whirProtocolId.length ≠ 64 ∨ c.whirSessionId.length ≠ 32) :
    checkedBaseState hash c s = none := by
  have hn : ¬(c.whirProtocolId.length = 64 ∧ c.whirSessionId.length = 32) := by omega
  simp [checkedBaseState,bindWhirIdentifiersChecked,hn]

theorem metadata_values_fit_actual_u64_fields (c : Verifier.Config) (he : Verifier.envelope c = true) :
    ∀ n ∈ metadataWords c, n < Transcript.u64Limit := by
  have hcw : c.numConstants ≤ Verifier.width c :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _)
  have hww : c.numWires ≤ Verifier.width c :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  simp only [Verifier.envelope,decide_eq_true_eq] at he
  intro n hn
  simp only [metadataWords,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst n; unfold Transcript.u64Limit; omega

/-- Existing statement/prevalidated interface sizes, not a new hash-security
assumption. Raw canonical PI elements are encoded directly. -/
def InputSizes (c : Verifier.Config) (s : Verifier.Statement) : Prop :=
  s.circuitDigest.length = 4 ∧ s.publicInputs.length ≤ 256 ∧
  c.whirProtocolId.length = 64 ∧ c.whirSessionId.length = 32

theorem every_base_frame_payload_fits_source (c : Verifier.Config) (s : Verifier.Statement)
    (h : InputSizes c s) : ∀ m ∈ baseMessages c s, m.payload.length < Transcript.u64Limit := by
  rcases h with ⟨hd,hp,hw,hs⟩
  intro m hm
  simp only [baseMessages,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
  all_goals subst m
  all_goals simp only [domainMessage,byteMessage,fieldVecMessage,root_bytes_length,
    bytes_length,metadata_has_exact_120_bytes,Transcript.field_vector_length,hd,hw,hs]
  all_goals first | (change _ < 18446744073709551616; omega) | decide

/-- Combined successful SOURCE-SIZED typed slice. Exact header frames include
the actual identifier guard; checkedDerive proves every source squeeze fits.
It still does not establish config/VK digest provenance or a metadata decoder. -/
theorem source_sized_initial_derivation (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement)
    (he : Verifier.envelope c = true) (hi : InputSizes c s) :
    checkedBaseState hash c s = some (baseState hash c s) ∧
    checkedDerive hash c s = some (derive hash c s) ∧
    (∀ n ∈ metadataWords c, n < Transcript.u64Limit) ∧
    (∀ m ∈ baseMessages c s, m.payload.length < Transcript.u64Limit) := by
  have hd : c.degreeBits ≤ 13 := by
    simp only [Verifier.envelope,decide_eq_true_eq] at he
    exact he.2.1
  exact ⟨checked_base_state_exact hash c s hi.2.2.1 hi.2.2.2,
    checked_derive_exact hash c s hd,metadata_values_fit_actual_u64_fields c he,
    every_base_frame_payload_fits_source c s hi⟩

def ext3At (hash : Hash) (digest : Transcript.Digest) (counter : Nat) : Ext3 :=
  Connections.fromTranscript ⟨Transcript.challengeAt hash digest counter,
    Transcript.challengeAt hash digest (counter+1),Transcript.challengeAt hash digest (counter+2)⟩

/-- Each vector position contains the SAME three consecutive reduced
32-byte digests as the source, not an independently supplied Ext3 value. -/
theorem draw_many_at (hash : Hash) (count : Nat) (s : State) (i : Nat) (hi : i < count) :
    (drawMany hash count s).1.get? i = some (ext3At hash s.digest (s.counter+3*i)) := by
  induction count generalizing s i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp only [drawMany,List.get?_cons_zero,Nat.mul_zero,Nat.add_zero]; rfl
      | succ i =>
          simp only [drawMany,List.get?_cons_succ]
          rw [ih (draw hash s).2 i (by omega)]
          simp only [draw_counter,draw_digest]
          congr 2
          omega

theorem seven_values_have_exact_counter_inputs (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (toInitial (derive hash c s)).logChallenges =
      [ext3At hash (etaState hash c s).digest 0,
       ext3At hash (denominatorState hash c s).digest 0,
       ext3At hash (denominatorState hash c s).digest 3,
       ext3At hash (mixState hash c s).digest 0,
       ext3At hash (relationState hash c s).digest 0,
       ext3At hash (relationState hash c s).digest 3,
       ext3At hash (relationState hash c s).digest 6] := rfl

theorem log_tau_uses_following_counter_blocks (hash : Hash) (c : Verifier.Config)
    (s : Verifier.Statement) (i : Nat) (hi : i < c.degreeBits) :
    (derive hash c s).log.tau.get? i =
      some (ext3At hash (relationState hash c s).digest (9+3*i)) := by
  exact draw_many_at hash c.degreeBits (relations hash c s).afterKappa i hi

theorem gate_alpha_follows_log_tau (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (derive hash c s).gateAlpha =
      ext3At hash (relationState hash c s).digest (9+3*c.degreeBits) := by
  change ext3At hash (drawMany hash c.degreeBits (relations hash c s).afterKappa).2.digest
    (drawMany hash c.degreeBits (relations hash c s).afterKappa).2.counter = _
  rw [(draw_many_shape hash c.degreeBits _).2.1,(draw_many_shape hash c.degreeBits _).2.2]
  rfl

theorem gate_tau_follows_gate_alpha (hash : Hash) (c : Verifier.Config)
    (s : Verifier.Statement) (i : Nat) (hi : i < c.degreeBits) :
    (derive hash c s).gateTau.get? i =
      some (ext3At hash (relationState hash c s).digest (12+3*c.degreeBits+3*i)) := by
  change (drawMany hash c.degreeBits (draw hash
    (drawMany hash c.degreeBits (relations hash c s).afterKappa).2).2).1.get? i = _
  rw [draw_many_at hash c.degreeBits _ i hi,draw_counter,draw_digest,
    (draw_many_shape hash c.degreeBits _).2.1,(draw_many_shape hash c.degreeBits _).2.2,relation_counter]
  congr 2
  omega

end Audit.Wire3.OuterInitial
