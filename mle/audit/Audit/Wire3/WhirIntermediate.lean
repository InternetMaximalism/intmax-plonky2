import Audit.Wire3.WhirPrefix
import Audit.Wire3.WhirSampling
import Audit.Wire3.WhirRows

/-!
# Concrete intermediate WHIR round composition, V2 three-by-one route

Manual mathematical execution of SpongefishWhirVerify._doIntermediateRound,
_openAndVerifyCommitment/_openSplitCommitments, and their constraint updates.
The order is new root, ALL OOD challenges, ALL answers, PoW, sampling, raw
Merkle openings, constraint RLC, OOD/query accumulation, constraint storage,
sumcheck, then previous-root replacement. Every byte operation uses the SAME
Spongefish state and sources. There is no Authenticate, decoder, challenge,
running-sum, or evaluator observation; only deterministic Hash is parameterized.

fromPrefix/runAfterPrefix derive the state from the actual initial execution.
Round zero opens its three initial base-field roots, one vector each; subsequent
rounds open the single Ext3 previous root. OpenParams is the validated caller's
PREVIOUS-round parameter projection, not arbitrary proof metadata. ProfileShape
is an explicit correspondence precondition, NOT a new runtime validation pass.
Other commitment/vector profiles and full schedule/ABI validation are excluded.

WhirSampling uses concrete bytewise challenges but reference insertion sort,
NOT a refinement of source in-place quicksort. Raw rows are authenticated before
RLC and canonical decoding, as in intermediate rounds (not final split reads).
Canonical decode then pure dot denotes the source's interleaved decode/accumulate
loop's mathematical result; its instruction/error/memory refinement is unproved.
Domain powers use Nat.pow modulo p, not a proof of the source _glPow loop.
Pure domain-point calculation is a projection with no transcript/hint effect;
its allocation timing (before standard Merkle, after split Merkle) is not modeled.
List get? failures expose missing source shape conditions rather than making
unchecked zero reads. Nat arithmetic does not model gas/overflow/assembly.
Hash security, query probability, and full WHIR/PCS soundness are NOT proved.
-/
namespace Audit.Wire3.WhirIntermediate
open Spongefish (Hash Bytes Digest Ext3)

structure OpenParams where
  codewordLength : Nat
  merkleDepth : Nat
  domainGenerator : Verifier.Base
  numCosets : Nat
  cosetSize : Nat
  inDomainSamples : Nat
  columns : Nat
  foldingRounds : Nat

structure RoundParams where
  outDomainSamples : Nat
  numVariables : Nat
  powThreshold : Nat
  sumcheckRounds : Nat
  sumcheckPowThreshold : Nat

structure State where
  sumcheck : WhirFinal.State
  hintPos : Nat
  initialRoots : List Digest
  vectorRlc : List Ext3
  previousRoot : Digest
  constraints : List WhirFinal.RoundConstraint
  completedRounds : Nat

def fromPrefix (r : WhirPrefix.Result) : State :=
  ⟨r.sumcheck, r.hintPos, r.initial.commitments.map (·.root), r.initial.vectorRlc,
    r.initial.prevRoot, [WhirPrefix.initialConstraint r], 0⟩

def spongeState (s : State) : Spongefish.State :=
  ⟨s.sumcheck.cursor.spongeState, s.sumcheck.cursor.transcriptPos, s.hintPos⟩

def rootsToOpen (s : State) : List Digest :=
  if s.completedRounds = 0 then s.initialRoots else [s.previousRoot]

def layout (s : State) (o : OpenParams) : WhirRows.Layout :=
  ⟨if s.completedRounds = 0 then .base else .ext3, o.columns⟩

def ProfileShape (s : State) (o : OpenParams) : Prop :=
  s.initialRoots.length = 3 ∧ s.vectorRlc.length = 3 ∧
  o.foldingRounds ≤ s.sumcheck.finalRandomness.length ∧ o.foldingRounds < 256 ∧
  o.columns = 2 ^ o.foldingRounds ∧ 0 < o.cosetSize ∧
  o.codewordLength = o.cosetSize * o.numCosets ∧
  o.codewordLength = 2 ^ o.merkleDepth ∧ o.merkleDepth < 256

structure Message where
  newRoot : Digest
  oodPoints : List Ext3
  oodAnswers : List Ext3

def receive (hash : Hash) (source : Bytes) (p : RoundParams) (s : Spongefish.State) :
    Option (Message × Spongefish.State) := do
  let (root, afterRoot) ← Spongefish.proverHash hash s source
  let (points, afterPoints) ← Spongefish.verifierExt3Many hash p.outDomainSamples afterRoot
  let (answers, afterAnswers) ← Spongefish.proverExt3Many hash source p.outDomainSamples afterPoints
  let afterPow ← Spongefish.verifyPow hash afterAnswers source p.powThreshold
  pure (⟨root,points,answers⟩,afterPow)

structure Opening where
  indices : List Nat
  groups : List (List WhirRows.RawRow)

def openPrevious (hash : Hash) (hints : Bytes) (o : OpenParams) (s : State)
    (start : Spongefish.State) : Option (Opening × Spongefish.State) := do
  let (indices, afterSampling) ← WhirSampling.challengeIndicesReference hash start
    o.codewordLength o.inDomainSamples
  let (groups, afterMerkle) ← WhirRows.openGroups hash o.merkleDepth indices (layout s o)
    hints (rootsToOpen s) afterSampling
  pure (⟨indices,groups⟩,afterMerkle)

def weights (s : State) (o : OpenParams) : Option (List Arithmetic.Ext3) :=
  if o.foldingRounds ≤ s.sumcheck.finalRandomness.length then
    some (WhirTerminal.eqWeights (s.sumcheck.finalRandomness.drop
      (s.sumcheck.finalRandomness.length - o.foldingRounds)))
  else none

def domainPoint (o : OpenParams) (index : Nat) : Arithmetic.Ext3 :=
  Arithmetic.fromBase (o.domainGenerator.val ^
    (index / o.cosetSize + (index % o.cosetSize) * o.numCosets))

def rowDot (l : WhirRows.Layout) (w : List Arithmetic.Ext3) (row : WhirRows.RawRow) :
    Option Arithmetic.Ext3 := do
  let values ← WhirRows.decodeRow l row
  pure (WhirTerminal.dot w (values.map Subtype.val))

def splitDot (l : WhirRows.Layout) (w : List Arithmetic.Ext3) (rlc : List Ext3)
    (query : Nat) : Nat → List (List WhirRows.RawRow) → Arithmetic.Ext3 → Option Arithmetic.Ext3
  | _, [], acc => some acc
  | c, group :: groups, acc => do
      let row ← group.get? query
      let value ← rowDot l w row
      let coefficient ← rlc.get? c
      let perCommit := Arithmetic.eadd Arithmetic.zero (Arithmetic.emul coefficient.val value)
      splitDot l w rlc query (c+1) groups (Arithmetic.eadd acc perCommit)

def queryValue (s : State) (o : OpenParams) (w : List Arithmetic.Ext3)
    (opening : Opening) (query : Nat) : Option Arithmetic.Ext3 :=
  if s.completedRounds = 0 then
    splitDot (layout s o) w s.vectorRlc query 0 opening.groups Arithmetic.zero
  else do
    let group ← opening.groups.get? 0
    let row ← group.get? query
    rowDot (layout s o) w row

def addOod (answers coefficients : List Ext3) (sum : Arithmetic.Ext3) : Arithmetic.Ext3 :=
  (answers.zip coefficients).foldl (fun acc pair =>
    Arithmetic.eadd acc (Arithmetic.emul pair.1.val pair.2.val)) sum

def addQueries (s : State) (o : OpenParams) (w : List Arithmetic.Ext3) (opening : Opening)
    (rlc : List Ext3) (offset : Nat) : Nat → Nat → Arithmetic.Ext3 → Option Arithmetic.Ext3
  | _, 0, sum => some sum
  | i, count+1, sum => do
      let value ← queryValue s o w opening i
      let coefficient ← rlc.get? (offset+i)
      addQueries s o w opening rlc offset (i+1) count
        (Arithmetic.eadd sum (Arithmetic.emul value coefficient.val))

structure Claims where
  sum : Arithmetic.Ext3
  coefficients : List Ext3

def accumulate (hash : Hash) (o : OpenParams) (s : State) (message : Message)
    (opening : Opening) (start : Spongefish.State) : Option (Claims × Spongefish.State) := do
  let w ← weights s o
  let (rlc, afterRlc) ← Spongefish.geometricChallenge hash start
    (message.oodAnswers.length + opening.indices.length)
  let sum ← addQueries s o w opening rlc message.oodAnswers.length 0 opening.indices.length
    (addOod message.oodAnswers rlc s.sumcheck.sum)
  pure (⟨sum,rlc⟩,afterRlc)

def newConstraint (o : OpenParams) (p : RoundParams) (message : Message)
    (opening : Opening) (claims : Claims) : WhirFinal.RoundConstraint :=
  ⟨p.numVariables, claims.coefficients.map Subtype.val,
    message.oodPoints.map Subtype.val ++ opening.indices.map (domainPoint o)⟩

def sumcheckStart (s : State) (claims : Claims) (afterRlc : Spongefish.State) : WhirFinal.State :=
  ⟨WhirFinalSpongefish.fromSpongefish afterRlc, claims.sum, s.sumcheck.finalRandomness⟩

def beforeSumcheck (o : OpenParams) (p : RoundParams) (s : State) (message : Message)
    (opening : Opening) (claims : Claims) (afterRlc : Spongefish.State) : State :=
  { s with
    sumcheck := sumcheckStart s claims afterRlc
    hintPos := afterRlc.hintPos
    constraints := s.constraints ++ [newConstraint o p message opening claims] }

def finish (hash : Hash) (source : Bytes) (o : OpenParams) (p : RoundParams) (s : State)
    (message : Message) (opening : Opening) (claims : Claims) (afterRlc : Spongefish.State) : Option State := do
  let prepared := beforeSumcheck o p s message opening claims afterRlc
  let result ← WhirFinal.runRounds (WhirFinalSpongefish.engine hash) p.sumcheckPowThreshold
    (WhirFinalSpongefish.fromTranscriptBytes source) p.sumcheckRounds prepared.sumcheck
  pure { prepared with
    sumcheck := result
    previousRoot := message.newRoot
    completedRounds := s.completedRounds + 1 }

def runRound (hash : Hash) (source hints : Bytes) (o : OpenParams) (p : RoundParams)
    (s : State) : Option State := do
  let (message, afterPow) ← receive hash source p (spongeState s)
  let (opening, afterMerkle) ← openPrevious hash hints o s afterPow
  let (claims, afterRlc) ← accumulate hash o s message opening afterMerkle
  finish hash source o p s message opening claims afterRlc

def runRounds (hash : Hash) (source hints : Bytes) : List (OpenParams × RoundParams) → State → Option State
  | [], s => some s
  | (o,p) :: rest, s => do
      let next ← runRound hash source hints o p s
      runRounds hash source hints rest next

/-- Executable entry from the already concrete initial phase, not a freely
chosen running sum, challenge list, previous root, or hint cursor. -/
def runAfterPrefix (hash : Hash) (source hints : Bytes) (initial : WhirInitial.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (count threshold : Nat)
    (start : Spongefish.State) (rounds : List (OpenParams × RoundParams)) : Option State := do
  let initialResult ← WhirPrefix.run hash source initial roots expected mask count threshold start
  runRounds hash source hints rounds (fromPrefix initialResult)

theorem receive_success_order (hash : Hash) (source : Bytes) (p : RoundParams)
    (s t : Spongefish.State) (message : Message) (h : receive hash source p s = some (message,t)) :
    ∃ afterRoot afterPoints afterAnswers,
      Spongefish.proverHash hash s source = some (message.newRoot,afterRoot) ∧
      Spongefish.verifierExt3Many hash p.outDomainSamples afterRoot = some (message.oodPoints,afterPoints) ∧
      Spongefish.proverExt3Many hash source p.outDomainSamples afterPoints = some (message.oodAnswers,afterAnswers) ∧
      Spongefish.verifyPow hash afterAnswers source p.powThreshold = some t := by
  unfold receive at h
  cases hr : Spongefish.proverHash hash s source with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨root,ar⟩
    cases hp : Spongefish.verifierExt3Many hash p.outDomainSamples ar with
    | none => simp [hr,hp] at h
    | some pair =>
      rcases pair with ⟨points,ap⟩
      cases ha : Spongefish.proverExt3Many hash source p.outDomainSamples ap with
      | none => simp [hr,hp,ha] at h
      | some pair =>
        rcases pair with ⟨answers,aa⟩
        cases hw : Spongefish.verifyPow hash aa source p.powThreshold with
        | none => simp [hr,hp,ha,hw] at h
        | some last =>
          simp only [hr,hp,ha,hw,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          exact ⟨ar,ap,aa,rfl,hp,ha,hw⟩

theorem opening_success_uses_previous_roots (hash : Hash) (hints : Bytes) (o : OpenParams)
    (s : State) (start last : Spongefish.State) (opening : Opening)
    (h : openPrevious hash hints o s start = some (opening,last)) :
    ∃ afterSampling,
      WhirSampling.challengeIndicesReference hash start o.codewordLength o.inDomainSamples =
        some (opening.indices,afterSampling) ∧
      WhirRows.openGroups hash o.merkleDepth opening.indices (layout s o) hints (rootsToOpen s)
        afterSampling = some (opening.groups,last) := by
  unfold openPrevious at h
  cases hs : WhirSampling.challengeIndicesReference hash start o.codewordLength o.inDomainSamples with
  | none => simp [hs] at h
  | some pair =>
    rcases pair with ⟨indices,afterSampling⟩
    cases hg : WhirRows.openGroups hash o.merkleDepth indices (layout s o) hints (rootsToOpen s) afterSampling with
    | none => simp [hs,hg] at h
    | some pair =>
      rcases pair with ⟨groups,afterMerkle⟩
      simp only [hs,hg,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨afterSampling,rfl,hg⟩

theorem accumulation_success_uses_actual_prior_sum (hash : Hash) (o : OpenParams) (s : State)
    (message : Message) (opening : Opening) (start last : Spongefish.State) (claims : Claims)
    (h : accumulate hash o s message opening start = some (claims,last)) :
    ∃ w, weights s o = some w ∧
      Spongefish.geometricChallenge hash start (message.oodAnswers.length + opening.indices.length) =
        some (claims.coefficients,last) ∧
      addQueries s o w opening claims.coefficients message.oodAnswers.length 0 opening.indices.length
        (addOod message.oodAnswers claims.coefficients s.sumcheck.sum) = some claims.sum := by
  unfold accumulate at h
  cases hw : weights s o with
  | none => simp [hw] at h
  | some w =>
    cases hr : Spongefish.geometricChallenge hash start (message.oodAnswers.length + opening.indices.length) with
    | none => simp [hw,hr] at h
    | some pair =>
      rcases pair with ⟨rlc,afterRlc⟩
      cases hs : addQueries s o w opening rlc message.oodAnswers.length 0 opening.indices.length
          (addOod message.oodAnswers rlc s.sumcheck.sum) with
      | none => simp [hw,hr,hs] at h
      | some sum =>
        simp only [hw,hr,hs,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨w,rfl,rfl,hs⟩

theorem finish_success_updates_exact_state (hash : Hash) (source : Bytes) (o : OpenParams)
    (p : RoundParams) (s t : State) (message : Message) (opening : Opening) (claims : Claims)
    (afterRlc : Spongefish.State) (h : finish hash source o p s message opening claims afterRlc = some t) :
    WhirFinal.runRounds (WhirFinalSpongefish.engine hash) p.sumcheckPowThreshold
      (WhirFinalSpongefish.fromTranscriptBytes source) p.sumcheckRounds (sumcheckStart s claims afterRlc) =
        some t.sumcheck ∧ t.hintPos = afterRlc.hintPos ∧ t.previousRoot = message.newRoot ∧
    t.constraints = s.constraints ++ [newConstraint o p message opening claims] ∧
    t.initialRoots = s.initialRoots ∧ t.vectorRlc = s.vectorRlc ∧ t.completedRounds = s.completedRounds+1 := by
  unfold finish beforeSumcheck at h
  cases hr : WhirFinal.runRounds (WhirFinalSpongefish.engine hash) p.sumcheckPowThreshold
      (WhirFinalSpongefish.fromTranscriptBytes source) p.sumcheckRounds (sumcheckStart s claims afterRlc) with
  | none => simp [hr] at h
  | some result =>
    simp only [hr,bind,Option.bind,pure,Option.some.injEq] at h
    subst t
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem round_success_is_one_execution (hash : Hash) (source hints : Bytes) (o : OpenParams)
    (p : RoundParams) (s t : State) (h : runRound hash source hints o p s = some t) :
    ∃ message afterPow opening afterMerkle claims afterRlc,
      receive hash source p (spongeState s) = some (message,afterPow) ∧
      openPrevious hash hints o s afterPow = some (opening,afterMerkle) ∧
      accumulate hash o s message opening afterMerkle = some (claims,afterRlc) ∧
      finish hash source o p s message opening claims afterRlc = some t := by
  unfold runRound at h
  cases hm : receive hash source p (spongeState s) with
  | none => simp [hm] at h
  | some pair =>
    rcases pair with ⟨message,afterPow⟩
    cases ho : openPrevious hash hints o s afterPow with
    | none => simp [hm,ho] at h
    | some pair =>
      rcases pair with ⟨opening,afterMerkle⟩
      cases hc : accumulate hash o s message opening afterMerkle with
      | none => simp [hm,ho,hc] at h
      | some pair =>
        rcases pair with ⟨claims,afterRlc⟩
        simp only [hm,ho,hc,bind,Option.bind] at h
        exact ⟨message,afterPow,opening,afterMerkle,claims,afterRlc,rfl,ho,hc,h⟩

theorem first_route_uses_all_three_base_roots (r : WhirPrefix.Result) (o : OpenParams)
    (h : r.initial.commitments.length = 3) :
    rootsToOpen (fromPrefix r) = r.initial.commitments.map (·.root) ∧
    (rootsToOpen (fromPrefix r)).length = 3 ∧ (layout (fromPrefix r) o).encoding = .base := by
  simp [rootsToOpen,fromPrefix,layout,h]

theorem round_success_next_route_is_single_ext3 (hash : Hash) (source hints : Bytes)
    (o nextOpen : OpenParams) (p : RoundParams) (s t : State)
    (h : runRound hash source hints o p s = some t) :
    rootsToOpen t = [t.previousRoot] ∧ (layout t nextOpen).encoding = .ext3 := by
  obtain ⟨m,_,op,_,c,ar,_,_,_,hf⟩ := round_success_is_one_execution hash source hints o p s t h
  have he := (finish_success_updates_exact_state hash source o p s t m op c ar hf).2.2.2.2.2.2
  simp [rootsToOpen,layout,he]

theorem round_success_preserves_initial_roots_and_rlc (hash : Hash) (source hints : Bytes)
    (o : OpenParams) (p : RoundParams) (s t : State)
    (h : runRound hash source hints o p s = some t) :
    t.initialRoots = s.initialRoots ∧ t.vectorRlc = s.vectorRlc := by
  obtain ⟨m,_,op,_,c,ar,_,_,_,hf⟩ := round_success_is_one_execution hash source hints o p s t h
  have he := finish_success_updates_exact_state hash source o p s t m op c ar hf
  exact ⟨he.2.2.2.2.1,he.2.2.2.2.2.1⟩

theorem round_success_adds_exact_rounds_and_constraint (hash : Hash) (source hints : Bytes)
    (o : OpenParams) (p : RoundParams) (s t : State)
    (h : runRound hash source hints o p s = some t) :
    t.sumcheck.finalRandomness.length = s.sumcheck.finalRandomness.length + p.sumcheckRounds ∧
    t.constraints.length = s.constraints.length+1 ∧ t.completedRounds = s.completedRounds+1 := by
  obtain ⟨m,_,op,_,c,ar,_,_,_,hf⟩ := round_success_is_one_execution hash source hints o p s t h
  have he := finish_success_updates_exact_state hash source o p s t m op c ar hf
  have hr := WhirFinal.completed_round_count_exact (WhirFinalSpongefish.engine hash)
    p.sumcheckPowThreshold (WhirFinalSpongefish.fromTranscriptBytes source)
    p.sumcheckRounds (sumcheckStart s c ar) t.sumcheck he.1
  exact ⟨hr,by simp [he.2.2.2.1],he.2.2.2.2.2.2⟩

theorem row_dot_uses_exact_canonical_raw_decode (l : WhirRows.Layout) (w : List Arithmetic.Ext3)
    (row : WhirRows.RawRow) (value : Arithmetic.Ext3) (h : rowDot l w row = some value) :
    ∃ values, WhirRows.decodeRow l row = some values ∧ values.length = l.columns ∧
      value = WhirTerminal.dot w (values.map Subtype.val) ∧
      (∀ v ∈ values, Arithmetic.Canonical v.val) := by
  unfold rowDot at h
  cases hd : WhirRows.decodeRow l row with
  | none => simp [hd] at h
  | some values =>
    simp only [hd,bind,Option.bind,pure,Option.some.injEq] at h
    exact ⟨values,rfl,(WhirRows.decode_fields_exact_shape l.encoding l.columns row.bytes values hd).1,
      h.symm,fun v _ => v.property⟩

theorem sequence_success_threads_actual_next (hash : Hash) (source hints : Bytes)
    (o : OpenParams) (p : RoundParams) (rest : List (OpenParams × RoundParams)) (s t : State)
    (h : runRounds hash source hints ((o,p)::rest) s = some t) :
    ∃ next, runRound hash source hints o p s = some next ∧
      runRounds hash source hints rest next = some t := by
  cases hn : runRound hash source hints o p s with
  | none => simp [runRounds,hn] at h
  | some next => exact ⟨next,rfl,by simpa [runRounds,hn] using h⟩

theorem entry_success_has_computed_prefix (hash : Hash) (source hints : Bytes)
    (initial : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (count threshold : Nat) (start : Spongefish.State) (rounds : List (OpenParams × RoundParams))
    (last : State)
    (h : runAfterPrefix hash source hints initial roots expected mask count threshold start rounds = some last) :
    ∃ initialResult, WhirPrefix.run hash source initial roots expected mask count threshold start = some initialResult ∧
      runRounds hash source hints rounds (fromPrefix initialResult) = some last := by
  unfold runAfterPrefix at h
  cases hp : WhirPrefix.run hash source initial roots expected mask count threshold start with
  | none => simp [hp] at h
  | some initialResult => exact ⟨initialResult,rfl,by simpa [hp] using h⟩

theorem received_ood_dimensions_and_hint_cursor (hash : Hash) (source : Bytes) (p : RoundParams)
    (s t : Spongefish.State) (message : Message) (h : receive hash source p s = some (message,t)) :
    message.oodPoints.length = p.outDomainSamples ∧
    message.oodAnswers.length = p.outDomainSamples ∧ t.hintPos = s.hintPos := by
  obtain ⟨ar,ap,aa,hr,hp,ha,hw⟩ := receive_success_order hash source p s t message h
  have a := WhirInitial.prover_hash_exact_read hash source s ar message.newRoot hr
  have b := Spongefish.verifier_many_exact_count_and_counter hash p.outDomainSamples ar ap message.oodPoints hp
  have c := Spongefish.prover_many_exact_count_and_cursor hash source p.outDomainSamples ap aa message.oodAnswers ha
  have d := WhirFinalSpongefish.pow_execution_preserves_hint_cursor hash p.powThreshold source aa t hw
  exact ⟨b.1,c.1,d.trans (c.2.2.trans (b.2.2.1.trans a.2.2.1))⟩

theorem received_transcript_consumption (hash : Hash) (source : Bytes) (p : RoundParams)
    (s t : Spongefish.State) (message : Message) (h : receive hash source p s = some (message,t)) :
    t.transcriptPos = s.transcriptPos + 32 + 24*p.outDomainSamples +
      WhirFinalSpongefish.powBytes p.powThreshold := by
  obtain ⟨ar,ap,aa,hr,hp,ha,hw⟩ := receive_success_order hash source p s t message h
  have a := WhirInitial.prover_hash_exact_read hash source s ar message.newRoot hr
  have b := Spongefish.verifier_many_exact_count_and_counter hash p.outDomainSamples ar ap message.oodPoints hp
  have c := Spongefish.prover_many_exact_count_and_cursor hash source p.outDomainSamples ap aa message.oodAnswers ha
  by_cases hs : p.powThreshold = Spongefish.maxCounter
  · rw [hs,Spongefish.pow_sentinel_consumes_nothing] at hw
    cases hw
    simp only [WhirFinalSpongefish.powBytes,hs,↓reduceIte]
    omega
  · obtain ⟨data,middle,nonce,hc,hm,_,_,_⟩ :=
      Spongefish.pow_success_checks_actual_digest hash aa t source p.powThreshold hs hw
    have d := Spongefish.verifier_message_preserves_read_cursors hash aa middle data 32 hc
    have e := Spongefish.prover_message_reads_then_absorbs hash middle t source nonce 8 hm
    simp only [WhirFinalSpongefish.powBytes,hs,↓reduceIte]
    omega

theorem opening_preserves_transcript_and_bounds_hints (hash : Hash) (hints : Bytes)
    (o : OpenParams) (s : State) (start last : Spongefish.State) (opening : Opening)
    (hv : WhirSampling.ValidDomain o.codewordLength) (hb : start.hintPos ≤ hints.length)
    (h : openPrevious hash hints o s start = some (opening,last)) :
    last.transcriptPos = start.transcriptPos ∧ last.hintPos ≤ hints.length ∧
    start.hintPos ≤ last.hintPos ∧ opening.groups.length = (rootsToOpen s).length ∧
    WhirSampling.StrictAscending opening.indices ∧ WhirSampling.NoDuplicates opening.indices := by
  obtain ⟨afterSampling,hs,hg⟩ := opening_success_uses_previous_roots hash hints o s start last opening h
  have a := WhirSampling.reference_sampling_output_properties hash start afterSampling
    o.codewordLength o.inDomainSamples opening.indices hv hs
  have b := WhirRows.groups_success_count_and_cursor hash o.merkleDepth opening.indices
    (layout s o) hints (rootsToOpen s) afterSampling last opening.groups (by omega) hg
  exact ⟨b.2.2.2.2.trans a.2.2.2.2.2.1,b.2.2.1,by omega,b.1,a.2.2.1,a.2.2.2.1⟩

/-- Extraction traverses the actual sequential group execution, so the
Merkle offset is not an independently supplied authentication observation. -/
theorem groups_success_extracts_same_position (hash : Hash) (hints : Bytes) (depth : Nat)
    (indices : List Nat) (l : WhirRows.Layout) (roots : List Digest) (groups : List (List WhirRows.RawRow))
    (s t : Spongefish.State) (position : Nat) (root : Digest)
    (h : WhirRows.openGroups hash depth indices l hints roots s = some (groups,t))
    (hr : roots.get? position = some root) :
    ∃ rows before after, groups.get? position = some rows ∧
      WhirRows.openGroup hash root depth indices l hints before = some (rows,after) := by
  induction roots generalizing s groups position with
  | nil => simp at hr
  | cons first rest ih =>
    obtain ⟨rows,tail,next,rfl,hg,ht⟩ :=
      WhirRows.groups_success_next_is_actual_returned_cursor hash depth indices l hints first rest s t groups h
    cases position with
    | zero =>
      cases hr
      exact ⟨rows,s,next,rfl,hg⟩
    | succ position =>
      obtain ⟨selected,before,after,hi,ho⟩ := ih tail next position ht hr
      exact ⟨selected,before,after,hi,ho⟩

theorem opening_each_root_uses_actual_raw_hashes (hash : Hash) (hints : Bytes)
    (o : OpenParams) (s : State) (start last : Spongefish.State) (opening : Opening)
    (position : Nat) (root : Digest)
    (h : openPrevious hash hints o s start = some (opening,last))
    (hr : (rootsToOpen s).get? position = some root) :
    ∃ rows before after, opening.groups.get? position = some rows ∧
      WhirRows.openGroup hash root o.merkleDepth opening.indices (layout s o) hints before = some (rows,after) ∧
      Merkle.verify hash root o.merkleDepth opening.indices (WhirRows.rowHashes hash rows) hints
        (before.hintPos+8+opening.indices.length*WhirRows.rowBytes (layout s o)) = some after.hintPos := by
  obtain ⟨afterSampling,_,hg⟩ := opening_success_uses_previous_roots hash hints o s start last opening h
  obtain ⟨rows,before,after,hi,ho⟩ := groups_success_extracts_same_position hash hints o.merkleDepth
    opening.indices (layout s o) (rootsToOpen s) opening.groups afterSampling last position root hg hr
  exact ⟨rows,before,after,hi,ho,WhirRows.group_success_same_merkle_inputs hash root
    o.merkleDepth opening.indices (layout s o) hints before after rows ho⟩

theorem successful_accumulation_rlc_and_cursors (hash : Hash) (o : OpenParams) (s : State)
    (message : Message) (opening : Opening) (start last : Spongefish.State) (claims : Claims)
    (h : accumulate hash o s message opening start = some (claims,last)) :
    claims.coefficients.length = message.oodAnswers.length+opening.indices.length ∧
    last.transcriptPos = start.transcriptPos ∧ last.hintPos = start.hintPos := by
  obtain ⟨_,_,hr,_⟩ := accumulation_success_uses_actual_prior_sum hash o s message opening start last claims h
  exact WhirInitial.geometric_challenge_shape hash start last _ claims.coefficients hr

theorem weights_use_last_actual_folding_randomness (s : State) (o : OpenParams)
    (w : List Arithmetic.Ext3) (h : weights s o = some w) :
    o.foldingRounds ≤ s.sumcheck.finalRandomness.length ∧
    w = WhirTerminal.eqWeights (s.sumcheck.finalRandomness.drop
      (s.sumcheck.finalRandomness.length-o.foldingRounds)) := by
  unfold weights at h
  split at h
  · rename_i hb
    exact ⟨hb,(Option.some.inj h).symm⟩
  · contradiction

theorem eq_weight_step_doubles_length (w : List Arithmetic.Ext3) (r : Arithmetic.Ext3) :
    (WhirTerminal.eqWeightStep w r).length = w.length*2 := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    simp only [WhirTerminal.eqWeightStep,List.bind_cons,List.length_append,List.length_cons,List.length_nil] at *
    omega

theorem eq_weight_loop_length (randomness w : List Arithmetic.Ext3) :
    (randomness.foldl WhirTerminal.eqWeightStep w).length = w.length * 2^randomness.length := by
  induction randomness generalizing w with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons,ih,eq_weight_step_doubles_length,List.length_cons,Nat.pow_succ]
    ac_rfl

theorem profile_weights_have_exact_row_columns (s : State) (o : OpenParams)
    (w : List Arithmetic.Ext3) (hp : ProfileShape s o) (hw : weights s o = some w) :
    w.length = o.columns := by
  obtain ⟨hb,rfl⟩ := weights_use_last_actual_folding_randomness s o w hw
  have hh : s.sumcheck.finalRandomness.length - (s.sumcheck.finalRandomness.length-o.foldingRounds) =
      o.foldingRounds := by omega
  simp only [WhirTerminal.eqWeights,eq_weight_loop_length,List.length_cons,List.length_nil,
    Nat.zero_add,Nat.one_mul,List.length_drop,hh]
  exact hp.2.2.2.2.1.symm

theorem profile_row_dot_pairs_every_column (s : State) (o : OpenParams)
    (w : List Arithmetic.Ext3) (row : WhirRows.RawRow) (value : Arithmetic.Ext3)
    (hp : ProfileShape s o) (hw : weights s o = some w)
    (h : rowDot (layout s o) w row = some value) :
    ∃ values, WhirRows.decodeRow (layout s o) row = some values ∧
      (w.zip (values.map Subtype.val)).length = o.columns ∧
      value = WhirTerminal.dot w (values.map Subtype.val) := by
  obtain ⟨values,hd,hl,hv,_⟩ := row_dot_uses_exact_canonical_raw_decode (layout s o) w row value h
  exact ⟨values,hd,by simp [List.length_zip,profile_weights_have_exact_row_columns s o w hp hw,hl,layout],hv⟩

theorem concrete_sumcheck_keeps_randomness_prefix (hash : Hash) (source : Bytes) (threshold count : Nat)
    (s t : WhirFinal.State)
    (h : WhirFinal.runRounds (WhirFinalSpongefish.engine hash) threshold
      (WhirFinalSpongefish.fromTranscriptBytes source) count s = some t) :
    ∃ suffix, suffix.length = count ∧ t.finalRandomness = s.finalRandomness ++ suffix := by
  induction count generalizing s with
  | zero =>
    have he : s = t := by simpa [WhirFinal.runRounds] using h
    exact ⟨[],rfl,by simp [he]⟩
  | succ count ih =>
    cases hr : WhirFinal.roundStep (WhirFinalSpongefish.engine hash) threshold
        (WhirFinalSpongefish.fromTranscriptBytes source) s with
    | none => simp [WhirFinal.runRounds,hr] at h
    | some next =>
      obtain ⟨m,_,_,r,cursor,_,_,_,_,_,_,hn⟩ := WhirFinal.round_step_success
        (WhirFinalSpongefish.engine hash) threshold (WhirFinalSpongefish.fromTranscriptBytes source) s next hr
      obtain ⟨suffix,hl,he⟩ := ih next (by simpa [WhirFinal.runRounds,hr] using h)
      exact ⟨r::suffix,by simp [hl],by simpa [hn,WhirFinal.advance,List.append_assoc] using he⟩

theorem round_success_keeps_full_challenge_prefix (hash : Hash) (source hints : Bytes)
    (o : OpenParams) (p : RoundParams) (s t : State)
    (h : runRound hash source hints o p s = some t) :
    ∃ suffix, suffix.length = p.sumcheckRounds ∧
      t.sumcheck.finalRandomness = s.sumcheck.finalRandomness ++ suffix := by
  obtain ⟨m,_,op,_,c,ar,_,_,_,hf⟩ := round_success_is_one_execution hash source hints o p s t h
  have he := finish_success_updates_exact_state hash source o p s t m op c ar hf
  exact concrete_sumcheck_keeps_randomness_prefix hash source p.sumcheckPowThreshold p.sumcheckRounds
    (sumcheckStart s c ar) t.sumcheck he.1

theorem round_success_exact_transcript_consumption (hash : Hash) (source hints : Bytes)
    (o : OpenParams) (p : RoundParams) (s t : State)
    (hv : WhirSampling.ValidDomain o.codewordLength) (hb : s.hintPos ≤ hints.length)
    (h : runRound hash source hints o p s = some t) :
    t.sumcheck.cursor.transcriptPos = s.sumcheck.cursor.transcriptPos +
      32 + 24*p.outDomainSamples + WhirFinalSpongefish.powBytes p.powThreshold +
      p.sumcheckRounds*(48+WhirFinalSpongefish.powBytes p.sumcheckPowThreshold) ∧
    s.hintPos ≤ t.hintPos ∧ t.hintPos ≤ hints.length := by
  obtain ⟨m,ap,op,am,c,ar,hm,ho,hc,hf⟩ := round_success_is_one_execution hash source hints o p s t h
  have a := received_transcript_consumption hash source p (spongeState s) ap m hm
  have b := (received_ood_dimensions_and_hint_cursor hash source p (spongeState s) ap m hm).2.2
  have d := opening_preserves_transcript_and_bounds_hints hash hints o s ap am op hv (by simpa [b,spongeState] using hb) ho
  have e := successful_accumulation_rlc_and_cursors hash o s m op am ar c hc
  have f := finish_success_updates_exact_state hash source o p s t m op c ar hf
  have g := WhirFinalSpongefish.rounds_success_exact_consumption hash p.sumcheckPowThreshold
    (WhirFinalSpongefish.fromTranscriptBytes source) p.sumcheckRounds (sumcheckStart s c ar) t.sumcheck f.1
  simp only [spongeState] at a b
  simp only [sumcheckStart,WhirFinalSpongefish.fromSpongefish] at g
  exact ⟨by omega,by omega,by omega⟩

theorem stored_constraint_same_points_and_rlc (hash : Hash) (source hints : Bytes)
    (o : OpenParams) (p : RoundParams) (s t : State)
    (h : runRound hash source hints o p s = some t) :
    ∃ message opening claims afterMerkle afterRlc,
      accumulate hash o s message opening afterMerkle = some (claims,afterRlc) ∧
      t.constraints = s.constraints ++ [newConstraint o p message opening claims] ∧
      (newConstraint o p message opening claims).coefficients.length =
        (newConstraint o p message opening claims).points.length ∧
      (newConstraint o p message opening claims).numVariables = p.numVariables := by
  obtain ⟨m,ap,op,am,c,ar,hm,_,hc,hf⟩ := round_success_is_one_execution hash source hints o p s t h
  have a := received_ood_dimensions_and_hint_cursor hash source p (spongeState s) ap m hm
  have b := successful_accumulation_rlc_and_cursors hash o s m op am ar c hc
  have d := finish_success_updates_exact_state hash source o p s t m op c ar hf
  refine ⟨m,op,c,am,ar,hc,d.2.2.2.1,?_,rfl⟩
  simp only [newConstraint,List.length_append,List.length_map]
  omega

theorem all_rounds_keep_initial_binding_and_constraint_count (hash : Hash) (source hints : Bytes)
    (rounds : List (OpenParams × RoundParams)) (s t : State)
    (h : runRounds hash source hints rounds s = some t) :
    t.initialRoots = s.initialRoots ∧ t.vectorRlc = s.vectorRlc ∧
    t.completedRounds = s.completedRounds+rounds.length ∧
    t.constraints.length = s.constraints.length+rounds.length := by
  induction rounds generalizing s with
  | nil =>
    cases h
    simp
  | cons pair rest ih =>
    rcases pair with ⟨o,p⟩
    obtain ⟨next,hn,ht⟩ := sequence_success_threads_actual_next hash source hints o p rest s t h
    have a := round_success_preserves_initial_roots_and_rlc hash source hints o p s next hn
    have b := round_success_adds_exact_rounds_and_constraint hash source hints o p s next hn
    have c := ih next ht
    exact ⟨c.1.trans a.1,c.2.1.trans a.2,by simp only [List.length_cons]; omega,
      by simp only [List.length_cons]; omega⟩

theorem round_new_root_is_actual_first_transcript_slice (hash : Hash) (source hints : Bytes)
    (o : OpenParams) (p : RoundParams) (s t : State)
    (h : runRound hash source hints o p s = some t) :
    t.previousRoot.val = (source.drop s.sumcheck.cursor.transcriptPos).take 32 := by
  obtain ⟨m,ap,op,_,c,ar,hm,_,_,hf⟩ := round_success_is_one_execution hash source hints o p s t h
  obtain ⟨afterRoot,_,_,hr,_,_,_⟩ := receive_success_order hash source p (spongeState s) ap m hm
  have he := finish_success_updates_exact_state hash source o p s t m op c ar hf
  rw [he.2.2.1]
  exact (WhirInitial.prover_hash_exact_read hash source (spongeState s) afterRoot m.newRoot hr).2.2.2

theorem successful_queries_check_every_value_and_coefficient (s : State) (o : OpenParams)
    (w : List Arithmetic.Ext3) (opening : Opening) (rlc : List Ext3)
    (offset start count : Nat) (sum output : Arithmetic.Ext3)
    (h : addQueries s o w opening rlc offset start count sum = some output) :
    ∀ relative, relative < count → ∃ value coefficient,
      queryValue s o w opening (start+relative) = some value ∧
      rlc.get? (offset+(start+relative)) = some coefficient := by
  induction count generalizing start sum with
  | zero => intro relative hr; omega
  | succ count ih =>
    cases hv : queryValue s o w opening start with
    | none => simp only [addQueries,hv,bind,Option.bind] at h
    | some value =>
      cases hc : rlc.get? (offset+start) with
      | none => simp only [addQueries,hv,hc,bind,Option.bind] at h
      | some coefficient =>
        have ht : addQueries s o w opening rlc offset (start+1) count
            (Arithmetic.eadd sum (Arithmetic.emul value coefficient.val)) = some output := by
          simpa only [addQueries,hv,hc,bind,Option.bind] using h
        intro relative hr
        cases relative with
        | zero => exact ⟨value,coefficient,by simpa using hv,by simpa using hc⟩
        | succ relative =>
          obtain ⟨v,c,hv',hc'⟩ := ih (start+1) _ ht relative (by omega)
          exact ⟨v,c,by simpa [Nat.add_assoc,Nat.add_comm 1 relative] using hv',
            by simpa [Nat.add_assoc,Nat.add_comm 1 relative] using hc'⟩

theorem successful_split_dot_checks_every_group (l : WhirRows.Layout)
    (w : List Arithmetic.Ext3) (rlc : List Ext3) (query start : Nat)
    (groups : List (List WhirRows.RawRow)) (sum output : Arithmetic.Ext3)
    (h : splitDot l w rlc query start groups sum = some output) :
    ∀ position group, groups.get? position = some group →
      ∃ row value coefficient, group.get? query = some row ∧ rowDot l w row = some value ∧
        rlc.get? (start+position) = some coefficient := by
  induction groups generalizing start sum with
  | nil => intro position group hg; simp at hg
  | cons first rest ih =>
    cases hr : first.get? query with
    | none => simp only [splitDot,hr,bind,Option.bind] at h
    | some row =>
      cases hv : rowDot l w row with
      | none => simp only [splitDot,hr,hv,bind,Option.bind] at h
      | some value =>
        cases hc : rlc.get? start with
        | none => simp only [splitDot,hr,hv,hc,bind,Option.bind] at h
        | some coefficient =>
          have ht : splitDot l w rlc query (start+1) rest
              (Arithmetic.eadd sum (Arithmetic.eadd Arithmetic.zero (Arithmetic.emul coefficient.val value))) =
                some output := by simpa only [splitDot,hr,hv,hc,bind,Option.bind] using h
          intro position group hg
          cases position with
          | zero =>
            cases hg
            exact ⟨row,value,coefficient,hr,hv,by simpa using hc⟩
          | succ position =>
            obtain ⟨r,v,c,hr',hv',hc'⟩ := ih (start+1) _ ht position group hg
            exact ⟨r,v,c,hr',hv',by simpa [Nat.add_assoc,Nat.add_comm 1 position] using hc'⟩

theorem successful_standard_query_uses_actual_first_group (s : State) (o : OpenParams)
    (w : List Arithmetic.Ext3) (opening : Opening) (query : Nat) (value : Arithmetic.Ext3)
    (hn : s.completedRounds ≠ 0) (h : queryValue s o w opening query = some value) :
    ∃ group row, opening.groups.get? 0 = some group ∧ group.get? query = some row ∧
      rowDot (layout s o) w row = some value := by
  simp only [queryValue,hn,↓reduceIte] at h
  cases hg : opening.groups.get? 0 with
  | none => simp only [hg,bind,Option.bind] at h
  | some group =>
    cases hr : group.get? query with
    | none => simp only [hg,hr,bind,Option.bind] at h
    | some row => exact ⟨group,row,rfl,hr,by simpa only [hg,hr,bind,Option.bind] using h⟩

theorem successful_accumulation_checks_all_sampled_queries (hash : Hash) (o : OpenParams)
    (s : State) (message : Message) (opening : Opening) (start last : Spongefish.State) (claims : Claims)
    (h : accumulate hash o s message opening start = some (claims,last)) :
    ∃ w, weights s o = some w ∧
      ∀ query, query < opening.indices.length → ∃ value coefficient,
        queryValue s o w opening query = some value ∧
        claims.coefficients.get? (message.oodAnswers.length+query) = some coefficient := by
  obtain ⟨w,hw,_,hq⟩ := accumulation_success_uses_actual_prior_sum hash o s message opening start last claims h
  refine ⟨w,hw,?_⟩
  intro query hquery
  simpa only [Nat.zero_add] using successful_queries_check_every_value_and_coefficient s o w opening
    claims.coefficients message.oodAnswers.length 0 opening.indices.length
    (addOod message.oodAnswers claims.coefficients s.sumcheck.sum) claims.sum hq query hquery

/-- Ordinary toy execution, not Keccak, production profile, or a proof fixture.
It executes three real initial root reads, three base row groups, then one Ext3
group on the next round, plus three nonempty concrete sumchecks on one source. -/
def exampleInitial : WhirInitial.Params := ⟨3,1,1,3,[[Verifier.zero,Verifier.zero,Verifier.zero]]⟩
def exampleOpen : OpenParams := ⟨1,0,Verifier.base 1,1,1,1,2,1⟩
def exampleRound : RoundParams := ⟨1,2,Spongefish.maxCounter,1,Spongefish.maxCounter⟩
def exampleHints : Bytes :=
  ((List.replicate 3 (Transcript.le 8 2 ++ List.replicate 16 Spongefish.zeroByte)).join) ++
    Transcript.le 8 2 ++ List.replicate 48 Spongefish.zeroByte
def exampleExecution : Option State :=
  runAfterPrefix (fun _ => Spongefish.zeroDigest) (List.replicate 736 Spongefish.zeroByte) exampleHints
    exampleInitial (List.replicate 3 Spongefish.zeroDigest) (List.replicate 3 Verifier.zero)
    [⟨7,by decide⟩] 1 Spongefish.maxCounter ⟨⟨Spongefish.zeroDigest,0⟩,0,0⟩
    [(exampleOpen,exampleRound),(exampleOpen,{exampleRound with numVariables := 1})]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem concrete_three_root_then_single_root_execution :
    exampleExecution.map (fun s => (s.completedRounds,s.constraints.length,
      s.sumcheck.finalRandomness.length,s.sumcheck.cursor.transcriptPos,s.hintPos)) =
        some (2,3,3,736,128) := by rfl

end Audit.Wire3.WhirIntermediate
