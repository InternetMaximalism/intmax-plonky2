import Audit.Wire3.WhirIntermediate

/-!
# Concrete initial-to-terminal WHIR composition, current three-by-one route

The retained PrefixState contains the original WhirPrefix.Result and the output
of the actual WhirIntermediate.runRounds started at fromPrefix of THAT result.
The final forms, original constraint RLC, accumulated constraints, running sum,
previous roots, randomness, transcript sponge and hint cursor are derived from
this execution. Only deterministic Hash is an observation. No Authenticate,
decoder, challenge, earlier sum, or independently supplied Context is accepted.

Source: SpongefishWhirVerify._phaseFinalVectorAndMerkle/_verifyFinalSplit,
_requireFinalOpening, _phaseSumcheck, _phaseFinalClaim, and _verifyWhirProof EOF.
Final vector bytes are read ONCE, before final PoW/sampling. The same vector is
used for each Horner comparison and the later final MLE fold. Finalsplit has
a dedicated loop: slice (without cursor mutation), raw hash, canonical row dot,
same vector-RLC accumulation, cursor advance, then that group's Merkle call.
It deliberately does NOT use WhirRows.openGroup, which authenticates first.
With an intermediate round the standard branch authenticates before row decode.

Params/OpenParams/forms are projections of the fixed validated VK/profile, not
new proof-selected inputs. ProfileShape is a correspondence PRECONDITION, not
a new source runtime guard. Production is exactly three commitments, one vector
each. No general single-commitment/multi-vector initial route is claimed.
The source's mutable final-vector fold is represented by an immutable snapshot;
instruction mutation, allocation, calldata/Yul, overflow, gas, exception payloads,
Rust/compiler refinement and full parameter decoding remain unproved.
The reference sampler here is replaced by proved-equal indexed quicksort and
compaction in WhirSamplingExecution. WhirConfigured derives ProfileShape from
one checked config and actual execution, retaining the explicit 3-by-1 profile.
Domain powers are Nat.pow mod p; WhirDomainPower proves the bitwise scalar loop
equality for bounded exponents. These are not source/compiler refinements.
The concrete whole execution here is a MANUAL MODEL, not a proof of whole-source
equivalence or WHIR/PCS probabilistic soundness, hash security or FS independence.
-/
namespace Audit.Wire3.WhirTail
open Spongefish (Hash Bytes Digest Ext3)

structure PrefixState where
  origin : WhirPrefix.Result
  current : WhirIntermediate.State

def runPrefix (hash : Hash) (source hints : Bytes) (initial : WhirInitial.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (count threshold : Nat)
    (start : Spongefish.State) (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams)) :
    Option PrefixState := do
  let origin ← WhirPrefix.run hash source initial roots expected mask count threshold start
  let current ← WhirIntermediate.runRounds hash source hints rounds (WhirIntermediate.fromPrefix origin)
  pure ⟨origin,current⟩

structure Params where
  openParams : WhirIntermediate.OpenParams
  finalSize : Nat
  finalRounds : Nat
  finalPowThreshold : Nat
  finalSumcheckPowThreshold : Nat

def totalVariables (s : PrefixState) : Nat := s.origin.initial.initialRoundConstraint.numVariables

def ProfileShape (s : PrefixState) (p : Params) : Prop :=
  WhirIntermediate.ProfileShape s.current p.openParams ∧
  p.finalSize = 2^p.finalRounds ∧ p.finalRounds < 256 ∧
  totalVariables s = s.current.sumcheck.finalRandomness.length+p.finalRounds ∧
  0 < totalVariables s ∧ totalVariables s < 256 ∧
  0 < s.origin.initial.forms.length ∧
  (∀ form ∈ s.origin.initial.forms, form.point.length = totalVariables s) ∧
  (∀ entry ∈ s.current.constraints,
    entry.coefficients.length = entry.points.length ∧ entry.numVariables ≤ totalVariables s)

theorem from_le_bounded (bytes : Bytes) : Transcript.fromLe bytes < 256^bytes.length := by
  induction bytes with
  | nil => decide
  | cons b bs ih =>
    have hb := b.isLt
    simp only [Transcript.fromLe,List.length_cons,Nat.pow_succ]
    omega

theorem encode_from_le_same_bytes (bytes : Bytes) :
    Transcript.le bytes.length (Transcript.fromLe bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    have hb := b.isLt
    have hm : (b.val+256*Transcript.fromLe bs)%256 = b.val := by omega
    have hd : (b.val+256*Transcript.fromLe bs)/256 = Transcript.fromLe bs := by omega
    simp only [List.length_cons,Transcript.fromLe,Transcript.le,hm,hd,ih]

/-- Big-endian bytes32-to-word projection used ONLY by the existing Plan type.
Merkle always receives the original Digest. No modulo truncation is used. -/
def rootWord (d : Digest) : WhirTerminal.Root :=
  ⟨Transcript.fromLe d.val.reverse,by
    have hb := from_le_bounded d.val.reverse
    have he : 256^32 = 2^256 := by decide
    simpa only [List.length_reverse,d.property,he] using hb⟩

def rootBytes (root : WhirTerminal.Root) : Bytes := (Transcript.le 32 root.val).reverse

theorem root_projection_is_lossless (d : Digest) : rootBytes (rootWord d) = d.val := by
  unfold rootBytes rootWord
  have h := encode_from_le_same_bytes d.val.reverse
  rw [List.length_reverse,d.property] at h
  rw [h,List.reverse_reverse]

structure SplitRows where
  rows : List WhirRows.RawRow
  hashes : List Digest
  values : List Arithmetic.Ext3

/-- The cursor is updated only AFTER the actual hash, canonical decoding,
and accumulation for this row. Coefficient lookup has no fallback value. -/
def readSplitRow (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (w : List Arithmetic.Ext3) (rlc : List Ext3) (commitment : Nat)
    (previous : Arithmetic.Ext3) (s : Spongefish.State) :
    Option ((WhirRows.RawRow × Digest × Arithmetic.Ext3) × Spongefish.State) := do
  let (bytes,nextOffset) ← Spongefish.readSlice hints s.hintPos (WhirRows.rowBytes l)
  let row : WhirRows.RawRow := ⟨s.hintPos,bytes⟩
  let leaf := hash row.bytes
  let dot ← WhirIntermediate.rowDot l w row
  let coefficient ← rlc.get? commitment
  let rowValue := Arithmetic.eadd Arithmetic.zero (Arithmetic.emul coefficient.val dot)
  let value := Arithmetic.eadd previous rowValue
  pure ((row,leaf,value),{s with hintPos := nextOffset})

def readSplitRows (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (w : List Arithmetic.Ext3) (rlc : List Ext3) (commitment : Nat) :
    List Arithmetic.Ext3 → Spongefish.State → Option (SplitRows × Spongefish.State)
  | [],s => some (⟨[],[],[]⟩,s)
  | value :: values,s => do
      let ((row,leaf,updated),next) ← readSplitRow hash hints l w rlc commitment value s
      let (rest,last) ← readSplitRows hash hints l w rlc commitment values next
      pure (⟨row::rest.rows,leaf::rest.hashes,updated::rest.values⟩,last)

def openSplitGroup (hash : Hash) (hints : Bytes) (l : WhirRows.Layout) (depth : Nat)
    (indices : List Nat) (root : Digest) (w : List Arithmetic.Ext3) (rlc : List Ext3)
    (commitment : Nat) (values : List Arithmetic.Ext3) (s : Spongefish.State) :
    Option (SplitRows × Spongefish.State) := do
  let afterPrefix ← Spongefish.consumeVecPrefix s hints (indices.length*l.columns)
  let (rows,afterRows) ← readSplitRows hash hints l w rlc commitment values afterPrefix
  let nextOffset ← Merkle.verify hash root depth indices rows.hashes hints afterRows.hintPos
  pure (rows,{afterRows with hintPos := nextOffset})

structure Opened where
  groups : List (List WhirRows.RawRow)
  values : List Arithmetic.Ext3

def openSplitGroups (hash : Hash) (hints : Bytes) (l : WhirRows.Layout) (depth : Nat)
    (indices : List Nat) (w : List Arithmetic.Ext3) (rlc : List Ext3) :
    Nat → List Digest → List Arithmetic.Ext3 → Spongefish.State → Option (Opened × Spongefish.State)
  | _,[],values,s => some (⟨[],values⟩,s)
  | c,root::roots,values,s => do
      let (group,next) ← openSplitGroup hash hints l depth indices root w rlc c values s
      let (rest,last) ← openSplitGroups hash hints l depth indices w rlc (c+1) roots group.values next
      pure (⟨group.rows::rest.groups,rest.values⟩,last)

def matchesOpening (o : WhirIntermediate.OpenParams) (vector : List Arithmetic.Ext3)
    (index : Nat) (value : Arithmetic.Ext3) : Bool :=
  Arithmetic.eq (WhirTerminal.polynomial vector (WhirIntermediate.domainPoint o index)) value

def checkValues (o : WhirIntermediate.OpenParams) (vector : List Arithmetic.Ext3) :
    List Nat → List Arithmetic.Ext3 → Bool
  | [],[] => true
  | i::indices,value::values => matchesOpening o vector i value && checkValues o vector indices values
  | _,_ => false

/-- Standard final ordering: each actual authenticated row is canonically
decoded and immediately compared before the next row is decoded. -/
def checkStandardRows (o : WhirIntermediate.OpenParams) (l : WhirRows.Layout)
    (w vector : List Arithmetic.Ext3) : List Nat → List WhirRows.RawRow → Option (List Arithmetic.Ext3)
  | [],[] => some []
  | i::indices,row::rows => do
      let value ← WhirIntermediate.rowDot l w row
      if matchesOpening o vector i value then do
        let values ← checkStandardRows o l w vector indices rows
        pure (value::values)
      else none
  | _,_ => none

def openAndCheck (hash : Hash) (hints : Bytes) (p : Params) (s : PrefixState)
    (indices : List Nat) (w vector : List Arithmetic.Ext3) (start : Spongefish.State) :
    Option (Opened × Spongefish.State) :=
  if s.current.completedRounds = 0 then do
    let (opened,last) ← openSplitGroups hash hints (WhirIntermediate.layout s.current p.openParams)
      p.openParams.merkleDepth indices w s.current.vectorRlc 0 s.current.initialRoots
      (List.replicate indices.length Arithmetic.zero) start
    if checkValues p.openParams vector indices opened.values then pure (opened,last) else none
  else do
    let (rows,last) ← WhirRows.openGroup hash s.current.previousRoot p.openParams.merkleDepth indices
      (WhirIntermediate.layout s.current p.openParams) hints start
    let values ← checkStandardRows p.openParams (WhirIntermediate.layout s.current p.openParams) w vector indices rows
    pure (⟨[rows],values⟩,last)

structure FinalRows where
  vector : List Ext3
  indices : List Nat
  weights : List Arithmetic.Ext3
  opened : Opened
  afterRows : Spongefish.State

def finalRows (hash : Hash) (source hints : Bytes) (p : Params) (s : PrefixState) : Option FinalRows := do
  let (vector,afterVector) ← Spongefish.proverExt3Many hash source p.finalSize
    (WhirIntermediate.spongeState s.current)
  let afterPow ← Spongefish.verifyPow hash afterVector source p.finalPowThreshold
  let (indices,afterSampling) ← WhirSampling.challengeIndicesReference hash afterPow
    p.openParams.codewordLength p.openParams.inDomainSamples
  let w ← WhirIntermediate.weights s.current p.openParams
  let (opened,afterRows) ← openAndCheck hash hints p s indices w (vector.map Subtype.val) afterSampling
  pure ⟨vector,indices,w,opened,afterRows⟩

def groupPlans (s : PrefixState) (r : FinalRows) : List WhirTerminal.GroupPlan :=
  if s.current.completedRounds = 0 then
    (s.current.initialRoots.zip s.current.vectorRlc).map fun pair =>
      ⟨rootWord pair.1,WhirTerminal.tensorWeights [pair.2.val] r.weights⟩
  else [⟨rootWord s.current.previousRoot,r.weights⟩]

def context (p : Params) (s : PrefixState) (r : FinalRows) : WhirFinal.Context :=
  { rowPlan := ⟨groupPlans s r,r.indices,p.finalRounds,p.finalSize,
      p.openParams.domainGenerator.val,p.openParams.numCosets,p.openParams.cosetSize⟩
    prefixRandomness := s.current.sumcheck.finalRandomness
    priorSum := s.current.sumcheck.sum
    afterRows := WhirFinalSpongefish.fromSpongefish r.afterRows
    hintPos := r.afterRows.hintPos
    totalVariables := totalVariables s
    powThreshold := p.finalSumcheckPowThreshold
    roundConstraints := s.current.constraints
    forms := WhirPrefix.linearForms s.origin }

structure Result where
  retained : PrefixState
  rows : FinalRows
  finalSumcheck : WhirFinal.State

/-- The existing concrete final engine and SAME WhirFinal.finalClaim/exhausted
are used directly, without a redundant row recheck or new contextShape guard. -/
def finish (hash : Hash) (source hints : Bytes) (p : Params) (s : PrefixState) (r : FinalRows) : Option Result := do
  let c := context p s r
  let last ← WhirFinal.runRounds (WhirFinalSpongefish.engine hash) p.finalSumcheckPowThreshold
    (WhirFinalSpongefish.fromTranscriptBytes source) p.finalRounds (WhirFinal.start c)
  if WhirFinal.finalClaim c (r.vector.map Subtype.val) last &&
      WhirFinal.exhausted c (WhirFinalSpongefish.fromTranscriptBytes source)
        (WhirFinalSpongefish.fromTranscriptBytes hints) last then
    pure ⟨s,r,last⟩
  else none

def runTail (hash : Hash) (source hints : Bytes) (p : Params) (s : PrefixState) : Option Result := do
  let rows ← finalRows hash source hints p s
  finish hash source hints p s rows

def run (hash : Hash) (protocolId sessionId instanceBytes source hints : Bytes)
    (initial : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (initialCount initialThreshold : Nat)
    (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams)) (p : Params) : Option Result := do
  let start := Spongefish.init hash protocolId sessionId instanceBytes
  let retained ← runPrefix hash source hints initial roots expected mask initialCount initialThreshold start rounds
  runTail hash source hints p retained

theorem prefix_success_retains_actual_pair (hash : Hash) (source hints : Bytes) (initial : WhirInitial.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (count threshold : Nat)
    (start : Spongefish.State) (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams))
    (retained : PrefixState)
    (h : runPrefix hash source hints initial roots expected mask count threshold start rounds = some retained) :
    WhirPrefix.run hash source initial roots expected mask count threshold start = some retained.origin ∧
    WhirIntermediate.runRounds hash source hints rounds (WhirIntermediate.fromPrefix retained.origin) =
      some retained.current := by
  unfold runPrefix at h
  cases hp : WhirPrefix.run hash source initial roots expected mask count threshold start with
  | none => simp [hp] at h
  | some origin =>
    cases hi : WhirIntermediate.runRounds hash source hints rounds (WhirIntermediate.fromPrefix origin) with
    | none => simp [hp,hi] at h
    | some current =>
      simp only [hp,hi,bind,Option.bind,pure,Option.some.injEq] at h
      subst retained
      exact ⟨rfl,hi⟩

theorem split_row_success_same_bytes_hash_decode_then_cursor (hash : Hash) (hints : Bytes)
    (l : WhirRows.Layout) (w : List Arithmetic.Ext3) (rlc : List Ext3) (c : Nat)
    (previous value : Arithmetic.Ext3) (s t : Spongefish.State) (row : WhirRows.RawRow) (leaf : Digest)
    (h : readSplitRow hash hints l w rlc c previous s = some ((row,leaf,value),t)) :
    ∃ nextOffset dot coefficient,
      Spongefish.readSlice hints s.hintPos (WhirRows.rowBytes l) = some (row.bytes,nextOffset) ∧
      row.offset = s.hintPos ∧ leaf = hash row.bytes ∧
      WhirIntermediate.rowDot l w row = some dot ∧ rlc.get? c = some coefficient ∧
      value = Arithmetic.eadd previous (Arithmetic.eadd Arithmetic.zero (Arithmetic.emul coefficient.val dot)) ∧
      t = {s with hintPos := nextOffset} := by
  unfold readSplitRow at h
  cases hs : Spongefish.readSlice hints s.hintPos (WhirRows.rowBytes l) with
  | none => simp [hs] at h
  | some pair =>
    rcases pair with ⟨bytes,nextOffset⟩
    cases hd : WhirIntermediate.rowDot l w ⟨s.hintPos,bytes⟩ with
    | none => simp only [hs,hd,bind,Option.bind] at h
    | some dot =>
      cases hc : rlc.get? c with
      | none => simp only [hs,hd,hc,bind,Option.bind] at h
      | some coefficient =>
        simp only [hs,hd,hc,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl,rfl,rfl⟩,rfl⟩
        exact ⟨nextOffset,dot,coefficient,rfl,rfl,rfl,hd,rfl,rfl,rfl⟩

theorem split_rows_success_hashes_and_lengths (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (w : List Arithmetic.Ext3) (rlc : List Ext3) (c : Nat) (previous : List Arithmetic.Ext3)
    (s t : Spongefish.State) (rows : SplitRows)
    (h : readSplitRows hash hints l w rlc c previous s = some (rows,t)) :
    rows.hashes = WhirRows.rowHashes hash rows.rows ∧ rows.rows.length = previous.length ∧
      rows.values.length = previous.length := by
  induction previous generalizing s rows with
  | nil => cases h; exact ⟨rfl,rfl,rfl⟩
  | cons value values ih =>
    cases hr : readSplitRow hash hints l w rlc c value s with
    | none => simp [readSplitRows,hr] at h
    | some pair =>
      rcases pair with ⟨⟨row,leaf,updated⟩,next⟩
      cases ht : readSplitRows hash hints l w rlc c values next with
      | none => simp [readSplitRows,hr,ht] at h
      | some pair =>
        rcases pair with ⟨rest,last⟩
        simp only [readSplitRows,hr,ht,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨_,_,_,_,_,hleaf,_,_,_,_⟩ :=
          split_row_success_same_bytes_hash_decode_then_cursor hash hints l w rlc c value updated s next row leaf hr
        have a := ih next rest ht
        exact ⟨by simp [WhirRows.rowHashes,hleaf,a.1],by simp [a.2.1],by simp [a.2.2]⟩

theorem split_group_success_actual_order (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (depth : Nat) (indices : List Nat) (root : Digest) (w : List Arithmetic.Ext3) (rlc : List Ext3)
    (c : Nat) (values : List Arithmetic.Ext3) (s t : Spongefish.State) (rows : SplitRows)
    (h : openSplitGroup hash hints l depth indices root w rlc c values s = some (rows,t)) :
    ∃ afterPrefix afterRows nextOffset,
      Spongefish.consumeVecPrefix s hints (indices.length*l.columns) = some afterPrefix ∧
      readSplitRows hash hints l w rlc c values afterPrefix = some (rows,afterRows) ∧
      Merkle.verify hash root depth indices rows.hashes hints afterRows.hintPos = some nextOffset ∧
      t = {afterRows with hintPos := nextOffset} := by
  unfold openSplitGroup at h
  cases hp : Spongefish.consumeVecPrefix s hints (indices.length*l.columns) with
  | none => simp [hp] at h
  | some afterPrefix =>
    cases hr : readSplitRows hash hints l w rlc c values afterPrefix with
    | none => simp [hp,hr] at h
    | some pair =>
      rcases pair with ⟨actual,afterRows⟩
      cases hm : Merkle.verify hash root depth indices actual.hashes hints afterRows.hintPos with
      | none => simp [hp,hr,hm] at h
      | some nextOffset =>
        simp only [hp,hr,hm,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨afterPrefix,afterRows,nextOffset,rfl,hr,hm,rfl⟩

theorem split_group_hashes_actual_decoded_rows (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (depth : Nat) (indices : List Nat) (root : Digest) (w : List Arithmetic.Ext3) (rlc : List Ext3)
    (c : Nat) (values : List Arithmetic.Ext3) (s t : Spongefish.State) (rows : SplitRows)
    (h : openSplitGroup hash hints l depth indices root w rlc c values s = some (rows,t)) :
    ∃ afterPrefix afterRows,
      readSplitRows hash hints l w rlc c values afterPrefix = some (rows,afterRows) ∧
      Merkle.verify hash root depth indices (WhirRows.rowHashes hash rows.rows) hints afterRows.hintPos =
        some t.hintPos := by
  obtain ⟨ap,ar,no,_,hr,hm,ht⟩ := split_group_success_actual_order hash hints l depth indices root w rlc c values s t rows h
  have he := (split_rows_success_hashes_and_lengths hash hints l w rlc c values ap ar rows hr).1
  exact ⟨ap,ar,hr,by simpa [ht,he] using hm⟩

theorem split_row_cursor_and_original_slice (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (w : List Arithmetic.Ext3) (rlc : List Ext3) (c : Nat) (previous value : Arithmetic.Ext3)
    (s t : Spongefish.State) (row : WhirRows.RawRow) (leaf : Digest)
    (h : readSplitRow hash hints l w rlc c previous s = some ((row,leaf,value),t)) :
    t.hintPos = s.hintPos+WhirRows.rowBytes l ∧ t.hintPos ≤ hints.length ∧
    t.sponge = s.sponge ∧ t.transcriptPos = s.transcriptPos ∧
    row.offset = s.hintPos ∧ row.bytes = (hints.drop s.hintPos).take (WhirRows.rowBytes l) ∧
    row.bytes.length = WhirRows.rowBytes l := by
  obtain ⟨next,_,_,hr,ho,_,_,_,_,ht⟩ :=
    split_row_success_same_bytes_hash_decode_then_cursor hash hints l w rlc c previous value s t row leaf h
  have a := Spongefish.read_slice_success hints row.bytes s.hintPos (WhirRows.rowBytes l) next hr
  exact ⟨by simpa [ht] using a.2.2.1,by simpa [ht] using a.2.2.2.2,
    by rw [ht],by rw [ht],ho,a.2.1,a.1⟩

theorem split_rows_success_exact_cursor (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (w : List Arithmetic.Ext3) (rlc : List Ext3) (c : Nat) (previous : List Arithmetic.Ext3)
    (s t : Spongefish.State) (rows : SplitRows) (hb : s.hintPos ≤ hints.length)
    (h : readSplitRows hash hints l w rlc c previous s = some (rows,t)) :
    t.hintPos = s.hintPos+previous.length*WhirRows.rowBytes l ∧ t.hintPos ≤ hints.length ∧
    t.sponge = s.sponge ∧ t.transcriptPos = s.transcriptPos ∧
    WhirRows.contiguousSlices hints (WhirRows.rowBytes l) s.hintPos rows.rows := by
  induction previous generalizing s rows with
  | nil => cases h; exact ⟨by simp,hb,rfl,rfl,True.intro⟩
  | cons value values ih =>
    cases hr : readSplitRow hash hints l w rlc c value s with
    | none => simp [readSplitRows,hr] at h
    | some pair =>
      rcases pair with ⟨⟨row,leaf,updated⟩,next⟩
      cases ht : readSplitRows hash hints l w rlc c values next with
      | none => simp [readSplitRows,hr,ht] at h
      | some pair =>
        rcases pair with ⟨rest,last⟩
        simp only [readSplitRows,hr,ht,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        have a := split_row_cursor_and_original_slice hash hints l w rlc c value updated s next row leaf hr
        have b := ih next rest a.2.1 ht
        refine ⟨?_,b.2.1,b.2.2.1.trans a.2.2.1,b.2.2.2.1.trans a.2.2.2.1,?_⟩
        · simp only [List.length_cons,Nat.succ_mul]; omega
        · exact ⟨a.2.2.2.2.1,a.2.2.2.2.2.1,a.2.2.2.2.2.2,by omega,
            by simpa [a.1] using b.2.2.2.2⟩

theorem split_group_success_exact_merkle_offset (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (depth : Nat) (indices : List Nat) (root : Digest) (w : List Arithmetic.Ext3) (rlc : List Ext3)
    (c : Nat) (values : List Arithmetic.Ext3) (s t : Spongefish.State) (rows : SplitRows)
    (hl : values.length = indices.length)
    (h : openSplitGroup hash hints l depth indices root w rlc c values s = some (rows,t)) :
    Merkle.verify hash root depth indices (WhirRows.rowHashes hash rows.rows) hints
      (s.hintPos+8+indices.length*WhirRows.rowBytes l) = some t.hintPos ∧
    WhirRows.contiguousSlices hints (WhirRows.rowBytes l) (s.hintPos+8) rows.rows := by
  obtain ⟨ap,ar,no,hp,hr,hm,ht⟩ := split_group_success_actual_order hash hints l depth indices root w rlc c values s t rows h
  have a := Spongefish.vec_prefix_success_exact s ap hints _ hp
  have b := split_rows_success_exact_cursor hash hints l w rlc c values ap ar rows a.2.1 hr
  have d := (split_rows_success_hashes_and_lengths hash hints l w rlc c values ap ar rows hr).1
  exact ⟨by simpa [ht,d,b.1,a.1,hl] using hm,by simpa [a.1] using b.2.2.2.2⟩

theorem split_groups_success_first_actual_group (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (depth : Nat) (indices : List Nat) (w : List Arithmetic.Ext3) (rlc : List Ext3)
    (c : Nat) (root : Digest) (roots : List Digest) (values : List Arithmetic.Ext3)
    (s t : Spongefish.State) (opened : Opened)
    (h : openSplitGroups hash hints l depth indices w rlc c (root::roots) values s = some (opened,t)) :
    ∃ group next rest,
      openSplitGroup hash hints l depth indices root w rlc c values s = some (group,next) ∧
      openSplitGroups hash hints l depth indices w rlc (c+1) roots group.values next = some (rest,t) ∧
      opened.groups = group.rows::rest.groups ∧ opened.values = rest.values := by
  cases hg : openSplitGroup hash hints l depth indices root w rlc c values s with
  | none => simp [openSplitGroups,hg] at h
  | some pair =>
    rcases pair with ⟨group,next⟩
    cases hr : openSplitGroups hash hints l depth indices w rlc (c+1) roots group.values next with
    | none => simp [openSplitGroups,hg,hr] at h
    | some pair =>
      rcases pair with ⟨rest,last⟩
      simp only [openSplitGroups,hg,hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨group,next,rest,rfl,hr,rfl,rfl⟩

theorem split_groups_each_root_has_actual_authentication (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (depth : Nat) (indices : List Nat) (w : List Arithmetic.Ext3) (rlc : List Ext3)
    (c : Nat) (roots : List Digest) (values : List Arithmetic.Ext3)
    (s t : Spongefish.State) (opened : Opened)
    (h : openSplitGroups hash hints l depth indices w rlc c roots values s = some (opened,t)) :
    ∀ position root, roots.get? position = some root →
      ∃ previous before after group,
        opened.groups.get? position = some group.rows ∧
        openSplitGroup hash hints l depth indices root w rlc (c+position) previous before = some (group,after) := by
  induction roots generalizing c s values opened with
  | nil => intro position root hr; simp at hr
  | cons root roots ih =>
    obtain ⟨group,next,rest,hg,hr,hgroups,_⟩ :=
      split_groups_success_first_actual_group hash hints l depth indices w rlc c root roots values s t opened h
    intro position selected hs
    cases position with
    | zero =>
      cases hs
      exact ⟨values,s,next,group,by rw [hgroups]; rfl,by simpa only [Nat.add_zero] using hg⟩
    | succ position =>
      obtain ⟨previous,before,after,selectedGroup,hi,ho⟩ := ih (c+1) group.values next rest hr position selected hs
      exact ⟨previous,before,after,selectedGroup,by simpa only [hgroups,List.get?_cons_succ] using hi,
        by simpa only [Nat.add_assoc,Nat.add_comm 1 position] using ho⟩

theorem split_branch_success_has_actual_groups (hash : Hash) (hints : Bytes) (p : Params)
    (s : PrefixState) (indices : List Nat) (w vector : List Arithmetic.Ext3)
    (start last : Spongefish.State) (opened : Opened) (hz : s.current.completedRounds = 0)
    (h : openAndCheck hash hints p s indices w vector start = some (opened,last)) :
    openSplitGroups hash hints (WhirIntermediate.layout s.current p.openParams) p.openParams.merkleDepth
      indices w s.current.vectorRlc 0 s.current.initialRoots (List.replicate indices.length Arithmetic.zero) start =
        some (opened,last) := by
  simp only [openAndCheck,hz,↓reduceIte] at h
  cases hg : openSplitGroups hash hints (WhirIntermediate.layout s.current p.openParams) p.openParams.merkleDepth
      indices w s.current.vectorRlc 0 s.current.initialRoots (List.replicate indices.length Arithmetic.zero) start with
  | none => simp [hg] at h
  | some pair =>
    rcases pair with ⟨actual,next⟩
    simp only [hg,bind,Option.bind] at h
    split at h
    · cases h; rfl
    · contradiction

theorem standard_branch_success_authenticates_before_decode (hash : Hash) (hints : Bytes) (p : Params)
    (s : PrefixState) (indices : List Nat) (w vector : List Arithmetic.Ext3)
    (start last : Spongefish.State) (opened : Opened) (hz : s.current.completedRounds ≠ 0)
    (h : openAndCheck hash hints p s indices w vector start = some (opened,last)) :
    ∃ rows, opened.groups = [rows] ∧
      WhirRows.openGroup hash s.current.previousRoot p.openParams.merkleDepth indices
        (WhirIntermediate.layout s.current p.openParams) hints start = some (rows,last) ∧
      checkStandardRows p.openParams (WhirIntermediate.layout s.current p.openParams) w vector indices rows =
        some opened.values := by
  simp only [openAndCheck,hz,↓reduceIte] at h
  cases hg : WhirRows.openGroup hash s.current.previousRoot p.openParams.merkleDepth indices
      (WhirIntermediate.layout s.current p.openParams) hints start with
  | none => simp [hg] at h
  | some pair =>
    rcases pair with ⟨rows,next⟩
    cases hc : checkStandardRows p.openParams (WhirIntermediate.layout s.current p.openParams) w vector indices rows with
    | none => simp [hg,hc] at h
    | some values =>
      simp only [hg,hc,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨rows,rfl,rfl,hc⟩

theorem checked_values_cover_every_index (o : WhirIntermediate.OpenParams) (vector : List Arithmetic.Ext3)
    (indices : List Nat) (values : List Arithmetic.Ext3) (h : checkValues o vector indices values = true) :
    indices.length = values.length ∧ ∀ pair ∈ indices.zip values, matchesOpening o vector pair.1 pair.2 = true := by
  induction indices generalizing values with
  | nil => cases values <;> simp_all [checkValues]
  | cons i indices ih =>
    cases values with
    | nil => simp [checkValues] at h
    | cons v values =>
      simp only [checkValues,Bool.and_eq_true] at h
      have he := ih values h.2
      exact ⟨by simp [he.1],by
        intro pair hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact h.1
        · exact he.2 pair hp⟩

theorem standard_success_checks_same_values (o : WhirIntermediate.OpenParams) (l : WhirRows.Layout)
    (w vector : List Arithmetic.Ext3) (indices : List Nat) (rows : List WhirRows.RawRow)
    (values : List Arithmetic.Ext3) (h : checkStandardRows o l w vector indices rows = some values) :
    checkValues o vector indices values = true := by
  induction indices generalizing rows values with
  | nil =>
    cases rows with
    | nil => cases h; rfl
    | cons row rows => simp [checkStandardRows] at h
  | cons i indices ih =>
    cases rows with
    | nil => simp [checkStandardRows] at h
    | cons row rows =>
      cases hd : WhirIntermediate.rowDot l w row with
      | none => simp [checkStandardRows,hd] at h
      | some value =>
        by_cases hm : matchesOpening o vector i value = true
        · cases ht : checkStandardRows o l w vector indices rows with
          | none => simp [checkStandardRows,hd,hm,ht] at h
          | some tail =>
            simp only [checkStandardRows,hd,hm,↓reduceIte,ht,bind,Option.bind,pure,Option.some.injEq] at h
            subst values
            simp only [checkValues,hm,ih rows tail ht,Bool.true_and]
        · simp [checkStandardRows,hd,hm] at h

theorem open_check_success_preserves_horner_checks (hash : Hash) (hints : Bytes) (p : Params)
    (s : PrefixState) (indices : List Nat) (w vector : List Arithmetic.Ext3)
    (start last : Spongefish.State) (opened : Opened)
    (h : openAndCheck hash hints p s indices w vector start = some (opened,last)) :
    checkValues p.openParams vector indices opened.values = true := by
  unfold openAndCheck at h
  split at h
  · cases hs : openSplitGroups hash hints (WhirIntermediate.layout s.current p.openParams)
        p.openParams.merkleDepth indices w s.current.vectorRlc 0 s.current.initialRoots
        (List.replicate indices.length Arithmetic.zero) start with
    | none => simp [hs] at h
    | some pair =>
      rcases pair with ⟨actual,next⟩
      simp only [hs,bind,Option.bind] at h
      split at h
      · cases h; assumption
      · contradiction
  · cases hg : WhirRows.openGroup hash s.current.previousRoot p.openParams.merkleDepth indices
        (WhirIntermediate.layout s.current p.openParams) hints start with
    | none => simp [hg] at h
    | some pair =>
      rcases pair with ⟨rows,next⟩
      cases hc : checkStandardRows p.openParams (WhirIntermediate.layout s.current p.openParams) w vector indices rows with
      | none => simp [hg,hc] at h
      | some values =>
        simp only [hg,hc,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact standard_success_checks_same_values p.openParams (WhirIntermediate.layout s.current p.openParams)
          w vector indices rows values hc

theorem final_rows_success_is_one_source_execution (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (r : FinalRows) (h : finalRows hash source hints p s = some r) :
    ∃ afterVector afterPow afterSampling,
      Spongefish.proverExt3Many hash source p.finalSize (WhirIntermediate.spongeState s.current) =
        some (r.vector,afterVector) ∧
      Spongefish.verifyPow hash afterVector source p.finalPowThreshold = some afterPow ∧
      WhirSampling.challengeIndicesReference hash afterPow p.openParams.codewordLength
        p.openParams.inDomainSamples = some (r.indices,afterSampling) ∧
      WhirIntermediate.weights s.current p.openParams = some r.weights ∧
      openAndCheck hash hints p s r.indices r.weights (r.vector.map Subtype.val) afterSampling =
        some (r.opened,r.afterRows) := by
  unfold finalRows at h
  cases hv : Spongefish.proverExt3Many hash source p.finalSize (WhirIntermediate.spongeState s.current) with
  | none => simp [hv] at h
  | some pair =>
    rcases pair with ⟨vector,afterVector⟩
    cases hp : Spongefish.verifyPow hash afterVector source p.finalPowThreshold with
    | none => simp [hv,hp] at h
    | some afterPow =>
      cases hs : WhirSampling.challengeIndicesReference hash afterPow p.openParams.codewordLength p.openParams.inDomainSamples with
      | none => simp [hv,hp,hs] at h
      | some pair =>
        rcases pair with ⟨indices,afterSampling⟩
        cases hw : WhirIntermediate.weights s.current p.openParams with
        | none => simp [hv,hp,hs,hw] at h
        | some w =>
          cases ho : openAndCheck hash hints p s indices w (vector.map Subtype.val) afterSampling with
          | none => simp [hv,hp,hs,hw,ho] at h
          | some pair =>
            rcases pair with ⟨opened,afterRows⟩
            simp only [hv,hp,hs,hw,ho,bind,Option.bind,pure,Option.some.injEq] at h
            subst r
            exact ⟨afterVector,afterPow,afterSampling,rfl,hp,hs,rfl,ho⟩

theorem final_rows_all_horner_checks_same_vector (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (r : FinalRows) (h : finalRows hash source hints p s = some r) :
    r.vector.length = p.finalSize ∧ r.indices.length = r.opened.values.length ∧
      ∀ pair ∈ r.indices.zip r.opened.values,
        Arithmetic.normalize (WhirTerminal.polynomial (r.vector.map Subtype.val)
          (WhirIntermediate.domainPoint p.openParams pair.1)) = Arithmetic.normalize pair.2 := by
  obtain ⟨av,_,asamp,hv,_,_,_,ho⟩ := final_rows_success_is_one_source_execution hash source hints p s r h
  have a := Spongefish.prover_many_exact_count_and_cursor hash source p.finalSize
    (WhirIntermediate.spongeState s.current) av r.vector hv
  have b := checked_values_cover_every_index p.openParams (r.vector.map Subtype.val) r.indices r.opened.values
    (open_check_success_preserves_horner_checks hash hints p s r.indices r.weights (r.vector.map Subtype.val)
      asamp r.afterRows r.opened ho)
  exact ⟨a.1,b.1,fun pair hp => (Arithmetic.normalized_equality_iff _ _).mp (b.2 pair hp)⟩

theorem context_fields_are_derived (p : Params) (s : PrefixState) (r : FinalRows) :
    (context p s r).prefixRandomness = s.current.sumcheck.finalRandomness ∧
    (context p s r).priorSum = s.current.sumcheck.sum ∧
    (context p s r).roundConstraints = s.current.constraints ∧
    (context p s r).forms = WhirPrefix.linearForms s.origin ∧
    (context p s r).hintPos = r.afterRows.hintPos ∧
    (context p s r).afterRows = WhirFinalSpongefish.fromSpongefish r.afterRows :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem fixed_profile_supplies_context_shape (p : Params) (s : PrefixState) (r : FinalRows)
    (h : ProfileShape s p) : WhirFinal.contextShape (context p s r) = true := by
  rcases h with ⟨_,_,_,hvars,hpos,hbound,hforms,hpoints,hconstraints⟩
  have hl : (WhirPrefix.linearForms s.origin).length = s.origin.initial.forms.length := by
    simp [WhirPrefix.linearForms]
  have hp : ∀ form ∈ WhirPrefix.linearForms s.origin, form.point.length = totalVariables s := by
    intro form hf
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hf
    simpa using hpoints original ho
  simp only [WhirFinal.contextShape,context,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  exact ⟨⟨⟨hvars,hpos,hbound,by omega⟩,hp⟩,hconstraints⟩

theorem finish_success_checks_existing_final_engine_and_eof (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (r : FinalRows) (result : Result)
    (h : finish hash source hints p s r = some result) :
    result.retained = s ∧ result.rows = r ∧
    WhirFinal.runRounds (WhirFinalSpongefish.engine hash) p.finalSumcheckPowThreshold
      (WhirFinalSpongefish.fromTranscriptBytes source) p.finalRounds (WhirFinal.start (context p s r)) =
        some result.finalSumcheck ∧
    WhirFinal.finalClaim (context p s r) (r.vector.map Subtype.val) result.finalSumcheck = true ∧
    WhirFinal.exhausted (context p s r) (WhirFinalSpongefish.fromTranscriptBytes source)
      (WhirFinalSpongefish.fromTranscriptBytes hints) result.finalSumcheck = true := by
  unfold finish at h
  cases hf : WhirFinal.runRounds (WhirFinalSpongefish.engine hash) p.finalSumcheckPowThreshold
      (WhirFinalSpongefish.fromTranscriptBytes source) p.finalRounds (WhirFinal.start (context p s r)) with
  | none => simp [hf] at h
  | some last =>
    simp only [hf,bind,Option.bind] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨rfl,rfl,rfl,hc.1,hc.2⟩
    · contradiction

theorem tail_success_same_vector_and_context (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (result : Result)
    (h : runTail hash source hints p s = some result) :
    result.retained = s ∧ finalRows hash source hints p s = some result.rows ∧
    finish hash source hints p s result.rows = some result := by
  unfold runTail at h
  cases hr : finalRows hash source hints p s with
  | none => simp [hr] at h
  | some r =>
    simp only [hr,bind,Option.bind] at h
    have hf := finish_success_checks_existing_final_engine_and_eof hash source hints p s r result h
    exact ⟨hf.1,by rw [hf.2.1],by rw [hf.2.1]; exact h⟩

theorem accepted_tail_has_exact_final_rounds_and_both_eof (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (result : Result)
    (h : runTail hash source hints p s = some result) :
    result.finalSumcheck.finalRandomness.length = p.finalRounds ∧
    result.finalSumcheck.cursor.transcriptPos = source.length ∧ result.rows.afterRows.hintPos = hints.length := by
  have ht := tail_success_same_vector_and_context hash source hints p s result h
  have hf := finish_success_checks_existing_final_engine_and_eof hash source hints p s result.rows result ht.2.2
  have hc := WhirFinal.completed_round_count_exact (WhirFinalSpongefish.engine hash) p.finalSumcheckPowThreshold
    (WhirFinalSpongefish.fromTranscriptBytes source) p.finalRounds (WhirFinal.start (context p s result.rows))
    result.finalSumcheck hf.2.2.1
  have he := hf.2.2.2.2
  simp only [WhirFinal.exhausted,context,decide_eq_true_eq,
    WhirFinalSpongefish.fromTranscriptBytes,List.length_map] at he
  exact ⟨by simpa [WhirFinal.start] using hc,he⟩

theorem accepted_tail_same_vector_nonzero_and_exact_claim (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (result : Result)
    (h : runTail hash source hints p s = some result) :
    Arithmetic.isZero (WhirFinal.finalPolynomial (result.rows.vector.map Subtype.val)
      result.finalSumcheck.finalRandomness) = false ∧
    ∃ inverse, WhirFinal.inverse (WhirFinal.finalPolynomial (result.rows.vector.map Subtype.val)
      result.finalSumcheck.finalRandomness) = some inverse ∧
      WhirFinal.subtractConstraints (s.current.sumcheck.finalRandomness ++ result.finalSumcheck.finalRandomness)
        s.current.constraints (Arithmetic.emul result.finalSumcheck.sum inverse) =
      WhirFinal.expectedLinearForm (WhirPrefix.linearForms s.origin)
        (s.current.sumcheck.finalRandomness ++ result.finalSumcheck.finalRandomness) := by
  have ht := tail_success_same_vector_and_context hash source hints p s result h
  have hf := finish_success_checks_existing_final_engine_and_eof hash source hints p s result.rows result ht.2.2
  have hn := WhirFinal.final_claim_requires_nonzero_and_full_equation (context p s result.rows)
    (result.rows.vector.map Subtype.val) result.finalSumcheck hf.2.2.2.1
  have he := WhirFinal.final_claim_requires_exact_full_equation (context p s result.rows)
    (result.rows.vector.map Subtype.val) result.finalSumcheck hf.2.2.2.1
  exact ⟨hn.1,by simpa only [context] using he⟩

theorem accepted_tail_every_sample_compared_with_same_vector (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (result : Result)
    (h : runTail hash source hints p s = some result) :
    result.rows.vector.length = p.finalSize ∧ result.rows.indices.length = result.rows.opened.values.length ∧
      ∀ pair ∈ result.rows.indices.zip result.rows.opened.values,
        Arithmetic.normalize (WhirTerminal.polynomial (result.rows.vector.map Subtype.val)
          (WhirIntermediate.domainPoint p.openParams pair.1)) = Arithmetic.normalize pair.2 :=
  final_rows_all_horner_checks_same_vector hash source hints p s result.rows
    (tail_success_same_vector_and_context hash source hints p s result h).2.1

theorem accepted_tail_full_final_fold_is_singleton (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (result : Result) (hs : p.finalSize = 2^p.finalRounds)
    (h : runTail hash source hints p s = some result) :
    (WhirFinal.foldLayers result.finalSumcheck.finalRandomness.reverse
      (result.rows.vector.map Subtype.val)).length = 1 := by
  have hv := (accepted_tail_every_sample_compared_with_same_vector hash source hints p s result h).1
  have hr := (accepted_tail_has_exact_final_rounds_and_both_eof hash source hints p s result h).1
  apply WhirFinal.full_final_fold_has_one_value
  simp only [List.length_map,List.length_reverse,hv,hr,hs]

theorem whole_execution_retains_initial_and_intermediate_provenance (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (initial : WhirInitial.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (count threshold : Nat)
    (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams)) (p : Params) (result : Result)
    (h : run hash protocolId sessionId instanceBytes source hints initial roots expected mask count threshold rounds p =
      some result) :
    WhirPrefix.run hash source initial roots expected mask count threshold
      (Spongefish.init hash protocolId sessionId instanceBytes) = some result.retained.origin ∧
    WhirIntermediate.runRounds hash source hints rounds (WhirIntermediate.fromPrefix result.retained.origin) =
      some result.retained.current ∧ runTail hash source hints p result.retained = some result := by
  unfold run at h
  cases hp : runPrefix hash source hints initial roots expected mask count threshold
      (Spongefish.init hash protocolId sessionId instanceBytes) rounds with
  | none => simp [hp] at h
  | some retained =>
    simp only [hp,bind,Option.bind] at h
    have he := (tail_success_same_vector_and_context hash source hints p retained result h).1
    have hr := prefix_success_retains_actual_pair hash source hints initial roots expected mask count threshold
      (Spongefish.init hash protocolId sessionId instanceBytes) rounds retained hp
    simpa only [he] using And.intro hr.1 (And.intro hr.2 h)

theorem accepted_split_tail_each_initial_root_has_actual_merkle (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (result : Result) (position : Nat) (root : Digest)
    (hz : s.current.completedRounds = 0) (hr : s.current.initialRoots.get? position = some root)
    (h : runTail hash source hints p s = some result) :
    ∃ previous before after group afterPrefix afterRows,
      result.rows.opened.groups.get? position = some group.rows ∧
      openSplitGroup hash hints (WhirIntermediate.layout s.current p.openParams) p.openParams.merkleDepth
        result.rows.indices root result.rows.weights s.current.vectorRlc position previous before = some (group,after) ∧
      readSplitRows hash hints (WhirIntermediate.layout s.current p.openParams) result.rows.weights
        s.current.vectorRlc position previous afterPrefix = some (group,afterRows) ∧
      Merkle.verify hash root p.openParams.merkleDepth result.rows.indices
        (WhirRows.rowHashes hash group.rows) hints afterRows.hintPos = some after.hintPos := by
  have ht := tail_success_same_vector_and_context hash source hints p s result h
  obtain ⟨_,_,asamp,_,_,_,_,ho⟩ := final_rows_success_is_one_source_execution hash source hints p s result.rows ht.2.1
  have hg := split_branch_success_has_actual_groups hash hints p s result.rows.indices result.rows.weights
    (result.rows.vector.map Subtype.val) asamp result.rows.afterRows result.rows.opened hz ho
  obtain ⟨previous,before,after,group,hi,hgroup⟩ := split_groups_each_root_has_actual_authentication hash hints
    (WhirIntermediate.layout s.current p.openParams) p.openParams.merkleDepth result.rows.indices result.rows.weights
    s.current.vectorRlc 0 s.current.initialRoots (List.replicate result.rows.indices.length Arithmetic.zero)
    asamp result.rows.afterRows result.rows.opened hg position root hr
  simp only [Nat.zero_add] at hgroup
  obtain ⟨ap,ar,hd,hm⟩ := split_group_hashes_actual_decoded_rows hash hints
    (WhirIntermediate.layout s.current p.openParams) p.openParams.merkleDepth result.rows.indices root result.rows.weights
    s.current.vectorRlc position previous before after group hgroup
  exact ⟨previous,before,after,group,ap,ar,hi,hgroup,hd,hm⟩

theorem accepted_standard_tail_same_root_rows_and_merkle_offset (hash : Hash) (source hints : Bytes)
    (p : Params) (s : PrefixState) (result : Result) (hz : s.current.completedRounds ≠ 0)
    (h : runTail hash source hints p s = some result) :
    ∃ rows afterSampling, result.rows.opened.groups = [rows] ∧
      WhirRows.openGroup hash s.current.previousRoot p.openParams.merkleDepth result.rows.indices
        (WhirIntermediate.layout s.current p.openParams) hints afterSampling = some (rows,result.rows.afterRows) ∧
      checkStandardRows p.openParams (WhirIntermediate.layout s.current p.openParams)
        result.rows.weights (result.rows.vector.map Subtype.val) result.rows.indices rows = some result.rows.opened.values ∧
      Merkle.verify hash s.current.previousRoot p.openParams.merkleDepth result.rows.indices
        (WhirRows.rowHashes hash rows) hints (afterSampling.hintPos+8+result.rows.indices.length*
          WhirRows.rowBytes (WhirIntermediate.layout s.current p.openParams)) = some result.rows.afterRows.hintPos := by
  have ht := tail_success_same_vector_and_context hash source hints p s result h
  obtain ⟨_,_,asamp,_,_,_,_,ho⟩ := final_rows_success_is_one_source_execution hash source hints p s result.rows ht.2.1
  obtain ⟨rows,hg,ha,hc⟩ := standard_branch_success_authenticates_before_decode hash hints p s
    result.rows.indices result.rows.weights (result.rows.vector.map Subtype.val) asamp result.rows.afterRows
    result.rows.opened hz ho
  exact ⟨rows,asamp,hg,ha,hc,WhirRows.group_success_same_merkle_inputs hash s.current.previousRoot
    p.openParams.merkleDepth result.rows.indices (WhirIntermediate.layout s.current p.openParams)
    hints asamp result.rows.afterRows rows ha⟩

theorem standard_checks_decode_every_actual_row (o : WhirIntermediate.OpenParams) (l : WhirRows.Layout)
    (w vector : List Arithmetic.Ext3) (indices : List Nat) (rows : List WhirRows.RawRow)
    (values : List Arithmetic.Ext3) (h : checkStandardRows o l w vector indices rows = some values) :
    ∀ pair ∈ indices.zip rows, ∃ value,
      WhirIntermediate.rowDot l w pair.2 = some value ∧ matchesOpening o vector pair.1 value = true := by
  induction indices generalizing rows values with
  | nil => simp
  | cons i indices ih =>
    cases rows with
    | nil => simp
    | cons row rows =>
      cases hd : WhirIntermediate.rowDot l w row with
      | none => simp [checkStandardRows,hd] at h
      | some value =>
        by_cases hm : matchesOpening o vector i value = true
        · cases ht : checkStandardRows o l w vector indices rows with
          | none => simp [checkStandardRows,hd,hm,ht] at h
          | some tail =>
            intro pair hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨value,hd,hm⟩
            · exact ih rows tail ht pair hp
        · simp [checkStandardRows,hd,hm] at h

theorem split_rows_decode_every_raw_row_before_auth (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (w : List Arithmetic.Ext3) (rlc : List Ext3) (c : Nat) (previous : List Arithmetic.Ext3)
    (s t : Spongefish.State) (rows : SplitRows)
    (h : readSplitRows hash hints l w rlc c previous s = some (rows,t)) :
    ∀ row ∈ rows.rows, ∃ dot, WhirIntermediate.rowDot l w row = some dot := by
  induction previous generalizing s rows with
  | nil => cases h; simp
  | cons value values ih =>
    cases hr : readSplitRow hash hints l w rlc c value s with
    | none => simp [readSplitRows,hr] at h
    | some pair =>
      rcases pair with ⟨⟨row,leaf,updated⟩,next⟩
      cases ht : readSplitRows hash hints l w rlc c values next with
      | none => simp [readSplitRows,hr,ht] at h
      | some pair =>
        rcases pair with ⟨rest,last⟩
        simp only [readSplitRows,hr,ht,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        intro selected hs
        rcases List.mem_cons.mp hs with rfl | hs
        · obtain ⟨_,dot,_,_,_,_,hd,_,_,_⟩ :=
            split_row_success_same_bytes_hash_decode_then_cursor hash hints l w rlc c value updated s next selected leaf hr
          exact ⟨dot,hd⟩
        · exact ih next rest ht selected hs

theorem split_empty_query_still_consumes_vec_prefix (hash : Hash) (hints : Bytes) (l : WhirRows.Layout)
    (depth : Nat) (root : Digest) (w : List Arithmetic.Ext3) (rlc : List Ext3) (c : Nat)
    (s t : Spongefish.State) (rows : SplitRows)
    (h : openSplitGroup hash hints l depth [] root w rlc c [] s = some (rows,t)) :
    rows.rows = [] ∧ rows.hashes = [] ∧ rows.values = [] ∧ t.hintPos = s.hintPos+8 := by
  obtain ⟨ap,ar,no,hp,hr,hm,ht⟩ := split_group_success_actual_order hash hints l depth [] root w rlc c [] s t rows h
  have he : (SplitRows.mk [] [] [],ap) = (rows,ar) := by simpa [readSplitRows] using hr
  cases he
  have hn : no = ap.hintPos := by simpa [Merkle.empty_opening_preserves_offset] using hm.symm
  have hb := (Spongefish.vec_prefix_success_exact s ap hints _ hp).1
  exact ⟨rfl,rfl,rfl,by simp [ht,hn,hb]⟩

theorem same_length_zip_keeps_firsts {α β : Type} (as : List α) (bs : List β)
    (h : as.length = bs.length) : (as.zip bs).map Prod.fst = as := by
  induction as generalizing bs with
  | nil => simp
  | cons a rest ih =>
    cases bs with
    | nil => simp at h
    | cons b tail => simp [ih tail (by simpa using h)]

theorem context_root_projection_keeps_same_bytes (p : Params) (s : PrefixState) (r : FinalRows)
    (h : ProfileShape s p) :
    ((context p s r).rowPlan.groups.map (fun group => rootBytes group.root)) =
      (WhirIntermediate.rootsToOpen s.current).map Subtype.val := by
  have hl : s.current.initialRoots.length = s.current.vectorRlc.length := h.1.1.trans h.1.2.1.symm
  unfold context groupPlans WhirIntermediate.rootsToOpen
  split
  · simp only [List.map_map,Function.comp_def,root_projection_is_lossless]
    have he := congrArg (List.map Subtype.val) (same_length_zip_keeps_firsts s.current.initialRoots s.current.vectorRlc hl)
    simpa only [List.map_map,Function.comp_def] using he
  · simp only [List.map_cons,List.map_nil,root_projection_is_lossless]

def exampleExt (n : Nat) : Bytes := Transcript.le 8 n ++ List.replicate 16 Spongefish.zeroByte
def examplePair (c0 c2 : Nat) : Bytes := exampleExt c0 ++ exampleExt c2
def exampleInitial (variables : Nat) : WhirInitial.Params :=
  ⟨3,1,0,variables,[List.replicate variables Verifier.zero]⟩
def exampleInitialSource : Bytes := List.replicate 192 Spongefish.zeroByte ++
  exampleExt 1 ++ exampleExt 0 ++ exampleExt 0 ++ examplePair 1 0
def exampleBaseGroup (first : Nat) : Bytes := Transcript.le 8 2 ++ Transcript.le 8 first ++ Transcript.le 8 0
def exampleBaseHints : Bytes := exampleBaseGroup 1 ++ exampleBaseGroup 0 ++ exampleBaseGroup 0
def exampleOpen : WhirIntermediate.OpenParams := ⟨1,0,Verifier.base 1,1,1,1,2,1⟩
def exampleSplitParams : Params := ⟨exampleOpen,1,0,Spongefish.maxCounter,Spongefish.maxCounter⟩
def exampleClaims : List Ext3 := [⟨Arithmetic.one,by decide⟩,Verifier.zero,Verifier.zero]
def exampleSplitRun : Option Result :=
  run (fun _ => Spongefish.zeroDigest) [] [] [] (exampleInitialSource ++ exampleExt 1) exampleBaseHints
    (exampleInitial 1) (List.replicate 3 Spongefish.zeroDigest) exampleClaims
    [⟨7,by decide⟩] 1 Spongefish.maxCounter [] exampleSplitParams

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Nonempty finalsplit example: three individually authenticated base groups,
one initial round, no intermediate/final rounds, nonzero final fold, exact EOF.
The constant hash is a toy function, not Keccak or a production proof fixture. -/
theorem actual_split_tail_executes_with_nonzero_final_claim :
    exampleSplitRun.map (fun r => (r.retained.current.completedRounds,r.rows.vector.length,
      r.finalSumcheck.finalRandomness.length,r.finalSumcheck.cursor.transcriptPos,r.rows.afterRows.hintPos)) =
        some (0,1,0,336,72) := by rfl

def exampleRound : WhirIntermediate.RoundParams := ⟨0,2,Spongefish.maxCounter,1,Spongefish.maxCounter⟩
def exampleSingleSource : Bytes := exampleInitialSource ++ List.replicate 32 Spongefish.zeroByte ++
  examplePair 2 0 ++ exampleExt 1 ++ exampleExt 0 ++ examplePair 2 0
def exampleSingleHints : Bytes := exampleBaseHints ++ Transcript.le 8 2 ++ exampleExt 1 ++ exampleExt 0
def exampleSingleParams : Params := ⟨exampleOpen,2,1,Spongefish.maxCounter,Spongefish.maxCounter⟩
def exampleSingleRun : Option Result :=
  run (fun _ => Spongefish.zeroDigest) [] [] [] exampleSingleSource exampleSingleHints
    (exampleInitial 3) (List.replicate 3 Spongefish.zeroDigest) exampleClaims
    [⟨7,by decide⟩] 1 Spongefish.maxCounter [(exampleOpen,exampleRound)] exampleSingleParams

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- A second ordinary toy path executes all six phases, one intermediate
round, standard Ext3 final authentication, and a nonempty final sumcheck. -/
theorem actual_single_tail_executes_all_phases :
    exampleSingleRun.map (fun r => (r.retained.current.completedRounds,r.retained.current.constraints.length,
      r.rows.vector.length,r.finalSumcheck.finalRandomness.length,
      r.finalSumcheck.cursor.transcriptPos,r.rows.afterRows.hintPos)) = some (1,2,2,1,488,128) := by rfl

end Audit.Wire3.WhirTail
