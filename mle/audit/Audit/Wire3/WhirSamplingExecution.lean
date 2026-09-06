import Audit.Wire3.WhirQuicksortCorrectness
import Audit.Wire3.WhirDedup
import Audit.Wire3.WhirTail
import Audit.Wire3.WhirConfigured

/-!
# Actual indexed sorting and compaction in the existing WHIR execution

The count=0 and numLeaves=1 returns occur FIRST and bypass sorting, in source
order. The other branch uses the existing concrete challengeRaw, the unchanged
indexed quicksort runner, and WhirDedup's actual indexed compaction. Sufficient
quicksort fuel is proved, not an additional accepted-input guard.

The distinct reference sampler remains unchanged. Its exact equality, including
the entire returned sponge/transcript/hint state and failures, is proved below.
Intermediate and Tail replacements then call this sampler and are proved equal
to the existing manual whole-run models. No external sortedness premise appears.

This closes the mathematical indexed-sort/compaction substitution boundary. It
does NOT establish Solidity/Yul/compiler/memory/uint256/gas refinement, hash or
FS independence, sampling probability, canonical config provenance, or PCS
soundness. Existing Intermediate/Tail production-profile limitations remain.
-/
namespace Audit.Wire3.WhirSamplingExecution
open Audit.Wire3
open Audit.Wire3.Spongefish (Hash Bytes Digest Ext3)
open Audit.Wire3.WhirQuicksort
open Audit.Wire3.WhirQuicksortCorrectness

def quicksortStage (xs : List Nat) : Option (List Nat) :=
  if 1 < xs.length then
    match quicksort (xs.length+1) xs 0 (xs.length-1) with
    | .error _ => none
    | .ok sorted => some sorted
  else some xs

/-- These are the source's two original-length tests. Compaction's own length
test agrees because the actual quicksort preserves that length. -/
def sortAndDedup (xs : List Nat) : Option (List Nat) := do
  let sorted ← quicksortStage xs
  if xs.length ≤ 1 then pure sorted else pure (WhirDedup.compact sorted)

theorem small_reference_identity (xs : List Nat) (h : xs.length ≤ 1) :
    WhirSampling.sortReference xs = xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys => simp only [List.length_cons] at h; omega

theorem small_dedup_identity (xs : List Nat) (h : xs.length ≤ 1) :
    WhirSampling.dedupAdjacent xs = xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys => simp only [List.length_cons] at h; omega

theorem quicksort_stage_exact (xs : List Nat) :
    quicksortStage xs = some (WhirSampling.sortReference xs) := by
  by_cases h : 1 < xs.length
  · simp only [quicksortStage,if_pos h,full_quicksort_exact_reference]
  · simp only [quicksortStage,if_neg h,small_reference_identity xs (by omega)]

theorem quicksort_stage_preserves_original_length (xs sorted : List Nat)
    (h : quicksortStage xs = some sorted) : sorted.length = xs.length := by
  rw [quicksort_stage_exact] at h
  cases h
  exact WhirSampling.sort_reference_length xs

theorem sort_and_dedup_exact (xs : List Nat) :
    sortAndDedup xs = some (WhirSampling.sortedUniqueReference xs) := by
  rw [sortAndDedup,quicksort_stage_exact]
  by_cases h : xs.length ≤ 1
  · simp only [bind,Option.bind,if_pos h,pure,WhirSampling.sortedUniqueReference,
      small_reference_identity xs h,small_dedup_identity xs h]
  · simp only [bind,Option.bind,if_neg h,pure,WhirDedup.compact_eq_adjacent_dedup,
      WhirSampling.sortedUniqueReference]

theorem sort_and_dedup_strict (xs result : List Nat) (h : sortAndDedup xs = some result) :
    WhirSampling.StrictAscending result := by
  rw [sort_and_dedup_exact] at h
  cases h
  exact WhirSampling.sorted_unique_reference_strict xs

theorem sort_and_dedup_membership (xs result : List Nat) (h : sortAndDedup xs = some result)
    (value : Nat) : value ∈ result ↔ value ∈ xs := by
  rw [sort_and_dedup_exact] at h
  cases h
  exact WhirSampling.sorted_unique_reference_membership xs value

def challengeIndices (hash : Hash) (s : Spongefish.State) (numLeaves count : Nat) :
    Option (List Nat × Spongefish.State) :=
  if count = 0 then some ([],s) else
  if numLeaves = 1 then some ([0],s) else do
    let (raw,next) ← WhirSampling.challengeRaw hash s numLeaves count
    let indices ← sortAndDedup raw
    pure (indices,next)

theorem zero_count_returns_before_domain_branch (hash : Hash) (s : Spongefish.State)
    (numLeaves : Nat) : challengeIndices hash s numLeaves 0 = some ([],s) := by
  simp [challengeIndices]

theorem singleton_domain_returns_before_raw_or_sort (hash : Hash) (s : Spongefish.State)
    (count : Nat) (hc : count ≠ 0) : challengeIndices hash s 1 count = some ([0],s) := by
  simp [challengeIndices,hc]

/-- This is equality of the full Option (indices,State), not merely equal
membership or equal cursor counts. It also covers every modeled failure. -/
theorem challenge_indices_exact_reference (hash : Hash) (s : Spongefish.State)
    (numLeaves count : Nat) :
    challengeIndices hash s numLeaves count =
      WhirSampling.challengeIndicesReference hash s numLeaves count := by
  by_cases hc : count = 0
  · simp only [challengeIndices,WhirSampling.challengeIndicesReference,WhirSampling.challengeRaw,
      if_pos hc,bind,Option.bind,pure,WhirSampling.sortedUniqueReference,
      WhirSampling.sortReference,WhirSampling.dedupAdjacent]
  · by_cases hn : numLeaves = 1
    · simp only [challengeIndices,WhirSampling.challengeIndicesReference,WhirSampling.challengeRaw,
        if_neg hc,if_pos hn,bind,Option.bind,pure,WhirSampling.sortedUniqueReference,
        WhirSampling.sortReference,WhirSampling.insertReference,WhirSampling.dedupAdjacent,
        WhirSampling.dedupFrom]
    · simp only [challengeIndices,if_neg hc,if_neg hn,WhirSampling.challengeIndicesReference]
      cases hr : WhirSampling.challengeRaw hash s numLeaves count with
      | none => rfl
      | some pair =>
          rcases pair with ⟨raw,next⟩
          simp only [bind,Option.bind,sort_and_dedup_exact,pure]

theorem successful_sampling_same_raw_cursor (hash : Hash) (s t : Spongefish.State)
    (numLeaves count : Nat) (indices : List Nat)
    (h : challengeIndices hash s numLeaves count = some (indices,t)) :
    ∃ raw, WhirSampling.challengeRaw hash s numLeaves count = some (raw,t) ∧
      indices = WhirSampling.sortedUniqueReference raw := by
  rw [challenge_indices_exact_reference,WhirSampling.challengeIndicesReference] at h
  cases hr : WhirSampling.challengeRaw hash s numLeaves count with
  | none => simp only [hr,bind,Option.bind] at h
  | some pair =>
      rcases pair with ⟨raw,next⟩
      simp only [hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨hi,ht⟩
      subst next
      exact ⟨raw,rfl,hi.symm⟩

theorem sort_and_dedup_does_not_change_raw_state (hash : Hash) (s t : Spongefish.State)
    (numLeaves count : Nat) (raw : List Nat)
    (h : WhirSampling.challengeRaw hash s numLeaves count = some (raw,t)) :
    challengeIndices hash s numLeaves count = some (WhirSampling.sortedUniqueReference raw,t) := by
  rw [challenge_indices_exact_reference,WhirSampling.challengeIndicesReference,h]
  rfl

theorem successful_sampling_properties (hash : Hash) (s t : Spongefish.State)
    (numLeaves count : Nat) (indices : List Nat) (hv : WhirSampling.ValidDomain numLeaves)
    (h : challengeIndices hash s numLeaves count = some (indices,t)) :
    indices.length ≤ count ∧ (∀ index ∈ indices, index < numLeaves) ∧
      WhirSampling.StrictAscending indices ∧ WhirSampling.NoDuplicates indices ∧
      t.sponge.digest = s.sponge.digest ∧ t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos := by
  rw [challenge_indices_exact_reference] at h
  exact WhirSampling.reference_sampling_output_properties hash s t numLeaves count indices hv h

theorem successful_sampling_counter_exact (hash : Hash) (s t : Spongefish.State)
    (numLeaves count : Nat) (indices : List Nat) (hc : count ≠ 0) (hn : numLeaves ≠ 1)
    (h : challengeIndices hash s numLeaves count = some (indices,t)) :
    t.sponge.counter = s.sponge.counter+count*WhirSampling.sizeBytes numLeaves ∧
      t.sponge.counter ≤ Spongefish.maxCounter := by
  rw [challenge_indices_exact_reference] at h
  exact WhirSampling.reference_sampling_counter_exact hash s t numLeaves count indices hc hn h

def openPrevious (hash : Hash) (hints : Bytes) (o : WhirIntermediate.OpenParams)
    (s : WhirIntermediate.State) (start : Spongefish.State) :
    Option (WhirIntermediate.Opening × Spongefish.State) := do
  let (indices,afterSampling) ← challengeIndices hash start o.codewordLength o.inDomainSamples
  let (groups,afterMerkle) ← WhirRows.openGroups hash o.merkleDepth indices (WhirIntermediate.layout s o)
    hints (WhirIntermediate.rootsToOpen s) afterSampling
  pure (⟨indices,groups⟩,afterMerkle)

theorem open_previous_exact_reference (hash : Hash) (hints : Bytes) (o : WhirIntermediate.OpenParams)
    (s : WhirIntermediate.State) (start : Spongefish.State) :
    openPrevious hash hints o s start = WhirIntermediate.openPrevious hash hints o s start := by
  simp only [openPrevious,challenge_indices_exact_reference,WhirIntermediate.openPrevious]

def runRound (hash : Hash) (source hints : Bytes) (o : WhirIntermediate.OpenParams)
    (p : WhirIntermediate.RoundParams) (s : WhirIntermediate.State) : Option WhirIntermediate.State := do
  let (message,afterPow) ← WhirIntermediate.receive hash source p (WhirIntermediate.spongeState s)
  let (opening,afterMerkle) ← openPrevious hash hints o s afterPow
  let (claims,afterRlc) ← WhirIntermediate.accumulate hash o s message opening afterMerkle
  WhirIntermediate.finish hash source o p s message opening claims afterRlc

theorem round_exact_reference (hash : Hash) (source hints : Bytes) (o : WhirIntermediate.OpenParams)
    (p : WhirIntermediate.RoundParams) (s : WhirIntermediate.State) :
    runRound hash source hints o p s = WhirIntermediate.runRound hash source hints o p s := by
  simp only [runRound,open_previous_exact_reference,WhirIntermediate.runRound]

def runRounds (hash : Hash) (source hints : Bytes) :
    List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams) →
      WhirIntermediate.State → Option WhirIntermediate.State
  | [],s => some s
  | (o,p)::rest,s => do
      let next ← runRound hash source hints o p s
      runRounds hash source hints rest next

theorem rounds_exact_reference (hash : Hash) (source hints : Bytes)
    (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams))
    (s : WhirIntermediate.State) :
    runRounds hash source hints rounds s = WhirIntermediate.runRounds hash source hints rounds s := by
  induction rounds generalizing s with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨o,p⟩
      simp only [runRounds,WhirIntermediate.runRounds,round_exact_reference]
      cases _hr : WhirIntermediate.runRound hash source hints o p s <;>
        simp only [bind,Option.bind,ih]

def runPrefix (hash : Hash) (source hints : Bytes) (initial : WhirInitial.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (count threshold : Nat)
    (start : Spongefish.State) (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams)) :
    Option WhirTail.PrefixState := do
  let origin ← WhirPrefix.run hash source initial roots expected mask count threshold start
  let current ← runRounds hash source hints rounds (WhirIntermediate.fromPrefix origin)
  pure ⟨origin,current⟩

theorem prefix_exact_reference (hash : Hash) (source hints : Bytes) (initial : WhirInitial.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (count threshold : Nat)
    (start : Spongefish.State) (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams)) :
    runPrefix hash source hints initial roots expected mask count threshold start rounds =
      WhirTail.runPrefix hash source hints initial roots expected mask count threshold start rounds := by
  simp only [runPrefix,rounds_exact_reference,WhirTail.runPrefix]

def finalRows (hash : Hash) (source hints : Bytes) (p : WhirTail.Params) (s : WhirTail.PrefixState) :
    Option WhirTail.FinalRows := do
  let (vector,afterVector) ← Spongefish.proverExt3Many hash source p.finalSize
    (WhirIntermediate.spongeState s.current)
  let afterPow ← Spongefish.verifyPow hash afterVector source p.finalPowThreshold
  let (indices,afterSampling) ← challengeIndices hash afterPow
    p.openParams.codewordLength p.openParams.inDomainSamples
  let w ← WhirIntermediate.weights s.current p.openParams
  let (opened,afterRows) ← WhirTail.openAndCheck hash hints p s indices w (vector.map Subtype.val) afterSampling
  pure ⟨vector,indices,w,opened,afterRows⟩

theorem final_rows_exact_reference (hash : Hash) (source hints : Bytes) (p : WhirTail.Params)
    (s : WhirTail.PrefixState) : finalRows hash source hints p s = WhirTail.finalRows hash source hints p s := by
  simp only [finalRows,challenge_indices_exact_reference,WhirTail.finalRows]

def runTail (hash : Hash) (source hints : Bytes) (p : WhirTail.Params) (s : WhirTail.PrefixState) :
    Option WhirTail.Result := do
  let rows ← finalRows hash source hints p s
  WhirTail.finish hash source hints p s rows

theorem tail_exact_reference (hash : Hash) (source hints : Bytes) (p : WhirTail.Params)
    (s : WhirTail.PrefixState) : runTail hash source hints p s = WhirTail.runTail hash source hints p s := by
  simp only [runTail,final_rows_exact_reference,WhirTail.runTail]

def run (hash : Hash) (protocolId sessionId instanceBytes source hints : Bytes)
    (initial : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (initialCount initialThreshold : Nat)
    (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams)) (p : WhirTail.Params) :
    Option WhirTail.Result := do
  let start := Spongefish.init hash protocolId sessionId instanceBytes
  let retained ← runPrefix hash source hints initial roots expected mask initialCount initialThreshold start rounds
  runTail hash source hints p retained

/-- Exact whole-model result equality, so all retained data, indices, terminal
states, EOF checks and failures are unchanged by replacing both sampler sites. -/
theorem whole_run_exact_reference (hash : Hash) (protocolId sessionId instanceBytes source hints : Bytes)
    (initial : WhirInitial.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (initialCount initialThreshold : Nat)
    (rounds : List (WhirIntermediate.OpenParams × WhirIntermediate.RoundParams)) (p : WhirTail.Params) :
    run hash protocolId sessionId instanceBytes source hints initial roots expected mask
        initialCount initialThreshold rounds p =
      WhirTail.run hash protocolId sessionId instanceBytes source hints initial roots expected mask
        initialCount initialThreshold rounds p := by
  simp only [run,prefix_exact_reference,tail_exact_reference,WhirTail.run]

theorem actual_sort_compaction_duplicate_example :
    sortAndDedup [1,2,3,0,1,2] = some [0,1,2,3] := rfl

/-- Toy hash exposes the byte counter. This nontrivial sampling example uses
six raw queries, actual indexed sorting, and compaction down to four rows. -/
theorem nontrivial_sampling_cursor_example :
    challengeIndices WhirSampling.exampleHash WhirSampling.exampleState 4 6 =
      some ([0,1,2,3],WhirSampling.advanceCounter WhirSampling.exampleState 6) := by
  rw [challenge_indices_exact_reference]
  exact WhirSampling.example_sorted_deduplicated_queries

theorem zero_count_precedes_singleton_example :
    challengeIndices WhirSampling.exampleHash WhirSampling.exampleState 1 0 =
      some ([],WhirSampling.exampleState) := zero_count_returns_before_domain_branch _ _ _

theorem singleton_skips_squeeze_and_sort_example :
    challengeIndices WhirSampling.exampleHash WhirSampling.exampleState 1 6 =
      some ([0],WhirSampling.exampleState) := singleton_domain_returns_before_raw_or_sort _ _ _ (by decide)

/-- The established nonzero-claim toy execution retains both sampler sites,
all six phases and exact EOF after their replacement. Hash is not Keccak. -/
theorem whole_execution_example :
    (run (fun _ => Spongefish.zeroDigest) [] [] [] WhirTail.exampleSingleSource WhirTail.exampleSingleHints
      (WhirTail.exampleInitial 3) (List.replicate 3 Spongefish.zeroDigest) WhirTail.exampleClaims
      [⟨7,by decide⟩] 1 Spongefish.maxCounter [(WhirTail.exampleOpen,WhirTail.exampleRound)]
      WhirTail.exampleSingleParams).map
        (fun r => (r.retained.current.completedRounds,r.retained.current.constraints.length,
          r.rows.vector.length,r.finalSumcheck.finalRandomness.length,
          r.finalSumcheck.cursor.transcriptPos,r.rows.afterRows.hintPos)) = some (1,2,2,1,488,128) := by
  rw [whole_run_exact_reference]
  exact WhirTail.actual_single_tail_executes_all_phases

/-- Same single checked configuration, now with actual indexed sorting at both
sampler sites. CallerProfile remains required for production correspondence. -/
def runConfigured (hash : Hash) (protocolId sessionId instanceBytes source hints : Bytes)
    (p : WhirConfigured.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes) :
    Option WhirTail.Result := do
  let forms ← WhirParameters.checkBound p roots.length expected.length mask.length
  run hash protocolId sessionId instanceBytes source hints (WhirParameters.initialParams p forms)
    roots expected mask p.initialSumcheckRounds p.initialSumcheckPowThreshold
    (WhirConfigured.phasePairs (WhirConfigured.initialOpen p) p.rounds) (WhirConfigured.finalParams p)

theorem configured_run_exact_reference (hash : Hash) (protocolId sessionId instanceBytes source hints : Bytes)
    (p : WhirConfigured.Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes) :
    runConfigured hash protocolId sessionId instanceBytes source hints p roots expected mask =
      WhirConfigured.run hash protocolId sessionId instanceBytes source hints p roots expected mask := by
  simp only [runConfigured,whole_run_exact_reference,WhirConfigured.run]

theorem configured_actual_success_derives_context_shape (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : WhirConfigured.Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result)
    (hp : WhirConfigured.CallerProfile p)
    (h : runConfigured hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    WhirFinal.contextShape (WhirTail.context (WhirConfigured.finalParams p) result.retained result.rows) = true := by
  rw [configured_run_exact_reference] at h
  exact WhirConfigured.configured_success_derives_existing_context_shape hash protocolId sessionId
    instanceBytes source hints p roots expected mask result hp h

end Audit.Wire3.WhirSamplingExecution
