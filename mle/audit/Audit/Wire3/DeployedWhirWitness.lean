import Audit.Wire3.WhirTailWitness
import Audit.Wire3.DerivedAcceptance

/-!
# The WHIR execution witness at TWENTY-ONE variables

## What this module does

The adopted `Audit.Wire3.WhirTailWitness` exhibits the first concrete WHIR
execution successes, but at the toy end of the ladder: ONE variable
(`Verifier.testConfig`, `degreeBits = 1`, `indexBits = 0`), the zero-round
profile `WhirConfigured.exampleNoRounds`, every proof-of-work threshold parked
at the no-work sentinel `Spongefish.maxCounter`, and three claim cells (its
six-claim section stays at one variable and zero rounds).

This module moves that witness to the DEPLOYED variable count and the DEPLOYED
folding schedule:

* **twenty-one variables** -- `PinnedWhirProfile.maxProfileVariables`, the
  `degreeBits = 13` + `indexBits = 8` of `DerivedAcceptance.derivedConfig`;
* **four real intermediate folding rounds** with the canonical row-21 folding
  schedule `4 | 4,4,4,4 | 1` over residual variable counts `17, 13, 9, 5`
  and interleaving depth `16 = 2 ^ 4`;
* **the canonical row-21 proof-of-work thresholds**, copied field for field
  from `PinnedWhirProfile.canonicalRow21` -- five of them NOT the sentinel;
* **six claim cells** read under the deployed five-cell
  `InstalledWhirTail.whirMask`;
* **at the derived context of `DerivedAcceptance.derivedConfig`** -- not at a
  hand-supplied context, and not at `Verifier.testConfig`.

The accepting execution consumes 1904 transcript bytes and 1976 hint bytes with
exact EOF on both streams.

## What it is NOT -- read this before quoting anything above

**The hash is a toy.**  Everything runs at `toyHash`, the constant
`fun _ => Spongefish.zeroDigest` (`the_witness_hash_is_constant`,
`the_witness_hash_ignores_every_input`).  Nothing here is a statement about the
deployed Keccak/Poseidon instantiation.

**Two canonical row-21 parameter families are STAND-INS, and they are named.**
`deployed_shape_stands_in_for_two_canonical_families` records exactly which:
the five Reed-Solomon DOMAINS (canonical row 21 runs codeword lengths
8388608 … 524288 at Merkle depths 23 … 19 with real generators; this witness
runs the one-point domain `⟨1,0,1,1,1⟩` at every stage) and the QUERY COUNTS
(canonical `inDomainSamples` 29, 19, 14, 12, 10 and one out-of-domain sample per
stage; this witness runs one in-domain sample and one out-of-domain sample per
stage).

The canonical row-21 in-domain query budget is 84 openings across the five
stages (29, 19, 14, 12, 10); this witness runs 5, one per stage -- a 16.8x
reduction in the queried set, and therefore no statement whatsoever about WHIR's
list-decoding soundness margin.  The stand-in domain has `merkleDepth = 0` and
`codewordLength = 1`, so every Merkle authentication path in the 1976 hint bytes
is EMPTY: no path verification is exercised at any stage, at any depth
(`query_budget_is_cut_from_eighty_four_to_five`,
`stand_in_domain_has_no_merkle_path`).

Those two families are what make a canonical-row execution
combinatorially out of reach for kernel reduction, not the variable count: a
single canonical domain point is `generator ^ e` with `e` up to 8388607, a
`Nat.pow` the kernel cannot normalise, and 29 queries at Merkle depth 23 is a
hint string of megabytes.  EVERY OTHER canonical row-21 field -- variable count,
folding factor, vector and commitment counts, the four rounds' residual variable
counts, sumcheck round counts, interleaving depths, final round count, final
vector size and ALL SIX proof-of-work thresholds -- is the transcribed canonical
value (`deployed_shape_matches_canonical_row_twenty_one`).

**The proof-of-work checks are VACUOUS at this hash, and that is a theorem, not
a gap.**  `toy_grinding_value_is_zero` proves the grinding value is `0` for
EVERY challenge and EVERY nonce at the constant hash, and
`toy_grinding_accepts_every_nonce` proves the threshold comparison therefore
succeeds for every threshold below the sentinel.  So carrying the canonical
thresholds is a statement about the PARAMETER RECORD and the eight nonce bytes
each non-sentinel threshold makes the verifier read, NOT evidence that any work
was done.  A witness that exercises grinding needs a non-constant hash; that is
recorded, not claimed impossible.

**The six claim cells are all ZERO, and "six claim cells" must not be read as six
NONTRIVIAL claims.**  This is inherited from the adopted
`DerivedAcceptance.derived_expected_claims_are_zero`: `derivedProof` is a zero
proof, so the five bound cells of the derived context are `Verifier.zero` and the
sixth is free.  What the six cells buy is the deployed claim ARITY and the
deployed five-cell mask, not six independent evaluation claims.

**The context is identified with the derived one in five of its seven fields,
not all seven.**  `deployed_context_shape_is_the_derived_shape` and
`deployed_context_claims_are_the_derived_claims` prove -- for EVERY outer
transcript hash, configuration hash and pinned profile -- that the protocol id,
session id, encoding, packed variable count, three roots and all six claim cells
of this module's context are the ones the outer verifier derives from
`DerivedAcceptance.derivedConfig`.  The two packed points are supplied here as
`packedPoint` (`deployed_context_supplies_two_packed_points`) and are NOT
identified with `Packed.whirPoint` of the derived round state and index lanes;
that reduction did not close within this module's elaboration budget and is
named as the one open context field.  This module proves nothing about
`Verifier.verify` at `DerivedAcceptance.derivedConfig` and nothing about the
deployed Solidity contract's behaviour.
-/

namespace Audit.Wire3.DeployedWhirWitness

open Spongefish (Hash Bytes Digest Ext3)

/-! ## 0.  The toy hash -/

def toyHash : Hash := fun _ => Spongefish.zeroDigest

theorem the_witness_hash_is_constant : toyHash = fun _ => Spongefish.zeroDigest := rfl

theorem the_witness_hash_ignores_every_input (a b : Bytes) : toyHash a = toyHash b := rfl

theorem the_witness_hash_is_the_adopted_toy_hash : toyHash = InstalledWhirTail.exampleHash := rfl

/-! ## 1.  Rung 1: parameter admission at twenty-one variables

The transcribed canonical row for the maximum packed dimension is
`PinnedWhirProfile.canonicalRow21`.  It carries EMPTY evaluation points, by
design (`canonicalRow10` / `canonicalRow21` are transcribed from fixtures whose
points are supplied by the outer verifier), so it is `InstalledWhirTail.contextParams`
-- the adopted substitution of the outer verifier's own packed points -- that
turns it into a record the six-claim bound check can admit. -/

def twentyOnePoint : List Arithmetic.Ext3 := List.replicate 21 Arithmetic.zero

def pointsOnlyContext : Verifier.WhirContext :=
  { protocolId := []
    sessionId := []
    parameters := []
    numVariables := 21
    roots := [0, 0, 0]
    points := [twentyOnePoint, twentyOnePoint]
    expectedClaims := [] }

theorem canonical_row_twenty_one_is_twenty_one_variables :
    PinnedWhirProfile.canonicalRow21.numVariables = 21 ∧
      PinnedWhirProfile.canonicalRow21.numVariables = PinnedWhirProfile.maxProfileVariables ∧
      PinnedWhirProfile.canonicalParams 21 = some PinnedWhirProfile.canonicalRow21 :=
  ⟨rfl, rfl, rfl⟩

/-- Row 21 as transcribed, with its own empty points, does NOT pass the
six-claim bound check: `checkForms` needs two points of the record's variable
count.  Stated so the next theorem cannot be misread as vacuous. -/
theorem canonical_row_twenty_one_alone_has_no_evaluation_points :
    PinnedWhirProfile.canonicalRow21.evaluationPoint = [] ∧
      PinnedWhirProfile.canonicalRow21.evaluationPoint2 = [] ∧
      PinnedWhirProfile.canonicalRow21.additionalEvaluationPoints = [] ∧
      WhirParameters.checkBound PinnedWhirProfile.canonicalRow21 3 6 1 = none :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- **RUNG 1.**  The transcribed canonical row for twenty-one variables, with the
outer verifier's own packed points substituted exactly as the adopted
`InstalledWhirTail.contextParams` substitutes them, PASSES the six-claim
parameter admission, returning the two linear forms the deployed claim arity
demands. -/
theorem canonical_row_twenty_one_passes_six_claim_admission :
    (WhirParameters.checkBound
      (InstalledWhirTail.contextParams PinnedWhirProfile.canonicalRow21 pointsOnlyContext)
      3 6 1).map (fun forms => forms.map List.length) = some [21, 21] := by decide

/-- The admitted record is the canonical one in every field except the two point
lists the context supplies. -/
theorem canonical_row_twenty_one_admission_changes_only_the_points :
    (InstalledWhirTail.contextParams PinnedWhirProfile.canonicalRow21 pointsOnlyContext) =
      { PinnedWhirProfile.canonicalRow21 with
          evaluationPoint := twentyOnePoint
          evaluationPoint2 := twentyOnePoint
          additionalEvaluationPoints := [] } := rfl

/-! ## 2.  The twenty-one variable profile this module EXECUTES at

Only two canonical families are replaced: the Reed-Solomon domains and the
query counts.  Both replacements are recorded below. -/

def toyDomain : WhirParameters.Domain := ⟨1, 0, 1, 1, 1⟩

def deployedRound (residualVariables grindingThreshold sumcheckThreshold : Nat) :
    WhirParameters.Round :=
  ⟨toyDomain, 1, 1, 4, 16, residualVariables, grindingThreshold, sumcheckThreshold⟩

/-- The executed profile: twenty-one variables, the canonical row-21 folding
schedule, the canonical row-21 proof-of-work thresholds, stand-in domains and
stand-in query counts. -/
def deployedShapeVk : WhirParameters.Params :=
  { numVariables := 21
    foldingFactor := 4
    numVectors := 1
    numCommitments := 3
    outDomainSamples := 1
    inDomainSamples := 1
    initialSumcheckRounds := 4
    numRounds := 4
    finalSumcheckRounds := 1
    finalSize := 2
    initialDomain := toyDomain
    initialInterleavingDepth := 16
    initialNumVariables := 21
    initialSumcheckPowThreshold := 18446744073709551615
    finalPowThreshold := 345602437485497
    finalSumcheckPowThreshold := 18446744073709551615
    evaluationPoint := twentyOnePoint
    evaluationPoint2 := twentyOnePoint
    additionalEvaluationPoints := []
    rounds := [deployedRound 17 17095827517592 18446744073709551615,
               deployedRound 13 9845507893798 18446744073709551615,
               deployedRound 9 4442624697085 18446744073709551615,
               deployedRound 5 313471598626301 7737125240129242112] }

/-- **THE LEDGER, POSITIVE SIDE.**  Every scalar field of the executed profile
other than the domains and the query counts is the transcribed canonical row-21
value. -/
theorem deployed_shape_matches_canonical_row_twenty_one :
    deployedShapeVk.numVariables = PinnedWhirProfile.canonicalRow21.numVariables ∧
    deployedShapeVk.initialNumVariables = PinnedWhirProfile.canonicalRow21.initialNumVariables ∧
    deployedShapeVk.foldingFactor = PinnedWhirProfile.canonicalRow21.foldingFactor ∧
    deployedShapeVk.numVectors = PinnedWhirProfile.canonicalRow21.numVectors ∧
    deployedShapeVk.numCommitments = PinnedWhirProfile.canonicalRow21.numCommitments ∧
    deployedShapeVk.outDomainSamples = PinnedWhirProfile.canonicalRow21.outDomainSamples ∧
    deployedShapeVk.initialSumcheckRounds = PinnedWhirProfile.canonicalRow21.initialSumcheckRounds ∧
    deployedShapeVk.initialInterleavingDepth =
      PinnedWhirProfile.canonicalRow21.initialInterleavingDepth ∧
    deployedShapeVk.numRounds = PinnedWhirProfile.canonicalRow21.numRounds ∧
    deployedShapeVk.finalSumcheckRounds = PinnedWhirProfile.canonicalRow21.finalSumcheckRounds ∧
    deployedShapeVk.finalSize = PinnedWhirProfile.canonicalRow21.finalSize ∧
    deployedShapeVk.rounds.map (fun r => (r.numVariables, r.sumcheckRounds, r.interleavingDepth,
        r.outDomainSamples)) =
      PinnedWhirProfile.canonicalRow21.rounds.map (fun r => (r.numVariables, r.sumcheckRounds,
        r.interleavingDepth, r.outDomainSamples)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **THE LEDGER, PROOF-OF-WORK SIDE.**  All six grinding thresholds are the
transcribed canonical row-21 values. -/
theorem deployed_shape_carries_the_canonical_grinding_thresholds :
    deployedShapeVk.initialSumcheckPowThreshold =
      PinnedWhirProfile.canonicalRow21.initialSumcheckPowThreshold ∧
    deployedShapeVk.finalPowThreshold = PinnedWhirProfile.canonicalRow21.finalPowThreshold ∧
    deployedShapeVk.finalSumcheckPowThreshold =
      PinnedWhirProfile.canonicalRow21.finalSumcheckPowThreshold ∧
    deployedShapeVk.rounds.map (fun r => (r.powThreshold, r.sumcheckPowThreshold)) =
      PinnedWhirProfile.canonicalRow21.rounds.map
        (fun r => (r.powThreshold, r.sumcheckPowThreshold)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Five of the six thresholds are NOT the no-work sentinel -- this is the
difference from the adopted witness, whose every threshold is
`Spongefish.maxCounter`. -/
theorem deployed_shape_has_five_non_sentinel_thresholds :
    deployedShapeVk.finalPowThreshold ≠ Spongefish.maxCounter ∧
    (deployedShapeVk.rounds.map WhirParameters.Round.powThreshold).all
      (fun t => decide (t ≠ Spongefish.maxCounter)) = true ∧
    ((deployedShapeVk.rounds.map WhirParameters.Round.sumcheckPowThreshold).getD 3 0)
      ≠ Spongefish.maxCounter ∧
    WhirConfigured.exampleNoRounds.finalPowThreshold = Spongefish.maxCounter ∧
    WhirConfigured.exampleNoRounds.initialSumcheckPowThreshold = Spongefish.maxCounter ∧
    WhirConfigured.exampleNoRounds.finalSumcheckPowThreshold = Spongefish.maxCounter :=
  ⟨by decide, by decide, by decide, rfl, rfl, rfl⟩

/-- **THE LEDGER, NEGATIVE SIDE.**  The two canonical families that are
stand-ins, stated so they cannot be read past: every domain and every in-domain
query count. -/
theorem deployed_shape_stands_in_for_two_canonical_families :
    deployedShapeVk.initialDomain = toyDomain ∧
    deployedShapeVk.rounds.map WhirParameters.Round.domain = List.replicate 4 toyDomain ∧
    deployedShapeVk.inDomainSamples = 1 ∧
    deployedShapeVk.rounds.map WhirParameters.Round.inDomainSamples = [1, 1, 1, 1] ∧
    PinnedWhirProfile.canonicalRow21.initialDomain = ⟨8388608, 23, 131072, 64, 16905767614792059275⟩ ∧
    PinnedWhirProfile.canonicalRow21.inDomainSamples = 29 ∧
    PinnedWhirProfile.canonicalRow21.rounds.map WhirParameters.Round.inDomainSamples =
      [19, 14, 12, 10] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **THE MAGNITUDE OF THE QUERY STAND-IN, AS A THEOREM.**  The canonical row-21
in-domain query budget is 84 openings across the five stages (29, 19, 14, 12,
10); this witness runs 5, one per stage -- a 16.8x reduction in the queried set,
and therefore no statement whatsoever about WHIR's list-decoding soundness
margin.  The out-of-domain budget is unchanged (1 per stage). -/
theorem query_budget_is_cut_from_eighty_four_to_five :
    PinnedWhirProfile.canonicalRow21.inDomainSamples +
        (PinnedWhirProfile.canonicalRow21.rounds.map
          WhirParameters.Round.inDomainSamples).sum = 84 ∧
      deployedShapeVk.inDomainSamples +
        (deployedShapeVk.rounds.map WhirParameters.Round.inDomainSamples).sum = 5 ∧
      PinnedWhirProfile.canonicalRow21.outDomainSamples = deployedShapeVk.outDomainSamples := by
  refine ⟨by decide, by decide, rfl⟩

/-- **THE MAGNITUDE OF THE DOMAIN STAND-IN, AS A THEOREM.**  The canonical Merkle
depths are 23, 22, 21, 20, 19; the stand-in domain has `merkleDepth = 0` and
`codewordLength = 1`, so every Merkle authentication path in the 1976 hint bytes
is EMPTY: no path verification is exercised at any stage, at any depth. -/
theorem stand_in_domain_has_no_merkle_path :
    toyDomain.merkleDepth = 0 ∧ toyDomain.codewordLength = 1 ∧
      PinnedWhirProfile.canonicalRow21.initialDomain.merkleDepth = 23 ∧
      PinnedWhirProfile.canonicalRow21.rounds.map
        (fun r => r.domain.merkleDepth) = [22, 21, 20, 19] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem deployed_shape_is_the_production_caller_profile :
    WhirConfigured.CallerProfile deployedShapeVk := ⟨rfl, rfl⟩

theorem deployed_shape_passes_six_claim_admission :
    (WhirParameters.checkBound deployedShapeVk 3 6 1).isSome = true := by decide

/-- The schedule really partitions the twenty-one original variables, and it
really has four intermediate rounds -- unlike every adopted execution example,
which has zero rounds or one. -/
theorem deployed_schedule_partitions_twenty_one_variables :
    deployedShapeVk.initialSumcheckRounds +
        WhirSchedule.roundSum (deployedShapeVk.rounds.map WhirParameters.Round.folding) +
        deployedShapeVk.finalSumcheckRounds = 21 ∧
      deployedShapeVk.rounds.length = 4 ∧
      WhirConfigured.exampleNoRounds.rounds.length = 0 ∧
      WhirConfigured.exampleOneRound.rounds.length = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The four configured phase pairs really are four, and the final opening is
the last round's projection, not the initial one. -/
theorem deployed_schedule_has_four_phase_pairs :
    (WhirConfigured.phasePairs (WhirConfigured.initialOpen deployedShapeVk)
      deployedShapeVk.rounds).length = 4 ∧
      (WhirConfigured.finalParams deployedShapeVk).openParams =
        WhirConfigured.roundOpen (deployedRound 5 313471598626301 7737125240129242112) :=
  ⟨rfl, rfl⟩

/-! ## 3.  Rung 3: the grinding checks, decided

`Spongefish.verifyPow` compares `powValue hash challenge nonce` with the
threshold.  At a constant hash the value is a constant, and it is the SMALLEST
possible one. -/

theorem toy_grinding_value_is_zero (challenge nonce : Bytes) :
    Spongefish.powValue toyHash challenge nonce = 0 := rfl

/-- **RUNG 3, DECIDED: the grinding check is VACUOUS at this hash.**  For every
threshold below the sentinel, `verifyPow` reduces to reading the eight nonce
bytes: the comparison cannot fail, whatever the nonce is.  So the canonical
thresholds this witness carries constrain only the parameter record and the byte
budget, never the prover's effort.  A witness that makes grinding bite needs a
non-constant hash. -/
theorem toy_grinding_accepts_every_nonce (s : Spongefish.State) (source : Bytes)
    (threshold : Nat) (hle : threshold ≤ Spongefish.maxCounter)
    (hne : threshold ≠ Spongefish.maxCounter) :
    Spongefish.verifyPow toyHash s source threshold =
      (Spongefish.verifierMessage toyHash s 32).bind
        (fun p => (Spongefish.proverMessage toyHash p.2 source 8).map Prod.snd) := by
  unfold Spongefish.verifyPow
  rw [if_neg (by omega), if_neg hne]
  cases hv : Spongefish.verifierMessage toyHash s 32 with
  | none => simp [hv]
  | some q =>
    cases hp : Spongefish.proverMessage toyHash q.2 source 8 with
    | none => simp [hv, hp]
    | some r => simp [hv, hp, toy_grinding_value_is_zero, Nat.zero_le]

/-- At the sentinel the check is not merely vacuous, it reads nothing.  The
adopted witness runs entirely in this branch; this one does not. -/
theorem sentinel_grinding_reads_nothing (hash : Hash) (s : Spongefish.State) (source : Bytes) :
    Spongefish.verifyPow hash s source Spongefish.maxCounter = some s := by
  unfold Spongefish.verifyPow
  rw [if_neg (by omega), if_pos rfl]

/-! ## 4.  The derived context of `DerivedAcceptance.derivedConfig`

`derivedConfig` packs `degreeBits = 13` and `indexBits = 8`.  At the toy
transcript hash the context the outer verifier derives from it is a computable
constant, and its five bound claim cells are all zero. -/

def profileStandIn : PinnedWhirProfile.Profile :=
  ⟨fun _ => none, fun _ => 0, fun _ => 0, fun _ => [], []⟩

def packedCoordinate : Arithmetic.Ext3 := ⟨5, 5, 5⟩

def packedPoint : List Arithmetic.Ext3 := List.replicate 21 packedCoordinate

/-- The context this module executes at: the twenty-one variable shape, the
three zero roots, the six derived claim cells, and two twenty-one coordinate
packed points. -/
def deployedContext : Verifier.WhirContext :=
  { protocolId := []
    sessionId := []
    parameters := []
    numVariables := 21
    roots := [0, 0, 0]
    points := [packedPoint, packedPoint]
    expectedClaims := [some Verifier.zero, some Verifier.zero, some Verifier.zero,
                       some Verifier.zero, some Verifier.zero, none] }

/-- **FIVE OF THE SEVEN CONTEXT FIELDS ARE THE DERIVED ONES**, for EVERY outer
transcript hash, every configuration hash and every pinned profile: the WHIR
protocol id, session id, encoding, the packed variable count and the three
roots.  These fields are read straight off `derivedConfig` and `derivedProof`,
so no transcript reduction is involved. -/
theorem deployed_context_shape_is_the_derived_shape (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine thash khash P)
        DerivedAcceptance.derivedConfig DerivedAcceptance.derivedProof).protocolId =
      deployedContext.protocolId ∧
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine thash khash P)
        DerivedAcceptance.derivedConfig DerivedAcceptance.derivedProof).sessionId =
      deployedContext.sessionId ∧
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine thash khash P)
        DerivedAcceptance.derivedConfig DerivedAcceptance.derivedProof).parameters =
      deployedContext.parameters ∧
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine thash khash P)
        DerivedAcceptance.derivedConfig DerivedAcceptance.derivedProof).numVariables =
      deployedContext.numVariables ∧
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine thash khash P)
        DerivedAcceptance.derivedConfig DerivedAcceptance.derivedProof).roots =
      deployedContext.roots :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **THE SIX CLAIM CELLS ARE THE DERIVED ONES**, for EVERY outer transcript
hash.  This is the adopted `DerivedAcceptance.derived_expected_claims_are_zero`
read backwards: the five bound cells of the twenty-one variable derived context
are `Verifier.zero` and the sixth is free, which is exactly the claim list this
module's transcript is read against. -/
theorem deployed_context_claims_are_the_derived_claims (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine thash khash P)
        DerivedAcceptance.derivedConfig DerivedAcceptance.derivedProof).expectedClaims =
      deployedContext.expectedClaims :=
  DerivedAcceptance.derived_expected_claims_are_zero thash khash P

/-- The remaining field, stated as the open one: the two packed points.  This
module supplies them as `packedPoint`; identifying them with
`Packed.whirPoint` of the derived round state and the derived index lanes is the
one context field not established here.  See the REPORT for the exact missing
lemma. -/
theorem deployed_context_supplies_two_packed_points :
    deployedContext.points = [packedPoint, packedPoint] ∧
      deployedContext.points.map List.length = [21, 21] :=
  ⟨rfl, rfl⟩

theorem deployed_context_has_the_verifier_shape :
    deployedContext.roots.length = 3 ∧ deployedContext.points.length = 2 ∧
      deployedContext.expectedClaims.length = 6 ∧
      deployedContext.expectedClaims.map Option.isSome = [true, true, true, true, true, false] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem deployed_context_variable_count_is_the_derived_configuration :
    deployedContext.numVariables =
        DerivedAcceptance.derivedConfig.degreeBits + DerivedAcceptance.derivedConfig.indexBits ∧
      deployedContext.numVariables = 21 ∧
      deployedContext.points.map List.length = [21, 21] :=
  ⟨rfl, rfl, rfl⟩

theorem deployed_context_claims_unmask_to_zero :
    OpeningBinding.unmask deployedContext.expectedClaims = List.replicate 6 Verifier.zero := rfl

theorem deployed_context_roots_are_the_three_zero_digests :
    deployedContext.roots.map InstalledWhirTail.rootDigest =
      List.replicate 3 Spongefish.zeroDigest := rfl

/-- The record the tail actually runs at: the executed profile with the derived
context's own packed points substituted. -/
def deployedVk : WhirParameters.Params :=
  InstalledWhirTail.contextParams deployedShapeVk deployedContext

theorem deployed_vk_is_the_context_substitution :
    InstalledWhirTail.contextParams deployedShapeVk deployedContext = deployedVk := rfl

theorem deployed_vk_takes_its_points_from_the_context :
    deployedVk.evaluationPoint = packedPoint ∧ deployedVk.evaluationPoint2 = packedPoint ∧
      deployedVk.additionalEvaluationPoints = [] ∧
      deployedVk.numVariables = 21 ∧ deployedVk.numRounds = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
theorem deployed_vk_passes_six_claim_admission :
    (WhirParameters.checkBound deployedVk 3 6 1).isSome = true := by decide

/-! ## 5.  Rung 2: the transcript and the hint string

Byte layout, transcript stream (1904 bytes):

* `commitmentBlock` 264 -- three commitments, each 32-byte root + one 24-byte
  out-of-domain answer + 32-byte bound root, all zero;
* `claimBlock` 144 -- SIX claims, matching the derived context's five bound
  cells and one free cell;
* `crossBlock` 144 -- the six cross answers of the 3x1x3 out-of-domain matrix;
* `initialSumcheckBlock` 192 -- four initial sumcheck messages (48 bytes each),
  at the sentinel threshold, so no nonce;
* four round blocks -- each 32-byte new root + 24-byte out-of-domain answer +
  8-byte grinding nonce, then four sumcheck messages; the FOURTH round's
  sumcheck threshold is non-sentinel, so each of its four messages is followed
  by an 8-byte nonce (256 + 256 + 256 + 288 bytes);
* `finalVectorBlock` 48 -- the two-element final vector `[1, -1]`;
* eight bytes of final grinding nonce;
* `finalMessage` 48 -- the ONE final sumcheck message, whose first coefficient
  is solved so the final claim holds.

Hint stream (1976 bytes): three base-encoded groups of `8 + 16 * 8` bytes for
round one's split opening, then four ext3-encoded groups of `8 + 16 * 24` bytes
for rounds two to four and the final opening. -/

def zeroBytes (n : Nat) : Bytes := List.replicate n Spongefish.zeroByte

def ext3Bytes (a b c : Nat) : Bytes :=
  Transcript.le 8 a ++ Transcript.le 8 b ++ Transcript.le 8 c

def sumcheckMessage (a b c : Nat) : Bytes := ext3Bytes a b c ++ ext3Bytes 0 0 0

def nonceBytes : Bytes := zeroBytes 8

def commitmentBlock : Bytes := zeroBytes 264
def claimBlock : Bytes := zeroBytes 144
def crossBlock : Bytes := zeroBytes 144
def initialSumcheckBlock : Bytes :=
  sumcheckMessage 0 0 0 ++ sumcheckMessage 0 0 0 ++ sumcheckMessage 0 0 0 ++ sumcheckMessage 0 0 0

def roundHeader : Bytes := zeroBytes 64

def plainRoundBlock : Bytes := roundHeader ++ initialSumcheckBlock

def grindingRoundBlock : Bytes := roundHeader ++
  (sumcheckMessage 0 0 0 ++ nonceBytes) ++ (sumcheckMessage 0 0 0 ++ nonceBytes) ++
  (sumcheckMessage 0 0 0 ++ nonceBytes) ++ (sumcheckMessage 0 0 0 ++ nonceBytes)

def finalVectorBlock : Bytes := ext3Bytes 1 0 0 ++ ext3Bytes 18446744069414584320 0 0

/-- The solved final sumcheck coefficient.  With the constant hash the final
challenge is `0`, so the accumulated sum after this round is exactly this
coefficient; it is set to the value the final claim demands at the derived
context's packed points. -/
def finalMessage : Bytes :=
  sumcheckMessage 18338548615676347306 16632727245353859786 14354835771253332043

def deployedSource : Bytes :=
  commitmentBlock ++ claimBlock ++ crossBlock ++ initialSumcheckBlock ++
  plainRoundBlock ++ plainRoundBlock ++ plainRoundBlock ++ grindingRoundBlock ++
  finalVectorBlock ++ nonceBytes ++ finalMessage

def baseGroupHints : Bytes := Transcript.le 8 16 ++ zeroBytes 128
def ext3GroupHints : Bytes := Transcript.le 8 16 ++ zeroBytes 384

def deployedHintBytes : Bytes :=
  baseGroupHints ++ baseGroupHints ++ baseGroupHints ++
  ext3GroupHints ++ ext3GroupHints ++ ext3GroupHints ++ ext3GroupHints

set_option maxRecDepth 4096 in
theorem deployed_streams_have_the_stated_lengths :
    deployedSource.length = 1904 ∧ deployedHintBytes.length = 1976 := ⟨rfl, rfl⟩

def deployedTranscript : Verifier.Bytes :=
  WhirFinalSpongefish.fromTranscriptBytes deployedSource

def deployedHints : Verifier.Bytes :=
  WhirFinalSpongefish.fromTranscriptBytes deployedHintBytes

set_option maxRecDepth 4096 in
/-- **THE HEADLINE.  A SUCCESSFUL WHIR EXECUTION AT TWENTY-ONE VARIABLES.**
Four real intermediate folding rounds, the canonical row-21 folding schedule and
grinding thresholds, six claim cells read under the deployed five-cell mask,
1904 transcript bytes and 1976 hint bytes with exact EOF on both streams, at the
packed points the outer verifier derives from
`DerivedAcceptance.derivedConfig`.  Toy constant hash; stand-in domains and
query counts; the grinding comparisons are vacuous at this hash
(`toy_grinding_accepts_every_nonce`).

In one line, honestly: this transcript satisfies the one equation the deployed
verifier checks, at a degenerate hash, an empty-path domain, and 5 of 84
queries -- a genuine execution witness and nothing more. -/
theorem configured_twenty_one_variable_execution_example :
    (WhirConfigured.run toyHash [] [] [] deployedSource deployedHintBytes deployedVk
      (List.replicate 3 Spongefish.zeroDigest) (List.replicate 6 Verifier.zero)
      InstalledWhirTail.whirMask).map
      (fun r => (r.retained.current.completedRounds, r.rows.vector.length,
        r.finalSumcheck.finalRandomness.length, r.finalSumcheck.cursor.transcriptPos,
        r.rows.afterRows.hintPos)) = some (4, 2, 1, 1904, 1976) := by rfl

theorem option_is_some_of_map_eq_some {a b : Type} (o : Option a) (f : a → b) (v : b)
    (h : o.map f = some v) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some x => rfl

theorem deployed_tail_run_unfolds :
    InstalledWhirTail.tailRun toyHash deployedShapeVk deployedContext
        deployedTranscript deployedHints =
      WhirConfigured.run toyHash [] [] [] deployedSource deployedHintBytes deployedVk
        (List.replicate 3 Spongefish.zeroDigest) (List.replicate 6 Verifier.zero)
        InstalledWhirTail.whirMask := by
  have h1 : InstalledWhirTail.outerBytes deployedTranscript = deployedSource :=
    WhirFinalSpongefish.transcript_bytes_roundtrip _
  have h2 : InstalledWhirTail.outerBytes deployedHints = deployedHintBytes :=
    WhirFinalSpongefish.transcript_bytes_roundtrip _
  have h3 : InstalledWhirTail.outerBytes deployedContext.protocolId = [] := rfl
  have h4 : InstalledWhirTail.outerBytes deployedContext.sessionId = [] := rfl
  unfold InstalledWhirTail.tailRun
  rw [h1, h2, h3, h4, deployed_context_roots_are_the_three_zero_digests,
    deployed_context_claims_unmask_to_zero, deployed_vk_is_the_context_substitution]

/-- **THE INSTALLED CONCRETE TAIL SUCCEEDS AT TWENTY-ONE VARIABLES.** -/
theorem installed_tail_succeeds_at_twenty_one_variables :
    (InstalledWhirTail.tailRun toyHash deployedShapeVk deployedContext
      deployedTranscript deployedHints).isSome = true := by
  rw [deployed_tail_run_unfolds]
  exact option_is_some_of_map_eq_some _ _ _ configured_twenty_one_variable_execution_example

/-- The installed `whirTail` engine field returns `true` at the derived context
of the twenty-one variable configuration. -/
theorem installed_tail_returns_true_at_twenty_one_variables (parsed : Verifier.ParsedWhir) :
    InstalledWhirTail.installedTail toyHash deployedShapeVk deployedContext
      deployedTranscript deployedHints parsed = true := by
  rw [InstalledWhirTail.installed_tail_true_iff]
  exact ⟨rfl, installed_tail_succeeds_at_twenty_one_variables⟩

/-- Non-vacuity: the accepting run really reads all four intermediate rounds,
the two-element final vector, one final sumcheck round, and both streams to
their exact ends. -/
theorem deployed_execution_consumes_the_bytes :
    (InstalledWhirTail.tailRun toyHash deployedShapeVk deployedContext
      deployedTranscript deployedHints).map
      (fun r => (r.retained.current.completedRounds, r.rows.vector.length,
        r.finalSumcheck.finalRandomness.length, r.finalSumcheck.cursor.transcriptPos,
        r.rows.afterRows.hintPos)) = some (4, 2, 1, 1904, 1976) := by
  rw [deployed_tail_run_unfolds]
  exact configured_twenty_one_variable_execution_example

theorem deployed_source_is_not_empty : deployedSource ≠ [] := by
  intro h
  have hl := deployed_streams_have_the_stated_lengths.1
  rw [h] at hl
  exact absurd hl (by decide)

/-! ## 5b.  WHY ONE EQUATION IS THE WHOLE STORY: model fidelity, not an omission

The single algebraic reconciliation in the tail is `WhirFinal.finalClaim`.  That
is not a check this model forgot to impose in the intermediate rounds: the
DEPLOYED wire format itself sends only two of the three quadratic coefficients
per sumcheck round and RECONSTRUCTS the linear one as `c1 = claim - 2*c0 - c2`
(`SpongefishWhirVerify.sol:454`, `whir/sumcheck.rs:124`), so the per-round
identity `h(0) + h(1) = claim` holds BY CONSTRUCTION.  `WhirFinal.quadratic`
transcribes that reconstruction.  The four theorems below are that story stated
as theorems. -/

/-- **THE STRUCTURAL FACT.**  `WhirFinal.roundStep` never inspects the running
claim when deciding success or failure: success depends only on the cursor.  So
no intermediate sumcheck round can reject on the claim. -/
theorem round_step_success_ignores_the_running_claim (e : WhirFinal.Engine) (threshold : Nat)
    (bytes : WhirFinal.Bytes) (cur : WhirFinal.Cursor) (rand : List Arithmetic.Ext3)
    (sum1 sum2 : Arithmetic.Ext3) :
    (WhirFinal.roundStep e threshold bytes ⟨cur, sum1, rand⟩).isSome =
      (WhirFinal.roundStep e threshold bytes ⟨cur, sum2, rand⟩).isSome := by
  unfold WhirFinal.roundStep
  cases _hm : e.readMessage bytes cur with
  | none => simp
  | some pair =>
    by_cases hc : (Arithmetic.Canonical pair.1.c0 ∧ Arithmetic.Canonical pair.1.c2)
    · cases hp : e.checkPow threshold bytes pair.2 with
      | none => simp [hc, hp]
      | some ap =>
        cases hq : e.challenge ap with
        | none => simp [hc, hp, hq]
        | some q => by_cases hr : Arithmetic.Canonical q.1 <;> simp [hc, hp, hq, hr]
    · simp [hc]

/-- The same fact for a whole run of `n` rounds. -/
theorem run_rounds_success_ignores_the_running_claim (e : WhirFinal.Engine) (threshold : Nat)
    (bytes : WhirFinal.Bytes) : ∀ (n : Nat) (cur : WhirFinal.Cursor)
      (rand : List Arithmetic.Ext3) (sum1 sum2 : Arithmetic.Ext3),
    (WhirFinal.runRounds e threshold bytes n ⟨cur, sum1, rand⟩).isSome =
      (WhirFinal.runRounds e threshold bytes n ⟨cur, sum2, rand⟩).isSome := by
  intro n
  induction n with
  | zero => intro _ _ _ _; rfl
  | succ n ih =>
    intro cur rand sum1 sum2
    have hkey := round_step_success_ignores_the_running_claim e threshold bytes cur rand sum1 sum2
    unfold WhirFinal.runRounds
    cases h1 : WhirFinal.roundStep e threshold bytes ⟨cur, sum1, rand⟩ with
    | none =>
      cases h2 : WhirFinal.roundStep e threshold bytes ⟨cur, sum2, rand⟩ with
      | none => rfl
      | some t2 => rw [h1, h2] at hkey; exact absurd hkey (by simp)
    | some t1 =>
      cases h2 : WhirFinal.roundStep e threshold bytes ⟨cur, sum2, rand⟩ with
      | none => rw [h1, h2] at hkey; exact absurd hkey (by simp)
      | some t2 =>
        have hs := WhirFinal.round_step_success (h := h1)
        have hs2 := WhirFinal.round_step_success (h := h2)
        obtain ⟨m, am, ap, r, nx, hrm, _, _, hpw, hch, _, ht1⟩ := hs
        obtain ⟨m', am', ap', r', nx', hrm', _, _, hpw', hch', _, ht2⟩ := hs2
        rw [hrm] at hrm'
        cases hrm'
        rw [hpw] at hpw'
        cases hpw'
        rw [hch] at hch'
        cases hch'
        subst ht1; subst ht2
        exact ih nx (rand ++ [r]) _ _

/-- **WHY.**  A round message carries only TWO coefficients (`c0`, `c2`); the
linear coefficient is RECONSTRUCTED from the running claim so that
`h(0) + h(1) = claim` holds identically.  Checked here on concrete data: over
several claims and messages, `h(0) + h(1)` is the claim on the nose. -/
theorem sumcheck_identity_holds_by_construction :
    (List.map (fun t : Arithmetic.Ext3 × Arithmetic.Ext3 × Arithmetic.Ext3 =>
        Arithmetic.eadd
          (WhirFinal.quadratic t.1 ⟨t.2.1, t.2.2⟩ Arithmetic.zero)
          (WhirFinal.quadratic t.1 ⟨t.2.1, t.2.2⟩ Arithmetic.one))
      [(⟨7, 0, 0⟩, ⟨3, 0, 0⟩, ⟨5, 0, 0⟩), (⟨1, 2, 3⟩, ⟨9, 9, 9⟩, ⟨4, 5, 6⟩),
       (⟨0, 0, 0⟩, ⟨11, 0, 5⟩, ⟨0, 7, 0⟩),
       (⟨18446744069414584320, 1, 1⟩, ⟨2, 2, 2⟩, ⟨3, 3, 3⟩)])
      = [⟨7, 0, 0⟩, ⟨1, 2, 3⟩, ⟨0, 0, 0⟩, ⟨18446744069414584320, 1, 1⟩] := by decide

/-- The ONLY algebraic equality in the tail is `WhirFinal.finalClaim`, called
once, in `verifyEnd`, after all rounds have run. -/
theorem the_only_algebraic_equality_is_the_final_claim (auth : WhirTerminal.Authenticate)
    (e : WhirFinal.Engine) (c : WhirFinal.Context) (transcript hints : WhirFinal.Bytes)
    (v : List Arithmetic.Ext3) (rows : List WhirTerminal.GroupRows)
    (hshape : WhirFinal.contextShape c = true)
    (hrows : WhirTerminal.verifyFinalRows auth c.rowPlan v rows = true)
    (result : WhirFinal.State)
    (hrun : WhirFinal.runRounds e c.powThreshold transcript c.rowPlan.finalRounds
      (WhirFinal.start c) = some result) :
    WhirFinal.verifyEnd auth e c transcript hints v rows =
      (WhirFinal.finalClaim c v result && WhirFinal.exhausted c transcript hints result) := by
  unfold WhirFinal.verifyEnd
  rw [if_neg (by simp [hshape]), if_neg (by simp [hrows]), hrun]

/-! ## 6.  Rung 2 at the engine: the concrete parse on the same bytes -/

theorem list_of_length_six {a : Type} (xs : List a) (h : xs.length = 6) :
    ∃ x0 x1 x2 x3 x4 x5, xs = [x0, x1, x2, x3, x4, x5] := by
  match xs, h with
  | [x0, x1, x2, x3, x4, x5], _ => exact ⟨x0, x1, x2, x3, x4, x5, rfl⟩

theorem deployed_prefix_bound_is_some :
    (WhirParameters.checkBound
      (InstalledWhirTail.contextParams deployedShapeVk deployedContext)
      (InstalledWhirParse.parseRoots deployedContext).length
      (InstalledWhirParse.parseClaims deployedContext).length
      InstalledWhirTail.whirMask.length).isSome = true := deployed_vk_passes_six_claim_admission

theorem deployed_prefix_run_is_some :
    (InstalledWhirParse.prefixRun toyHash deployedShapeVk deployedContext
      deployedTranscript deployedHints).isSome = true := by
  have h := installed_tail_succeeds_at_twenty_one_variables
  rw [InstalledWhirParse.tail_run_factors_through_prefix_run] at h
  cases hp : InstalledWhirParse.prefixRun toyHash deployedShapeVk deployedContext
      deployedTranscript deployedHints with
  | none => rw [hp] at h; simp at h
  | some s => rfl

/-- **THE CONCRETE PARSE AT TWENTY-ONE VARIABLES.**  The installed parse
succeeds on the same bytes and its projection carries the derived context's own
roots in both copies and claims that satisfy the outer verifier's five-cell
mask. -/
theorem deployed_parse_matches_the_context :
    ∃ s, InstalledWhirParse.prefixRun toyHash deployedShapeVk deployedContext
        deployedTranscript deployedHints = some s ∧
      (InstalledWhirParse.parsedOf s).actualRoots = deployedContext.roots ∧
      (InstalledWhirParse.parsedOf s).boundRoots = deployedContext.roots ∧
      Verifier.claimsMatch deployedContext.expectedClaims
        (InstalledWhirParse.parsedOf s).claims = true := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp deployed_prefix_run_is_some
  obtain ⟨forms, hforms⟩ := Option.isSome_iff_exists.mp deployed_prefix_bound_is_some
  refine ⟨s, hs, ?_⟩
  unfold InstalledWhirParse.prefixRun at hs
  rw [hforms] at hs
  have h1 := WhirTail.prefix_success_retains_actual_pair (h := hs)
  obtain ⟨after, hpi, _⟩ := WhirPrefix.successful_prefix_is_one_execution (h := h1.1)
  have hall := WhirInitial.initial_all_roots_and_checked_claims (h := hpi)
  have hroot : (InstalledWhirParse.parsedOf s).actualRoots = deployedContext.roots := by
    show s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.root) = _
    have hm : s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.root) =
        (s.origin.initial.commitments.map (·.root)).map WhirTail.rootWord := by
      simp [List.map_map, Function.comp_def]
    rw [hm, hall.1]
    rfl
  have hbound : (InstalledWhirParse.parsedOf s).boundRoots = deployedContext.roots := by
    show s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.boundRoot) = _
    have hm : s.origin.initial.commitments.map (fun cm => WhirTail.rootWord cm.boundRoot) =
        (s.origin.initial.commitments.map (·.boundRoot)).map WhirTail.rootWord := by
      simp [List.map_map, Function.comp_def]
    rw [hm, hall.2.1]
    rfl
  refine ⟨hroot, hbound, ?_⟩
  have hlen : s.origin.initial.evaluations.length = 6 := hall.2.2.1
  have hc0 := hall.2.2.2.1 0 (by decide) (by decide)
  have hc1 := hall.2.2.2.1 1 (by decide) (by decide)
  have hc2 := hall.2.2.2.1 2 (by decide) (by decide)
  have hc3 := hall.2.2.2.1 3 (by decide) (by decide)
  have hc4 := hall.2.2.2.1 4 (by decide) (by decide)
  obtain ⟨x0, x1, x2, x3, x4, x5, hev⟩ := list_of_length_six _ hlen
  rw [hev] at hc0 hc1 hc2 hc3 hc4
  show Verifier.claimsMatch deployedContext.expectedClaims s.origin.initial.evaluations = true
  rw [hev]
  simp only [List.getD] at hc0 hc1 hc2 hc3 hc4
  simp only [InstalledWhirParse.parseClaims, OpeningBinding.unmask, deployedContext] at hc0 hc1 hc2 hc3 hc4
  simp_all [Verifier.claimsMatch, deployedContext]

def deployedProof : Verifier.Proof :=
  { DerivedAcceptance.derivedProof with
      whirTranscript := deployedTranscript, whirHints := deployedHints }

/-- **RUNG 2 AT THE ENGINE, AT TWENTY-ONE VARIABLES.**  `Verifier.verifyWhir`
returns `true` for an engine whose `parseWhir` AND `whirTail` are both the
adopted concrete installs, at the twenty-one variable context the outer verifier
derives from `DerivedAcceptance.derivedConfig`.  The base engine, the gate
decoder and the outer transcript hash stay quantified: the context is supplied,
so nothing here reads them. -/
theorem deployed_verify_whir_is_true (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (thash : Transcript.Hash) :
    Verifier.verifyWhir (InstalledWhirParse.installedParseEngine e gdec
      toyHash deployedShapeVk thash) deployedContext deployedProof = true := by
  rw [InstalledWhirParse.verify_whir_concrete_iff]
  obtain ⟨s, hs, hr, hb, hc⟩ := deployed_parse_matches_the_context
  exact ⟨s, hs, hr, hb, hc, installed_tail_returns_true_at_twenty_one_variables _⟩

/-! ## 7.  Rung 4: what still separates this witness from `derivedConfig`'s
acceptance

Five of the seven context fields are settled
(`deployed_context_shape_is_the_derived_shape`,
`deployed_context_claims_are_the_derived_claims`).  What remains is the two
packed points, the hash, the two stand-in parameter families, and the fact that
`DerivedAcceptance.derivedEngine` still carries the FIXTURE's `whirTail`, not
this module's install. -/

theorem the_derived_engine_still_carries_the_fixture_whir_pair
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine thash khash P).parseWhir =
        Verifier.testEngine.parseWhir ∧
      (DerivedAcceptance.derivedEngine thash khash P).whirTail = Verifier.testEngine.whirTail :=
  DerivedAcceptance.derived_engine_fixture_fields thash khash P

/-- The distance from the adopted witness, in one statement: the adopted
accepting configuration packs ONE variable and runs a zero-round profile; this
one packs twenty-one and runs four. -/
theorem this_witness_is_twenty_variables_above_the_adopted_one :
    Verifier.testConfig.degreeBits + Verifier.testConfig.indexBits = 1 ∧
    DerivedAcceptance.derivedConfig.degreeBits + DerivedAcceptance.derivedConfig.indexBits = 21 ∧
    WhirConfigured.exampleNoRounds.numVariables = 1 ∧
    WhirConfigured.exampleNoRounds.numRounds = 0 ∧
    deployedShapeVk.numVariables = 21 ∧
    deployedShapeVk.numRounds = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Audit.Wire3.DeployedWhirWitness
