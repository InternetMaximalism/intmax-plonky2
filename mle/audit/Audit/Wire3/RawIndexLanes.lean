import Audit.Wire3.RawBlockLanes
import Audit.Wire3.ReducedEngineIndex

/-!
# RAW-INDEX LANES: THE INDEX HALF WITHOUT THE REDUCED-HISTORY RESTRICTION

## WHAT THIS MODULE PROVES, AND WHAT IT DOES NOT -- READ THIS FIRST

The adopted `RawBlockLanes` removes the reduced-history restriction from the OUTER
half of the adaptive union bound: for every `StrategyChainBound.RoundCausal` round
message `S`, `strategic_raw_full_bad_draw_probability_le` bounds the outer, tau and
alpha lanes of `strategicShape c s S` by `combinedBound` plus one chain clash term.
Its HONESTY says in as many words that the INDEX half is NOT delivered there,
because the adopted `ReducedIndexLanes` states the index lanes over an
`OuterLaneTransport.ReducedStrategy` and a used-claims choice
`U : List Element -> Verifier.UsedClaims` reading the REDUCED round-challenge
history: `extendedShape`, `realizedClaims`, `extended_strat_shape_is_claim_shape`,
`extended_stage_is_index_digest`, `realized_history_reassign`,
`realized_claims_reassign` and the invariance through `outer_history_reassign` all
live on the reduced side.

THIS MODULE REMOVES THAT RESTRICTION TOO, and then transfers the result onto the
explicit engine's OWN index event.  `rawExtendedShape` is the adopted
`StrategyChainBound.strategicShape` below stage `22 + 5 d` and the eight adopted
`InstalledIndexSampler.claimFrames` of the claims a RAW used-claims choice
`U : (Nat -> Nat -> Block) -> Verifier.UsedClaims` picks after seeing the RAW
32-byte answers at every stage up to `22 + 5 d` -- every counter, every stage,
nothing reduced.  `ClaimsCausal d U` is the protocol's own causality for that
choice, the exact analogue of the adopted `RoundCausal`: the used claims are fixed
before the index digest's own challenge cells are squeezed, which is the ONLY
thing the diagonal step asks of them.

WHAT MAKES THIS WORK IS THAT THE COUNTING IS ALREADY STRATEGY-INDEPENDENT.  The
adopted `ReducedIndexLanes` sections 2, 3 and 4 -- `idxFibre`, `idx_fibre_stable`,
`idx_fibre_card`, `indexRead`, `idx_target_card`, `idx_diagonal_card`,
`idx_diagonal_mass_le` and `idx_diagonal_mass_le_density` -- are all stated over an
ABSTRACT `strat : StrategyChainBound.Strategy`.  They are REUSED VERBATIM below;
not one of them is restated, and no new counting is invented anywhere in this
file.  Only the two INVARIANCE facts are strategy-specific, and both are one line:
the used claims move with the raw view, which the adopted
`RawBlockLanes.table_view_reassign_lower` freezes below the index stage, and the
committed cells move with the reduced round-challenge history, which the adopted
`ReducedIndexLanes.outer_history_reassign` -- itself stated over an abstract
strategy -- freezes.

## WHAT IS PROVED

1. THE RAW EXTENDED PROVER (sections 1 and 2).  `rawExtendedShape` is a
   `StrategyChainBound.Strategy`, so the whole adopted strategy-chain machinery
   applies to it unchanged; `raw_extended_shape_bounded` discharges its length
   budget from the adopted `strategic_shape_bounded` and the adopted
   `IndexLanesOracle.claim_shape_payload_bound`; `raw_extended_agrees_below` says
   it IS `strategicShape c s S` below the claim frames, in the adopted
   `ReducedEngineIndex.AgreeBelow` sense.
   `raw_extended_strat_shape_is_claim_shape` identifies the eight frames past the
   rounds with the adopted `IndexLanesOracle.claimShapeAt` of the RAW realized
   claims, `raw_extended_stage_is_index_digest` identifies the chain's
   stage-`22 + 5 d + 8` digest with the adopted
   `InstalledIndexSampler.indexDigest` at those claims, and
   `raw_index_read_is_actual_index_draw` identifies the chain's index column with
   the adopted `InstalledIndexSampler.actualIndexDraw`.
2. THE DIAGONAL AT THE INDEX DIGEST (section 3).  `raw_realized_claims_reassign`
   and `raw_history_reassign` are the two invariances (both proved for EVERY
   counter at the index digest, which is what makes the numeric overlap of the
   index counters with the round counters moot);
   `raw_index_bad_no_clash_mass_le` is the adopted
   `ReducedIndexLanes.idx_diagonal_mass_le_density` at the raw target, with the
   adopted `IndexLanesOracle.guarded_index_bad_event_mass_le` as the density.
3. THE FULL BOUND FOR RAW STRATEGIES (sections 4 and 5).
   `raw_full_index_bad_draw_probability_le_combined` and its paired form
   `strategic_raw_full_index_bad_draw_probability_le`:

     `oracleProbability (boundedQueries L) (RawBlockLanes' full event U raw index event)`
       `<= ChallengeUnionBound.combinedBound d q d constraints`
          `+ 2 * ChallengeUnionBound.tauTerm bits`
          `+ (22 + 5 d + 8) (22 + 5 d + 9) / 2 / |Block|`

   for EVERY `RoundCausal S` and EVERY `ClaimsCausal d U`.  ONE clash term pays for
   all four masses, because the no-clash events nest.
4. THE ENGINE TRANSFER (sections 6 to 8).  `rawRealizedRun` is the run record of
   the raw adaptive prover -- the adopted `OuterLaneTransport.realizedProof` at the
   messages `S` really emitted, with the raw realized claims written into `used`.
   `raw_run_log_draw_is_history_entry` is the adopted
   `OuterLaneTransport.strategic_run_log_draw_is_log_triple` applied DIRECTLY: no
   reduced detour is needed, because that theorem is already stated for
   `strategicShape c s S` at a `RoundCausal S`.  The adopted
   `TwoStageConditionalCount.row_point_is_outer_draw_function` puts the engine's
   row point on the history, the adopted `ReducedEngineIndex.committedOf` closes it
   as a function of the history at FIXED extracted columns, and
   `raw_engine_index_bad_event_eq` is a `Finset` identity between the engine's own
   index bad event and the raw index event of section 3.  The headlines are
   `raw_engine_index_bad_draw_probability_le` and its five-cell form
   `raw_engine_index_bad_draw_probability_le_all_cells`.
5. NON-DEGENERACY AND THE CLOSED INSTANCES (sections 9 and 10).  `blockClaims` is a
   used-claims choice that reads a RAW BLOCK at stage `22` -- a stage that is not
   `roundStage i` for any `i`, so the adopted `OuterLaneTransport.reducedHistory`
   cannot see it -- and `block_claims_depends` exhibits its dependence.
   `raw_engine_index_bad_event_at_honest_cells` shows the guard bites.
   `raw_index_engine_bound_at_thirteen` and its five-cell twin are the closed
   instances at `S := StrategyChainBound.challengeTruncatedMessage m` -- the
   genuinely raw prover the adopted `OuterLaneTransport` header names as unpairable
   -- and at `U := blockClaims u0 u1`, with

     `<= combinedBound 13 8 13 123 + 2 * tauTerm 8 + 4560 / |Block|`,
     `<= combinedBound 13 8 13 123 + 5 (2 tauTerm 8) + 4560 / |Block|`,

   both recorded strictly below `1`.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)` -- one
independent uniform block per byte string of length at most `L`.  NOTHING HERE IS
A STATEMENT ABOUT keccak, about Poseidon, or about any concrete permutation, and
no reduction from a concrete hash is attempted or implied.

(ii) THE PROVER IS TRANSCRIPT-RESTRICTED.  A `StrategyChainBound.Strategy` is
handed the stage digests and the oracle's answers at the challenge inputs of those
digests; IT MAKES NO ORACLE QUERIES OF ITS OWN.  GRINDING IS THEREFORE EXCLUDED: a
real random-oracle-model adversary that hashes many candidate payloads and keeps a
lucky one is not of this type, and its clash mass grows with its query count.  The
adopted `GrindingQueryBound` / `GrindingGraphBound` / `GrindingLinearBound` develop
that separately; nothing here covers it.

(iii) `RoundCausal S` AND `ClaimsCausal d U` ARE THE PROTOCOL'S OWN CAUSALITY, AND
THEY ARE HYPOTHESES.  Round `r`'s message reads only the stages up to `22 + 5 r`,
and the used-claims choice reads only the stages up to `22 + 5 d`.  A prover that
violated them would be predicting a digest it has not seen.  They are nonetheless
ASSUMPTIONS on the strategy, not theorems about it, and `blockClaims` /
`challengeTruncatedMessage` are exhibited so that they are known satisfiable at a
NON-DEGENERATE instance.

(iv) THE ENGINE TRANSFER IS AT THE REALIZED RUN.  Sections 6 to 8 speak about the
explicit `SoundnessAssembly.engine` at `rawRealizedRun`, the proof record carrying
the messages the strategy really emitted at the table and the claims it really
chose.  It is not a statement about every proof record the engine might be handed.

(v) THE EXTRACTED COLUMNS `cols`, THE ZERO-CHECK DATA `g` AND THE ROW COEFFICIENTS
`coeffsOf` ARE FIXED DATA, bound outside the oracle law.  That is exactly the
standing assumption the adopted `ReducedIndexLanes` and `ReducedEngineIndex` make,
and it is what lets `ReducedEngineIndex.committedOf` be a function of the history
alone.  The adopted `CommitmentOrder` join -- whether the deployed commitment order
forces those columns -- remains OPEN and is not addressed here.

(vi) WHIR AND MERKLE ARE EXCLUDED.  No WHIR round, no Merkle path, no proof-of-work
grinding check is modelled anywhere below.

(vii) THIS IS A GOOD-DRAW-CONDITIONAL STATEMENT ABOUT ONE NAMED EVENT, AND IT IS
NOT THE SYSTEM'S SOUNDNESS ERROR.  Every bound is the mass of an explicitly named
`Finset` of oracle tables, conditioned on the chain's own no-clash event with the
complement paid for by ONE birthday term.  ACCEPTANCE IS NEVER EXHIBITED: not one
statement below says that a verifier accepts, or that an accepting adversary
exists, or that the extractor succeeds.  NO ADAPTIVE FIAT--SHAMIR SOUNDNESS IS PROVED.

(viii) THE MODEL IS R1b -- the adopted round-one-b chain model, in which the
strategy's stage digests are the chain's own.  The run-level transport of the
adopted `StrategyChainBound` HONESTY (iii)'s LAST SENTENCE IS NOT ADDRESSED HERE;
it remains open exactly as the adopted `RawBlockLanes` HONESTY leaves it.

(ix) `Finset.univ` APPEARS ONLY IN THIS MODULE'S OWN DEFINITIONS
(`rawIndexBadEvent`, `rawEngineIndexBadEvent`), where it is the full table space of
the uniform law, mirroring the adopted `ReducedIndexLanes.indexBadEvent` and
`ReducedEngineIndex.engineIndexBadEvent`.  No cardinality of `Element`, `Block` or
`OuterChallenge.DigestTriple` is ever evaluated numerically or handed to `ring` or
`omega`; the exponent bookkeeping is the adopted `ReducedFullTransport.peel_pow`
style throughout.
-/

namespace Audit.Wire3.RawIndexLanes

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.IndexLanesOracle
open Audit.Wire3.ReducedIndexLanes
open Audit.Wire3.ReducedEngineIndex
open Audit.Wire3.RawBlockLanes

/-! ## 1. A RAW USED-CLAIMS CHOICE AND THE RAW EXTENDED PROVER -/

/-- **A RAW USED-CLAIMS CHOICE.**  The prover picks the claims it opens as a
function of the RAW 32-byte answers -- every stage, every counter -- rather than of
the reduced round-challenge list the adopted
`ReducedIndexLanes.UsedClaimsStrategy` is handed.  NOTHING IS REDUCED HERE: no
`OuterChallenge.reduceTriple`, no restriction to counters below `6`, no restriction
to round stages. -/
def RawUsedClaims : Type := (Nat → Nat → Block) → Verifier.UsedClaims

/-- **THE PROTOCOL'S CAUSALITY, FOR THE USED-CLAIMS CHOICE.**  The claims are
chosen after all `d` coupled rounds and BEFORE the index digest's own challenge
cells are squeezed: the choice reads only the stages up to `22 + 5 d`.  This is
the adopted `StrategyChainBound.RoundCausal` at `r := d`, for a
`Verifier.UsedClaims`-valued function. -/
def ClaimsCausal (d : Nat) (U : RawUsedClaims) : Prop :=
  ∀ ch1 ch2 : Nat → Nat → Block, (∀ j, j ≤ 22 + 5 * d → ch1 j = ch2 j) → U ch1 = U ch2

/-- The width budget of a raw used-claims choice, quantified over EVERY raw view it
may see -- which is what adaptivity costs, exactly as the adopted
`StrategyChainBound.strategic_shape_bounded` quantifies the round messages. -/
def RawUsedClaimsBounded (W : Nat) (U : RawUsedClaims) : Prop :=
  ∀ ch, (U ch).logPreprocessed.length ≤ W ∧ (U ch).logWitness.length ≤ W ∧
    (U ch).logNormInverse.length ≤ W ∧ (U ch).gatePreprocessed.length ≤ W ∧
    (U ch).gateWitness.length ≤ W

/-- **THE RAW EXTENDED STRATEGIC SHAPE.**  The adopted
`StrategyChainBound.strategicShape` for the first `22 + 5 d` stages -- a RAW round
message, not a reduced one -- and then the EIGHT adopted
`InstalledIndexSampler.claimFrames` of the claims the prover chooses at the raw
view.  This is a `StrategyChainBound.Strategy`, so every lemma of the adopted
strategy-chain machinery applies to it unchanged. -/
def rawExtendedShape (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d : Nat) : Strategy :=
  fun k h ch =>
    if k < 22 + 5 * d then strategicShape c s S k h ch
    else claimShapeAt (U ch) (k - (22 + 5 * d))

theorem raw_extended_shape_apply (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d k : Nat) (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block) :
    rawExtendedShape c s S U d k h ch
      = if k < 22 + 5 * d then strategicShape c s S k h ch
        else claimShapeAt (U ch) (k - (22 + 5 * d)) := rfl

theorem raw_extended_shape_round (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d k : Nat) (hk : k < 22 + 5 * d) (h : Nat → Transcript.Digest)
    (ch : Nat → Nat → Block) :
    rawExtendedShape c s S U d k h ch = strategicShape c s S k h ch := if_pos hk

theorem raw_extended_shape_claim (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d i : Nat) (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block) :
    rawExtendedShape c s S U d (22 + 5 * d + i) h ch = claimShapeAt (U ch) i := by
  rw [raw_extended_shape_apply, if_neg (by omega),
    show 22 + 5 * d + i - (22 + 5 * d) = i from by omega]

/-- (1) **THE LENGTH BUDGET OF THE RAW EXTENDED PROVER, DISCHARGED.**  The first
`22 + 5 d` stages are the adopted `StrategyChainBound.strategic_shape_bounded`; the
last eight are the adopted `IndexLanesOracle.claim_shape_payload_bound`, quantified
over every raw view. -/
theorem raw_extended_shape_bounded (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d q W : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hU : RawUsedClaimsBounded W U) (hLq : 189 + 24 * q ≤ L) (hLW : 69 + 24 * W ≤ L)
    (hdom : 86 ≤ L) :
    StrategyBounded L (rawExtendedShape c s S U d) := by
  intro k h ch
  rw [raw_extended_shape_apply]
  by_cases hk : k < 22 + 5 * d
  · rw [if_pos hk]
    exact strategic_shape_bounded L c s S q hpre hSlog hSgate hLq k h ch
  · rw [if_neg hk]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hU ch
    exact claim_shape_payload_bound L W (U ch) h1 h2 h3 h4 h5 hLW hdom (k - (22 + 5 * d))

/-- (1) **THE RAW EXTENDED CHAIN IS THE STRATEGIC CHAIN BELOW THE CLAIM FRAMES**,
in the adopted `ReducedEngineIndex.AgreeBelow` sense.  The eight claim frames sit
strictly after every round stage, so everything the adopted `RawBlockLanes` proves
about `strategicShape c s S` below `22 + 5 d` is inherited. -/
theorem raw_extended_agrees_below (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d : Nat) :
    AgreeBelow (rawExtendedShape c s S U d) (strategicShape c s S) (22 + 5 * d) :=
  fun k hk h ch => raw_extended_shape_round c s S U d k hk h ch

/-! ## 2. THE REALIZED CLAIMS, THE INDEX DIGEST AND THE INDEX COLUMN -/

/-- **THE USED CLAIMS THE RAW EXTENDED PROVER REALLY PLAYS AT ONE TABLE**: its
choice at the adopted `RawBlockLanes.tableView` of the run -- the RAW 32-byte
answers, at every stage and every counter. -/
def rawRealizedClaims (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d : Nat) (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (T : OracleTable (boundedQueries L)) : Verifier.UsedClaims :=
  U (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T)

/-- (2) **THE VIEW THE CHAIN HANDS THE PROVER AT A LATER STAGE AGREES WITH THE RAW
VIEW BELOW THAT STAGE.**  The adopted `StrategyChainBound.strat_hist_eq` truncates
the history, and the adopted `challenge_at_is_sel` identifies the answer with the
table's value at the adopted `challengeSel`. -/
theorem raw_stage_view_is_table_view (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (k : Nat)
    (T : OracleTable (boundedQueries L)) (j : Nat) (hj : j ≤ k) :
    (fun cnt => challengeAt L hL T (stratHist L hL e0 strat hb k T j) cnt)
      = tableView L hL e0 strat hb T j := by
  funext cnt
  rw [strat_hist_eq L hL e0 strat hb k T j, Nat.min_eq_left hj]
  exact challenge_at_is_sel L hL e0 strat hb j cnt T

/-- (2) **THE EIGHT FRAMES BEYOND THE ROUNDS ARE THE CLAIM FRAMES OF THE RAW
REALIZED CLAIMS.**  At stage `22 + 5 d + i` the raw extended strategy plays the
adopted `IndexLanesOracle.claimShapeAt` of the claims it chose at the run's own raw
view: the view it is handed there agrees with `tableView` at every stage at or
below `22 + 5 d`, which by `ClaimsCausal` is all the choice reads. -/
theorem raw_extended_strat_shape_is_claim_shape (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d : Nat) (hU : ClaimsCausal d U) (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (T : OracleTable (boundedQueries L)) (i : Nat) :
    stratShapeAt L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (22 + 5 * d + i) T
      = claimShapeAt (rawRealizedClaims L hL c s S U d hb T) i := by
  show rawExtendedShape c s S U d (22 + 5 * d + i)
      (stratHist L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (22 + 5 * d + i) T)
      (fun i2 cnt => challengeAt L hL T
        (stratHist L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (22 + 5 * d + i) T i2) cnt)
    = claimShapeAt (rawRealizedClaims L hL c s S U d hb T) i
  rw [raw_extended_shape_claim]
  refine congrArg (fun u => claimShapeAt u i) (hU _ _ (fun j hj => ?_))
  exact raw_stage_view_is_table_view L hL OuterInitial.zeroDigest
    (rawExtendedShape c s S U d) hb (22 + 5 * d + i) T j (by omega)

/-- (2) The raw extended chain, past the rounds, IS the adopted
`BirthdayClashBound.foldDigest` of the eight claim frames. -/
theorem raw_extended_state_fold (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (T : OracleTable (boundedQueries L)) :
    ∀ j : Nat,
      strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (22 + 5 * d + j) T
        = foldDigest (hashOf (boundedQueries L) T)
            (strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
              (22 + 5 * d) T)
            (claimShapeAt (rawRealizedClaims L hL c s S U d hb T)) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j2 ih =>
      show strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (22 + 5 * d + j2 + 1) T = _
      rw [strategy_state_succ L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (22 + 5 * d + j2) T]
      show blockDigest (T (strategySel L hL OuterInitial.zeroDigest
          (rawExtendedShape c s S U d) hb (22 + 5 * d + j2) T))
        = (hashOf (boundedQueries L) T) (Transcript.frame
            (foldDigest (hashOf (boundedQueries L) T)
              (strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
                (22 + 5 * d) T)
              (claimShapeAt (rawRealizedClaims L hL c s S U d hb T)) j2)
            (claimShapeAt (rawRealizedClaims L hL c s S U d hb T) j2).1
            (claimShapeAt (rawRealizedClaims L hL c s S U d hb T) j2).2)
      rw [← hash_of_at (boundedQueries L) T
        (strategySel L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (22 + 5 * d + j2) T)]
      show (hashOf (boundedQueries L) T) (Transcript.frame
          (strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
            (22 + 5 * d + j2) T)
          (stratShapeAt L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
            (22 + 5 * d + j2) T).1
          (stratShapeAt L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
            (22 + 5 * d + j2) T).2) = _
      rw [ih, raw_extended_strat_shape_is_claim_shape L hL c s S U d hU hb T j2]

/-- (2) **THE HEADLINE IDENTIFICATION.**  The raw extended chain's digest after
`22 + 5 d + 8` stages IS the adopted `InstalledIndexSampler.indexDigest` at the
USED CLAIMS THE PROVER REALLY PLAYED -- the ones it chose after seeing the RAW
blocks of every stage up to `22 + 5 d`.  The hypothesis `hst` is the same
chain-model identification the adopted `IndexLanesOracle` takes, and it is
satisfiable by the chain's own state
(`raw_extended_index_state_hypothesis_is_satisfiable`). -/
theorem raw_extended_stage_is_index_digest (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (T : OracleTable (boundedQueries L)) (st : Transcript.State)
    (hst : st.digest = strategyFrameState L hL OuterInitial.zeroDigest
      (rawExtendedShape c s S U d) hb (22 + 5 * d) T) :
    strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (indexStage d) T
      = InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st
          (rawRealizedClaims L hL c s S U d hb T) := by
  have hfold := raw_extended_state_fold L hL c s S U d hU hb T 8
  have habs := fold_digest_absorb (hashOf (boundedQueries L) T)
    (InstalledIndexSampler.claimFrames (rawRealizedClaims L hL c s S U d hb T))
    (strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
      (22 + 5 * d) T)
    (claimShapeAt (rawRealizedClaims L hL c s S U d hb T)) (fun j _ => rfl)
  have hcf : (InstalledIndexSampler.claimFrames
      (rawRealizedClaims L hL c s S U d hb T)).length = 8 := rfl
  rw [hcf] at habs
  have hstep : strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
      (indexStage d) T
      = InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T)
          ⟨strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
            (22 + 5 * d) T, 0⟩ (rawRealizedClaims L hL c s S U d hb T) := by
    show strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (22 + 5 * d + 8) T = _
    rw [hfold, habs]
    rfl
  rw [hstep]
  exact index_digest_congr (hashOf (boundedQueries L) T) _ st
    (rawRealizedClaims L hL c s S U d hb T) hst.symm

/-- (2) The chain-model hypothesis is satisfiable: the chain's own post-rounds
state is a snapshot with that digest. -/
theorem raw_extended_index_state_hypothesis_is_satisfiable (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d : Nat) (hU : ClaimsCausal d U) (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (T : OracleTable (boundedQueries L)) :
    ∃ st : Transcript.State,
      st.digest = strategyFrameState L hL OuterInitial.zeroDigest
        (rawExtendedShape c s S U d) hb (22 + 5 * d) T ∧
      strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (indexStage d) T
        = InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st
            (rawRealizedClaims L hL c s S U d hb T) :=
  ⟨⟨strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
      (22 + 5 * d) T, 0⟩, rfl,
    raw_extended_stage_is_index_digest L hL c s S U d hU hb T _ rfl⟩

/-- (2) **THE INDEX COLUMN THE RAW EXTENDED CHAIN READS IS THE ADOPTED SAMPLER'S
OWN DRAW.**  Nothing is re-modelled: the table's three answers at the adopted
`InstalledIndexSampler.indexCounter` block of the stage-`22 + 5 d + 8` digest ARE
the three block digests the installed sampler squeezes, by the adopted
`OuterLaneTransport.stage_triple_is_actual_digests` and the digest identification
above.  The adopted `ReducedIndexLanes.indexRead` is reused verbatim. -/
theorem raw_index_read_is_actual_index_draw (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d bits : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (T : OracleTable (boundedQueries L)) (st : Transcript.State)
    (hst : st.digest = strategyFrameState L hL OuterInitial.zeroDigest
      (rawExtendedShape c s S U d) hb (22 + 5 * d) T) :
    indexRead L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb (indexStage d)
        bits T
      = InstalledIndexSampler.actualIndexDraw (hashOf (boundedQueries L) T)
          (InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st
            (rawRealizedClaims L hL c s S U d hb T)) bits := by
  funext k
  rw [index_read_at_counter L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
      (indexStage d) bits T k,
    stage_triple_is_actual_digests L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
      (indexStage d) (InstalledIndexSampler.indexCounter bits k) T,
    raw_extended_stage_is_index_digest L hL c s S U d hU hb T st hst]
  rfl


/-! ## 3. THE DIAGONAL AT THE INDEX DIGEST -/

/-- **THE INDEX BAD SET THE RUN'S OWN VIEW AND HISTORY PICK OUT.**  The adopted
`IndexLanesOracle.guardedIndexBadEvent` -- which is the adopted
`SoundnessAssembly.indexBadEvent`, guard for guard -- at the supplied cells the
prover's RAW used-claims choice determines and at a committed family read off the
reduced round-challenge history, which is what the explicit engine's row point is
a function of (section 7). -/
noncomputable def rawIndexBadTarget (bits : Nat) (U : RawUsedClaims) (cellIndex : Fin 5)
    (committed : List Element → List Element) (ch : Nat → Nat → Block)
    (xs : List Element) : Finset (InstalledIndexSampler.IndexSpace bits) :=
  guardedIndexBadEvent bits (OpenedClaimFold.lift (usedCell (U ch) cellIndex)) (committed xs)

/-- (3) On the branch where the prover supplies exactly the committed family the
target is EMPTY -- the adopted guard.  The adopted
`ReducedIndexLanes.index_bad_target_at_honest_cells`, at a raw choice. -/
theorem raw_index_bad_target_at_honest_cells (bits : Nat) (U : RawUsedClaims)
    (cellIndex : Fin 5) (committed : List Element → List Element)
    (ch : Nat → Nat → Block) (xs : List Element)
    (h : committed xs = OpenedClaimFold.lift (usedCell (U ch) cellIndex)) :
    rawIndexBadTarget bits U cellIndex committed ch xs = ∅ := by
  rw [rawIndexBadTarget, h]
  exact guarded_index_bad_event_of_equal_cells bits _

/-- (3) **THE PROVER HAS COMMITTED TO ITS CLAIMS BEFORE THE INDEX CELLS ARE READ.**
The raw view below the index stage is frozen by the adopted
`RawBlockLanes.table_view_reassign_lower`, and `ClaimsCausal` says the choice reads
nothing else.  THIS IS THE ONE STRATEGY-SPECIFIC INVARIANCE OF THE WHOLE MODULE. -/
theorem raw_realized_claims_reassign (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d cc : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
      (indexStage d)) (b : Block) :
    rawRealizedClaims L hL c s S U d hb
        (reassign T (challengeSel L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (indexStage d) cc T) b)
      = rawRealizedClaims L hL c s S U d hb T :=
  hU _ _ (fun j hj => table_view_reassign_lower L hL OuterInitial.zeroDigest
    (rawExtendedShape c s S U d) hb (indexStage d) cc T hT b j (by rw [indexStage]; omega))

/-- (3) And the reduced round-challenge history is frozen too: the adopted
`ReducedIndexLanes.outer_history_reassign`, which is stated over an ABSTRACT
strategy and is therefore REUSED VERBATIM here. -/
theorem raw_history_reassign (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d cc : Nat)
    (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
      (indexStage d)) (b : Block) :
    outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (reassign T (challengeSel L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (indexStage d) cc T) b) d
      = outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T d :=
  outer_history_reassign L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
    (indexStage d) cc T hT b d (fun i hi => round_stage_lt_index_stage i d hi)

open Classical in
/-- **THE RAW INDEX BAD EVENT ON THE ORACLE TABLE**, at the realized claims and the
realized history.  The target is NOT fixed data: it moves with the table, through
BOTH the raw view and the reduced history.  `Finset.univ` here is this module's own
(see HONESTY (ix)). -/
noncomputable def rawIndexBadEvent (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d bits : Nat)
    (hb : StrategyBounded L (rawExtendedShape c s S U d)) (cellIndex : Fin 5)
    (committed : List Element → List Element) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    indexRead L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb (indexStage d)
        bits T
      ∈ rawIndexBadTarget bits U cellIndex committed
          (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T)
          (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T d))

open Classical in
theorem mem_raw_index_bad_event (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d bits : Nat)
    (hb : StrategyBounded L (rawExtendedShape c s S U d)) (cellIndex : Fin 5)
    (committed : List Element → List Element) (T : OracleTable (boundedQueries L)) :
    T ∈ rawIndexBadEvent L hL c s S U d bits hb cellIndex committed ↔
      indexRead L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb (indexStage d)
          bits T
        ∈ rawIndexBadTarget bits U cellIndex committed
            (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T)
            (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T d) := by
  rw [rawIndexBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

open Classical in
/-- (3) **THE INDEX-LANE MASS FOR THE RAW ADAPTIVE PROVER.**  Conditioned on the
raw extended chain's own no-clash event at stage `22 + 5 d + 8`, the mass of the
event that the realized index draw lands in the bad set THE RUN'S OWN RAW VIEW AND
HISTORY picked out is at most `2 * ChallengeUnionBound.tauTerm bits` -- exactly the
constant the adopted `IndexLanesOracle.guarded_index_bad_event_mass_le` gets for a
FIXED proof record.

The counting is the adopted `ReducedIndexLanes.idx_diagonal_mass_le_density`,
REUSED VERBATIM: it is stated over an abstract `strat : Strategy`, so the raw
extended prover is an instance of it with nothing changed.  The only new inputs are
the two invariances above. -/
theorem raw_index_bad_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d bits : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d)) (cellIndex : Fin 5)
    (committed : List Element → List Element) (hbu : 6 * bits ≤ Transcript.u64Limit) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
            (indexStage d)).filter (fun T =>
          indexRead L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
              (indexStage d) bits T
            ∈ rawIndexBadTarget bits U cellIndex committed
                (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T)
                (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
                  T d)))
      ≤ 2 * ChallengeUnionBound.tauTerm bits := by
  refine idx_diagonal_mass_le_density L hL OuterInitial.zeroDigest
    (rawExtendedShape c s S U d) hb (indexStage d) bits
    (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb (indexStage d))
    (fun m _ => stage_stable_no_clash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d)
      hb (indexStage d) (tripleCounters (indexBlockBase m))) hbu
    (fun T => rawIndexBadTarget bits U cellIndex committed
      (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T)
      (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T d))
    (fun T hT m _ cc _ b => ?_) (2 * ChallengeUnionBound.tauTerm bits) ?_ (fun T _ => ?_)
  · show rawIndexBadTarget bits U cellIndex committed
        (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (reassign T (challengeSel L hL OuterInitial.zeroDigest
            (rawExtendedShape c s S U d) hb (indexStage d) cc T) b))
        (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (reassign T (challengeSel L hL OuterInitial.zeroDigest
            (rawExtendedShape c s S U d) hb (indexStage d) cc T) b) d)
      = rawIndexBadTarget bits U cellIndex committed
        (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T)
        (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T d)
    rw [rawIndexBadTarget, rawIndexBadTarget,
      show U (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
            (reassign T (challengeSel L hL OuterInitial.zeroDigest
              (rawExtendedShape c s S U d) hb (indexStage d) cc T) b))
          = U (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T) from
        raw_realized_claims_reassign L hL c s S U d cc hU hb T hT b,
      raw_history_reassign L hL c s S U d cc hb T hT b]
  · have h := tau_term_nonneg bits
    linarith
  · exact guarded_index_bad_event_mass_le bits
      (OpenedClaimFold.lift (usedCell (U (tableView L hL OuterInitial.zeroDigest
        (rawExtendedShape c s S U d) hb T)) cellIndex))
      (committed (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        T d))

open Classical in
/-- (3) The same, with the conditioning written as an intersection. -/
theorem raw_index_bad_event_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d bits : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d)) (cellIndex : Fin 5)
    (committed : List Element → List Element) (hbu : 6 * bits ≤ Transcript.u64Limit) :
    oracleProbability (boundedQueries L)
        (rawIndexBadEvent L hL c s S U d bits hb cellIndex committed
          ∩ stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
              (indexStage d))
      ≤ 2 * ChallengeUnionBound.tauTerm bits := by
  have hsub : rawIndexBadEvent L hL c s S U d bits hb cellIndex committed
        ∩ stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
            (indexStage d)
      ⊆ (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          (indexStage d)).filter (fun T =>
          indexRead L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
              (indexStage d) bits T
            ∈ rawIndexBadTarget bits U cellIndex committed
                (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb T)
                (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
                  T d)) := by
    rw [rawIndexBadEvent]
    exact univ_filter_inter_subset _ _ _ (fun T hT => hT)
  exact le_trans (oracle_probability_mono (boundedQueries L) _ _ hsub)
    (raw_index_bad_no_clash_mass_le L hL c s S U d bits hU hb cellIndex committed hbu)

/-! ## 4. THE OUTER, TAU AND ALPHA MASSES AT THE INDEX CONDITIONING STAGE -/

open Classical in
/-- (4) **THE FIRST THREE SUMMANDS AT THE LARGER CONDITIONING STAGE.**  The adopted
`RawBlockLanes.rawFullBadEvent`, conditioned on the raw extended chain's no-clash
event at stage `22 + 5 d + 8` rather than at `22 + 5 d`: the adopted
`OuterLaneTransport.stage_no_clash_mono` nests the two, so more than one index
summand can later be added under ONE complement term.  The three masses are the
adopted `RawBlockLanes.raw_no_clash_mass_le` and the adopted
`ReducedFullTransport.gate_tau_no_clash_mass_le` / `gate_alpha_no_clash_mass_le`,
reused verbatim. -/
theorem raw_full_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (d q rows constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
          ∩ stageNoClash L hL e0 strat hb (indexStage d))
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints := by
  have hnest : stageNoClash L hL e0 strat hb (indexStage d)
      ⊆ stageNoClash L hL e0 strat hb ReducedFullTransport.deriveStage :=
    stage_no_clash_mono L hL e0 strat hb ReducedFullTransport.deriveStage (indexStage d)
      (le_of_lt (derive_stage_lt_index_stage d))
  have hu3 := inter_union_mass_le L
    (rawOuterBadEvent L hL e0 strat hb logLane gateLane d
      ∪ ReducedFullTransport.gateTauBadEvent L hL e0 strat hb d g)
    (ReducedFullTransport.gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf)
    (stageNoClash L hL e0 strat hb (indexStage d))
  have hu4 := inter_union_mass_le L
    (rawOuterBadEvent L hL e0 strat hb logLane gateLane d)
    (ReducedFullTransport.gateTauBadEvent L hL e0 strat hb d g)
    (stageNoClash L hL e0 strat hb (indexStage d))
  have houter := raw_no_clash_mass_le L hL e0 strat hb logLane gateLane hlcau hgcau 5 (q + 2)
    hlog hgate (indexStage d) d
    (fun r hr => le_of_lt (round_stage_lt_index_stage r d hr))
  rw [round_terms_sum d q] at houter
  have htausub : ReducedFullTransport.gateTauBadEvent L hL e0 strat hb d g
        ∩ stageNoClash L hL e0 strat hb (indexStage d)
      ⊆ (stageNoClash L hL e0 strat hb ReducedFullTransport.deriveStage).filter (fun T =>
          ReducedFullTransport.tauRead L hL e0 strat hb d T
            ∈ ChallengeUnionBound.productEvent d
                (ZeroCheckSemantics.zeroCheckBadSet d g)) := by
    rw [ReducedFullTransport.gateTauBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have htau : oracleProbability (boundedQueries L)
      (ReducedFullTransport.gateTauBadEvent L hL e0 strat hb d g
        ∩ stageNoClash L hL e0 strat hb (indexStage d))
      ≤ ChallengeUnionBound.tauTerm d :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ htausub)
      (ReducedFullTransport.gate_tau_no_clash_mass_le L hL e0 strat hb d g hdu)
  have halphasub : ReducedFullTransport.gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
        ∩ stageNoClash L hL e0 strat hb (indexStage d)
      ⊆ (stageNoClash L hL e0 strat hb ReducedFullTransport.deriveStage).filter (fun T =>
          stageTriple L hL e0 strat hb ReducedFullTransport.deriveStage
              (ReducedFullTransport.alphaBase d) T
            ∈ OuterChallenge.tupleEvent
                (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)) := by
    rw [ReducedFullTransport.gateAlphaBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have halpha : oracleProbability (boundedQueries L)
      (ReducedFullTransport.gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
        ∩ stageNoClash L hL e0 strat hb (indexStage d))
      ≤ ChallengeUnionBound.alphaTerm rows constraints :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ halphasub)
      (ReducedFullTransport.gate_alpha_no_clash_mass_le L hL e0 strat hb d rows constraints
        coeffsOf hdu hclen)
  rw [rawFullBadEvent]
  linarith

/-! ## 5. THE FULL BOUND WITH THE INDEX LANES, FOR RAW STRATEGIES -/

open Classical in
/-- **THE FULL BAD EVENT WITH THE RAW INDEX LANES INCLUDED**: the adopted
`RawBlockLanes.rawFullBadEvent` -- some coupled round of either RAW outer lane
agrees, or the gate tau column lands in the adopted zero-check bad set, or the gate
alpha lands in the adopted row union -- OR the realized index draw lands in the bad
set the run's own raw view and history picked out. -/
noncomputable def rawFullIndexBadEvent (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d bits : Nat)
    (hb : StrategyBounded L (rawExtendedShape c s S U d)) (logLane gateLane : RawLane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (committed : List Element → List Element) : Finset (OracleTable (boundedQueries L)) :=
  rawFullBadEvent L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb logLane
      gateLane d rows g coeffsOf
    ∪ rawIndexBadEvent L hL c s S U d bits hb cellIndex committed

open Classical in
theorem mem_raw_full_index_bad_event (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d bits : Nat)
    (hb : StrategyBounded L (rawExtendedShape c s S U d)) (logLane gateLane : RawLane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (committed : List Element → List Element) (T : OracleTable (boundedQueries L)) :
    T ∈ rawFullIndexBadEvent L hL c s S U d bits hb logLane gateLane rows g coeffsOf
        cellIndex committed ↔
      (T ∈ rawFullBadEvent L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
          logLane gateLane d rows g coeffsOf ∨
        T ∈ rawIndexBadEvent L hL c s S U d bits hb cellIndex committed) := by
  rw [rawFullIndexBadEvent, Finset.mem_union]

open Classical in
/-- (5) **THE FULL BOUND, WITH THE RAW INDEX LANES.**  The four masses are
conditioned on the SAME no-clash event, that of the raw extended chain at its full
`22 + 5 d + 8` stages, so ONE complement term pays for all four.

READ HONESTY (vii): THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR. -/
theorem raw_full_index_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d bits : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d)) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (q rows constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (committed : List Element → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * bits ≤ Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullIndexBadEvent L hL c s S U d bits hb logLane gateLane rows g coeffsOf
          cellIndex committed)
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints
        + 2 * ChallengeUnionBound.tauTerm bits
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (rawFullIndexBadEvent L hL c s S U d bits hb logLane gateLane rows g coeffsOf cellIndex
        committed)
      (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (indexStage d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (rawFullIndexBadEvent L hL c s S U d bits hb logLane gateLane rows g coeffsOf cellIndex
        committed
      ∩ stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (indexStage d))
    ((stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
      (indexStage d))ᶜ)
  have hs1 := inter_union_mass_le L
    (rawFullBadEvent L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb logLane
      gateLane d rows g coeffsOf)
    (rawIndexBadEvent L hL c s S U d bits hb cellIndex committed)
    (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb (indexStage d))
  have hfull := raw_full_no_clash_mass_le L hL OuterInitial.zeroDigest
    (rawExtendedShape c s S U d) hb logLane gateLane hlcau hgcau d q rows constraints g
    coeffsOf hdu hlog hgate hclen
  have hidx := raw_index_bad_event_no_clash_mass_le L hL c s S U d bits hU hb cellIndex
    committed hbu
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hb
        (indexStage d))ᶜ)
      ≤ ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL OuterInitial.zeroDigest
      (rawExtendedShape c s S U d) hb (indexStage d)
  rw [rawFullIndexBadEvent] at hmono hu1 ⊢
  linarith

open Classical in
/-- (5) **THE SAME, WITH THE CONSTANT READ OFF AS THE ADOPTED `combinedBound` PLUS
THE INDEX TERM.**  At `rows = 2 ^ d` the first three summands ARE
`ChallengeUnionBound.combinedBound d q d constraints`, term for term. -/
theorem raw_full_index_bad_draw_probability_le_combined (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims)
    (d bits : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d)) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (committed : List Element → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * bits ≤ Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullIndexBadEvent L hL c s S U d bits hb logLane gateLane (2 ^ d) g coeffsOf
          cellIndex committed)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 2 * ChallengeUnionBound.tauTerm bits
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := raw_full_index_bad_draw_probability_le L hL c s S U d bits hU hb logLane gateLane
    hlcau hgcau q (2 ^ d) constraints g coeffsOf cellIndex committed hdu hbu hlog hgate hclen
  rw [ChallengeUnionBound.combinedBound]
  exact h

open Classical in
/-- (5) **THE PAIRED FORM: THE INDEX HALF FOR RAW STRATEGIES.**  The strategy is
`rawExtendedShape c s S U d` for an arbitrary `RoundCausal S` and an arbitrary
`ClaimsCausal d U`, and the two outer lanes are the adopted
`RawBlockLanes.rawLogLaneOfStrategy` / `rawGateLaneOfStrategy` -- ITS OWN, so round
`r`'s bad set is built from the message THE PROVER CHOSE after seeing the RAW
blocks of every earlier stage, and the index bad set is built from the claims THE
PROVER CHOSE after seeing the RAW blocks of every round.  NO REDUCED-HISTORY
RESTRICTION REMAINS ON EITHER HALF.

  `<= combinedBound d q d constraints + 2 tauTerm bits + (22+5d+8)(22+5d+9)/2/|Block|`.

READ THE HONESTY HEADER. -/
theorem strategic_raw_full_index_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d bits : Nat) (hU : ClaimsCausal d U)
    (hb : StrategyBounded L (rawExtendedShape c s S U d))
    (trlog trgate : Nat → (Nat → Nat → Block) → List Element)
    (htrlog : RawCausal trlog) (htrgate : RawCausal trgate) (a1 b1 a2 b2 : Element)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (committed : List Element → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * bits ≤ Transcript.u64Limit)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (trlog r ch).length ≤ 5)
    (hlengate : ∀ (r : Nat) (ch : Nat → Nat → Block), (trgate r ch).length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullIndexBadEvent L hL c s S U d bits hb
          (rawLogLaneOfStrategy S trlog a1 b1) (rawGateLaneOfStrategy S trgate a2 b2)
          (2 ^ d) g coeffsOf cellIndex committed)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 2 * ChallengeUnionBound.tauTerm bits
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  raw_full_index_bad_draw_probability_le_combined L hL c s S U d bits hU hb
    (rawLogLaneOfStrategy S trlog a1 b1) (rawGateLaneOfStrategy S trgate a2 b2)
    (raw_log_lane_causal S hS trlog htrlog a1 b1)
    (raw_gate_lane_causal S hS trgate htrgate a2 b2) q constraints g coeffsOf cellIndex
    committed hdu hbu (raw_log_lane_bounded S trlog a1 b1 5 hSlog hlenlog)
    (raw_gate_lane_bounded S trgate a2 b2 (q + 2) hSgate hlengate) hclen


/-! ## 6. THE REALIZED RUN OF THE RAW ADAPTIVE PROVER -/

/-- **THE RUN RECORD OF THE RAW ADAPTIVE PROVER AT ONE TABLE**: the adopted
`ReducedEngineIndex.realizedUsedProof` at the messages the RAW round-message choice
produced -- the adopted `StrategyChainBound.realizedMessages` -- with the claims the
RAW used-claims choice picked at the run's own raw view written into `used`. -/
def rawRealizedRun (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S))
    (T : OracleTable (boundedQueries L)) : Verifier.Proof :=
  realizedUsedProof s (realizedMessages L hL c s S hbS c.degreeBits T)
    (rawRealizedClaims L hL c s S U d hbE T)

theorem raw_realized_run_statement (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    Verifier.statement (rawRealizedRun L hL c s S U d hbE hbS T) = s := rfl

theorem raw_realized_run_messages (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    roundMessages (rawRealizedRun L hL c s S U d hbE hbS T)
      = realizedMessages L hL c s S hbS c.degreeBits T :=
  realized_used_proof_messages _ _ _

theorem raw_realized_run_used (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    (rawRealizedRun L hL c s S U d hbE hbS T).used
      = rawRealizedClaims L hL c s S U d hbE T := rfl

theorem raw_realized_run_messages_length (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    (roundMessages (rawRealizedRun L hL c s S U d hbE hbS T)).length = c.degreeBits := by
  rw [raw_realized_run_messages, realized_messages_length]

theorem raw_realized_run_length_budget (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    ∀ k, 61 + (prefixRoundShape c
        (Verifier.statement (rawRealizedRun L hL c s S U d hbE hbS T))
        (roundMessages (rawRealizedRun L hL c s S U d hbE hbS T)) k).2.length ≤ L := by
  rw [raw_realized_run_statement, raw_realized_run_messages]
  exact strategic_hlen_of_bounded L hL c s S hbS c.degreeBits T

/-! ### 6.1 The run's outer-draw coordinates are the realized history's entries -/

/-- (6) **THE RUN'S `Draw.outerLog r` COORDINATE IS ENTRY `2 r` OF THE REALIZED
HISTORY.**  The adopted `OuterLaneTransport.strategic_run_log_draw_is_log_triple` is
stated for `strategicShape c s S` at a `RoundCausal S`, so it applies DIRECTLY here
-- the adopted `ReducedEngineIndex` had to go through `reducedRoundMessage R` and
its causality lemma; nothing of the sort is needed for a raw prover. -/
theorem raw_run_log_draw_is_history_entry (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (U : RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L))
    (hdeg : c.degreeBits = d) (r : Nat) (hr : r < c.degreeBits) :
    OuterChallenge.reduceTriple (InstalledRoundCommit.actualDigestDraw
        (hashOf (boundedQueries L) T) c (rawRealizedRun L hL c s S U d hbE hbS T)
        (JointChallengeSpace.Draw.outerLog ⟨r, hr⟩))
      = ((outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T d).get?
          (2 * r)).getD 0 := by
  have h1 := strategic_run_log_draw_is_log_triple L hL c s S hbS hS
    (rawRealizedRun L hL c s S U d hbE hbS T) T
    (raw_realized_run_statement L hL c s S U d hbE hbS T)
    (raw_realized_run_messages L hL c s S U d hbE hbS T)
    (raw_realized_run_length_budget L hL c s S U d hbE hbS T)
    (raw_realized_run_messages_length L hL c s S U d hbE hbS T) ⟨r, hr⟩
  have h2 : logTriple L hL OuterInitial.zeroDigest (strategicShape c s S) hbS r T
      = logTriple L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE r T :=
    (stage_triple_of_agree L hL OuterInitial.zeroDigest _ _ hbE hbS (22 + 5 * d)
      (raw_extended_agrees_below c s S U d) T (roundStage r) 0
      (by rw [roundStage]; omega)).symm
  rw [h1.trans h2, outer_history_get_log L hL OuterInitial.zeroDigest
    (rawExtendedShape c s S U d) hbE T d r (by omega)]
  rfl

/-- (6) The same for the GATE coordinate and entry `2 r + 1`. -/
theorem raw_run_gate_draw_is_history_entry (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (U : RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L))
    (hdeg : c.degreeBits = d) (r : Nat) (hr : r < c.degreeBits) :
    OuterChallenge.reduceTriple (InstalledRoundCommit.actualDigestDraw
        (hashOf (boundedQueries L) T) c (rawRealizedRun L hL c s S U d hbE hbS T)
        (JointChallengeSpace.Draw.outerGate ⟨r, hr⟩))
      = ((outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T d).get?
          (2 * r + 1)).getD 0 := by
  have h1 := strategic_run_gate_draw_is_gate_triple L hL c s S hbS hS
    (rawRealizedRun L hL c s S U d hbE hbS T) T
    (raw_realized_run_statement L hL c s S U d hbE hbS T)
    (raw_realized_run_messages L hL c s S U d hbE hbS T)
    (raw_realized_run_length_budget L hL c s S U d hbE hbS T)
    (raw_realized_run_messages_length L hL c s S U d hbE hbS T) ⟨r, hr⟩
  have h2 : gateTriple L hL OuterInitial.zeroDigest (strategicShape c s S) hbS r T
      = gateTriple L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE r T :=
    (stage_triple_of_agree L hL OuterInitial.zeroDigest _ _ hbE hbS (22 + 5 * d)
      (raw_extended_agrees_below c s S U d) T (roundStage r) 3
      (by rw [roundStage]; omega)).symm
  rw [h1.trans h2, outer_history_get_gate L hL OuterInitial.zeroDigest
    (rawExtendedShape c s S U d) hbE T d r (by omega)]
  rfl

/-! ### 6.2 The committed cells are a function of the realized history -/

/-- (6) **THE ROW POINT OF THE EXPLICIT ENGINE AT THE RAW REALIZED RUN IS READ OFF
THE REALIZED HISTORY.**  The adopted
`TwoStageConditionalCount.row_point_is_outer_draw_function` puts entry `r` of the
adopted `OpenedClaimFold.cellRow` at the run's own outer draw; the two lemmas above
put that draw on the history.  The adopted `ReducedEngineIndex.rowFromHistory` and
`cellOffset` are reused verbatim. -/
theorem raw_lift_cell_row_is_row_from_history (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5) (T : OracleTable (boundedQueries L)) :
    OpenedClaimFold.lift (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
          (hashOf (boundedQueries L) T) khash P c₀) c
          (rawRealizedRun L hL c s S U d hbE hbS T)) cellIndex)
      = rowFromHistory cellIndex
          (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T d) := by
  have hmlen := raw_realized_run_messages_length L hL c s S U d hbE hbS T
  have hxlen : (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T
      d).length = 2 * d :=
    outer_history_length L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T d
  have hhalf : (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T
        d).length / 2 = d := by
    rw [hxlen]; omega
  have hrowlen : (OpenedClaimFold.cellRow (Verifier.derivedRounds
        (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
        (rawRealizedRun L hL c s S U d hbE hbS T)) cellIndex).length = c.degreeBits := by
    rw [TwoStageConditionalCount.cell_row_length gdec hash khash P c₀ c
      (rawRealizedRun L hL c s S U d hbE hbS T) cellIndex (hashOf (boundedQueries L) T)]
    exact hmlen
  refine List.ext_get? (fun k => ?_)
  by_cases hk : k < c.degreeBits
  · rw [lift_get, TwoStageConditionalCount.row_point_is_outer_draw_function gdec hash
      (hashOf (boundedQueries L) T) khash P c₀ c (rawRealizedRun L hL c s S U d hbE hbS T)
      hdb hmlen cellIndex k hk,
      row_from_history_get cellIndex _ k (by rw [hhalf]; omega)]
    fin_cases cellIndex
    · exact congrArg some
        (raw_run_log_draw_is_history_entry L hL c s S hS U d hbE hbS T hdeg k hk)
    · exact congrArg some
        (raw_run_log_draw_is_history_entry L hL c s S hS U d hbE hbS T hdeg k hk)
    · exact congrArg some
        (raw_run_log_draw_is_history_entry L hL c s S hS U d hbE hbS T hdeg k hk)
    · exact congrArg some
        (raw_run_gate_draw_is_history_entry L hL c s S hS U d hbE hbS T hdeg k hk)
    · exact congrArg some
        (raw_run_gate_draw_is_history_entry L hL c s S hS U d hbE hbS T hdeg k hk)
  · rw [List.get?_eq_none.mpr
        (by rw [OpenedClaimFold.lift, List.length_map, hrowlen]; omega),
      row_from_history_get_none cellIndex _ k (by rw [hhalf]; omega)]

/-- (6) **THE COMMITTED CELL FAMILY AS A FUNCTION OF THE REALIZED HISTORY.**  The
extracted columns are FIXED DATA (HONESTY (v)) and the row point they are evaluated
at is read off the history, so the whole family is: the adopted
`ReducedEngineIndex.committedOf`, reused verbatim.  This is what licenses
instantiating section 5 at `committed := committedOf cols cellIndex`. -/
theorem raw_committed_is_history_function (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (T : OracleTable (boundedQueries L)) :
    IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
            (hashOf (boundedQueries L) T) khash P c₀) c
            (rawRealizedRun L hL c s S U d hbE hbS T)) cellIndex))
      = committedOf cols cellIndex
          (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T d) :=
  congrArg (IndexPointZeroCheck.openedCells (cols cellIndex))
    (raw_lift_cell_row_is_row_from_history gdec hash khash P c₀ L hL c s S hS U d hbE hbS
      hdeg hdb cellIndex T)

/-! ## 7. THE INDEX DIGEST AND THE INDEX DRAW OF THE RAW REALIZED RUN -/

/-- (7) **THE RAW EXTENDED CHAIN'S POST-ROUNDS DIGEST IS THE RUN'S OWN POST-ROUNDS
DIGEST.**  The adopted `ConcreteChainThreading.chain_model_is_the_run_chain` at
`r = degreeBits`, carried onto the raw extended chain by section 1 and the adopted
`StrategyChainBound.strategic_prover_chain_is_strategy_chain`.  This discharges the
chain-model hypothesis `hst` of section 2 AT THE SNAPSHOT THE ADOPTED
`SoundnessAssembly.actualIndexDraw` USES, rather than at the chain's own. -/
theorem raw_extended_rounds_state_is_run_digest (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (T : OracleTable (boundedQueries L)) :
    (InstalledRoundCommit.concreteFinal (hashOf (boundedQueries L) T)
        (OuterInitial.derive (hashOf (boundedQueries L) T) c
          (Verifier.statement (rawRealizedRun L hL c s S U d hbE hbS T))).state 0
        ((rawRealizedRun L hL c s S U d hbE hbS T).logRounds.zip
          (rawRealizedRun L hL c s S U d hbE hbS T).gateRounds)).digest
      = strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE
          (22 + 5 * d) T := by
  have hmlen := raw_realized_run_messages_length L hL c s S U d hbE hbS T
  have hbud := raw_realized_run_length_budget L hL c s S U d hbE hbS T
  have hshape : prefixRoundShape c (Verifier.statement (rawRealizedRun L hL c s S U d hbE hbS T))
        (roundMessages (rawRealizedRun L hL c s S U d hbE hbS T))
      = prefixRoundShape c s (realizedMessages L hL c s S hbS c.degreeBits T) := by
    rw [raw_realized_run_statement, raw_realized_run_messages]
  have h1 : strategyFrameState L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE
        (22 + 5 * d) T
      = strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
        (22 + 5 * d) T :=
    strategy_frame_state_of_agree L hL OuterInitial.zeroDigest _ _ hbE hbS (22 + 5 * d)
      (raw_extended_agrees_below c s S U d) T (22 + 5 * d) (Nat.le_refl _)
  have h2 : strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
        (22 + 5 * d) T
      = frameState L OuterInitial.zeroDigest
          (prefixRoundShape c s (realizedMessages L hL c s S hbS c.degreeBits T))
          (strategic_hlen_of_bounded L hL c s S hbS c.degreeBits T) (22 + 5 * d) T := by
    rw [← hdeg]
    exact strategic_prover_chain_is_strategy_chain L hL c s S hbS hS c.degreeBits T
      (22 + 5 * c.degreeBits) (Nat.le_refl _)
  have h3 : frameState L OuterInitial.zeroDigest
        (prefixRoundShape c (Verifier.statement (rawRealizedRun L hL c s S U d hbE hbS T))
          (roundMessages (rawRealizedRun L hL c s S U d hbE hbS T))) hbud (22 + 5 * d) T
      = frameState L OuterInitial.zeroDigest
        (prefixRoundShape c s (realizedMessages L hL c s S hbS c.degreeBits T))
        (strategic_hlen_of_bounded L hL c s S hbS c.degreeBits T) (22 + 5 * d) T :=
    frame_state_shape_congr L OuterInitial.zeroDigest _ _ hshape hbud
      (strategic_hlen_of_bounded L hL c s S hbS c.degreeBits T) (22 + 5 * d) T
  have h4 := ConcreteChainThreading.chain_model_is_the_run_chain L c
    (rawRealizedRun L hL c s S U d hbE hbS T) hbud T c.degreeBits (Nat.le_of_eq hmlen.symm)
  have hstage : 22 + 5 * d = 22 + 5 * c.degreeBits := by omega
  rw [h1, h2, ← h3, hstage, h4,
    show (roundMessages (rawRealizedRun L hL c s S U d hbE hbS T)).take c.degreeBits
      = roundMessages (rawRealizedRun L hL c s S U d hbE hbS T) from by
        rw [← hmlen, List.take_length]]
  rfl

/-- (7) **THE EXPLICIT ENGINE'S OWN INDEX DRAW AT THE RAW REALIZED RUN IS THE RAW
EXTENDED CHAIN'S INDEX COLUMN.**  Section 2's identification at the snapshot the
adopted `SoundnessAssembly.actualIndexDraw` names, which the previous theorem
supplies. -/
theorem raw_run_index_draw_is_index_read (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (U : RawUsedClaims) (d : Nat) (hU : ClaimsCausal d U)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (T : OracleTable (boundedQueries L)) :
    SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c
        (rawRealizedRun L hL c s S U d hbE hbS T)
      = indexRead L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE (indexStage d)
          c.indexBits T :=
  (raw_index_read_is_actual_index_draw L hL c s S U d c.indexBits hU hbE T
    (InstalledRoundCommit.concreteFinal (hashOf (boundedQueries L) T)
      (OuterInitial.derive (hashOf (boundedQueries L) T) c
        (Verifier.statement (rawRealizedRun L hL c s S U d hbE hbS T))).state 0
      ((rawRealizedRun L hL c s S U d hbE hbS T).logRounds.zip
        (rawRealizedRun L hL c s S U d hbE hbS T).gateRounds))
    (raw_extended_rounds_state_is_run_digest L hL c s S hS U d hbE hbS hdeg T)).symm

/-! ## 8. THE EXPLICIT ENGINE'S OWN INDEX BAD EVENT, FOR A RAW PROVER -/

/-- (8) **THE EXPLICIT ENGINE'S INDEX BAD SET AT THE RAW REALIZED RUN IS SECTION 3'S
TARGET AT `committedOf`.**  Both cell families are read off the run: the supplied
one by the adopted `ReducedIndexLanes.used_cell_is_bound_cell` and the definition of
`rawRealizedClaims`, the committed one by `raw_committed_is_history_function`. -/
theorem raw_engine_index_target_is_raw_target (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (T : OracleTable (boundedQueries L)) :
    SoundnessAssembly.indexBadEvent c.indexBits
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell
          (rawRealizedRun L hL c s S U d hbE hbS T).used
          (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
            (hashOf (boundedQueries L) T) khash P c₀) c
            (rawRealizedRun L hL c s S U d hbE hbS T)) cellIndex).1)
        (IndexPointZeroCheck.openedCells (cols cellIndex)
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow
            (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
              (hashOf (boundedQueries L) T) khash P c₀) c
              (rawRealizedRun L hL c s S U d hbE hbS T)) cellIndex)))
      = rawIndexBadTarget c.indexBits U cellIndex (committedOf cols cellIndex)
          (tableView L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T)
          (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T d) := by
  rw [← guarded_is_assembly_index_bad_event, rawIndexBadTarget, used_cell_is_bound_cell,
    raw_committed_is_history_function gdec hash khash P c₀ L hL c s S hS U d hbE hbS hdeg hdb
      cellIndex cols T]
  rfl

open Classical in
/-- **THE EXPLICIT ENGINE'S OWN INDEX BAD EVENT ON THE ORACLE TABLE**, at the raw
realized run: the run's own adopted `SoundnessAssembly.actualIndexDraw` lands in the
adopted `SoundnessAssembly.indexBadEvent` built from the run's own supplied and
committed cells.  `Finset.univ` here is this module's own (see HONESTY (ix)). -/
noncomputable def rawEngineIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c
        (rawRealizedRun L hL c s S U d hbE hbS T)
      ∈ SoundnessAssembly.indexBadEvent c.indexBits
          (OpenedClaimFold.lift (OpenedClaimFold.boundCell
            (rawRealizedRun L hL c s S U d hbE hbS T).used
            (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
              (hashOf (boundedQueries L) T) khash P c₀) c
              (rawRealizedRun L hL c s S U d hbE hbS T)) cellIndex).1)
          (IndexPointZeroCheck.openedCells (cols cellIndex)
            (OpenedClaimFold.lift (OpenedClaimFold.cellRow
              (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
                (hashOf (boundedQueries L) T) khash P c₀) c
                (rawRealizedRun L hL c s S U d hbE hbS T)) cellIndex))))

open Classical in
/-- (8) **THE ENGINE'S OWN INDEX BAD EVENT IS SECTION 3'S RAW INDEX EVENT AT
`committed := committedOf cols cellIndex`.**  Set for set, on the nose. -/
theorem raw_engine_index_bad_event_eq (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hU : ClaimsCausal d U)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) :
    rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS cellIndex cols
      = rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
          (committedOf cols cellIndex) := by
  refine Finset.ext (fun T => ?_)
  rw [rawEngineIndexBadEvent, Finset.mem_filter, mem_raw_index_bad_event]
  simp only [Finset.mem_univ, true_and]
  rw [raw_run_index_draw_is_index_read L hL c s S hS U d hU hbE hbS hdeg T,
    raw_engine_index_target_is_raw_target gdec hash khash P c₀ L hL c s S hS U d hbE hbS
      hdeg hdb cellIndex cols T]


open Classical in
/-- **THE UNION THIS MODULE BOUNDS**: the adopted `RawBlockLanes.rawFullBadEvent` at
the raw extended prover's own chain, union the EXPLICIT ENGINE'S OWN index bad event
at the raw realized run. -/
noncomputable def rawFullEngineIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (logLane gateLane : RawLane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  rawFullBadEvent L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE logLane
      gateLane d rows g coeffsOf
    ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS cellIndex cols

open Classical in
theorem raw_full_engine_index_bad_event_eq (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hU : ClaimsCausal d U)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (logLane gateLane : RawLane) (rows : Nat) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    rawFullEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logLane gateLane
        rows g coeffsOf cellIndex cols
      = rawFullIndexBadEvent L hL c s S U d c.indexBits hbE logLane gateLane rows g coeffsOf
          cellIndex (committedOf cols cellIndex) := by
  rw [rawFullEngineIndexBadEvent, rawFullIndexBadEvent,
    raw_engine_index_bad_event_eq gdec hash khash P c₀ L hL c s S hS U d hU hbE hbS hdeg hdb
      cellIndex cols]

open Classical in
/-- (8) **THE HEADLINE: THE FULL ADAPTIVE BOUND ON THE ENGINE'S OWN EVENTS, FOR A
TRANSCRIPT-RESTRICTED CAUSAL RAW PROVER.**  For EVERY `RoundCausal S` and EVERY `ClaimsCausal d U`, the mass of
the adopted `RawBlockLanes.rawFullBadEvent` UNION THE EXPLICIT ENGINE'S OWN index
bad event at the raw realized run is at most

  `combinedBound d q d constraints + 2 tauTerm c.indexBits + one clash term`.

The index summand is not stated at a modelled `committed` parameter: it is the
engine's own committed family, which `raw_committed_is_history_function` PROVES is a
function of the realized history once the extracted columns are fixed data.

READ THE HONESTY HEADER: this is a good-draw-conditional statement about ONE named
event on the oracle table, not the system's soundness error, acceptance is never
exhibited, and no adaptive Fiat--Shamir soundness is claimed. -/
theorem raw_engine_index_bad_draw_probability_le (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hU : ClaimsCausal d U)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logLane
          gateLane (2 ^ d) g coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  rw [raw_full_engine_index_bad_event_eq gdec hash khash P c₀ L hL c s S hS U d hU hbE hbS
    hdeg hdb logLane gateLane (2 ^ d) g coeffsOf cellIndex cols]
  exact raw_full_index_bad_draw_probability_le_combined L hL c s S U d c.indexBits hU hbE
    logLane gateLane hlcau hgcau q constraints g coeffsOf cellIndex
    (committedOf cols cellIndex) hdu hbu hlog hgate hclen

/-! ## 9. ALL FIVE BOUND CELLS -/

open Classical in
/-- **THE FIVE BOUND CELLS' ENGINE INDEX BAD EVENTS, UNIONED.**  The adopted
`SoundnessAssembly.explicit_good_draw_assembly` takes its index hypothesis at ONE
`cellIndex`; the five cells each need one. -/
noncomputable def rawAllCellsEngineIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S))
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  (((rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 0 cols
    ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 1 cols)
    ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 2 cols)
    ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 3 cols)
    ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 4 cols

open Classical in
/-- **THE UNION OVER ALL FIVE BOUND CELLS.** -/
noncomputable def rawFullAllCellsEngineIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (U : RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (logLane gateLane : RawLane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  rawFullBadEvent L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE logLane
      gateLane d rows g coeffsOf
    ∪ rawAllCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS cols

open Classical in
/-- (9) **THE HEADLINE, AT ALL FIVE BOUND CELLS.**  Five index summands, ONE clash
term: all six masses are conditioned on the SAME no-clash event of the raw extended
chain at its full `22 + 5 d + 8` stages.

  `<= combinedBound d q d constraints + 5 (2 tauTerm c.indexBits) + clash`.

READ THE HONESTY HEADER. -/
theorem raw_engine_index_bad_draw_probability_le_all_cells (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hU : ClaimsCausal d U)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element))
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullAllCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS
          logLane gateLane (2 ^ d) g coeffsOf cols)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 5 * (2 * ChallengeUnionBound.tauTerm c.indexBits)
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hcell : ∀ i : Fin 5,
      rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS i cols
        = rawIndexBadEvent L hL c s S U d c.indexBits hbE i (committedOf cols i) :=
    fun i => raw_engine_index_bad_event_eq gdec hash khash P c₀ L hL c s S hS U d hU hbE hbS
      hdeg hdb i cols
  have hidx : ∀ i : Fin 5, oracleProbability (boundedQueries L)
      (rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS i cols
        ∩ stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE
            (indexStage d))
      ≤ 2 * ChallengeUnionBound.tauTerm c.indexBits := by
    intro i
    rw [hcell i]
    exact raw_index_bad_event_no_clash_mass_le L hL c s S U d c.indexBits hU hbE i
      (committedOf cols i) hbu
  have hfull := raw_full_no_clash_mass_le L hL OuterInitial.zeroDigest
    (rawExtendedShape c s S U d) hbE logLane gateLane hlcau hgcau d q (2 ^ d) constraints g
    coeffsOf hdu hlog hgate hclen
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (rawFullAllCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logLane
        gateLane (2 ^ d) g coeffsOf cols)
      (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE
        (indexStage d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (rawFullAllCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logLane
      gateLane (2 ^ d) g coeffsOf cols
      ∩ stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE
        (indexStage d))
    ((stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE
      (indexStage d))ᶜ)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE
        (indexStage d))ᶜ)
      ≤ ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL OuterInitial.zeroDigest
      (rawExtendedShape c s S U d) hbE (indexStage d)
  have hs1 := inter_union_mass_le L
    (rawFullBadEvent L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE logLane
      gateLane d (2 ^ d) g coeffsOf)
    (rawAllCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS cols)
    (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE (indexStage d))
  have hs2 := inter_union_mass_le L
    (((rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 0 cols
      ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 1 cols)
      ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 2 cols)
      ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 3 cols)
    (rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 4 cols)
    (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE (indexStage d))
  have hs3 := inter_union_mass_le L
    ((rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 0 cols
      ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 1 cols)
      ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 2 cols)
    (rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 3 cols)
    (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE (indexStage d))
  have hs4 := inter_union_mass_le L
    (rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 0 cols
      ∪ rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 1 cols)
    (rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 2 cols)
    (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE (indexStage d))
  have hs5 := inter_union_mass_le L
    (rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 0 cols)
    (rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS 1 cols)
    (stageNoClash L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE (indexStage d))
  have h0 := hidx 0
  have h1 := hidx 1
  have h2 := hidx 2
  have h3 := hidx 3
  have h4 := hidx 4
  rw [ChallengeUnionBound.combinedBound]
  rw [rawFullAllCellsEngineIndexBadEvent, rawAllCellsEngineIndexBadEvent] at hmono hu1 ⊢
  rw [rawAllCellsEngineIndexBadEvent] at hs1
  linarith


/-! ## 10. NON-DEGENERACY: A GENUINELY RAW USED-CLAIMS CHOICE, AND THE GUARD -/

/-- **A USED-CLAIMS CHOICE THAT READS A RAW BLOCK.**  The prover opens `u0` or `u1`
according to the full 256-bit value of the stage-`22` challenge block at counter
`0`.  Stage `22` is NOT `roundStage i` for any `i` -- the round stages start at
`roundStage 0 = 27` -- so the adopted `OuterLaneTransport.reducedHistory` cannot see
this choice at all, and no `ReducedIndexLanes.UsedClaimsStrategy` realizes it.
It obeys `ClaimsCausal d` for every `d`. -/
def blockClaims (u0 u1 : Verifier.UsedClaims) : RawUsedClaims :=
  fun ch => if Transcript.fromLe (ch 22 0).val = 0 then u0 else u1

/-- (10) It obeys the protocol's causality, at every `d`: it reads stage `22`, and
`22 <= 22 + 5 d`. -/
theorem block_claims_causal (u0 u1 : Verifier.UsedClaims) (d : Nat) :
    ClaimsCausal d (blockClaims u0 u1) := by
  intro ch1 ch2 h
  show (if Transcript.fromLe (ch1 22 0).val = 0 then u0 else u1)
    = (if Transcript.fromLe (ch2 22 0).val = 0 then u0 else u1)
  rw [h 22 (by omega)]

/-- (10) Its width budget, at every raw view. -/
theorem block_claims_bounded (u0 u1 : Verifier.UsedClaims) (W : Nat)
    (h0 : u0.logPreprocessed.length ≤ W ∧ u0.logWitness.length ≤ W ∧
      u0.logNormInverse.length ≤ W ∧ u0.gatePreprocessed.length ≤ W ∧
      u0.gateWitness.length ≤ W)
    (h1 : u1.logPreprocessed.length ≤ W ∧ u1.logWitness.length ≤ W ∧
      u1.logNormInverse.length ≤ W ∧ u1.gatePreprocessed.length ≤ W ∧
      u1.gateWitness.length ≤ W) :
    RawUsedClaimsBounded W (blockClaims u0 u1) := by
  intro ch
  by_cases h : Transcript.fromLe (ch 22 0).val = 0
  · have hs : blockClaims u0 u1 ch = u0 := by
      show (if Transcript.fromLe (ch 22 0).val = 0 then u0 else u1) = u0
      rw [if_pos h]
    rw [hs]
    exact h0
  · have hs : blockClaims u0 u1 ch = u1 := by
      show (if Transcript.fromLe (ch 22 0).val = 0 then u0 else u1) = u1
      rw [if_neg h]
    rw [hs]
    exact h1

theorem block_claims_at_probe_zero (u0 u1 : Verifier.UsedClaims) :
    blockClaims u0 u1 (probeView zeroDigestBlock) = u0 := by
  have hv : probeView zeroDigestBlock 22 0 = zeroDigestBlock := by
    show (if (22 : Nat) = 22 then zeroDigestBlock else zeroDigestBlock) = zeroDigestBlock
    rw [if_pos rfl]
  have h0 : Transcript.fromLe (Transcript.le 32 0) = 0 :=
    Transcript.fromLe_le_roundtrip 32 0 (small_lt_byte_power 0 (by norm_num))
  show (if Transcript.fromLe (probeView zeroDigestBlock 22 0).val = 0 then u0 else u1) = u0
  rw [hv]
  show (if Transcript.fromLe (Transcript.le 32 0) = 0 then u0 else u1) = u0
  rw [h0, if_pos rfl]

theorem block_claims_at_probe_one (u0 u1 : Verifier.UsedClaims) :
    blockClaims u0 u1 (probeView oneDigestBlock) = u1 := by
  have hv : probeView oneDigestBlock 22 0 = oneDigestBlock := by
    show (if (22 : Nat) = 22 then oneDigestBlock else zeroDigestBlock) = oneDigestBlock
    rw [if_pos rfl]
  have h1 : Transcript.fromLe (Transcript.le 32 1) = 1 :=
    Transcript.fromLe_le_roundtrip 32 1 (small_lt_byte_power 1 (by norm_num))
  show (if Transcript.fromLe (probeView oneDigestBlock 22 0).val = 0 then u0 else u1) = u1
  rw [hv]
  show (if Transcript.fromLe (Transcript.le 32 1) = 0 then u0 else u1) = u1
  rw [h1, if_neg (by omega)]

/-- (10) **THE USED-CLAIMS CHOICE IS GENUINELY RAW.**  Two raw views that agree at
EVERY round stage -- so the adopted `OuterLaneTransport.reducedHistory` cannot tell
them apart, by the adopted `RawBlockLanes.probe_view_agrees_at_round_stages` -- give
DIFFERENT used claims.  So `ClaimsCausal` is satisfied by a choice that is NOT a
function of the reduced history, and the index half proved above is strictly more
general than the adopted `ReducedIndexLanes` one. -/
theorem block_claims_depends (u0 u1 : Verifier.UsedClaims) (hne : u0 ≠ u1) :
    (∀ i : Nat, probeView zeroDigestBlock (roundStage i)
        = probeView oneDigestBlock (roundStage i)) ∧
      blockClaims u0 u1 (probeView zeroDigestBlock)
        ≠ blockClaims u0 u1 (probeView oneDigestBlock) := by
  refine ⟨fun i => probe_view_agrees_at_round_stages zeroDigestBlock oneDigestBlock i, ?_⟩
  rw [block_claims_at_probe_zero, block_claims_at_probe_one]
  exact hne

open Classical in
/-- (10) **THE GUARD BITES ON THE ENGINE'S OWN EVENT.**  If the extracted columns
open at the row point to exactly the cells the prover supplied, the engine's index
bad event is EMPTY -- so the bound is not a bound on the whole table space by fiat,
and the hypothesis "the index draw misses it" is not refutable. -/
theorem raw_engine_index_bad_event_at_honest_cells (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawUsedClaims) (d : Nat) (hU : ClaimsCausal d U)
    (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hhon : ∀ (ch : Nat → Nat → Block) (xs : List Element),
      committedOf cols cellIndex xs = OpenedClaimFold.lift (usedCell (U ch) cellIndex)) :
    rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS cellIndex cols = ∅ := by
  rw [raw_engine_index_bad_event_eq gdec hash khash P c₀ L hL c s S hS U d hU hbE hbS hdeg hdb
    cellIndex cols]
  refine Finset.eq_empty_of_forall_not_mem (fun T hT => ?_)
  rw [mem_raw_index_bad_event, raw_index_bad_target_at_honest_cells c.indexBits U cellIndex
    (committedOf cols cellIndex) _ _ (hhon _ _)] at hT
  exact absurd hT (Finset.not_mem_empty _)

/-- (10) The row point read off the realized history really has `d` entries -- the
transfer is not about an empty row. -/
theorem raw_realized_row_from_history_length (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawUsedClaims) (d : Nat) (hbE : StrategyBounded L (rawExtendedShape c s S U d))
    (cellIndex : Fin 5) (T : OracleTable (boundedQueries L)) :
    (rowFromHistory cellIndex
        (outerHistory L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T d)).length
      = d := by
  rw [row_from_history_length,
    outer_history_length L hL OuterInitial.zeroDigest (rawExtendedShape c s S U d) hbE T d]
  omega

/-! ## 11. THE CLOSED INSTANCES AT THIRTEEN ROUNDS AND EIGHT INDEX BITS -/

/-- (11) The length budget of the raw extended prover at the genuinely raw
`StrategyChainBound.challengeTruncatedMessage`, discharged. -/
theorem truncated_raw_extended_bounded (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage) (U : RawUsedClaims) (W : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hU : RawUsedClaimsBounded W U) (hLq : 189 + 24 * 8 ≤ L) (hLW : 69 + 24 * W ≤ L)
    (hdom : 86 ≤ L) :
    StrategyBounded L (rawExtendedShape c s (challengeTruncatedMessage m) U 13) :=
  raw_extended_shape_bounded L c s (challengeTruncatedMessage m) U 13 8 W hpre
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hmlog)
    (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
    hU hLq hLW hdom

open Classical in
/-- (11) **THE CLOSED INSTANCE.**  Thirteen coupled rounds, `quotientDegree = 8`,
`numGateConstraints = 123`, `indexBits = 8`, the adopted genuinely raw
`StrategyChainBound.challengeTruncatedMessage` as the round-message choice -- the
very prover the adopted `OuterLaneTransport` header names as unpairable with a
`Lane` -- and `blockClaims u0 u1`, a used-claims choice the reduced history cannot
see, at ONE bound cell.  The index summand is the EXPLICIT ENGINE'S OWN index bad
event at the raw realized run.

  `<= combinedBound 13 8 13 123 + 2 * tauTerm 8 + 4560 / |Block|`.

Neither `StrategyBounded` nor `64 <= L` nor either counter budget is left as a
hypothesis.  READ THE HONESTY HEADER: THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR. -/
theorem raw_index_engine_bound_at_thirteen (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage) (u0 u1 : Verifier.UsedClaims)
    (W : Nat) (a1 b1 a2 b2 : Element) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hc13 : c.degreeBits = 13) (hcidx : c.indexBits = 8)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (h0 : u0.logPreprocessed.length ≤ W ∧ u0.logWitness.length ≤ W ∧
      u0.logNormInverse.length ≤ W ∧ u0.gatePreprocessed.length ≤ W ∧
      u0.gateWitness.length ≤ W)
    (h1 : u1.logPreprocessed.length ≤ W ∧ u1.logWitness.length ≤ W ∧
      u1.logNormInverse.length ≤ W ∧ u1.gatePreprocessed.length ≤ W ∧
      u1.gateWitness.length ≤ W)
    (hLq : 189 + 24 * 8 ≤ L) (hLW : 69 + 24 * W ≤ L) (hdom : 86 ≤ L) :
    oracleProbability (boundedQueries L)
        (rawFullEngineIndexBadEvent gdec hash khash P c₀ L (Nat.le_trans (by omega) hLq) c s
          (challengeTruncatedMessage m) (blockClaims u0 u1) 13
          (truncated_raw_extended_bounded L c s m (blockClaims u0 u1) W hpre hmlog hmgate
            (block_claims_bounded u0 u1 W h0 h1) hLq hLW hdom)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
          (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a1 b1)
          (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a2 b2)
          (2 ^ 13) g coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 2 * ChallengeUnionBound.tauTerm 8 + 4560 / (Fintype.card Block : ℚ) := by
  have h := raw_engine_index_bad_draw_probability_le gdec hash khash P c₀ L
    (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
    (challenge_truncated_round_causal m) (blockClaims u0 u1) 13
    (block_claims_causal u0 u1 13)
    (truncated_raw_extended_bounded L c s m (blockClaims u0 u1) W hpre hmlog hmgate
      (block_claims_bounded u0 u1 W h0 h1) hLq hLW hdom)
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
    hc13 (by omega)
    (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a1 b1)
    (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a2 b2)
    (raw_log_lane_causal (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
      rawZeroTruth raw_zero_truth_causal a1 b1)
    (raw_gate_lane_causal (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
      rawZeroTruth raw_zero_truth_causal a2 b2)
    8 123 g coeffsOf cellIndex cols ReducedFullTransport.thirteen_counter_budget
    (by rw [hcidx]; exact eight_index_counter_budget)
    (raw_log_lane_bounded (challengeTruncatedMessage m) rawZeroTruth a1 b1 5
      (fun r ch => by
        rw [(challenge_truncated_message_lengths m r ch).1]
        exact hmlog)
      (raw_zero_truth_length 5))
    (raw_gate_lane_bounded (challengeTruncatedMessage m) rawZeroTruth a2 b2 (8 + 2)
      (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
      (raw_zero_truth_length (8 + 2))) hclen
  rw [hcidx] at h
  have harith : ((indexStage 13 : Nat) : ℚ) * (((indexStage 13 : Nat) : ℚ) + 1) / 2
      = 4560 := by
    rw [index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

/-- (11) The closed constant is strictly below `1`; inherited verbatim from the
adopted `ReducedIndexLanes.full_index_bound_at_thirteen_lt_one`. -/
theorem raw_index_engine_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) < 1 :=
  full_index_bound_at_thirteen_lt_one

open Classical in
/-- (11) **THE CLOSED INSTANCE AT ALL FIVE BOUND CELLS.**  Same genuinely raw
prover, same genuinely raw used-claims choice, five index summands, one clash term:

  `<= combinedBound 13 8 13 123 + 5 (2 tauTerm 8) + 4560 / |Block|`. -/
theorem raw_index_engine_bound_at_thirteen_all_cells (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage) (u0 u1 : Verifier.UsedClaims)
    (W : Nat) (a1 b1 a2 b2 : Element) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element))
    (hc13 : c.degreeBits = 13) (hcidx : c.indexBits = 8)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (h0 : u0.logPreprocessed.length ≤ W ∧ u0.logWitness.length ≤ W ∧
      u0.logNormInverse.length ≤ W ∧ u0.gatePreprocessed.length ≤ W ∧
      u0.gateWitness.length ≤ W)
    (h1 : u1.logPreprocessed.length ≤ W ∧ u1.logWitness.length ≤ W ∧
      u1.logNormInverse.length ≤ W ∧ u1.gatePreprocessed.length ≤ W ∧
      u1.gateWitness.length ≤ W)
    (hLq : 189 + 24 * 8 ≤ L) (hLW : 69 + 24 * W ≤ L) (hdom : 86 ≤ L) :
    oracleProbability (boundedQueries L)
        (rawFullAllCellsEngineIndexBadEvent gdec hash khash P c₀ L
          (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
          (blockClaims u0 u1) 13
          (truncated_raw_extended_bounded L c s m (blockClaims u0 u1) W hpre hmlog hmgate
            (block_claims_bounded u0 u1 W h0 h1) hLq hLW hdom)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
          (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a1 b1)
          (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a2 b2)
          (2 ^ 13) g coeffsOf cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 5 * (2 * ChallengeUnionBound.tauTerm 8) + 4560 / (Fintype.card Block : ℚ) := by
  have h := raw_engine_index_bad_draw_probability_le_all_cells gdec hash khash P c₀ L
    (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
    (challenge_truncated_round_causal m) (blockClaims u0 u1) 13
    (block_claims_causal u0 u1 13)
    (truncated_raw_extended_bounded L c s m (blockClaims u0 u1) W hpre hmlog hmgate
      (block_claims_bounded u0 u1 W h0 h1) hLq hLW hdom)
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
    hc13 (by omega)
    (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a1 b1)
    (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a2 b2)
    (raw_log_lane_causal (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
      rawZeroTruth raw_zero_truth_causal a1 b1)
    (raw_gate_lane_causal (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
      rawZeroTruth raw_zero_truth_causal a2 b2)
    8 123 g coeffsOf cols ReducedFullTransport.thirteen_counter_budget
    (by rw [hcidx]; exact eight_index_counter_budget)
    (raw_log_lane_bounded (challengeTruncatedMessage m) rawZeroTruth a1 b1 5
      (fun r ch => by
        rw [(challenge_truncated_message_lengths m r ch).1]
        exact hmlog)
      (raw_zero_truth_length 5))
    (raw_gate_lane_bounded (challengeTruncatedMessage m) rawZeroTruth a2 b2 (8 + 2)
      (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
      (raw_zero_truth_length (8 + 2))) hclen
  rw [hcidx] at h
  have harith : ((indexStage 13 : Nat) : ℚ) * (((indexStage 13 : Nat) : ℚ) + 1) / 2
      = 4560 := by
    rw [index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

/-- (11) And the five-cell constant is still strictly below `1`, by the adopted
evaluations: the adopted three-term envelope is at most `2 ^ (-172)`, five index
terms at most `5 / 2 ^ 185`, the clash term at most `2 ^ (-243)`.
`Fintype.card Block` is never evaluated.  READ HONESTY (vii). -/
theorem raw_index_engine_bound_at_thirteen_all_cells_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 5 * (2 * ChallengeUnionBound.tauTerm 8)
        + 4560 / (Fintype.card Block : ℚ) < 1 :=
  engine_index_bound_at_thirteen_all_cells_lt_one

end Audit.Wire3.RawIndexLanes
