import Audit.Wire3.EngineOuterDiagonal

/-!
# THE LANE-LIST IDENTIFICATION, AND THE ADAPTIVE ASSEMBLY-FAILURE EVENT

## THE GAP THIS MODULE CLOSES -- READ THIS FIRST

The adopted `EngineOuterDiagonal` closed the OUTER alpha diagonal for the adaptive
line and named, under "THE PRECISE REMAINING STEP", exactly one leg it did not
close:

> THE LANE-LIST IDENTIFICATION.  `realizedRounds ... (gateF a) 3 T 0 d` would have
> to be `ConditionalSoundness.gateLaneOf E c (realizedRunProof ... T) gateTruths`,
> and `realizedRounds ... (logF a) 0 T 0 d` the matching `logLaneOf` list.  The
> lengths already agree (the adopted
> `RunLevelTransportAudit.realized_rounds_length`); what is NOT proved anywhere is
> the identification of the two lists' `message` and `truth` FIELDS round by
> round.

Section 1 proves exactly that, and section 2 draws the consequence the adopted
header said was blocked by it: the adopted
`EngineOuterDiagonal.rawEngineAllOwnBadEvent`, at this module's engine families,
IS the event "the run's own joint draw lands in the adopted
`SoundnessAssembly.outerBadEvent`".  Section 3 is the adaptive analogue of the
adopted `RunLevelUnionBound.assembly_failure_subset_run_union` and of the adopted
`IndexStageFinerSplit.assembly_failure_mass_le_unconditional`.

## WHY THE IDENTIFICATION IS TRUE, AND WHERE THE WORK IS

Both sides are read off the SAME two pieces of data.

* THE MESSAGES.  The adopted `ConditionalSoundness.lane` reads round `k`'s message
  as `(sel m).map OuterRound.lift` off the `k`-th entry of `p.logRounds.zip
  p.gateRounds`, and at `p := RunLevelTransportAudit.realizedRunProof` that list IS
  the adopted `StrategyChainBound.realizedMessages` (the adopted
  `RunLevelTransportAudit.realized_run_proof_round_messages`), i.e. the adopted
  `messagesFrom` of the strategy's own round function.  The adopted
  `RunLevelTransportAudit.realizedRounds` reads round `k`'s message as
  `lane.message k (tableView ...)`, and at the adopted
  `RawBlockLanes.rawGateLaneOfStrategy` that is the same lifted cell by the adopted
  `RawBlockLanes.raw_gate_lane_message_is_realized` / its log twin.
* THE TRUTHS.  The adopted `lane` reads round `k`'s truth as entry `k` of the
  SUPPLIED list (`truths.headD []`, with `truths.tail` per round).  This module's
  `truthColumn` is that column as a raw lane's free `truth` field; it reads no
  challenge, so it is `RawBlockLanes.RawCausal` outright.
* THE CHALLENGES ARE NOT MATCHED, AND DO NOT HAVE TO BE.  `frozen_lane_congr`
  proves that the adopted `AdaptiveAgreementFamily.frozenLane` is a function of the
  round list's `message`/`truth` projection alone.  That is the adopted
  `EngineOuterDiagonal` note ("the `challenge` field is NOT part of what has to be
  matched") turned into a theorem.

The whole of section 1 is therefore two structural inductions (`lane_map_is_data_rounds`,
`realized_rounds_map_is_data_rounds`) into a common normal form `dataRounds`, plus a
congruence.  No transcript state is threaded: the projection never reads it.

## WHAT IS PROVED

1. SECTION 0/1.  `frozen_lane_congr`; `truthColumn` and its causality and degree
   bounds; `realized_gate_rounds_are_engine_gate_lane` and
   `realized_log_rounds_are_constant_log_lane` -- THE NAMED LEG.  The engine `E` is
   FREE in both: it reaches the adopted `gateLaneOf`/`logLaneOf` only through the
   `challenge` field.
2. SECTION 2.  `assembly_gate_lane_is_frozen_realized` /
   `assembly_log_lane_is_frozen_realized` (the adopted `SoundnessAssembly.gateLane`
   / `logLane` ARE the frozen lanes of the realized rounds),
   `engine_outer_bad_event_is_assembly_adaptive_outer_event` (the outer summand),
   and `engine_all_own_bad_event_is_assembly_outer_bad_event` -- THE EVENT
   IDENTITY, `Finset` for `Finset`.  The engine's transcript-hash argument is
   absorbed exactly as the adopted
   `TwoStageConditionalCount.explicit_outer_bad_event_is_the_family` absorbs it for
   a fixed prover: it reaches the outer event only through challenge values and the
   alpha, and `enginePublicHash` / `engine_public_hash_is_hash_free` show the
   public-hash argument does not move with it at all.  The tau summand is the
   adopted `EngineTauDiagonal.engineTauBadEvent` at the adopted `engineGate`
   (`alpha_read_is_gate_alpha_element`); the alpha summand is the adopted
   `ReducedFullTransport.gateAlphaBadEvent`, which mentions no challenge.
3. SECTION 3.  `adaptiveAssemblyFailureEvent`, `adaptiveIndexBadEvent`,
   `adaptive_assembly_failure_subset` (a `Finset` inclusion with NO hypothesis) and
   `adaptive_assembly_failure_mass_le`:

     `<= combinedBound degreeBits q degreeBits constraints + ONE clash term
        + (the mass of the index half)`.

4. SECTION 4.  `adaptive_index_bad_event_subset_live_guard` (the index half is
   contained in the tables at which the adopted
   `IndexPointZeroCheck.CellsDifferOnCube` guard is LIVE -- honest openings
   contribute nothing), `adaptive_assembly_bound_at_thirteen_lt_one`,
   `adaptive_payoff_hypotheses_satisfiable` and `truth_column_at_empty_list`.

## WHAT REMAINS `∀`-QUANTIFIED OR ASSUMED

Precisely, and nothing is hidden:

* `tables = s0.tables` -- the adopted `CommitmentOrder` / `CommitmentOrderSurvey`
  `CommittedTables` extraction join, inherited VERBATIM from the adopted
  `EngineTauDiagonal` HONESTY (iii) and not strengthened.  The tau summand's
  zero-check table is `EngineTauDiagonal.engineGate c gates publicHash s0.tables`,
  so `tables` is READ OFF the supplied `s0` here; that is the same join in another
  guise, not a new one.
* `coeffsOf` -- a free family.  The adopted
  `CommitmentOrderSurvey.coefficients_are_determined_by_the_tables` makes the alpha
  summand a function of the TABLES alone only UNDER its own premise
  `∀ i, i < rows → prefixCoeffTable c gates publicHash t i = some (coeffsOf i)`,
  which is not assumed anywhere below.
* `logTruths` / `gateTruths` -- the SUPPLIED truth columns of the adopted
  `SoundnessAssembly.outerBadEvent`.  FREE DATA, not the engine's derived values;
  this module's `truthColumn` models exactly that freedom.
* R1b -- the adopted honest-openings relation, inside the adopted
  `SoundnessAssembly.AssemblyResidue`.  Neither used nor strengthened here.
* ACCEPTANCE IS NEVER EXHIBITED.  No accepting proof for the explicit engine is
  produced anywhere below; `adaptiveAssemblyFailureEvent` is a set defined by a
  NEGATED implication, so it is well defined whether or not any table accepts.
* THE FAILURE EVENT IS EMPTY AT EVERY NON-DEGENERATE CONFIGURATION.
  `adaptiveAssemblyFailureEvent` carries ACCEPTANCE as a conjunct: it is the
  negation of an implication whose antecedent is `Integrated.verify ... =
  Except.ok ()`.  The adopted `Integrated.verify` ends in `Verifier.verify`
  (`Integrated.lean:59-66`), which rejects unless `Verifier.shape pin c p = true`
  (`Verifier.lean:415`), and `Verifier.shape` demands
  `p.used.logPreprocessed.length = c.numConstants + c.numRouted`,
  `p.used.logWitness.length = c.numWires` and
  `p.used.logNormInverse.length = 2 * c.numRouted` (`Verifier.lean:139-141`).  The
  proof record this module quantifies over is
  `RunLevelTransportAudit.realizedRunProof`, whose `used` field is the untouched
  `Verifier.testProof.used` of lengths `1, 1, 0` (`Verifier.lean:596-600`,
  `RunLevelTransportAudit.lean:582-587`).  Acceptance therefore forces
  `numRouted = 0`, `numConstants = 1` and `numWires = 1`.  AT EVERY OTHER
  CONFIGURATION `adaptiveAssemblyFailureEvent = ∅` AND EVERY BOUND BELOW IS
  VACUOUSLY TRUE, including the closed instance `adaptive_assembly_bound_at_thirteen`
  -- the adopted `IndexHalfTransport` records this as
  `adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`.  `degreeBits`
  and `numPublicInputs` are NOT pinned by this (`logRounds`, `gateRounds` and
  `publicInputs` are overridden by the adopted `realizedProof`), and at the
  degenerate configuration `Verifier.width c = 1`, so the fixture's
  `constituentWidth := 1` adds no further pin.  WHEREVER THIS MODULE SAYS ITS
  HYPOTHESES ARE SATISFIABLE AND THEREFORE THAT NOTHING IS VACUOUS, THAT INFERENCE
  IS INVALID: hypothesis satisfiability is not non-emptiness of the bounded event.
  To obtain a non-vacuous statement the used claims must be a PARAMETER of the
  event, as in the adopted `IndexHalfTransport.adaptiveAssemblyFailureEventWith`.
* THE INDEX HALF'S MASS.  The adopted `RawIndexLanes` weighs the index event at the
  adopted `rawRealizedRun` -- the EXTENDED-shape chain, a proof record differing
  from `realizedRunProof` in its `used` field.  This module therefore carries the
  index term as an unevaluated `oracleProbability` and states NO bound for it.
  THAT IS THE ONE STEP STILL OWED for a single-constant adaptive payoff, and it is
  a transport between two proof records at one strategy, not a new probabilistic
  argument.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`.  Replacing
the deployed permutation by a table drawn from that law is an assumption with no
proof anywhere in this tree.

(ii) THE PROVER CLASS.  TRANSCRIPT-RESTRICTED CAUSAL: every statement about a
strategy below is at the adopted `RawBlockLanes.strategicShape` for an arbitrary
`StrategyChainBound.RoundCausal S`, a prover handed the stage digests of its own
chain and the oracle's answers at the CHALLENGE inputs of those digests, making no
oracle queries of its own.  GRINDING IS EXCLUDED by every theorem below.

(iii) THE ENGINE IS EXPLICIT, AT THE REALIZED RUN.  Sections 2 and 3 are stated at
`SoundnessAssembly.engine gdec hash (hashOf T) khash P c₀` -- the table's OWN hash --
and at `RunLevelTransportAudit.realizedRunProof`, the proof the prover actually
submits at that table.  Nothing below quantifies a proof outside the law.

(iv) WHAT THE ASSEMBLY CONCLUSION IS.  GOOD-DRAW-CONDITIONAL CONSTRAINT VANISHING
ON THE EXTRACTED TABLES, plus a per-column identification, plus the pinned WHIR
parameter row and the `core c = core c₀` / `KhashCollision` disjunction.  IT IS NOT
CIRCUIT TRUTH, and it is not a satisfiability claim.

(v) R1b, AND ACCEPTANCE.  The opened-claim relation in force upstream is the
adopted R1b honest-openings relation, carried inside the adopted
`SoundnessAssembly.AssemblyResidue`; this module neither uses nor strengthens it.
No accepting run is exhibited.

(vi) WHIR AND MERKLE ARE EXCLUDED, AND THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS
ERROR.  `combinedBound` covers the outer sumcheck round-agreement events, the gate
tau multilinear zero check and the gate alpha zero check only.  The WHOLE
WHIR/Merkle contribution -- proximity and list decoding, the query-repetition
profile, Merkle collision resistance -- is EXCLUDED, and it is the dominant term.
Quoting the constant of section 4 as the wire-v3 soundness error would be wrong by
roughly seventy bits.  NOTHING BELOW IS A CLAIM THAT FIAT--SHAMIR SOUNDNESS HAS
BEEN PROVED FOR AN ADAPTIVE PROVER: the Fiat--Shamir half -- that the run's
encoding draw is `JointChallengeSpace.jointProbability`-distributed -- remains
exactly as unformalized as the adopted `JointChallengeSpace.DrawEncodesRun` header
says.

(vii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's OWN
definitions (`adaptiveEngineOuterBadEvent`, `adaptiveIndexBadEvent`,
`adaptiveAssemblyFailureEvent`) and in the STATEMENT of
`adaptive_index_bad_event_subset_live_guard`, which spells a filter over the table
space out; through the generic `Finset.mem_univ` it also appears in a few proofs.
No tactic or term below ever puts `Finset.univ` on `Element` or on
`OuterChallenge.DigestTriple` in a reducible position, and NO `Nat` OR `ℚ`
ARITHMETIC TACTIC BELOW IS EVER SHOWN A `Fintype.card` OF ANY OF THEM: the one
`linarith` that meets `Fintype.card Block` is fed the adopted
`BirthdayClashBound.block_card_cast_pos` and the cardinality never leaves the
atom.  No membership over `OuterChallenge.DigestTriple` at a CONCRETE lane is
elaborated anywhere.  `open Classical in` is used for the declarations whose
statements mention membership in a `Finset` over the table space, exactly as the
adopted `RawBlockLanes`, `EngineTauDiagonal` and `EngineOuterDiagonal` do; the one
`simp only`-based unfolding of a filter (`adaptive_assembly_failure_subset`) is
preceded by `classical`, exactly as the adopted
`RunLevelUnionBound.assembly_failure_subset_run_union` is, because the failure
predicate is a negated implication.  `ChallengeUnionBound.combinedBound` and
`tauTerm` are never evaluated.  The closed instance of section 4 mentions `13`
literally, as the adopted `EngineOuterDiagonal` section-5 instances do.
-/

namespace Audit.Wire3.AdaptiveAssemblyFailure

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.RawBlockLanes
open Audit.Wire3.EngineOuterDiagonal

/-! ## 0. THE PROJECTION THE FROZEN WALK CONSUMES -/

/-- The only two fields of a `ConditionalSoundness.LaneRound` that the adopted
`AdaptiveAgreementFamily.frozenLane` reads. -/
def laneData (r : ConditionalSoundness.LaneRound) : List Element × List Element :=
  (r.message, r.truth)

theorem option_map_message (o1 o2 : Option ConditionalSoundness.LaneRound)
    (h : o1.map laneData = o2.map laneData) :
    o1.map ConditionalSoundness.LaneRound.message
      = o2.map ConditionalSoundness.LaneRound.message := by
  cases o1 with
  | none => cases o2 with
    | none => rfl
    | some b => simp [laneData] at h
  | some a => cases o2 with
    | none => simp [laneData] at h
    | some b =>
      have hab : laneData a = laneData b := by simpa using h
      exact congrArg some (congrArg Prod.fst hab)

theorem option_map_truth (o1 o2 : Option ConditionalSoundness.LaneRound)
    (h : o1.map laneData = o2.map laneData) :
    o1.map ConditionalSoundness.LaneRound.truth
      = o2.map ConditionalSoundness.LaneRound.truth := by
  cases o1 with
  | none => cases o2 with
    | none => rfl
    | some b => simp [laneData] at h
  | some a => cases o2 with
    | none => simp [laneData] at h
    | some b =>
      have hab : laneData a = laneData b := by simpa using h
      exact congrArg some (congrArg Prod.snd hab)

theorem get_map_laneData : ∀ (l : List ConditionalSoundness.LaneRound) (n : Nat),
    (l.map laneData).get? n = (l.get? n).map laneData
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: as, n + 1 => get_map_laneData as n

theorem get_laneData (rs1 rs2 : List ConditionalSoundness.LaneRound)
    (h : rs1.map laneData = rs2.map laneData) (n : Nat) :
    (rs1.get? n).map laneData = (rs2.get? n).map laneData := by
  rw [← get_map_laneData, ← get_map_laneData, h]

/-- **THE FROZEN LANE READS ONLY `message` AND `truth`.**  Two round lists with
the same `laneData` projection give the SAME adopted
`AdaptiveAgreementFamily.frozenLane`, whatever their `challenge` fields are.  This
is the reason the lane-list identification of section 1 does not have to match
challenges. -/
theorem frozen_lane_congr (rs1 rs2 : List ConditionalSoundness.LaneRound) (a b : Element)
    (own : Bool) (h : rs1.map laneData = rs2.map laneData) :
    AdaptiveAgreementFamily.frozenLane rs1 a b own
      = AdaptiveAgreementFamily.frozenLane rs2 a b own := by
  refine AdaptiveAgreementFamily.lane_eq _ _ (funext fun xs => ?_) (funext fun xs => ?_)
    rfl rfl rfl
  · show ((rs1.get? (AdaptiveAgreementFamily.halfLength xs)).map
        ConditionalSoundness.LaneRound.message).getD []
      = ((rs2.get? (AdaptiveAgreementFamily.halfLength xs)).map
        ConditionalSoundness.LaneRound.message).getD []
    rw [option_map_message _ _ (get_laneData rs1 rs2 h _)]
  · show ((rs1.get? (AdaptiveAgreementFamily.halfLength xs)).map
        ConditionalSoundness.LaneRound.truth).getD []
      = ((rs2.get? (AdaptiveAgreementFamily.halfLength xs)).map
        ConditionalSoundness.LaneRound.truth).getD []
    rw [option_map_truth _ _ (get_laneData rs1 rs2 h _)]

/-! ## 1. THE LANE-LIST IDENTIFICATION -/

/-- The `message`/`truth` data of a lane, round by round, from round `k` on. -/
def dataRounds (M Tr : Nat → List Element) : Nat → Nat → List (List Element × List Element)
  | _, 0 => []
  | k, n + 1 => (M k, Tr k) :: dataRounds M Tr (k + 1) n

theorem data_rounds_succ (M Tr : Nat → List Element) (k n : Nat) :
    dataRounds M Tr k (n + 1) = (M k, Tr k) :: dataRounds M Tr (k + 1) n := rfl

theorem data_rounds_congr (M1 Tr1 M2 Tr2 : Nat → List Element)
    (hM : ∀ j, M1 j = M2 j) (hT : ∀ j, Tr1 j = Tr2 j) :
    ∀ (n k : Nat), dataRounds M1 Tr1 k n = dataRounds M2 Tr2 k n
  | 0, _ => rfl
  | n + 1, k => by
      rw [data_rounds_succ, data_rounds_succ, hM k, hT k, data_rounds_congr M1 Tr1 M2 Tr2 hM hT n]

theorem tail_drop : ∀ (l : List (List Element)) (k : Nat), (l.drop k).tail = l.drop (k + 1)
  | [], 0 => rfl
  | _ :: _, 0 => rfl
  | [], _ + 1 => rfl
  | _ :: as, k + 1 => tail_drop as k

theorem lane_cons (commit : Verifier.CommitRound)
    (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3) (truths : List (List Element))
    (st : Verifier.RoundState) (m : Verifier.CoupledMessage)
    (ms : List Verifier.CoupledMessage) :
    ConditionalSoundness.lane commit sel pick truths st (m :: ms)
      = (⟨(sel m).map OuterRound.lift, truths.headD [],
          OuterRound.lift (pick (commit st.transcript st.roundIndex m.1 m.2))⟩ :
            ConditionalSoundness.LaneRound) ::
        ConditionalSoundness.lane commit sel pick truths.tail
          (Verifier.roundStep commit st m) ms := rfl

/-- (1) **THE ADOPTED `ConditionalSoundness.lane`, PROJECTED.**  Read off a
message list that is the adopted `StrategyChainBound.messagesFrom` of a
round-indexed message function, the lane's `message`/`truth` data is exactly the
lifted selected cell of round `j` paired with entry `j` of the SUPPLIED truth
list.  The round STATE is carried through untouched: the projection never reads
it. -/
theorem lane_map_is_data_rounds (commit : Verifier.CommitRound)
    (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3)
    (f : Nat → Verifier.CoupledMessage) (truths : List (List Element)) :
    ∀ (n k : Nat) (st : Verifier.RoundState),
      (ConditionalSoundness.lane commit sel pick (truths.drop k) st
          (messagesFrom f k n)).map laneData
        = dataRounds (fun j => (sel (f j)).map OuterRound.lift)
            (fun j => (truths.drop j).headD []) k n
  | 0, _, _ => rfl
  | n + 1, k, st => by
      show ((⟨(sel (f k)).map OuterRound.lift, (truths.drop k).headD [],
          OuterRound.lift (pick (commit st.transcript st.roundIndex (f k).1 (f k).2))⟩ :
            ConditionalSoundness.LaneRound) ::
          ConditionalSoundness.lane commit sel pick (truths.drop k).tail
            (Verifier.roundStep commit st (f k)) (messagesFrom f (k + 1) n)).map laneData
        = dataRounds (fun j => (sel (f j)).map OuterRound.lift)
            (fun j => (truths.drop j).headD []) k (n + 1)
      rw [tail_drop truths k, List.map_cons, data_rounds_succ,
        lane_map_is_data_rounds commit sel pick f truths n (k + 1)
          (Verifier.roundStep commit st (f k))]
      rfl

/-- (1) **THE ADOPTED `RunLevelTransportAudit.realizedRounds`, PROJECTED.**  Its
`message`/`truth` data is the raw lane's two fields at the adopted
`RawBlockLanes.tableView`, round index by round index. -/
theorem realized_rounds_map_is_data_rounds (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ (n k : Nat),
      (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane base T k n).map laneData
        = dataRounds (fun j => lane.message j (tableView L hL e0 strat hb T))
            (fun j => lane.truth j (tableView L hL e0 strat hb T)) k n
  | 0, _ => rfl
  | n + 1, k => by
      rw [RunLevelTransportAudit.realized_rounds_cons, List.map_cons, data_rounds_succ,
        realized_rounds_map_is_data_rounds L hL e0 strat hb lane base T n (k + 1)]
      rfl

/-! ### 1.1 The truth column as a raw lane's `truth` field -/

/-- **THE SUPPLIED TRUTH LIST, AS A RAW LANE'S FREE `truth` FIELD.**  Round `k`
reads entry `k` of the adopted `SoundnessAssembly.outerBadEvent`'s SUPPLIED truth
list, exactly as the adopted `ConditionalSoundness.lane` does, and reads NO
challenge. -/
def truthColumn (truths : List (List Element)) : Nat → (Nat → Nat → Block) → List Element :=
  fun k _ => (truths.drop k).headD []

theorem truth_column_causal (truths : List (List Element)) : RawCausal (truthColumn truths) :=
  fun _ _ _ _ => rfl

theorem head_drop_cases (l : List (List Element)) :
    ∀ (k : Nat), (l.drop k).headD [] = [] ∨ (l.drop k).headD [] ∈ l
  | 0 => by
      cases l with
      | nil => exact Or.inl rfl
      | cons a as => exact Or.inr (List.mem_cons_self _ _)
  | k + 1 => by
      cases l with
      | nil => exact Or.inl rfl
      | cons a as =>
        rcases head_drop_cases as k with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem truth_column_length (truths : List (List Element)) (bd : Nat)
    (h : ∀ u ∈ truths, u.length ≤ bd) (k : Nat) (ch : Nat → Nat → Block) :
    (truthColumn truths k ch).length ≤ bd := by
  rcases head_drop_cases truths k with hk | hk
  · show ((truths.drop k).headD []).length ≤ bd
    rw [hk]
    exact Nat.zero_le _
  · exact h _ hk

/-! ### 1.2 The two families -/

/-- **THE ENGINE'S OWN ALPHA-INDEXED GATE LANE AT THE SUPPLIED TRUTH COLUMN.**
The adopted `EngineOuterDiagonal.engineGateLaneOfStrategy` with the free `truth`
field instantiated at `truthColumn`. -/
def engineGateLane (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (gateTruths : List (List Element)) (B : Element → Element) : Element → RawLane :=
  engineGateLaneOfStrategy S (truthColumn gateTruths) B

/-- **THE LOG FAMILY, CONSTANT IN THE ALPHA**, at the supplied truth column. -/
def constantLogLane (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (logTruths : List (List Element)) (b : Element) : Element → RawLane :=
  constantLogLaneOfStrategy S (truthColumn logTruths) b

theorem engine_gate_lane_causal (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (gateTruths : List (List Element)) (B : Element → Element) :
    AlphaRawLaneCausal (engineGateLane S gateTruths B) :=
  engine_gate_lane_of_strategy_causal S hS (truthColumn gateTruths)
    (truth_column_causal gateTruths) B

theorem constant_log_lane_causal (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (logTruths : List (List Element)) (b : Element) :
    AlphaRawLaneCausal (constantLogLane S logTruths b) :=
  constant_log_lane_of_strategy_causal S hS (truthColumn logTruths)
    (truth_column_causal logTruths) b

theorem engine_gate_lane_bounded (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (gateTruths : List (List Element)) (B : Element → Element) (bd : Nat)
    (hS : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ bd)
    (ht : ∀ u ∈ gateTruths, u.length ≤ bd) :
    AlphaRawLaneBounded (engineGateLane S gateTruths B) bd :=
  engine_gate_lane_of_strategy_bounded S (truthColumn gateTruths) B bd hS
    (truth_column_length gateTruths bd ht)

theorem constant_log_lane_bounded (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (logTruths : List (List Element)) (b : Element) (bd : Nat)
    (hS : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ bd)
    (ht : ∀ u ∈ logTruths, u.length ≤ bd) :
    AlphaRawLaneBounded (constantLogLane S logTruths b) bd :=
  constant_log_lane_of_strategy_bounded S (truthColumn logTruths) b bd hS
    (truth_column_length logTruths bd ht)

/-! ### 1.3 THE IDENTIFICATION ITSELF -/

/-- (1) **THE NAMED LEG OF THE ADOPTED `EngineOuterDiagonal`'s "PRECISE REMAINING
STEP", GATE SIDE.**  The adopted `RunLevelTransportAudit.realizedRounds` of this
module's alpha-indexed engine gate family and the adopted
`ConditionalSoundness.gateLaneOf` of the adopted
`RunLevelTransportAudit.realizedRunProof` carry THE SAME `message` AND `truth`
DATA, round by round -- the projection the adopted
`AdaptiveAgreementFamily.frozenLane` consumes (`frozen_lane_congr`).  `E` IS FREE:
the engine reaches `gateLaneOf` only through the `challenge` field, which is not
part of the projection. -/
theorem realized_gate_rounds_are_engine_gate_lane (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hbS : StrategyBounded L (strategicShape c s S)) (gateTruths : List (List Element))
    (B : Element → Element) (a : Element) (E : Verifier.Engine) (d : Nat)
    (T : OracleTable (boundedQueries L)) :
    (RunLevelTransportAudit.realizedRounds L hL OuterInitial.zeroDigest (strategicShape c s S)
        hbS (engineGateLane S gateTruths B a) 3 T 0 d).map laneData
      = (ConditionalSoundness.gateLaneOf E c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T) gateTruths).map
        laneData := by
  have hms : ConditionalSoundness.gateLaneOf E c
      (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T) gateTruths
        = ConditionalSoundness.lane E.commitRound Prod.snd Verifier.RoundChallenges.gate
            (gateTruths.drop 0)
            (Verifier.start (E.initialTranscript c
              (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T)))
            (messagesFrom (fun r => S r (strategicChallenges L hL c s S hbS r T)) 0 d) := by
    show ConditionalSoundness.lane E.commitRound Prod.snd Verifier.RoundChallenges.gate
        gateTruths
        (Verifier.start (E.initialTranscript c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T)))
        (roundMessages (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T)) = _
    rw [RunLevelTransportAudit.realized_run_proof_round_messages]
    rfl
  rw [hms, lane_map_is_data_rounds, realized_rounds_map_is_data_rounds]
  refine data_rounds_congr _ _ _ _ (fun j => ?_) (fun _ => rfl) d 0
  exact raw_gate_lane_message_is_realized L hL c s S hS hbS (truthColumn gateTruths) 0 (B a) j T

/-- (1) **THE SAME ON THE LOG SIDE.** -/
theorem realized_log_rounds_are_constant_log_lane (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hbS : StrategyBounded L (strategicShape c s S)) (logTruths : List (List Element))
    (b : Element) (a : Element) (E : Verifier.Engine) (d : Nat)
    (T : OracleTable (boundedQueries L)) :
    (RunLevelTransportAudit.realizedRounds L hL OuterInitial.zeroDigest (strategicShape c s S)
        hbS (constantLogLane S logTruths b a) 0 T 0 d).map laneData
      = (ConditionalSoundness.logLaneOf E c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T) logTruths).map
        laneData := by
  have hms : ConditionalSoundness.logLaneOf E c
      (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T) logTruths
        = ConditionalSoundness.lane E.commitRound Prod.fst Verifier.RoundChallenges.log
            (logTruths.drop 0)
            (Verifier.start (E.initialTranscript c
              (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T)))
            (messagesFrom (fun r => S r (strategicChallenges L hL c s S hbS r T)) 0 d) := by
    show ConditionalSoundness.lane E.commitRound Prod.fst Verifier.RoundChallenges.log
        logTruths
        (Verifier.start (E.initialTranscript c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T)))
        (roundMessages (RunLevelTransportAudit.realizedRunProof L hL c s S hbS d T)) = _
    rw [RunLevelTransportAudit.realized_run_proof_round_messages]
    rfl
  rw [hms, lane_map_is_data_rounds, realized_rounds_map_is_data_rounds]
  refine data_rounds_congr _ _ _ _ (fun j => ?_) (fun _ => rfl) d 0
  exact raw_log_lane_message_is_realized L hL c s S hS hbS (truthColumn logTruths) 0 b j T

/-! ## 2. THE ENGINE'S OWN FROZEN LANES, AND THE EVENT IDENTITY -/

/-- **THE PUBLIC-HASH ARGUMENT THE ADOPTED `SoundnessAssembly.outerBadEvent`
FORMS**, at the adopted `RunLevelTransportAudit.realizedRunProof`.  The proof's
public inputs ARE the statement's (the adopted
`EngineTauDiagonal.engine_public_hash_is_the_statement_public_hash`), and the
explicit engine's `publicInputsHash` field does not mention its transcript hash --
so this is a function of the statement alone, table-independent and
hash-independent (`engine_public_hash_is_hash_free`). -/
def enginePublicHash (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (th : Transcript.Hash) (s : Verifier.Statement) :
    Nat → Verifier.Base :=
  GateTerminalBinding.publicHashFunction
    ((SoundnessAssembly.engine gdec hash th khash P c₀).publicInputsHash s.publicInputs)

/-- (2) The explicit engine's public-hash function does not move with the
transcript hash. -/
theorem engine_public_hash_is_hash_free (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (th1 th2 : Transcript.Hash) (s : Verifier.Statement) :
    enginePublicHash gdec hash khash P c₀ th1 s = enginePublicHash gdec hash khash P c₀ th2 s :=
  rfl

/-- (2) **THE ADOPTED `SoundnessAssembly.gateLane` OF THE REALIZED RUN IS THE
FROZEN LANE OF THE REALIZED ROUNDS.**  Section 1's identification, carried through
the adopted `AdaptiveAgreementFamily.frozenLane` by `frozen_lane_congr`.  The
engine's transcript-hash argument reaches this `Lane` only through the alpha `a`,
which is exactly what `ha` names. -/
theorem assembly_gate_lane_is_frozen_realized (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (th0 : Transcript.Hash) (L : Nat)
    (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (gateTruths : List (List Element))
    (T : OracleTable (boundedQueries L)) (a : Element)
    (ha : TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) = a) :
    SoundnessAssembly.gateLane (hashOf (boundedQueries L) T)
        (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) gates s0 gateTruths
      = AdaptiveAgreementFamily.frozenLane
          (RunLevelTransportAudit.realizedRounds L hL OuterInitial.zeroDigest
            (strategicShape c s S) hbS
            (engineGateLane S gateTruths
              (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0) a)
            3 T 0 c.degreeBits)
          0 (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0 a) false := by
  have hfroz : SoundnessAssembly.gateLane (hashOf (boundedQueries L) T)
      (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
      (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) gates s0 gateTruths
        = AdaptiveAgreementFamily.frozenLane
            (ConditionalSoundness.gateLaneOf
              (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
              (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) gateTruths)
            0 (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0 a)
            false := by
    rw [← ha]
    rfl
  rw [hfroz]
  exact (frozen_lane_congr _ _ _ _ false
    (realized_gate_rounds_are_engine_gate_lane L hL c s S hS hbS gateTruths
      (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0) a
      (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀)
      c.degreeBits T)).symm

/-- (2) **THE SAME FOR THE ADOPTED `SoundnessAssembly.logLane`.**  No alpha enters
it: the adopted `JointChallengeSpace.logCompareOf` reads no transcript
coordinate. -/
theorem assembly_log_lane_is_frozen_realized (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hbS : StrategyBounded L (strategicShape c s S)) (logTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (T : OracleTable (boundedQueries L)) (a : Element) :
    SoundnessAssembly.logLane
        (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) logTruths t pr
      = AdaptiveAgreementFamily.frozenLane
          (RunLevelTransportAudit.realizedRounds L hL OuterInitial.zeroDigest
            (strategicShape c s S) hbS
            (constantLogLane S logTruths (JointChallengeSpace.logCompareOf t pr) a)
            0 T 0 c.degreeBits)
          0 (JointChallengeSpace.logCompareOf t pr) true :=
  (frozen_lane_congr _ _ _ _ true
    (realized_log_rounds_are_constant_log_lane L hL c s S hS hbS logTruths
      (JointChallengeSpace.logCompareOf t pr) a
      (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀)
      c.degreeBits T)).symm

open Classical in
/-- **THE RUN'S OWN JOINT DRAW LANDS IN THE ENGINE'S OWN FOUR-FAMILY OUTER BAD
EVENT.**  The tables at which the adopted `SoundnessAssembly.outerBadEvent` --
built at the TABLE'S OWN hash, at the engine carrying that hash, and at the proof
the adaptive prover actually submits there -- contains the run's own adopted
`SoundnessAssembly.actualDigestDraw`.  `Finset.univ` here is this module's own
(see HONESTY (vii)). -/
noncomputable def adaptiveEngineOuterBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    SoundnessAssembly.actualDigestDraw (hashOf (boundedQueries L) T) c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
      ∈ SoundnessAssembly.outerBadEvent (hashOf (boundedQueries L) T)
          (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
          gates s0 logTruths gateTruths t pr coeffsOf)

open Classical in
theorem mem_adaptive_engine_outer_bad_event (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS gates s0 logTruths
        gateTruths t pr coeffsOf ↔
      SoundnessAssembly.actualDigestDraw (hashOf (boundedQueries L) T) c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
        ∈ SoundnessAssembly.outerBadEvent (hashOf (boundedQueries L) T)
            (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
            (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
            gates s0 logTruths gateTruths t pr coeffsOf := by
  rw [adaptiveEngineOuterBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

open Classical in
/-- (2) **THE OUTER SUMMAND, IDENTIFIED.**  The adopted
`EngineOuterDiagonal.engineOuterBadEvent` at this module's two families IS "the
run's own draw lands in the adopted
`OuterSequentialConditioning.adaptiveOuterEvent` of the adopted
`SoundnessAssembly`'s OWN two frozen lanes".  Section 1's lane-list
identification, the adopted `EngineOuterDiagonal.frozen_walk_of_realized_log` /
`frozen_walk_of_realized_gate` walk bridge, and the adopted
`RunLevelTransportAudit.realized_draw_is_actual_digest_draw` transport. -/
theorem engine_outer_bad_event_is_assembly_adaptive_outer_event (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (th0 : Transcript.Hash) (L : Nat)
    (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (T : OracleTable (boundedQueries L)) :
    (T ∈ engineOuterBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
        c.degreeBits (constantLogLane S logTruths (JointChallengeSpace.logCompareOf t pr))
        (engineGateLane S gateTruths
          (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0)))
      ↔ SoundnessAssembly.actualDigestDraw (hashOf (boundedQueries L) T) c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
        ∈ OuterSequentialConditioning.adaptiveOuterEvent c.degreeBits
            (SoundnessAssembly.logLane
              (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
              (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
              logTruths t pr)
            (SoundnessAssembly.gateLane (hashOf (boundedQueries L) T)
              (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
              (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
              gates s0 gateTruths) := by
  have hdr : RunLevelTransportAudit.realizedDraw L hL OuterInitial.zeroDigest
      (strategicShape c s S) hbS c.degreeBits T
        = SoundnessAssembly.actualDigestDraw (hashOf (boundedQueries L) T) c
            (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) :=
    RunLevelTransportAudit.realized_draw_is_actual_digest_draw L hL c s S hbS hS T
  have halpha : TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
      (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
        = EngineTauDiagonal.alphaRead L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
            c.degreeBits T :=
    (EngineTauDiagonal.alpha_read_is_gate_alpha_element L hL c s S hbS hS T).symm
  rw [engine_outer_bad_event_is_run_level L hL OuterInitial.zeroDigest (strategicShape c s S)
      hbS c.degreeBits (constantLogLane S logTruths (JointChallengeSpace.logCompareOf t pr))
      (engineGateLane S gateTruths
        (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0))
      (constant_log_lane_of_strategy_claim S (truthColumn logTruths)
        (JointChallengeSpace.logCompareOf t pr))
      (engine_gate_lane_of_strategy_claim S (truthColumn gateTruths)
        (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0)),
    runLevelEngineOuterEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [assembly_log_lane_is_frozen_realized gdec hash khash P c₀ L hL c s S hS hbS logTruths t pr
      T (EngineTauDiagonal.alphaRead L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
        c.degreeBits T),
    assembly_gate_lane_is_frozen_realized gdec hash khash P c₀ th0 L hL c s S hS hbS gates s0
      gateTruths T (EngineTauDiagonal.alphaRead L hL OuterInitial.zeroDigest
        (strategicShape c s S) hbS c.degreeBits T) halpha,
    ← hdr, OuterSequentialConditioning.adaptiveOuterEvent, Finset.mem_union,
    JointChallengeSpace.outerEvent, Finset.mem_union,
    frozen_walk_of_realized_log L hL OuterInitial.zeroDigest (strategicShape c s S) hbS _
      c.degreeBits T 0 (JointChallengeSpace.logCompareOf t pr),
    frozen_walk_of_realized_gate L hL OuterInitial.zeroDigest (strategicShape c s S) hbS _
      c.degreeBits T 0
      (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0
        (EngineTauDiagonal.alphaRead L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
          c.degreeBits T))]
  exact Iff.rfl

open Classical in
/-- **THE EVENT IDENTITY.**  The adopted
`EngineOuterDiagonal.rawEngineAllOwnBadEvent`, at this module's engine families,
IS the event `adaptiveEngineOuterBadEvent`: "the run's own joint draw lands in the
adopted `SoundnessAssembly.outerBadEvent` of the engine carrying the table's own
hash, at the proof the adaptive prover actually submits there".  `Finset` for
`Finset`, for EVERY `StrategyChainBound.RoundCausal S`.

WHAT STAYS ASSUMED, AND IT IS EXACTLY WHAT THE ADOPTED `EngineTauDiagonal` AND
`EngineOuterDiagonal` LEFT ASSUMED: `tables = s0.tables` is READ OFF the statement
(`s0` is supplied here, so the `CommittedTables` extraction join is the SAME one,
not a new one), and `coeffsOf` is the same free family, pinned to those tables by
the adopted `CommitmentOrderSurvey` premise.  The truth columns are the SUPPLIED
free lists.  NOTHING here is a probability statement; see HONESTY. -/
theorem engine_all_own_bad_event_is_assembly_outer_bad_event (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (th0 : Transcript.Hash) (L : Nat)
    (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List Element) :
    rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
        c.degreeBits (2 ^ c.degreeBits)
        (constantLogLane S logTruths (JointChallengeSpace.logCompareOf t pr))
        (engineGateLane S gateTruths
          (engineEndpoint c gates (enginePublicHash gdec hash khash P c₀ th0 s) s0))
        (EngineTauDiagonal.engineGate c gates (enginePublicHash gdec hash khash P c₀ th0 s)
          s0.tables) coeffsOf
      = adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS gates s0 logTruths
          gateTruths t pr coeffsOf := by
  ext T
  have hdr : RunLevelTransportAudit.realizedDraw L hL OuterInitial.zeroDigest
      (strategicShape c s S) hbS c.degreeBits T
        = SoundnessAssembly.actualDigestDraw (hashOf (boundedQueries L) T) c
            (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) :=
    RunLevelTransportAudit.realized_draw_is_actual_digest_draw L hL c s S hbS hS T
  have halpha : TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
      (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
        = EngineTauDiagonal.alphaRead L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
            c.degreeBits T :=
    (EngineTauDiagonal.alpha_read_is_gate_alpha_element L hL c s S hbS hS T).symm
  rw [mem_raw_engine_all_own_bad_event, mem_adaptive_engine_outer_bad_event,
    SoundnessAssembly.outerBadEvent, OuterSequentialConditioning.mem_adaptiveJointBadEvent]
  refine or_congr (engine_outer_bad_event_is_assembly_adaptive_outer_event gdec hash khash P c₀
    th0 L hL c s S hS hbS gates s0 logTruths gateTruths t pr T) (or_congr ?_ ?_)
  · rw [← hdr, RunLevelTransportAudit.gate_tau_is_run_level,
      EngineTauDiagonal.mem_engine_tau_bad_event, ReducedFullTransport.mem_gate_tau_bad_event,
      halpha]
    exact Iff.rfl
  · rw [← hdr, RunLevelTransportAudit.gate_alpha_is_run_level]

/-! ## 3. THE ADAPTIVE ASSEMBLY-FAILURE EVENT -/

open Classical in
/-- **THE INDEX HALF AT THE REALIZED RUN.**  The adopted
`SoundnessAssembly.indexBadEvent` of the run's own supplied and committed cell
families, containing the run's own adopted `SoundnessAssembly.actualIndexDraw`;
the engine, the cells and the draw all move with the table's own hash.  This is
the adopted `RawIndexLanes.rawEngineIndexBadEvent` shape at the adopted
`RunLevelTransportAudit.realizedRunProof` instead of at the adopted
`RawIndexLanes.rawRealizedRun`. -/
def suppliedCellsAt (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (T : OracleTable (boundedQueries L)) : List Element :=
  OpenedClaimFold.lift (OpenedClaimFold.boundCell
    (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T).used
    (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
      (hashOf (boundedQueries L) T) khash P c₀) c
      (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T))
    cellIndex).1

/-- **THE COMMITTED CELL FAMILY AT THE REALIZED RUN**, at the row point the run's
own outer draw determines. -/
def committedCellsAt (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (T : OracleTable (boundedQueries L)) : List Element :=
  IndexPointZeroCheck.openedCells (cols cellIndex)
    (OpenedClaimFold.lift (OpenedClaimFold.cellRow
      (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
        (hashOf (boundedQueries L) T) khash P c₀) c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T))
      cellIndex))

open Classical in
/-- **THE INDEX HALF AT THE REALIZED RUN** (continued). -/
noncomputable def adaptiveIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
      ∈ SoundnessAssembly.indexBadEvent c.indexBits
          (suppliedCellsAt gdec hash khash P c₀ L hL c s S hbS cellIndex T)
          (committedCellsAt gdec hash khash P c₀ L hL c s S hbS cellIndex cols T))

open Classical in
theorem mem_adaptive_index_bad_event (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (T : OracleTable (boundedQueries L)) :
    T ∈ adaptiveIndexBadEvent gdec hash khash P c₀ L hL c s S hbS cellIndex cols ↔
      SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
        ∈ SoundnessAssembly.indexBadEvent c.indexBits
            (suppliedCellsAt gdec hash khash P c₀ L hL c s S hbS cellIndex T)
            (committedCellsAt gdec hash khash P c₀ L hL c s S hbS cellIndex cols T) := by
  rw [adaptiveIndexBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

open Classical in
/-- **THE TABLES ON WHICH THE ADOPTED `SoundnessAssembly.explicit_good_draw_assembly`
CONCLUSION FAILS FOR THE ADAPTIVE PROVER.**  The adopted
`RunLevelUnionBound.assemblyFailureEvent` with the FIXED proof `p` replaced by the
proof the adaptive prover actually submits at the table, the adopted
`RunLevelTransportAudit.realizedRunProof`.  The conclusion is the adopted one
verbatim; it is NOT circuit truth (see HONESTY (v)). -/
noncomputable def adaptiveAssemblyFailureEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ¬ (
    Integrated.verify (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀)
        gdec pin chain c (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
      = Except.ok () →
    SoundnessAssembly.AssemblyResidue gdec hash (hashOf (boundedQueries L) T) khash P c₀ pin c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) wq
        (pre ++ gate :: post) s0 sLast xg cells gateTruths coeffsOf cellIndex cols →
    ((∀ row < 2 ^ c.degreeBits,
        (∀ g' ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig c) g' s0.tables row
            = Verifier.zero) →
        (∀ g' ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig c) g' s0.tables row
            = Verifier.zero) →
        GateRejectionPower.rowFilter (Integrated.gateConfig c) gate s0.tables row
            ≠ Verifier.zero →
        ∃ terms, GatesComplete.evaluateUnfiltered gate
              (AlphaZeroCheck.rowWires s0.tables row)
              (AlphaZeroCheck.rowConstants s0.tables row)
              (GateTerminalBinding.publicHashFunction
                ((SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P
                  c₀).publicInputsHash
                  (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits
                    T).publicInputs))
              (Integrated.gateConfig c).numSelectors = some terms
            ∧ ∀ y ∈ terms, y = Verifier.zero)
      ∧ OpenedClaimFold.lift (OpenedClaimFold.boundCell
            (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T).used
            (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
              (hashOf (boundedQueries L) T) khash P c₀) c
              (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T))
            cellIndex).1
          = IndexPointZeroCheck.openedCells (cols cellIndex)
            (OpenedClaimFold.lift (OpenedClaimFold.cellRow
              (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
                (hashOf (boundedQueries L) T) khash P c₀) c
                (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T))
              cellIndex))
      ∧ (PinnedWhirProfile.pinnedParams P c₀ = wq ∧ 0 < wq.inDomainSamples ∧ wq.rounds ≠ [])
      ∧ (ExplicitEngine.core c = ExplicitEngine.core c₀
          ∨ ExplicitEngine.KhashCollision khash))))

open Classical in
/-- (3) **THE ADAPTIVE ANALOGUE OF THE ADOPTED
`RunLevelUnionBound.assembly_failure_subset_run_union`.**  A `Finset` inclusion
with NO hypothesis: on every table outside the engine's own outer bad event and
outside the engine's own index bad event -- both read at the table's own hash and
at the proof the ADAPTIVE prover submits there -- the adopted
`SoundnessAssembly.explicit_good_draw_assembly` supplies its conclusion, because
its two draw hypotheses `hdraw` and `hidx` are exactly those two
non-memberships. -/
theorem adaptive_assembly_failure_subset (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) :
    adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L hL c s S hbS wq pre post gate
        s0 sLast xg cells gateTruths coeffsOf cellIndex cols
      ⊆ adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS (pre ++ gate :: post) s0
          logTruths gateTruths t pr coeffsOf
        ∪ adaptiveIndexBadEvent gdec hash khash P c₀ L hL c s S hbS cellIndex cols := by
  classical
  intro T hT
  simp only [adaptiveAssemblyFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  rw [Finset.mem_union, mem_adaptive_engine_outer_bad_event, mem_adaptive_index_bad_event]
  by_contra hcon
  push_neg at hcon
  exact hT (fun hacc hres => SoundnessAssembly.explicit_good_draw_assembly gdec hash
    (hashOf (boundedQueries L) T) khash P c₀ pin chain c
    (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) wq pre post gate s0
    sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols hacc hres hcon.1 hcon.2)

open Classical in
/-- **THE PAYOFF: THE ADAPTIVE ANALOGUE OF THE ADOPTED
`IndexStageFinerSplit.assembly_failure_mass_le_unconditional`.**  For EVERY
`StrategyChainBound.RoundCausal S` -- a transcript-restricted causal prover whose
message at every round is chosen after seeing the raw challenge blocks of every
earlier stage -- the mass of the tables at which the adopted
`SoundnessAssembly.explicit_good_draw_assembly` conclusion fails AT THE PROOF THAT
PROVER ACTUALLY SUBMITS is at most the adopted
`ChallengeUnionBound.combinedBound`, one chain-clash term, and the mass of the
index half.

THE INDEX TERM IS CARRIED, NOT DROPPED.  The adopted
`RawIndexLanes.raw_index_bad_event_no_clash_mass_le` weighs the index event at the
adopted `RawIndexLanes.rawRealizedRun` -- the EXTENDED-shape chain, whose proof
record differs from `realizedRunProof` in its `used` field -- so no adopted result
weighs the event at THIS proof, and this module states none.  What section 4 does
give, with no hypothesis, is that the index term vanishes on the honest half of
the table space (`adaptive_index_bad_event_subset_live_guard`). -/
theorem adaptive_assembly_failure_mass_le (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (hbS : StrategyBounded L (strategicShape c s S))
    (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (q constraints : Nat)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ u ∈ logTruths, u.length ≤ 5)
    (hlengate : ∀ u ∈ gateTruths, u.length ≤ q + 2)
    (hdu : 12 + 6 * c.degreeBits < Transcript.u64Limit)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L hL c s S hbS wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + ((22 + 5 * c.degreeBits : Nat) : ℚ) * (((22 + 5 * c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ)
        + oracleProbability (boundedQueries L)
            (adaptiveIndexBadEvent gdec hash khash P c₀ L hL c s S hbS cellIndex cols) := by
  have hsub := oracle_probability_mono (boundedQueries L) _ _
    (adaptive_assembly_failure_subset gdec hash khash P c₀ pin chain L hL c s S hbS wq pre post
      gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols)
  have hun := oracle_probability_union_le (boundedQueries L)
    (adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS (pre ++ gate :: post) s0
      logTruths gateTruths t pr coeffsOf)
    (adaptiveIndexBadEvent gdec hash khash P c₀ L hL c s S hbS cellIndex cols)
  have hblock := raw_engine_all_own_block_bad_draw_probability_le L hL OuterInitial.zeroDigest
    (strategicShape c s S) hbS c.degreeBits q constraints
    (constantLogLane S logTruths (JointChallengeSpace.logCompareOf t pr))
    (engineGateLane S gateTruths
      (engineEndpoint c (pre ++ gate :: post) (enginePublicHash gdec hash khash P c₀ th0 s) s0))
    (constant_log_lane_causal S hS logTruths (JointChallengeSpace.logCompareOf t pr))
    (engine_gate_lane_causal S hS gateTruths
      (engineEndpoint c (pre ++ gate :: post) (enginePublicHash gdec hash khash P c₀ th0 s) s0))
    (constant_log_lane_bounded S logTruths (JointChallengeSpace.logCompareOf t pr) 5 hSlog hlenlog)
    (engine_gate_lane_bounded S gateTruths
      (engineEndpoint c (pre ++ gate :: post) (enginePublicHash gdec hash khash P c₀ th0 s) s0)
      (q + 2) hSgate hlengate)
    (EngineTauDiagonal.engineGate c (pre ++ gate :: post)
      (enginePublicHash gdec hash khash P c₀ th0 s) s0.tables) coeffsOf hdu hclen
  rw [engine_all_own_bad_event_is_assembly_outer_bad_event gdec hash khash P c₀ th0 L hL c s S hS
    hbS (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf] at hblock
  linarith

/-! ## 4. NON-VACUITY, AND THE CLOSED INSTANCE -/

open Classical in
/-- (4) **THE INDEX HALF LIVES ONLY WHERE THE GUARD IS LIVE.**  A `Finset`
inclusion with no hypothesis: at a table whose supplied and committed cell
families agree on the whole index cube the adopted
`SoundnessAssembly.indexBadEvent` is EMPTY (the adopted
`index_bad_event_of_cube_agreement`), so that table is not in the index half at
all.  Honest openings contribute nothing. -/
theorem adaptive_index_bad_event_subset_live_guard (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    adaptiveIndexBadEvent gdec hash khash P c₀ L hL c s S hbS cellIndex cols
      ⊆ Finset.univ.filter (fun T =>
          IndexPointZeroCheck.CellsDifferOnCube c.indexBits
            (suppliedCellsAt gdec hash khash P c₀ L hL c s S hbS cellIndex T)
            (committedCellsAt gdec hash khash P c₀ L hL c s S hbS cellIndex cols T)) := by
  classical
  intro T hT
  rw [mem_adaptive_index_bad_event] at hT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hcon
  rw [SoundnessAssembly.index_bad_event_of_cube_agreement _ _ _ hcon] at hT
  exact absurd hT (Finset.not_mem_empty _)

/-- (4) **THE CLOSED CONSTANT AT THE ENVELOPE'S THIRTEEN COUPLED ROUNDS IS
STRICTLY BELOW `1`.**  `22 + 5 * 13 = 87` chain stages, so `3828 / |Block|`, which
is below the adopted `EngineOuterDiagonal.raw_engine_all_own_bound_at_thirteen`'s
own `4560 / |Block| + 2 * tauTerm 8`.  **THIS COVERS THE FIRST TWO SUMMANDS OF
`adaptive_assembly_failure_mass_le` ONLY**: the third summand, the mass of
`adaptiveIndexBadEvent`, is NOT included here and THIS MODULE BOUNDS IT NOWHERE
(see the remaining step in the header).  What chains out of the two theorems
together is `mass < 1 + P[index half]`, not `mass < 1`.  READ THE HONESTY HEADER:
THIS IS NOT THE PROTOCOL'S SOUNDNESS ERROR. -/
theorem adaptive_assembly_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123
        + ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) < 1 := by
  have hone := raw_engine_all_own_bound_at_thirteen_lt_one
  have htau := SoundnessAssembly.tau_term_nonneg 8
  have hpos : (0 : ℚ) < (Fintype.card Block : ℚ) := block_card_cast_pos
  have hnum : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  have hinv : (0 : ℚ) ≤ (Fintype.card Block : ℚ)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  have e1 : (3828 : ℚ) / (Fintype.card Block : ℚ) = 3828 * (Fintype.card Block : ℚ)⁻¹ :=
    div_eq_mul_inv _ _
  have e2 : (4560 : ℚ) / (Fintype.card Block : ℚ) = 4560 * (Fintype.card Block : ℚ)⁻¹ :=
    div_eq_mul_inv _ _
  rw [hnum]
  linarith

/-- (4) **THE HYPOTHESES OF THE PAYOFF ARE SATISFIABLE**: the counter budget holds
at thirteen coupled rounds, the empty coefficient family meets the
coefficient-length budget, and the EMPTY truth list meets both degree budgets --
the same witnesses the adopted `EngineOuterDiagonal` closed instance uses.  THIS
DOES NOT MAKE THE BOUNDS ABOVE NON-VACUOUS.  Hypothesis satisfiability is not
non-emptiness of the bounded event, and the bounded event here IS empty at every
configuration other than `numWires = 1`, `numRouted = 0`, `numConstants = 1` --
see the emptiness bullet of the honesty header, and the adopted
`IndexHalfTransport.adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`. -/
theorem adaptive_payoff_hypotheses_satisfiable :
    (12 + 6 * 13 < Transcript.u64Limit) ∧
      (∀ i, i < 2 ^ 13 → ((fun _ => ([] : List Element)) i).length ≤ 123) ∧
      (∀ u ∈ ([] : List (List Element)), u.length ≤ 5) ∧
      (∀ u ∈ ([] : List (List Element)), u.length ≤ 10) :=
  ⟨ReducedFullTransport.thirteen_counter_budget, fun _ _ => Nat.zero_le _, fun _ h => absurd h (List.not_mem_nil _),
    fun _ h => absurd h (List.not_mem_nil _)⟩

open Classical in
/-- (4) **TESTED AT THE CONSTANT TRUTH COLUMN.**  At the adopted
`RawBlockLanes.rawZeroTruth` choice -- the truth column that is EMPTY at every
round -- this module's `truthColumn` family is exactly that adopted choice, so the
identification of section 1 specialises to the setting every adopted closed
instance is stated in. -/
theorem truth_column_at_empty_list (k : Nat) (ch : Nat → Nat → Block) :
    truthColumn [] k ch = rawZeroTruth k ch := by
  cases k with
  | zero => rfl
  | succ _ => rfl

end Audit.Wire3.AdaptiveAssemblyFailure
