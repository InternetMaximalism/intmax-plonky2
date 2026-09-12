import Audit.Wire3.EngineTauDiagonal
import Audit.Wire3.TwoStageConditionalCount
import Audit.Wire3.RawBlockLanes
import Audit.Wire3.RunLevelTransportAudit
import Audit.Wire3.RawIndexLanes
import Audit.Wire3.SoundnessAssembly

/-!
# THE OUTER ALPHA DIAGONAL: THE ENGINE'S OWN OUTER BAD EVENT FOR THE ADAPTIVE PROVER

## THE GAP THIS MODULE CLOSES -- READ THIS FIRST

The adopted `EngineTauDiagonal` closed the TAU diagonal for the adaptive line and
said, in its HONESTY (iv), exactly what it did not close:

> THE OUTER DIAGONAL FOR THE ADAPTIVE PROVER IS STILL OPEN.  The adopted
> `SoundnessAssembly.outerBadEvent` depends on the alpha coordinate through its
> lanes as well as through `g`; the adopted `TwoStageConditionalCount` handles
> that dependence for a FIXED prover, and no module -- including this one --
> handles it for the adaptive line.

That is the sentence this module removes.  The adopted
`SoundnessAssembly.outerBadEvent` is, by the adopted
`TwoStageConditionalCount.outer_bad_event_is_outer_bad_at`,

  `adaptiveJointBadEvent d (logLane E c p logTruths t pr)
      (frozenLane (gateLaneOf E c p gateTruths) 0 (endpointSum gc gates ph ALPHA s0) false)
      (gateValue gc gates ph ALPHA s0.tables) (2 ^ d) coeffsOf`,

and the alpha enters it in EXACTLY TWO PLACES: the gate lane's INITIAL TRUTH
CLAIM (the adopted `GateClaimChain.endpointSum` at the alpha) and the tau
column's zero-check table (the adopted `ZeroCheckSemantics.gateValue` at the
alpha).  The second is the adopted `EngineTauDiagonal`'s subject.  THE FIRST IS
THIS MODULE'S: the gate lane's running claims -- and hence EVERY ROUND'S BAD SET
-- move with the answer the same oracle gives at the alpha cell.

The adopted `RawBlockLanes.rawOuterBadEvent` is the CONSTANT-ALPHA SLICE of the
event this module bounds (`engine_outer_bad_event_constant_slice`, a `rfl`), so
no adopted theorem bounds the diagonal.  Section 2 bounds it, by the SAME
constant `ChallengeUnionBound.outerTerm d q`.

## WHY IT IS TRUE, AND WHERE THE WORK IS

The alpha cell is read at the adopted `ReducedFullTransport.deriveStage = 22`,
at counter `alphaBase d = 9 + 3 d`.  Round `r`'s own two challenge triples are
read at the adopted `OuterLaneTransport.roundStage r = 22 + 5 r + 5`, which is
STRICTLY LATER.  So reassigning any of round `r`'s own challenge answers leaves
the alpha cell where it was (`engine_outer_alpha_invariant`, the adopted
`OuterLaneTransport.stage_triple_reassign_lower` at `deriveStage < roundStage r`
under the chain's no-clash event) -- and therefore leaves the whole alpha-indexed
target where it was, since the adopted `RawBlockLanes.raw_target_reassign` does
the rest for the lane the alpha selects.  THAT IS THE ENTIRE DIFFERENCE FROM THE
ADOPTED `RawBlockLanes`, and the adopted `OuterLaneTransport.stage_triple_target_card`
diagonal fresh step -- whose hypothesis is exactly "the target is unmoved by the
stage's own cells" -- then applies UNCHANGED.  The per-round cardinality is the
adopted `RawBlockLanes.raw_target_card_le` at the selected lane, which holds
UNIFORMLY in the alpha; that uniformity is what makes the diagonal cost nothing.

## WHAT IS PROVED

1. SECTION 1.  HOW THE ALPHA ENTERS, FOR THE ADAPTIVE PROVER.
   `engine_outer_bad_at_parts` (the two places, by `rfl`),
   `engine_outer_bad_event_depends_on_alpha_and_messages` and its
   `raw_extended` twin: at the adopted `RunLevelTransportAudit.realizedRunProof`
   the adopted `SoundnessAssembly.outerBadEvent` AT THE TABLE'S OWN HASH is the
   adopted `TwoStageConditionalCount.outerBadAt` family read at the cell the
   chain squeezes at the derive digest, the adopted
   `EngineTauDiagonal.alphaRead`.
2. SECTION 2.  THE ALPHA-INDEXED RAW LANE FAMILY AND THE DIAGONAL:
   `AlphaRawLaneCausal`, `AlphaRawLaneBounded`, `engineOuterTarget`,
   `engine_outer_alpha_invariant`, `engine_outer_target_reassign`,
   `engine_outer_round_mass_le`, the events, and
   `engine_outer_no_clash_mass_le` -- the headline of this module --
   together with `engine_outer_bad_draw_probability_le`.
3. SECTION 3.  ALL FOUR FAMILIES.  `rawEngineAllOwnBadEvent`,
   `raw_engine_all_own_no_clash_mass_le`, and
   `raw_engine_all_own_bad_draw_probability_le`: for EVERY
   `StrategyChainBound.RoundCausal S`, EVERY `RawIndexLanes.ClaimsCausal d U`,
   EVERY alpha-indexed lane family and EVERY alpha-to-table map,

     `<= combinedBound d q d constraints + 2 tauTerm c.indexBits + ONE clash term`.

4. SECTION 4.  THE IDENTIFICATION, AND THE WALK BRIDGE.
   `engine_outer_bad_event_is_run_level`, UNDER THE TWO HYPOTHESES
   `∀ a, (logF a).claim = 0` AND `∀ a, (gateF a).claim = 0` -- both discharged for
   section 5's own families by `constant_log_lane_of_strategy_claim` and
   `engine_gate_lane_of_strategy_claim`, so neither is a gap -- says the table
   event of section 2 IS "the run's own realized draw lands in the adopted
   `JointChallengeSpace.outerEvent` of the lane rounds the prover actually played
   AT ITS OWN ALPHA"; and
   `engine_outer_event_is_the_run_outer_event_at_the_engine_alpha`, which puts
   the adopted `InstalledRoundCommit.actualDigestDraw` at the adopted
   `realizedRunProof` and the adopted `TranscriptProvenance.gateAlphaElement` in
   place of both, PROVED through the adopted
   `RunLevelTransportAudit.realized_draw_is_actual_digest_draw` and the adopted
   `EngineTauDiagonal.alpha_read_is_gate_alpha_element`.  THEN THE WALK BRIDGE,
   WITH NO HYPOTHESIS AT ALL: `drawn_at_realized_gate` / `drawn_at_realized_log`
   (the adopted `JointChallengeSpace.DrawnAt` holds at the realized draw for this
   module's own realized lane rounds BY CONSTRUCTION) and hence
   `frozen_walk_of_realized_gate` / `frozen_walk_of_realized_log` (the adopted
   `AdaptiveAgreementFamily`'s frozen walk IS the adopted
   `JointChallengeSpace.laneEvent`, at the realized draw).
5. SECTION 5.  A GENUINELY MOVING OUTER TARGET (`sampleOuterLane`,
   `sample_outer_target_depends_on_alpha`), the ENGINE's own alpha-indexed gate
   lane (`engineGateLaneOfStrategy` at `engineEndpoint`), the closed instance at
   the envelope's thirteen coupled rounds
   (`raw_engine_all_own_bound_at_thirteen`, strictly below `1`), and the test at
   the constant family (`engine_outer_bound_at_constant_family`).

## WHICH EVENTS ARE THE ENGINE'S OWN AFTER THIS MODULE

In `raw_engine_all_own_bad_draw_probability_le` (section 3), at the adopted
`RawIndexLanes.rawExtendedShape` prover:

* OUTER -- THE ENGINE'S OWN, diagonal in the alpha cell (THIS MODULE).  The
  lane family is alpha-indexed, and section 5 instantiates it at the adopted
  `SoundnessAssembly.gateLane`'s own truth claim, the adopted
  `GateClaimChain.endpointSum` at the alpha.  What is NOT yet done is the last
  leg -- see "THE PRECISE REMAINING STEP" below.
* TAU -- THE ENGINE'S OWN, the adopted `EngineTauDiagonal.engineTauBadEvent`,
  identified with the engine's alpha by the adopted
  `EngineTauDiagonal.raw_extended_alpha_read_is_gate_alpha_element`.
* INDEX -- THE ENGINE'S OWN, the adopted `RawIndexLanes.rawEngineIndexBadEvent`.
* ALPHA -- the adopted `ReducedFullTransport.gateAlphaBadEvent` at a FIXED
  `coeffsOf`.  ITS TARGET MENTIONS NO CHALLENGE AT ALL: the adopted
  `CommitmentOrderSurvey.coefficients_are_determined_by_the_tables` and
  `prefix_coefficients_ignore_the_eq_column` say the adopted
  `ChallengeUnionBound.alphaUnionBadSet rows coeffsOf` is a function of the
  TABLES alone (`prefixCoeffTable` takes neither a hash nor a proof).  NAME THE
  PREMISE: that determination theorem is stated UNDER
  `∀ i, i < rows → prefixCoeffTable c gates publicHash t i = some (coeffsOf i)`,
  i.e. it applies only to a `coeffsOf` PINNED to the tables by
  `prefixCoeffTable`.  So the accurate statement is: WITH THE TABLES FIXED AND
  `coeffsOf` SO PINNED the alpha event is already the engine's own, and no
  diagonal is needed for it -- the `∀ coeffsOf` quantifier is the
  `tables = s0.tables` join in another guise, not a separate weakening.  READ
  HONESTY (iii).

SO ALL FOUR FAMILIES ARE THE ENGINE'S OWN, in the sense that each is stated at
the engine's own data, modulo `tables = s0.tables` (with `coeffsOf` pinned to
those tables by `prefixCoeffTable`, as just said) and, FOR THE OUTER SUMMAND
ONLY, the lane-list identification of "THE PRECISE REMAINING STEP" below.  Those
are TWO unidentified items, not one, and the second is the outer summand's alone.

## WHAT STAYS `∀`-QUANTIFIED IN THE FINAL THEOREM

Precisely: the gate list `gates`, the public-hash function, the extracted state
`s0`, the truth columns `logTruths` / `gateTruths` (as the raw lanes' free
`truth` fields), the coefficient family `coeffsOf`, the extracted columns `cols`
and the cell index.  `s0` is NOT quantified only "through `tables`": it enters
the outer truth claim DIRECTLY, as the last argument of the adopted
`GateClaimChain.endpointSum … alpha s0` that `engine_outer_bad_at_parts`
displays, as well as through `s0.tables` in the tau column.  Of these arguments
only `tables` is a GAP in the sense of the adopted `CommitmentOrder` /
`CommitmentOrderSurvey` `CommittedTables` extraction join; the rest are data the
adopted `SoundnessAssembly.AssemblyResidue` supplies and the adopted
`SoundnessAssembly.explicit_good_draw_assembly` is stated at.  The public-hash
argument is NOT a gap, by the adopted
`EngineTauDiagonal.engine_public_hash_is_the_statement_public_hash`.

## THE PRECISE REMAINING STEP (THE ASSEMBLY-FAILURE COROLLARY WAS NOT REACHED)

Section 4 gets as far as: the bounded event IS

  `{T | actualDigestDraw (hashOf T) c (realizedRunProof … T)
        ∈ JointChallengeSpace.outerEvent d  a  b
            (realizedRounds … (logF ALPHA) 0 T 0 d)
            (realizedRounds … (gateF ALPHA) 3 T 0 d)}`,

with `ALPHA = gateAlphaElement (hashOf T) c (realizedRunProof … T)` -- the
engine's own alpha at the engine's own realized proof, and under the two
`claim = 0` hypotheses named in WHAT IS PROVED (4).  The adopted
`SoundnessAssembly.outerBadEvent` is instead
`OuterSequentialConditioning.adaptiveJointBadEvent` at the adopted
`AdaptiveAgreementFamily.frozenLane` of `ConditionalSoundness.logLaneOf` /
`gateLaneOf`.  EXACTLY ONE LEG IS MISSING:

THE LANE-LIST IDENTIFICATION.  `realizedRounds … (gateF a) 3 T 0 d` would have to
be `ConditionalSoundness.gateLaneOf E c (realizedRunProof … T) gateTruths`, and
`realizedRounds … (logF a) 0 T 0 d` the matching `logLaneOf` list.  The lengths
already agree (the adopted `RunLevelTransportAudit.realized_rounds_length`); what
is NOT proved anywhere is the identification of the two lists' `message` and
`truth` FIELDS round by round.  The adopted `RunLevelTransportAudit` does not
prove this, and neither does this module.  NOTE that the `challenge` field is NOT
part of what has to be matched: the adopted `AdaptiveAgreementFamily.frozenLane`
reads only `.message` and `.truth`, and `gateLaneOf`'s `challenge` field comes
from the abstract `e.commitRound`, which the walk never looks at (the adopted
`AdaptiveAgreementFamily.Example.frozenLane_ignores_values`).

THE WALK BRIDGE IS NOT AN OBSTACLE, AND THIS MODULE PROVES SO.  It is tempting to
list, as a second leg, the adopted
`AdaptiveAgreementFamily.frozen_lane_matches_laneEvent_at_encoding_draw`'s
hypothesis -- the adopted `JointChallengeSpace.DrawEncodesRun` at
`realizedDraw … T` -- and to observe that the adopted `draw_encodes_run_inhabited`
proves it only at the adopted `canonicalDraw`, a DIFFERENT point of the joint
space.  THAT IS A MISDIAGNOSIS.  The frozen walk itself
(`AdaptiveAgreementFamily.frozen_gate_walk` / `frozen_log_walk`) asks only for the
adopted `JointChallengeSpace.DrawnAt` OF THE LIST IT IS HANDED, and for this
module's own `RunLevelTransportAudit.realizedRounds` at `realizedDraw … T` that
holds BY CONSTRUCTION, with NO hypothesis: the rounds' `challenge` field IS the
reduced realized triple, which is what the adopted
`RunLevelTransportAudit.realized_draw_gate_proj` / `realized_draw_log_proj` say
the realized draw's coordinates reduce to.  Section 4 proves exactly that --
`drawn_at_realized_gate`, `drawn_at_realized_log` -- and then the bridge itself,
`frozen_walk_of_realized_gate` and `frozen_walk_of_realized_log`.  The `gateDrawn`
/ `logDrawn` halves of `DrawEncodesRun` at the realized draw would FOLLOW from the
lane-list identification above, so there is no independent second leg.

NOTE 3 (THE ENGINE ARGUMENT).  The adopted
`SoundnessAssembly.explicit_good_draw_assembly` is stated at the explicit engine
`SoundnessAssembly.engine gdec hash thash khash P c₀`, whose transcript-hash
argument MOVES with `hashOf T` at the realized run.  That is already absorbed
upstream, not a further gap: the adopted
`TwoStageConditionalCount.explicit_outer_bad_event_is_the_family` replaces that
`thash` inside `engine` by an ARBITRARY `th0`, a `Finset` equality with no
hypothesis, precisely because `frozenLane` ignores challenge values and the
engine's hash reaches the outer event only through them.

Consequently `assembly_failure_subset_all_own` and the mass corollary -- the
adaptive-line analogue of the adopted
`TwoStageConditionalCount.assembly_failure_mass_le_unconditional` -- ARE NOT IN
THIS MODULE, and the four events bounded here are NOT claimed to be literally
the four hypotheses of the adopted `SoundnessAssembly.explicit_good_draw_assembly`
at the realized run.  What IS claimed is the displayed run-level form above.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)` -- one
independent uniform block per byte string of length at most `L`.  The fresh-query
fact everything rests on, the adopted `BirthdayClashBound.fresh_coordinate_probability`,
is the DEFINING property of a random table and is false, as a theorem, for any
fixed hash.  Replacing the deployed permutation by a table drawn from this law is
an assumption with no proof anywhere in this tree.

(ii) THE PROVER CLASS.  TRANSCRIPT-RESTRICTED CAUSAL.  Section 2 holds for every
`StrategyChainBound.Strategy`; section 3 and section 5 are at the adopted
`RawIndexLanes.rawExtendedShape` for an arbitrary
`StrategyChainBound.RoundCausal S` and an arbitrary
`RawIndexLanes.ClaimsCausal d U` -- a prover handed the stage digests of its own
chain and the oracle's answers at the CHALLENGE inputs of those digests, making no
oracle queries of its own.  GRINDING -- a prover that hashes candidate payloads
itself and keeps the one whose digest collides -- IS EXCLUDED by every theorem
below.  THE OUTER DIAGONAL ITSELF COSTS NO EXTRA RESTRICTION:
`engine_outer_no_clash_mass_le` holds for every `Strategy` and every
alpha-indexed lane family whatsoever, including families no engine realizes.

(iii) `tables = s0.tables` REMAINS THE ASSUMPTION.  Exactly as the adopted
`EngineTauDiagonal` HONESTY (iii) leaves it: the adopted `CommitmentOrder` /
`CommitmentOrderSurvey` `CommittedTables` extraction join is inherited verbatim
and not strengthened.  Every "the engine's own" claim above is modulo that one
argument, and the alpha family's `coeffsOf` is the same join in another guise.

(iv) WHIR AND MERKLE ARE EXCLUDED.  `combinedBound` covers (a) the outer sumcheck
round-agreement events, (b) the gate tau multilinear zero check and (c) the gate
alpha zero check; the index term covers the adopted index sampler.  The WHOLE
WHIR/Merkle contribution -- proximity and list decoding, the query-repetition
profile, Merkle collision resistance -- is EXCLUDED, and it is the dominant term.
Quoting the constant of section 5 as the wire-v3 soundness error would be wrong by
roughly seventy bits.

(v) GOOD-DRAW-CONDITIONAL, AND R1b.  The meaning of the per-round bad sets remains
the adopted `ConditionalSoundness` one -- GOOD-DRAW-CONDITIONAL, with that
module's assumption list untouched -- and nothing here instantiates it.  The
opened-claim relation in force upstream is the adopted R1b honest-openings
relation; this module neither uses nor strengthens it.

(vi) ACCEPTANCE IS NEVER EXHIBITED, AND THESE MASSES ARE NOT THE SYSTEM'S
SOUNDNESS ERROR.  No accepting proof is produced anywhere below, no extractor is
run, and nothing below is a claim that FIAT--SHAMIR SOUNDNESS HAS BEEN PROVED FOR
AN ADAPTIVE PROVER.  What is bounded is the mass of named events defined directly
on the oracle table.  The Fiat--Shamir half -- that the run's encoding draw is
`JointChallengeSpace.jointProbability`-distributed -- remains exactly as
unformalized as the adopted `JointChallengeSpace.DrawEncodesRun` header says.

(vii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's
OWN definitions (`engineRoundBadEvent`, `runLevelEngineOuterEvent`), in the
STATEMENT of section 4's
`engine_outer_event_is_the_run_outer_event_at_the_engine_alpha` -- which spells
`runLevelEngineOuterEvent` out at the realized proof and so necessarily repeats
its `Finset.univ.filter` over the table space -- and, through the generic
`Finset.mem_univ` on `OracleTable`, in a few proofs; no tactic or term below ever
puts `Finset.univ` on `Element` or on `OuterChallenge.DigestTriple` in a reducible
position, and NO `Nat` OR `ℚ` ARITHMETIC TACTIC BELOW IS EVER SHOWN A
`Fintype.card` OF ANY OF THEM: the one `ring` in section 2 is run on a statement
generalized over the ratio (`succ_mul_split`), so the cardinality never reaches
it.  For the same reason section 5's moving-target witness is phrased through a
CARDINALITY (`raw_target_zero_card_eq_zero_of_eq`, via the adopted
`OuterChallenge.fixed_point_set_preimage_bound`) rather than through an emptiness:
no membership over `OuterChallenge.DigestTriple` at a CONCRETE lane is elaborated
anywhere, and the two lemmas that touch the adopted `ConditionalSoundness.roundBadSet`
are stated over an ABSTRACT lane so that no `if a = b` on concrete `Element`s is
ever reduced.  `open Classical in` is used for the declarations whose statements mention
membership in, or images into, a `Finset` over the table space, exactly as the
adopted `RawBlockLanes` and `EngineTauDiagonal` do.  Memberships over the table
space are manipulated through `Finset` equalities and the adopted generic helpers
`OuterLaneTransport.univ_filter_inter_subset`, `subset_inter_union_compl` and
`ReducedEngineIndex.inter_union_mass_le`.  `ChallengeUnionBound.outerTerm` and
`tauTerm` are never evaluated.  The two closed instances of section 5 mention
`d = 13` literally, as the adopted
`EngineTauDiagonal.raw_engine_full_index_bound_at_thirteen` does.
-/

namespace Audit.Wire3.EngineOuterDiagonal

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.ReducedFullTransport
open Audit.Wire3.RawBlockLanes
open Audit.Wire3.EngineTauDiagonal

/-! ## 1. HOW THE ALPHA ENTERS THE ENGINE'S OUTER BAD EVENT, ADAPTIVELY -/

/-- (1) **THE TWO PLACES THE ALPHA ENTERS, WRITTEN OUT.**  By `rfl` from the
adopted `TwoStageConditionalCount.outerBadAt`: the alpha appears in the gate
lane's INITIAL TRUTH CLAIM (the adopted `GateClaimChain.endpointSum`) and in the
tau column's zero-check table (the adopted `ZeroCheckSemantics.gateValue`), and
NOWHERE ELSE.

READ OFF THE STATEMENT WHAT THE TRUTH COLUMN IS.  The adopted
`SoundnessAssembly.outerBadEvent` builds both lanes from
`ConditionalSoundness.logLaneOf` / `gateLaneOf E c p logTruths gateTruths`: the
round MESSAGES are read off the PROOF `p`, and the round TRUTHS are the SUPPLIED
lists `logTruths` / `gateTruths` -- FREE DATA, not the engine's derived values.
For the adaptive prover the proof is the adopted
`RunLevelTransportAudit.realizedRunProof`, so the messages are functions of the
earlier challenges, which is exactly what the adopted `RawBlockLanes.RawLane`'s
`message` field already models; and the free truth column is what its `truth`
field already models.  So the ONLY thing an adaptive outer diagonal has to add on
top of the adopted `RawBlockLanes` is the alpha-dependence of the initial truth
claim -- which is what section 2 does. -/
theorem engine_outer_bad_at_parts (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) (alpha : Element) :
    TwoStageConditionalCount.outerBadAt E c p gates s0 logTruths gateTruths t pr coeffsOf alpha
      = OuterSequentialConditioning.adaptiveJointBadEvent c.degreeBits
          (SoundnessAssembly.logLane E c p logTruths t pr)
          (AdaptiveAgreementFamily.frozenLane
            (ConditionalSoundness.gateLaneOf E c p gateTruths) 0
            (GateClaimChain.endpointSum (Integrated.gateConfig c) gates
              (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
              alpha s0) false)
          (ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates
            (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
            alpha s0.tables)
          (2 ^ c.degreeBits) coeffsOf := rfl

/-- **THE ENGINE'S OWN ALPHA-INDEXED OUTER BAD FAMILY, AT THE REALIZED PROOF.**
The adopted `TwoStageConditionalCount.outerBadAt` at the adopted
`RunLevelTransportAudit.realizedRunProof`, i.e. at the proof the strategic prover
actually submits at the table `T`. -/
noncomputable def engineOuterBadAtRealized (L : Nat) (hL : 64 ≤ L) (E : Verifier.Engine)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) (alpha : Element) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  TwoStageConditionalCount.outerBadAt E c
    (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) gates s0 logTruths
    gateTruths t pr coeffsOf alpha

/-- (1) **THE ADAPTIVE DEPENDENCE FACT.**  At the adopted
`RunLevelTransportAudit.realizedRunProof`, the adopted
`SoundnessAssembly.outerBadEvent` read AT THE TABLE'S OWN HASH is the
alpha-indexed family read at the cell the chain squeezes at the derive digest --
the adopted `EngineTauDiagonal.alphaRead`.  This is the adaptive-line analogue of
the adopted `TwoStageConditionalCount.outer_bad_event_depends_on_alpha_only`: both
the HASH and the PROOF move with the table, and the event's whole dependence on
the hash is still the one cell.  PROVED, not assumed: the adopted
`EngineTauDiagonal.alpha_read_is_gate_alpha_element` supplies the identification
of the cell. -/
theorem engine_outer_bad_event_depends_on_alpha_and_messages (L : Nat) (hL : 64 ≤ L)
    (E : Verifier.Engine) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    SoundnessAssembly.outerBadEvent (hashOf (boundedQueries L) T) E c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) gates s0
        logTruths gateTruths t pr coeffsOf
      = engineOuterBadAtRealized L hL E c s S hbS gates s0 logTruths gateTruths t pr coeffsOf T
          (alphaRead L hL OuterInitial.zeroDigest (strategicShape c s S) hbS c.degreeBits T) := by
  rw [engineOuterBadAtRealized, alpha_read_is_gate_alpha_element L hL c s S hbS hS T]
  exact TwoStageConditionalCount.outer_bad_event_is_outer_bad_at _ E c _ gates s0 logTruths
    gateTruths t pr coeffsOf

/-- (1) **THE SAME AT THE SECTION-3 PROVER.**  The adopted
`RawIndexLanes.rawExtendedShape` reads the same alpha cell -- the adopted
`EngineTauDiagonal.raw_extended_alpha_read_is_gate_alpha_element` -- at the SAME
realized run proof. -/
theorem raw_extended_engine_outer_bad_event_depends_on_alpha_and_messages (L : Nat)
    (hL : 64 ≤ L) (E : Verifier.Engine) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    SoundnessAssembly.outerBadEvent (hashOf (boundedQueries L) T) E c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) gates s0
        logTruths gateTruths t pr coeffsOf
      = engineOuterBadAtRealized L hL E c s S hbS gates s0 logTruths gateTruths t pr coeffsOf T
          (alphaRead L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
            hbE c.degreeBits T) := by
  rw [engineOuterBadAtRealized,
    raw_extended_alpha_read_is_gate_alpha_element L hL c s S hS U d hbE hbS T]
  exact TwoStageConditionalCount.outer_bad_event_is_outer_bad_at _ E c _ gates s0 logTruths
    gateTruths t pr coeffsOf

/-! ## 2. THE ALPHA-INDEXED RAW LANE FAMILY AND THE OUTER DIAGONAL -/

/-- **AN ALPHA-INDEXED RAW LANE FAMILY OBEYS THE PROTOCOL'S CAUSALITY** when each
of its members does.  The index is the alpha VALUE; causality is about the round
index and the raw challenge view, so the two conditions do not interact. -/
def AlphaRawLaneCausal (F : Element → RawLane) : Prop :=
  ∀ a : Element, RawLaneCausal (F a)

/-- **AND OBEYS THE DEGREE BOUND** when each of its members does, with ONE bound
uniform in the alpha.  That uniformity is exactly what makes the diagonal cost
nothing: the per-round cardinality below is the same at every alpha. -/
def AlphaRawLaneBounded (F : Element → RawLane) (b : Nat) : Prop :=
  ∀ a : Element, RawLaneBounded (F a) b

/-- **ROUND `r`'s TARGET AT THE ALPHA THE SAME ORACLE DREW.**  The adopted
`RawBlockLanes.rawTarget` of the lane the alpha cell selects.  The adopted
`RawBlockLanes.rawOuterBadEvent` is the CONSTANT-family slice of the event built
from this (`engine_outer_bad_event_constant_slice`). -/
noncomputable def engineOuterTarget (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (F : Element → RawLane)
    (base r : Nat) (T : OracleTable (boundedQueries L)) : Finset OuterChallenge.DigestTriple :=
  rawTarget L hL e0 strat hb (F (alphaRead L hL e0 strat hb d T)) base r T

/-- (2) **THE ALPHA CELL IS UNMOVED BY REASSIGNING ANY OF ROUND `r`'s OWN
CHALLENGE ANSWERS.**  The alpha is read at the adopted
`ReducedFullTransport.deriveStage = 22`; round `r`'s own answers are at the
adopted `OuterLaneTransport.roundStage r = 22 + 5 r + 5`, strictly later.  The
adopted `OuterLaneTransport.stage_triple_reassign_lower` under the chain's
no-clash event. -/
theorem engine_outer_alpha_invariant (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d r cnt : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL e0 strat hb (roundStage r)) (b : Block) :
    alphaRead L hL e0 strat hb d
        (reassign T (challengeSel L hL e0 strat hb (roundStage r) cnt T) b)
      = alphaRead L hL e0 strat hb d T := by
  rw [alphaRead, alphaRead, stage_triple_reassign_lower L hL e0 strat hb (roundStage r) cnt
    deriveStage (alphaBase d) (by rw [deriveStage, roundStage]; omega) T hT b]

/-- (2) **HENCE SO IS ROUND `r`'s ALPHA-INDEXED TARGET.**  Two facts compose: the
alpha cell does not move (above), so the SAME member of the family is selected;
and that member's target does not move, by the adopted
`RawBlockLanes.raw_target_reassign`, which is discharged from causality alone.
This is the hypothesis shape of the adopted
`OuterLaneTransport.stage_triple_target_card` diagonal fresh step -- "the target
may depend on any cells other than the stage's own" -- and the alpha is such a
cell. -/
theorem engine_outer_target_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (F : Element → RawLane)
    (hF : AlphaRawLaneCausal F) (base r cnt : Nat) (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL e0 strat hb (roundStage r)) (b : Block) :
    engineOuterTarget L hL e0 strat hb d F base r
        (reassign T (challengeSel L hL e0 strat hb (roundStage r) cnt T) b)
      = engineOuterTarget L hL e0 strat hb d F base r T := by
  rw [engineOuterTarget, engineOuterTarget,
    engine_outer_alpha_invariant L hL e0 strat hb d r cnt T hT b]
  exact raw_target_reassign L hL e0 strat hb (F (alphaRead L hL e0 strat hb d T))
    (hF _) base r cnt T hT b

/-- (2) **THE PER-ROUND CARDINALITY, UNIFORMLY IN THE ALPHA.**  The adopted
`RawBlockLanes.raw_target_card_le` at the selected member.  NO CARDINALITY IS
EVALUATED. -/
theorem engine_outer_target_card_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (F : Element → RawLane)
    (bd : Nat) (hbd : AlphaRawLaneBounded F bd) (base r : Nat)
    (T : OracleTable (boundedQueries L)) :
    (engineOuterTarget L hL e0 strat hb d F base r T).card
      ≤ bd * OuterChallenge.fiberCeiling ^ 3 :=
  raw_target_card_le L hL e0 strat hb (F (alphaRead L hL e0 strat hb d T)) bd (hbd _) base r T

/-- (2) **ROUND `r`'s DIAGONAL MASS, AT EITHER LANE FAMILY.**  Conditioned on the
chain's no-clash event up to round `r`'s own stage, the lane's own challenge
triple of round `r` lands in the bad set chosen by ITS OWN RAW HISTORY AND BY THE
ALPHA THE SAME ORACLE DREW, with mass at most `bd * ceil ^ 3 / |DigestTriple|` --
the SAME constant the adopted `RawBlockLanes.raw_round_mass_le` pays at a fixed
lane. -/
theorem engine_outer_round_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (F : Element → RawLane)
    (hF : AlphaRawLaneCausal F) (bd : Nat) (hbd : AlphaRawLaneBounded F bd) (base : Nat)
    (hbase : base + 2 < Transcript.u64Limit) (r : Nat) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL e0 strat hb (roundStage r)).filter
          (fun T => stageTriple L hL e0 strat hb (roundStage r) base T
            ∈ engineOuterTarget L hL e0 strat hb d F base r T))
      ≤ ((bd * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ) :=
  stage_triple_target_mass_le L hL e0 strat hb (roundStage r) base hbase
    (stageNoClash L hL e0 strat hb (roundStage r))
    (stage_stable_no_clash L hL e0 strat hb (roundStage r) (tripleCounters base))
    (engineOuterTarget L hL e0 strat hb d F base r)
    (fun T hT cnt _ b => engine_outer_target_reassign L hL e0 strat hb d F hF base r cnt T hT b)
    (bd * OuterChallenge.fiberCeiling ^ 3)
    (fun T _ => engine_outer_target_card_le L hL e0 strat hb d F bd hbd base r T)

open Classical in
/-- THE EVENT THAT COUPLED ROUND `r`'s OWN CHALLENGE TRIPLE, AT COUNTER `base`,
LANDS IN THE BAD SET THE ALPHA-INDEXED FAMILY HAS CHOSEN FOR IT AT THE ALPHA THE
SAME ORACLE DREW. -/
noncomputable def engineRoundBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (F : Element → RawLane)
    (base r : Nat) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => stageTriple L hL e0 strat hb (roundStage r) base T
    ∈ engineOuterTarget L hL e0 strat hb d F base r T)

open Classical in
/-- Round `r` agrees on either lane family: the log family at counters `0, 1, 2`
and the gate family at counters `3, 4, 5` of the SAME stage digest. -/
noncomputable def engineBothBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) (r : Nat) : Finset (OracleTable (boundedQueries L)) :=
  engineRoundBadEvent L hL e0 strat hb d logF 0 r ∪ engineRoundBadEvent L hL e0 strat hb d gateF 3 r

open Classical in
/-- The union over the first `k` coupled rounds. -/
noncomputable def engineOuterUpto (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) (k : Nat) : Finset (OracleTable (boundedQueries L)) :=
  (Finset.range k).biUnion (fun r => engineBothBadEvent L hL e0 strat hb d logF gateF r)

open Classical in
/-- **THE ENGINE'S OWN OUTER BAD EVENT ON THE ORACLE TABLE.**  Some coupled round
of either lane family agrees, at the alpha the SAME oracle drew.  THE TARGET MOVES
WITH THE TABLE THROUGH THE ALPHA CELL; this is what the adopted
`RawBlockLanes.rawOuterBadEvent` does not do. -/
noncomputable def engineOuterBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) : Finset (OracleTable (boundedQueries L)) :=
  engineOuterUpto L hL e0 strat hb d logF gateF d

open Classical in
/-- (2) **THE ADOPTED RAW OUTER EVENT IS THE CONSTANT-FAMILY SLICE OF THIS ONE.**
Set for set, on the nose.  So every adopted outer bound in the tree -- the adopted
`RawBlockLanes.raw_outer_bad_draw_probability_le`,
`raw_full_bad_draw_probability_le`, the adopted
`EngineTauDiagonal.raw_engine_full_bad_draw_probability_le` and their closed
instances -- is a statement about `engineOuterBadEvent … (fun _ => logLane)
(fun _ => gateLane)` and about nothing else. -/
theorem engine_outer_bad_event_constant_slice (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (logLane gateLane : RawLane) :
    rawOuterBadEvent L hL e0 strat hb logLane gateLane d
      = engineOuterBadEvent L hL e0 strat hb d (fun _ => logLane) (fun _ => gateLane) :=
  rfl

theorem engine_outer_upto_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) :
    engineOuterUpto L hL e0 strat hb d logF gateF 0
      = (∅ : Finset (OracleTable (boundedQueries L))) := by
  rw [engineOuterUpto, Finset.range_zero, Finset.biUnion_empty]

open Classical in
/-- (2) On the no-clash event, round `r`'s diagonal event is covered by the two
FIXED-STAGE events of the per-round bound: the adopted
`OuterLaneTransport.stage_no_clash_mono` nests the conditioning events. -/
theorem engine_outer_round_inter_subset (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) (n r : Nat) (hr : roundStage r ≤ n) :
    engineBothBadEvent L hL e0 strat hb d logF gateF r ∩ stageNoClash L hL e0 strat hb n
      ⊆ ((stageNoClash L hL e0 strat hb (roundStage r)).filter
            (fun T => stageTriple L hL e0 strat hb (roundStage r) 0 T
              ∈ engineOuterTarget L hL e0 strat hb d logF 0 r T))
        ∪ ((stageNoClash L hL e0 strat hb (roundStage r)).filter
            (fun T => stageTriple L hL e0 strat hb (roundStage r) 3 T
              ∈ engineOuterTarget L hL e0 strat hb d gateF 3 r T)) := by
  rw [engineBothBadEvent, Finset.union_inter_distrib_right, engineRoundBadEvent,
    engineRoundBadEvent]
  exact Finset.union_subset_union
    (univ_filter_inter_subset _ _ _ (stage_no_clash_mono L hL e0 strat hb (roundStage r) n hr))
    (univ_filter_inter_subset _ _ _ (stage_no_clash_mono L hL e0 strat hb (roundStage r) n hr))

/-- A `Nat`-to-`ℚ` split of `(k + 1) * x`, stated over an ABSTRACT `x` so that no
arithmetic tactic below is ever shown a `Fintype.card`.  READ HONESTY (vii). -/
theorem succ_mul_split (k : Nat) (x : ℚ) : ((k + 1 : Nat) : ℚ) * x = x + (k : ℚ) * x := by
  push_cast
  ring

open Classical in
/-- (2) **THE UNION OVER THE ROUNDS, ON THE NO-CLASH EVENT.**  Each summand is a
fixed-stage statement by the nesting, and each is the diagonal bound of
`engine_outer_round_mass_le`. -/
theorem engine_outer_upto_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) (hlcau : AlphaRawLaneCausal logF)
    (hgcau : AlphaRawLaneCausal gateF) (bl bg : Nat) (hlog : AlphaRawLaneBounded logF bl)
    (hgate : AlphaRawLaneBounded gateF bg) (n : Nat) :
    ∀ k : Nat, (∀ r, r < k → roundStage r ≤ n) →
      oracleProbability (boundedQueries L)
          (engineOuterUpto L hL e0 strat hb d logF gateF k ∩ stageNoClash L hL e0 strat hb n)
        ≤ (k : ℚ) * (((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [engine_outer_upto_zero, Finset.empty_inter, oracle_probability_empty,
        Nat.cast_zero, zero_mul]
  | succ k2 ih =>
      intro hk
      have hk2 : ∀ r, r < k2 → roundStage r ≤ n := fun r hr => hk r (by omega)
      have hkk : roundStage k2 ≤ n := hk k2 (by omega)
      have hsplit : engineOuterUpto L hL e0 strat hb d logF gateF (k2 + 1)
            ∩ stageNoClash L hL e0 strat hb n
          = (engineBothBadEvent L hL e0 strat hb d logF gateF k2
              ∩ stageNoClash L hL e0 strat hb n)
            ∪ (engineOuterUpto L hL e0 strat hb d logF gateF k2
              ∩ stageNoClash L hL e0 strat hb n) := by
        rw [engineOuterUpto, engineOuterUpto, Finset.range_succ, Finset.biUnion_insert,
          Finset.union_inter_distrib_right]
      have hround : oracleProbability (boundedQueries L)
          (engineBothBadEvent L hL e0 strat hb d logF gateF k2
            ∩ stageNoClash L hL e0 strat hb n)
          ≤ ((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
        refine le_trans (oracle_probability_mono (boundedQueries L) _ _
          (engine_outer_round_inter_subset L hL e0 strat hb d logF gateF n k2 hkk)) ?_
        refine le_trans (oracle_probability_union_le (boundedQueries L) _ _) ?_
        exact add_le_add
          (engine_outer_round_mass_le L hL e0 strat hb d logF hlcau bl hlog 0
            (small_counter_lt 2 (by omega)) k2)
          (engine_outer_round_mass_le L hL e0 strat hb d gateF hgcau bg hgate 3
            (small_counter_lt 5 (by omega)) k2)
      rw [hsplit, succ_mul_split k2 _]
      exact le_trans (oracle_probability_union_le (boundedQueries L) _ _)
        (add_le_add hround (ih hk2))

open Classical in
/-- (2) **THE HEADLINE OF THIS MODULE.**  Under the chain's no-clash event up to
any stage at or beyond the coupled rounds, the mass of the event that some coupled
round of either lane family agrees AT THE ALPHA THE SAME ORACLE DREW is at most
the adopted `ChallengeUnionBound.outerTerm d q` -- and NOTHING ELSE.  The diagonal
costs nothing.

THIS HOLDS FOR EVERY `StrategyChainBound.Strategy` and EVERY alpha-indexed lane
family obeying the protocol's causality and the adopted degree bounds, including
families no engine realizes.  READ THE HONESTY HEADER. -/
theorem engine_outer_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d q : Nat)
    (logF gateF : Element → RawLane) (hlcau : AlphaRawLaneCausal logF)
    (hgcau : AlphaRawLaneCausal gateF) (hlog : AlphaRawLaneBounded logF 5)
    (hgate : AlphaRawLaneBounded gateF (q + 2)) (n : Nat)
    (hrn : ∀ r, r < d → roundStage r ≤ n) :
    oracleProbability (boundedQueries L)
        (engineOuterBadEvent L hL e0 strat hb d logF gateF ∩ stageNoClash L hL e0 strat hb n)
      ≤ ChallengeUnionBound.outerTerm d q := by
  have h := engine_outer_upto_no_clash_mass_le L hL e0 strat hb d logF gateF hlcau hgcau 5
    (q + 2) hlog hgate n d hrn
  rw [round_terms_sum d q] at h
  rw [engineOuterBadEvent]
  exact h

open Classical in
/-- (2) **THE UNCONDITIONAL FORM.**  The adopted
`StrategyChainBound.strategy_chain_clash_probability_le` pays for the
conditioning.  The constant is the adopted `RawBlockLanes`'s own
`raw_outer_bad_draw_probability_le` constant, unchanged. -/
theorem engine_outer_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d q : Nat)
    (logF gateF : Element → RawLane) (hlcau : AlphaRawLaneCausal logF)
    (hgcau : AlphaRawLaneCausal gateF) (hlog : AlphaRawLaneBounded logF 5)
    (hgate : AlphaRawLaneBounded gateF (q + 2)) :
    oracleProbability (boundedQueries L)
        (engineOuterBadEvent L hL e0 strat hb d logF gateF)
      ≤ ChallengeUnionBound.outerTerm d q
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl (engineOuterBadEvent L hL e0 strat hb d logF gateF)
      (stageNoClash L hL e0 strat hb (22 + 5 * d)))
  have hunion := oracle_probability_union_le (boundedQueries L)
    (engineOuterBadEvent L hL e0 strat hb d logF gateF
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
  have hround := engine_outer_no_clash_mass_le L hL e0 strat hb d q logF gateF hlcau hgcau
    hlog hgate (22 + 5 * d) (fun r hr => round_stage_le r d hr)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
      ≤ ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL e0 strat hb (22 + 5 * d)
  linarith

/-! ## 3. ALL FOUR FAMILIES THE ENGINE'S OWN -/

open Classical in
/-- **THE FULL BAD EVENT WITH THE ENGINE'S OWN OUTER EVENT AND THE ENGINE'S OWN
TAU EVENT.**  The adopted `EngineTauDiagonal.rawEngineFullBadEvent` with its
`∀`-lane outer summand replaced by the diagonal one of section 2. -/
noncomputable def rawEngineAllOwnBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d rows : Nat)
    (logF gateF : Element → RawLane) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) : Finset (OracleTable (boundedQueries L)) :=
  (engineOuterBadEvent L hL e0 strat hb d logF gateF ∪ engineTauBadEvent L hL e0 strat hb d G)
    ∪ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf

open Classical in
theorem mem_raw_engine_all_own_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d rows : Nat)
    (logF gateF : Element → RawLane) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) (T : OracleTable (boundedQueries L)) :
    T ∈ rawEngineAllOwnBadEvent L hL e0 strat hb d rows logF gateF G coeffsOf ↔
      (T ∈ engineOuterBadEvent L hL e0 strat hb d logF gateF ∨
        T ∈ engineTauBadEvent L hL e0 strat hb d G ∨
        T ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf) := by
  simp only [rawEngineAllOwnBadEvent, Finset.mem_union, or_assoc]

open Classical in
/-- (3) **THE ADOPTED `EngineTauDiagonal` EVENT IS THE CONSTANT-FAMILY SLICE OF
THIS ONE**, set for set, on the nose. -/
theorem raw_engine_all_own_bad_event_constant_slice (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (logLane gateLane : RawLane) (d rows : Nat) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) :
    rawEngineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf
      = rawEngineAllOwnBadEvent L hL e0 strat hb d rows (fun _ => logLane) (fun _ => gateLane)
          G coeffsOf :=
  rfl

open Classical in
/-- (3) **THE THREE BLOCK-LEVEL MASSES AT AN ARBITRARY CONDITIONING STAGE AT OR
BEYOND THE ROUNDS.**  Isolated so that the index summand can be added under ONE
complement term, exactly as the adopted
`EngineTauDiagonal.raw_engine_full_no_clash_mass_le` does. -/
theorem raw_engine_all_own_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d q rows constraints : Nat)
    (logF gateF : Element → RawLane) (hlcau : AlphaRawLaneCausal logF)
    (hgcau : AlphaRawLaneCausal gateF) (hlog : AlphaRawLaneBounded logF 5)
    (hgate : AlphaRawLaneBounded gateF (q + 2)) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) (n : Nat)
    (hn : deriveStage ≤ n) (hrn : ∀ r, r < d → roundStage r ≤ n) :
    oracleProbability (boundedQueries L)
        (rawEngineAllOwnBadEvent L hL e0 strat hb d rows logF gateF G coeffsOf
          ∩ stageNoClash L hL e0 strat hb n)
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints := by
  have hnest : stageNoClash L hL e0 strat hb n
      ⊆ stageNoClash L hL e0 strat hb deriveStage :=
    stage_no_clash_mono L hL e0 strat hb deriveStage n hn
  have hu3 := ReducedEngineIndex.inter_union_mass_le L
    (engineOuterBadEvent L hL e0 strat hb d logF gateF ∪ engineTauBadEvent L hL e0 strat hb d G)
    (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf)
    (stageNoClash L hL e0 strat hb n)
  have hu4 := ReducedEngineIndex.inter_union_mass_le L
    (engineOuterBadEvent L hL e0 strat hb d logF gateF)
    (engineTauBadEvent L hL e0 strat hb d G)
    (stageNoClash L hL e0 strat hb n)
  have houter := engine_outer_no_clash_mass_le L hL e0 strat hb d q logF gateF hlcau hgcau
    hlog hgate n hrn
  have htau := engine_tau_no_clash_mass_le_at L hL e0 strat hb d G hdu n hn
  have halphasub : gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
        ∩ stageNoClash L hL e0 strat hb n
      ⊆ (stageNoClash L hL e0 strat hb deriveStage).filter (fun T =>
          stageTriple L hL e0 strat hb deriveStage (alphaBase d) T
            ∈ OuterChallenge.tupleEvent
                (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)) := by
    rw [gateAlphaBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have halpha : oracleProbability (boundedQueries L)
      (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
        ∩ stageNoClash L hL e0 strat hb n)
      ≤ ChallengeUnionBound.alphaTerm rows constraints :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ halphasub)
      (gate_alpha_no_clash_mass_le L hL e0 strat hb d rows constraints coeffsOf hdu hclen)
  rw [rawEngineAllOwnBadEvent]
  linarith

open Classical in
/-- (3) **THE BLOCK-LEVEL HEADLINE**: outer diagonal, tau diagonal and alpha, all
at the engine's own data, unconditionally. -/
theorem raw_engine_all_own_block_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (d q constraints : Nat) (logF gateF : Element → RawLane)
    (hlcau : AlphaRawLaneCausal logF) (hgcau : AlphaRawLaneCausal gateF)
    (hlog : AlphaRawLaneBounded logF 5) (hgate : AlphaRawLaneBounded gateF (q + 2))
    (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawEngineAllOwnBadEvent L hL e0 strat hb d (2 ^ d) logF gateF G coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (rawEngineAllOwnBadEvent L hL e0 strat hb d (2 ^ d) logF gateF G coeffsOf)
      (stageNoClash L hL e0 strat hb (22 + 5 * d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (rawEngineAllOwnBadEvent L hL e0 strat hb d (2 ^ d) logF gateF G coeffsOf
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
  have hfull := raw_engine_all_own_no_clash_mass_le L hL e0 strat hb d q (2 ^ d) constraints
    logF gateF hlcau hgcau hlog hgate G coeffsOf hdu hclen (22 + 5 * d)
    (by rw [deriveStage]; omega) (fun r hr => round_stage_le r d hr)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
      ≤ ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL e0 strat hb (22 + 5 * d)
  rw [ChallengeUnionBound.combinedBound]
  linarith

open Classical in
/-- **ALL FOUR FAMILIES, THE ENGINE'S OWN.**  The outer diagonal of section 2, the
adopted `EngineTauDiagonal.engineTauBadEvent`, the adopted
`ReducedFullTransport.gateAlphaBadEvent` and the adopted
`RawIndexLanes.rawEngineIndexBadEvent`. -/
noncomputable def rawEngineAllOwnIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (logF gateF : Element → RawLane)
    (rows : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) :
    Finset (OracleTable (boundedQueries L)) :=
  rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
      hbE d rows logF gateF G coeffsOf
    ∪ RawIndexLanes.rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS
        cellIndex cols

open Classical in
/-- (3) **THE ADOPTED `EngineTauDiagonal` SECTION-5 UNION IS THE CONSTANT-FAMILY
SLICE OF THIS ONE**, set for set. -/
theorem raw_engine_all_own_index_bad_event_constant_slice (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (logLane gateLane : RawLane)
    (rows : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) :
    rawEngineFullIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logLane gateLane
        rows G coeffsOf cellIndex cols
      = rawEngineAllOwnIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS
          (fun _ => logLane) (fun _ => gateLane) rows G coeffsOf cellIndex cols :=
  rfl

open Classical in
/-- **THE HEADLINE OF SECTION 3, AND THE FIRST BOUND IN THIS TREE WITH ALL FOUR
FAMILIES THE ENGINE'S OWN.**  For EVERY `StrategyChainBound.RoundCausal S`, EVERY
`RawIndexLanes.ClaimsCausal d U`, EVERY alpha-indexed lane family obeying the
protocol's causality and the adopted degree bounds, and EVERY alpha-to-table map
`G`:

  `<= combinedBound d q d constraints + 2 tauTerm c.indexBits + ONE clash term at
   stage 22 + 5 d + 8`.

WHICH FAMILIES ARE THE ENGINE'S OWN: ALL FOUR.  OUTER -- the diagonal of section 2
(this module).  TAU -- the adopted `EngineTauDiagonal.engineTauBadEvent`.  INDEX --
the adopted `RawIndexLanes.rawEngineIndexBadEvent`.  ALPHA -- the adopted
`gateAlphaBadEvent` at a fixed `coeffsOf`, which mentions no challenge at all
(adopted `CommitmentOrderSurvey.coefficients_are_determined_by_the_tables`, whose
own premise pins `coeffsOf` to `prefixCoeffTable c gates publicHash t`) and so
needs no diagonal.  READ THE STATEMENT: in THIS theorem the lane families are
still `∀`-QUANTIFIED -- the engine's own families are substituted only in section
5's closed instance.  THE ARGUMENTS STILL UNIDENTIFIED ARE `tables = s0.tables`
(with `coeffsOf` pinned to those tables) AND, FOR THE OUTER SUMMAND ALONE, the
lane-list identification.  READ THE HONESTY HEADER, AND "THE PRECISE REMAINING
STEP". -/
theorem raw_engine_all_own_bad_draw_probability_le (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat) (hU : RawIndexLanes.ClaimsCausal d U)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (logF gateF : Element → RawLane)
    (hlcau : AlphaRawLaneCausal logF) (hgcau : AlphaRawLaneCausal gateF)
    (q constraints : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hlog : AlphaRawLaneBounded logF 5) (hgate : AlphaRawLaneBounded gateF (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawEngineAllOwnIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logF gateF
          (2 ^ d) G coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((ReducedIndexLanes.indexStage d : Nat) : ℚ)
            * (((ReducedIndexLanes.indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have heq : rawEngineAllOwnIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logF
        gateF (2 ^ d) G coeffsOf cellIndex cols
      = rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S U d) hbE d (2 ^ d) logF gateF G coeffsOf
        ∪ RawIndexLanes.rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
            (ReducedEngineIndex.committedOf cols cellIndex) := by
    rw [rawEngineAllOwnIndexBadEvent, RawIndexLanes.raw_engine_index_bad_event_eq gdec hash khash
      P c₀ L hL c s S hS U d hU hbE hbS hdeg hdb cellIndex cols]
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S U d) hbE d (2 ^ d) logF gateF G coeffsOf
        ∪ RawIndexLanes.rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
            (ReducedEngineIndex.committedOf cols cellIndex))
      (stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
        hbE (ReducedIndexLanes.indexStage d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    ((rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S U d) hbE d (2 ^ d) logF gateF G coeffsOf
        ∪ RawIndexLanes.rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
            (ReducedEngineIndex.committedOf cols cellIndex))
      ∩ stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
          hbE (ReducedIndexLanes.indexStage d))
    ((stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
      hbE (ReducedIndexLanes.indexStage d))ᶜ)
  have hs1 := ReducedEngineIndex.inter_union_mass_le L
    (rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S U d) hbE d (2 ^ d) logF gateF G coeffsOf)
    (RawIndexLanes.rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
      (ReducedEngineIndex.committedOf cols cellIndex))
    (stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
      hbE (ReducedIndexLanes.indexStage d))
  have hfull := raw_engine_all_own_no_clash_mass_le L hL OuterInitial.zeroDigest
    (RawIndexLanes.rawExtendedShape c s S U d) hbE d q (2 ^ d) constraints logF gateF hlcau
    hgcau hlog hgate G coeffsOf hdu hclen (ReducedIndexLanes.indexStage d)
    (le_of_lt (ReducedIndexLanes.derive_stage_lt_index_stage d))
    (fun r hr => le_of_lt (ReducedIndexLanes.round_stage_lt_index_stage r d hr))
  have hidx := RawIndexLanes.raw_index_bad_event_no_clash_mass_le L hL c s S U d c.indexBits
    hU hbE cellIndex (ReducedEngineIndex.committedOf cols cellIndex) hbu
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
        hbE (ReducedIndexLanes.indexStage d))ᶜ)
      ≤ ((ReducedIndexLanes.indexStage d : Nat) : ℚ)
          * (((ReducedIndexLanes.indexStage d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S U d) hbE (ReducedIndexLanes.indexStage d)
  rw [heq, ChallengeUnionBound.combinedBound]
  linarith

/-! ## 4. THE IDENTIFICATION: THE RUN'S OWN DRAW AT THE RUN'S OWN ALPHA -/

open Classical in
/-- (4) Membership in the diagonal round event at a table `T` is membership in the
adopted `RawBlockLanes.rawRoundBadEvent` OF THE LANE THE ALPHA AT `T` SELECTS.
The two `Finset`s are different -- one fixes the lane, the other lets it move --
but they agree at `T`, which is all a pointwise argument needs. -/
theorem mem_engine_round_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (F : Element → RawLane)
    (base r : Nat) (T : OracleTable (boundedQueries L)) :
    T ∈ engineRoundBadEvent L hL e0 strat hb d F base r ↔
      T ∈ rawRoundBadEvent L hL e0 strat hb (F (alphaRead L hL e0 strat hb d T)) base r := by
  rw [engineRoundBadEvent, rawRoundBadEvent, Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact Iff.rfl

open Classical in
/-- (4) The diagonal outer event, unfolded to the two per-lane round disjunctions
at the alpha the oracle drew. -/
theorem mem_engine_outer_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) (T : OracleTable (boundedQueries L)) :
    T ∈ engineOuterBadEvent L hL e0 strat hb d logF gateF ↔
      ((∃ i, i < d ∧
          T ∈ rawRoundBadEvent L hL e0 strat hb (logF (alphaRead L hL e0 strat hb d T)) 0 i) ∨
        (∃ i, i < d ∧
          T ∈ rawRoundBadEvent L hL e0 strat hb (gateF (alphaRead L hL e0 strat hb d T)) 3 i)) := by
  rw [engineOuterBadEvent, engineOuterUpto, Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hr, hmem⟩
    rw [Finset.mem_range] at hr
    rw [engineBothBadEvent, Finset.mem_union] at hmem
    rcases hmem with hmem | hmem
    · exact Or.inl ⟨r, hr, (mem_engine_round_bad_event L hL e0 strat hb d logF 0 r T).mp hmem⟩
    · exact Or.inr ⟨r, hr, (mem_engine_round_bad_event L hL e0 strat hb d gateF 3 r T).mp hmem⟩
  · rintro (⟨i, hi, hmem⟩ | ⟨i, hi, hmem⟩)
    · exact ⟨i, Finset.mem_range.mpr hi, Finset.mem_union.mpr
        (Or.inl ((mem_engine_round_bad_event L hL e0 strat hb d logF 0 i T).mpr hmem))⟩
    · exact ⟨i, Finset.mem_range.mpr hi, Finset.mem_union.mpr
        (Or.inr ((mem_engine_round_bad_event L hL e0 strat hb d gateF 3 i T).mpr hmem))⟩

open Classical in
/-- **THE RUN-LEVEL FORM OF THE DIAGONAL OUTER EVENT.**  The tables at which the
RUN'S OWN joint draw -- the digest triples the chain actually squeezes -- lands in
the adopted `JointChallengeSpace.outerEvent` of the lane rounds the prover
actually played, AT THE ALPHA THE SAME ORACLE DREW.  This is the adopted
`RunLevelTransportAudit.runLevelOuterEvent` with the FIXED lanes replaced by the
alpha-indexed family read at the table's own alpha cell. -/
noncomputable def runLevelEngineOuterEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T ∈
      JointChallengeSpace.outerEvent d
        (logF (alphaRead L hL e0 strat hb d T)).truthClaim
        (gateF (alphaRead L hL e0 strat hb d T)).truthClaim
        (RunLevelTransportAudit.realizedRounds L hL e0 strat hb
          (logF (alphaRead L hL e0 strat hb d T)) 0 T 0 d)
        (RunLevelTransportAudit.realizedRounds L hL e0 strat hb
          (gateF (alphaRead L hL e0 strat hb d T)) 3 T 0 d))

open Classical in
/-- (4) **THE DIAGONAL OUTER EVENT IS THE RUN-LEVEL ONE**, `Finset` for `Finset`,
at every strategy and every alpha-indexed family whose claimed running claim
starts at the adopted `0`.  The adopted
`RunLevelTransportAudit.outer_lane_event_iff` applied, at each table separately,
to the member the alpha at that table selects. -/
theorem engine_outer_bad_event_is_run_level (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (logF gateF : Element → RawLane) (hlc : ∀ a : Element, (logF a).claim = 0)
    (hgc : ∀ a : Element, (gateF a).claim = 0) :
    engineOuterBadEvent L hL e0 strat hb d logF gateF
      = runLevelEngineOuterEvent L hL e0 strat hb d logF gateF := by
  ext T
  have hrun : T ∈ runLevelEngineOuterEvent L hL e0 strat hb d logF gateF ↔
      RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T ∈
        JointChallengeSpace.outerEvent d
          (logF (alphaRead L hL e0 strat hb d T)).truthClaim
          (gateF (alphaRead L hL e0 strat hb d T)).truthClaim
          (RunLevelTransportAudit.realizedRounds L hL e0 strat hb
            (logF (alphaRead L hL e0 strat hb d T)) 0 T 0 d)
          (RunLevelTransportAudit.realizedRounds L hL e0 strat hb
            (gateF (alphaRead L hL e0 strat hb d T)) 3 T 0 d) := by
    rw [runLevelEngineOuterEvent, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  rw [hrun, JointChallengeSpace.outerEvent, Finset.mem_union,
    RunLevelTransportAudit.outer_lane_event_iff L hL e0 strat hb
      (logF (alphaRead L hL e0 strat hb d T)) 0 d (JointChallengeSpace.logProj d) T
      (fun j hj => RunLevelTransportAudit.realized_draw_log_proj L hL e0 strat hb d T j hj)
      0 (logF (alphaRead L hL e0 strat hb d T)).truthClaim (hlc _) rfl,
    RunLevelTransportAudit.outer_lane_event_iff L hL e0 strat hb
      (gateF (alphaRead L hL e0 strat hb d T)) 3 d (JointChallengeSpace.gateProj d) T
      (fun j hj => RunLevelTransportAudit.realized_draw_gate_proj L hL e0 strat hb d T j hj)
      0 (gateF (alphaRead L hL e0 strat hb d T)).truthClaim (hgc _) rfl]
  exact mem_engine_outer_bad_event L hL e0 strat hb d logF gateF T

open Classical in
/-- (4) **THE IDENTIFICATION, AT THE ADOPTED `RawBlockLanes.strategicShape`
PROVER.**  The event section 2 bounds IS

  `{T | actualDigestDraw (hashOf T) c (realizedRunProof … T)
        ∈ JointChallengeSpace.outerEvent d a b (realized log rounds) (realized gate rounds)}`

with BOTH the draw and the alpha the RUN'S OWN: the draw is the adopted
`InstalledRoundCommit.actualDigestDraw` at the adopted
`RunLevelTransportAudit.realizedRunProof` (the adopted
`realized_draw_is_actual_digest_draw`), and the alpha selecting the lane family is
the adopted `TranscriptProvenance.gateAlphaElement` at the TABLE'S OWN HASH and at
that same realized proof (the adopted
`EngineTauDiagonal.alpha_read_is_gate_alpha_element`).  BOTH ARE PROVED, NOT
ASSUMED.

THIS IS AS FAR AS THIS MODULE GOES TOWARD THE ADOPTED
`SoundnessAssembly.outerBadEvent` along the ALPHA and DRAW axes; the ONE leg that
remains -- the lane-list identification -- is spelled out under "THE PRECISE
REMAINING STEP" in the header, and it is not assumed anywhere.  The walk bridge is
NOT a second leg: `frozen_walk_of_realized_gate` / `frozen_walk_of_realized_log`
below discharge it outright. -/
theorem engine_outer_event_is_the_run_outer_event_at_the_engine_alpha (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hbS : StrategyBounded L (strategicShape c s S)) (logF gateF : Element → RawLane)
    (hlc : ∀ a : Element, (logF a).claim = 0) (hgc : ∀ a : Element, (gateF a).claim = 0) :
    engineOuterBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hbS c.degreeBits
        logF gateF
      = Finset.univ.filter (fun T =>
          InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c
              (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
            ∈ JointChallengeSpace.outerEvent c.degreeBits
                (logF (TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
                  (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits
                    T))).truthClaim
                (gateF (TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
                  (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits
                    T))).truthClaim
                (RunLevelTransportAudit.realizedRounds L hL OuterInitial.zeroDigest
                  (strategicShape c s S) hbS
                  (logF (TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
                    (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)))
                  0 T 0 c.degreeBits)
                (RunLevelTransportAudit.realizedRounds L hL OuterInitial.zeroDigest
                  (strategicShape c s S) hbS
                  (gateF (TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
                    (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)))
                  3 T 0 c.degreeBits)) := by
  rw [engine_outer_bad_event_is_run_level L hL OuterInitial.zeroDigest (strategicShape c s S)
    hbS c.degreeBits logF gateF hlc hgc, runLevelEngineOuterEvent]
  refine Finset.filter_congr (fun T _ => ?_)
  rw [RunLevelTransportAudit.realized_draw_is_actual_digest_draw L hL c s S hbS hS T,
    alpha_read_is_gate_alpha_element L hL c s S hbS hS T]

/-- (4) **THE REALIZED DRAW CARRIES THE REALIZED GATE ROUNDS' OWN CHALLENGES, BY
CONSTRUCTION AND WITH NO HYPOTHESIS.**  The `challenge` field of the adopted
`RunLevelTransportAudit.realizedRounds` IS the reduced stage triple the chain
squeezes at `roundStage k`, and the adopted
`RunLevelTransportAudit.realized_draw_gate_proj` says the realized draw's gate
coordinate at `k` is that very triple.  So the adopted
`JointChallengeSpace.DrawnAt` -- the ONLY thing the adopted
`AdaptiveAgreementFamily.frozen_gate_walk` asks of a draw -- holds at the realized
draw for this module's own lane rounds, for EVERY table.  READ "THE PRECISE
REMAINING STEP": this is why the walk bridge is NOT an obstacle. -/
theorem drawn_at_realized_gate (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (d : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ (n k : Nat), k + n ≤ d →
      JointChallengeSpace.DrawnAt d (RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T)
        (JointChallengeSpace.gateProj d)
        (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane 3 T k n) k
  | 0, k, _ => by
      rw [RunLevelTransportAudit.realizedRounds]
      exact trivial
  | n + 1, k, hkn => by
      rw [RunLevelTransportAudit.realizedRounds]
      refine ⟨?_, drawn_at_realized_gate L hL e0 strat hb lane d T n (k + 1) (by omega)⟩
      show OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) 3 T)
        = OuterChallenge.reduceTriple
            (RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T
              (JointChallengeSpace.gateProj d k))
      rw [RunLevelTransportAudit.realized_draw_gate_proj L hL e0 strat hb d T k (by omega)]

/-- (4) **THE SAME FOR THE LOG COORDINATES**, through the adopted
`RunLevelTransportAudit.realized_draw_log_proj`. -/
theorem drawn_at_realized_log (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (d : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ (n k : Nat), k + n ≤ d →
      JointChallengeSpace.DrawnAt d (RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T)
        (JointChallengeSpace.logProj d)
        (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane 0 T k n) k
  | 0, k, _ => by
      rw [RunLevelTransportAudit.realizedRounds]
      exact trivial
  | n + 1, k, hkn => by
      rw [RunLevelTransportAudit.realizedRounds]
      refine ⟨?_, drawn_at_realized_log L hL e0 strat hb lane d T n (k + 1) (by omega)⟩
      show OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) 0 T)
        = OuterChallenge.reduceTriple
            (RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T
              (JointChallengeSpace.logProj d k))
      rw [RunLevelTransportAudit.realized_draw_log_proj L hL e0 strat hb d T k (by omega)]

/-- (4) **THE WALK BRIDGE AT THE REALIZED DRAW, GATE SIDE, WITH NO HYPOTHESIS.**
The adopted `AdaptiveAgreementFamily`'s FROZEN walk of this module's own realized
gate rounds IS the adopted `JointChallengeSpace.laneEvent` of those same rounds, at
the realized draw.  The adopted `AdaptiveAgreementFamily.frozen_gate_walk` at
`drawn_at_realized_gate`, with the list length supplied by the adopted
`RunLevelTransportAudit.realized_rounds_length` so that the left side is the
adopted `OuterSequentialConditioning.adaptiveLaneEvent` on the nose.  The two
`Element` arguments are FREE: the adopted `AdaptiveAgreementFamily.frozenLane`
reads only the rounds' `message` and `truth` fields, never their `challenge`
field, which is exactly why the remaining lane-list identification does not have
to match challenges. -/
theorem frozen_walk_of_realized_gate (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (d : Nat)
    (T : OracleTable (boundedQueries L)) (a b : Element) :
    (RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T ∈
        OuterSequentialConditioning.adaptiveLaneEvent d
          (AdaptiveAgreementFamily.frozenLane
            (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane 3 T 0 d) a b false))
      ↔ RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T ∈
          JointChallengeSpace.laneEvent d (JointChallengeSpace.gateProj d) a b
            (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane 3 T 0 d) 0 := by
  have h := AdaptiveAgreementFamily.frozen_gate_walk d
    (RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T)
    (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane 3 T 0 d) a b 0
    (drawn_at_realized_gate L hL e0 strat hb lane d T d 0 (by omega))
  rw [RunLevelTransportAudit.realized_rounds_length L hL e0 strat hb lane 3 T d 0] at h
  rw [AdaptiveAgreementFamily.adaptiveLaneEvent_eq]
  exact h

/-- (4) **THE WALK BRIDGE AT THE REALIZED DRAW, LOG SIDE**, through the adopted
`AdaptiveAgreementFamily.frozen_log_walk` -- the lane that owns the EVEN
coordinates of the adopted interleaved schedule. -/
theorem frozen_walk_of_realized_log (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (d : Nat)
    (T : OracleTable (boundedQueries L)) (a b : Element) :
    (RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T ∈
        OuterSequentialConditioning.adaptiveLaneEvent d
          (AdaptiveAgreementFamily.frozenLane
            (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane 0 T 0 d) a b true))
      ↔ RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T ∈
          JointChallengeSpace.laneEvent d (JointChallengeSpace.logProj d) a b
            (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane 0 T 0 d) 0 := by
  have h := AdaptiveAgreementFamily.frozen_log_walk d
    (RunLevelTransportAudit.realizedDraw L hL e0 strat hb d T)
    (RunLevelTransportAudit.realizedRounds L hL e0 strat hb lane 0 T 0 d) a b 0
    (drawn_at_realized_log L hL e0 strat hb lane d T d 0 (by omega))
  rw [RunLevelTransportAudit.realized_rounds_length L hL e0 strat hb lane 0 T d 0] at h
  rw [AdaptiveAgreementFamily.adaptiveLaneEvent_eq]
  exact h

/-! ## 5. A GENUINELY MOVING OUTER TARGET, THE ENGINE'S OWN FAMILY, AND THE
CLOSED INSTANCE -/

/-- **AN ALPHA-INDEXED RAW LANE FAMILY WHOSE ROUND-`0` TARGET GENUINELY MOVES.**
Its claimed running claim is `1` and its truth claim IS THE ALPHA, so at alpha `1`
the adopted `ConditionalSoundness.roundBadSet` takes its DIAGONAL branch and the
target is EMPTY, while at alpha `0` the family is the adopted
`RawBlockLanes.separatedRawLane`, whose round-`0` target is INHABITED. -/
def sampleOuterLane : Element → RawLane :=
  fun a => { message := fun _ _ => [1], truth := fun _ _ => [], claim := 1, truthClaim := a }

/-- (5) At alpha `0` the family IS the adopted `RawBlockLanes.separatedRawLane`. -/
theorem sample_outer_lane_at_zero : sampleOuterLane 0 = separatedRawLane := rfl

/-- (5) It obeys the protocol's causality at every alpha (its messages read no
challenge at all). -/
theorem sample_outer_lane_causal : AlphaRawLaneCausal sampleOuterLane :=
  fun _ => ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- (5) And the adopted degree bound at every alpha, uniformly. -/
theorem sample_outer_lane_bounded (b : Nat) (hbb : 1 ≤ b) :
    AlphaRawLaneBounded sampleOuterLane b := by
  refine fun _ _ _ => ⟨?_, Nat.zero_le _⟩
  show ([(1 : Element)]).length ≤ b
  exact hbb

/-- (5) **A RAW LANE WHOSE TWO INITIAL CLAIMS COINCIDE HAS AN EMPTY ROUND-`0` BAD
SET**: the adopted `ConditionalSoundness.roundBadSet` takes its DIAGONAL branch.
Stated over an ABSTRACT lane, exactly as the adopted
`RawBlockLanes.raw_target_zero_nonempty_of_agreement` is, so that no tactic is
ever asked to decide an equality of two concrete `Element`s -- the adopted
`OuterLaneTransport` HONESTY (vii) constraint, and a hard one.  READ
HONESTY (vii). -/
theorem raw_bad_set_zero_empty_of_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) (heq : lane.claim = lane.truthClaim) :
    rawBadSet L hL e0 strat hb lane base 0 T = (∅ : Finset Element) := by
  have hc1 : (rawClaims L hL e0 strat hb lane base T 0).1 = lane.claim := rfl
  have hc2 : (rawClaims L hL e0 strat hb lane base T 0).2 = lane.truthClaim := rfl
  rw [rawBadSet, ConditionalSoundness.roundBadSet, hc1, hc2, if_pos heq]

/-- (5) **AND THEN AN EMPTY ROUND-`0` TARGET**, counted rather than enumerated:
the adopted `OuterChallenge.fixed_point_set_preimage_bound` caps the pullback's
cardinality by `points.card * fiberCeiling ^ 3`, which is `0`.  Phrased as a
CARDINALITY so that no membership over `OuterChallenge.DigestTriple` is ever
elaborated.  READ HONESTY (vii). -/
theorem raw_target_zero_card_eq_zero_of_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) (heq : lane.claim = lane.truthClaim) :
    (rawTarget L hL e0 strat hb lane base 0 T).card = 0 := by
  have h := OuterChallenge.fixed_point_set_preimage_bound
    (rawBadSet L hL e0 strat hb lane base 0 T)
  have hz : (rawBadSet L hL e0 strat hb lane base 0 T).card
      * OuterChallenge.fiberCeiling ^ 3 = 0 := by
    rw [raw_bad_set_zero_empty_of_eq L hL e0 strat hb lane base T heq, Finset.card_empty,
      Nat.zero_mul]
  exact Nat.le_zero.mp (le_of_le_of_eq h hz)

/-- (5) **THE OUTER TARGET GENUINELY DEPENDS ON THE ALPHA CELL.**  At alpha `0`
the family IS the adopted `RawBlockLanes.separatedRawLane`, whose round-`0` target
is INHABITED (the adopted `separated_raw_target_zero_nonempty`); at alpha `1` its
two initial claims coincide and the target has no point at all.  So the diagonal of
section 2 is not a disguised constant-target statement: the set round `0`'s coupled
challenge is tested against really does move with the answer the oracle gives at
the alpha cell.  This is the outer counterpart of the adopted
`EngineTauDiagonal.engine_tau_target_depends_on_alpha`. -/
theorem sample_outer_target_depends_on_alpha (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (base : Nat)
    (T : OracleTable (boundedQueries L)) :
    rawTarget L hL e0 strat hb (sampleOuterLane 0) base 0 T
      ≠ rawTarget L hL e0 strat hb (sampleOuterLane 1) base 0 T := by
  intro h
  have h1 := raw_target_zero_card_eq_zero_of_eq L hL e0 strat hb (sampleOuterLane 1) base T rfl
  have h0 : 0 < (rawTarget L hL e0 strat hb (sampleOuterLane 0) base 0 T).card :=
    Finset.card_pos.mpr (separated_raw_target_zero_nonempty L hL e0 strat hb base T)
  rw [h, h1] at h0
  exact Nat.lt_irrefl 0 h0

/-- **THE ENGINE'S OWN ALPHA-TO-TRUTH-CLAIM MAP.**  The adopted
`GateClaimChain.endpointSum` with the alpha LEFT FREE.  The adopted
`SoundnessAssembly.gateLane`'s truth claim is this map applied to the adopted
`TranscriptProvenance.gateAlphaElement`. -/
def engineEndpoint (c : Verifier.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (s0 : GateTerminalBinding.ProverState) :
    Element → Element :=
  fun a => GateClaimChain.endpointSum (Integrated.gateConfig c) gates publicHash a s0

/-- (5) **THE ENGINE'S GATE LANE IS THAT MAP AT THE DRAWN ALPHA**, by definition:
the `b` field of the adopted `SoundnessAssembly.gateLane`.  This is the OUTER
counterpart of the adopted `EngineTauDiagonal.engine_gate_at_the_drawn_alpha`. -/
theorem engine_endpoint_is_the_gate_lane_truth_claim (thash : Transcript.Hash)
    (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (gateTruths : List (List Element)) :
    SoundnessAssembly.gateLane thash E c p gates s0 gateTruths
      = AdaptiveAgreementFamily.frozenLane (ConditionalSoundness.gateLaneOf E c p gateTruths) 0
          (engineEndpoint c gates
              (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs)) s0
            (TranscriptProvenance.gateAlphaElement thash c p)) false := rfl

/-- **THE ENGINE'S OWN ALPHA-INDEXED GATE LANE, AT A RAW STRATEGY.**  The
strategy's own gate cell as the round message, a free truth column, the adopted
claimed running claim `0`, and THE TRUTH CLAIM THE ENGINE USES -- the adopted
`GateClaimChain.endpointSum` AT THE ALPHA. -/
def engineGateLaneOfStrategy (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (B : Element → Element) :
    Element → RawLane :=
  fun a => rawGateLaneOfStrategy S tr 0 (B a)

theorem engine_gate_lane_of_strategy_causal
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (tr : Nat → (Nat → Nat → Block) → List Element) (htr : RawCausal tr)
    (B : Element → Element) : AlphaRawLaneCausal (engineGateLaneOfStrategy S tr B) :=
  fun a => raw_gate_lane_causal S hS tr htr 0 (B a)

theorem engine_gate_lane_of_strategy_bounded
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (B : Element → Element) (bd : Nat)
    (hS : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ bd)
    (htr : ∀ (r : Nat) (ch : Nat → Nat → Block), (tr r ch).length ≤ bd) :
    AlphaRawLaneBounded (engineGateLaneOfStrategy S tr B) bd :=
  fun a => raw_gate_lane_bounded S tr 0 (B a) bd hS htr

theorem engine_gate_lane_of_strategy_claim
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (B : Element → Element) (a : Element) :
    (engineGateLaneOfStrategy S tr B a).claim = 0 := rfl

/-- **THE LOG FAMILY IS CONSTANT IN THE ALPHA**, and that is not an omission: the
adopted `SoundnessAssembly.logLane` is the adopted
`AdaptiveAgreementFamily.frozenLane` at the adopted
`JointChallengeSpace.logCompareOf t pr`, which reads NO transcript coordinate.
The alpha enters the engine's outer event through the GATE lane only. -/
def constantLogLaneOfStrategy (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (b : Element) : Element → RawLane :=
  fun _ => rawLogLaneOfStrategy S tr 0 b

theorem constant_log_lane_of_strategy_causal
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (tr : Nat → (Nat → Nat → Block) → List Element) (htr : RawCausal tr) (b : Element) :
    AlphaRawLaneCausal (constantLogLaneOfStrategy S tr b) :=
  fun _ => raw_log_lane_causal S hS tr htr 0 b

theorem constant_log_lane_of_strategy_bounded
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (b : Element) (bd : Nat)
    (hS : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ bd)
    (htr : ∀ (r : Nat) (ch : Nat → Nat → Block), (tr r ch).length ≤ bd) :
    AlphaRawLaneBounded (constantLogLaneOfStrategy S tr b) bd :=
  fun _ => raw_log_lane_bounded S tr 0 b bd hS htr

theorem constant_log_lane_of_strategy_claim
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (b : Element) (a : Element) :
    (constantLogLaneOfStrategy S tr b a).claim = 0 := rfl

open Classical in
/-- (5) **THE CLOSED INSTANCE AT THE ENVELOPE'S THIRTEEN COUPLED ROUNDS.**  The
adopted `RawIndexLanes.raw_index_engine_bound_at_thirteen`'s own closed setting --
thirteen coupled rounds, `quotientDegree = 8`, `numGateConstraints = 123`,
`indexBits = 8`, the adopted genuinely raw
`StrategyChainBound.challengeTruncatedMessage` as the round-message choice and the
adopted `RawIndexLanes.blockClaims u0 u1` as the used-claims choice -- now carrying
THE ENGINE'S OWN OUTER EVENT at the engine's own alpha-to-truth-claim map
`engineEndpoint` AND the engine's own tau event at the engine's own alpha-to-table
map `EngineTauDiagonal.engineGate`, at the SAME constant:

  `<= combinedBound 13 8 13 123 + 2 * tauTerm 8 + 4560 / |Block|`.

READ OFF THE STATEMENT WHAT THE TRUTH COLUMN IS HERE: both families are built at
the adopted `RawBlockLanes.rawZeroTruth`, the truth choice that returns the EMPTY
list at every round and every challenge view.  That is a legitimate instance of
the free `truth` field -- the adopted `SoundnessAssembly.outerBadEvent` takes the
truth columns as SUPPLIED data -- but it is a PARTICULAR one, chosen because the
adopted `raw_zero_truth_causal` / `raw_zero_truth_length` discharge the causality
and degree hypotheses at every bound; the general bound of section 3 is the one
that is `∀`-quantified over truth columns.

Neither `StrategyBounded` nor `64 <= L` nor either counter budget is left as a
hypothesis.  READ THE HONESTY HEADER AND "THE PRECISE REMAINING STEP": THIS IS NOT
THE SYSTEM'S SOUNDNESS ERROR. -/
theorem raw_engine_all_own_bound_at_thirteen (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage) (u0 u1 : Verifier.UsedClaims)
    (W : Nat) (b1 : Element) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (s0 : GateTerminalBinding.ProverState)
    (tables : GateSuffixPolynomial.Tables) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
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
        (rawEngineAllOwnIndexBadEvent gdec hash khash P c₀ L (Nat.le_trans (by omega) hLq) c s
          (challengeTruncatedMessage m) (RawIndexLanes.blockClaims u0 u1) 13
          (RawIndexLanes.truncated_raw_extended_bounded L c s m
            (RawIndexLanes.blockClaims u0 u1) W hpre hmlog hmgate
            (RawIndexLanes.block_claims_bounded u0 u1 W h0 h1) hLq hLW hdom)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
          (constantLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth b1)
          (engineGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth
            (engineEndpoint c gates publicHash s0))
          (2 ^ 13) (engineGate c gates publicHash tables) coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 2 * ChallengeUnionBound.tauTerm 8 + 4560 / (Fintype.card Block : ℚ) := by
  have h := raw_engine_all_own_bad_draw_probability_le gdec hash khash P c₀ L
    (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
    (challenge_truncated_round_causal m) (RawIndexLanes.blockClaims u0 u1) 13
    (RawIndexLanes.block_claims_causal u0 u1 13)
    (RawIndexLanes.truncated_raw_extended_bounded L c s m (RawIndexLanes.blockClaims u0 u1) W
      hpre hmlog hmgate (RawIndexLanes.block_claims_bounded u0 u1 W h0 h1) hLq hLW hdom)
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
    hc13 (by omega)
    (constantLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth b1)
    (engineGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth
      (engineEndpoint c gates publicHash s0))
    (constant_log_lane_of_strategy_causal (challengeTruncatedMessage m)
      (challenge_truncated_round_causal m) rawZeroTruth raw_zero_truth_causal b1)
    (engine_gate_lane_of_strategy_causal (challengeTruncatedMessage m)
      (challenge_truncated_round_causal m) rawZeroTruth raw_zero_truth_causal
      (engineEndpoint c gates publicHash s0))
    8 123 (engineGate c gates publicHash tables) coeffsOf cellIndex cols
    thirteen_counter_budget
    (by rw [hcidx]; exact ReducedIndexLanes.eight_index_counter_budget)
    (constant_log_lane_of_strategy_bounded (challengeTruncatedMessage m) rawZeroTruth b1 5
      (fun r ch => by
        rw [(challenge_truncated_message_lengths m r ch).1]
        exact hmlog)
      (raw_zero_truth_length 5))
    (engine_gate_lane_of_strategy_bounded (challengeTruncatedMessage m) rawZeroTruth
      (engineEndpoint c gates publicHash s0) (8 + 2)
      (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
      (raw_zero_truth_length (8 + 2))) hclen
  rw [hcidx] at h
  have harith : ((ReducedIndexLanes.indexStage 13 : Nat) : ℚ)
      * (((ReducedIndexLanes.indexStage 13 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [ReducedIndexLanes.index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

/-- (5) **AND THAT CLOSED CONSTANT IS STRICTLY BELOW `1`**, inherited verbatim from
the adopted `RawIndexLanes.raw_index_engine_bound_at_thirteen_lt_one`: the OUTER
diagonal, like the tau diagonal before it, costs nothing.  READ HONESTY (iv), (vi):
THIS IS NOT THE PROTOCOL'S SOUNDNESS ERROR. -/
theorem raw_engine_all_own_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) < 1 :=
  RawIndexLanes.raw_index_engine_bound_at_thirteen_lt_one

/-- (5) **THE HYPOTHESES OF THE CLOSED INSTANCE ARE SATISFIABLE**, so it is not
vacuous: the counter budgets hold at thirteen coupled rounds and eight index bits,
and the coefficient-length budget is met by the empty coefficient family -- the
same witness the adopted `ChallengeUnionBound` closed instances use.  The name
carries the `outer_` prefix because the adopted `EngineTauDiagonal` -- which this
module `open`s -- already has a `closed_instance_hypotheses_satisfiable` of its
own, and the two would be ambiguous wherever both namespaces are opened. -/
theorem outer_closed_instance_hypotheses_satisfiable :
    (12 + 6 * 13 < Transcript.u64Limit) ∧ (6 * 8 ≤ Transcript.u64Limit) ∧
      (∀ i, i < 2 ^ 13 → ((fun _ => ([] : List Element)) i).length ≤ 123) :=
  ⟨thirteen_counter_budget, ReducedIndexLanes.eight_index_counter_budget,
    fun _ _ => Nat.zero_le _⟩

open Classical in
/-- (5) **TESTED AT THE CONSTANT FAMILY.**  At a constant alpha-indexed family and a
constant alpha-to-table map the whole of sections 2 and 3 collapses, set for set,
to the adopted `RawBlockLanes` / `EngineTauDiagonal` statement, so nothing above is
a strengthening that only a moving target could satisfy. -/
theorem engine_outer_bound_at_constant_family (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane) (d q constraints : Nat)
    (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullBadEvent L hL e0 strat hb logLane gateLane d (2 ^ d) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  rw [raw_engine_full_bad_event_constant_slice,
    raw_engine_all_own_bad_event_constant_slice L hL e0 strat hb logLane gateLane d (2 ^ d)
      (fun _ => g) coeffsOf]
  exact raw_engine_all_own_block_bad_draw_probability_le L hL e0 strat hb d q constraints
    (fun _ => logLane) (fun _ => gateLane) (fun _ => hlcau) (fun _ => hgcau)
    (fun _ => hlog) (fun _ => hgate) (fun _ => g) coeffsOf hdu hclen

end Audit.Wire3.EngineOuterDiagonal
