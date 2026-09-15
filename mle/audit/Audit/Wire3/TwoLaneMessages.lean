import Audit.Wire3.GrindLanePairing

/-!
# TWO COUPLED MESSAGES AT ONE ROUND: THE SPLIT LANES

## The restriction this module removes

The adopted `Audit.Wire3.GrindLanePairing` (GLP) records, as its HONESTY (v), the
LARGEST restriction on its own headline:

  `both_paired_lanes_carry_the_same_message :`
    `(grinderLane e0 q g tr1 cl1 tcl1).message = (grinderLane e0 q g tr2 cl2 tcl2).message := rfl`

The grinder emits ONE payload at stage `22 + 5 * r`, and `grinderMessage` is the
only message `grinderLane` installs, so in GLP's section-5 headline the LOG lane
and the GATE lane carry IDENTICAL round messages -- while in the protocol they are
two DISTINCT coupled prover messages.  This module removes that restriction.

## THE FINDING THIS MODULE CARRIES -- ABOUT THE ADOPTED GRINDING MODEL, NOT ABOUT
## THIS CANDIDATE

READ THIS BEFORE THE CONSTRUCTION.  GLP's WHOLE LINE RUNS AT ONE PAYLOAD PER ROUND
WHERE THE PROTOCOL HAS TWO COUPLED CELLS ABSORBED ONE STAGE APART.  Section 1
proves both halves of that off the adopted definitions.  The log cell is the
chain's stage-`22 + (5 r + 2)` absorb and the gate cell is its stage-`22 + (5 r + 3)`
absorb (`chain_log_cell_at_stage_two`, `chain_gate_cell_at_stage_three`), while
`GrindingQueryBound.GrindingStrategy` has exactly ONE `absorb` per stage
(`run_stage_absorb_carries_one_payload`) and `GrindingUnionBound.GrindCausal`
forbids a round-`r` lane from reaching either cell stage -- its CHALLENGE half
does so immediately, since the reconstruction's `digestLookup … ch (stage r)` reads
`ch` at `stage r` while the cut pins `ch` only at `j ≤ 22 + 5 r`.

SO THE GRINDING LINE IS AT A STRICTLY COARSER GRANULARITY THAN THE PROTOCOL, AND
NO SPLITTING OF THE SINGLE PAYLOAD REPAIRS THAT.  A split can only MODEL the two
coupled cells; a function of the round-`r` payload is a function of ONE absorb,
whatever the function, so no choice of split recovers the second one.  What would
repair it is a lemma
that does not exist in the adopted tree: a version of
`GrindingUnionBound.grinding_union_bad_draw_probability_le_combined` whose lane
causality cuts at `roundStage r * (q + 1)` answer positions instead of
`(22 + 5 r + 1) * (q + 1)`.  `GrindingUnionBound`'s own comment
(GrindingUnionBound.lean:1184-1192) records that its diagonal step would survive
such a cut, since `grind_run_view_reassign_lower` only needs `22 + 5 r < j`; NO
ADOPTED LEMMA STATES THE HEADLINE AT THAT CUT, and none is proved here.  This is a
finding about the ADOPTED grinding model, not a defect opened by this candidate,
and it is the most that section 2 below is entitled to claim.

## 1. WHERE THE SECOND PAYLOAD LIVES (section 1 below)

The question was settled by reading the adopted chain, NOT by guessing, and the
answer has two halves that pull in opposite directions.

(a) ON THE TRANSCRIPT CHAIN THE TWO CELLS ARE ABSORBED AT TWO DISTINCT STAGES.
The adopted `BirthdayClashBound.roundShapeAt` gives round `i` five frames, and
frame `2` carries `OuterAdapter.encodedVec m.1` (the LOG cell) while frame `3`
carries `OuterAdapter.encodedVec m.2` (the GATE cell); `roundShape ms k` is frame
`k % 5` of round `k / 5`, and `prefixRoundShape c s ms k` is the relation prefix
below `22` and `roundShape ms (k - 22)` above it.  So the LOG cell is the stage
`22 + (5 r + 2)` absorb of the chain and the GATE cell is the stage `22 + (5 r + 3)`
absorb.  `chain_log_cell_at_stage_two` and `chain_gate_cell_at_stage_three` state
exactly that, off the adopted definitions.

(b) BUT AT THE LANE LAYER BOTH ARE PROJECTIONS OF ONE ROUND-`r` OBJECT.
`Verifier.CoupledMessage` is `List Ext3 × List Ext3`: one object with two
components.  The adopted `StrategyChainBound.strategicShape` evaluates ONE
`S r ch : Verifier.CoupledMessage` per round and selects frame `(k - 22) % 5` out
of it (`strategic_shape_log_cell`, `strategic_shape_gate_cell`), and the adopted
`RawBlockLanes.rawLogLaneOfStrategy` / `rawGateLaneOfStrategy` recover the pair as
`(S r ch).1.map OuterRound.lift` and `(S r ch).2.map OuterRound.lift`
(`adopted_raw_lanes_project_one_round_object`) -- a PROJECTION of one object, not a
second absorb.  The adopted `BirthdayClashBound.roundMessages` is
`p.logRounds.zip p.gateRounds`, and `roundMessage p r` is one entry of that zip,
read by `.1` and `.2`.

(c) AND THE ADOPTED CAUSALITY CUT FORBIDS A ROUND-`r` LANE FROM READING EITHER
CELL STAGE.  `GrindingUnionBound.GrindCausal` lets round `r`'s message read the
run's answers only at the `(22 + 5 r + 1) (q + 1)` positions of stages `<= 22 + 5 r`
and the challenge view only at stages `<= 22 + 5 r`.  Both cell stages,
`22 + 5 r + 2` and `22 + 5 r + 3`, are ABOVE that cut, and so is the history the
run hands their absorbs.  Section 2 proves this is not a cosmetic obstruction:
`grinder_message_at_stage_causal` shows the GLP reconstruction is `GrindCausal`
whenever the stage it reads is at most `22 + 5 r`, and
`later_stage_reconstruction_is_not_grind_causal` exhibits a legal
`GrindingBounded`, `ChallengeRestricted` grinder at which the SAME reconstruction
at stage `22 + 5 r + 2` is NOT `GrindCausal` -- so that reconstruction cannot be
handed to the adopted headline AS A CONSTRUCTION OVER ALL GRINDERS.  IT IS NOT
THAT A LATER STAGE IS NEVER CAUSAL: `D1_blind_grinder_later_stage_is_grind_causal`
exhibits an equally legal grinder at which the SAME reconstruction IS `GrindCausal`
at EVERY stage function, however far above the cut it reads.

SO THE CONSTRUCTION IS A SPLITTING, NOT A SECOND ABSORB.  Within the adopted
headline's hypotheses a round-`r` lane may read exactly one payload, the
stage-`22 + 5 r` absorb, and the two coupled messages must be recovered from it the
way the adopted raw lanes recover theirs from `S r ch`: by projection.  That is
what section 3 builds.

## 2. WHAT IS PROVED

1. THE SPLIT (section 3).  `logHalf bs = bs.take 120` and `gateHalf bs = bs.drop 120`
   cut the absorbed payload at the adopted log-lane degree bound -- five encoded
   field elements, `24 * 5` bytes.  `halves_recover_payload` is
   `logHalf bs ++ gateHalf bs = bs`, so nothing of the payload is dropped and
   nothing is invented.  `grinderLogMessage` and `grinderGateMessage` decode the
   two halves through GLP's OWN `decodeElements`; no new decoder is written.
2. THE TWO PAIRINGS (section 3).  `grinder_log_lane_message_is_absorbed_payload`
   and `grinder_gate_lane_message_is_absorbed_payload` are the analogues of GLP's
   `grinder_lane_message_is_absorbed_payload`, one per lane: at EVERY table, each
   lane's round-`r` message IS its half of the payload `g`'s stage-`22 + 5 r`
   absorb emits, at the very history, probe answers and challenge answers the run
   hands it.  `grinder_split_messages_concatenate_at_the_run` puts them back
   together into that payload.
3. THEY ARE GENUINELY DIFFERENT (section 4).
   `split_lanes_can_carry_different_messages` exhibits a grinder and a round at
   which the two lanes' messages DIFFER, and
   `split_selector_lanes_differ_at_every_view` strengthens it: for that grinder
   they differ at EVERY run view and EVERY challenge view, hence in particular at
   every table of a real run (`split_lanes_differ_at_the_run`).  This is the
   theorem that retires GLP HONESTY (v); it is a real inequality at a witness --
   a five-element log message against a one-element gate message.
   AND THE THRESHOLD AT WHICH THEY SEPARATE, EXACTLY (section 3).
   `A3_both_halves_nonempty_iff`: both halves are non-empty EXACTLY above
   `24 * 5` bytes.  At or below that the gate lane is SILENT, which is the whole of
   GLP's covered class (`B3_glp_selector_grinder_gate_message_is_empty`,
   `B4_split_and_glp_gate_lanes_differ_at_selector_grinder`).  Read item 3 with
   HONESTY (iv): the lanes differ there by silencing one of them.
4. THE RESTATED HEADLINE (section 5).
   `grinder_split_union_bad_draw_probability_le_combined` is GLP's headline with
   the single paired lane replaced by the two SPLIT lanes.  The constant is GLP's,
   term for term, and the coupled-stage-only payload hypothesis `hp` is GLP's,
   quantified over `22 + 5 * r` only.
   THE NEW BYTE BUDGET, EXACTLY.  The LOG lane needs NO payload hypothesis at all
   (`grinder_log_lane_bounded`): its half is at most `24 * 5` bytes by
   construction, so it always decodes to at most five elements -- GLP's `hfitlog`
   is DISCHARGED here, not assumed.  The GATE lane pays the only budget:
   `gate_budget_iff` says `hfitgate` is EXACTLY
   `p <= 24 * 5 + 24 * (quo + 2)` bytes, and `gate_budget_at_adopted_quotient` says
   that at the adopted `quo = 8` it is EXACTLY `p <= 360` bytes, i.e. fifteen
   encoded field elements per absorb -- five on the log lane and ten on the gate
   lane.  THE SPLIT DOES NOT HALVE THE BUDGET: it RAISES it, from GLP's 120 bytes
   to 360, because the two halves are disjoint and each lane pays only for its own.
   `three_hundred_and_sixty_bytes_fit` and `sixteen_elements_do_not_fit` put the
   boundary exactly one element out.
5. THE WITNESSES (section 6).  `splitSelectorGrinder` probes at its own digest and
   absorbs `unitRepeat 5 ++ bytesOfElement 1` when and only when its first probe
   came back the constant table's block, and `unitRepeat 5 ++ bytesOfElement 0`
   otherwise: a 144-byte payload whose log half is five elements and whose gate
   half is one, at every branch.  It is `GrindingBounded`, `ChallengeRestricted`,
   provably reads its probe answers (`split_selector_grinder_reads_probes`) and
   provably is NOT the lift of any adopted `StrategyChainBound.Strategy`.
   `split_selector_gate_target_zero_nonempty` and `E3_log_target_zero_nonempty`
   inhabit BOTH lanes' round-`0` targets, and
   `split_selector_split_bound_at_thirteen` /
   `F1_split_bound_at_thirteen_with_inhabited_log_target` close the instance at
   thirteen rounds with EVERY hypothesis discharged.  It is ALREADY outside GLP's
   budget at every `p` (`C3_split_selector_is_outside_glp_budget`), which is the
   sharpest evidence that the widening is real.
   AND THE WITNESS AT THE CEILING (section 6c).  `bigGrinder` absorbs `24 * 15 = 360`
   bytes, the exact budget of section 4, and is the ONLY payload size at which BOTH
   split lanes carry adopted shape-legal lengths -- five and ten
   (`C8_big_grinder_halves`).  `C11_big_grinder_split_bound_at_thirteen` closes the
   headline there, and `C10_big_grinder_is_outside_glp_budget` shows GLP cannot
   reach it at any `p`.
6. THE SCOPE (section 7).  `short_payload_gives_empty_gate_message` is the price of
   the fixed boundary: a grinder whose payload is at most `24 * 5` bytes -- GLP's
   own `selectorGrinder`, provably
   (`B3_glp_selector_grinder_gate_message_is_empty`) -- has an EMPTY gate-lane
   message under this split, which is not a legal round message
   (`B1_accepted_gate_rounds_never_empty_nor_singleton`).
   `split_boundary_is_not_read_off_the_payload` states the boundary as what it is: a
   convention of this module.  Section 7b states what the deployed chain does that
   the grinding chain does not -- it length-prefixes every cell
   (`G0_adopted_cell_encoding_is_prefixed`), which is why a shape-legal log cell is
   128 chain bytes and not 120.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Everything below is about the
uniform counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`, and
this module inherits GLP's and `GrindingUnionBound`'s honesty headers in full.
Replacing the deployed Keccak by a table drawn from that law is an assumption with
no proof anywhere in this tree.

(ii) `ChallengeRestricted` IS STILL ASSUMED AND STILL NOT DISCHARGED.  Nothing
below weakens it, and the pre-read attack -- `GrindingUnionBound.preReadGrinder`,
whose bad-draw mass is one on the pre-read event -- is still uncharged.  NOTHING
BELOW SHOWS THAT GRINDING BUYS A PROVER ANYTHING.  `splitSelectorGrinder` reads
probe `0` once and branches between two CONSTANT payloads; IT DOES NOT SEARCH, it
never re-probes and it never retries, exactly as GLP says of its own
`selectorGrinder` and `GrindingUnionBound` of its `probeGrinder`.  The prover that
WOULD search is excluded by `ChallengeRestricted`, not by any budget here.

(iii) WHAT THE SPLIT IS, AND WHAT IT IS NOT.  It is a projection of one absorbed
payload into two lane messages, in the shape in which the adopted
`RawBlockLanes.rawLogLaneOfStrategy` / `rawGateLaneOfStrategy` project one
`Verifier.CoupledMessage`.  IT IS NOT TWO ABSORBS.  The deployed chain does absorb
the two cells at two distinct stages (`chain_log_cell_at_stage_two`,
`chain_gate_cell_at_stage_three`), and THERE IS A LEGAL GRINDER AT WHICH A LANE
CARRYING THE LATER ABSORB IS NOT `GrindCausal`
(`later_stage_reconstruction_is_not_grind_causal`,
`D2_later_stage_obstruction_general`), so THE GLP-SHAPED RECONSTRUCTION AT THE
LATER STAGE cannot be fed to the adopted headline without first widening
`GrindingUnionBound.GrindCausal` and reproving that headline.  THAT IS NOT
ATTEMPTED HERE.  I did not find a two-absorb pairing that is `GrindCausal`, and no
adopted lemma gives one; a later stage is NOT always fatal, either -- at
`blindGrinder` the same reconstruction is causal at every stage
(`D1_blind_grinder_later_stage_is_grind_causal`).  The missing lemma is named
exactly in section 2: a version of
`GrindingUnionBound.grinding_union_bad_draw_probability_le_combined` whose lane
causality cuts at `roundStage r * (q + 1)` answer positions instead of
`(22 + 5 r + 1) * (q + 1)`.  `GrindingUnionBound`'s own comment records that its
diagonal step would survive such a cut, but no adopted lemma states the headline
at it and none is proved here.

(iv) THE BOUNDARY `24 * 5` IS THIS MODULE'S CONVENTION, AND THE TWO LANES SEPARATE
ONLY ABOVE IT.

THE TWO LANES SEPARATE ONLY ABOVE `24 * 5` BYTES.  `logHalf bs` and `gateHalf bs`
are both non-empty exactly when `120 < bs.length`
(`A3_both_halves_nonempty_iff`, off `A1_log_half_nonempty_iff` and
`A2_gate_half_nonempty_iff`); at or below that the GATE lane's message is EMPTY, so
on the WHOLE of GLP's covered class -- every grinder GLP's `hfitlog` admits, its own
`selectorGrinder` included (`B3_glp_selector_grinder_gate_message_is_empty`) --
this split makes the two lanes differ by SILENCING the gate lane, not by giving it
the protocol's second message.  An empty gate cell is not a legal round message:
the adopted `Verifier.shape` demands `c.quotientDegree + 2` entries per gate round
and five per log round (`B1_accepted_gate_rounds_never_empty_nor_singleton`,
`B2_accepted_log_rounds_have_length_five`, both off the adopted
`Verifier.acceptance_exact_round_shapes`), and these two lanes attain both lengths
together only at a payload of exactly `24 * 15 = 360` bytes
(`C8_big_grinder_halves`: log five, gate ten).  Neither this module nor GLP
enforces those lengths -- `GrindLaneBounded` is a `≤` -- so this is a coarseness
INHERITED from the adopted grinding model, not one opened here.  GLP's own single
lane is length `1` on both sides at its own witness, which is no more shape-legal
than what this split produces there; the point is not that this module manufactures
an illegality, but that NEITHER line enforces the protocol's round shapes.

WHERE THE BOUNDARY COMES FROM, AND WHAT DOES NOT TRANSPORT.  The GRINDING model's
payload carries no length prefix -- `GrindingStrategy.absorb` returns a bare byte
string and GLP's `decodeElements` reads it as a bare concatenation
(`G3_glp_layout_is_unprefixed`) -- so nothing in IT marks where the log cell ends.
The deployed chain DOES prefix each cell with `le 8` of its length
(`Transcript.ext3VecBytes`, Transcript.lean:83; `G0_adopted_cell_encoding_is_prefixed`),
which is why a shape-legal log cell is 128 chain bytes and not 120
(`G1_shape_legal_log_cell_is_128_chain_bytes`, and
`G2_shape_legal_gate_cell_is_248_chain_bytes` at the adopted `quotientDegree = 8`);
NO ADOPTED LEMMA TRANSPORTS THAT PREFIX ONTO THE GRINDING CHAIN'S SINGLE PAYLOAD.
The number `120` is nonetheless principled inside GLP's own decoder convention: it
is the twenty-four-byte limb width times the shape-legal log-round length.

`split_boundary_is_not_read_off_the_payload` and
`short_payload_gives_empty_gate_message` state the consequences.  The split itself
is conservative rather than unsound -- the two pairings of section 3 are equations
true by construction -- but the boundary is a modelling choice, and it is the
reason a prover whose log cell is shorter than five elements is modelled here with
its gate cell shifted.  No adopted lemma recovers the true boundary from the
grinding chain's single payload.

(v) GLP's DECODER HONESTY IS INHERITED WHOLE.  `decodeElements` agrees with the
adopted `Spongefish.decodeCanonicalExt3` only on exactly twenty-four bytes whose
limbs are already below the modulus; off that domain it INVENTS and is not
injective (GLP's `decoder_invents_on_rejected_payloads`).  Both halves below are
decoded through it, so both lane messages inherit that caveat.

(vi) ONLY `message` IS PAIRED.  A `GrindLane` has four fields.  `truth`, `claim`
and `truthClaim` remain free parameters on both lanes, exactly as they are in GLP
and in the adopted `RawBlockLanes`; they are the HONEST column and the initial
running claims, which are not the prover's data.

(vii) THE ROUND SCHEDULE IS GLP's AND IS NOT DERIVED.  Round `r` is identified with
chain stage `22 + 5 r`, the index `GrindCausal` and `roundStage` already use.  That
the deployed protocol absorbs round `r`'s coupled cells at `22 + 5 r + 2` and
`22 + 5 r + 3` is section 1's reading of the adopted shape; no run-level schedule is
threaded onto the grinding chain here.

(viii) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  No extractor, no
knowledge soundness, no adaptive Fiat--Shamir statement.  The index lanes, the WHIR
folding transcript and the Merkle openings are not covered here any more than they
are in GLP.

(ix) NO CARDINALITY IS EVALUATED.  `Fintype.card Block` appears only inside
statements transported verbatim from GLP; no cardinality of `Element`, `Block` or
`OuterChallenge.DigestTriple` is ever evaluated numerically or handed to a `ring`
or `omega` goal.  `Finset.univ` does not appear in any STATEMENT of this module.

(x) BOTH LANES' ROUND-`0` TARGETS ARE INHABITED, AND WHAT THAT STILL DOES NOT SAY.
`split_selector_gate_target_zero_nonempty` inhabits the round-`0` target of the
GATE lane, whose message at the constant table is `[1]` -- the adopted
`RawBlockLanes.separatedRawLane` message, so the adopted
`separated_raw_lane_agrees_at_zero` applies verbatim.  The LOG lane's round-`0`
message is FIVE elements (`E1_split_selector_log_message_zero`: it is `[1,1,1,1,1]`),
so that adopted agreement lemma does not apply to it; `E3_log_target_zero_nonempty`
inhabits its target instead, at the SAME grinder, the SAME table and the SAME
running claims, with the honest column `logFiveTruth`
(`E2a_log_five_truth_causal`, `E2b_log_five_truth_length`) in place of
`grindZeroTruth`, and `F1_split_bound_at_thirteen_with_inhabited_log_target` closes
the thirteen-round instance at that column.  So the log lane's target gap is NOT
forced by the split: it was an artefact of pairing a FIVE-element log message with
the EMPTY honest column `grindZeroTruth = fun _ _ _ => []`.  Whether the ORIGINAL
column's log target is empty is not settled here in either direction, and nothing
below claims it is.  As in GLP and `GrindingUnionBound`, a non-empty target is a
`Finset` of DIGEST TRIPLES and does not by itself give a non-empty event of TABLES.
-/

namespace Audit.Wire3.TwoLaneMessages

open Audit.Wire3
open Audit.Wire3.GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.ReducedFullTransport
open Audit.Wire3.RawBlockLanes
open Audit.Wire3.GrindingQueryBound
open Audit.Wire3.GrindingUnionBound
open Audit.Wire3.GrindLanePairing

/-! ## 1. WHERE THE SECOND PAYLOAD LIVES

Four readings of the adopted sources, stated as theorems rather than as prose.
Together they say: the two coupled cells of round `r` are absorbed at two DISTINCT
chain stages, but both are components of ONE round-`r` object, and the adopted lane
layer recovers them by PROJECTION out of that object. -/

/-- (1) **THE LOG CELL IS THE CHAIN'S STAGE-`22 + (5 r + 2)` ABSORB.**  Frame `2` of
the adopted `BirthdayClashBound.roundShapeAt` carries `encodedVec m.1`, and
`prefixRoundShape` puts round `r`'s frames at `22 + 5 r + j`. -/
theorem chain_log_cell_at_stage_two (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (r : Nat) :
    (prefixRoundShape c s ms (22 + (5 * r + 2))).2
      = OuterAdapter.encodedVec ((ms.get? r).getD ([], [])).1 := by
  rw [prefix_round_shape_round, round_shape_payload_two]

/-- (1) **AND THE GATE CELL IS THE CHAIN'S STAGE-`22 + (5 r + 3)` ABSORB.**  So on
the transcript chain the two coupled messages are two DIFFERENT absorbs, one stage
apart. -/
theorem chain_gate_cell_at_stage_three (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (r : Nat) :
    (prefixRoundShape c s ms (22 + (5 * r + 3))).2
      = OuterAdapter.encodedVec ((ms.get? r).getD ([], [])).2 := by
  rw [prefix_round_shape_round, round_shape_payload_three]

/-- (1) **BUT BOTH CELLS COME OUT OF ONE ROUND-`r` OBJECT.**  The adopted
`StrategyChainBound.strategicShape` evaluates `S r ch` ONCE per round and selects a
frame out of it; the log cell is frame `2` of that one object. -/
theorem strategic_shape_log_cell (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (r : Nat)
    (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block) :
    strategicShape c s S (22 + (5 * r + 2)) h ch = roundShapeMsg (S r ch) r 2 := by
  rw [strategic_shape_apply, if_neg (by omega),
    show (22 + (5 * r + 2) - 22) / 5 = r from by omega,
    show (22 + (5 * r + 2) - 22) % 5 = 2 from by omega]

/-- (1) **AND THE GATE CELL IS FRAME `3` OF THE SAME OBJECT.** -/
theorem strategic_shape_gate_cell (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (r : Nat)
    (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block) :
    strategicShape c s S (22 + (5 * r + 3)) h ch = roundShapeMsg (S r ch) r 3 := by
  rw [strategic_shape_apply, if_neg (by omega),
    show (22 + (5 * r + 3) - 22) / 5 = r from by omega,
    show (22 + (5 * r + 3) - 22) % 5 = 3 from by omega]

/-- (1) **SO THE ADOPTED LANE LAYER RECOVERS THE PAIR BY PROJECTION.**  The adopted
`RawBlockLanes.rawLogLaneOfStrategy` and `rawGateLaneOfStrategy` read the SAME
`S r ch` and take its two components.  This is the shape the split of section 3
copies: one object per round, two lane messages out of it. -/
theorem adopted_raw_lanes_project_one_round_object
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr1 tr2 : Nat → (Nat → Nat → Block) → List Element) (a1 b1 a2 b2 : Element)
    (r : Nat) (ch : Nat → Nat → Block) :
    ((rawLogLaneOfStrategy S tr1 a1 b1).message r ch,
        (rawGateLaneOfStrategy S tr2 a2 b2).message r ch)
      = ((S r ch).1.map OuterRound.lift, (S r ch).2.map OuterRound.lift) := rfl

/-- (1) **AND THE RUN'S COUPLED MESSAGES ARE ONE ZIP.**  The adopted
`BirthdayClashBound.roundMessages` pairs the proof's log rounds with its gate
rounds; round `r`'s two cells are the two components of one entry. -/
theorem round_message_is_one_entry_of_the_zip (p : Verifier.Proof) (r : Nat) :
    roundMessage p r = (((p.logRounds.zip p.gateRounds).get? r).getD ([], [])) := rfl

/-- (1) **WHILE THE GRINDING MODEL GIVES ONE PAYLOAD PER STAGE.**  The run's
stage-`k` query is the absorb, and it carries the one payload
`(g.absorb k …).2` -- the adopted `GrindingQueryBound.grind_query_absorb`, read for
its payload component. -/
theorem run_stage_absorb_carries_one_payload (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (a : Nat → Block) (ch : Transcript.Digest → Nat → Block)
    (k : Nat) :
    (grindQuery e0 q g a ch (slotPos q k q)).2.2
      = (g.absorb k (stateOf e0 q a) ch (probeAnsOf q a)).2 := by
  rw [grind_query_absorb]

/-- (1) **AND AN EMPTY GATE CELL IS NOT A LEGAL ROUND MESSAGE.**  Off the ADOPTED
`Verifier.acceptance_exact_round_shapes` (Verifier.lean:492-499, stated over
`Verifier.verify … = .ok ()`): every gate round of an ACCEPTED proof has length
`c.quotientDegree + 2`, hence is neither empty nor a singleton.  So the gate shapes
the split of section 3 produces at a short payload (EMPTY,
`short_payload_gives_empty_gate_message`) and at `splitSelectorGrinder` (ONE
element, `split_selector_gate_message_length`) are not legal `gateRounds` entries.

FAIRNESS: neither is GLP's own single lane, which is length one on BOTH sides at
its own `selectorGrinder`.  NEITHER LINE ENFORCES THESE LENGTHS -- `GrindLaneBounded`
is a `≤`, in GLP exactly as here -- so the illegality is INHERITED from the adopted
grinding model rather than opened here.

VACUITY: the hypothesis is satisfiable at a non-degenerate instance in the adopted
tree -- `NonDegenerateAcceptance.model_acceptance_at_nondegenerate_config`
(NonDegenerateAcceptance.lean:653-654) is
`Verifier.verify wideEngine widePin 1 wideConfig wideProof = .ok ()`, by `rfl`, at a
seven-wire configuration.  That module is not imported here; nothing below needs
it. -/
theorem B1_accepted_gate_rounds_never_empty_nor_singleton
    (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (h : Verifier.verify e pin chain c p = .ok ())
    (m : List Verifier.Ext3) (hm : m ∈ p.gateRounds) :
    m.length = c.quotientDegree + 2 ∧ m ≠ [] ∧ m.length ≠ 1 := by
  have hs := (Verifier.acceptance_exact_round_shapes e pin chain c p h).2.2.2
  rw [List.all_eq_true] at hs
  have hlen : m.length = c.quotientDegree + 2 := by
    have := hs m hm
    rwa [decide_eq_true_eq] at this
  refine ⟨hlen, ?_, by omega⟩
  intro hnil
  rw [hnil, List.length_nil] at hlen
  omega

/-- (1) **AND EVERY LOG ROUND OF AN ACCEPTED PROOF HAS LENGTH EXACTLY FIVE** -- which
is where this module's `24 * 5` boundary comes from, and which the split's log lane
attains only when the absorbed payload is at least `120` bytes long
(`A1_log_half_nonempty_iff`, `C8_big_grinder_halves`).  Same vacuity witness as
`B1_accepted_gate_rounds_never_empty_nor_singleton`. -/
theorem B2_accepted_log_rounds_have_length_five
    (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (h : Verifier.verify e pin chain c p = .ok ())
    (m : List Verifier.Ext3) (hm : m ∈ p.logRounds) : m.length = 5 := by
  have hs := (Verifier.acceptance_exact_round_shapes e pin chain c p h).2.2.1
  rw [List.all_eq_true] at hs
  have := hs m hm
  rwa [decide_eq_true_eq] at this

/-! ## 2. WHY THE PAIR CANNOT BE TWO ABSORBS AT THIS LEVEL

The GLP reconstruction, with the stage index made a parameter.  It is `GrindCausal`
WHENEVER the stage it reads stays at or below `22 + 5 r`; at the LOG cell's own
stage `22 + 5 r + 2` there is a LEGAL GRINDER at which it is not, so AS A
CONSTRUCTION OVER ALL GRINDERS it cannot be handed to the adopted headline.  IT IS
CAUSAL AT SOME GRINDERS -- `D1_blind_grinder_later_stage_is_grind_causal` exhibits
one at EVERY stage function, however far above the cut -- and no adopted lemma rules
that out, nor is any such claim made here.

THE ARITHMETIC, ISOLATED, so that a reader can see WHICH HALF of `GrindCausal` a
widening lemma would have to widen.  The HISTORY the reconstruction reads at stage
`s` is `grinderHist e0 q s a`, which depends on the run's answers only below
`s * (q + 1)`: at `s = 22 + 5 r + 1` the last position it touches is
`slotPos q (22 + 5 r) q`, which at `r = 0` is `slotPos q 22 q = 23 q + 22`, strictly
below `23 (q + 1)` -- INSIDE the cut.  So the history half alone does NOT force
`stage r ≤ 22 + 5 r`.  What forces it is the CHALLENGE half,
`digestLookup (grinderHist …) ch (stage r)`, which reads `ch` AT `stage r` while
`GrindCausal` pins `ch` only at `j ≤ 22 + 5 r`; and, once `0 < q`, the PROBE half as
well, since `grinderProbes e0 q s a` truncates at `slotPos q s q = s (q + 1) + q`,
already above `(22 + 5 r + 1) (q + 1)` at `s = 22 + 5 r + 1`. -/

/-- **THE GLP RECONSTRUCTION AT A PARAMETRIC STAGE.**  At `stage r = 22 + 5 * r`
this IS the adopted `GrindLanePairing.grinderMessage`
(`adopted_message_is_at_the_coupled_stage`). -/
def grinderMessageAtStage (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (stage : Nat → Nat) : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element :=
  fun r a ch =>
    decodeElements
      (g.absorb (stage r) (grinderHist e0 q (stage r) a)
        (digestLookup (grinderHist e0 q (stage r) a) ch (stage r))
        (grinderProbes e0 q (stage r) a)).2

theorem adopted_message_is_at_the_coupled_stage (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) :
    grinderMessageAtStage e0 q g (fun r => 22 + 5 * r) = grinderMessage e0 q g := rfl

/-- (2) **THE RECONSTRUCTION IS CAUSAL WHENEVER IT STAYS AT OR BELOW THE ROUND'S
OWN STAGE.**  This is GLP's `grinder_message_causal` with the stage index freed; the
hypothesis `stage r ≤ 22 + 5 * r` is what the proof uses and all it uses.  THE
IMPLICATION IS ONE-DIRECTIONAL: it does not say that a higher stage is never
causal, and `D1_blind_grinder_later_stage_is_grind_causal` shows that at some legal
grinders it is. -/
theorem grinder_message_at_stage_causal (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (stage : Nat → Nat) (hstage : ∀ r, stage r ≤ 22 + 5 * r) :
    GrindCausal q (grinderMessageAtStage e0 q g stage) := by
  intro r a1 a2 ch1 ch2 ha hch
  have hcut : ∀ m, m < (stage r + 1) * (q + 1) → a1 m = a2 m := by
    intro m hm
    refine ha m (lt_of_lt_of_le hm ?_)
    exact Nat.mul_le_mul_right (q + 1) (by have := hstage r; omega)
  have hh : grinderHist e0 q (stage r) a1 = grinderHist e0 q (stage r) a2 :=
    grinder_hist_congr e0 q (stage r) a1 a2 hcut
  have hp : grinderProbes e0 q (stage r) a1 = grinderProbes e0 q (stage r) a2 :=
    grinder_probes_congr e0 q (stage r) a1 a2 hcut
  have hl : digestLookup (grinderHist e0 q (stage r) a1) ch1 (stage r)
      = digestLookup (grinderHist e0 q (stage r) a1) ch2 (stage r) :=
    digest_lookup_congr _ ch1 ch2 (stage r)
      (fun j hj => hch j (le_trans hj (hstage r)))
  show decodeElements (g.absorb (stage r) (grinderHist e0 q (stage r) a1)
      (digestLookup (grinderHist e0 q (stage r) a1) ch1 (stage r))
      (grinderProbes e0 q (stage r) a1)).2
    = decodeElements (g.absorb (stage r) (grinderHist e0 q (stage r) a2)
      (digestLookup (grinderHist e0 q (stage r) a2) ch2 (stage r))
      (grinderProbes e0 q (stage r) a2)).2
  rw [hl, hh, hp]

/-- **A GRINDER WHOSE ABSORB READS ITS OWN STAGE DIGEST.**  It emits the
twenty-four bytes of `1` when and only when the digest it is handed at its own
stage is the digest it was handed at stage `0`, and the bytes of `0` otherwise.
It never consults the challenge oracle, so it is `ChallengeRestricted`, and its
payload is always twenty-four bytes, so it is `GrindingBounded`.  It exists only to
witness the obstruction below. -/
def historyGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun k h _ _ =>
    (0, if (h k).bytes = (h 0).bytes then bytesOfElement 1 else bytesOfElement 0)

theorem history_grinder_payload_length (k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    (historyGrinder.absorb k h ch pa).2.length ≤ 24 := by
  show (if (h k).bytes = (h 0).bytes then bytesOfElement 1
      else bytesOfElement 0).length ≤ 24
  by_cases hc : (h k).bytes = (h 0).bytes
  · rw [if_pos hc, bytes_of_element_length]
  · rw [if_neg hc, bytes_of_element_length]

theorem history_grinder_bounded (L : Nat) (hL : 93 ≤ L) : GrindingBounded L historyGrinder := by
  refine ⟨fun _ i _ _ _ => ?_, fun k h ch pa => ?_⟩
  · show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · exact le_trans (Nat.add_le_add_left (history_grinder_payload_length k h ch pa) 61) (by omega)

theorem history_grinder_challenge_restricted : ChallengeRestricted historyGrinder :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- (2) **THE OBSTRUCTION, EXHIBITED -- AND NOT AT ONE OFFSET ONLY.**  At
`historyGrinder` the GLP reconstruction read at ANY stage function whose round-`0`
stage is at least `24` is NOT `GrindCausal`: two run views that agree at every
answer position the adopted causality cut allows give it DIFFERENT round-`0`
messages, at one and the same challenge view.  The LOG cell's own stage
`22 + 5 r + 2` and the GATE cell's own stage `22 + 5 r + 3` are both of that form,
so the obstruction is not an artefact of the one offset the module started from.

The reason is structural rather than incidental: the history the run hands a
stage-`t + 1` absorb with `23 ≤ t` contains the digest of the answer at position
`slotPos q t q`, which is at or above the round-`0` cut `(22 + 5 * 0 + 1) * (q + 1)`.

WHAT THIS DOES NOT SAY.  It does NOT say that reading a later stage breaks
causality in general.  It says that THERE IS A LEGAL GRINDER at which it does, which
is exactly what rules the later-stage reconstruction out as a UNIFORM construction
over all grinders -- the only form the adopted headline can consume.  At other legal
grinders the same reconstruction IS causal at every stage:
`D1_blind_grinder_later_stage_is_grind_causal`. -/
theorem D2_later_stage_obstruction_general (q t : Nat) (ht : 23 ≤ t)
    (stage : Nat → Nat) (hs : stage 0 = t + 1) :
    ¬ GrindCausal q (grinderMessageAtStage OuterInitial.zeroDigest q historyGrinder stage) := by
  intro hc
  have hcut := hc 0 (fun _ => unitTarget)
    (fun m => if m < (22 + 5 * 0 + 1) * (q + 1) then unitTarget else oneDigestBlock)
    (fun _ _ => unitTarget) (fun _ _ => unitTarget)
    (fun _ hm => (if_pos hm).symm) (fun _ _ => rfl)
  have hmul : 23 * (q + 1) ≤ t * (q + 1) := Nat.mul_le_mul_right (q + 1) ht
  have hpos : ¬ (slotPos q t q < (22 + 5 * 0 + 1) * (q + 1)) := by
    rw [slotPos]; omega
  have hone : grinderMessageAtStage OuterInitial.zeroDigest q historyGrinder stage 0
      (fun _ => unitTarget) (fun _ _ => unitTarget) = [1] := by
    show decodeElements (if (grinderHist OuterInitial.zeroDigest q (stage 0)
          (fun _ => unitTarget) (stage 0)).bytes
        = (grinderHist OuterInitial.zeroDigest q (stage 0) (fun _ => unitTarget) 0).bytes
        then bytesOfElement 1 else bytesOfElement 0) = [1]
    rw [hs]
    have hh1 : grinderHist OuterInitial.zeroDigest q (t + 1) (fun _ : Nat => unitTarget) (t + 1)
        = blockDigest unitTarget := by
      show (if t + 1 ≤ t + 1 then
          stateOf OuterInitial.zeroDigest q (fun _ : Nat => unitTarget) (t + 1)
        else OuterInitial.zeroDigest) = blockDigest unitTarget
      rw [if_pos (Nat.le_refl _)]
      rfl
    have hh0 : grinderHist OuterInitial.zeroDigest q (t + 1) (fun _ : Nat => unitTarget) 0
        = OuterInitial.zeroDigest := by
      show (if 0 ≤ t + 1 then
          stateOf OuterInitial.zeroDigest q (fun _ : Nat => unitTarget) 0
        else OuterInitial.zeroDigest) = OuterInitial.zeroDigest
      rw [if_pos (Nat.zero_le _)]
      rfl
    rw [hh1, hh0, if_pos (show (blockDigest unitTarget).bytes
      = OuterInitial.zeroDigest.bytes from rfl), decode_elements_of_element]
  have hzero : grinderMessageAtStage OuterInitial.zeroDigest q historyGrinder stage 0
      (fun m => if m < (22 + 5 * 0 + 1) * (q + 1) then unitTarget else oneDigestBlock)
      (fun _ _ => unitTarget) = [0] := by
    show decodeElements (if (grinderHist OuterInitial.zeroDigest q (stage 0)
          (fun m => if m < (22 + 5 * 0 + 1) * (q + 1) then unitTarget else oneDigestBlock)
          (stage 0)).bytes
        = (grinderHist OuterInitial.zeroDigest q (stage 0)
          (fun m => if m < (22 + 5 * 0 + 1) * (q + 1) then unitTarget else oneDigestBlock)
          0).bytes
        then bytesOfElement 1 else bytesOfElement 0) = [0]
    rw [hs]
    have hh1 : (grinderHist OuterInitial.zeroDigest q (t + 1)
        (fun m => if m < (22 + 5 * 0 + 1) * (q + 1) then unitTarget else oneDigestBlock)
        (t + 1)).bytes = oneDigestBlock.val := by
      show (if t + 1 ≤ t + 1 then
          stateOf OuterInitial.zeroDigest q
            (fun m => if m < (22 + 5 * 0 + 1) * (q + 1) then unitTarget else oneDigestBlock)
            (t + 1)
        else OuterInitial.zeroDigest).bytes = oneDigestBlock.val
      rw [if_pos (Nat.le_refl _)]
      show (blockDigest (if slotPos q t q < (22 + 5 * 0 + 1) * (q + 1)
          then unitTarget else oneDigestBlock)).bytes = oneDigestBlock.val
      rw [if_neg hpos]
      rfl
    have hh0 : (grinderHist OuterInitial.zeroDigest q (t + 1)
        (fun m => if m < (22 + 5 * 0 + 1) * (q + 1) then unitTarget else oneDigestBlock)
        0).bytes = unitTarget.val := by
      show (if 0 ≤ t + 1 then
          stateOf OuterInitial.zeroDigest q
            (fun m => if m < (22 + 5 * 0 + 1) * (q + 1) then unitTarget else oneDigestBlock) 0
        else OuterInitial.zeroDigest).bytes = unitTarget.val
      rw [if_pos (Nat.zero_le _)]
      rfl
    rw [hh1, hh0, if_neg one_block_ne_unit_target, decode_elements_of_element]
  rw [hone, hzero] at hcut
  exact zero_ne_one (List.head_eq_of_cons_eq hcut).symm

/-- (2) **THE OBSTRUCTION AT THE LOG CELL'S OWN STAGE.**  The instance of
`D2_later_stage_obstruction_general` at `t = 23`: at `historyGrinder` the same
reconstruction read at the LOG CELL's own chain stage `22 + 5 r + 2` is NOT
`GrindCausal`.  The history the run hands the stage-`22 + 5 r + 2` absorb contains
the digest of the stage-`22 + 5 r + 1` absorb answer, which sits at answer position
`slotPos q (22 + 5 r + 1) q`, above the cut.

SO THE GLP-SHAPED RECONSTRUCTION AT THE LATER STAGE CANNOT BE HANDED TO THE ADOPTED
HEADLINE.  What would be needed is a version of
`GrindingUnionBound.grinding_union_bad_draw_probability_le_combined` whose lane
causality cuts at `roundStage r * (q + 1)` answer positions instead of
`(22 + 5 * r + 1) * (q + 1)`.  That module's own comment records that its diagonal
step would survive such a cut; NO ADOPTED LEMMA STATES THE HEADLINE AT IT, and none
is proved here.  I did not find a two-absorb pairing that IS `GrindCausal`, and no
adopted lemma gives one. -/
theorem later_stage_reconstruction_is_not_grind_causal (q : Nat) :
    ¬ GrindCausal q (grinderMessageAtStage OuterInitial.zeroDigest q historyGrinder
        (fun r => 22 + 5 * r + 2)) :=
  D2_later_stage_obstruction_general q 23 (by omega) _ (by omega)

/-- (2) **AND THE GATE CELL'S OWN STAGE `22 + 5 r + 3` IS COVERED TOO**, so the
obstruction is not tied to the log cell's offset. -/
theorem D2b_gate_cell_stage_is_not_grind_causal (q : Nat) :
    ¬ GrindCausal q (grinderMessageAtStage OuterInitial.zeroDigest q historyGrinder
        (fun r => 22 + 5 * r + 3)) :=
  D2_later_stage_obstruction_general q 24 (by omega) _ (by omega)

/-- **A GRINDER WHOSE ABSORB IGNORES THE HISTORY.**  It probes exactly as
`historyGrinder` does, but its absorb is the CONSTANT twenty-four bytes of `1`.  It
is `GrindingBounded` and `ChallengeRestricted` on the same arithmetic, and it exists
to keep the obstruction above from being overstated. -/
def blindGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun _ _ _ _ => (0, bytesOfElement 1)

theorem D1b_blind_grinder_bounded (L : Nat) (hL : 93 ≤ L) : GrindingBounded L blindGrinder := by
  refine ⟨fun _ i _ _ _ => ?_, fun _ _ _ _ => ?_⟩
  · show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · show 61 + (bytesOfElement 1).length ≤ L
    rw [bytes_of_element_length]
    omega

theorem D1c_blind_grinder_challenge_restricted : ChallengeRestricted blindGrinder :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- (2) **AND A LEGAL GRINDER WHOSE LATER-STAGE RECONSTRUCTION *IS* `GrindCausal`.**
At `blindGrinder` the SAME reconstruction that fails causality at `historyGrinder`
is `GrindCausal` at EVERY stage function, however far above the adopted cut it
reads.  So `later_stage_reconstruction_is_not_grind_causal` and
`D2_later_stage_obstruction_general` are NOT statements that "reading a later stage
breaks causality"; what they establish is that the later-stage reconstruction
cannot be handed to the adopted headline as a construction over ALL grinders, which
is the only form that headline accepts. -/
theorem D1_blind_grinder_later_stage_is_grind_causal (e0 : Transcript.Digest) (q : Nat)
    (stage : Nat → Nat) :
    GrindCausal q (grinderMessageAtStage e0 q blindGrinder stage) :=
  fun _ _ _ _ _ _ _ => rfl

/-! ## 3. THE SPLIT LANES

The stage-`22 + 5 r` payload is cut at the adopted log-lane degree bound -- five
encoded field elements, `24 * 5` bytes -- and each lane decodes its own half through
GLP's own `decodeElements`.  Nothing is dropped: `halves_recover_payload`. -/

/-- **THE LOG HALF OF AN ABSORBED PAYLOAD**: its first `24 * 5` bytes, the adopted
log-lane degree bound in the twenty-four-byte limb layout of GLP's
`bytesOfElement`. -/
def logHalf (bs : Transcript.Bytes) : Transcript.Bytes := bs.take 120

/-- **AND THE GATE HALF**: everything after them. -/
def gateHalf (bs : Transcript.Bytes) : Transcript.Bytes := bs.drop 120

/-- (3) **THE TWO HALVES ARE THE PAYLOAD.**  Nothing of the prover's absorb is
dropped by the split and nothing is invented by it. -/
theorem halves_recover_payload (bs : Transcript.Bytes) : logHalf bs ++ gateHalf bs = bs :=
  List.take_append_drop 120 bs

/-- (3) **THE LOG HALF NEVER EXCEEDS THE ADOPTED LOG DEGREE BOUND'S WORTH OF
BYTES**, whatever the prover absorbs. -/
theorem log_half_length_le (bs : Transcript.Bytes) : (logHalf bs).length ≤ 120 := by
  show (bs.take 120).length ≤ 120
  rw [List.length_take]
  exact Nat.min_le_left _ _

/-- (3) **AND THE GATE HALF IS WHAT IS LEFT.** -/
theorem gate_half_length (bs : Transcript.Bytes) : (gateHalf bs).length = bs.length - 120 := by
  show (bs.drop 120).length = bs.length - 120
  rw [List.length_drop]

/-- (3) **THE LOG HALF IS NON-EMPTY AS SOON AS THE PAYLOAD IS.** -/
theorem A1_log_half_nonempty_iff (bs : Transcript.Bytes) :
    logHalf bs ≠ [] ↔ 0 < bs.length := by
  constructor
  · intro h
    by_contra hc
    exact h (by
      have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [logHalf, this]; rfl)
  · intro h hnil
    have hz : (logHalf bs).length = 0 := by rw [hnil]; rfl
    rw [logHalf, List.length_take] at hz
    omega

/-- (3) **BUT THE GATE HALF IS NON-EMPTY ONLY ABOVE `24 * 5` BYTES.** -/
theorem A2_gate_half_nonempty_iff (bs : Transcript.Bytes) :
    gateHalf bs ≠ [] ↔ 120 < bs.length := by
  constructor
  · intro h
    by_contra hc
    exact h (by rw [← List.length_eq_zero, gate_half_length]; omega)
  · intro h hnil
    have hz : (gateHalf bs).length = 0 := by rw [hnil]; rfl
    rw [gate_half_length] at hz
    omega

/-- (3) **SO THE TWO LANES SEPARATE ONLY ABOVE `24 * 5` BYTES.**  Both halves are
non-empty EXACTLY when `120 < bs.length`.  At or below that threshold the GATE
lane's message is EMPTY (`short_payload_gives_empty_gate_message`), and `120` is
precisely the ceiling of GLP's own `hfitlog` (`(p + 23) / 24 ≤ 5` is `p ≤ 120`), so
on the WHOLE of GLP's covered class -- its own `selectorGrinder` included
(`B3_glp_selector_grinder_gate_message_is_empty`) -- this split makes the two lanes
differ by SILENCING the gate lane rather than by giving it the protocol's second
message.  See HONESTY (iv): the two lanes attain the adopted shape-legal lengths
TOGETHER only at a payload of `24 * 15 = 360` bytes (`C8_big_grinder_halves`). -/
theorem A3_both_halves_nonempty_iff (bs : Transcript.Bytes) :
    (logHalf bs ≠ [] ∧ gateHalf bs ≠ []) ↔ 120 < bs.length := by
  rw [A1_log_half_nonempty_iff, A2_gate_half_nonempty_iff]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-- **THE SPLIT ROUND MESSAGE.**  GLP's reconstruction of what the run hands the
stage-`22 + 5 r` absorb, with one half of the payload taken out of it. -/
def grinderSplitMessage (half : Transcript.Bytes → Transcript.Bytes)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) :
    Nat → (Nat → Block) → (Nat → Nat → Block) → List Element :=
  fun r a ch =>
    decodeElements
      (half (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a)
        (digestLookup (grinderHist e0 q (22 + 5 * r) a) ch (22 + 5 * r))
        (grinderProbes e0 q (22 + 5 * r) a)).2)

/-- **THE LOG LANE'S ROUND MESSAGE.** -/
def grinderLogMessage (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) :
    Nat → (Nat → Block) → (Nat → Nat → Block) → List Element :=
  grinderSplitMessage logHalf e0 q g

/-- **THE GATE LANE'S ROUND MESSAGE.** -/
def grinderGateMessage (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) :
    Nat → (Nat → Block) → (Nat → Nat → Block) → List Element :=
  grinderSplitMessage gateHalf e0 q g

/-- (3) **EITHER HALF OBEYS THE PROTOCOL'S CAUSALITY**, because the payload it is
taken out of does: the split is applied after the absorb, so it cannot widen what
the message reads. -/
theorem grinder_split_message_causal (half : Transcript.Bytes → Transcript.Bytes)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) :
    GrindCausal q (grinderSplitMessage half e0 q g) := by
  intro r a1 a2 ch1 ch2 ha hch
  have hh : grinderHist e0 q (22 + 5 * r) a1 = grinderHist e0 q (22 + 5 * r) a2 :=
    grinder_hist_congr e0 q (22 + 5 * r) a1 a2 ha
  have hp : grinderProbes e0 q (22 + 5 * r) a1 = grinderProbes e0 q (22 + 5 * r) a2 :=
    grinder_probes_congr e0 q (22 + 5 * r) a1 a2 ha
  have hl : digestLookup (grinderHist e0 q (22 + 5 * r) a1) ch1 (22 + 5 * r)
      = digestLookup (grinderHist e0 q (22 + 5 * r) a1) ch2 (22 + 5 * r) :=
    digest_lookup_congr _ ch1 ch2 (22 + 5 * r) hch
  show decodeElements (half (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a1)
      (digestLookup (grinderHist e0 q (22 + 5 * r) a1) ch1 (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) a1)).2)
    = decodeElements (half (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a2)
      (digestLookup (grinderHist e0 q (22 + 5 * r) a2) ch2 (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) a2)).2)
  rw [hl, hh, hp]

theorem grinder_log_message_causal (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) :
    GrindCausal q (grinderLogMessage e0 q g) := grinder_split_message_causal logHalf e0 q g

theorem grinder_gate_message_causal (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) :
    GrindCausal q (grinderGateMessage e0 q g) := grinder_split_message_causal gateHalf e0 q g

/-- (3) **THE LOG LANE'S MESSAGE IS AT MOST FIVE ELEMENTS, WITH NO HYPOTHESIS ON
THE PROVER AT ALL.**  Its half is at most `24 * 5` bytes by construction, so GLP's
`hfitlog` is DISCHARGED here rather than assumed. -/
theorem grinder_log_message_length_le (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block) :
    (grinderLogMessage e0 q g r a ch).length ≤ 5 := by
  have h := decode_elements_length_le_of_payload
    (logHalf (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a)
      (digestLookup (grinderHist e0 q (22 + 5 * r) a) ch (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) a)).2) 120 (log_half_length_le _)
  exact le_trans h (by norm_num)

/-- (3) **AND THE GATE LANE'S MESSAGE IS BOUNDED BY WHAT IS LEFT OF THE PAYLOAD.**
The payload bound is required only at the COUPLED stages `22 + 5 r`, exactly as in
GLP: the split lanes never read the absorb anywhere else, and a uniform `∀ k` bound
would exclude legal provers such as GLP's `mixedGrinder`. -/
theorem grinder_gate_message_length_le (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (p : Nat)
    (hp : ∀ (r : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (g.absorb (22 + 5 * r) h ch pa).2.length ≤ p)
    (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block) :
    (grinderGateMessage e0 q g r a ch).length ≤ (p - 120 + 23) / 24 := by
  refine decode_elements_length_le_of_payload _ (p - 120) ?_
  rw [gate_half_length]
  exact Nat.sub_le_sub_right (hp r _ _ _) 120

/-- **THE LOG LANE.**  `truth` is a free causal column and `claim`, `truthClaim` are
the initial running claims, exactly as in GLP and the adopted `RawBlockLanes`. -/
def grinderLogLane (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (cl tcl : Element) : GrindLane where
  message := grinderLogMessage e0 q g
  truth := tr
  claim := cl
  truthClaim := tcl

/-- **AND THE GATE LANE.** -/
def grinderGateLane (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (cl tcl : Element) : GrindLane where
  message := grinderGateMessage e0 q g
  truth := tr
  claim := cl
  truthClaim := tcl

theorem grinder_log_lane_causal (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (htr : GrindCausal q tr)
    (cl tcl : Element) : GrindLaneCausal q (grinderLogLane e0 q g tr cl tcl) :=
  ⟨grinder_log_message_causal e0 q g, htr⟩

theorem grinder_gate_lane_causal (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (htr : GrindCausal q tr)
    (cl tcl : Element) : GrindLaneCausal q (grinderGateLane e0 q g tr cl tcl) :=
  ⟨grinder_gate_message_causal e0 q g, htr⟩

/-- (3) **THE LOG LANE IS BOUNDED WITH NO PAYLOAD HYPOTHESIS.**  Compare GLP's
`grinder_lane_bounded_at_coupled_stages`, which needs `hp` and `hfitlog` on both
lanes. -/
theorem grinder_log_lane_bounded (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (htr : ∀ (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block), (tr r a ch).length ≤ 5) :
    GrindLaneBounded (grinderLogLane e0 q g tr cl tcl) 5 :=
  fun r a ch => ⟨grinder_log_message_length_le e0 q g r a ch, htr r a ch⟩

/-- (3) **AND THE GATE LANE IS BOUNDED BY THE REST OF THE PAYLOAD.** -/
theorem grinder_gate_lane_bounded_at_coupled_stages (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (p bd : Nat)
    (hp : ∀ (r : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (g.absorb (22 + 5 * r) h ch pa).2.length ≤ p)
    (hfit : (p - 120 + 23) / 24 ≤ bd)
    (htr : ∀ (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block), (tr r a ch).length ≤ bd) :
    GrindLaneBounded (grinderGateLane e0 q g tr cl tcl) bd :=
  fun r a ch =>
    ⟨le_trans (grinder_gate_message_length_le e0 q g p hp r a ch) hfit, htr r a ch⟩

/-! ### 3b. THE TWO PAIRINGS -/

/-- (3b) **THE PAYLOAD THE LANE-SIDE RECONSTRUCTION FEEDS IS THE PAYLOAD THE RUN
FEEDS.**  GLP's `grinder_lane_message_is_absorbed_payload`, one level below the
decoder, so that both halves can be taken out of it. -/
theorem grinder_absorb_payload_is_the_run_payload (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g) (r : Nat) (T : OracleTable (boundedQueries L)) :
    (g.absorb (22 + 5 * r)
        (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
        (digestLookup (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
          (grindTableView L hL e0 q g hb T) (22 + 5 * r))
        (grinderProbes e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))).2
      = (g.absorb (22 + 5 * r)
          (stateOf e0 q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))
          (challengesOf L hL T)
          (probeAnsOf q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))).2 := by
  have habs := hcr.2 (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
    (digestLookup (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
      (grindTableView L hL e0 q g hb T) (22 + 5 * r))
    (challengesOf L hL T)
    (grinderProbes e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
    (fun j hj => grinder_lookup_is_challenges L hL e0 q g hb (22 + 5 * r) T j hj)
  rw [habs, grinder_hist_is_run_history, grinder_probes_is_run_probes]

/-- (3b) **EITHER SPLIT LANE'S ROUND MESSAGE IS ITS OWN HALF OF THE PAYLOAD THE RUN
ABSORBS**, at EVERY table and with no conditioning event -- GLP's pairing, once per
half. -/
theorem grinder_split_message_is_absorbed_payload (half : Transcript.Bytes → Transcript.Bytes)
    (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (r : Nat) (T : OracleTable (boundedQueries L)) :
    grinderSplitMessage half e0 q g r (grindRunView L hL e0 q g hb T)
        (grindTableView L hL e0 q g hb T)
      = decodeElements (half (g.absorb (22 + 5 * r)
          (stateOf e0 q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))
          (challengesOf L hL T)
          (probeAnsOf q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))).2) := by
  show decodeElements (half (g.absorb (22 + 5 * r)
      (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
      (digestLookup (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
        (grindTableView L hL e0 q g hb T) (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))).2) = _
  rw [grinder_absorb_payload_is_the_run_payload L hL e0 q g hb hcr r T]

/-- (3b) **THE LOG LANE'S PAIRING.** -/
theorem grinder_log_lane_message_is_absorbed_payload (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (r : Nat) (T : OracleTable (boundedQueries L)) :
    (grinderLogLane e0 q g tr cl tcl).message r (grindRunView L hL e0 q g hb T)
        (grindTableView L hL e0 q g hb T)
      = decodeElements (logHalf (g.absorb (22 + 5 * r)
          (stateOf e0 q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))
          (challengesOf L hL T)
          (probeAnsOf q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))).2) :=
  grinder_split_message_is_absorbed_payload logHalf L hL e0 q g hb hcr r T

/-- (3b) **AND THE GATE LANE'S.** -/
theorem grinder_gate_lane_message_is_absorbed_payload (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (r : Nat) (T : OracleTable (boundedQueries L)) :
    (grinderGateLane e0 q g tr cl tcl).message r (grindRunView L hL e0 q g hb T)
        (grindTableView L hL e0 q g hb T)
      = decodeElements (gateHalf (g.absorb (22 + 5 * r)
          (stateOf e0 q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))
          (challengesOf L hL T)
          (probeAnsOf q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))).2) :=
  grinder_split_message_is_absorbed_payload gateHalf L hL e0 q g hb hcr r T

/-- (3b) **AND THE TWO LANES' HALVES ARE THE WHOLE PAYLOAD THE RUN ABSORBS.**  So
the split loses nothing: the two coupled messages of round `r` together are exactly
what the prover submitted at that stage. -/
theorem grinder_split_messages_concatenate_at_the_run (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (r : Nat) (T : OracleTable (boundedQueries L)) :
    logHalf (g.absorb (22 + 5 * r)
        (stateOf e0 q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))
        (challengesOf L hL T)
        (probeAnsOf q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))).2
      ++ gateHalf (g.absorb (22 + 5 * r)
        (stateOf e0 q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))
        (challengesOf L hL T)
        (probeAnsOf q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))).2
      = (g.absorb (22 + 5 * r)
        (stateOf e0 q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))
        (challengesOf L hL T)
        (probeAnsOf q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))).2 :=
  halves_recover_payload _

/-! ## 4. THE BYTE BUDGET, AND THAT THE TWO LANES REALLY DIFFER -/

/-- (4) **THE GATE-LANE BUDGET IS EXACTLY `24 * 5 + 24 * (quo + 2)` BYTES.**  The
log lane pays nothing: `grinder_log_lane_bounded` needs no payload hypothesis. -/
theorem gate_budget_iff (p quo : Nat) :
    ((p - 120 + 23) / 24 ≤ quo + 2) ↔ p ≤ 120 + 24 * (quo + 2) := by omega

/-- (4) **AND AT THE ADOPTED `quo = 8` IT IS EXACTLY 360 BYTES**, i.e. fifteen
encoded field elements per absorb: five on the log lane and ten on the gate lane.
GLP's budget at the same quotient is 120 bytes, five elements, shared by both
lanes; the split RAISES the budget rather than halving it, because the two halves
are disjoint. -/
theorem gate_budget_at_adopted_quotient (p : Nat) :
    ((p - 120 + 23) / 24 ≤ 8 + 2) ↔ p ≤ 360 := by omega

/-- (4) **THE CANDIDATE'S GATE BUDGET IS IMPLIED BY GLP's**, at every `p` and every
`quo`.  So the hypothesis set of section 5 is strictly WEAKER than GLP's on the byte
budget: `hfitlog` is DROPPED (`grinder_log_lane_bounded` takes no hypothesis on `g`
at all) and `hfitgate` is RELAXED, never relocated.

WHAT THIS DOES NOT SAY.  It does NOT make section 5's headline imply GLP's, nor
GLP's imply section 5's: the two bound DIFFERENT `grindingFullBadEvent`s, because
the lanes differ (`B4_split_and_glp_gate_lanes_differ_at_selector_grinder`).  The
widening is real in the direction of the COVERED CLASS -- there are legal grinders
outside GLP's budget at every `p` and inside this one
(`C3_split_selector_is_outside_glp_budget` at `144` bytes,
`C10_big_grinder_is_outside_glp_budget` at `360`). -/
theorem C1_candidate_gate_budget_is_weaker (p quo : Nat) (h : (p + 23) / 24 ≤ quo + 2) :
    (p - 120 + 23) / 24 ≤ quo + 2 := by omega

/-- (4) **FIFTEEN ENCODED ELEMENTS ARE INSIDE THE BUDGET AT `quo = 8`.** -/
theorem three_hundred_and_sixty_bytes_fit : ((unitRepeat 15).length - 120 + 23) / 24 ≤ 8 + 2 := by
  rw [unit_repeat_length]

/-- (4) **AND SIXTEEN ARE OUTSIDE IT**, by exactly one element. -/
theorem sixteen_elements_do_not_fit :
    ¬ (((unitRepeat 16).length - 120 + 23) / 24 ≤ 8 + 2) := by
  rw [unit_repeat_length]
  decide

theorem unit_repeat_five_length : (unitRepeat 5).length = 120 := by
  rw [unit_repeat_length]

/-- (4) GLP's `unitRepeat` is a bare concatenation, so it splits at any element
boundary. -/
theorem C4_unit_repeat_add (m n : Nat) :
    unitRepeat (m + n) = unitRepeat m ++ unitRepeat n := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
      have hs : k + 1 + n = (k + n) + 1 := by omega
      rw [hs]
      show bytesOfElement 1 ++ unitRepeat (k + n) = unitRepeat (k + 1) ++ unitRepeat n
      rw [ih]
      rfl

/-- (4) A payload of five encoded elements followed by one more splits into exactly
those five and exactly that one. -/
theorem log_half_of_five_plus_one (x : Element) :
    logHalf (unitRepeat 5 ++ bytesOfElement x) = unitRepeat 5 :=
  take_of_append _ _ 120 unit_repeat_five_length

theorem gate_half_of_five_plus_one (x : Element) :
    gateHalf (unitRepeat 5 ++ bytesOfElement x) = bytesOfElement x :=
  drop_of_append _ _ 120 unit_repeat_five_length

/-! ## 5. THE HEADLINE, AT TWO DISTINCT COUPLED MESSAGES -/

open Classical in
/-- (5) **THE ADOPTED HEADLINE, WITH THE TWO LANES CARRYING THE TWO MESSAGES THE
GRINDER ACTUALLY SUBMITS.**  GLP's
`grinder_paired_union_bad_draw_probability_le_combined` puts the SAME message
family on both outer lanes -- its HONESTY (v), and the restriction its adversarial
review judged LARGER than the byte budget.  Here the LOG lane carries
`grinderLogMessage` and the GATE lane carries `grinderGateMessage`, and
`split_lanes_can_carry_different_messages` shows these are genuinely different
families.  The constant is unchanged -- the adopted
`ChallengeUnionBound.combinedBound` plus the adopted grinding chain's clash term --
and nothing is added or dropped.

WHAT THE HYPOTHESES NOW COST.  `hp` is GLP's, quantified over the COUPLED stages
`22 + 5 * r` ONLY, because the split lanes read the absorb nowhere else; a uniform
`∀ k` form was already shown by GLP to exclude legal provers such as its
`mixedGrinder`, which absorbs 144 bytes at the non-coupled stage `0`.  `hfitlog` is
GONE: the log half is at most `24 * 5` bytes by construction, so the log lane's
degree bound is discharged rather than assumed (`grinder_log_lane_bounded`).  The
only budget left is `hfitgate`, which `gate_budget_iff` shows is EXACTLY
`p ≤ 120 + 24 * (quo + 2)` bytes -- at the adopted `quo = 8`, EXACTLY 360 bytes, or
fifteen encoded field elements per absorb, against GLP's 120 bytes and five.

THE TWO LANES SEPARATE ONLY ABOVE `24 * 5` BYTES.  `logHalf bs` and `gateHalf bs`
are both non-empty exactly when `120 < bs.length` (`A3_both_halves_nonempty_iff`);
at or below that the GATE lane's message is EMPTY, so on the WHOLE of GLP's covered
class -- every grinder GLP's `hfitlog` admits, its own `selectorGrinder` included
(`B3_glp_selector_grinder_gate_message_is_empty`) -- this split makes the two lanes
differ by SILENCING the gate lane, not by giving it the protocol's second message.
An empty gate cell is not a legal round message: the adopted `Verifier.shape`
demands `c.quotientDegree + 2` entries per gate round and five per log round
(`B1_accepted_gate_rounds_never_empty_nor_singleton`,
`B2_accepted_log_rounds_have_length_five`), and these two lanes attain both lengths
together only at a payload of exactly `24 * 15 = 360` bytes
(`C8_big_grinder_halves`).  Neither this module nor GLP enforces those lengths --
`GrindLaneBounded` is a `≤` -- so this is a coarseness INHERITED from the adopted
grinding model, not one opened here.  `C11_big_grinder_split_bound_at_thirteen`
closes this headline at the `360`-byte grinder, the only point at which BOTH lanes
carry shape-legal lengths.

NEITHER THIS HEADLINE NOR GLP's IS AN INSTANCE OF THE OTHER.  They bound DIFFERENT
`grindingFullBadEvent`s, because the lanes differ
(`B4_split_and_glp_gate_lanes_differ_at_selector_grinder`: at one and the same
grinder, table and round, this split's gate message is `[]` where GLP's paired lane
carries `[1]`), so neither statement can be obtained from the other by substituting
arguments.  That is a statement about the SHAPE of the two statements, proved at a
common grinder; NO NON-IMPLICATION BETWEEN THE TWO PROBABILITY BOUNDS IS PROVED
HERE, and none is claimed.  What IS comparable is the byte budget, and there the
hypothesis
here is strictly weaker (`C1_candidate_gate_budget_is_weaker`), with legal grinders
covered here and outside GLP's budget at every `p`
(`C3_split_selector_is_outside_glp_budget`, `C10_big_grinder_is_outside_glp_budget`).

WHAT THIS IS NOT.  It is NOT a demonstration that grinding buys a prover anything,
and no SEARCHING prover is exhibited anywhere in this module; see HONESTY (ii).
`ChallengeRestricted g` is still assumed and still undischarged.  And the split is a
PROJECTION of one absorbed payload, not two absorbs: see HONESTY (iii) and
`later_stage_reconstruction_is_not_grind_causal`. -/
theorem grinder_split_union_bad_draw_probability_le_combined (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g)
    (trlog trgate : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (htrlog : GrindCausal q trlog) (htrgate : GrindCausal q trgate)
    (cl1 tcl1 cl2 tcl2 : Element) (d quo constraints p : Nat)
    (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hp : ∀ (r : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (g.absorb (22 + 5 * r) h ch pa).2.length ≤ p)
    (hfitgate : (p - 120 + 23) / 24 ≤ quo + 2)
    (htrlogb : ∀ (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block),
      (trlog r a ch).length ≤ 5)
    (htrgateb : ∀ (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block),
      (trgate r a ch).length ≤ quo + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L hL e0 q g hb (grinderLogLane e0 q g trlog cl1 tcl1)
          (grinderGateLane e0 q g trgate cl2 tcl2) d (2 ^ d) gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d quo d constraints
        + (((22 + 5 * d) * (q + 1) : Nat) : ℚ) * ((((22 + 5 * d) * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  grinding_union_bad_draw_probability_le_combined L hL e0 q g hb hcr
    (grinderLogLane e0 q g trlog cl1 tcl1) (grinderGateLane e0 q g trgate cl2 tcl2)
    (grinder_log_lane_causal e0 q g trlog htrlog cl1 tcl1)
    (grinder_gate_lane_causal e0 q g trgate htrgate cl2 tcl2)
    d quo constraints gv coeffsOf hdu
    (grinder_log_lane_bounded e0 q g trlog cl1 tcl1 htrlogb)
    (grinder_gate_lane_bounded_at_coupled_stages e0 q g trgate cl2 tcl2 p (quo + 2) hp
      hfitgate htrgateb)
    hclen

/-! ## 6. THE WITNESSES -/

/-- **A GRINDER WHOSE TWO COUPLED MESSAGES DIFFER, AND WHICH SELECTS ON ITS
PROBES.**  It probes at its own current digest exactly as the adopted
`GrindingQueryBound.probeGrinder` does, and its absorb emits five encoded copies of
the field element `1` followed by the twenty-four bytes of `1` WHEN AND ONLY WHEN
its first probe came back the constant table's block, and followed by the bytes of
`0` otherwise.  So its LOG half is five elements at every branch, its GATE half is
one element, and the two are never equal.

IT DOES NOT SEARCH.  It reads probe `0` once and branches between two CONSTANT
payloads; it never re-probes and it never retries.  This is an instance of the
arithmetic of section 5, in the same sense in which GLP's `selectorGrinder` and
`GrindingUnionBound`'s `probeGrinder` are instances of theirs, and it is NOT
evidence that grinding buys a prover anything. -/
def splitSelectorGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun k _ _ pa =>
    (0, if (pa k 0).val = unitTarget.val then unitRepeat 5 ++ bytesOfElement 1
        else unitRepeat 5 ++ bytesOfElement 0)

/-- (6) Its absorb payload is always five encoded elements followed by one more. -/
theorem split_selector_absorb_form (k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    ∃ x : Element, (splitSelectorGrinder.absorb k h ch pa).2 = unitRepeat 5 ++ bytesOfElement x := by
  by_cases hc : (pa k 0).val = unitTarget.val
  · exact ⟨1, by
      show (if (pa k 0).val = unitTarget.val then unitRepeat 5 ++ bytesOfElement 1
        else unitRepeat 5 ++ bytesOfElement 0) = _
      rw [if_pos hc]⟩
  · exact ⟨0, by
      show (if (pa k 0).val = unitTarget.val then unitRepeat 5 ++ bytesOfElement 1
        else unitRepeat 5 ++ bytesOfElement 0) = _
      rw [if_neg hc]⟩

theorem split_selector_payload_length (k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    (splitSelectorGrinder.absorb k h ch pa).2.length ≤ 144 := by
  obtain ⟨x, hx⟩ := split_selector_absorb_form k h ch pa
  rw [hx, List.length_append, unit_repeat_five_length, bytes_of_element_length]

/-- (6) And EXACTLY `144` bytes, at every stage and every branch. -/
theorem C2_split_selector_payload_exact (k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    (splitSelectorGrinder.absorb k h ch pa).2.length = 144 := by
  obtain ⟨x, hx⟩ := split_selector_absorb_form k h ch pa
  rw [hx, List.length_append, unit_repeat_five_length, bytes_of_element_length]

/-- (6) **THIS MODULE'S OWN CLOSED INSTANCE ALREADY LIVES OUTSIDE GLP's BUDGET.**
For EVERY `p` at which GLP's coupled-stage payload hypothesis holds of
`splitSelectorGrinder`, GLP's `hfitlog` FAILS.  So GLP's headline cannot be applied
to this grinder at any `p`, while section 5's can (`split_selector_fits_gate`).
That is the sharpest evidence that the budget widening is real, and it sits at the
144-byte witness this module already ships.

VACUITY: `hp` is satisfiable at `p = 144`, by `split_selector_payload_length`. -/
theorem C3_split_selector_is_outside_glp_budget (p : Nat)
    (hp : ∀ (r : Nat) (h : Nat → Transcript.Digest)
      (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block),
      (splitSelectorGrinder.absorb (22 + 5 * r) h ch pa).2.length ≤ p) :
    ¬ ((p + 23) / 24 ≤ 5) := by
  have h144 := hp 0 (fun _ => OuterInitial.zeroDigest) (fun _ _ => unitTarget)
    (fun _ _ => unitTarget)
  rw [C2_split_selector_payload_exact] at h144
  omega

theorem split_selector_grinder_bounded (L : Nat) (hL : 205 ≤ L) :
    GrindingBounded L splitSelectorGrinder := by
  refine ⟨fun _ i _ _ _ => ?_, fun k h ch pa => ?_⟩
  · show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · exact le_trans (Nat.add_le_add_left (split_selector_payload_length k h ch pa) 61) (by omega)

theorem split_selector_grinder_challenge_restricted : ChallengeRestricted splitSelectorGrinder :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- (6) **IT READS ITS PROBE ANSWERS.**  Two probe histories that differ at probe
`0` of the stage give it different absorbs, at the same stage digests and the same
challenge answers. -/
theorem split_selector_grinder_reads_probes :
    ∃ (k : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
        (pa1 pa2 : Nat → Nat → Block),
      splitSelectorGrinder.absorb k h ch pa1 ≠ splitSelectorGrinder.absorb k h ch pa2 := by
  refine ⟨0, fun _ => OuterInitial.zeroDigest, fun _ _ => unitTarget,
    fun _ _ => unitTarget, fun _ _ => oneDigestBlock, ?_⟩
  intro hEq
  have hp : (if (unitTarget.val : Transcript.Bytes) = unitTarget.val
        then unitRepeat 5 ++ bytesOfElement 1 else unitRepeat 5 ++ bytesOfElement 0)
      = (if (oneDigestBlock.val : Transcript.Bytes) = unitTarget.val
        then unitRepeat 5 ++ bytesOfElement 1 else unitRepeat 5 ++ bytesOfElement 0) :=
    congrArg Prod.snd hEq
  rw [if_pos rfl, if_neg one_block_ne_unit_target] at hp
  have hx : bytesOfElement (1 : Element) = bytesOfElement (0 : Element) := by
    rw [← gate_half_of_five_plus_one (1 : Element), ← gate_half_of_five_plus_one (0 : Element),
      hp]
  have hy : elementOfBytes (bytesOfElement (1 : Element))
      = elementOfBytes (bytesOfElement (0 : Element)) := congrArg elementOfBytes hx
  rw [element_of_bytes_of_element, element_of_bytes_of_element] at hy
  exact zero_ne_one hy.symm

/-- (6) **AND IT IS THEREFORE NOT THE LIFT OF ANY TRANSCRIPT-RESTRICTED PROVER**, by
the adopted `GrindingQueryBound.grinding_of_strategy_ignores_probes`. -/
theorem split_selector_grinder_is_not_transcript_restricted (strat : StrategyChainBound.Strategy) :
    splitSelectorGrinder ≠ grindingOfStrategy strat := by
  intro h
  obtain ⟨k, hh, ch, pa1, pa2, hne⟩ := split_selector_grinder_reads_probes
  refine hne ?_
  rw [h]
  exact grinding_of_strategy_ignores_probes strat k hh ch pa1 pa2

/-- (6) **AND IT DOES NOT SEARCH -- FORMALISED.**  HONESTY (ii) asserts in prose
that this witness reads one probe and branches between two constant payloads; here
that is a theorem.  Its absorb is a FUNCTION OF ONE PROBE ANSWER and of nothing
else: not of the stage digests, not of the challenge oracle, not of any other
probe.  Two invocations agreeing only at `pa k 0` agree outright. -/
theorem D3_split_selector_absorb_depends_only_on_probe_zero (k : Nat)
    (h1 h2 : Nat → Transcript.Digest) (ch1 ch2 : Transcript.Digest → Nat → Block)
    (pa1 pa2 : Nat → Nat → Block) (h : pa1 k 0 = pa2 k 0) :
    splitSelectorGrinder.absorb k h1 ch1 pa1 = splitSelectorGrinder.absorb k h2 ch2 pa2 := by
  simp only [splitSelectorGrinder, h]

/-- (6) **THE LOG LANE'S MESSAGE AT THAT GRINDER IS FIVE ELEMENTS, AT EVERY VIEW.** -/
theorem split_selector_log_message_length (e0 : Transcript.Digest) (q r : Nat)
    (a : Nat → Block) (ch : Nat → Nat → Block) :
    (grinderLogMessage e0 q splitSelectorGrinder r a ch).length = 5 := by
  obtain ⟨x, hx⟩ := split_selector_absorb_form (22 + 5 * r)
    (grinderHist e0 q (22 + 5 * r) a)
    (digestLookup (grinderHist e0 q (22 + 5 * r) a) ch (22 + 5 * r))
    (grinderProbes e0 q (22 + 5 * r) a)
  show (decodeElements (logHalf (splitSelectorGrinder.absorb (22 + 5 * r) _ _ _).2)).length = 5
  rw [hx, log_half_of_five_plus_one, decode_unit_repeat_length]

/-- (6) **AND THE GATE LANE'S IS ONE.** -/
theorem split_selector_gate_message_length (e0 : Transcript.Digest) (q r : Nat)
    (a : Nat → Block) (ch : Nat → Nat → Block) :
    (grinderGateMessage e0 q splitSelectorGrinder r a ch).length = 1 := by
  obtain ⟨x, hx⟩ := split_selector_absorb_form (22 + 5 * r)
    (grinderHist e0 q (22 + 5 * r) a)
    (digestLookup (grinderHist e0 q (22 + 5 * r) a) ch (22 + 5 * r))
    (grinderProbes e0 q (22 + 5 * r) a)
  show (decodeElements (gateHalf (splitSelectorGrinder.absorb (22 + 5 * r) _ _ _).2)).length = 1
  rw [hx, gate_half_of_five_plus_one, decode_elements_of_element]
  rfl

/-- (6) **SO THE TWO LANES DIFFER AT EVERY ROUND, EVERY RUN VIEW AND EVERY
CHALLENGE VIEW.** -/
theorem split_selector_lanes_differ_at_every_view (e0 : Transcript.Digest) (q r : Nat)
    (a : Nat → Block) (ch : Nat → Nat → Block)
    (tr1 tr2 : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (cl1 tcl1 cl2 tcl2 : Element) :
    (grinderLogLane e0 q splitSelectorGrinder tr1 cl1 tcl1).message r a ch
      ≠ (grinderGateLane e0 q splitSelectorGrinder tr2 cl2 tcl2).message r a ch := by
  intro hEq
  have hlen := congrArg List.length hEq
  rw [show (grinderLogLane e0 q splitSelectorGrinder tr1 cl1 tcl1).message r a ch
      = grinderLogMessage e0 q splitSelectorGrinder r a ch from rfl,
    show (grinderGateLane e0 q splitSelectorGrinder tr2 cl2 tcl2).message r a ch
      = grinderGateMessage e0 q splitSelectorGrinder r a ch from rfl,
    split_selector_log_message_length, split_selector_gate_message_length] at hlen
  exact absurd hlen (by decide)

/-- (6) **THE THEOREM THAT RETIRES GLP HONESTY (v).**  A grinder and a round at
which the LOG lane's message and the GATE lane's message are DIFFERENT lists.
GLP's `both_paired_lanes_carry_the_same_message` is a `rfl` saying the two lanes of
its headline are definitionally equal as message families; here they are provably
unequal at a witness -- five elements against one. -/
theorem split_lanes_can_carry_different_messages :
    ∃ (g : GrindingStrategy) (e0 : Transcript.Digest) (q r : Nat) (a : Nat → Block)
        (ch : Nat → Nat → Block)
        (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element),
      (grinderLogLane e0 q g tr cl tcl).message r a ch
        ≠ (grinderGateLane e0 q g tr cl tcl).message r a ch :=
  ⟨splitSelectorGrinder, OuterInitial.zeroDigest, 0, 0, fun _ => unitTarget,
    fun _ _ => unitTarget, grindZeroTruth, 1, 0,
    split_selector_lanes_differ_at_every_view OuterInitial.zeroDigest 0 0 _ _ _ _ 1 0 1 0⟩

/-- (6) **AND THEY DIFFER AT A REAL RUN**, at every table and every probe budget. -/
theorem split_lanes_differ_at_the_run (L : Nat) (hL : 64 ≤ L) (hL2 : 205 ≤ L)
    (e0 : Transcript.Digest) (q r : Nat) (T : OracleTable (boundedQueries L))
    (tr1 tr2 : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (cl1 tcl1 cl2 tcl2 : Element) :
    (grinderLogLane e0 q splitSelectorGrinder tr1 cl1 tcl1).message r
        (grindRunView L hL e0 q splitSelectorGrinder (split_selector_grinder_bounded L hL2) T)
        (grindTableView L hL e0 q splitSelectorGrinder (split_selector_grinder_bounded L hL2) T)
      ≠ (grinderGateLane e0 q splitSelectorGrinder tr2 cl2 tcl2).message r
        (grindRunView L hL e0 q splitSelectorGrinder (split_selector_grinder_bounded L hL2) T)
        (grindTableView L hL e0 q splitSelectorGrinder
          (split_selector_grinder_bounded L hL2) T) :=
  split_selector_lanes_differ_at_every_view e0 q r _ _ tr1 tr2 cl1 tcl1 cl2 tcl2

/-- (6) **THE GATE LANE'S ROUND-`0` MESSAGE AT THE CONSTANT TABLE IS `[1]`**, the
adopted `RawBlockLanes.separatedRawLane`'s: the grinder takes its favourable branch
and the gate half is the twenty-four bytes of `1`. -/
theorem split_selector_gate_message_zero (L : Nat) (hL : 64 ≤ L) (hL2 : 205 ≤ L) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element) :
    (grinderGateLane OuterInitial.zeroDigest q splitSelectorGrinder tr cl tcl).message 0
        (grindRunView L hL OuterInitial.zeroDigest q splitSelectorGrinder
          (split_selector_grinder_bounded L hL2) (constantTable L))
        (grindTableView L hL OuterInitial.zeroDigest q splitSelectorGrinder
          (split_selector_grinder_bounded L hL2) (constantTable L))
      = [1] := by
  have hpa := grinder_probes_at_constant_table L hL q splitSelectorGrinder
    (split_selector_grinder_bounded L hL2) (22 + 5 * 0)
  show decodeElements (gateHalf (splitSelectorGrinder.absorb (22 + 5 * 0) _ _
      (grinderProbes OuterInitial.zeroDigest q (22 + 5 * 0)
        (grindRunView L hL OuterInitial.zeroDigest q splitSelectorGrinder
          (split_selector_grinder_bounded L hL2) (constantTable L)))).2) = [1]
  rw [hpa]
  show decodeElements (gateHalf (if (unitTarget.val : Transcript.Bytes) = unitTarget.val
      then unitRepeat 5 ++ bytesOfElement 1 else unitRepeat 5 ++ bytesOfElement 0)) = [1]
  rw [if_pos rfl, gate_half_of_five_plus_one, decode_elements_of_element]

/-- (6) **SO THE GATE LANE'S ROUND-`0` TARGET IS INHABITED**, at every probe budget
and every counter base.

WHAT THIS DOES NOT SAY.  The target is a `Finset` of DIGEST TRIPLES and the bounded
event is a `Finset` of TABLES; a non-empty target does not by itself give a
non-empty event, and nothing here or in the adopted `GrindingUnionBound` bridges
the two.  The LOG lane's round-`0` target is inhabited too, at a different honest
column: `E3_log_target_zero_nonempty`.  See HONESTY (x). -/
theorem split_selector_gate_target_zero_nonempty (L : Nat) (hL : 64 ≤ L) (hL2 : 205 ≤ L)
    (q : Nat) (base : Nat) :
    (grindRawTarget L hL OuterInitial.zeroDigest q splitSelectorGrinder
      (split_selector_grinder_bounded L hL2)
      (grinderGateLane OuterInitial.zeroDigest q splitSelectorGrinder grindZeroTruth 1 0)
      base 0 (constantTable L)).Nonempty := by
  refine grind_raw_target_zero_nonempty_of_agreement L hL OuterInitial.zeroDigest q
    splitSelectorGrinder (split_selector_grinder_bounded L hL2)
    (grinderGateLane OuterInitial.zeroDigest q splitSelectorGrinder grindZeroTruth 1 0)
    base (constantTable L) zeroDigestTriple (fun h => zero_ne_one h.symm) ?_
  have hmsg := split_selector_gate_message_zero L hL hL2 q grindZeroTruth 1 0
  show (OuterRound.polynomial (1 : Element)
        ((grinderGateLane OuterInitial.zeroDigest q splitSelectorGrinder
          grindZeroTruth 1 0).message 0 _ _)).eval
      (OuterChallenge.reduceTriple zeroDigestTriple)
    = (OuterRound.polynomial (0 : Element)
        ((grinderGateLane OuterInitial.zeroDigest q splitSelectorGrinder
          grindZeroTruth 1 0).truth 0 _ _)).eval
      (OuterChallenge.reduceTriple zeroDigestTriple)
  rw [hmsg]
  exact separated_raw_lane_agrees_at_zero
    (grindTableView L hL OuterInitial.zeroDigest q splitSelectorGrinder
      (split_selector_grinder_bounded L hL2) (constantTable L))

/-! ### 6b. THE LOG LANE'S ROUND-`0` TARGET

The gap HONESTY (x) used to concede was not forced by the split.  It came from
pairing a FIVE-element log message with the EMPTY honest column `grindZeroTruth`,
for which the adopted `separated_raw_lane_agrees_at_zero` has nothing to say.  At a
legal five-element honest column it closes. -/

theorem E0a_decode_unit_repeat (n : Nat) :
    decodeElementsAux n (unitRepeat n) = List.replicate n 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show decodeElementsAux (k + 1) (bytesOfElement 1 ++ unitRepeat k) = _
      rw [decode_elements_aux_chunk k _ _ (bytes_of_element_length 1),
        element_of_bytes_of_element, ih]
      rfl

theorem E0b_decode_unit_repeat_five : decodeElements (unitRepeat 5) = [1, 1, 1, 1, 1] := by
  have hfuel : ((unitRepeat 5).length + 23) / 24 = 5 := by rw [unit_repeat_length]
  rw [decodeElements, hfuel, E0a_decode_unit_repeat]
  rfl

/-- (6b) **THE LOG LANE'S ROUND-`0` MESSAGE AT THE CONSTANT TABLE, COMPUTED.**  The
module elsewhere gives only its length; it is `[1, 1, 1, 1, 1]`. -/
theorem E1_split_selector_log_message_zero (L : Nat) (hL : 64 ≤ L) (hL2 : 205 ≤ L) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element) :
    (grinderLogLane OuterInitial.zeroDigest q splitSelectorGrinder tr cl tcl).message 0
        (grindRunView L hL OuterInitial.zeroDigest q splitSelectorGrinder
          (split_selector_grinder_bounded L hL2) (constantTable L))
        (grindTableView L hL OuterInitial.zeroDigest q splitSelectorGrinder
          (split_selector_grinder_bounded L hL2) (constantTable L))
      = [1, 1, 1, 1, 1] := by
  have hpa := grinder_probes_at_constant_table L hL q splitSelectorGrinder
    (split_selector_grinder_bounded L hL2) (22 + 5 * 0)
  show decodeElements (logHalf (splitSelectorGrinder.absorb (22 + 5 * 0) _ _
      (grinderProbes OuterInitial.zeroDigest q (22 + 5 * 0)
        (grindRunView L hL OuterInitial.zeroDigest q splitSelectorGrinder
          (split_selector_grinder_bounded L hL2) (constantTable L)))).2) = _
  rw [hpa]
  show decodeElements (logHalf (if (unitTarget.val : Transcript.Bytes) = unitTarget.val
      then unitRepeat 5 ++ bytesOfElement 1 else unitRepeat 5 ++ bytesOfElement 0)) = _
  rw [if_pos rfl, log_half_of_five_plus_one, E0b_decode_unit_repeat_five]

/-- **AN HONEST COLUMN FOR THE LOG LANE**, as legal as GLP's `grindZeroTruth`:
constant, hence `GrindCausal`, and of length five, hence inside the log lane's
adopted degree bound.  It is the HONEST column, not the prover's data -- a free
parameter of the lane in GLP and in the adopted `RawBlockLanes` alike. -/
def logFiveTruth : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element :=
  fun _ _ _ => [1, 1, 1, 1, 0]

theorem E2a_log_five_truth_causal (q : Nat) : GrindCausal q logFiveTruth :=
  fun _ _ _ _ _ _ _ => rfl

theorem E2b_log_five_truth_length (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block) :
    (logFiveTruth r a ch).length ≤ 5 := Nat.le_refl 5

/-- (6b) The five-element analogue of the adopted `separated_raw_lane_agrees_at_zero`:
at the adopted `zeroDigestTriple` the claimed and honest round-`0` polynomials
agree. -/
theorem E2c_five_element_agreement :
    (OuterRound.polynomial (1 : Element) [1, 1, 1, 1, 1]).eval
        (OuterChallenge.reduceTriple zeroDigestTriple)
      = (OuterRound.polynomial (0 : Element) [1, 1, 1, 1, 0]).eval
        (OuterChallenge.reduceTriple zeroDigestTriple) := by
  rw [reduce_zero_digest_triple, OuterRound.polynomial_eval_exact,
    OuterRound.polynomial_eval_exact]
  simp only [OuterRound.evaluate, OuterRound.constantCoefficient, OuterRound.coefficientSum,
    List.reverse_cons, List.foldl, List.foldl_append, mul_zero, zero_add]
  ring

/-- (6b) **SO THE LOG LANE'S ROUND-`0` TARGET IS INHABITED TOO**, at the SAME
grinder, the SAME table and the SAME running claims as the gate lane's, with
`logFiveTruth` in place of `grindZeroTruth`.

WHAT THIS SETTLES AND WHAT IT DOES NOT.  It settles that the log-lane target gap is
NOT forced by the split.  It does NOT say that the original column's target is
empty -- no lemma here or in the adopted tree settles that either way -- and, as
everywhere in this line, a non-empty target is a `Finset` of DIGEST TRIPLES and does
not by itself give a non-empty event of TABLES. -/
theorem E3_log_target_zero_nonempty (L : Nat) (hL : 64 ≤ L) (hL2 : 205 ≤ L)
    (q : Nat) (base : Nat) :
    (grindRawTarget L hL OuterInitial.zeroDigest q splitSelectorGrinder
      (split_selector_grinder_bounded L hL2)
      (grinderLogLane OuterInitial.zeroDigest q splitSelectorGrinder logFiveTruth 1 0)
      base 0 (constantTable L)).Nonempty := by
  refine grind_raw_target_zero_nonempty_of_agreement L hL OuterInitial.zeroDigest q
    splitSelectorGrinder (split_selector_grinder_bounded L hL2)
    (grinderLogLane OuterInitial.zeroDigest q splitSelectorGrinder logFiveTruth 1 0)
    base (constantTable L) zeroDigestTriple (fun h => zero_ne_one h.symm) ?_
  have hmsg := E1_split_selector_log_message_zero L hL hL2 q logFiveTruth 1 0
  show (OuterRound.polynomial (1 : Element)
        ((grinderLogLane OuterInitial.zeroDigest q splitSelectorGrinder
          logFiveTruth 1 0).message 0 _ _)).eval
      (OuterChallenge.reduceTriple zeroDigestTriple)
    = (OuterRound.polynomial (0 : Element)
        ((grinderLogLane OuterInitial.zeroDigest q splitSelectorGrinder
          logFiveTruth 1 0).truth 0 _ _)).eval
      (OuterChallenge.reduceTriple zeroDigestTriple)
  rw [hmsg]
  exact E2c_five_element_agreement

theorem split_selector_fits_gate : (144 - 120 + 23) / 24 ≤ 8 + 2 := by norm_num

open Classical in
/-- (6) **THE CLOSED INSTANCE, AT A PROVER WHOSE TWO COUPLED MESSAGES DIFFER.**
Thirteen coupled rounds, `q` frame probes per stage, the LOG lane carrying
`splitSelectorGrinder`'s five-element log half and the GATE lane carrying its
one-element gate half -- two provably DIFFERENT message families
(`split_selector_lanes_differ_at_every_view`) -- and the adopted
`ChallengeUnionBound.combinedBound 13 8 13 123` plus the adopted grinding chain's
clash mass at `N = 87 (q + 1)`.  Every hypothesis of section 5 is discharged here;
none is assumed.

THE PROVER DOES NOT SEARCH: see HONESTY (ii). -/
theorem split_selector_split_bound_at_thirteen (L : Nat) (hL : 205 ≤ L) (q : Nat)
    (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q
          splitSelectorGrinder (split_selector_grinder_bounded L hL)
          (grinderLogLane OuterInitial.zeroDigest q splitSelectorGrinder grindZeroTruth 1 0)
          (grinderGateLane OuterInitial.zeroDigest q splitSelectorGrinder grindZeroTruth 1 0)
          13 (2 ^ 13) gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + ((87 * (q + 1) : Nat) : ℚ) * (((87 * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := grinder_split_union_bad_draw_probability_le_combined L
    (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q splitSelectorGrinder
    (split_selector_grinder_bounded L hL) split_selector_grinder_challenge_restricted
    grindZeroTruth grindZeroTruth (grind_zero_truth_causal q) (grind_zero_truth_causal q)
    1 0 1 0 13 8 123 144 gv coeffsOf thirteen_counter_budget
    (fun r => split_selector_payload_length (22 + 5 * r))
    split_selector_fits_gate (grind_zero_truth_length 5) (grind_zero_truth_length 10) hclen
  have harith : ((22 + 5 * 13) * (q + 1) : Nat) = 87 * (q + 1) := by omega
  rw [harith] at h
  exact h

open Classical in
/-- (6) **THE SAME CLOSED INSTANCE WITH BOTH LANES' ROUND-`0` TARGETS INHABITED.**
`split_selector_split_bound_at_thirteen` with the LOG lane's honest column
`logFiveTruth` in place of `grindZeroTruth`.  Every hypothesis is discharged exactly
as there, and now BOTH lanes' round-`0` targets are provably inhabited
(`E3_log_target_zero_nonempty`, `split_selector_gate_target_zero_nonempty`), which
is what retires the concession the module used to make in HONESTY (x). -/
theorem F1_split_bound_at_thirteen_with_inhabited_log_target (L : Nat) (hL : 205 ≤ L) (q : Nat)
    (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q
          splitSelectorGrinder (split_selector_grinder_bounded L hL)
          (grinderLogLane OuterInitial.zeroDigest q splitSelectorGrinder logFiveTruth 1 0)
          (grinderGateLane OuterInitial.zeroDigest q splitSelectorGrinder grindZeroTruth 1 0)
          13 (2 ^ 13) gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + ((87 * (q + 1) : Nat) : ℚ) * (((87 * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := grinder_split_union_bad_draw_probability_le_combined L
    (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q splitSelectorGrinder
    (split_selector_grinder_bounded L hL) split_selector_grinder_challenge_restricted
    logFiveTruth grindZeroTruth (E2a_log_five_truth_causal q) (grind_zero_truth_causal q)
    1 0 1 0 13 8 123 144 gv coeffsOf thirteen_counter_budget
    (fun r => split_selector_payload_length (22 + 5 * r))
    split_selector_fits_gate E2b_log_five_truth_length (grind_zero_truth_length 10) hclen
  have harith : ((22 + 5 * 13) * (q + 1) : Nat) = 87 * (q + 1) := by omega
  rw [harith] at h
  exact h

/-! ### 6c. THE WITNESS AT THE `360`-BYTE CEILING

`splitSelectorGrinder` is a 144-byte prover: its gate half is ONE element, which is
not a shape-legal gate round.  The only payload at which BOTH split lanes carry
adopted shape-legal lengths is `24 * 15 = 360` bytes -- five elements on the log
lane and ten on the gate lane at the adopted `quotientDegree = 8`.  This is that
grinder, and it is the strongest available defence of the `120` boundary. -/

/-- **A LEGAL GRINDER AT THE NEW `360`-BYTE CEILING**: fifteen encoded field
elements at every stage.  Like GLP's `selectorGrinder` and this module's
`splitSelectorGrinder` it is an instance of the arithmetic, NOT a searching
prover -- its absorb is CONSTANT, so it does not even read a probe. -/
def bigGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun _ _ _ _ => (0, unitRepeat 15)

theorem C5_big_grinder_payload (k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    (bigGrinder.absorb k h ch pa).2.length = 360 := by
  show (unitRepeat 15).length = 360
  rw [unit_repeat_length]

theorem C6_big_grinder_bounded (L : Nat) (hL : 421 ≤ L) : GrindingBounded L bigGrinder := by
  refine ⟨fun _ i _ _ _ => ?_, fun k h ch pa => ?_⟩
  · show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · exact le_trans (Nat.add_le_add_left (le_of_eq (C5_big_grinder_payload k h ch pa)) 61)
      (by omega)

theorem C7_big_grinder_challenge_restricted : ChallengeRestricted bigGrinder :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- (6c) **AT A `360`-BYTE PAYLOAD THE SPLIT PRODUCES EXACTLY THE TWO ADOPTED
`Verifier.shape` LENGTHS** at the adopted `quotientDegree = 8`: FIVE on the log lane
and TEN on the gate lane (`B1_accepted_gate_rounds_never_empty_nor_singleton`,
`B2_accepted_log_rounds_have_length_five`).  So the `24 * 5` boundary is not
arbitrary at the ceiling section 4 names -- it is the adopted log-round length times
the twenty-four-byte limb layout -- and this is the ONLY payload size at which both
split lanes are shape-legal at once. -/
theorem C8_big_grinder_halves (e0 : Transcript.Digest) (q r : Nat) (a : Nat → Block)
    (ch : Nat → Nat → Block) :
    (grinderLogMessage e0 q bigGrinder r a ch).length = 5
      ∧ (grinderGateMessage e0 q bigGrinder r a ch).length = 10 := by
  have hsplit : unitRepeat 15 = unitRepeat 5 ++ unitRepeat 10 := C4_unit_repeat_add 5 10
  constructor
  · show (decodeElements (logHalf (unitRepeat 15))).length = 5
    rw [hsplit, logHalf, take_of_append _ _ 120 unit_repeat_five_length,
      decode_unit_repeat_length]
  · show (decodeElements (gateHalf (unitRepeat 15))).length = 10
    rw [hsplit, gateHalf, drop_of_append _ _ 120 unit_repeat_five_length,
      decode_unit_repeat_length]

theorem C9_big_grinder_fits_gate : (360 - 120 + 23) / 24 ≤ 8 + 2 := by norm_num

/-- (6c) **AND GLP CANNOT REACH THIS GRINDER AT ANY `p`.**  Same shape as
`C3_split_selector_is_outside_glp_budget`, at the ceiling rather than at 144 bytes.

VACUITY: `hp` is satisfiable at `p = 360`, by `C5_big_grinder_payload`. -/
theorem C10_big_grinder_is_outside_glp_budget (p : Nat)
    (hp : ∀ (r : Nat) (h : Nat → Transcript.Digest)
      (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block),
      (bigGrinder.absorb (22 + 5 * r) h ch pa).2.length ≤ p) :
    ¬ ((p + 23) / 24 ≤ 5) := by
  have h360 := hp 0 (fun _ => OuterInitial.zeroDigest) (fun _ _ => unitTarget)
    (fun _ _ => unitTarget)
  rw [C5_big_grinder_payload] at h360
  omega

open Classical in
/-- (6c) **THE CLOSED INSTANCE AT THE `360`-BYTE CEILING.**  Thirteen coupled rounds,
`q` frame probes per stage, a prover absorbing fifteen encoded field elements at
every coupled stage, and BOTH split lanes at their exact adopted `Verifier.shape`
lengths -- five on the log lane, ten on the gate lane (`C8_big_grinder_halves`).
This is the instance section 4's budget claim names and the only one at which the
`120` boundary yields two shape-legal round messages at once.  Every hypothesis of
section 5 is discharged; none is assumed.

THE PROVER DOES NOT SEARCH: its absorb is constant, so it does not read a probe at
all.  See HONESTY (ii). -/
theorem C11_big_grinder_split_bound_at_thirteen (L : Nat) (hL : 421 ≤ L) (q : Nat)
    (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q
          bigGrinder (C6_big_grinder_bounded L hL)
          (grinderLogLane OuterInitial.zeroDigest q bigGrinder grindZeroTruth 1 0)
          (grinderGateLane OuterInitial.zeroDigest q bigGrinder grindZeroTruth 1 0)
          13 (2 ^ 13) gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + ((87 * (q + 1) : Nat) : ℚ) * (((87 * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := grinder_split_union_bad_draw_probability_le_combined L
    (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q bigGrinder
    (C6_big_grinder_bounded L hL) C7_big_grinder_challenge_restricted
    grindZeroTruth grindZeroTruth (grind_zero_truth_causal q) (grind_zero_truth_causal q)
    1 0 1 0 13 8 123 360 gv coeffsOf thirteen_counter_budget
    (fun r h ch pa => le_of_eq (C5_big_grinder_payload (22 + 5 * r) h ch pa))
    C9_big_grinder_fits_gate (grind_zero_truth_length 5) (grind_zero_truth_length 10) hclen
  have harith : ((22 + 5 * 13) * (q + 1) : Nat) = 87 * (q + 1) := by omega
  rw [harith] at h
  exact h

/-! ## 7. WHAT THE SPLIT COSTS -/

/-- (7) **THE PRICE OF THE FIXED BOUNDARY.**  A grinder whose whole absorb payload
is at most `24 * 5` bytes has an EMPTY gate-lane message: the split gives its entire
payload to the log lane.  GLP's own `selectorGrinder` absorbs twenty-four bytes and
is of exactly this shape, so under this split its gate lane says nothing.  This is
the honest cost of a boundary that is read off nothing in the payload. -/
theorem short_payload_gives_empty_gate_message (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block)
    (hshort : (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a)
      (digestLookup (grinderHist e0 q (22 + 5 * r) a) ch (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) a)).2.length ≤ 120) :
    grinderGateMessage e0 q g r a ch = [] := by
  have hnil : gateHalf (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a)
      (digestLookup (grinderHist e0 q (22 + 5 * r) a) ch (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) a)).2 = [] := by
    rw [← List.length_eq_zero, gate_half_length]
    omega
  show decodeElements (gateHalf (g.absorb (22 + 5 * r) _ _ _).2) = []
  rw [hnil]
  rfl

/-- (7) **AND THAT IS GLP's OWN ADOPTED WITNESS.**  `selectorGrinder` absorbs
twenty-four bytes, so under this split its GATE lane says nothing -- at every round,
every run view and every challenge view.  The theorem above states this as a general
lemma; here it is instantiated at the grinder GLP actually ships, which is the case
that matters for the comparison. -/
theorem B3_glp_selector_grinder_gate_message_is_empty (e0 : Transcript.Digest) (q r : Nat)
    (a : Nat → Block) (ch : Nat → Nat → Block) :
    grinderGateMessage e0 q selectorGrinder r a ch = [] :=
  short_payload_gives_empty_gate_message e0 q selectorGrinder r a ch
    (le_trans (selector_grinder_payload_length _ _ _ _) (by omega))

/-- (7) **SO ON GLP's COVERED CLASS THE SPLIT DOES NOT REFINE GLP's EVENT -- IT
REPLACES THE GATE LANE BY A SILENT ONE.**  At one and the same grinder, table,
round and view, this split's gate message is `[]` where GLP's paired lane carries
`[1]`.  The two headlines therefore bound DIFFERENT `grindingFullBadEvent`s and
NEITHER IMPLIES THE OTHER; see the section-5 docstring and HONESTY (iv). -/
theorem B4_split_and_glp_gate_lanes_differ_at_selector_grinder
    (L : Nat) (hL : 64 ≤ L) (hL2 : 93 ≤ L) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element) :
    (grinderGateLane OuterInitial.zeroDigest q selectorGrinder tr cl tcl).message 0
        (grindRunView L hL OuterInitial.zeroDigest q selectorGrinder
          (selector_grinder_bounded L hL2) (constantTable L))
        (grindTableView L hL OuterInitial.zeroDigest q selectorGrinder
          (selector_grinder_bounded L hL2) (constantTable L)) = []
      ∧ (grinderLane OuterInitial.zeroDigest q selectorGrinder tr cl tcl).message 0
        (grindRunView L hL OuterInitial.zeroDigest q selectorGrinder
          (selector_grinder_bounded L hL2) (constantTable L))
        (grindTableView L hL OuterInitial.zeroDigest q selectorGrinder
          (selector_grinder_bounded L hL2) (constantTable L)) = [1] :=
  ⟨B3_glp_selector_grinder_gate_message_is_empty _ _ _ _ _,
    selector_grinder_paired_message_zero L hL hL2 q tr cl tcl⟩

/-- (7) **AND THE BOUNDARY IS A CONVENTION, NOT A READING.**  Two payloads that a
prover could absorb -- five encoded elements then one, and one then five -- have
the SAME length and are split at the SAME byte, so the split cannot be recovering a
boundary the prover chose: the payload carries no mark of where the log cell ends.
On the deployed chain the two cells are two separate frames with their own lengths
(`chain_log_cell_at_stage_two`, `chain_gate_cell_at_stage_three`); no adopted lemma
recovers that boundary from the grinding chain's single payload. -/
theorem split_boundary_is_not_read_off_the_payload :
    (unitRepeat 5 ++ bytesOfElement (0 : Element)).length
        = (bytesOfElement (0 : Element) ++ unitRepeat 5).length ∧
      (logHalf (unitRepeat 5 ++ bytesOfElement (0 : Element))).length
        = (logHalf (bytesOfElement (0 : Element) ++ unitRepeat 5)).length := by
  constructor
  · rw [List.length_append, List.length_append, unit_repeat_five_length,
      bytes_of_element_length]
  · show (List.take 120 (unitRepeat 5 ++ bytesOfElement (0 : Element))).length
        = (List.take 120 (bytesOfElement (0 : Element) ++ unitRepeat 5)).length
    rw [List.length_take, List.length_take, List.length_append, List.length_append,
      unit_repeat_five_length, bytes_of_element_length]

/-! ### 7b. THE ADOPTED CHAIN DOES CARRY A LENGTH PREFIX -- THE GRINDING CHAIN DOES
NOT

The honest statement of what the grinding model loses.  It is NOT that a length
prefix is absorbed nowhere: the deployed chain prefixes EVERY coupled cell with the
eight little-endian bytes of its length.  It is that no adopted lemma transports
that prefix onto the grinding chain's single payload, where
`GrindingStrategy.absorb` returns a BARE byte string and GLP's `decodeElements`
reads it as a bare concatenation. -/

/-- (7b) **THE ADOPTED CELL ENCODING IS LENGTH-PREFIXED.**  `OuterAdapter.encodedVec`
is `Transcript.ext3VecBytes`, which is `le 8` of the length FOLLOWED BY the
twenty-four-byte limbs (Transcript.lean:83). -/
theorem G0_adopted_cell_encoding_is_prefixed (xs : List Verifier.Ext3) :
    OuterAdapter.encodedVec xs
      = Transcript.le 8 xs.length
        ++ (xs.map Connections.toTranscript).bind Transcript.ext3Bytes := by
  show Transcript.ext3VecBytes (xs.map Connections.toTranscript) = _
  rw [Transcript.ext3VecBytes, List.length_map]

/-- (7b) **SO A SHAPE-LEGAL LOG CELL IS 128 CHAIN BYTES, NOT 120.**  The eight
prefix bytes are the difference, and they are exactly what the grinding chain's
payload does not carry. -/
theorem G1_shape_legal_log_cell_is_128_chain_bytes (xs : List Verifier.Ext3)
    (h : xs.length = 5) : (OuterAdapter.encodedVec xs).length = 128 := by
  rw [OuterAdapter.encoded_vector_length, h]

/-- (7b) **AND A SHAPE-LEGAL GATE CELL AT THE ADOPTED `quotientDegree = 8` IS 248
CHAIN BYTES.** -/
theorem G2_shape_legal_gate_cell_is_248_chain_bytes (xs : List Verifier.Ext3)
    (h : xs.length = 10) : (OuterAdapter.encodedVec xs).length = 248 := by
  rw [OuterAdapter.encoded_vector_length, h]

/-- (7b) **WHILE GLP's OWN DECODER LAYOUT IS UNPREFIXED**: `24 * n` bytes for `n`
elements and nothing else.  `120 = 24 * 5` is therefore principled INSIDE that
convention -- the limb width times the adopted shape-legal log-round length
(`B2_accepted_log_rounds_have_length_five`) -- and it is the chain's eight-byte
prefix, not the boundary itself, that does not transport. -/
theorem G3_glp_layout_is_unprefixed (n : Nat) : (unitRepeat n).length = 24 * n :=
  unit_repeat_length n

end Audit.Wire3.TwoLaneMessages
