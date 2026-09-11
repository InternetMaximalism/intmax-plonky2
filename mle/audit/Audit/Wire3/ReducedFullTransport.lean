import Audit.Wire3.OuterLaneTransport
import Audit.Wire3.ConcreteChainThreading

/-!
# THE FULL `combinedBound` CONSTANT FOR THE REDUCED-HISTORY ADAPTIVE PROVER

## WHAT THIS MODULE PROVES, AND WHAT IT DOES NOT -- READ THIS FIRST

The adopted `OuterLaneTransport.reduced_outer_lane_bad_draw_probability_le` bounds,
for the REDUCED-HISTORY subclass of transcript-restricted adaptive provers, the
mass of the outer sumcheck lanes' round-agreement event by the adopted
`ChallengeUnionBound.outerTerm degreeBits quotientDegree` plus the chain's own
clash term.  Its HONESTY (iv) records exactly what is missing: the `tauTerm` (the
gate tau zero-check column) and the `alphaTerm` (the gate alpha row union) of the
adopted `ChallengeUnionBound.combinedBound` are NOT transported.

THIS MODULE TRANSPORTS THEM.  The headline
`reduced_full_bad_draw_probability_le` bounds the mass of the UNION of

* the adopted outer lane bad event at the reduced pairing, and
* the gate tau bad event at the derive digest, and
* the gate alpha bad event at the derive digest

by the WHOLE adopted `ChallengeUnionBound.combinedBound degreeBits quotientDegree
degreeBits constraints`, plus the one shared chain clash term
`(22 + 5 d) (22 + 5 d + 1) / 2 / |Block|`.  That clash term is SHARED, not
doubled: the no-clash events are nested (the adopted
`OuterLaneTransport.stage_no_clash_mono`), so conditioning the block-0 masses on
`noClash 22` and the round masses on `noClash (22 + 5 d)` costs ONE complement.

## WHAT THE TAU AND ALPHA BAD SETS DEPEND ON -- THE POINT THAT MAKES THIS WORK

The adopted `JointChallengeSpace.tauBadEvent d g` is
`tauEvent d (ZeroCheckSemantics.zeroCheckBadSet d g)`: its ONLY index is
`g : Nat -> Element`, the gate value table.  The adopted
`JointChallengeSpace.alphaBadEvent d rows coeffsOf` is
`coordEvent d Draw.gateAlpha (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)`:
its only indices are `rows` and `coeffsOf : Nat -> List Element`, the per-row gate
slot coefficients.  NEITHER MENTIONS A ROUND MESSAGE, A LANE, A STRATEGY OR A
TABLE.  Contrast the adopted `JointChallengeSpace.outerEvent`, which recurses
through `OuterRound.evaluate a r.message r.challenge` -- the run's REALIZED
challenge -- and is therefore RUN-RELATIVE; that is why the outer lanes need the
adopted `OuterLaneTransport` diagonal machinery at all.

So for a `OuterLaneTransport.ReducedStrategy` -- indeed for EVERY
`StrategyChainBound.Strategy` -- the tau and alpha targets are FIXED DATA: in every
theorem below `g`, `rows` and `coeffsOf` are bound OUTSIDE the oracle law, and no
theorem below lets the prover choose them after seeing a challenge.  That is why
the adopted `OuterLaneTransport.stage_triple_target_mass_le` is applied here AT A
CONSTANT TARGET (`fun _ => ...`), and why no diagonal argument is needed for these
two lanes.  `gate_alpha_bad_event_congr` and `gate_tau_bad_event_congr` state the
matching structural fact: both events are CYLINDERS on the block-0 coordinates --
two tables reading the same block-0 triples are both in or both out.

WHAT IS NOT CLAIMED.  That `g` and `coeffsOf` are the DEPLOYED run's tables is not
proved here and is not provable here: it is the adopted `CommitmentOrder` reading
that the twenty-two-frame prefix carries the preprocessed, witness and
norm-inverse roots (`only_two_domain_separators_after_the_last_root`), together
with that module's own open `CommittedTables` extraction join.  This module
INHERITS that reading unchanged; it does not strengthen it.

## WHAT IS PROVED

1. THE BLOCK-0 COUNTERS (section 1).  `deriveStage = 22` is the stage of the
   strategy chain at which the adopted `JointChallengeSpace.sourceBlock` value `0`
   lives -- the digest after the twenty-two relation-prefix frames of the adopted
   `CommitmentOrder.gateChallengeFrames`.  `alphaBase d = 9 + 3 d` and
   `tauBase d i = 12 + 3 d + 3 i` are the adopted
   `JointChallengeSpace.sourceCounter` of `Draw.gateAlpha` and `Draw.gateTau i`,
   and `alpha_base_is_source_counter` / `tau_base_is_source_counter` PROVE that
   identification rather than assert it.  `tau_counters_disjoint` is the
   separation the peel needs: block `n` and block `m` share no counter when
   `n < m`.
2. THE GATE ALPHA LANE (section 2).  `gate_alpha_no_clash_mass_le` is the adopted
   `OuterLaneTransport.stage_triple_target_mass_le` at the CONSTANT target
   `OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)`,
   whose mass-form constant is the adopted
   `OuterChallenge.uniformTupleProbability` of that set, hence the adopted
   `ChallengeUnionBound.alphaTerm` by the adopted `alpha_union_mass_bound`.  One
   scheduled draw, three counters.
3. THE GATE TAU COLUMN (section 3).  This is the technical work.  The adopted
   `ZeroCheckSemantics.zeroCheckBadSet d g` is NOT a product of per-coordinate
   sets -- it is an arbitrary set of `d`-tuples with a Schwartz--Zippel CARDINALITY
   bound -- so the whole `3 d`-counter block must be peeled JOINTLY.  `tauFibre`
   prescribes the first `n` tau triples, `tau_fibre_stable` shows the prescription
   already made is unmoved by a LATER block's answers (the adopted
   `OuterLaneTransport.stage_triple_reassign_same`: different counters at one
   digest are different queries), and `tau_fibre_card` peels the blocks one at a
   time with the adopted `OuterLaneTransport.stage_triple_fibre_card`, giving the
   EXACT count `|fibre| * |DigestTriple| ^ d = |noClash 22|`.  `tau_target_card`
   then sums over the target, `tau_target_mass_le` divides, and
   `gate_tau_no_clash_mass_le` composes with the adopted
   `ChallengeUnionBound.tau_product_mass_bound` to reach the adopted `tauTerm d`.
4. THE UNION (section 4).  `full_bad_draw_probability_le` unions the three masses
   on the no-clash event and adds ONE complement term, the adopted
   `StrategyChainBound.strategy_chain_clash_probability_le` at `22 + 5 d` stages.
   `full_bad_draw_probability_le_combined` reads the three constants off as the
   adopted `ChallengeUnionBound.combinedBound d q d constraints` at
   `rows = 2 ^ d`, which is the row count that bound uses.
5. THE HEADLINE AT THE REDUCED PAIRING (section 5).
   `reduced_full_bad_draw_probability_le` specialises section 4 to
   `OuterLaneTransport.strategyOfReduced` and the lanes IT determines
   (`logLaneOfReduced`, `gateLaneOfReduced`), for which the adopted
   `log_lane_of_reduced_message_is_realized` and its gate twin prove that round
   `r`'s outer bad set is built from the message THE PROVER CHOSE.
6. THE CLOSED INSTANCE (section 6).  `reduced_full_bound_at_thirteen` is the
   envelope's thirteen coupled rounds, `quotientDegree = 8`, `constraints = 123`,
   for the adopted non-trivial `OuterLaneTransport.previousChallengeMessage`, with
   neither the length budget nor the counter budget left as a hypothesis:

     `<= ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / |Block|`,

   and `reduced_full_bound_at_thirteen_lt_one` records that this is strictly below
   `1`.  READ HONESTY (v): THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR.
7. TWO FOLLOW-UPS TO THE ADOPTED SECTION 8 (section 7).  The adopted
   `OuterLaneTransport.previous_challenge_message_depends` exhibits its dependence
   at the one-element histories `[0]` and `[1]`, which no log coordinate ever sees:
   the adopted `outer_history_length` says a log coordinate's prefix has length
   `2 r`.  `previous_challenge_message_depends_at_realizable_history` moves the
   witness to the even length `2`.  `reduced_event_nonempty` is the non-vacuity
   corollary the adopted section 8 lacks: at a reduced prover whose round-`0` log
   cell is `[1]` and an honest round polynomial `[]`, ROUND `0`'s LOG TARGET IS
   INHABITED, by the adopted `lane_bad_nonempty_of_agreement` at the adopted
   `zeroDigestTriple`.  `reduced_event_nonempty_at_previous_challenge` exhibits
   such a prover inside the closed instance's own subclass.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)` -- one
independent uniform block per byte string of length at most `L`.  The fresh-query
lemma everything rests on, the adopted
`BirthdayClashBound.fresh_coordinate_probability`, is the DEFINING property of a
random table and is false, as a theorem, for any fixed hash.  Replacing the
deployed permutation by a table drawn from this law is an assumption with no proof
anywhere in this tree.

(ii) THE PROVER IS TRANSCRIPT-RESTRICTED AND REDUCED-HISTORY, AND GRINDING IS
EXCLUDED.  A `StrategyChainBound.Strategy` is handed the stage digests of its own
chain and the oracle's answers at the CHALLENGE inputs of those digests, and makes
no oracle queries of its own; a random-oracle-model Fiat--Shamir prover that hashes
candidate payloads itself and keeps the one whose digest collides -- GRINDING -- is
NOT covered.  The headline of section 5 restricts further, to the adopted
`OuterLaneTransport.ReducedStrategy`: a prover whose round message is a function of
the REDUCED round-challenge history alone.  Note also that for `strategicShape c s S`
the twenty-two prefix frames are the adopted `gateChallengeFrames c s`: the
commitment roots live in the statement `s` and are FIXED BEFORE the chain -- which
is exactly why `g` and `coeffsOf` are legitimately fixed data here, and also why
this prover cannot choose its commitments adaptively.  RAW-BLOCK-READING
STRATEGIES REMAIN OPEN, for exactly the reason the adopted `OuterLaneTransport` header's
`laneOfStrategy` paragraph gives.  Sections 2, 3 and 4 do hold for EVERY
`Strategy`, but their outer summand is then the adopted prefix-dependent lane
transport, not an adaptive union bound -- read the adopted HONESTY (iii).

(iii) THE LANES COVERED ARE THE OUTER SUMCHECK LANES AND THE TWO BLOCK-0 GATE
LANES, AND NOTHING ELSE.  The constant reached is EXACTLY the adopted
`ChallengeUnionBound.combinedBound`, term for term.  THE INDEX LANES ARE NOT
INCLUDED.  Their squeezes are read at the chain's stage `22 + 5 d + 8` digest (the
adopted `IndexLanesOracle`), and the adopted `IndexStageFinerSplit` bounds their
family by `2 * ChallengeUnionBound.tauTerm indexBits` FOR A FIXED PROOF RECORD.
COULD THAT `2 * tauTerm` BE ADDED HERE BY THE SAME ROUTE?  NOT BY THE
CONSTANT-TARGET ROUTE OF SECTIONS 2 AND 3, AND THIS MODULE DOES NOT ADD IT.  The
index bad sets are indexed by the run's USED CLAIMS, which the adopted
`InstalledIndexSampler.indexDigest` absorbs AFTER the coupled rounds; for an
adaptive prover those claims are functions of the round messages, hence of the
table, so the target is NOT fixed data and the constant-target lemma does not
apply.  What WOULD apply is the adopted
`OuterLaneTransport.stage_triple_target_mass_le` in its DIAGONAL form -- the target
may move with the table provided it is unmoved by the three answers it is tested
against, which is the statement that the used claims are fixed before the index
digest's own challenges are squeezed.  Proving that invariance, and a uniform
cardinality bound on the index bad set over the conditioning event, is exactly the
work NOT done below.  Treat "the index lanes cost another `2 * tauTerm`" as an
UNPROVED conjecture in this module's model.  The WHIR folding transcript and the
Merkle openings are not in `combinedBound` at all and are excluded a fortiori.

(iv) THE OUTER SUMMAND IS IMPORTED, NOT REPROVED.  Section 4 calls the adopted
`OuterLaneTransport.outer_no_clash_mass_le` and `round_terms_sum`.  Everything the
adopted module's HONESTY says about that summand -- in particular that a round's
bad set is the LANE's, and that the lane and the strategy are paired only for the
reduced subclass -- carries over verbatim.  Section 5 uses the adopted pairing
lemmas to make that summand an adaptive one; sections 2, 3 and 4 add nothing to
that pairing question, because their two events do not mention a lane at all.

(v) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  `combinedBound` covers
(a) the outer sumcheck round-agreement events, (b) the gate tau multilinear zero
check and (c) the gate alpha zero check.  It EXCLUDES the entire WHIR/Merkle
contribution -- proximity/list decoding, the query-repetition profile, and Merkle
collision resistance -- which is the DOMINANT term.  The deployed design point is
around a hundred bits.  Quoting the number of section 6 as the wire-v3 soundness
error would be wrong by roughly seventy bits.  The meaning of the per-round bad
sets remains the adopted `ConditionalSoundness` one -- GOOD-DRAW-CONDITIONAL, with
that module's assumption list untouched -- and nothing here instantiates it.

(vi) NO ADAPTIVE FIAT--SHAMIR SOUNDNESS IS CLAIMED.  What is bounded is the mass of
one named event defined directly on the oracle table.  The Fiat--Shamir half --
that the run's encoding draw is `JointChallengeSpace.jointProbability`-distributed
-- remains exactly as unformalized as the adopted
`JointChallengeSpace.DrawEncodesRun` header says, and nothing below is a claim that
Fiat--Shamir soundness has been established for an adaptive prover.  In particular
the events of sections 2 and 3 are this module's OWN table-level events; they are
NOT the adopted `RandomOracleSqueezes.runDrawEvent` at the adopted `jointBadEvent`,
and no theorem below identifies the two.  What IS identified is the CONSTANT: term
by term, it is the adopted `combinedBound`.

(vii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's OWN
definitions (`gateAlphaBadEvent`, `gateTauBadEvent`) and, through the generic lemmas
`Finset.mem_univ` / `Finset.card_univ` on `OracleTable`, in a few proofs; no tactic or
term below ever puts `Finset.univ` on `Element`, on `OuterChallenge.DigestTriple` or
on `ChallengeUnionBound.TripleTuple` in a position that can be reduced, and no
`Nat` arithmetic tactic below is ever shown a `Fintype.card` of any of them --
`peel_pow` does the only exponent bookkeeping and is stated over ABSTRACT naturals,
exactly as the adopted `OuterLaneTransport.peel_three` is and for the same reason.
`triple_tuple_card_as_triples` is proved from the adopted
`ChallengeUnionBound.product_space_card` and the adopted
`OuterChallenge.digest_tuple_cardinality` rather than by unfolding a `Fintype`
instance.  `open Classical in` is used for the declarations whose statements
mention membership in a `Finset (ChallengeUnionBound.TripleTuple d)`, exactly as
the adopted `ChallengeUnionBound.productEvent` does and for the same reason: the
decidability instance for that Pi type is not otherwise available here.  Every
digest-level membership goes through the adopted
`JointChallengeSpace.mem_tupleEvent` or `ChallengeUnionBound.mem_productEvent`;
memberships over the table space are manipulated through `Finset` equalities and
the adopted generic helpers `univ_filter_inter_subset` and
`subset_inter_union_compl`.  The closed instance of section 6 mentions
`ZeroCheckSemantics.zeroCheckBadSet 13 g` at a literal `13`, as the adopted
`RandomOracleSqueezes` closed instance mentions `jointBadEvent 13`; it is a
noncomputable `Finset` that no tactic below evaluates.
-/

namespace Audit.Wire3.ReducedFullTransport

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3.OuterLaneTransport

/-! ## 1. THE DERIVE DIGEST AND ITS BLOCK-0 COUNTERS -/

/-- **THE DERIVE DIGEST IS STAGE `22` OF THE STRATEGY CHAIN**: the state after the
twenty-two relation-prefix frames of the adopted
`CommitmentOrder.gateChallengeFrames`, which is where the adopted
`JointChallengeSpace.sourceBlock` value `0` lives. -/
def deriveStage : Nat := 22

/-- The gate alpha's counter, the adopted `JointChallengeSpace.sourceCounter` of
`Draw.gateAlpha`. -/
def alphaBase (d : Nat) : Nat := 9 + 3 * d

/-- Gate tau coordinate `i`'s counter, the adopted
`JointChallengeSpace.sourceCounter` of `Draw.gateTau i`. -/
def tauBase (d i : Nat) : Nat := 12 + 3 * d + 3 * i

theorem alpha_base_is_source_counter (d : Nat) :
    alphaBase d = JointChallengeSpace.sourceCounter d JointChallengeSpace.Draw.gateAlpha := rfl

theorem tau_base_is_source_counter (d : Nat) (i : Fin d) :
    tauBase d i.val
      = JointChallengeSpace.sourceCounter d (JointChallengeSpace.Draw.gateTau i) := rfl

/-- The counter budget: below this every block-0 counter of `combinedBound` is
below the adopted `Transcript.u64Limit`, so the adopted
`StrategyChainBound.challenge_sel_ne_of_counter` separates them. -/
theorem alpha_counter_lt (d : Nat) (hdu : 12 + 6 * d < Transcript.u64Limit) :
    alphaBase d + 2 < Transcript.u64Limit := by
  rw [alphaBase]
  omega

theorem tau_counter_lt (d i : Nat) (hi : i < d) (hdu : 12 + 6 * d < Transcript.u64Limit) :
    tauBase d i + 2 < Transcript.u64Limit := by
  rw [tauBase]
  omega

theorem tau_counter_mem_lt (d i c : Nat) (hi : i < d) (hc : c ∈ tripleCounters (tauBase d i))
    (hdu : 12 + 6 * d < Transcript.u64Limit) : c < Transcript.u64Limit := by
  rcases (mem_triple_counters (tauBase d i) c).mp hc with h | h | h <;>
    (rw [h, tauBase]; omega)

/-- (1) **TWO TAU BLOCKS SHARE NO COUNTER.**  The blocks are three apart, so block
`m`'s three counters miss block `n`'s whenever `n < m`.  This is what makes the
peel of section 3 legitimate. -/
theorem tau_counters_disjoint (d n m c : Nat) (hnm : n < m)
    (hc : c ∈ tripleCounters (tauBase d m)) : c ∉ tripleCounters (tauBase d n) := by
  intro hc2
  rcases (mem_triple_counters (tauBase d m) c).mp hc with h | h | h <;>
    rcases (mem_triple_counters (tauBase d n) c).mp hc2 with h2 | h2 | h2 <;>
    · rw [h, tauBase, tauBase] at h2
      omega

theorem thirteen_counter_budget : 12 + 6 * 13 < Transcript.u64Limit := by
  rw [Transcript.u64Limit]
  omega

/-- (1) **THE ONLY EXPONENT BOOKKEEPING, OVER ABSTRACT NATURALS.**  Stated so that
no tactic is ever shown a `Fintype.card` in a `Nat` arithmetic goal -- the adopted
`OuterLaneTransport.peel_three` is stated abstractly for the same reason. -/
theorem peel_pow (x y cb n : Nat) (h : x * cb = y) : x * cb ^ (n + 1) = y * cb ^ n := by
  rw [pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm, h]

/-! ## 2. THE GATE ALPHA LANE AT THE DERIVE DIGEST -/

/-- **THE GATE ALPHA BAD EVENT ON THE ORACLE TABLE.**  The digest triple the chain
reads at the DERIVE DIGEST from the gate alpha counter reduces into the adopted
`ChallengeUnionBound.alphaUnionBadSet`.  `rows` and `coeffsOf` are bound OUTSIDE
the oracle law: the adopted alpha family is indexed by the gate wire/constant
tables, which the adopted `CommitmentOrder` twenty-two-frame prefix has already
absorbed, so this target is FIXED DATA, not a function of the table or of the
prover's round messages. -/
noncomputable def gateAlphaBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d rows : Nat)
    (coeffsOf : Nat → List Element) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    stageTriple L hL e0 strat hb deriveStage (alphaBase d) T
      ∈ OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf))

theorem mem_gate_alpha_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d rows : Nat)
    (coeffsOf : Nat → List Element) (T : OracleTable (boundedQueries L)) :
    T ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf ↔
      OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb deriveStage (alphaBase d) T)
        ∈ ChallengeUnionBound.alphaUnionBadSet rows coeffsOf := by
  rw [gateAlphaBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact JointChallengeSpace.mem_tupleEvent _ _

/-- (2) **IT IS A CYLINDER ON THE BLOCK-0 COORDINATES.**  Two tables that read the
same gate alpha triple at the derive digest are both in the event or both out of
it: the event looks at nothing else, and in particular at no round message. -/
theorem gate_alpha_bad_event_congr (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d rows : Nat)
    (coeffsOf : Nat → List Element) (T1 T2 : OracleTable (boundedQueries L))
    (h : stageTriple L hL e0 strat hb deriveStage (alphaBase d) T1
      = stageTriple L hL e0 strat hb deriveStage (alphaBase d) T2) :
    (T1 ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf ↔
      T2 ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf) := by
  rw [mem_gate_alpha_bad_event, mem_gate_alpha_bad_event, h]

/-- (2) **THE GATE ALPHA MASS, CONDITIONED ON THE CHAIN'S NO-CLASH EVENT.**  The
adopted `OuterLaneTransport.stage_triple_target_mass_le` at a CONSTANT target -- no
diagonal is needed, because the alpha bad set is fixed data -- composed with the
adopted `ChallengeUnionBound.alpha_union_mass_bound`.  The constant is the adopted
`alphaTerm`, exactly the summand `combinedBound` carries. -/
theorem gate_alpha_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d rows constraints : Nat)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL e0 strat hb deriveStage).filter (fun T =>
          stageTriple L hL e0 strat hb deriveStage (alphaBase d) T
            ∈ OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)))
      ≤ ChallengeUnionBound.alphaTerm rows constraints := by
  have hmass := stage_triple_target_mass_le L hL e0 strat hb deriveStage (alphaBase d)
    (alpha_counter_lt d hdu) (stageNoClash L hL e0 strat hb deriveStage)
    (stage_stable_no_clash L hL e0 strat hb deriveStage (tripleCounters (alphaBase d)))
    (fun _ => OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf))
    (fun _ _ _ _ _ => rfl)
    (OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)).card
    (fun _ _ => le_refl _)
  have hdef : (((OuterChallenge.tupleEvent
        (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)).card : ℚ)
      / (Fintype.card OuterChallenge.DigestTriple : ℚ))
      = OuterChallenge.uniformTupleProbability
          (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf) := rfl
  rw [hdef] at hmass
  exact hmass.trans
    (ChallengeUnionBound.alpha_union_mass_bound rows constraints coeffsOf hclen)

/-! ## 3. THE GATE TAU COLUMN AT THE DERIVE DIGEST -/

/-- **THE GATE TAU COLUMN THE CHAIN READS AT THE DERIVE DIGEST**: coordinate `i` is
the digest triple at the derive digest's counters `12 + 3 d + 3 i, +1, +2`, the
adopted `JointChallengeSpace.sourceCounter` block of `Draw.gateTau i`. -/
def tauRead (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) :
    ChallengeUnionBound.TripleTuple d :=
  fun i => stageTriple L hL e0 strat hb deriveStage (tauBase d i.val) T

/-- The prescribed-prefix fibre of the no-clash event: the tables whose first `n`
tau coordinates take the prescribed values. -/
noncomputable def tauFibre (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (t : Nat → OuterChallenge.DigestTriple) :
    Nat → Finset (OracleTable (boundedQueries L))
  | 0 => stageNoClash L hL e0 strat hb deriveStage
  | n + 1 =>
      (tauFibre L hL e0 strat hb d t n).filter
        (fun T => stageTriple L hL e0 strat hb deriveStage (tauBase d n) T = t n)

theorem tau_fibre_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (t : Nat → OuterChallenge.DigestTriple) :
    tauFibre L hL e0 strat hb d t 0 = stageNoClash L hL e0 strat hb deriveStage := rfl

theorem tau_fibre_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (t : Nat → OuterChallenge.DigestTriple) (n : Nat) :
    tauFibre L hL e0 strat hb d t (n + 1)
      = (tauFibre L hL e0 strat hb d t n).filter
          (fun T => stageTriple L hL e0 strat hb deriveStage (tauBase d n) T = t n) := rfl

/-- (3) Membership in the fibre, spelled out. -/
theorem mem_tau_fibre (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (t : Nat → OuterChallenge.DigestTriple) :
    ∀ (n : Nat) (T : OracleTable (boundedQueries L)),
      T ∈ tauFibre L hL e0 strat hb d t n ↔
        (T ∈ stageNoClash L hL e0 strat hb deriveStage ∧
          ∀ i, i < n → stageTriple L hL e0 strat hb deriveStage (tauBase d i) T = t i) := by
  intro n
  induction n with
  | zero =>
      intro T
      exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, fun h => h.1⟩
  | succ n2 ih =>
      intro T
      rw [tau_fibre_succ, Finset.mem_filter, ih T]
      constructor
      · rintro ⟨⟨hT, hall⟩, hlast⟩
        refine ⟨hT, fun i hi => ?_⟩
        rcases Nat.lt_or_ge i n2 with h | h
        · exact hall i h
        · have hie : i = n2 := by omega
          rw [hie]
          exact hlast
      · rintro ⟨hT, hall⟩
        exact ⟨⟨hT, fun i hi => hall i (by omega)⟩, hall n2 (by omega)⟩

/-- (3) **THE FIBRE IS STAGE-STABLE AT EVERY LATER TAU BLOCK.**  The prescriptions
already made are at counters `12 + 3 d + 3 i` with `i < m`, and the three counters
of block `m` are different queries at the same digest, so overwriting them does not
change which tables the earlier prescriptions allow (the adopted
`OuterLaneTransport.stage_triple_reassign_same`). -/
theorem tau_fibre_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (t : Nat → OuterChallenge.DigestTriple)
    (hdu : 12 + 6 * d < Transcript.u64Limit) :
    ∀ n m : Nat, n ≤ m → m < d →
      StageStable L hL e0 strat hb deriveStage (tripleCounters (tauBase d m))
        (tauFibre L hL e0 strat hb d t n) := by
  intro n
  induction n with
  | zero =>
      intro m _ _
      exact stage_stable_no_clash L hL e0 strat hb deriveStage (tripleCounters (tauBase d m))
  | succ n2 ih =>
      intro m hnm hmd
      have hprev := ih m (by omega) hmd
      rw [tau_fibre_succ]
      refine stage_stable_filter L hL e0 strat hb deriveStage (tripleCounters (tauBase d m))
        (tauFibre L hL e0 strat hb d t n2) hprev
        (fun T => stageTriple L hL e0 strat hb deriveStage (tauBase d n2) T = t n2)
        (fun T hT c hc b => ?_)
      show stageTriple L hL e0 strat hb deriveStage (tauBase d n2)
            (reassign T (challengeSel L hL e0 strat hb deriveStage c T) b) = t n2
        ↔ stageTriple L hL e0 strat hb deriveStage (tauBase d n2) T = t n2
      rw [stage_triple_reassign_same L hL e0 strat hb deriveStage (tauBase d n2) c
        (tau_counter_mem_lt d m c hmd hc hdu)
        (tau_counter_lt d n2 (by omega) hdu)
        (tau_counters_disjoint d n2 m c (by omega) hc) T (hprev.1 T hT) b]

/-- (3) **THE JOINT FIBRE COUNT OVER THE WHOLE TAU COLUMN.**  Each prescription of
the `d` tau triples is met by exactly a `1 / |DigestTriple| ^ d` share of the
no-clash event: `d` applications of the adopted
`OuterLaneTransport.stage_triple_fibre_card`, one per scheduled draw, with
`peel_pow` doing the exponent bookkeeping over abstract naturals. -/
theorem tau_fibre_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (t : Nat → OuterChallenge.DigestTriple)
    (hdu : 12 + 6 * d < Transcript.u64Limit) :
    ∀ n : Nat, n ≤ d →
      (tauFibre L hL e0 strat hb d t n).card * Fintype.card OuterChallenge.DigestTriple ^ n
        = (stageNoClash L hL e0 strat hb deriveStage).card := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [tau_fibre_zero, pow_zero, Nat.mul_one]
  | succ n2 ih =>
      intro hn
      have hstep : (tauFibre L hL e0 strat hb d t (n2 + 1)).card
            * Fintype.card OuterChallenge.DigestTriple
          = (tauFibre L hL e0 strat hb d t n2).card :=
        stage_triple_fibre_card L hL e0 strat hb deriveStage (tauBase d n2)
          (tau_counter_lt d n2 (by omega) hdu) (tauFibre L hL e0 strat hb d t n2)
          (tau_fibre_stable L hL e0 strat hb d t hdu n2 n2 (le_refl n2) (by omega)) (t n2)
      exact (peel_pow _ _ _ n2 hstep).trans (ih (by omega))

/-- A total prescription extending one tau tuple; the adopted
`OuterLaneTransport.zeroDigestTriple` fills the unused indices. -/
def tauExtend (d : Nat) (t : ChallengeUnionBound.TripleTuple d) :
    Nat → OuterChallenge.DigestTriple :=
  fun i => if h : i < d then t ⟨i, h⟩ else zeroDigestTriple

theorem tau_extend_apply (d : Nat) (t : ChallengeUnionBound.TripleTuple d) (i : Nat) (h : i < d) :
    tauExtend d t i = t ⟨i, h⟩ := by
  rw [tauExtend, dif_pos h]

/-- (3) The whole-column fibre is exactly the set of no-clash tables that read `t`. -/
theorem tau_fibre_at_extend (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (t : ChallengeUnionBound.TripleTuple d)
    (T : OracleTable (boundedQueries L)) :
    T ∈ tauFibre L hL e0 strat hb d (tauExtend d t) d ↔
      (T ∈ stageNoClash L hL e0 strat hb deriveStage ∧ tauRead L hL e0 strat hb d T = t) := by
  rw [mem_tau_fibre]
  constructor
  · rintro ⟨hT, hall⟩
    refine ⟨hT, ?_⟩
    funext i
    show stageTriple L hL e0 strat hb deriveStage (tauBase d i.val) T = t i
    rw [hall i.val i.isLt, tau_extend_apply d t i.val i.isLt]
  · rintro ⟨hT, hread⟩
    refine ⟨hT, fun i hi => ?_⟩
    rw [tau_extend_apply d t i hi, ← hread]
    rfl

open Classical in
/-- (3) **THE TARGET COUNT OVER THE TAU COLUMN.**  For a set `S` of tau tuples --
fixed data, bound outside the law -- exactly `|S|` fibres are caught. -/
theorem tau_target_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (S : Finset (ChallengeUnionBound.TripleTuple d)) :
    ((stageNoClash L hL e0 strat hb deriveStage).filter
          (fun T => tauRead L hL e0 strat hb d T ∈ S)).card
        * Fintype.card OuterChallenge.DigestTriple ^ d
      = S.card * (stageNoClash L hL e0 strat hb deriveStage).card := by
  have hfib : ((stageNoClash L hL e0 strat hb deriveStage).filter
        (fun T => tauRead L hL e0 strat hb d T ∈ S)).card
      = ∑ t in S, (((stageNoClash L hL e0 strat hb deriveStage).filter
          (fun T => tauRead L hL e0 strat hb d T ∈ S)).filter
            (fun T => tauRead L hL e0 strat hb d T = t)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => (Finset.mem_filter.mp hx).2)
  have key : ∀ t ∈ S,
      (((stageNoClash L hL e0 strat hb deriveStage).filter
          (fun T => tauRead L hL e0 strat hb d T ∈ S)).filter
            (fun T => tauRead L hL e0 strat hb d T = t)).card
          * Fintype.card OuterChallenge.DigestTriple ^ d
        = (stageNoClash L hL e0 strat hb deriveStage).card := by
    intro t ht
    have hset : ((stageNoClash L hL e0 strat hb deriveStage).filter
          (fun T => tauRead L hL e0 strat hb d T ∈ S)).filter
            (fun T => tauRead L hL e0 strat hb d T = t)
        = tauFibre L hL e0 strat hb d (tauExtend d t) d := by
      apply Finset.ext
      intro T
      rw [tau_fibre_at_extend, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hT, -⟩, hEq⟩
        exact ⟨hT, hEq⟩
      · rintro ⟨hT, hEq⟩
        exact ⟨⟨hT, hEq ▸ ht⟩, hEq⟩
    rw [hset]
    exact tau_fibre_card L hL e0 strat hb d (tauExtend d t) hdu d (le_refl d)
  rw [hfib, Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

/-- (3) The tau column's alphabet, symbolically, from the adopted
`ChallengeUnionBound.product_space_card` and the adopted
`OuterChallenge.digest_tuple_cardinality`.  No `Fintype` instance is unfolded and
no cardinality is evaluated. -/
theorem triple_tuple_card_as_triples (d : Nat) :
    Fintype.card (ChallengeUnionBound.TripleTuple d)
      = Fintype.card OuterChallenge.DigestTriple ^ d := by
  rw [ChallengeUnionBound.product_space_card, OuterChallenge.digest_tuple_cardinality]

open Classical in
/-- (3) **THE TARGET MASS OVER THE TAU COLUMN.** -/
theorem tau_target_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (S : Finset (ChallengeUnionBound.TripleTuple d)) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL e0 strat hb deriveStage).filter
          (fun T => tauRead L hL e0 strat hb d T ∈ S))
      ≤ (S.card : ℚ) / (Fintype.card (ChallengeUnionBound.TripleTuple d) : ℚ) := by
  have hcard := tau_target_card L hL e0 strat hb d hdu S
  have hAle : (stageNoClash L hL e0 strat hb deriveStage).card
      ≤ Fintype.card (OracleTable (boundedQueries L)) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_univ _
  have hnat : ((stageNoClash L hL e0 strat hb deriveStage).filter
        (fun T => tauRead L hL e0 strat hb d T ∈ S)).card
      * Fintype.card OuterChallenge.DigestTriple ^ d
      ≤ S.card * Fintype.card (OracleTable (boundedQueries L)) := by
    rw [hcard]
    exact Nat.mul_le_mul_left _ hAle
  have hQ : (((stageNoClash L hL e0 strat hb deriveStage).filter
        (fun T => tauRead L hL e0 strat hb d T ∈ S)).card : ℚ)
      * ((Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d)
      ≤ (S.card : ℚ) * (Fintype.card (OracleTable (boundedQueries L)) : ℚ) := by
    exact_mod_cast hnat
  have hD : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d := by
    have h1 : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
      exact_mod_cast JointChallengeSpace.digest_triple_card_pos
    exact pow_pos h1 d
  rw [triple_tuple_card_as_triples, Nat.cast_pow, oracleProbability,
    div_le_div_iff (oracle_card_cast_pos (boundedQueries L)) hD]
  exact hQ

open Classical in
/-- **THE GATE TAU BAD EVENT ON THE ORACLE TABLE.**  The tau column the chain reads
at the DERIVE DIGEST reduces into the adopted
`ZeroCheckSemantics.zeroCheckBadSet`.  `g` is bound OUTSIDE the oracle law: the
adopted tau family is indexed by the gate value table, absorbed in the adopted
`CommitmentOrder` twenty-two-frame prefix, so this target too is FIXED DATA. -/
noncomputable def gateTauBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (g : Nat → Element) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    tauRead L hL e0 strat hb d T ∈ ChallengeUnionBound.productEvent d
      (ZeroCheckSemantics.zeroCheckBadSet d g))

open Classical in
theorem mem_gate_tau_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (g : Nat → Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ gateTauBadEvent L hL e0 strat hb d g ↔
      ChallengeUnionBound.reduceTuple d (tauRead L hL e0 strat hb d T)
        ∈ ZeroCheckSemantics.zeroCheckBadSet d g := by
  rw [gateTauBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact ChallengeUnionBound.mem_productEvent _ _ _

open Classical in
/-- (3) **IT IS A CYLINDER ON THE BLOCK-0 COORDINATES.** -/
theorem gate_tau_bad_event_congr (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (g : Nat → Element)
    (T1 T2 : OracleTable (boundedQueries L))
    (h : tauRead L hL e0 strat hb d T1 = tauRead L hL e0 strat hb d T2) :
    (T1 ∈ gateTauBadEvent L hL e0 strat hb d g ↔ T2 ∈ gateTauBadEvent L hL e0 strat hb d g) := by
  rw [mem_gate_tau_bad_event, mem_gate_tau_bad_event, h]

open Classical in
/-- (3) **THE GATE TAU MASS, CONDITIONED ON THE CHAIN'S NO-CLASH EVENT.**  The
constant is the adopted `ChallengeUnionBound.tauTerm`, exactly the summand
`combinedBound` carries. -/
theorem gate_tau_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (g : Nat → Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL e0 strat hb deriveStage).filter (fun T =>
          tauRead L hL e0 strat hb d T ∈ ChallengeUnionBound.productEvent d
            (ZeroCheckSemantics.zeroCheckBadSet d g)))
      ≤ ChallengeUnionBound.tauTerm d := by
  have hmass := tau_target_mass_le L hL e0 strat hb d hdu
    (ChallengeUnionBound.productEvent d (ZeroCheckSemantics.zeroCheckBadSet d g))
  have hdef : (((ChallengeUnionBound.productEvent d
        (ZeroCheckSemantics.zeroCheckBadSet d g)).card : ℚ)
      / (Fintype.card (ChallengeUnionBound.TripleTuple d) : ℚ))
      = ChallengeUnionBound.uniformProductProbability d
          (ZeroCheckSemantics.zeroCheckBadSet d g) := rfl
  rw [hdef] at hmass
  exact hmass.trans (ChallengeUnionBound.tau_product_mass_bound d g)

/-! ## 4. THE UNION, AND THE ONE SHARED CLASH TERM -/

/-- **THE FULL BAD EVENT ON THE ORACLE TABLE**: some coupled round of either OUTER
lane agrees, OR the gate tau column lands in the adopted zero-check bad set, OR the
gate alpha lands in the adopted row union.  The association is the adopted
`JointChallengeSpace.jointBadEvent`'s. -/
noncomputable def fullBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (d rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  (outerLaneBadEvent L hL e0 strat hb logLane gateLane d
      ∪ gateTauBadEvent L hL e0 strat hb d g)
    ∪ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf

/-- (4) **IT REALLY IS A DISJUNCTION**, exactly as the adopted
`JointChallengeSpace.mem_jointBadEvent` is on the ideal space. -/
theorem mem_full_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (d rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ fullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf ↔
      (T ∈ outerLaneBadEvent L hL e0 strat hb logLane gateLane d ∨
        T ∈ gateTauBadEvent L hL e0 strat hb d g ∨
        T ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf) := by
  simp only [fullBadEvent, Finset.mem_union, or_assoc]

open Classical in
/-- (4) **THE FULL BAD-DRAW BOUND, FOR EVERY STRATEGY AND EVERY PAIR OF LANES.**
The three masses are conditioned on nested no-clash events -- `22 + 5 d` for the
rounds, `22` for the block-0 squeezes, and the adopted
`OuterLaneTransport.stage_no_clash_mono` puts the former inside the latter -- so
ONE complement term pays for all three.

READ HONESTY (ii) AND (iv): the outer summand here is the adopted PREFIX-DEPENDENT
lane transport, which becomes an adaptive union bound only at the reduced pairing
of section 5.  The tau and alpha summands are adaptive already, for the reason in
the header: their bad sets do not depend on a round message. -/
theorem full_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (d q rows constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (fullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf)
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hnest : stageNoClash L hL e0 strat hb (22 + 5 * d)
      ⊆ stageNoClash L hL e0 strat hb deriveStage :=
    stage_no_clash_mono L hL e0 strat hb deriveStage (22 + 5 * d) (by rw [deriveStage]; omega)
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl (fullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf)
      (stageNoClash L hL e0 strat hb (22 + 5 * d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (fullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
  have hsplit : fullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
        ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)
      = ((outerLaneBadEvent L hL e0 strat hb logLane gateLane d
            ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
          ∪ (gateTauBadEvent L hL e0 strat hb d g
            ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)))
        ∪ (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
            ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)) := by
    rw [fullBadEvent, Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
  have hu2 : oracleProbability (boundedQueries L)
        (fullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
          ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
      ≤ oracleProbability (boundedQueries L)
          ((outerLaneBadEvent L hL e0 strat hb logLane gateLane d
              ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
            ∪ (gateTauBadEvent L hL e0 strat hb d g
              ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)))
        + oracleProbability (boundedQueries L)
            (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
              ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)) := by
    rw [hsplit]
    exact oracle_probability_union_le (boundedQueries L) _ _
  have hu3 := oracle_probability_union_le (boundedQueries L)
    (outerLaneBadEvent L hL e0 strat hb logLane gateLane d
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    (gateTauBadEvent L hL e0 strat hb d g ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
  have houter := outer_no_clash_mass_le L hL e0 strat hb logLane gateLane 5 (q + 2)
    hlog hgate (22 + 5 * d) d (fun r hr => round_stage_le r d hr)
  rw [round_terms_sum d q] at houter
  have htausub : gateTauBadEvent L hL e0 strat hb d g
        ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)
      ⊆ (stageNoClash L hL e0 strat hb deriveStage).filter (fun T =>
          tauRead L hL e0 strat hb d T ∈ ChallengeUnionBound.productEvent d
            (ZeroCheckSemantics.zeroCheckBadSet d g)) := by
    rw [gateTauBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have htau : oracleProbability (boundedQueries L)
      (gateTauBadEvent L hL e0 strat hb d g ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
      ≤ ChallengeUnionBound.tauTerm d :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ htausub)
      (gate_tau_no_clash_mass_le L hL e0 strat hb d g hdu)
  have halphasub : gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
        ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)
      ⊆ (stageNoClash L hL e0 strat hb deriveStage).filter (fun T =>
          stageTriple L hL e0 strat hb deriveStage (alphaBase d) T
            ∈ OuterChallenge.tupleEvent
                (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)) := by
    rw [gateAlphaBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have halpha : oracleProbability (boundedQueries L)
      (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
        ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
      ≤ ChallengeUnionBound.alphaTerm rows constraints :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ halphasub)
      (gate_alpha_no_clash_mass_le L hL e0 strat hb d rows constraints coeffsOf hdu hclen)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
      ≤ ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL e0 strat hb (22 + 5 * d)
  linarith

/-- (4) **THE SAME, WITH THE CONSTANT READ OFF AS THE ADOPTED `combinedBound`.**  At
`rows = 2 ^ degreeBits` -- the row count the adopted bound uses -- the three terms
ARE `ChallengeUnionBound.combinedBound degreeBits quotientDegree degreeBits
constraints`, term for term, with nothing added and nothing dropped. -/
theorem full_bad_draw_probability_le_combined (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (d q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (fullBadEvent L hL e0 strat hb logLane gateLane d (2 ^ d) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := full_bad_draw_probability_le L hL e0 strat hb logLane gateLane d q (2 ^ d)
    constraints g coeffsOf hdu hlog hgate hclen
  rw [ChallengeUnionBound.combinedBound]
  exact h

/-! ## 5. THE HEADLINE AT THE REDUCED PAIRING -/

/-- (5) **THE FULL `combinedBound` CONSTANT FOR A REDUCED-HISTORY ADAPTIVE PROVER.**
The strategy is the adopted `OuterLaneTransport.strategyOfReduced c s R` and the
outer lanes are ITS OWN -- the adopted `log_lane_of_reduced_message_is_realized` and
its gate twin prove that round `r`'s outer bad set is built from the message THE
PROVER CHOSE after seeing the reduced challenges of the earlier rounds.  The gate
tau and gate alpha bad sets are FIXED DATA (see the header), so their masses are
transported at a CONSTANT target.  The constant is the WHOLE adopted
`ChallengeUnionBound.combinedBound d q d constraints`, plus ONE chain clash term.

READ HONESTY (iii): THE INDEX LANES ARE NOT INCLUDED, and (v): THIS IS NOT THE
SYSTEM'S SOUNDNESS ERROR. -/
theorem reduced_full_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (trlog trgate : List Element → List Element) (a1 b1 a2 b2 : Element)
    (hb : StrategyBounded L (strategyOfReduced c s R)) (d q constraints : Nat)
    (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hRlog : ∀ (r : Nat) (xs : List Element), (R r xs).1.length ≤ 5)
    (hRgate : ∀ (r : Nat) (xs : List Element), (R r xs).2.length ≤ q + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (fullBadEvent L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
          (logLaneOfReduced R trlog a1 b1) (gateLaneOfReduced R trgate a2 b2)
          d (2 ^ d) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  full_bad_draw_probability_le_combined L hL OuterInitial.zeroDigest
    (strategyOfReduced c s R) hb (logLaneOfReduced R trlog a1 b1)
    (gateLaneOfReduced R trgate a2 b2) d q constraints g coeffsOf hdu
    (log_lane_of_reduced_bounded R trlog a1 b1 5 hRlog htrlog)
    (gate_lane_of_reduced_bounded R trgate a2 b2 (q + 2) hRgate htrgate) hclen

/-! ## 6. THE CLOSED INSTANCE -/

/-- (6) **THE CLOSED INSTANCE AT THE ENVELOPE'S THIRTEEN COUPLED ROUNDS**, for the
adopted non-trivial `OuterLaneTransport.previousChallengeMessage`: neither the
length budget nor the counter budget is left as a hypothesis, and the constant is
the adopted `ChallengeUnionBound.combinedBound 13 8 13 123` plus the adopted
`3828 / |Block|`.  The two running claims and the honest round messages are free
parameters, as in the adopted `ConditionalSoundness` model.  READ HONESTY (v). -/
theorem reduced_full_bound_at_thirteen (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage)
    (trlog trgate : List Element → List Element) (a1 b1 a2 b2 : Element)
    (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (fullBadEvent L (Nat.le_trans (by omega) hLq) OuterInitial.zeroDigest
          (strategyOfReduced c s (previousChallengeMessage m))
          (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
            (previous_challenge_message_log_length m 5 hmlog)
            (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
          (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
          (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2)
          13 (2 ^ 13) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) := by
  have h := reduced_full_bad_draw_probability_le L (Nat.le_trans (by omega) hLq) c s
    (previousChallengeMessage m) trlog trgate a1 b1 a2 b2
    (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
      (previous_challenge_message_log_length m 5 hmlog)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
    13 8 123 g coeffsOf thirteen_counter_budget
    (previous_challenge_message_log_length m 5 hmlog)
    (previous_challenge_message_gate_length m (8 + 2) hmgate) htrlog htrgate hclen
  have harith : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  rw [harith] at h
  exact h

/-- (6) **AND THE CLOSED CONSTANT IS STRICTLY BELOW `1`.**  The adopted
`ChallengeUnionBound.combined_bound_at_extremes_numeric` puts the three-term
envelope at most `2 ^ (-172)` and the adopted
`ConcreteChainThreading.birthday_term_le_two_pow_neg` puts the chain term at most
`2 ^ (-244)`.  `Fintype.card Block` is never evaluated: it enters only through the
adopted lemma.  READ HONESTY (v): this is NOT the protocol's soundness error. -/
theorem reduced_full_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) < 1 := by
  have h1 : ChallengeUnionBound.combinedBound 13 8 13 123 ≤ (1 : ℚ) / 2 ^ 172 :=
    ChallengeUnionBound.combined_bound_at_extremes_numeric
  have h2 : (3828 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 244 :=
    ConcreteChainThreading.birthday_term_le_two_pow_neg
  have h3 : (1 : ℚ) / 2 ^ 172 + 1 / 2 ^ 244 < 1 := by norm_num
  linarith

/-! ## 7. TWO FOLLOW-UPS TO THE ADOPTED SECTION 8 -/

/-- (7) The length a LOG coordinate's reduced prefix actually has, restating the
adopted `OuterLaneTransport.outer_history_length`: `2 r`, hence EVEN.  The adopted
`previous_challenge_message_depends` exhibits its witness at the one-element lists
`[0]` and `[1]`, which are therefore not prefixes any log coordinate is handed. -/
theorem realizable_history_length_even (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L))
    (r : Nat) : (outerHistory L hL e0 strat hb T r).length = 2 * r :=
  outer_history_length L hL e0 strat hb T r

/-- (7) **THE DEPENDENCE WITNESS, MOVED TO A REALIZABLE LENGTH.**  Two histories of
the EVEN length `2` -- the length the adopted `outer_history_length` gives a log
coordinate at round `1` -- that differ only in the adopted oldest-first head give
different messages.  So the adopted `previousChallengeMessage m` is non-constant
already on the lists a log coordinate is actually handed, not merely on the
odd-length lists of the adopted witness. -/
theorem previous_challenge_message_depends_at_realizable_history
    (m : Verifier.CoupledMessage) (hm : m.2 ≠ []) (r : Nat) (y : Element) :
    ([(0 : Element), y].length = 2 * 1) ∧
      previousChallengeMessage m r [(0 : Element), y]
        ≠ previousChallengeMessage m r [(1 : Element), y] := by
  refine ⟨rfl, ?_⟩
  intro h
  have h2 : (if ([(0 : Element), y].headD 0) = 0 then [] else m.2)
      = (if ([(1 : Element), y].headD 0) = 0 then [] else m.2) :=
    congrArg Prod.snd h
  have hz0 : ([(0 : Element), y].headD 0) = 0 := rfl
  have hz1 : ¬ (([(1 : Element), y].headD 0) = 0) := by
    intro hz
    exact zero_ne_one (show (0 : Element) = 1 from hz.symm)
  rw [if_pos hz0, if_neg hz1] at h2
  exact hm h2.symm

/-- (7) **A REDUCED PROVER'S ROUND-`0` LOG TARGET IS INHABITED.**  The adopted
section 8 proves a bound but exhibits no inhabited bad set at the reduced pairing;
this closes that gap.  The lane is the prover's OWN
(`OuterLaneTransport.logLaneOfReduced`), its round-`0` message is the prover's own
round-`0` log cell, and with that cell `[1]` against the honest `[]` and the two
running claims `1` against `0` the adopted `ConditionalSoundness.roundBadSet` does
not take its diagonal branch and the two adopted round polynomials MEET AT THE
FIELD ZERO -- the adopted `zeroDigestTriple` reduces to `0`.  So the per-round bound
of the adopted section 4 is not, here, a bound on an empty set. -/
theorem reduced_event_nonempty (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (trlog : List Element → List Element)
    (hb : StrategyBounded L (strategyOfReduced c s R)) (gateLane : Lane)
    (T : OracleTable (boundedQueries L))
    (hR : (R 0 []).1 = [Norm.one]) (htr : trlog [] = []) :
    (logTarget L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
      (logLaneOfReduced R trlog (1 : Element) (0 : Element)) gateLane 0 T).Nonempty := by
  have hmsg : (logLaneOfReduced R trlog (1 : Element) (0 : Element)).message []
      = separatedLane.message [] := by
    show List.map OuterRound.lift (R 0 ([] : List Element)).1 = [(1 : Element)]
    rw [hR]
    rfl
  have hagree : (OuterRound.polynomial
        (logLaneOfReduced R trlog (1 : Element) (0 : Element)).claim
        ((logLaneOfReduced R trlog (1 : Element) (0 : Element)).message [])).eval
          (OuterChallenge.reduceTriple zeroDigestTriple)
      = (OuterRound.polynomial
        (logLaneOfReduced R trlog (1 : Element) (0 : Element)).truthClaim
        ((logLaneOfReduced R trlog (1 : Element) (0 : Element)).truth [])).eval
          (OuterChallenge.reduceTriple zeroDigestTriple) := by
    show (OuterRound.polynomial (1 : Element)
        ((logLaneOfReduced R trlog (1 : Element) (0 : Element)).message [])).eval
          (OuterChallenge.reduceTriple zeroDigestTriple)
      = (OuterRound.polynomial (0 : Element) (trlog [])).eval
          (OuterChallenge.reduceTriple zeroDigestTriple)
    rw [hmsg, htr]
    exact separated_lane_agrees_at_zero
  exact lane_bad_nonempty_of_agreement (logLaneOfReduced R trlog (1 : Element) (0 : Element))
    zeroDigestTriple rfl (fun h => zero_ne_one (show (0 : Element) = 1 from h.symm)) hagree

/-- (7) **AND SUCH A PROVER LIVES IN THE CLOSED INSTANCE'S OWN SUBCLASS.**  The
adopted `previousChallengeMessage` with log cell `[Norm.one]` is a reduced-history
prover meeting section 6's log length budget whose round-`0` log target is
inhabited, so the closed instance of section 6 is not a bound on an empty outer
event. -/
theorem reduced_event_nonempty_at_previous_challenge (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (mgate : List Verifier.Ext3)
    (trlog : List Element → List Element)
    (hb : StrategyBounded L (strategyOfReduced c s
      (previousChallengeMessage ([Norm.one], mgate)))) (gateLane : Lane)
    (T : OracleTable (boundedQueries L)) (htr : trlog [] = []) :
    (([Norm.one] : List Verifier.Ext3).length ≤ 5) ∧
      (logTarget L hL OuterInitial.zeroDigest
        (strategyOfReduced c s (previousChallengeMessage ([Norm.one], mgate))) hb
        (logLaneOfReduced (previousChallengeMessage ([Norm.one], mgate)) trlog
          (1 : Element) (0 : Element)) gateLane 0 T).Nonempty := by
  refine ⟨?_, ?_⟩
  · show (1 : Nat) ≤ 5
    omega
  · exact reduced_event_nonempty L hL c s (previousChallengeMessage ([Norm.one], mgate)) trlog hb
      gateLane T rfl htr

/-! ## 9. Identifications the review asked to be theorems, not prose -/

/-- **STAGE `22` OF THE REDUCED PROVER'S CHAIN IS THE ADOPTED DERIVE DIGEST.**  The
adopted `StrategyChainBound.strategic_prover_chain_base` at round `0`, through
`OuterLaneTransport.reduced_round_causal`. -/
theorem derive_stage_is_derive_digest (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy)
    (hb : StrategyBounded L (strategyOfReduced c s R)) (T : OracleTable (boundedQueries L)) :
    strategyFrameState L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb deriveStage T
      = (OuterInitial.derive (hashOf (boundedQueries L) T) c s).state.digest :=
  strategic_prover_chain_base L hL c s (reducedRoundMessage R) hb (reduced_round_causal R) 0 T

open Classical in
/-- **THE GATE-TAU EVENT IS THE ADOPTED `tauBadEvent` PULLED BACK.**  At any joint
point whose gate-tau coordinates are the chain's stage-`22` triples at the adopted
source counters, membership agrees. -/
theorem gate_tau_bad_event_is_pullback (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (g : Nat → Element)
    (T : OracleTable (boundedQueries L)) (w : JointChallengeSpace.JointSpace d)
    (hw : ∀ i : Fin d, w (JointChallengeSpace.Draw.gateTau i)
      = stageTriple L hL e0 strat hb deriveStage
          (JointChallengeSpace.sourceCounter d (JointChallengeSpace.Draw.gateTau i)) T) :
    T ∈ gateTauBadEvent L hL e0 strat hb d g ↔ w ∈ JointChallengeSpace.tauBadEvent d g := by
  rw [mem_gate_tau_bad_event, JointChallengeSpace.tauBadEvent, JointChallengeSpace.mem_tauEvent]
  have : JointChallengeSpace.tauReduction d w
      = ChallengeUnionBound.reduceTuple d (tauRead L hL e0 strat hb d T) := by
    funext i
    show OuterChallenge.reduceTriple (w (JointChallengeSpace.Draw.gateTau i)) = _
    rw [hw i]
    rfl
  rw [this]

/-- **THE GATE-ALPHA EVENT IS THE ADOPTED `alphaBadEvent` PULLED BACK.** -/
theorem gate_alpha_bad_event_is_pullback (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d rows : Nat)
    (coeffsOf : Nat → List Element) (T : OracleTable (boundedQueries L))
    (w : JointChallengeSpace.JointSpace d)
    (hw : w JointChallengeSpace.Draw.gateAlpha
      = stageTriple L hL e0 strat hb deriveStage
          (JointChallengeSpace.sourceCounter d JointChallengeSpace.Draw.gateAlpha) T) :
    T ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
      ↔ w ∈ JointChallengeSpace.alphaBadEvent d rows coeffsOf := by
  rw [mem_gate_alpha_bad_event, JointChallengeSpace.alphaBadEvent,
    JointChallengeSpace.mem_coordEvent, hw]
  rfl

end Audit.Wire3.ReducedFullTransport
