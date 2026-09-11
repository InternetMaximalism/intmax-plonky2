import Audit.Wire3.ReducedFullTransport
import Audit.Wire3.RawBlockLanes
import Audit.Wire3.RawIndexLanes
import Audit.Wire3.RunLevelTransportAudit
import Audit.Wire3.CommitmentOrderSurvey

/-!
# THE ALPHA DIAGONAL: THE ENGINE'S OWN GATE-TAU EVENT ON THE ORACLE TABLE

## THE GAP THIS MODULE CLOSES -- READ THIS FIRST

The explicit engine's gate zero-check table is

  `ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash
      (TranscriptProvenance.gateAlphaElement thash c p) s0.tables`

(the adopted `SoundnessAssembly.outerBadEvent`, and the adopted
`JointChallengeSpace.runBadEvent`).  Its fourth argument, the adopted
`TranscriptProvenance.gateAlphaElement thash c p`, IS THE BLOCK-`0` COORDINATE
`JointChallengeSpace.Draw.gateAlpha`: the adopted
`CommitmentOrderSurvey.prefixAlpha` is `ext3At` of the prefix digest at the adopted
`JointChallengeSpace.sourceCounter d Draw.gateAlpha`, and the adopted
`JointChallengeSpace.DrawEncodesRun.alphaDrawn` is the seam that makes it the
DRAWN coordinate.  In the random-oracle chain of the adopted
`ReducedFullTransport` that counter is `alphaBase d = 9 + 3 d` at the derive
digest.  SO THE ENGINE'S `g` IS A FUNCTION OF A CHALLENGE.

Every gate-tau event in the adopted ROM line -- the adopted
`ReducedFullTransport.gateTauBadEvent L hL e0 strat hb d g` with `g` FREE, the
adopted `tau_target_mass_le` at a FIXED target set `S`, the adopted
`full_bad_draw_probability_le` and `reduced_full_bad_draw_probability_le`, and the
adopted `RawBlockLanes` / `RawIndexLanes` / `ReducedIndexLanes` /
`ReducedEngineIndex` / `GrindingUnionBound` headlines that inherit them -- is
therefore the CONSTANT-ALPHA SLICE of the engine's own tau event.  Section 1 turns
that sentence into a theorem (`rft_tau_event_is_constant_slice`).  The engine's own
event is the DIAGONAL

  `{T | tauRead T ∈ productEvent d (zeroCheckBadSet d (G (alphaRead T)))}`,

`G` being the alpha-to-table map `fun a => gateValue gc gates publicHash a tables`.
NO ADOPTED THEOREM BOUNDS THAT SET.  This module bounds it, by the SAME constant
`ChallengeUnionBound.tauTerm d`.

## WHY IT IS TRUE, AND WHERE THE WORK IS

The alpha counter `alphaBase d = 9 + 3 d` is DISJOINT from every tau counter
`tauBase d i + {0,1,2} = 12 + 3 d + 3 i + {0,1,2}`
(`alpha_base_not_tau_counter`, `tau_counter_not_alpha_counter`).  So at the derive
digest the `3 d` tau cells are FRESH RELATIVE TO THE ALPHA CELL, and the target --
which reads the table only through the alpha cell -- is UNMOVED by reassigning any
tau cell (`engine_tau_alpha_invariant`, `engine_tau_target_invariant`).  That is
exactly the hypothesis shape of the adopted
`OuterLaneTransport.stage_triple_target_card`, whose partition-by-target-value
route is the one-draw case of what section 2 does for the `d`-draw joint peel.

What is NOT available off the shelf is the joint form.  The adopted
`ZeroCheckSemantics.zeroCheckBadSet d g` is not a product of per-coordinate sets,
so all `d` tau blocks must be peeled TOGETHER, as the adopted
`ReducedFullTransport.tauFibre` does -- but the adopted fibre machinery is hard-wired
to start at `stageNoClash deriveStage`, and the diagonal needs it to start at a
BLOCK of the partition.  Section 2 therefore restates the adopted peel over an
ABSTRACT stage-stable base `A` (`tauFibreOn`, `tau_fibre_on_stable`,
`tau_fibre_on_card`, `tau_target_card_on`), then partitions by the target's value
and sums (`tau_diag_card`, `tau_diag_mass_le`).  The per-value constant is the
adopted `ChallengeUnionBound.tau_product_mass_bound d g`, which holds for EVERY
`g` -- that uniformity in `g` is precisely what makes the diagonal cost nothing.

## WHAT IS PROVED

1. SECTION 1.  `alphaRead` (the alpha cell the chain reads at the derive digest),
   `engineTauBadEvent` (the engine's own tau event, at an arbitrary alpha-to-table
   map `G`), `mem_engine_tau_bad_event`, and
   `rft_tau_event_is_constant_slice`: the adopted `gateTauBadEvent … g` IS
   `engineTauBadEvent … (fun _ => g)`.  Plus the counter disjointness the diagonal
   rests on.
2. SECTION 2.  The abstract-base joint peel and the alpha diagonal:
   `engine_tau_no_clash_mass_le`, the headline of this module.
3. SECTION 3.  The full bound with the engine's own tau event in place of the
   `∀ g` one: `full_bad_draw_probability_le_engine_tau`, its `combinedBound` form,
   and the reduced-history pairing.
4. SECTION 4.  The same at RAW lanes (the adopted `RawBlockLanes`), including the
   strategic pairing `strategic_raw_full_bad_draw_probability_le_engine_tau`.
5. SECTION 5.  The bridge to the adopted `RawIndexLanes`:
   `raw_engine_full_bad_draw_probability_le` bounds the union of the raw outer
   lanes, THE ENGINE'S OWN TAU EVENT, the `∀ coeffsOf` alpha event and THE
   ENGINE'S OWN INDEX EVENT.
6. SECTION 6.  **THE IDENTIFICATION OF THE ALPHA ARGUMENT.**
   `alpha_read_is_gate_alpha_element` proves that at the adopted
   `RawBlockLanes.strategicShape` the cell `alphaRead` reads IS the adopted
   `TranscriptProvenance.gateAlphaElement` at the table's own hash and at the
   proof the prover submits there, and `engine_tau_event_at_realized_alpha`
   rewrites the event at `engineGate` into that form, set for set;
   `raw_extended_alpha_read_is_gate_alpha_element` and
   `raw_extended_engine_tau_event_at_realized_alpha` do the same at the section-5
   prover `RawIndexLanes.rawExtendedShape`.  Then a closed instance at the
   envelope's thirteen coupled rounds with a GENUINELY NON-CONSTANT `G`
   (`sampleGate`), for which `engine_tau_target_depends_on_alpha` exhibits two
   alphas whose zero-check bad sets differ (one empty, one inhabited); the
   constant is strictly below `1`; and `raw_engine_full_index_bound_at_thirteen`,
   the closed instance of the SECTION-5 headline at the adopted genuinely raw
   prover of `RawIndexLanes.raw_index_engine_bound_at_thirteen`.

## WHICH EVENTS IN THE FINAL THEOREM ARE THE ENGINE'S OWN

In `raw_engine_full_bad_draw_probability_le` (section 5):

* TAU -- THE ENGINE'S OWN, diagonal in the alpha cell (this module's contribution),
  and the cell it is diagonal in is IDENTIFIED with the engine's alpha, not merely
  named so: section 6's `raw_extended_alpha_read_is_gate_alpha_element` and
  `raw_extended_engine_tau_event_at_realized_alpha` at the very prover of this
  theorem, `RawIndexLanes.rawExtendedShape`.  What is still unidentified in the
  target is `tables`, and only `tables`; READ HONESTY (iii).
* INDEX -- THE ENGINE'S OWN, the adopted `RawIndexLanes.rawEngineIndexBadEvent`,
  identified with the raw-lane index event by the adopted
  `raw_engine_index_bad_event_eq`.
* ALPHA -- the `∀ rows, ∀ coeffsOf` LANE FORM, the adopted
  `ReducedFullTransport.gateAlphaBadEvent`.  Its target is the adopted
  `ChallengeUnionBound.alphaUnionBadSet rows coeffsOf` with `coeffsOf` FIXED DATA;
  the adopted `CommitmentOrderSurvey.prefix_coefficients_ignore_the_eq_column` and
  `coefficients_are_determined_by_the_tables` say that family mentions no
  challenge at all (`prefixCoeffTable` takes neither a hash nor a proof), so no
  diagonal is needed -- but the identification of `coeffsOf` with the DEPLOYED
  run's coefficients is the adopted `CommittedTables` extraction join, which this
  module inherits and does not strengthen.
* OUTER -- the `∀`-LANE FORM, the adopted `RawBlockLanes.rawOuterBadEvent` at raw
  lanes with FREE truth functions and FREE running claims.  IT IS NOT the adopted
  `SoundnessAssembly.outerBadEvent`, which also depends on the alpha coordinate.
  THAT diagonal was done by the adopted `TwoStageConditionalCount` FOR THE FIXED
  PROVER ONLY; FOR THE ADAPTIVE LINE IT IS STILL OPEN, and nothing below closes it.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)` -- one
independent uniform block per byte string of length at most `L`.  The fresh-query
fact everything rests on, the adopted `BirthdayClashBound.fresh_coordinate_probability`,
is the DEFINING property of a random table and is false, as a theorem, for any
fixed hash.  Replacing the deployed permutation by a table drawn from this law is
an assumption with no proof anywhere in this tree.

(ii) THE PROVER CLASS IS UNCHANGED.  Sections 1--3 are stated for EVERY
`StrategyChainBound.Strategy`: a TRANSCRIPT-RESTRICTED prover, handed the stage
digests of its own chain and the oracle's answers at the CHALLENGE inputs of those
digests, making no oracle queries of its own.  GRINDING -- a prover that hashes
candidate payloads itself and keeps the one whose digest collides -- is NOT
covered by any theorem below.  Section 3's pairing is the adopted
`OuterLaneTransport.ReducedStrategy` (reduced round-challenge history); section 4's
is the adopted `RawBlockLanes.strategicShape` at an arbitrary `RoundCausal S` (raw
block reading); section 5's is the adopted `RawIndexLanes.rawExtendedShape` at an
arbitrary `RoundCausal S` and `ClaimsCausal d U`.  THE ALPHA DIAGONAL ITSELF COSTS
NO EXTRA RESTRICTION: `engine_tau_no_clash_mass_le` holds for every `Strategy` and
every `G : Element → Nat → Element` whatsoever, including `G`s no gate
configuration realizes.

(iii) WHAT THE DIAGONAL DOES AND DOES NOT SAY.  It says: the mass of the event
"the tau column lands in the zero-check bad set OF THE TABLE THE SAME ORACLE
DREW AT THE ALPHA CELL" is at most `tauTerm d`, the same constant the adopted
constant-`g` slice pays.  In the bounds of sections 2--5 the map `G` is a FREE
PARAMETER, and the bounds hold for `G`s no gate configuration realizes.

WHAT SECTION 6 ADDS, AND WHAT IS LEFT.  `alpha_read_is_gate_alpha_element` and
`raw_extended_alpha_read_is_gate_alpha_element` PROVE -- they do not assume --
that the cell `alphaRead` reads at the derive digest IS the adopted
`TranscriptProvenance.gateAlphaElement (hashOf T) c p` at the table's OWN hash and
at the proof `p` the prover actually submits at that table, the adopted
`RunLevelTransportAudit.realizedRunProof`, for the section-4 prover
(`RawBlockLanes.strategicShape`) and for the section-5 prover
(`RawIndexLanes.rawExtendedShape`) respectively.
`engine_tau_event_at_realized_alpha` and its raw twin then rewrite this module's
own event at `G := engineGate c gates publicHash tables` into the form whose
target is `ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash
(gateAlphaElement (hashOf T) c (realizedRunProof … T)) tables`, set for set --
which is the adopted `SoundnessAssembly.outerBadEvent`'s zero-check table with ONE
argument still unidentified.

That one argument is `tables`.  Comparing with the adopted
`SoundnessAssembly.outerBadEvent`, the gate list and the configuration are the
same data the event is stated at; `publicHash` there is
`GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs)`, and
`engine_public_hash_is_the_statement_public_hash` shows the realized proof's
public inputs are the STATEMENT's, so that argument is a function of `E` and `s`
alone and is NOT a gap; the deployed engine's `s0.tables` is.  THE REMAINING
UNPROVED ARGUMENT IS EXACTLY `tables = s0.tables` -- the adopted `CommitmentOrder`
/ `CommitmentOrderSurvey` `CommittedTables` extraction join, which remains open
exactly as those modules leave it.  Sections 5 and 6 of the adopted
`CommitmentOrderSurvey` are inherited verbatim and not strengthened.

(iv) THE OUTER DIAGONAL FOR THE ADAPTIVE PROVER IS STILL OPEN.  See the list
above.  The adopted `SoundnessAssembly.outerBadEvent` depends on the alpha
coordinate through its lanes as well as through `g`; the adopted
`TwoStageConditionalCount` handles that dependence for a FIXED prover, and no
module -- including this one -- handles it for the adaptive line.  Do not read
`raw_engine_full_bad_draw_probability_le` as "the engine's four families are all
bounded adaptively": TWO of the four (tau here, index in the adopted
`RawIndexLanes`) are the engine's own; the outer and alpha summands are the
`∀`-lane forms.

(v) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  `combinedBound` covers
(a) the outer sumcheck round-agreement events, (b) the gate tau multilinear zero
check and (c) the gate alpha zero check; the index term covers the adopted index
sampler.  The WHOLE WHIR/Merkle contribution -- proximity and list decoding, the
query-repetition profile, Merkle collision resistance -- is EXCLUDED, and it is the
dominant term.  The deployed design point is around a hundred bits; quoting the
constant of section 6 as the wire-v3 soundness error would be wrong by roughly
seventy bits.  The meaning of the per-round bad sets remains the adopted
`ConditionalSoundness` one -- GOOD-DRAW-CONDITIONAL, with that module's assumption
list untouched -- and nothing here instantiates it.

(vi) NO ADAPTIVE FIAT--SHAMIR SOUNDNESS IS CLAIMED.  What is bounded is the mass of
named events defined directly on the oracle table.  The Fiat--Shamir half -- that
the run's encoding draw is `JointChallengeSpace.jointProbability`-distributed --
remains exactly as unformalized as the adopted `JointChallengeSpace.DrawEncodesRun`
header says.  Acceptance is never exhibited, no extractor is run, and nothing below
is a claim that Fiat--Shamir soundness has been established for an adaptive prover.

(vii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's OWN
definitions (`engineTauBadEvent`), in the STATEMENTS of section 6's
`engine_tau_event_at_realized_alpha` and
`raw_extended_engine_tau_event_at_realized_alpha` -- which spell that definition
out at the realized alpha and so necessarily repeat its `Finset.univ.filter` over
the table space -- and, through the generic `Finset.mem_univ` /
`Finset.card_univ` on `OracleTable`, in a few proofs; no tactic or term below ever
puts `Finset.univ` on `Element`, on `OuterChallenge.DigestTriple` or on
`ChallengeUnionBound.TripleTuple` in a reducible position, and no `Nat` or `ℚ`
arithmetic tactic below is ever shown a `Fintype.card` of any of them -- the only
exponent bookkeeping goes through the adopted `ReducedFullTransport.peel_pow` and
`triple_tuple_card_as_triples`, stated over abstract naturals.  `open Classical in`
is used for the declarations whose statements mention membership in, or images
into, a `Finset (ChallengeUnionBound.TripleTuple d)`, exactly as the adopted
`ChallengeUnionBound.productEvent` and `ReducedFullTransport.tau_target_card` do.
Every digest-level membership goes through the adopted
`ChallengeUnionBound.mem_productEvent`; memberships over the table space are
manipulated through `Finset` equalities and the adopted generic helpers
`OuterLaneTransport.univ_filter_inter_subset`, `subset_inter_union_compl` and
`ReducedEngineIndex.inter_union_mass_le`; the two `…_at_realized_alpha`
statements are proved by `Finset.filter_congr` over that space and nothing else.
`ChallengeUnionBound.tauTerm` is never
evaluated; `tau_term_nonneg` derives its sign from the adopted
`uniform_product_probability_nonneg` rather than from its formula.  The two closed
instances of section 6 mention `d = 13` literally, as the adopted
`ReducedFullTransport.reduced_full_bound_at_thirteen` and the adopted
`RawIndexLanes.raw_index_engine_bound_at_thirteen` do.
-/

namespace Audit.Wire3.EngineTauDiagonal

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.ReducedFullTransport
open Audit.Wire3.RawBlockLanes

/-! ## 1. THE ENGINE'S OWN TAU EVENT, AND THE SLICE THE ADOPTED LINE BOUNDS -/

/-- **THE ALPHA CELL THE CHAIN READS AT THE DERIVE DIGEST**, reduced to a field
element: the adopted `OuterChallenge.reduceTriple` of the digest triple at the
adopted `ReducedFullTransport.alphaBase d = 9 + 3 d`, which
`ReducedFullTransport.alpha_base_is_source_counter` PROVES is the adopted
`JointChallengeSpace.sourceCounter d Draw.gateAlpha`. -/
def alphaRead (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) : Element :=
  OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb deriveStage (alphaBase d) T)

open Classical in
/-- **THE ENGINE'S OWN GATE-TAU BAD EVENT ON THE ORACLE TABLE.**  The tau column
the chain reads at the derive digest lands in the adopted
`ZeroCheckSemantics.zeroCheckBadSet` OF THE TABLE THE SAME ORACLE'S ALPHA CELL
SELECTS.  `G` is the alpha-to-table map: for the explicit engine it is
`engineGate c gates publicHash tables` of section 6, i.e.
`fun a => ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash a
tables`.  THAT THE ARGUMENT IT IS APPLIED TO IS THE ENGINE'S OWN IS NOT A
DEFINITIONAL REMARK AND IS NOT ASSUMED: section 6's
`alpha_read_is_gate_alpha_element` PROVES that at the adopted
`RawBlockLanes.strategicShape` the cell `alphaRead` reads IS the adopted
`TranscriptProvenance.gateAlphaElement` at the table's own hash and at the proof
the prover actually submits there (the adopted
`RunLevelTransportAudit.realizedRunProof`), and
`engine_tau_event_at_realized_alpha` rewrites the event below into that form, set
for set.  `raw_extended_alpha_read_is_gate_alpha_element` and its event form do
the same at the adopted `RawIndexLanes.rawExtendedShape`, the prover of section 5.
What is then still NOT proved about the engine's table is only
`tables = s0.tables` -- the adopted `CommitmentOrder` / `CommitmentOrderSurvey`
`CommittedTables` join; `publicHash` is not a further gap, because the adopted
`SoundnessAssembly.outerBadEvent` takes it as
`GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs)` and
`engine_public_hash_is_the_statement_public_hash` shows that at the realized proof
this is a function of the STATEMENT alone.  THE TARGET MOVES WITH THE TABLE;
this is what the adopted `ReducedFullTransport.gateTauBadEvent` does not do. -/
noncomputable def engineTauBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (G : Element → Nat → Element) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    tauRead L hL e0 strat hb d T ∈ ChallengeUnionBound.productEvent d
      (ZeroCheckSemantics.zeroCheckBadSet d (G (alphaRead L hL e0 strat hb d T))))

open Classical in
theorem mem_engine_tau_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (G : Element → Nat → Element) (T : OracleTable (boundedQueries L)) :
    T ∈ engineTauBadEvent L hL e0 strat hb d G ↔
      ChallengeUnionBound.reduceTuple d (tauRead L hL e0 strat hb d T)
        ∈ ZeroCheckSemantics.zeroCheckBadSet d (G (alphaRead L hL e0 strat hb d T)) := by
  rw [engineTauBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact ChallengeUnionBound.mem_productEvent _ _ _

open Classical in
/-- (1) **THE ADOPTED ROM TAU EVENT IS THE CONSTANT-ALPHA SLICE OF THE ENGINE'S.**
Set for set, on the nose.  So every adopted tau bound in the tree -- the adopted
`ReducedFullTransport.gate_tau_no_clash_mass_le`, `full_bad_draw_probability_le`,
`RawBlockLanes.raw_full_bad_draw_probability_le`,
`RawIndexLanes.raw_engine_index_bad_draw_probability_le` and their descendants --
is a statement about `engineTauBadEvent … (fun _ => g)` and about nothing else. -/
theorem rft_tau_event_is_constant_slice (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) (g : Nat → Element) :
    gateTauBadEvent L hL e0 strat hb d g = engineTauBadEvent L hL e0 strat hb d (fun _ => g) :=
  rfl

/-- (1) **THE ALPHA COUNTER IS NOT A TAU COUNTER.**  `alphaBase d = 9 + 3 d` is
below every `tauBase d i = 12 + 3 d + 3 i`, so it misses that block's three
counters. -/
theorem alpha_base_not_tau_counter (d i : Nat) :
    alphaBase d ∉ tripleCounters (tauBase d i) := by
  simp only [alphaBase, tauBase, tripleCounters, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- (1) **AND CONVERSELY**: no tau counter is one of the alpha block's three
counters.  This is the form the diagonal needs -- the three ALPHA cells must be
untouched when a TAU cell is reassigned. -/
theorem tau_counter_not_alpha_counter (d i c : Nat) (hc : c ∈ tripleCounters (tauBase d i)) :
    c ∉ tripleCounters (alphaBase d) := by
  rcases (mem_triple_counters (tauBase d i) c).mp hc with h | h | h <;>
    · rw [h]
      simp only [alphaBase, tauBase, tripleCounters, Finset.mem_insert, Finset.mem_singleton]
      omega

/-- (1) **THE ALPHA CELL IS UNMOVED BY REASSIGNING A TAU CELL.**  The adopted
`OuterLaneTransport.stage_triple_reassign_same`: two counters below the adopted
`Transcript.u64Limit` at one digest are two different queries. -/
theorem engine_tau_alpha_invariant (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL e0 strat hb deriveStage) (m : Nat) (hmd : m < d) (c : Nat)
    (hc : c ∈ tripleCounters (tauBase d m)) (b : Block) :
    alphaRead L hL e0 strat hb d
        (reassign T (challengeSel L hL e0 strat hb deriveStage c T) b)
      = alphaRead L hL e0 strat hb d T := by
  rw [alphaRead, alphaRead, stage_triple_reassign_same L hL e0 strat hb deriveStage
    (alphaBase d) c (tau_counter_mem_lt d m c hmd hc hdu) (alpha_counter_lt d hdu)
    (tau_counter_not_alpha_counter d m c hc) T hT b]

open Classical in
/-- (1) **HENCE SO IS THE ENGINE'S TAU TARGET.**  The target reads the table only
through the alpha cell, so the `3 d` tau cells it is tested against cannot move
it -- the hypothesis shape of the adopted
`OuterLaneTransport.stage_triple_target_card`, now for the whole tau column. -/
theorem engine_tau_target_invariant (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (G : Element → Nat → Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb deriveStage)
    (m : Nat) (hmd : m < d) (c : Nat) (hc : c ∈ tripleCounters (tauBase d m)) (b : Block) :
    ChallengeUnionBound.productEvent d (ZeroCheckSemantics.zeroCheckBadSet d
        (G (alphaRead L hL e0 strat hb d
          (reassign T (challengeSel L hL e0 strat hb deriveStage c T) b))))
      = ChallengeUnionBound.productEvent d (ZeroCheckSemantics.zeroCheckBadSet d
          (G (alphaRead L hL e0 strat hb d T))) := by
  rw [engine_tau_alpha_invariant L hL e0 strat hb d hdu T hT m hmd c hc b]

/-! ## 2. THE JOINT PEEL OVER AN ABSTRACT BASE, AND THE ALPHA DIAGONAL -/

/-- The prescribed-prefix fibre of an ARBITRARY stage-stable base `A`: the tables
of `A` whose first `n` tau triples take the prescribed values.  The adopted
`ReducedFullTransport.tauFibre` is this at `A = stageNoClash deriveStage`; the
diagonal needs it at a BLOCK of the target's partition, which is why the base is a
parameter here. -/
noncomputable def tauFibreOn (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (t : Nat → OuterChallenge.DigestTriple) :
    Nat → Finset (OracleTable (boundedQueries L))
  | 0 => A
  | n + 1 =>
      (tauFibreOn L hL e0 strat hb d A t n).filter
        (fun T => stageTriple L hL e0 strat hb deriveStage (tauBase d n) T = t n)

theorem tau_fibre_on_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (t : Nat → OuterChallenge.DigestTriple) : tauFibreOn L hL e0 strat hb d A t 0 = A := rfl

theorem tau_fibre_on_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (t : Nat → OuterChallenge.DigestTriple) (n : Nat) :
    tauFibreOn L hL e0 strat hb d A t (n + 1)
      = (tauFibreOn L hL e0 strat hb d A t n).filter
          (fun T => stageTriple L hL e0 strat hb deriveStage (tauBase d n) T = t n) := rfl

/-- (2) Membership in the fibre, spelled out. -/
theorem mem_tau_fibre_on (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (t : Nat → OuterChallenge.DigestTriple) :
    ∀ (n : Nat) (T : OracleTable (boundedQueries L)),
      T ∈ tauFibreOn L hL e0 strat hb d A t n ↔
        (T ∈ A ∧ ∀ i, i < n →
          stageTriple L hL e0 strat hb deriveStage (tauBase d i) T = t i) := by
  intro n
  induction n with
  | zero =>
      intro T
      exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, fun h => h.1⟩
  | succ n2 ih =>
      intro T
      rw [tau_fibre_on_succ, Finset.mem_filter, ih T]
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

/-- (2) **THE FIBRE IS STAGE-STABLE AT EVERY LATER TAU BLOCK**, whenever the base
is.  The adopted `ReducedFullTransport.tau_fibre_stable` argument, with the base a
parameter: the prescriptions already made sit at counters of blocks `i < m`, which
the adopted `ReducedFullTransport.tau_counters_disjoint` separates from block
`m`'s. -/
theorem tau_fibre_on_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (t : Nat → OuterChallenge.DigestTriple)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hA : ∀ m, m < d →
      StageStable L hL e0 strat hb deriveStage (tripleCounters (tauBase d m)) A) :
    ∀ n m : Nat, n ≤ m → m < d →
      StageStable L hL e0 strat hb deriveStage (tripleCounters (tauBase d m))
        (tauFibreOn L hL e0 strat hb d A t n) := by
  intro n
  induction n with
  | zero =>
      intro m _ hmd
      exact hA m hmd
  | succ n2 ih =>
      intro m hnm hmd
      have hprev := ih m (by omega) hmd
      rw [tau_fibre_on_succ]
      refine stage_stable_filter L hL e0 strat hb deriveStage (tripleCounters (tauBase d m))
        (tauFibreOn L hL e0 strat hb d A t n2) hprev
        (fun T => stageTriple L hL e0 strat hb deriveStage (tauBase d n2) T = t n2)
        (fun T hT c hc b => ?_)
      show stageTriple L hL e0 strat hb deriveStage (tauBase d n2)
            (reassign T (challengeSel L hL e0 strat hb deriveStage c T) b) = t n2
        ↔ stageTriple L hL e0 strat hb deriveStage (tauBase d n2) T = t n2
      rw [stage_triple_reassign_same L hL e0 strat hb deriveStage (tauBase d n2) c
        (tau_counter_mem_lt d m c hmd hc hdu)
        (tau_counter_lt d n2 (by omega) hdu)
        (tau_counters_disjoint d n2 m c (by omega) hc) T (hprev.1 T hT) b]

/-- (2) **THE JOINT FIBRE COUNT OVER THE WHOLE TAU COLUMN, AT AN ABSTRACT BASE.**
`d` applications of the adopted `OuterLaneTransport.stage_triple_fibre_card`, with
the adopted `ReducedFullTransport.peel_pow` doing the exponent bookkeeping over
abstract naturals. -/
theorem tau_fibre_on_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (t : Nat → OuterChallenge.DigestTriple) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hA : ∀ m, m < d →
      StageStable L hL e0 strat hb deriveStage (tripleCounters (tauBase d m)) A) :
    ∀ n : Nat, n ≤ d →
      (tauFibreOn L hL e0 strat hb d A t n).card
          * Fintype.card OuterChallenge.DigestTriple ^ n
        = A.card := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [tau_fibre_on_zero, pow_zero, Nat.mul_one]
  | succ n2 ih =>
      intro hn
      have hstep : (tauFibreOn L hL e0 strat hb d A t (n2 + 1)).card
            * Fintype.card OuterChallenge.DigestTriple
          = (tauFibreOn L hL e0 strat hb d A t n2).card :=
        stage_triple_fibre_card L hL e0 strat hb deriveStage (tauBase d n2)
          (tau_counter_lt d n2 (by omega) hdu) (tauFibreOn L hL e0 strat hb d A t n2)
          (tau_fibre_on_stable L hL e0 strat hb d A t hdu hA n2 n2 (le_refl n2) (by omega))
          (t n2)
      exact (peel_pow _ _ _ n2 hstep).trans (ih (by omega))

/-- (2) The whole-column fibre at an abstract base is exactly the tables of the
base that read the prescribed tau tuple. -/
theorem tau_fibre_on_at_extend (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (t : ChallengeUnionBound.TripleTuple d)
    (T : OracleTable (boundedQueries L)) :
    T ∈ tauFibreOn L hL e0 strat hb d A (tauExtend d t) d ↔
      (T ∈ A ∧ tauRead L hL e0 strat hb d T = t) := by
  rw [mem_tau_fibre_on]
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
/-- (2) **THE CONSTANT-TARGET COUNT AT AN ABSTRACT BASE.**  Exactly `|S|` fibres
are caught, each of size `|A| / |DigestTriple| ^ d`.  The adopted
`ReducedFullTransport.tau_target_card` is this at `A = stageNoClash deriveStage`. -/
theorem tau_target_card_on (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < d →
      StageStable L hL e0 strat hb deriveStage (tripleCounters (tauBase d m)) A)
    (S : Finset (ChallengeUnionBound.TripleTuple d)) :
    (A.filter (fun T => tauRead L hL e0 strat hb d T ∈ S)).card
        * Fintype.card OuterChallenge.DigestTriple ^ d
      = S.card * A.card := by
  have hfib : (A.filter (fun T => tauRead L hL e0 strat hb d T ∈ S)).card
      = ∑ t in S, ((A.filter (fun T => tauRead L hL e0 strat hb d T ∈ S)).filter
          (fun T => tauRead L hL e0 strat hb d T = t)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => (Finset.mem_filter.mp hx).2)
  have key : ∀ t ∈ S,
      ((A.filter (fun T => tauRead L hL e0 strat hb d T ∈ S)).filter
          (fun T => tauRead L hL e0 strat hb d T = t)).card
          * Fintype.card OuterChallenge.DigestTriple ^ d
        = A.card := by
    intro t ht
    have hset : (A.filter (fun T => tauRead L hL e0 strat hb d T ∈ S)).filter
          (fun T => tauRead L hL e0 strat hb d T = t)
        = tauFibreOn L hL e0 strat hb d A (tauExtend d t) d := by
      apply Finset.ext
      intro T
      rw [tau_fibre_on_at_extend, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hT, -⟩, hEq⟩
        exact ⟨hT, hEq⟩
      · rintro ⟨hT, hEq⟩
        exact ⟨⟨hT, hEq ▸ ht⟩, hEq⟩
    rw [hset]
    exact tau_fibre_on_card L hL e0 strat hb d A (tauExtend d t) hdu hA d (le_refl d)
  rw [hfib, Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

open Classical in
/-- (2) **THE ALPHA DIAGONAL, COUNTING FORM.**  The target `targ T` is whatever the
ALPHA CELL has made it at the table `T`; all that is asked of it is that the `3 d`
tau cells it is tested against cannot move it.  The conditioning event is
partitioned by the VALUE of `targ`, the target is constant on each block, each
block is stage-stable at every tau block (the alpha cell is not a tau cell), and
`tau_target_card_on` applies there.  This is the adopted
`OuterLaneTransport.stage_triple_target_card` idea at `d` scheduled draws instead
of one -- with the per-value size budget stated as a RATIO, because the adopted
`ChallengeUnionBound.tau_product_mass_bound` is a density bound. -/
theorem tau_diag_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < d →
      StageStable L hL e0 strat hb deriveStage (tripleCounters (tauBase d m)) A)
    (targ : OracleTable (boundedQueries L) → Finset (ChallengeUnionBound.TripleTuple d))
    (hinv : ∀ T ∈ A, ∀ m, m < d → ∀ c ∈ tripleCounters (tauBase d m), ∀ b : Block,
      targ (reassign T (challengeSel L hL e0 strat hb deriveStage c T) b) = targ T)
    (mu : ℚ)
    (hmu : ∀ T ∈ A, ((targ T).card : ℚ)
      ≤ mu * (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d) :
    ((A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T)).card : ℚ)
      ≤ mu * (A.card : ℚ) := by
  have hNpos : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d := by
    have h1 : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
      exact_mod_cast JointChallengeSpace.digest_triple_card_pos
    exact pow_pos h1 d
  have hfib1 : (A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T)).card
      = ∑ S in A.image targ,
          ((A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T)).filter
            (fun T => targ T = S)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun x hx => Finset.mem_image_of_mem targ (Finset.mem_filter.mp hx).1)
  have hfib2 : A.card = ∑ S in A.image targ, (A.filter (fun T => targ T = S)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem targ hx)
  have key : ∀ S ∈ A.image targ,
      ((A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T)).filter
          (fun T => targ T = S)).card * Fintype.card OuterChallenge.DigestTriple ^ d
        = S.card * (A.filter (fun T => targ T = S)).card := by
    intro S _
    have hAS : ∀ m, m < d →
        StageStable L hL e0 strat hb deriveStage (tripleCounters (tauBase d m))
          (A.filter (fun T => targ T = S)) := by
      intro m hmd
      refine stage_stable_filter L hL e0 strat hb deriveStage (tripleCounters (tauBase d m))
        A (hA m hmd) (fun T => targ T = S) (fun T hT c hc b => ?_)
      show targ (reassign T (challengeSel L hL e0 strat hb deriveStage c T) b) = S
        ↔ targ T = S
      rw [hinv T hT m hmd c hc b]
    have hEq : (A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T)).filter
          (fun T => targ T = S)
        = (A.filter (fun T => targ T = S)).filter
            (fun T => tauRead L hL e0 strat hb d T ∈ S) := by
      apply Finset.ext
      intro T
      constructor
      · intro hT
        obtain ⟨hT1, hTS⟩ := Finset.mem_filter.mp hT
        obtain ⟨hTA, hTd⟩ := Finset.mem_filter.mp hT1
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hTA, hTS⟩, hTS ▸ hTd⟩
      · intro hT
        obtain ⟨hT1, hTd⟩ := Finset.mem_filter.mp hT
        obtain ⟨hTA, hTS⟩ := Finset.mem_filter.mp hT1
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hTA, hTS ▸ hTd⟩, hTS⟩
    rw [hEq]
    exact tau_target_card_on L hL e0 strat hb d hdu (A.filter (fun T => targ T = S)) hAS S
  have hnat : (A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T)).card
      * Fintype.card OuterChallenge.DigestTriple ^ d
      = ∑ S in A.image targ, S.card * (A.filter (fun T => targ T = S)).card := by
    rw [hfib1, Finset.sum_mul]
    exact Finset.sum_congr rfl key
  have hQ : ((A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T)).card : ℚ)
      * ((Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d)
      = ∑ S in A.image targ,
          (S.card : ℚ) * ((A.filter (fun T => targ T = S)).card : ℚ) := by
    have hc := congrArg (fun n : Nat => (n : ℚ)) hnat
    push_cast at hc
    exact hc
  have hcastA : ∑ S in A.image targ, ((A.filter (fun T => targ T = S)).card : ℚ)
      = (A.card : ℚ) := by
    have hc := congrArg (fun n : Nat => (n : ℚ)) hfib2
    push_cast at hc
    exact hc.symm
  have hbound : ∑ S in A.image targ,
        (S.card : ℚ) * ((A.filter (fun T => targ T = S)).card : ℚ)
      ≤ ∑ S in A.image targ,
        (mu * (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d)
          * ((A.filter (fun T => targ T = S)).card : ℚ) := by
    refine Finset.sum_le_sum (fun S hS => ?_)
    obtain ⟨T0, hT0A, hT0⟩ := Finset.mem_image.mp hS
    have hS2 : (S.card : ℚ)
        ≤ mu * (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d := by
      rw [← hT0]
      exact hmu T0 hT0A
    exact mul_le_mul_of_nonneg_right hS2 (Nat.cast_nonneg _)
  have hsum2 : ∑ S in A.image targ,
        (mu * (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d)
          * ((A.filter (fun T => targ T = S)).card : ℚ)
      = (mu * (A.card : ℚ)) * ((Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d) := by
    rw [← Finset.mul_sum, hcastA]
    ring
  have hle : ((A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T)).card : ℚ)
      * ((Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d)
      ≤ (mu * (A.card : ℚ)) * ((Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d) := by
    rw [hQ, ← hsum2]
    exact hbound
  exact le_of_mul_le_mul_right hle hNpos

open Classical in
/-- (2) **THE ALPHA DIAGONAL, AS A MASS.** -/
theorem tau_diag_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < d →
      StageStable L hL e0 strat hb deriveStage (tripleCounters (tauBase d m)) A)
    (targ : OracleTable (boundedQueries L) → Finset (ChallengeUnionBound.TripleTuple d))
    (hinv : ∀ T ∈ A, ∀ m, m < d → ∀ c ∈ tripleCounters (tauBase d m), ∀ b : Block,
      targ (reassign T (challengeSel L hL e0 strat hb deriveStage c T) b) = targ T)
    (mu : ℚ) (hmu0 : 0 ≤ mu)
    (hmu : ∀ T ∈ A, ((targ T).card : ℚ)
      ≤ mu * (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d) :
    oracleProbability (boundedQueries L)
        (A.filter (fun T => tauRead L hL e0 strat hb d T ∈ targ T))
      ≤ mu := by
  have hcard := tau_diag_card L hL e0 strat hb d hdu A hA targ hinv mu hmu
  have hAle : (A.card : ℚ) ≤ (Fintype.card (OracleTable (boundedQueries L)) : ℚ) := by
    have h : A.card ≤ Fintype.card (OracleTable (boundedQueries L)) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_univ A
    exact_mod_cast h
  rw [oracleProbability, div_le_iff (oracle_card_cast_pos (boundedQueries L))]
  exact le_trans hcard (mul_le_mul_of_nonneg_left hAle hmu0)

/-- (2) The adopted `ChallengeUnionBound.tauTerm` is nonnegative, read off the
adopted `uniform_product_probability_nonneg` and `tau_product_mass_bound` rather
than off its formula: no cardinality enters. -/
theorem tau_term_nonneg (d : Nat) : 0 ≤ ChallengeUnionBound.tauTerm d :=
  le_trans (ChallengeUnionBound.uniform_product_probability_nonneg d _)
    (ChallengeUnionBound.tau_product_mass_bound d (fun _ => 0))

open Classical in
/-- (2) The adopted tau density bound in the size form the diagonal consumes, for
EVERY `g`.  That uniformity in `g` is what makes the diagonal free. -/
theorem tau_product_card_le (d : Nat) (g : Nat → Element) :
    ((ChallengeUnionBound.productEvent d (ZeroCheckSemantics.zeroCheckBadSet d g)).card : ℚ)
      ≤ ChallengeUnionBound.tauTerm d
        * (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d := by
  have hNpos : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d := by
    have h1 : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
      exact_mod_cast JointChallengeSpace.digest_triple_card_pos
    exact pow_pos h1 d
  have h := ChallengeUnionBound.tau_product_mass_bound d g
  rw [ChallengeUnionBound.uniformProductProbability, triple_tuple_card_as_triples,
    Nat.cast_pow, div_le_iff hNpos] at h
  exact h

open Classical in
/-- (2) **THE HEADLINE: THE ENGINE'S OWN TAU EVENT COSTS EXACTLY THE ADOPTED
`tauTerm d`.**  The target moves with the alpha cell the same oracle answered at
counter `9 + 3 d`; the `3 d` tau cells are fresh relative to it; and the adopted
`ChallengeUnionBound.tau_product_mass_bound` bounds the density of the zero-check
bad set for EVERY value the alpha cell can take.  This is the bound the adopted
line does not have.  It holds for EVERY `Strategy` and EVERY `G`. -/
theorem engine_tau_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (G : Element → Nat → Element) (hdu : 12 + 6 * d < Transcript.u64Limit) :
    oracleProbability (boundedQueries L)
        (engineTauBadEvent L hL e0 strat hb d G
          ∩ stageNoClash L hL e0 strat hb deriveStage)
      ≤ ChallengeUnionBound.tauTerm d := by
  have hsub : engineTauBadEvent L hL e0 strat hb d G
        ∩ stageNoClash L hL e0 strat hb deriveStage
      ⊆ (stageNoClash L hL e0 strat hb deriveStage).filter (fun T =>
          tauRead L hL e0 strat hb d T ∈ ChallengeUnionBound.productEvent d
            (ZeroCheckSemantics.zeroCheckBadSet d (G (alphaRead L hL e0 strat hb d T)))) := by
    rw [engineTauBadEvent]
    exact univ_filter_inter_subset _ _ _ (fun T hT => hT)
  refine le_trans (oracle_probability_mono (boundedQueries L) _ _ hsub) ?_
  exact tau_diag_mass_le L hL e0 strat hb d hdu (stageNoClash L hL e0 strat hb deriveStage)
    (fun m _ => stage_stable_no_clash L hL e0 strat hb deriveStage
      (tripleCounters (tauBase d m)))
    (fun T => ChallengeUnionBound.productEvent d
      (ZeroCheckSemantics.zeroCheckBadSet d (G (alphaRead L hL e0 strat hb d T))))
    (fun T hT m hmd c hc b =>
      engine_tau_target_invariant L hL e0 strat hb d G hdu T hT m hmd c hc b)
    (ChallengeUnionBound.tauTerm d) (tau_term_nonneg d)
    (fun T _ => tau_product_card_le d (G (alphaRead L hL e0 strat hb d T)))

open Classical in
/-- (2) **THE SAME AT THE LARGER CONDITIONING STAGE.**  The adopted
`OuterLaneTransport.stage_no_clash_mono` nests the chains' no-clash events, so the
diagonal is available under any conditioning stage at or beyond the derive
digest. -/
theorem engine_tau_no_clash_mass_le_at (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (G : Element → Nat → Element) (hdu : 12 + 6 * d < Transcript.u64Limit) (n : Nat)
    (hn : deriveStage ≤ n) :
    oracleProbability (boundedQueries L)
        (engineTauBadEvent L hL e0 strat hb d G ∩ stageNoClash L hL e0 strat hb n)
      ≤ ChallengeUnionBound.tauTerm d := by
  have hsub : engineTauBadEvent L hL e0 strat hb d G ∩ stageNoClash L hL e0 strat hb n
      ⊆ engineTauBadEvent L hL e0 strat hb d G
          ∩ stageNoClash L hL e0 strat hb deriveStage := by
    intro T hT
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hT
    exact Finset.mem_inter.mpr ⟨h1, stage_no_clash_mono L hL e0 strat hb deriveStage n hn h2⟩
  exact le_trans (oracle_probability_mono (boundedQueries L) _ _ hsub)
    (engine_tau_no_clash_mass_le L hL e0 strat hb d G hdu)

/-! ## 3. THE FULL BOUND WITH THE ENGINE'S OWN TAU EVENT -/

open Classical in
/-- **THE FULL BAD EVENT WITH THE ENGINE'S OWN TAU EVENT**: some coupled round of
either OUTER lane agrees, OR the tau column lands in the zero-check bad set OF THE
TABLE THE ALPHA CELL SELECTS, OR the gate alpha lands in the adopted row union.
Only the middle disjunct differs from the adopted
`ReducedFullTransport.fullBadEvent`. -/
noncomputable def engineFullBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (d rows : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  (outerLaneBadEvent L hL e0 strat hb logLane gateLane d
      ∪ engineTauBadEvent L hL e0 strat hb d G)
    ∪ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf

open Classical in
theorem mem_engine_full_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (d rows : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ engineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf ↔
      (T ∈ outerLaneBadEvent L hL e0 strat hb logLane gateLane d ∨
        T ∈ engineTauBadEvent L hL e0 strat hb d G ∨
        T ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf) := by
  simp only [engineFullBadEvent, Finset.mem_union, or_assoc]

open Classical in
/-- (3) **THE ADOPTED FULL EVENT IS THE CONSTANT-ALPHA SLICE OF THIS ONE.** -/
theorem engine_full_bad_event_constant_slice (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (d rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) :
    fullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
      = engineFullBadEvent L hL e0 strat hb logLane gateLane d rows (fun _ => g) coeffsOf :=
  rfl

open Classical in
/-- (3) **THE FULL BAD-DRAW BOUND WITH THE ENGINE'S OWN TAU EVENT**, for every
strategy and every pair of lanes.  The constant is UNCHANGED from the adopted
`ReducedFullTransport.full_bad_draw_probability_le`: the diagonal costs nothing.
The three masses are conditioned on nested no-clash events, so ONE complement term
pays for all three.

READ HONESTY (ii) AND (iv): the outer summand here is the adopted
prefix-dependent lane transport in its `∀`-lane form, and the alpha summand is the
`∀ coeffsOf` form; only the tau summand is the engine's own. -/
theorem full_bad_draw_probability_le_engine_tau (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (logLane gateLane : Lane) (d q rows constraints : Nat) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (engineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf)
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hnest : stageNoClash L hL e0 strat hb (22 + 5 * d)
      ⊆ stageNoClash L hL e0 strat hb deriveStage :=
    stage_no_clash_mono L hL e0 strat hb deriveStage (22 + 5 * d) (by rw [deriveStage]; omega)
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (engineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf)
      (stageNoClash L hL e0 strat hb (22 + 5 * d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (engineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
  have hu2 := ReducedEngineIndex.inter_union_mass_le L
    (outerLaneBadEvent L hL e0 strat hb logLane gateLane d
      ∪ engineTauBadEvent L hL e0 strat hb d G)
    (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf)
    (stageNoClash L hL e0 strat hb (22 + 5 * d))
  have hu3 := ReducedEngineIndex.inter_union_mass_le L
    (outerLaneBadEvent L hL e0 strat hb logLane gateLane d)
    (engineTauBadEvent L hL e0 strat hb d G)
    (stageNoClash L hL e0 strat hb (22 + 5 * d))
  have houter := outer_no_clash_mass_le L hL e0 strat hb logLane gateLane 5 (q + 2)
    hlog hgate (22 + 5 * d) d (fun r hr => round_stage_le r d hr)
  rw [round_terms_sum d q] at houter
  have htau := engine_tau_no_clash_mass_le_at L hL e0 strat hb d G hdu (22 + 5 * d)
    (by rw [deriveStage]; omega)
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
  rw [engineFullBadEvent] at hmono hu1 ⊢
  linarith

open Classical in
/-- (3) **THE SAME, WITH THE CONSTANT READ OFF AS THE ADOPTED `combinedBound`.** -/
theorem full_bad_draw_probability_le_engine_tau_combined (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (logLane gateLane : Lane) (d q constraints : Nat) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (engineFullBadEvent L hL e0 strat hb logLane gateLane d (2 ^ d) G coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := full_bad_draw_probability_le_engine_tau L hL e0 strat hb logLane gateLane d q
    (2 ^ d) constraints G coeffsOf hdu hlog hgate hclen
  rw [ChallengeUnionBound.combinedBound]
  exact h

open Classical in
/-- (3) **THE REDUCED-HISTORY PAIRING, WITH THE ENGINE'S OWN TAU EVENT.**  The
adopted `ReducedFullTransport.reduced_full_bad_draw_probability_le` with its
`∀ g` tau event replaced by the diagonal one, at the same constant. -/
theorem reduced_full_bad_draw_probability_le_engine_tau (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (trlog trgate : List Element → List Element) (a1 b1 a2 b2 : Element)
    (hb : StrategyBounded L (strategyOfReduced c s R)) (d q constraints : Nat)
    (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hRlog : ∀ (r : Nat) (xs : List Element), (R r xs).1.length ≤ 5)
    (hRgate : ∀ (r : Nat) (xs : List Element), (R r xs).2.length ≤ q + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (engineFullBadEvent L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
          (logLaneOfReduced R trlog a1 b1) (gateLaneOfReduced R trgate a2 b2)
          d (2 ^ d) G coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  full_bad_draw_probability_le_engine_tau_combined L hL OuterInitial.zeroDigest
    (strategyOfReduced c s R) hb (logLaneOfReduced R trlog a1 b1)
    (gateLaneOfReduced R trgate a2 b2) d q constraints G coeffsOf hdu
    (log_lane_of_reduced_bounded R trlog a1 b1 5 hRlog htrlog)
    (gate_lane_of_reduced_bounded R trgate a2 b2 (q + 2) hRgate htrgate) hclen

/-! ## 4. THE SAME AT RAW LANES -/

open Classical in
/-- **THE RAW-LANE FULL BAD EVENT WITH THE ENGINE'S OWN TAU EVENT.**  The adopted
`RawBlockLanes.rawFullBadEvent` with its `∀ g` tau summand replaced by the
diagonal one. -/
noncomputable def rawEngineFullBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (d rows : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  (rawOuterBadEvent L hL e0 strat hb logLane gateLane d
      ∪ engineTauBadEvent L hL e0 strat hb d G)
    ∪ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf

open Classical in
theorem mem_raw_engine_full_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (d rows : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ rawEngineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf ↔
      (T ∈ rawOuterBadEvent L hL e0 strat hb logLane gateLane d ∨
        T ∈ engineTauBadEvent L hL e0 strat hb d G ∨
        T ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf) := by
  simp only [rawEngineFullBadEvent, Finset.mem_union, or_assoc]

open Classical in
/-- (4) **THE ADOPTED RAW-LANE FULL EVENT IS THE CONSTANT-ALPHA SLICE OF THIS
ONE.**  The section-3 statement `engine_full_bad_event_constant_slice` at raw
lanes: set for set, on the nose. -/
theorem raw_engine_full_bad_event_constant_slice (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (logLane gateLane : RawLane) (d rows : Nat) (g : Nat → Element)
    (coeffsOf : Nat → List Element) :
    rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
      = rawEngineFullBadEvent L hL e0 strat hb logLane gateLane d rows (fun _ => g) coeffsOf :=
  rfl

open Classical in
/-- (4) **THE RAW OUTER, ENGINE-TAU AND ALPHA MASSES AT AN ARBITRARY CONDITIONING
STAGE AT OR BEYOND THE ROUNDS.**  Isolated so that section 5 can add the index
summand under ONE complement term, exactly as the adopted
`RawIndexLanes.raw_full_no_clash_mass_le` does for the `∀ g` tau event. -/
theorem raw_engine_full_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (d q rows constraints : Nat) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) (n : Nat)
    (hn : deriveStage ≤ n) (hrn : ∀ r, r < d → roundStage r ≤ n) :
    oracleProbability (boundedQueries L)
        (rawEngineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf
          ∩ stageNoClash L hL e0 strat hb n)
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints := by
  have hnest : stageNoClash L hL e0 strat hb n
      ⊆ stageNoClash L hL e0 strat hb deriveStage :=
    stage_no_clash_mono L hL e0 strat hb deriveStage n hn
  have hu3 := ReducedEngineIndex.inter_union_mass_le L
    (rawOuterBadEvent L hL e0 strat hb logLane gateLane d
      ∪ engineTauBadEvent L hL e0 strat hb d G)
    (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf)
    (stageNoClash L hL e0 strat hb n)
  have hu4 := ReducedEngineIndex.inter_union_mass_le L
    (rawOuterBadEvent L hL e0 strat hb logLane gateLane d)
    (engineTauBadEvent L hL e0 strat hb d G)
    (stageNoClash L hL e0 strat hb n)
  have houter := raw_no_clash_mass_le L hL e0 strat hb logLane gateLane hlcau hgcau 5 (q + 2)
    hlog hgate n d hrn
  rw [round_terms_sum d q] at houter
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
  rw [rawEngineFullBadEvent]
  linarith

open Classical in
/-- (4) **THE RAW-LANE FULL BOUND WITH THE ENGINE'S OWN TAU EVENT.** -/
theorem raw_full_bad_draw_probability_le_engine_tau (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (logLane gateLane : RawLane) (hlcau : RawLaneCausal logLane)
    (hgcau : RawLaneCausal gateLane) (d q rows constraints : Nat)
    (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawEngineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf)
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (rawEngineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf)
      (stageNoClash L hL e0 strat hb (22 + 5 * d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (rawEngineFullBadEvent L hL e0 strat hb logLane gateLane d rows G coeffsOf
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
  have hfull := raw_engine_full_no_clash_mass_le L hL e0 strat hb logLane gateLane hlcau hgcau
    d q rows constraints G coeffsOf hdu hlog hgate hclen (22 + 5 * d)
    (by rw [deriveStage]; omega) (fun r hr => round_stage_le r d hr)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
      ≤ ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL e0 strat hb (22 + 5 * d)
  linarith

open Classical in
/-- (4) **THE SAME, AS THE ADOPTED `combinedBound`.** -/
theorem raw_full_bad_draw_probability_le_engine_tau_combined (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (logLane gateLane : RawLane) (hlcau : RawLaneCausal logLane)
    (hgcau : RawLaneCausal gateLane) (d q constraints : Nat) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawEngineFullBadEvent L hL e0 strat hb logLane gateLane d (2 ^ d) G coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := raw_full_bad_draw_probability_le_engine_tau L hL e0 strat hb logLane gateLane
    hlcau hgcau d q (2 ^ d) constraints G coeffsOf hdu hlog hgate hclen
  rw [ChallengeUnionBound.combinedBound]
  exact h

open Classical in
/-- (4) **THE RAW-STRATEGY PAIRING, WITH THE ENGINE'S OWN TAU EVENT.**  The adopted
`RawBlockLanes.strategic_raw_full_bad_draw_probability_le` with the diagonal tau
event, at the same constant: the strategy is `strategicShape c s S` for an
arbitrary `RoundCausal S` and the two outer lanes are ITS OWN. -/
theorem strategic_raw_full_bad_draw_probability_le_engine_tau (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hb : StrategyBounded L (strategicShape c s S))
    (trlog trgate : Nat → (Nat → Nat → Block) → List Element)
    (htrlog : RawCausal trlog) (htrgate : RawCausal trgate)
    (a1 b1 a2 b2 : Element) (d q constraints : Nat) (G : Element → Nat → Element)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (trlog r ch).length ≤ 5)
    (hlengate : ∀ (r : Nat) (ch : Nat → Nat → Block), (trgate r ch).length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawEngineFullBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (rawLogLaneOfStrategy S trlog a1 b1) (rawGateLaneOfStrategy S trgate a2 b2)
          d (2 ^ d) G coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  raw_full_bad_draw_probability_le_engine_tau_combined L hL OuterInitial.zeroDigest
    (strategicShape c s S) hb (rawLogLaneOfStrategy S trlog a1 b1)
    (rawGateLaneOfStrategy S trgate a2 b2)
    (raw_log_lane_causal S hS trlog htrlog a1 b1)
    (raw_gate_lane_causal S hS trgate htrgate a2 b2)
    d q constraints G coeffsOf hdu
    (raw_log_lane_bounded S trlog a1 b1 5 hSlog hlenlog)
    (raw_gate_lane_bounded S trgate a2 b2 (q + 2) hSgate hlengate) hclen

/-! ## 5. THE BRIDGE TO THE ADOPTED ENGINE INDEX EVENT -/

open Classical in
/-- **THE RAW FULL EVENT WITH THE ENGINE'S OWN TAU EVENT AND THE ENGINE'S OWN
INDEX EVENT.**  TWO of the four families are the engine's own here; the outer and
alpha summands are the `∀`-lane forms.  READ HONESTY (iv). -/
noncomputable def rawEngineFullIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (logLane gateLane : RawLane)
    (rows : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) :
    Finset (OracleTable (boundedQueries L)) :=
  rawEngineFullBadEvent L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
      hbE logLane gateLane d rows G coeffsOf
    ∪ RawIndexLanes.rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS
        cellIndex cols

open Classical in
/-- (5) **THE ADOPTED REBUILT UNION IS THE CONSTANT-ALPHA SLICE OF THIS ONE.**  At
a constant alpha-to-table map the union of section 5 IS the adopted
`RawIndexLanes.rawFullEngineIndexBadEvent`, set for set, on the nose.  So the
adopted `RawIndexLanes.raw_engine_index_bad_draw_probability_le` and its closed
instances are statements about `rawEngineFullIndexBadEvent … (fun _ => g) …` and
about nothing else. -/
theorem raw_engine_full_index_bad_event_constant_slice (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (logLane gateLane : RawLane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    rawEngineFullIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logLane gateLane
        rows (fun _ => g) coeffsOf cellIndex cols
      = RawIndexLanes.rawFullEngineIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS
          logLane gateLane rows g coeffsOf cellIndex cols :=
  rfl

open Classical in
/-- (5) **THE FIRST BOUND IN THIS TREE ON THE ENGINE'S OWN TAU EVENT TOGETHER WITH
THE ENGINE'S OWN INDEX EVENT.**  For EVERY `RoundCausal S`, EVERY `ClaimsCausal d U`
and EVERY alpha-to-table map `G`:

  `<= combinedBound d q d constraints + 2 tauTerm c.indexBits + clash at 22 + 5 d + 8`.

WHICH FAMILIES ARE THE ENGINE'S OWN: TAU (diagonal in the alpha cell, this
module) and INDEX (the adopted `RawIndexLanes.rawEngineIndexBadEvent`).  The OUTER
summand is the adopted `RawBlockLanes.rawOuterBadEvent` in its `∀`-truth-function,
`∀`-claim form -- NOT the adopted `SoundnessAssembly.outerBadEvent`, whose own
alpha dependence is handled only for the FIXED prover, by the adopted
`TwoStageConditionalCount`, and remains OPEN for the adaptive line.  The ALPHA
summand is the `∀ rows, ∀ coeffsOf` form.  READ HONESTY (iii), (iv), (v), (vi). -/
theorem raw_engine_full_bad_draw_probability_le (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat) (hU : RawIndexLanes.ClaimsCausal d U)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdeg : c.degreeBits = d)
    (hdb : c.degreeBits ≤ 13) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (q constraints : Nat) (G : Element → Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawEngineFullIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logLane
          gateLane (2 ^ d) G coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((ReducedIndexLanes.indexStage d : Nat) : ℚ)
            * (((ReducedIndexLanes.indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have heq : rawEngineFullIndexBadEvent gdec hash khash P c₀ L hL c s S U d hbE hbS logLane
        gateLane (2 ^ d) G coeffsOf cellIndex cols
      = rawEngineFullBadEvent L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S U d) hbE logLane gateLane d (2 ^ d) G coeffsOf
        ∪ RawIndexLanes.rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
            (ReducedEngineIndex.committedOf cols cellIndex) := by
    rw [rawEngineFullIndexBadEvent, RawIndexLanes.raw_engine_index_bad_event_eq gdec hash khash
      P c₀ L hL c s S hS U d hU hbE hbS hdeg hdb cellIndex cols]
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (rawEngineFullBadEvent L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S U d) hbE logLane gateLane d (2 ^ d) G coeffsOf
        ∪ RawIndexLanes.rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
            (ReducedEngineIndex.committedOf cols cellIndex))
      (stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
        hbE (ReducedIndexLanes.indexStage d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    ((rawEngineFullBadEvent L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S U d) hbE logLane gateLane d (2 ^ d) G coeffsOf
        ∪ RawIndexLanes.rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
            (ReducedEngineIndex.committedOf cols cellIndex))
      ∩ stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
          hbE (ReducedIndexLanes.indexStage d))
    ((stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
      hbE (ReducedIndexLanes.indexStage d))ᶜ)
  have hs1 := ReducedEngineIndex.inter_union_mass_le L
    (rawEngineFullBadEvent L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S U d) hbE logLane gateLane d (2 ^ d) G coeffsOf)
    (RawIndexLanes.rawIndexBadEvent L hL c s S U d c.indexBits hbE cellIndex
      (ReducedEngineIndex.committedOf cols cellIndex))
    (stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
      hbE (ReducedIndexLanes.indexStage d))
  have hfull := raw_engine_full_no_clash_mass_le L hL OuterInitial.zeroDigest
    (RawIndexLanes.rawExtendedShape c s S U d) hbE logLane gateLane hlcau hgcau d q (2 ^ d)
    constraints G coeffsOf hdu hlog hgate hclen (ReducedIndexLanes.indexStage d)
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

/-! ## 6. A GENUINELY MOVING TARGET, AND THE CLOSED INSTANCE -/

/-- The engine's own alpha-to-table map: the adopted
`ZeroCheckSemantics.gateValue` at the adopted `Integrated.gateConfig`, with the
alpha argument LEFT FREE.  The adopted `SoundnessAssembly.outerBadEvent`'s zero
check table is this map applied to the adopted
`TranscriptProvenance.gateAlphaElement`. -/
def engineGate (c : Verifier.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (tables : GateSuffixPolynomial.Tables) :
    Element → Nat → Element :=
  fun a => ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash a tables

/-- (6) **THE ENGINE'S TABLE IS THIS MAP AT THE DRAWN ALPHA**, by definition: the
`g` of the adopted `SoundnessAssembly.outerBadEvent` and the adopted
`JointChallengeSpace.runBadEvent`. -/
theorem engine_gate_at_the_drawn_alpha (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (tables : GateSuffixPolynomial.Tables) :
    engineGate c gates publicHash tables (TranscriptProvenance.gateAlphaElement thash c p)
      = ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash
          (TranscriptProvenance.gateAlphaElement thash c p) tables := rfl

/-- (6) **AT THE ADOPTED SURVEY CONFIGURATION** the map is the adopted
`GateDenseRound.exampleConfig`'s, by the adopted
`CommitmentOrderSurvey.survey_gate_config`. -/
theorem engine_gate_at_survey_config (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (tables : GateSuffixPolynomial.Tables) (a : Element) :
    engineGate CommitmentOrderSurvey.surveyConfig gates publicHash tables a
      = ZeroCheckSemantics.gateValue GateDenseRound.exampleConfig gates publicHash a tables := by
  rw [engineGate, CommitmentOrderSurvey.survey_gate_config]

/-- (6) **THE ALPHA CELL THIS MODULE READS IS THE ENGINE'S OWN ALPHA, AT THE PROOF
THE PROVER ACTUALLY SUBMITS.**  This is the load-bearing identification, and it is
PROVED, not assumed: at the adopted `RawBlockLanes.strategicShape` with an
arbitrary `RoundCausal S`, the cell `alphaRead` reads at the derive digest IS the
adopted `TranscriptProvenance.gateAlphaElement` at the TABLE'S OWN hash and at the
adopted `RunLevelTransportAudit.realizedRunProof` -- the table-dependent proof the
strategic prover submits at that very table.  Route: the adopted
`RunLevelTransportAudit.realized_draw_is_actual_digest_draw` at the `gateAlpha`
coordinate (the adopted `realized_draw_gate_alpha`), then the adopted
`OuterInitial.gate_alpha_follows_log_tau` for the adopted
`TranscriptProvenance.derived`. -/
theorem alpha_read_is_gate_alpha_element (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (T : OracleTable (boundedQueries L)) :
    alphaRead L hL OuterInitial.zeroDigest (strategicShape c s S) hb c.degreeBits T
      = TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hb c.degreeBits T) := by
  have h := congrFun (RunLevelTransportAudit.realized_draw_is_actual_digest_draw L hL c s S hb hS T)
    JointChallengeSpace.Draw.gateAlpha
  rw [RunLevelTransportAudit.realized_draw_gate_alpha] at h
  rw [alphaRead, h, TranscriptProvenance.gateAlphaElement, TranscriptProvenance.derived,
    OuterInitial.gate_alpha_follows_log_tau]
  rfl

open Classical in
/-- (6) **HENCE THIS MODULE'S EVENT AT `engineGate` IS THE ENGINE'S OWN GATE-TAU
EVENT AT THE REALIZED PROOF**, set for set.  The target is
`ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash
(TranscriptProvenance.gateAlphaElement (hashOf T) c (realizedRunProof … T)) tables`
-- the adopted `SoundnessAssembly.outerBadEvent`'s zero-check table with `tables`
the one remaining unidentified argument.  READ HONESTY (iii). -/
theorem engine_tau_event_at_realized_alpha (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (tables : GateSuffixPolynomial.Tables) :
    engineTauBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb c.degreeBits
        (engineGate c gates publicHash tables)
      = Finset.univ.filter (fun T =>
          tauRead L hL OuterInitial.zeroDigest (strategicShape c s S) hb c.degreeBits T
            ∈ ChallengeUnionBound.productEvent c.degreeBits
              (ZeroCheckSemantics.zeroCheckBadSet c.degreeBits
                (ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash
                  (TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
                    (RunLevelTransportAudit.realizedRunProof L hL c s S hb c.degreeBits T))
                  tables))) := by
  rw [engineTauBadEvent]
  refine Finset.filter_congr (fun T _ => ?_)
  rw [engineGate, alpha_read_is_gate_alpha_element L hL c s S hb hS T]

/-- (6) **THE SAME AT THE SECTION-5 PROVER.**  The adopted
`RawIndexLanes.rawExtendedShape` agrees with `strategicShape` below `22 + 5 d` in
the adopted `ReducedEngineIndex.AgreeBelow` sense, and the derive digest is stage
`22`, so the adopted `ReducedEngineIndex.stage_triple_of_agree` carries the alpha
triple across; the proof is the SAME realized run proof, the extra claim frames
being strictly later than every stage the alpha cell is read at. -/
theorem raw_extended_alpha_read_is_gate_alpha_element (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    alphaRead L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d) hbE
        c.degreeBits T
      = TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
          (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) := by
  rw [alphaRead, ReducedEngineIndex.stage_triple_of_agree L hL OuterInitial.zeroDigest
    (RawIndexLanes.rawExtendedShape c s S U d) (strategicShape c s S) hbE hbS (22 + 5 * d)
    (RawIndexLanes.raw_extended_agrees_below c s S U d) T deriveStage (alphaBase c.degreeBits)
    (by rw [deriveStage]; omega)]
  exact alpha_read_is_gate_alpha_element L hL c s S hbS hS T

open Classical in
/-- (6) **AND THE SECTION-5 EVENT AT `engineGate` IS THE ENGINE'S OWN**, set for
set, at the SAME realized proof. -/
theorem raw_extended_engine_tau_event_at_realized_alpha (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (tables : GateSuffixPolynomial.Tables) :
    engineTauBadEvent L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d)
        hbE c.degreeBits (engineGate c gates publicHash tables)
      = Finset.univ.filter (fun T =>
          tauRead L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d) hbE
              c.degreeBits T
            ∈ ChallengeUnionBound.productEvent c.degreeBits
              (ZeroCheckSemantics.zeroCheckBadSet c.degreeBits
                (ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash
                  (TranscriptProvenance.gateAlphaElement (hashOf (boundedQueries L) T) c
                    (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T))
                  tables))) := by
  rw [engineTauBadEvent]
  refine Finset.filter_congr (fun T _ => ?_)
  rw [engineGate,
    raw_extended_alpha_read_is_gate_alpha_element L hL c s S hS U d hbE hbS T]

/-- (6) **THE PUBLIC-HASH ARGUMENT IS NOT A SECOND GAP.**  The adopted
`SoundnessAssembly.outerBadEvent` forms its `publicHash` as
`GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs)`, and
the adopted `RunLevelTransportAudit.realizedProof` copies the STATEMENT's public
inputs, so at the realized run proof that argument is a function of `E` and `s`
alone -- table-independent and prover-independent.  What is left unidentified in
the engine's zero-check table is therefore `tables` only. -/
theorem engine_public_hash_is_the_statement_public_hash (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) (E : Verifier.Engine) :
    GateTerminalBinding.publicHashFunction (E.publicInputsHash
        (RunLevelTransportAudit.realizedRunProof L hL c s S hb N T).publicInputs)
      = GateTerminalBinding.publicHashFunction (E.publicInputsHash s.publicInputs) := rfl

open Classical in
/-- A map from the alpha cell to a gate value table that GENUINELY MOVES: at
alpha `0` the table is identically zero, at every other alpha it is the adopted
`ZeroCheckSemantics.exampleValues`. -/
noncomputable def sampleGate : Element → Nat → Element :=
  fun a => if a = 0 then (fun _ => 0) else ZeroCheckSemantics.exampleValues

open Classical in
theorem sample_gate_at_zero : sampleGate 0 = (fun _ => (0 : Element)) := by
  rw [sampleGate, if_pos rfl]

open Classical in
theorem sample_gate_at_one : sampleGate 1 = ZeroCheckSemantics.exampleValues := by
  rw [sampleGate, if_neg (one_ne_zero)]

open Classical in
/-- (6) **THE ENGINE'S TAU TARGET GENUINELY DEPENDS ON THE ALPHA CELL.**  At
`sampleGate` the adopted `ZeroCheckSemantics.zeroCheckBadSet 1` is EMPTY at alpha
`0` (the table is cube-zero) and INHABITED at alpha `1` (the adopted
`ZeroCheckSemantics.example_bad_set_nonempty`).  So the diagonal of section 2 is
not a disguised constant-target statement: the set the tau column is tested
against really does move with the answer at counter `alphaBase 1`. -/
theorem engine_tau_target_depends_on_alpha :
    ZeroCheckSemantics.zeroCheckBadSet 1 (sampleGate 0)
      ≠ ZeroCheckSemantics.zeroCheckBadSet 1 (sampleGate 1) := by
  have hzero : ZeroCheckSemantics.zeroCheckBadSet 1 (sampleGate 0) = ∅ := by
    rw [sample_gate_at_zero]
    exact ZeroCheckSemantics.zeroCheckBadSet_empty 1 (fun _ => (0 : Element)) (fun _ _ => rfl)
  have hone : (ZeroCheckSemantics.zeroCheckBadSet 1 (sampleGate 1)).Nonempty := by
    rw [sample_gate_at_one]
    exact ZeroCheckSemantics.example_bad_set_nonempty
  intro h
  rw [← h, hzero] at hone
  exact Finset.not_nonempty_empty hone

open Classical in
/-- (6) **AND THE MAP ITSELF IS NOT CONSTANT.** -/
theorem sample_gate_not_constant : sampleGate 0 ≠ sampleGate 1 := by
  intro h
  have h1 : (sampleGate 0) 1 = (sampleGate 1) 1 := congrFun h 1
  rw [sample_gate_at_zero, sample_gate_at_one] at h1
  exact ZeroCheckSemantics.example_value_nonzero h1.symm

open Classical in
/-- (6) **THE CLOSED INSTANCE AT THE ENVELOPE'S THIRTEEN COUPLED ROUNDS, WITH A
NON-CONSTANT ALPHA-TO-TABLE MAP.**  Neither the length budget nor the counter
budget is left as a hypothesis, and the constant is the adopted
`ChallengeUnionBound.combinedBound 13 8 13 123` plus the adopted `3828 / |Block|` --
identical to the adopted `ReducedFullTransport.reduced_full_bound_at_thirteen`,
which is the CONSTANT-ALPHA SLICE of this statement.  READ HONESTY (v). -/
theorem reduced_engine_full_bound_at_thirteen (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage)
    (trlog trgate : List Element → List Element) (a1 b1 a2 b2 : Element)
    (coeffsOf : Nat → List Element)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (engineFullBadEvent L (Nat.le_trans (by omega) hLq) OuterInitial.zeroDigest
          (strategyOfReduced c s (previousChallengeMessage m))
          (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
            (previous_challenge_message_log_length m 5 hmlog)
            (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
          (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
          (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2)
          13 (2 ^ 13) sampleGate coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) := by
  have h := reduced_full_bad_draw_probability_le_engine_tau L (Nat.le_trans (by omega) hLq) c s
    (previousChallengeMessage m) trlog trgate a1 b1 a2 b2
    (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
      (previous_challenge_message_log_length m 5 hmlog)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
    13 8 123 sampleGate coeffsOf thirteen_counter_budget
    (previous_challenge_message_log_length m 5 hmlog)
    (previous_challenge_message_gate_length m (8 + 2) hmgate) htrlog htrgate hclen
  have harith : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  rw [harith] at h
  exact h

/-- (6) **AND THE CLOSED CONSTANT IS STRICTLY BELOW `1`**, by the adopted
`ReducedFullTransport.reduced_full_bound_at_thirteen_lt_one`: the constant is the
same one, because the diagonal costs nothing.  READ HONESTY (v): THIS IS NOT THE
PROTOCOL'S SOUNDNESS ERROR. -/
theorem reduced_engine_full_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) < 1 :=
  reduced_full_bound_at_thirteen_lt_one

/-- (6) **THE HYPOTHESES OF SECTION 6 ARE SATISFIABLE**, so the closed instance is
not vacuous: the counter budget holds at thirteen coupled rounds (the adopted
`ReducedFullTransport.thirteen_counter_budget`) and the coefficient-length budget
is met by the empty coefficient family, the same witness the adopted
`ChallengeUnionBound` closed instances use. -/
theorem closed_instance_hypotheses_satisfiable :
    (12 + 6 * 13 < Transcript.u64Limit) ∧
      (∀ i, i < 2 ^ 13 → ((fun _ => ([] : List Element)) i).length ≤ 123) :=
  ⟨thirteen_counter_budget, fun _ _ => Nat.zero_le _⟩

open Classical in
/-- (6) **THE CLOSED INSTANCE OF THE SECTION-5 HEADLINE.**  The adopted
`RawIndexLanes.raw_index_engine_bound_at_thirteen`'s own closed setting -- thirteen
coupled rounds, `quotientDegree = 8`, `numGateConstraints = 123`, `indexBits = 8`,
the adopted genuinely raw `StrategyChainBound.challengeTruncatedMessage` as the
round-message choice and the adopted `RawIndexLanes.blockClaims u0 u1` as the
used-claims choice -- now carrying THE ENGINE'S OWN TAU EVENT at the NON-CONSTANT
`sampleGate` instead of the adopted `∀ g` one, at the SAME constant:

  `<= combinedBound 13 8 13 123 + 2 * tauTerm 8 + 4560 / |Block|`.

Neither `StrategyBounded` nor `64 <= L` nor either counter budget is left as a
hypothesis.  READ HONESTY (iii), (iv), (v), (vi): THIS IS NOT THE SYSTEM'S
SOUNDNESS ERROR. -/
theorem raw_engine_full_index_bound_at_thirteen (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage) (u0 u1 : Verifier.UsedClaims)
    (W : Nat) (a1 b1 a2 b2 : Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
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
        (rawEngineFullIndexBadEvent gdec hash khash P c₀ L (Nat.le_trans (by omega) hLq) c s
          (challengeTruncatedMessage m) (RawIndexLanes.blockClaims u0 u1) 13
          (RawIndexLanes.truncated_raw_extended_bounded L c s m
            (RawIndexLanes.blockClaims u0 u1) W hpre hmlog hmgate
            (RawIndexLanes.block_claims_bounded u0 u1 W h0 h1) hLq hLW hdom)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
          (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a1 b1)
          (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a2 b2)
          (2 ^ 13) sampleGate coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 2 * ChallengeUnionBound.tauTerm 8 + 4560 / (Fintype.card Block : ℚ) := by
  have h := raw_engine_full_bad_draw_probability_le gdec hash khash P c₀ L
    (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
    (challenge_truncated_round_causal m) (RawIndexLanes.blockClaims u0 u1) 13
    (RawIndexLanes.block_claims_causal u0 u1 13)
    (RawIndexLanes.truncated_raw_extended_bounded L c s m (RawIndexLanes.blockClaims u0 u1) W
      hpre hmlog hmgate (RawIndexLanes.block_claims_bounded u0 u1 W h0 h1) hLq hLW hdom)
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
    hc13 (by omega)
    (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a1 b1)
    (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a2 b2)
    (raw_log_lane_causal (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
      rawZeroTruth raw_zero_truth_causal a1 b1)
    (raw_gate_lane_causal (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
      rawZeroTruth raw_zero_truth_causal a2 b2)
    8 123 sampleGate coeffsOf cellIndex cols thirteen_counter_budget
    (by rw [hcidx]; exact ReducedIndexLanes.eight_index_counter_budget)
    (raw_log_lane_bounded (challengeTruncatedMessage m) rawZeroTruth a1 b1 5
      (fun r ch => by
        rw [(challenge_truncated_message_lengths m r ch).1]
        exact hmlog)
      (raw_zero_truth_length 5))
    (raw_gate_lane_bounded (challengeTruncatedMessage m) rawZeroTruth a2 b2 (8 + 2)
      (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
      (raw_zero_truth_length (8 + 2))) hclen
  rw [hcidx] at h
  have harith : ((ReducedIndexLanes.indexStage 13 : Nat) : ℚ)
      * (((ReducedIndexLanes.indexStage 13 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [ReducedIndexLanes.index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

/-- (6) **AND THAT CLOSED CONSTANT IS STRICTLY BELOW `1`**, inherited verbatim from
the adopted `RawIndexLanes.raw_index_engine_bound_at_thirteen_lt_one`: the diagonal
costs nothing.  READ HONESTY (v). -/
theorem raw_engine_full_index_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) < 1 :=
  RawIndexLanes.raw_index_engine_bound_at_thirteen_lt_one

open Classical in
/-- (6) **TESTED AT THE CONSTANT TABLE.**  At a constant alpha-to-table map the
whole of section 3 collapses, set for set, to the adopted
`ReducedFullTransport` statement, so nothing above is a strengthening that only a
moving target could satisfy. -/
theorem engine_bound_at_constant_table (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
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
  rw [engine_full_bad_event_constant_slice]
  exact full_bad_draw_probability_le_engine_tau_combined L hL e0 strat hb logLane gateLane
    d q constraints (fun _ => g) coeffsOf hdu hlog hgate hclen

end Audit.Wire3.EngineTauDiagonal
