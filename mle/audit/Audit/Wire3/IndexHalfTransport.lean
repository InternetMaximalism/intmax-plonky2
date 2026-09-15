import Audit.Wire3.AdaptiveAssemblyFailure
import Audit.Wire3.EngineOuterDiagonal
import Audit.Wire3.RawIndexLanes
import Audit.Wire3.ReducedEngineIndex
import Audit.Wire3.ReducedIndexLanes
import Audit.Wire3.RunLevelTransportAudit
import Audit.Wire3.SoundnessAssembly

/-!
# THE INDEX HALF, TRANSPORTED: ONE CONSTANT FOR THE ADAPTIVE ASSEMBLY FAILURE

## THE GAP THIS MODULE CLOSES -- READ THIS FIRST

The adopted `AdaptiveAssemblyFailure` proved, for every transcript-restricted causal
prover and with NO hypothesis, that the adaptive assembly-failure event is contained in
the engine's own outer bad event union the engine's own INDEX bad event, and it weighed
the first half.  Under "WHAT REMAINS `∀`-QUANTIFIED OR ASSUMED" its header named exactly
one leg it did not close:

> THE INDEX HALF'S MASS.  The adopted `RawIndexLanes` weighs the index event at the
> adopted `rawRealizedRun` -- the EXTENDED-shape chain, a proof record differing from
> `realizedRunProof` in its `used` field.  This module therefore carries the index term
> as an unevaluated `oracleProbability` and states NO bound for it.  THAT IS THE ONE
> STEP STILL OWED for a single-constant adaptive payoff, and it is a transport between
> two proof records at one strategy, not a new probabilistic argument.

Sections 1 to 4 do exactly that, and nothing more: the index term becomes
`2 * tauTerm c.indexBits`, and the two halves' clash terms become ONE.

## HOW THE SHAPE GAP CLOSES, AND WHY IT IS CHEAP -- OPTION (a)

The adopted `SoundnessAssembly.actualIndexDraw thash c p` reads `p` through the
concreteFinal snapshot of the round messages, and the adopted
`SoundnessAssembly.indexBadEvent`'s supplied cells come from `boundCell p.used ...`
while its committed cells come from `cellRow (derivedRounds ...)`.  So the adopted
`AdaptiveAssemblyFailure.adaptiveIndexBadEvent` (at `realizedRunProof`) and the adopted
`RawIndexLanes.rawEngineIndexBadEvent` (at `rawRealizedRun`) coincide as soon as the two
proof records' `used` fields agree -- everything else is already the same list of
messages.

And the `used` field of `realizedRunProof` is a CONSTANT.  The adopted `realizedProof`
builds its record from `Verifier.testProof` and overrides every field the outer chain
reads, leaving `used` untouched; `realized_run_proof_used` states that in one line.  So
the used-claims choice that reproduces `realizedRunProof` is
`constantClaims defaultClaims`, the adopted `RawIndexLanes.ClaimsCausal` condition holds
for it trivially, and `raw_realized_run_is_realized_run_proof` is a proof-record identity
(`rfl`).  Option (b) -- restating the adopted `AdaptiveAssemblyFailure` sections 1 to 3
over `rawExtendedShape` -- was NOT needed and is not attempted.

THE ONE THING THAT DID NEED WORK is that the outer half is proved at the STRATEGIC chain
and the index half at the RAW EXTENDED chain, so their no-clash conditioning events are
events of different chains.  Section 2 shows the two chains make the SAME frame queries
below stage `22 + 5 d` (the adopted `ReducedEngineIndex.strat_hist_of_agree` plus the
adopted `RawIndexLanes.raw_extended_agrees_below`), hence have the same no-clash event
there, hence the extended chain's no-clash event at `indexStage d` sits INSIDE the
strategic chain's at `22 + 5 d`.  One clash term pays for both halves, exactly as the
adopted `EngineOuterDiagonal.raw_engine_all_own_bad_draw_probability_le` pays once for
its four families.  NO SECOND CLASH TERM IS ADDED ANYWHERE BELOW.

## WHAT IS PROVED

0. `constantClaims` / `defaultClaims`, their `ClaimsCausal` and width budgets, and
   `constant_claims_extended_bounded` -- the extended chain's length budget discharged
   FROM the strategic chain's own, with no `hpre`/`hSlog`/`hSgate` of its own.
1. `realized_run_proof_used`, `raw_realized_run_is_realized_run_proof`, and
   `adaptive_index_bad_event_is_raw_engine_index_bad_event` -- the two index events are
   the same `Finset`.
2. `strategy_sel_of_agree`, `stage_no_clash_of_agree`, `raw_extended_no_clash_subset`.
3. `adaptive_index_half_mass_le`:
   `<= 2 * tauTerm c.indexBits + (indexStage d)(indexStage d + 1)/2/|Block|`.
4. `adaptive_assembly_failure_mass_le_single_constant`:
   `<= combinedBound d q d constraints + 2 * tauTerm c.indexBits
       + (indexStage d)(indexStage d + 1)/2/|Block|` -- ONE constant, ONE clash term.
5. `adaptive_assembly_bound_at_thirteen` (a closed instance with no `StrategyBounded`,
   no `64 <= L` and no counter budget left as a hypothesis),
   `adaptive_single_constant_at_thirteen_lt_one` (`< 1`), and
   `adaptive_single_constant_hypotheses_satisfiable`.
6. THE FIVE-CELL FORM.  The adopted `SoundnessAssembly.explicit_good_draw_assembly` takes
   its index hypothesis `hidx` at ONE `cellIndex` and concludes the cell identity at that
   same `cellIndex`, so the adopted `adaptiveAssemblyFailureEvent` is a PER-CELL event and
   no five-cell union is forced by the statement.  The union over the five bound cells is
   nevertheless the event that SOME cell's assembly conclusion fails, and it is bounded
   here by `combinedBound 13 8 13 123 + 5 (2 tauTerm 8) + 4560/|Block|`, still `< 1`,
   still one clash term.
7. THE USED CLAIMS MADE A PARAMETER, AND THE LENGTH OBSTRUCTION REMOVED (sections 0b and
   1b).  `realizedRunProofWith u` is the adopted `ReducedEngineIndex.realizedUsedProof` at
   the adopted `StrategyChainBound.realizedMessages`: the SAME statement and the SAME
   table-dependent round messages as the adopted
   `RunLevelTransportAudit.realizedRunProof`, with the used claims a PARAMETER.  At
   `defaultClaims` it is that adopted record on the nose; at `constantClaims u` it is the
   adopted `RawIndexLanes.rawRealizedRun` on the nose; and the adopted
   `SoundnessAssembly.outerBadEvent` / `actualDigestDraw` do not move with `u` at all
   (`outer_bad_event_at_claims`), so the outer summand is the adopted one unchanged.
   `adaptiveIndexBadEventWith`, `adaptiveAssemblyFailureEventWith` and
   `adaptiveAllCellsFailureEventWith` mirror the adopted event definitions VERBATIM at that
   record, and the whole chain of 1 to 6 is restated at a general `u` (`…_at_claims`), the
   fixture statements kept as corollaries.  `matchingClaims c` is the used-claims record
   whose five lists have the lengths the adopted `Verifier.shape` demands at `c`, and
   `shape_satisfiable_at_matching_claims` proves those five conjuncts;
   `adaptive_assembly_bound_at_thirteen_at_matching_claims` and
   `adaptive_all_cells_bound_at_thirteen_at_matching_claims` are the closed instances
   there.  THIS REMOVES A LENGTH OBSTRUCTION; IT DOES NOT EXHIBIT ACCEPTANCE -- see the
   vacuity bullet below.
8. THE VACUITY OF THE FIXTURE INSTANTIATION, RECORDED AS THEOREMS:
   `shape_forces_degenerate_config_at_fixture_claims`,
   `acceptance_forces_degenerate_config_at_fixture_claims` and
   `adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`.

## WHAT REMAINS `∀`-QUANTIFIED OR ASSUMED

Nothing below strengthens or weakens any adopted assumption, and no adopted statement is
altered.  Sections 0b and 1b add a `u`-parametric RESTATEMENT of the adopted event
definitions; that is a new statement of this module, not a change to the adopted one.
What the adopted `AdaptiveAssemblyFailure` left assumed is inherited VERBATIM:

* `tables = s0.tables` -- the committed-tables extraction join, `s0` supplied.  The
  adopted `CommittedTablesClauses` has since DECOMPOSED that join into R1b plus two
  localized collisions; that decomposition is neither used nor strengthened here, and the
  join itself is not discharged anywhere in this tree.
* `coeffsOf` -- a free family.  The adopted
  `CommitmentOrderSurvey.coefficients_are_determined_by_the_tables` makes the alpha
  summand a function of the tables alone only UNDER its own `prefixCoeffTable` premise,
  which is NOT assumed below.
* `logTruths` / `gateTruths` -- the SUPPLIED free truth columns of the adopted
  `SoundnessAssembly.outerBadEvent`; not the engine's derived values.
* R1b -- the adopted honest-openings relation, carried inside the adopted
  `SoundnessAssembly.AssemblyResidue`.  Neither used nor strengthened here.
* ACCEPTANCE IS NEVER EXHIBITED, AND AT THE FIXTURE `used` IT IS IMPOSSIBLE OUTSIDE A
  DEGENERATE CONFIGURATION.  No accepting proof for the explicit engine is produced
  anywhere below; the failure event is a set defined by a NEGATED implication, so it is
  well defined whether or not any table accepts.  BUT WELL DEFINED IS NOT NON-VACUOUS.
  The adopted `AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent`
  (`AdaptiveAssemblyFailure.lean:837-843`) carries acceptance as a CONJUNCT; the adopted
  `Integrated.verify` ends in `Verifier.verify` (`Integrated.lean:59-66`), which rejects
  unless `Verifier.shape pin c p = true` (`Verifier.lean:415`); and `Verifier.shape`
  demands `p.used.logPreprocessed.length = c.numConstants + c.numRouted`,
  `p.used.logWitness.length = c.numWires` and `p.used.logNormInverse.length = 2 *
  c.numRouted` (`Verifier.lean:139-141`).  At the fixture record those lengths are
  `1, 1, 0` (`Verifier.lean:596-600`), forcing `c.numConstants + c.numRouted = 1`,
  `c.numWires = 1` and `c.numRouted = 0`, i.e. `numRouted = 0`, `numConstants = 1`,
  `numWires = 1`.  SO AT EVERY CONFIGURATION WITH `numWires ≠ 1` OR `numRouted ≠ 0` THE
  ADOPTED EVENT IS EMPTY AND THE FIXTURE HEADLINE IS VACUOUSLY TRUE
  (`adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`).  That is a
  property of the FIXTURE instantiation only: the repaired instantiation
  `adaptiveAssemblyFailureEventWith (matchingClaims c)` -- headlined by
  `adaptive_assembly_failure_mass_le_single_constant_at_claims` and closed by
  `adaptive_assembly_bound_at_thirteen_at_matching_claims` -- meets all five of the
  shape gate's used-claim conjuncts at `c` itself
  (`shape_satisfiable_at_matching_claims`), so the acceptance antecedent is no longer
  refuted by length arithmetic there.  BE PRECISE ABOUT WHAT IS AND IS NOT PINNED: at the
  degenerate configuration `Verifier.width c = 1`, so the fixture's
  `constituentWidth := 1` adds no further pin, while `c.degreeBits` and
  `c.numPublicInputs` stay FREE because `logRounds`, `gateRounds` and `publicInputs` ARE
  overridden by the adopted `realizedProof`.  And removing the length obstruction is NOT
  exhibiting acceptance: the remaining shape conjuncts (`protocolVersion`,
  `constituentWidth`, `circuitDigest`, `publicInputs.length`, `preprocessedRoot`, the two
  WHIR length caps, the round-list lengths, the per-round widths) are discharged nowhere
  in this tree, and neither is `Verifier.envelope`.
* THE ADAPTIVE PROVER'S SURVIVING FREEDOM IS THE ROUND MESSAGES AND THE STATEMENT ONLY --
  THE `used` CLAIMS OF THE FIXTURE-LEVEL STATEMENTS ARE A CONSTANT.  `defaultClaims` IS
  `Verifier.testProof.used = ⟨[zero], [zero], [], [zero], [zero]⟩`
  (`Verifier.lean:596-600`), the all-zero fixture record.  The adopted index bad event
  DEPENDS on `p.used` -- its supplied cells are `boundCell (realizedRunProof …).used …` --
  so of the two halves only the DERIVED INDICES half is adaptive at the fixture
  instantiation.  What the adaptive prover still varies there is exactly the coupled round
  messages (through the strategy `S`) and the statement fields
  (`circuitDigest`, `publicInputs`, `preprocessedRoot`, `witnessRoot`, `normInverseRoot`);
  `used`, `whirTranscript`, `whirHints`, `protocolVersion` and `constituentWidth` are
  FIXTURE CONSTANTS.  This is inherited from the adopted
  `RunLevelTransportAudit.realizedProof` (`RunLevelTransportAudit.lean:582-587`), a
  `{ Verifier.testProof with … }` record that overrides only those five statement fields
  and the two round lists.  Its own docstring justifies the fixture by "every theorem
  below reads the proof only through `Verifier.statement` and `roundMessages`" -- a
  premise that is BREACHED from the adopted `AdaptiveAssemblyFailure` onward, where
  `suppliedCellsAt` reads `p.used` and the event asserts full `Integrated.verify`
  acceptance.  Sections 0b and 1b below remove that constant by making `u` a parameter;
  they do NOT remove `whirTranscript`, `whirHints`, `protocolVersion` or
  `constituentWidth` from the fixture.
* THREE HYPOTHESES THIS MODULE ADDS THAT THE ADOPTED `AdaptiveAssemblyFailure` HEADLINE
  DOES NOT HAVE.  `hbE` -- a `StrategyBounded L` for the RAW EXTENDED chain, a second
  chain the adopted headline never mentions (it is discharged in every closed instance by
  `default_claims_extended_bounded` / `matching_claims_extended_bounded`, from the
  strategic chain's own budget).  `hdb : c.degreeBits ≤ 13` -- needed by the adopted
  `RawIndexLanes.raw_engine_index_bad_event_eq`; the adopted headline carries no degree
  ceiling.  `hbu : 6 * c.indexBits ≤ Transcript.u64Limit` -- the index counter budget of
  the adopted `RawIndexLanes.raw_index_bad_event_no_clash_mass_le`.  All three are
  witnessed at the envelope (`adaptive_single_constant_hypotheses_satisfiable`), but they
  are additions, not inheritances.
* WHAT IS NO LONGER CARRIED AS AN UNEVALUATED PROBABILITY: the index term.  Section 4's
  bound is a closed constant with no unevaluated `oracleProbability` in it.  THAT IS A
  STATEMENT ABOUT THE FORM OF THE BOUND ONLY; it discharges none of the assumptions above,
  and it does not make the bounded event non-empty.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`.  Replacing the
deployed permutation by a table drawn from that law is an assumption with no proof
anywhere in this tree.

(ii) THE PROVER CLASS.  TRANSCRIPT-RESTRICTED CAUSAL: every statement below is at the
adopted `RawBlockLanes.strategicShape` for an arbitrary `StrategyChainBound.RoundCausal S`
-- a prover handed the stage digests of its own chain and the oracle's answers at the
CHALLENGE inputs of those digests, making no oracle queries of its own.  GRINDING IS
EXCLUDED by every theorem below.

(iii) THE ENGINE IS EXPLICIT, AT THE REALIZED RUN.  Everything is stated at
`SoundnessAssembly.engine gdec hash (hashOf T) khash P c₀` -- the table's OWN hash -- and
at `RunLevelTransportAudit.realizedRunProof`, or at `realizedRunProofWith u`, which is
that record with the used claims made a parameter.  THE WORD "SUBMITS" IS NOT USED HERE:
this record is a CONSTRUCTED WITNESS whose round messages track the table and whose
remaining fields are the adopted `Verifier.testProof`'s.  It models the round-message and
statement freedom of the transcript-restricted causal prover, and (at `u`) its used
claims; it does NOT model the prover's WHIR behaviour, its `whirTranscript` and
`whirHints` being fixture constants.  Nothing below quantifies a proof outside the law,
and nothing below asserts that any prover's actual submission is this record.

(iv) WHAT IS NOW A SINGLE CONSTANT, AND WHAT IS STILL ASSUMED.  What became a single
constant is the MASS: section 4 has no unevaluated probability in it.  What is still
assumed is listed above: the adopted list -- `tables = s0.tables` (now decomposed by the
adopted `CommittedTablesClauses` into R1b plus two localized collisions, but NOT
discharged), `coeffsOf`'s `prefixCoeffTable` premise, the free truth columns, R1b, and the
fact that acceptance is never exhibited -- PLUS three items that are this module's own:
the fixture constancy of `used` (at the fixture-level statements), `whirTranscript`,
`whirHints`, `protocolVersion` and `constituentWidth`; the emptiness of the adopted event
at every non-degenerate configuration; and the three added hypotheses `hbE`, `hdb` and
`hbu`.

(v) WHAT THE ASSEMBLY CONCLUSION IS.  GOOD-DRAW-CONDITIONAL CONSTRAINT VANISHING ON THE
EXTRACTED TABLES, plus a per-column identification, plus the pinned WHIR parameter row
and the `core c = core c₀` / `KhashCollision` disjunction.  IT IS NOT CIRCUIT TRUTH, and
it is not a satisfiability claim.

(vi) WHIR AND MERKLE ARE EXCLUDED, AND THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.
`combinedBound` covers the outer sumcheck round-agreement events, the gate tau
multilinear zero check and the gate alpha zero check only; the index term covers the
index-lane diagonal.  The WHOLE WHIR/Merkle contribution -- proximity and list decoding,
the query-repetition profile, Merkle collision resistance -- is EXCLUDED, and it is the
dominant term.  Quoting the constant of section 5 as the wire-v3 soundness error would be
wrong by roughly seventy bits.  NOTHING BELOW IS A CLAIM THAT ADAPTIVE FIAT--SHAMIR
SOUNDNESS HAS BEEN PROVED: the Fiat--Shamir half -- that the run's encoding draw is
`JointChallengeSpace.jointProbability`-distributed -- remains exactly as unformalized as
the adopted `JointChallengeSpace.DrawEncodesRun` header says.

(vii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's own text
ONLY in the three mirrored definitions `adaptiveIndexBadEventWith`,
`adaptiveAssemblyFailureEventWith` and `adaptiveAllCellsFailureEventWith`, each a verbatim
transcription of the corresponding adopted `AdaptiveAssemblyFailure` definition with the
used claims made a parameter; every other event named below is an adopted one, and the
adopted ones are themselves `Finset.univ.filter` sets.  No tactic or term
below is ever shown a `Fintype.card` of `Element`, of `Block` or of
`OuterChallenge.DigestTriple` in a reducible position: `Fintype.card Block` enters only as
an ATOM inside the clash term that the adopted
`StrategyChainBound.strategy_chain_clash_probability_le` supplies, and the `linarith`
calls treat the whole quotient as an atom.  `ChallengeUnionBound.combinedBound` and
`tauTerm` are never evaluated; `combinedBound` is unfolded exactly once per headline, to
its three named summands.  No membership over `OuterChallenge.DigestTriple` at a CONCRETE
lane is elaborated anywhere.  `open Classical in` is used for the declarations whose
statements mention `Finset` membership or union over the table space, exactly as the
adopted `RawIndexLanes`, `EngineOuterDiagonal` and `AdaptiveAssemblyFailure` do.  The
closed instances mention `13`, `8`, `123` and `4560` literally, as the adopted
`EngineOuterDiagonal` and `RawIndexLanes` section-11 instances do.
-/


namespace Audit.Wire3.IndexHalfTransport

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.RawBlockLanes
open Audit.Wire3.EngineOuterDiagonal


/-! ## 0. THE CONSTANT USED-CLAIMS CHOICE -/

/-- **A CONSTANT USED-CLAIMS CHOICE.**  The adopted `RawIndexLanes.RawUsedClaims` that
ignores the raw view entirely.  It is a legitimate member of the adopted raw
used-claims class -- the class is `∀`-quantified, so instantiating it at a constant is a
SPECIALISATION of the adopted bound and never a strengthening of it.  BUT A SPECIALISATION
IS A LOSS OF GENERALITY, AND HERE IT COSTS SOMETHING: the resulting claims record is
chosen before the run rather than adaptively, and at `defaultClaims` it is the all-zero
fixture record whose lengths force a degenerate configuration.  Read the header's vacuity
bullet, and prefer `matchingClaims c` to `defaultClaims` when a non-degenerate `c` is in
view. -/
def constantClaims (u : Verifier.UsedClaims) : RawIndexLanes.RawUsedClaims := fun _ => u

/-- **THE USED CLAIMS THE PROOF RECORD OF THE ADOPTED
`RunLevelTransportAudit.realizedRunProof` ACTUALLY CARRIES.**  That record is built
from `Verifier.testProof` by the adopted `realizedProof`, which overrides every field
the outer chain reads and leaves `used` alone; so its `used` field is this constant,
at every table and every strategy (`realized_run_proof_used`). -/
def defaultClaims : Verifier.UsedClaims := Verifier.testProof.used

/-- (0) Its width budget, at `W = 1`: the five lists of `Verifier.testProof.used` have
lengths `1, 1, 0, 1, 1`. -/
theorem default_claims_bounded :
    RawIndexLanes.RawUsedClaimsBounded 1 (constantClaims defaultClaims) :=
  fun _ => ⟨Nat.le_refl 1, Nat.le_refl 1, Nat.zero_le 1, Nat.le_refl 1, Nat.le_refl 1⟩

/-- (0) **`ClaimsCausal` IS SATISFIED TRIVIALLY BY A CONSTANT CHOICE.**  The claims are
chosen before the index digest's cells are squeezed because they are chosen before
anything at all. -/
theorem constant_claims_causal (u : Verifier.UsedClaims) (d : Nat) :
    RawIndexLanes.ClaimsCausal d (constantClaims u) := fun _ _ _ => rfl

/-- (0) **THE LENGTH BUDGET OF THE EXTENDED CHAIN AT A CONSTANT CLAIMS CHOICE,
DISCHARGED FROM THE STRATEGIC CHAIN'S OWN BUDGET.**  Below `22 + 5 d` the extended
shape IS the adopted `StrategyChainBound.strategicShape`, so `hbS` is reused verbatim;
above it the eight frames are the adopted `IndexLanesOracle.claim_shape_payload_bound`.
Unlike the adopted `RawIndexLanes.raw_extended_shape_bounded` this needs no
`hpre`/`hSlog`/`hSgate` of its own. -/
theorem constant_claims_extended_bounded (L W : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (u : Verifier.UsedClaims) (d : Nat)
    (hbS : StrategyBounded L (strategicShape c s S))
    (hU : RawIndexLanes.RawUsedClaimsBounded W (constantClaims u))
    (hLW : 69 + 24 * W ≤ L) (hdom : 86 ≤ L) :
    StrategyBounded L (RawIndexLanes.rawExtendedShape c s S (constantClaims u) d) := by
  intro k h ch
  rw [RawIndexLanes.raw_extended_shape_apply]
  by_cases hk : k < 22 + 5 * d
  · rw [if_pos hk]
    exact hbS k h ch
  · rw [if_neg hk]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hU ch
    exact IndexLanesOracle.claim_shape_payload_bound L W (constantClaims u ch) h1 h2 h3 h4 h5
      hLW hdom (k - (22 + 5 * d))

/-- (0) The same at `defaultClaims`, where `W = 1` makes the two payload budgets a
single `93 ≤ L`. -/
theorem default_claims_extended_bounded (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (d : Nat)
    (hbS : StrategyBounded L (strategicShape c s S)) (hdom : 93 ≤ L) :
    StrategyBounded L (RawIndexLanes.rawExtendedShape c s S (constantClaims defaultClaims) d) :=
  constant_claims_extended_bounded L 1 c s S defaultClaims d hbS default_claims_bounded
    (by omega) (by omega)

/-! ## 0b. THE FIXTURE CLAIMS PIN THE CONFIGURATION, AND A MATCHING CHOICE DOES NOT -/

/-- (0b) **THE SHAPE GATE, READ AT A PROOF WHOSE `used` IS THE FIXTURE RECORD.**  The
adopted `Verifier.shape` (`Verifier.lean:139-141`) asks the three used-claim lists to
have lengths `c.numConstants + c.numRouted`, `c.numWires` and `2 * c.numRouted`.  At
`defaultClaims = Verifier.testProof.used` (`Verifier.lean:596-600`) those lengths are
`1, 1, 0`, so the gate FORCES a degenerate configuration.  This is the reviewer's probe,
promoted to a recorded fact of this tree. -/
theorem shape_forces_degenerate_config_at_fixture_claims (pin : Verifier.Pinned)
    (c : Verifier.Config) (p : Verifier.Proof) (hu : p.used = defaultClaims)
    (hs : Verifier.shape pin c p = true) :
    c.numWires = 1 ∧ c.numRouted = 0 ∧ c.numConstants = 1 := by
  have hlit : defaultClaims
      = ⟨[Verifier.zero], [Verifier.zero], [], [Verifier.zero], [Verifier.zero]⟩ := rfl
  simp only [Verifier.shape, decide_eq_true_eq, hu, hlit, List.length_cons,
    List.length_nil] at hs
  omega

/-- (0b) **THE SAME, STRAIGHT FROM ACCEPTANCE.**  The adopted
`Verifier.verify_success_checks` returns `Verifier.shape` from an accepting run
(`Verifier.lean:415`), and the adopted `Integrated.verify` ends in `Verifier.verify`
(`Integrated.lean:59-66`), so at a proof carrying the fixture used claims ACCEPTANCE
ITSELF is impossible outside the degenerate configuration. -/
theorem acceptance_forces_degenerate_config_at_fixture_claims (e : Verifier.Engine)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hu : p.used = defaultClaims) (hacc : Verifier.verify e pin chain c p = .ok ()) :
    c.numWires = 1 ∧ c.numRouted = 0 ∧ c.numConstants = 1 :=
  shape_forces_degenerate_config_at_fixture_claims pin c p hu
    (Verifier.verify_success_checks e pin chain c p hacc).2.2.2.2.1

/-- (0b) **THE USED-CLAIMS CHOICE WHOSE SHAPE MATCHES A GIVEN CONFIGURATION.**  Five
lists of the lengths the adopted `Verifier.shape` demands at `c`.  The entries are
`Verifier.zero` because NOTHING below reads them: only their LENGTHS enter the shape
gate and the adopted `RawIndexLanes.RawUsedClaimsBounded` width budget. -/
def matchingClaims (c : Verifier.Config) : Verifier.UsedClaims :=
  ⟨List.replicate (c.numConstants + c.numRouted) Verifier.zero,
    List.replicate c.numWires Verifier.zero,
    List.replicate (2 * c.numRouted) Verifier.zero,
    List.replicate (c.numConstants + c.numRouted) Verifier.zero,
    List.replicate c.numWires Verifier.zero⟩

/-- (0b) **THE PAYOFF OF THE REPAIR: THE LENGTH OBSTRUCTION IS GONE.**  At
`matchingClaims c` all five used-claim conjuncts of the adopted `Verifier.shape` hold AT
`c` ITSELF -- in particular the three the fixture record contradicted.  So for a proof
record carrying these claims the acceptance antecedent of the failure event is no longer
impossible by length arithmetic at a configuration with many wires or routed wires.

THIS IS NOT AN EXHIBITION OF ACCEPTANCE.  The remaining shape conjuncts
(`protocolVersion`, `constituentWidth`, `circuitDigest`, `publicInputs.length`,
`preprocessedRoot`, the two WHIR length caps, the round-list lengths and the per-round
widths) are NOT discharged here, and no accepting proof is produced anywhere in this
tree.  What is removed is exactly the arithmetic impossibility. -/
theorem shape_satisfiable_at_matching_claims (c : Verifier.Config) :
    (matchingClaims c).logPreprocessed.length = c.numConstants + c.numRouted ∧
      (matchingClaims c).logWitness.length = c.numWires ∧
      (matchingClaims c).logNormInverse.length = 2 * c.numRouted ∧
      (matchingClaims c).gatePreprocessed.length = c.numConstants + c.numRouted ∧
      (matchingClaims c).gateWitness.length = c.numWires :=
  ⟨List.length_replicate _ _, List.length_replicate _ _, List.length_replicate _ _,
    List.length_replicate _ _, List.length_replicate _ _⟩

/-- (0b) The width budget of the matching choice, at any `W` dominating the three
lengths `c` demands. -/
theorem matching_claims_bounded (c : Verifier.Config) (W : Nat)
    (hcon : c.numConstants + c.numRouted ≤ W) (hwir : c.numWires ≤ W)
    (hrou : 2 * c.numRouted ≤ W) :
    RawIndexLanes.RawUsedClaimsBounded W (constantClaims (matchingClaims c)) := fun _ =>
  ⟨(List.length_replicate _ _).le.trans hcon, (List.length_replicate _ _).le.trans hwir,
    (List.length_replicate _ _).le.trans hrou, (List.length_replicate _ _).le.trans hcon,
    (List.length_replicate _ _).le.trans hwir⟩

/-- (0b) The matching choice's extended-chain length budget, discharged from the
strategic chain's own exactly as `default_claims_extended_bounded` does. -/
theorem matching_claims_extended_bounded (L W : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (d : Nat) (hbS : StrategyBounded L (strategicShape c s S))
    (hcon : c.numConstants + c.numRouted ≤ W) (hwir : c.numWires ≤ W)
    (hrou : 2 * c.numRouted ≤ W) (hLW : 69 + 24 * W ≤ L) (hdom : 86 ≤ L) :
    StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims (matchingClaims c)) d) :=
  constant_claims_extended_bounded L W c s S (matchingClaims c) d hbS
    (matching_claims_bounded c W hcon hwir hrou) hLW hdom

/-! ## 1. THE SHAPE GAP, CLOSED -/

/-- (1) **THE CRUX OF THE SHAPE GAP, IN ONE LINE.**  The `used` field of the proof the
adaptive prover submits at a table is the SAME record at every table and every
strategy: the adopted `realizedProof` never touches it.  So the used-claims choice
that reproduces `realizedRunProof` is a CONSTANT one, and `ClaimsCausal` costs
nothing. -/
theorem realized_run_proof_used (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    (RunLevelTransportAudit.realizedRunProof L hL c s S hbS N T).used = defaultClaims := rfl

/-- (1) **THE SHAPE GAP, CLOSED -- OPTION (a).**  At the constant claims choice
`constantClaims defaultClaims` the adopted `RawIndexLanes.rawRealizedRun` IS the
adopted `RunLevelTransportAudit.realizedRunProof`, on the nose: both are the adopted
`realizedProof` at the adopted `StrategyChainBound.realizedMessages`, and the `used`
field the raw run writes in is the one the record already carried.  NO probabilistic
content: this is a proof-record identity. -/
theorem raw_realized_run_is_realized_run_proof (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (d : Nat)
    (hbE : StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims defaultClaims) d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    RawIndexLanes.rawRealizedRun L hL c s S (constantClaims defaultClaims) d hbE hbS T
      = RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T := rfl

open Classical in
/-- (1) **HENCE THE TWO INDEX EVENTS COINCIDE, `Finset` FOR `Finset`.**  The adopted
`AdaptiveAssemblyFailure.adaptiveIndexBadEvent` -- the run's own adopted
`SoundnessAssembly.actualIndexDraw` in the adopted `SoundnessAssembly.indexBadEvent` of
the run's own supplied and committed cells, all at `realizedRunProof` -- IS the adopted
`RawIndexLanes.rawEngineIndexBadEvent` at that constant claims choice.  Both the
concreteFinal snapshot the draw is read from and the `p.used` the supplied cells are
read from move with the SAME proof record, so nothing else has to agree. -/
theorem adaptive_index_bad_event_is_raw_engine_index_bad_event
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (d : Nat)
    (hbE : StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims defaultClaims) d))
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    AdaptiveAssemblyFailure.adaptiveIndexBadEvent gdec hash khash P c₀ L hL c s S hbS cellIndex
        cols
      = RawIndexLanes.rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S
          (constantClaims defaultClaims) d hbE hbS cellIndex cols := rfl

/-! ## 1b. THE SAME RUN RECORD WITH THE USED CLAIMS AS A PARAMETER -/

/-- (1b) **THE ADOPTED REALIZED RUN, WITH `used` MADE A PARAMETER.**  The adopted
`ReducedEngineIndex.realizedUsedProof` at the adopted
`StrategyChainBound.realizedMessages`: the SAME statement and the SAME table-dependent
round messages as the adopted `RunLevelTransportAudit.realizedRunProof`, with `u` written
into the one field that record inherits from `Verifier.testProof`.  This is what lets the
whole line below be stated at a used-claims record whose lengths match a NON-DEGENERATE
configuration; see section 0b and the header's vacuity bullet. -/
def realizedRunProofWith (u : Verifier.UsedClaims) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) : Verifier.Proof :=
  ReducedEngineIndex.realizedUsedProof s (realizedMessages L hL c s S hbS N T) u

/-- (1b) At the fixture claims it IS the adopted record, on the nose. -/
theorem realized_run_proof_with_at_default_claims (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    realizedRunProofWith defaultClaims L hL c s S hbS N T
      = RunLevelTransportAudit.realizedRunProof L hL c s S hbS N T := rfl

/-- (1b) And at a constant claims choice it IS the adopted `RawIndexLanes.rawRealizedRun`,
so every adopted raw-index lemma applies to it verbatim. -/
theorem raw_realized_run_at_constant_claims (u : Verifier.UsedClaims) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S (constantClaims u) d))
    (hbS : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    RawIndexLanes.rawRealizedRun L hL c s S (constantClaims u) d hbE hbS T
      = realizedRunProofWith u L hL c s S hbS c.degreeBits T := rfl

/-- (1b) **THE OUTER HALF DOES NOT MOVE.**  The adopted `SoundnessAssembly.outerBadEvent`
and the adopted `SoundnessAssembly.actualDigestDraw` read the proof record through fields
other than `used`, so at every `u` they are the adopted ones on the nose.  THIS IS WHY the
outer summand of every bound below is quoted from the adopted
`AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent` unchanged. -/
theorem outer_bad_event_at_claims (u : Verifier.UsedClaims) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    SoundnessAssembly.outerBadEvent (hashOf (boundedQueries L) T)
        (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
        (realizedRunProofWith u L hL c s S hbS c.degreeBits T) gates s0 logTruths gateTruths t
        pr coeffsOf
      = SoundnessAssembly.outerBadEvent (hashOf (boundedQueries L) T)
        (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
        (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) gates s0
        logTruths gateTruths t pr coeffsOf := rfl

open Classical in
/-- (1b) **THE INDEX HALF AT A PARAMETRIC USED-CLAIMS RECORD.**  The adopted
`AdaptiveAssemblyFailure.adaptiveIndexBadEvent` verbatim, with `realizedRunProofWith u` in
place of the adopted `RunLevelTransportAudit.realizedRunProof`. -/
noncomputable def adaptiveIndexBadEventWith (u : Verifier.UsedClaims)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c
        (realizedRunProofWith u L hL c s S hbS c.degreeBits T)
      ∈ SoundnessAssembly.indexBadEvent c.indexBits
          (OpenedClaimFold.lift (OpenedClaimFold.boundCell
            (realizedRunProofWith u L hL c s S hbS c.degreeBits T).used
            (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
              (hashOf (boundedQueries L) T) khash P c₀) c
              (realizedRunProofWith u L hL c s S hbS c.degreeBits T)) cellIndex).1)
          (IndexPointZeroCheck.openedCells (cols cellIndex)
            (OpenedClaimFold.lift (OpenedClaimFold.cellRow
              (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
                (hashOf (boundedQueries L) T) khash P c₀) c
                (realizedRunProofWith u L hL c s S hbS c.degreeBits T)) cellIndex))))

open Classical in
theorem mem_adaptive_index_bad_event_with (u : Verifier.UsedClaims)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (T : OracleTable (boundedQueries L)) :
    T ∈ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS cellIndex cols ↔
      SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c
          (realizedRunProofWith u L hL c s S hbS c.degreeBits T)
        ∈ SoundnessAssembly.indexBadEvent c.indexBits
            (OpenedClaimFold.lift (OpenedClaimFold.boundCell
              (realizedRunProofWith u L hL c s S hbS c.degreeBits T).used
              (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
                (hashOf (boundedQueries L) T) khash P c₀) c
                (realizedRunProofWith u L hL c s S hbS c.degreeBits T)) cellIndex).1)
            (IndexPointZeroCheck.openedCells (cols cellIndex)
              (OpenedClaimFold.lift (OpenedClaimFold.cellRow
                (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
                  (hashOf (boundedQueries L) T) khash P c₀) c
                  (realizedRunProofWith u L hL c s S hbS c.degreeBits T)) cellIndex))) := by
  rw [adaptiveIndexBadEventWith, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

open Classical in
/-- (1b) **THE PARAMETRIC INDEX EVENT IS THE ADOPTED RAW ENGINE INDEX EVENT.**  The
`u`-parametric restatement of `adaptive_index_bad_event_is_raw_engine_index_bad_event`:
still a `Finset` identity by `rfl`, because the raw run at `constantClaims u` IS
`realizedRunProofWith u`. -/
theorem adaptive_index_bad_event_with_is_raw_engine_index_bad_event (u : Verifier.UsedClaims)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S (constantClaims u) d))
    (hbS : StrategyBounded L (strategicShape c s S)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS cellIndex cols
      = RawIndexLanes.rawEngineIndexBadEvent gdec hash khash P c₀ L hL c s S
          (constantClaims u) d hbE hbS cellIndex cols := rfl

open Classical in
/-- (1b) **THE FAILURE EVENT AT A PARAMETRIC USED-CLAIMS RECORD.**  The adopted
`AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent` verbatim -- the same negated
implication, the same adopted `SoundnessAssembly.AssemblyResidue`, the same adopted
conclusion -- with `realizedRunProofWith u` in place of the adopted
`RunLevelTransportAudit.realizedRunProof`.  `Finset.univ` here mirrors the adopted
definition's own (see HONESTY (vii)). -/
noncomputable def adaptiveAssemblyFailureEventWith (u : Verifier.UsedClaims)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ¬ (
    Integrated.verify (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀)
        gdec pin chain c (realizedRunProofWith u L hL c s S hbS c.degreeBits T)
      = Except.ok () →
    SoundnessAssembly.AssemblyResidue gdec hash (hashOf (boundedQueries L) T) khash P c₀ pin c
        (realizedRunProofWith u L hL c s S hbS c.degreeBits T) wq
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
                  (realizedRunProofWith u L hL c s S hbS c.degreeBits T).publicInputs))
              (Integrated.gateConfig c).numSelectors = some terms
            ∧ ∀ y ∈ terms, y = Verifier.zero)
      ∧ OpenedClaimFold.lift (OpenedClaimFold.boundCell
            (realizedRunProofWith u L hL c s S hbS c.degreeBits T).used
            (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
              (hashOf (boundedQueries L) T) khash P c₀) c
              (realizedRunProofWith u L hL c s S hbS c.degreeBits T))
            cellIndex).1
          = IndexPointZeroCheck.openedCells (cols cellIndex)
            (OpenedClaimFold.lift (OpenedClaimFold.cellRow
              (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
                (hashOf (boundedQueries L) T) khash P c₀) c
                (realizedRunProofWith u L hL c s S hbS c.degreeBits T))
              cellIndex))
      ∧ (PinnedWhirProfile.pinnedParams P c₀ = wq ∧ 0 < wq.inDomainSamples ∧ wq.rounds ≠ [])
      ∧ (ExplicitEngine.core c = ExplicitEngine.core c₀
          ∨ ExplicitEngine.KhashCollision khash))))

/-- (1b) At the fixture claims the parametric failure event IS the adopted one. -/
theorem adaptive_assembly_failure_event_with_at_default_claims (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    adaptiveAssemblyFailureEventWith defaultClaims gdec hash khash P c₀ pin chain L hL c s S hbS
        wq pre post gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols
      = AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L hL
          c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols := rfl

open Classical in
/-- (1b) **THE `u`-PARAMETRIC ANALOGUE OF THE ADOPTED
`AdaptiveAssemblyFailure.adaptive_assembly_failure_subset`.**  The adopted
`SoundnessAssembly.explicit_good_draw_assembly` quantifies its proof record `p` freely, so
it applies at `realizedRunProofWith u` exactly as it does at the adopted realized run; and
its outer draw hypothesis is the ADOPTED outer event's non-membership, by
`outer_bad_event_at_claims`. -/
theorem adaptive_assembly_failure_with_subset (u : Verifier.UsedClaims)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) :
    adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL c s S hbS wq pre post
        gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols
      ⊆ AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS
          (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
        ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS cellIndex cols := by
  classical
  intro T hT
  simp only [adaptiveAssemblyFailureEventWith, Finset.mem_filter, Finset.mem_univ,
    true_and] at hT
  rw [Finset.mem_union, AdaptiveAssemblyFailure.mem_adaptive_engine_outer_bad_event,
    mem_adaptive_index_bad_event_with]
  by_contra hcon
  push_neg at hcon
  exact hT (fun hacc hres => SoundnessAssembly.explicit_good_draw_assembly gdec hash
    (hashOf (boundedQueries L) T) khash P c₀ pin chain c
    (realizedRunProofWith u L hL c s S hbS c.degreeBits T) wq pre post gate s0
    sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols hacc hres hcon.1 hcon.2)

/-! ## 2. THE TWO CHAINS SHARE THEIR NO-CLASH EVENT BELOW THE CLAIM FRAMES -/

/-- (2) **TWO STRATEGIES THAT AGREE BELOW `n` MAKE THE SAME STAGE-`k` FRAME QUERY FOR
`k < n`.**  The adopted `ReducedEngineIndex.strat_hist_of_agree` freezes the history
and `AgreeBelow` freezes the played shape.  The companion of the adopted
`ReducedEngineIndex.challenge_sel_of_agree`, for the CHAIN's own query rather than a
challenge input. -/
theorem strategy_sel_of_agree (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (s1 s2 : Strategy) (hb1 : StrategyBounded L s1) (hb2 : StrategyBounded L s2)
    (n : Nat) (hag : ReducedEngineIndex.AgreeBelow s1 s2 n)
    (T : OracleTable (boundedQueries L)) (k : Nat) (hk : k < n) :
    strategySel L hL e0 s1 hb1 k T = strategySel L hL e0 s2 hb2 k T := by
  apply Subtype.ext
  have hH : stratHist L hL e0 s1 hb1 k T = stratHist L hL e0 s2 hb2 k T :=
    ReducedEngineIndex.strat_hist_of_agree L hL e0 s1 s2 hb1 hb2 n hag T k (le_of_lt hk)
  show Transcript.frame (strategyFrameState L hL e0 s1 hb1 k T)
      (stratShapeAt L hL e0 s1 hb1 k T).1 (stratShapeAt L hL e0 s1 hb1 k T).2
    = Transcript.frame (strategyFrameState L hL e0 s2 hb2 k T)
      (stratShapeAt L hL e0 s2 hb2 k T).1 (stratShapeAt L hL e0 s2 hb2 k T).2
  rw [strategyFrameState, strategyFrameState, stratShapeAt, stratShapeAt, hH, hag k hk]

/-- (2) **SO THEY HAVE THE SAME NO-CLASH EVENT UP TO STAGE `n`.**  The adopted
`BirthdayClashBound.noClash` membership predicate reads `chainVal` at stages `< j`
only. -/
theorem stage_no_clash_of_agree (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (s1 s2 : Strategy) (hb1 : StrategyBounded L s1) (hb2 : StrategyBounded L s2)
    (n : Nat) (hag : ReducedEngineIndex.AgreeBelow s1 s2 n) (j : Nat) (hj : j ≤ n) :
    stageNoClash L hL e0 s1 hb1 j = stageNoClash L hL e0 s2 hb2 j := by
  refine Finset.ext (fun T => ?_)
  have hval : ∀ k, k < j → chainVal (strategySel L hL e0 s1 hb1) k T
      = chainVal (strategySel L hL e0 s2 hb2) k T := by
    intro k hk
    show T (strategySel L hL e0 s1 hb1 k T) = T (strategySel L hL e0 s2 hb2 k T)
    rw [strategy_sel_of_agree L hL e0 s1 s2 hb1 hb2 n hag T k (lt_of_lt_of_le hk hj)]
  rw [stageNoClash, stageNoClash, mem_no_clash, mem_no_clash]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r t hrt htj => ?_, fun t htj => ?_⟩
    · rw [← hval r (lt_trans hrt htj), ← hval t htj]
      exact h1 r t hrt htj
    · rw [← hval t htj]
      exact h2 t htj
  · rintro ⟨h1, h2⟩
    refine ⟨fun r t hrt htj => ?_, fun t htj => ?_⟩
    · rw [hval r (lt_trans hrt htj), hval t htj]
      exact h1 r t hrt htj
    · rw [hval t htj]
      exact h2 t htj

/-- (2) **THE NESTING THAT BUYS ONE CLASH TERM.**  The raw extended chain's no-clash
event at `indexStage d = 22 + 5 d + 8` sits inside the STRATEGIC chain's no-clash event
at `22 + 5 d`.  This is what lets the outer half -- proved at the strategic chain by
the adopted `AdaptiveAssemblyFailure` -- and the index half -- proved at the extended
chain by the adopted `RawIndexLanes` -- be conditioned on ONE event, exactly as the
adopted `EngineOuterDiagonal.raw_engine_all_own_bad_draw_probability_le` conditions its
four families on one. -/
theorem raw_extended_no_clash_subset (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (U : RawIndexLanes.RawUsedClaims) (d : Nat)
    (hbE : StrategyBounded L (RawIndexLanes.rawExtendedShape c s S U d))
    (hbS : StrategyBounded L (strategicShape c s S)) :
    stageNoClash L hL OuterInitial.zeroDigest (RawIndexLanes.rawExtendedShape c s S U d) hbE
        (ReducedIndexLanes.indexStage d)
      ⊆ stageNoClash L hL OuterInitial.zeroDigest (strategicShape c s S) hbS (22 + 5 * d) := by
  have heq := stage_no_clash_of_agree L hL OuterInitial.zeroDigest
    (RawIndexLanes.rawExtendedShape c s S U d) (strategicShape c s S) hbE hbS (22 + 5 * d)
    (RawIndexLanes.raw_extended_agrees_below c s S U d) (22 + 5 * d) (Nat.le_refl _)
  rw [← heq]
  exact stage_no_clash_mono L hL OuterInitial.zeroDigest
    (RawIndexLanes.rawExtendedShape c s S U d) hbE (22 + 5 * d)
    (ReducedIndexLanes.indexStage d) (by rw [ReducedIndexLanes.indexStage]; omega)

/-! ## 3. THE INDEX HALF, WEIGHED -/

open Classical in
/-- (3) **THE INDEX HALF THE ADOPTED `AdaptiveAssemblyFailure` CARRIED UNEVALUATED, NOW
BOUNDED.**  For every transcript-restricted causal `S`, the mass of the adopted
`adaptiveIndexBadEvent` is at most `2 * tauTerm c.indexBits` plus one clash term at
`indexStage c.degreeBits`.  THIS IS THE STEP THE ADOPTED HEADER CALLED "THE ONE STEP
STILL OWED"; it is a transport of the adopted
`RawIndexLanes.raw_index_bad_event_no_clash_mass_le` along section 1's proof-record
identity, not a new probabilistic argument.  READ THE HONESTY HEADER. -/
theorem adaptive_index_half_mass_le_at_claims (u : Verifier.UsedClaims)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S)
    (hbE : StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdb : c.degreeBits ≤ 13)
    (hbu : 6 * c.indexBits ≤ Transcript.u64Limit) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    oracleProbability (boundedQueries L)
        (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS cellIndex cols)
      ≤ 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
            * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have heq : adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS cellIndex cols
      = RawIndexLanes.rawIndexBadEvent L hL c s S (constantClaims u) c.degreeBits
          c.indexBits hbE cellIndex (ReducedEngineIndex.committedOf cols cellIndex) := by
    rw [adaptive_index_bad_event_with_is_raw_engine_index_bad_event u gdec hash khash P c₀ L hL c
      s S c.degreeBits hbE hbS cellIndex cols,
      RawIndexLanes.raw_engine_index_bad_event_eq gdec hash khash P c₀ L hL c s S hS
        (constantClaims u) c.degreeBits
        (constant_claims_causal u c.degreeBits) hbE hbS rfl hdb cellIndex cols]
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (RawIndexLanes.rawIndexBadEvent L hL c s S (constantClaims u) c.degreeBits
        c.indexBits hbE cellIndex (ReducedEngineIndex.committedOf cols cellIndex))
      (stageNoClash L hL OuterInitial.zeroDigest
        (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
        (ReducedIndexLanes.indexStage c.degreeBits)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (RawIndexLanes.rawIndexBadEvent L hL c s S (constantClaims u) c.degreeBits
        c.indexBits hbE cellIndex (ReducedEngineIndex.committedOf cols cellIndex)
      ∩ stageNoClash L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
          (ReducedIndexLanes.indexStage c.degreeBits))
    ((stageNoClash L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits))ᶜ)
  have hidx := RawIndexLanes.raw_index_bad_event_no_clash_mass_le L hL c s S
    (constantClaims u) c.degreeBits c.indexBits
    (constant_claims_causal u c.degreeBits) hbE cellIndex
    (ReducedEngineIndex.committedOf cols cellIndex) hbu
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL OuterInitial.zeroDigest
        (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
        (ReducedIndexLanes.indexStage c.degreeBits))ᶜ)
      ≤ ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
          * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits)
  rw [heq]
  linarith

open Classical in
/-- (3) The same at the FIXTURE used claims, where the event is the adopted
`AdaptiveAssemblyFailure.adaptiveIndexBadEvent` on the nose.  READ THE HEADER'S VACUITY
BULLET: at that record the acceptance antecedent of the failure event of section 4 is
unsatisfiable outside a degenerate configuration; this index bound itself is NOT
conditioned on acceptance and is unaffected. -/
theorem adaptive_index_half_mass_le (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S)
    (hbE : StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims defaultClaims) c.degreeBits))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdb : c.degreeBits ≤ 13)
    (hbu : 6 * c.indexBits ≤ Transcript.u64Limit) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    oracleProbability (boundedQueries L)
        (AdaptiveAssemblyFailure.adaptiveIndexBadEvent gdec hash khash P c₀ L hL c s S hbS
          cellIndex cols)
      ≤ 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
            * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  adaptive_index_half_mass_le_at_claims defaultClaims gdec hash khash P c₀ L hL c s S hS hbE hbS
    hdb hbu cellIndex cols

/-! ## 4. THE SINGLE CONSTANT -/

open Classical in
/-- (4) **THE PAYOFF: THE ADOPTED `AdaptiveAssemblyFailure.adaptive_assembly_failure_mass_le`
WITH ITS THIRD SUMMAND EVALUATED AND ITS CLASH TERMS FUSED.**  For EVERY
`StrategyChainBound.RoundCausal S` -- a transcript-restricted causal prover, grinding
excluded -- the mass of the tables at which the adopted
`SoundnessAssembly.explicit_good_draw_assembly` conclusion fails AT THE PROOF THAT
PROVER ACTUALLY SUBMITS is at most

  `combinedBound c.degreeBits q c.degreeBits constraints + 2 * tauTerm c.indexBits
     + (22 + 5 d + 8)(22 + 5 d + 9)/2 / |Block|`,

ONE clash term, at the larger of the two conditioning stages.  The outer half is the
adopted `EngineOuterDiagonal.raw_engine_all_own_no_clash_mass_le` at the strategic
chain and the index half the adopted `RawIndexLanes.raw_index_bad_event_no_clash_mass_le`
at the raw extended chain; section 2 nests the two conditioning events, so the clash
term is paid once.

READ THE HONESTY HEADER: this is the random-oracle model, the conclusion is
good-draw-conditional and is NOT circuit truth, acceptance is never exhibited, and
WHIR/Merkle are excluded -- this constant is not the system's soundness error. -/
theorem adaptive_assembly_failure_mass_le_single_constant_at_claims
    (u : Verifier.UsedClaims) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S)
    (hbE : StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdb : c.degreeBits ≤ 13)
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
    (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL
          c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
            * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hsub := oracle_probability_mono (boundedQueries L) _ _
    (adaptive_assembly_failure_with_subset u gdec hash khash P c₀ pin chain L hL
      c s S hbS wq pre post gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex
      cols)
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS
          (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
        ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
            cellIndex cols)
      (stageNoClash L hL OuterInitial.zeroDigest
        (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
        (ReducedIndexLanes.indexStage c.degreeBits)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    ((AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS
          (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
        ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
            cellIndex cols)
      ∩ stageNoClash L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
          (ReducedIndexLanes.indexStage c.degreeBits))
    ((stageNoClash L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits))ᶜ)
  have hs1 := ReducedEngineIndex.inter_union_mass_le L
    (AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS
      (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS cellIndex
      cols)
    (stageNoClash L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits))
  have hnest := raw_extended_no_clash_subset L hL c s S (constantClaims u)
    c.degreeBits hbE hbS
  have hAeq : AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S
        hbS (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
      = rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
          c.degreeBits (2 ^ c.degreeBits)
          (AdaptiveAssemblyFailure.constantLogLane S logTruths
            (JointChallengeSpace.logCompareOf t pr))
          (AdaptiveAssemblyFailure.engineGateLane S gateTruths
            (engineEndpoint c (pre ++ gate :: post)
              (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0))
          (EngineTauDiagonal.engineGate c (pre ++ gate :: post)
            (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0.tables)
          coeffsOf :=
    (AdaptiveAssemblyFailure.engine_all_own_bad_event_is_assembly_outer_bad_event gdec hash khash
      P c₀ th0 L hL c s S hS hbS (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf).symm
  have hAsub : AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S
          hbS (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
        ∩ stageNoClash L hL OuterInitial.zeroDigest
            (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
            (ReducedIndexLanes.indexStage c.degreeBits)
      ⊆ rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
            c.degreeBits (2 ^ c.degreeBits)
            (AdaptiveAssemblyFailure.constantLogLane S logTruths
              (JointChallengeSpace.logCompareOf t pr))
            (AdaptiveAssemblyFailure.engineGateLane S gateTruths
              (engineEndpoint c (pre ++ gate :: post)
                (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0))
            (EngineTauDiagonal.engineGate c (pre ++ gate :: post)
              (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0.tables)
            coeffsOf
        ∩ stageNoClash L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
            (22 + 5 * c.degreeBits) := by
    rw [hAeq]
    exact Finset.inter_subset_inter (Finset.Subset.refl _) hnest
  have hAmass := le_trans (oracle_probability_mono (boundedQueries L) _ _ hAsub)
    (raw_engine_all_own_no_clash_mass_le L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
      c.degreeBits q (2 ^ c.degreeBits) constraints
      (AdaptiveAssemblyFailure.constantLogLane S logTruths
        (JointChallengeSpace.logCompareOf t pr))
      (AdaptiveAssemblyFailure.engineGateLane S gateTruths
        (engineEndpoint c (pre ++ gate :: post)
          (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0))
      (AdaptiveAssemblyFailure.constant_log_lane_causal S hS logTruths
        (JointChallengeSpace.logCompareOf t pr))
      (AdaptiveAssemblyFailure.engine_gate_lane_causal S hS gateTruths
        (engineEndpoint c (pre ++ gate :: post)
          (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0))
      (AdaptiveAssemblyFailure.constant_log_lane_bounded S logTruths
        (JointChallengeSpace.logCompareOf t pr) 5 hSlog hlenlog)
      (AdaptiveAssemblyFailure.engine_gate_lane_bounded S gateTruths
        (engineEndpoint c (pre ++ gate :: post)
          (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0)
        (q + 2) hSgate hlengate)
      (EngineTauDiagonal.engineGate c (pre ++ gate :: post)
        (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0.tables)
      coeffsOf hdu hclen (22 + 5 * c.degreeBits)
      (by rw [ReducedFullTransport.deriveStage]; omega)
      (fun r hr => round_stage_le r c.degreeBits hr))
  have hBeq : adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
        cellIndex cols
      = RawIndexLanes.rawIndexBadEvent L hL c s S (constantClaims u) c.degreeBits
          c.indexBits hbE cellIndex (ReducedEngineIndex.committedOf cols cellIndex) := by
    rw [adaptive_index_bad_event_with_is_raw_engine_index_bad_event u gdec hash khash P c₀ L hL c s S
      c.degreeBits hbE hbS cellIndex cols,
      RawIndexLanes.raw_engine_index_bad_event_eq gdec hash khash P c₀ L hL c s S hS
        (constantClaims u) c.degreeBits
        (constant_claims_causal u c.degreeBits) hbE hbS rfl hdb cellIndex cols]
  have hBmass := RawIndexLanes.raw_index_bad_event_no_clash_mass_le L hL c s S
    (constantClaims u) c.degreeBits c.indexBits
    (constant_claims_causal u c.degreeBits) hbE cellIndex
    (ReducedEngineIndex.committedOf cols cellIndex) hbu
  rw [← hBeq] at hBmass
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL OuterInitial.zeroDigest
        (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
        (ReducedIndexLanes.indexStage c.degreeBits))ᶜ)
      ≤ ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
          * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits)
  rw [ChallengeUnionBound.combinedBound]
  linarith

open Classical in
/-- (4) **THE SAME AT THE FIXTURE USED CLAIMS**, where the event is the adopted
`AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent` on the nose.  READ THE HEADER'S
VACUITY BULLET: at THIS instantiation the acceptance conjunct of the adopted event is
unsatisfiable at every configuration with `numWires ≠ 1` or `numRouted ≠ 0`
(`adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`), so this corollary
is non-vacuous only at the degenerate configuration.  The `_at_claims` form above, at
`matchingClaims c`, is the one whose acceptance antecedent survives a general `c`. -/
theorem adaptive_assembly_failure_mass_le_single_constant (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S)
    (hbE : StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims defaultClaims) c.degreeBits))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdb : c.degreeBits ≤ 13)
    (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (q constraints : Nat)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ v ∈ logTruths, v.length ≤ 5)
    (hlengate : ∀ v ∈ gateTruths, v.length ≤ q + 2)
    (hdu : 12 + 6 * c.degreeBits < Transcript.u64Limit)
    (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L hL
          c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
            * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  adaptive_assembly_failure_mass_le_single_constant_at_claims defaultClaims gdec hash khash P c₀
    pin chain th0 L hL c s S hS hbE hbS hdb wq pre post gate s0 sLast xg cells logTruths
    gateTruths t pr coeffsOf cellIndex cols q constraints hSlog hSgate hlenlog hlengate hdu hbu
    hclen

/-! ## 5. THE CLOSED INSTANCES, AND THE VACUITY OF THE FIXTURE ONE -/

/-- (5) **THE SINGLE CONSTANT AT THE ENVELOPE IS STRICTLY BELOW `1`.**  Inherited
verbatim from the adopted `RawIndexLanes.raw_index_engine_bound_at_thirteen_lt_one`:
the SAME three summands, because section 4's bound is that theorem's constant.  Unlike
the adopted `AdaptiveAssemblyFailure.adaptive_assembly_bound_at_thirteen_lt_one`, this
covers ALL of section 4's bound -- there is no carried term left outside it.
`Fintype.card Block` is never evaluated. -/
theorem adaptive_single_constant_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) < 1 :=
  RawIndexLanes.raw_index_engine_bound_at_thirteen_lt_one

open Classical in
/-- (5) **THE CLOSED INSTANCE.**  Thirteen coupled rounds, `quotientDegree = 8`,
`numGateConstraints = 123`, `indexBits = 8`, the adopted genuinely raw
`StrategyChainBound.challengeTruncatedMessage` as the round-message choice, the EMPTY
truth column, at ONE bound cell.  Neither `StrategyBounded` (for either chain) nor
`64 ≤ L` nor either counter budget is left as a hypothesis.

  `<= combinedBound 13 8 13 123 + 2 * tauTerm 8 + 4560 / |Block|`, and that is `< 1`.

READ THE HONESTY HEADER: THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR. -/
theorem adaptive_assembly_bound_at_thirteen (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (m : Verifier.CoupledMessage) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (hc13 : c.degreeBits = 13) (hcidx : c.indexBits = 8)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L
          (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) wq pre post
          gate s0 sLast xg cells [] coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 2 * ChallengeUnionBound.tauTerm 8 + 4560 / (Fintype.card Block : ℚ) := by
  have h := adaptive_assembly_failure_mass_le_single_constant gdec hash khash P c₀ pin chain th0 L
    (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
    (challenge_truncated_round_causal m)
    (default_claims_extended_bounded L c s (challengeTruncatedMessage m) c.degreeBits
      (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) (by omega))
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) (by omega)
    wq pre post gate s0 sLast xg cells [] [] t pr coeffsOf cellIndex cols 8 123
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hmlog)
    (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
    (fun _ hu => absurd hu (List.not_mem_nil _))
    (fun _ hu => absurd hu (List.not_mem_nil _))
    (by rw [hc13]; exact ReducedFullTransport.thirteen_counter_budget)
    (by rw [hcidx]; exact ReducedIndexLanes.eight_index_counter_budget)
    (by rw [hc13]; exact hclen)
  rw [hc13, hcidx] at h
  have harith : ((ReducedIndexLanes.indexStage 13 : Nat) : ℚ)
      * (((ReducedIndexLanes.indexStage 13 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [ReducedIndexLanes.index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

/-- (5) **THE HYPOTHESES OF SECTION 4 ARE SATISFIABLE**: both counter budgets hold at the
envelope, the empty coefficient family and the EMPTY truth lists meet the degree budgets,
and the constant claims choice meets both the width budget and `ClaimsCausal` at every
`d`.  THIS IS HYPOTHESIS SATISFIABILITY, NOT NON-VACUITY OF THE CONCLUSION: the bounded
event still carries acceptance as a conjunct, and at the fixture used claims that conjunct
is itself unsatisfiable outside the degenerate configuration
(`adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`). -/
theorem adaptive_single_constant_hypotheses_satisfiable :
    (12 + 6 * 13 < Transcript.u64Limit) ∧ (6 * 8 ≤ Transcript.u64Limit) ∧
      (∀ i, i < 2 ^ 13 → ((fun _ => ([] : List Element)) i).length ≤ 123) ∧
      (∀ u ∈ ([] : List (List Element)), u.length ≤ 5) ∧
      (∀ u ∈ ([] : List (List Element)), u.length ≤ 10) ∧
      RawIndexLanes.RawUsedClaimsBounded 1 (constantClaims defaultClaims) ∧
      (∀ d : Nat, RawIndexLanes.ClaimsCausal d (constantClaims defaultClaims)) :=
  ⟨ReducedFullTransport.thirteen_counter_budget, ReducedIndexLanes.eight_index_counter_budget,
    fun _ _ => Nat.zero_le _, fun _ h => absurd h (List.not_mem_nil _),
    fun _ h => absurd h (List.not_mem_nil _), default_claims_bounded,
    fun d => constant_claims_causal defaultClaims d⟩

open Classical in
/-- (5) **THE CLOSED INSTANCE OF THE REPAIRED LINE, AT A USED-CLAIMS RECORD WHOSE SHAPE
MATCHES `c`.**  The same envelope as `adaptive_assembly_bound_at_thirteen` -- thirteen
coupled rounds, `quotientDegree = 8`, `numGateConstraints = 123`, `indexBits = 8`, the
adopted genuinely raw `StrategyChainBound.challengeTruncatedMessage`, the EMPTY truth
column, ONE bound cell -- but at `matchingClaims c` rather than at the fixture record, so
the acceptance conjunct of the event is no longer refuted by length arithmetic at a
configuration with many wires or routed wires (`shape_satisfiable_at_matching_claims`).
The width parameter `W` is the prover's claim-width budget; the extended chain's length
budget is discharged from `hbS` plus `69 + 24 W ≤ L`.

  `<= combinedBound 13 8 13 123 + 2 * tauTerm 8 + 4560 / |Block|`, and that is `< 1`.

ACCEPTANCE IS STILL NEVER EXHIBITED -- the remaining shape conjuncts are not discharged
anywhere.  READ THE HONESTY HEADER: THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR. -/
theorem adaptive_assembly_bound_at_thirteen_at_matching_claims (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L W : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (m : Verifier.CoupledMessage) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (hc13 : c.degreeBits = 13) (hcidx : c.indexBits = 8)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hcon : c.numConstants + c.numRouted ≤ W) (hwir : c.numWires ≤ W)
    (hrou : 2 * c.numRouted ≤ W) (hLW : 69 + 24 * W ≤ L)
    (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (adaptiveAssemblyFailureEventWith (matchingClaims c) gdec hash khash P c₀ pin chain L
          (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) wq pre post
          gate s0 sLast xg cells [] coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 2 * ChallengeUnionBound.tauTerm 8 + 4560 / (Fintype.card Block : ℚ) := by
  have h := adaptive_assembly_failure_mass_le_single_constant_at_claims (matchingClaims c) gdec
    hash khash P c₀ pin chain th0 L (Nat.le_trans (by omega) hLq) c s
    (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
    (matching_claims_extended_bounded L W c s (challengeTruncatedMessage m) c.degreeBits
      (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) hcon hwir hrou hLW
      (by omega))
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) (by omega)
    wq pre post gate s0 sLast xg cells [] [] t pr coeffsOf cellIndex cols 8 123
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hmlog)
    (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
    (fun _ hu => absurd hu (List.not_mem_nil _))
    (fun _ hu => absurd hu (List.not_mem_nil _))
    (by rw [hc13]; exact ReducedFullTransport.thirteen_counter_budget)
    (by rw [hcidx]; exact ReducedIndexLanes.eight_index_counter_budget)
    (by rw [hc13]; exact hclen)
  rw [hc13, hcidx] at h
  have harith : ((ReducedIndexLanes.indexStage 13 : Nat) : ℚ)
      * (((ReducedIndexLanes.indexStage 13 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [ReducedIndexLanes.index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

open Classical in
/-- (5) **THE VACUITY OF THE FIXTURE INSTANTIATION, RECORDED AS A THEOREM OF THIS TREE.**
The adopted `AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent` carries ACCEPTANCE as
a conjunct (the event is the NEGATION of an implication whose antecedent is
`Integrated.verify … = Except.ok ()`).  The adopted `SoundnessAssembly`'s own
`explicit_accepted_run_facts` returns `Verifier.shape` from acceptance, and at the fixture
used-claims record the shape gate forces one wire and no routed wires.  Hence at EVERY
other configuration the adopted event is the EMPTY set and the fixture headline
`adaptive_assembly_failure_mass_le_single_constant` -- like the adopted
`AdaptiveAssemblyFailure.adaptive_assembly_bound_at_thirteen` it specialises -- is
vacuously true there.

This is why section 1b makes the used claims a parameter and why
`adaptive_assembly_bound_at_thirteen_at_matching_claims` is the instance that carries
content at a general `c`. -/
theorem adaptive_assembly_failure_event_is_empty_at_nondegenerate_config
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (hnd : c.numWires ≠ 1 ∨ c.numRouted ≠ 0) :
    AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L hL c s
        S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_not_mem (fun T hT => ?_)
  simp only [AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent, Finset.mem_filter,
    Finset.mem_univ, true_and] at hT
  refine hT (fun hacc => False.elim ?_)
  have hdeg := shape_forces_degenerate_config_at_fixture_claims pin c
    (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T) rfl
    (SoundnessAssembly.explicit_accepted_run_facts gdec hash (hashOf (boundedQueries L) T) khash
      P c₀ pin chain c (RunLevelTransportAudit.realizedRunProof L hL c s S hbS c.degreeBits T)
      [] hacc).2.1
  rcases hnd with h | h
  · exact h hdeg.1
  · exact h hdeg.2.1

/-! ## 6. ALL FIVE BOUND CELLS -/

/-- (6) A five-fold union of events, each inside `A` union its own `B`, is inside `A`
union the five `B`s. -/
theorem five_union_subset (L : Nat)
    (E0 E1 E2 E3 E4 A B0 B1 B2 B3 B4 : Finset (OracleTable (boundedQueries L)))
    (h0 : E0 ⊆ A ∪ B0) (h1 : E1 ⊆ A ∪ B1) (h2 : E2 ⊆ A ∪ B2) (h3 : E3 ⊆ A ∪ B3)
    (h4 : E4 ⊆ A ∪ B4) :
    ((((E0 ∪ E1) ∪ E2) ∪ E3) ∪ E4) ⊆ A ∪ ((((B0 ∪ B1) ∪ B2) ∪ B3) ∪ B4) := by
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  rcases hx with ((((hx | hx) | hx) | hx) | hx)
  · have hm := h0 hx
    simp only [Finset.mem_union] at hm
    tauto
  · have hm := h1 hx
    simp only [Finset.mem_union] at hm
    tauto
  · have hm := h2 hx
    simp only [Finset.mem_union] at hm
    tauto
  · have hm := h3 hx
    simp only [Finset.mem_union] at hm
    tauto
  · have hm := h4 hx
    simp only [Finset.mem_union] at hm
    tauto

/-- (6) And the five `B`s, conditioned on one event, cost five times one bound. -/
theorem five_union_inter_mass_le (L : Nat)
    (B0 B1 B2 B3 B4 N : Finset (OracleTable (boundedQueries L))) (x : ℚ)
    (h0 : oracleProbability (boundedQueries L) (B0 ∩ N) ≤ x)
    (h1 : oracleProbability (boundedQueries L) (B1 ∩ N) ≤ x)
    (h2 : oracleProbability (boundedQueries L) (B2 ∩ N) ≤ x)
    (h3 : oracleProbability (boundedQueries L) (B3 ∩ N) ≤ x)
    (h4 : oracleProbability (boundedQueries L) (B4 ∩ N) ≤ x) :
    oracleProbability (boundedQueries L) (((((B0 ∪ B1) ∪ B2) ∪ B3) ∪ B4) ∩ N)
      ≤ 5 * x := by
  have a1 := ReducedEngineIndex.inter_union_mass_le L (((B0 ∪ B1) ∪ B2) ∪ B3) B4 N
  have a2 := ReducedEngineIndex.inter_union_mass_le L ((B0 ∪ B1) ∪ B2) B3 N
  have a3 := ReducedEngineIndex.inter_union_mass_le L (B0 ∪ B1) B2 N
  have a4 := ReducedEngineIndex.inter_union_mass_le L B0 B1 N
  linarith

open Classical in

/-- (6) The five bound cells' adaptive assembly-failure events at a PARAMETRIC used-claims
record, unioned. -/
noncomputable def adaptiveAllCellsFailureEventWith (u : Verifier.UsedClaims)
    (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cols : Fin 5 → List (List Element)) :
    Finset (OracleTable (boundedQueries L)) :=
  ((((adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL c
          s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 0 cols
        ∪ adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L
          hL c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 1 cols)
        ∪ adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L
          hL c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 2 cols)
        ∪ adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L
          hL c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 3 cols)
        ∪ adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L
          hL c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 4 cols)

open Classical in

/-- The five bound cells' adaptive assembly-failure events, unioned. -/
noncomputable def adaptiveAllCellsFailureEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hbS : StrategyBounded L (strategicShape c s S)) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cols : Fin 5 → List (List Element)) :
    Finset (OracleTable (boundedQueries L)) :=
  ((((AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L hL c
          s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 0 cols
        ∪ AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L
          hL c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 1 cols)
        ∪ AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L
          hL c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 2 cols)
        ∪ AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L
          hL c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 3 cols)
        ∪ AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent gdec hash khash P c₀ pin chain L
          hL c s S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 4 cols)
open Classical in

/-- (6) **THE FIVE-CELL FORM.**  The adopted `SoundnessAssembly.explicit_good_draw_assembly`
takes its index hypothesis `hidx` at ONE `cellIndex` and concludes the cell identity at
that same `cellIndex`, so the adopted `AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent`
is a per-cell event.  The event that SOME of the five bound cells' assembly conclusions
fails is their union, and it costs five index summands under ONE clash term. -/
theorem adaptive_all_cells_failure_mass_le_at_claims (u : Verifier.UsedClaims)
    (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S)
    (hbE : StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdb : c.degreeBits ≤ 13)
    (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element)) (q constraints : Nat)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ u ∈ logTruths, u.length ≤ 5)
    (hlengate : ∀ u ∈ gateTruths, u.length ≤ q + 2)
    (hdu : 12 + 6 * c.degreeBits < Transcript.u64Limit)
    (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (adaptiveAllCellsFailureEventWith u gdec hash khash P c₀ pin chain L hL c s S hbS wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + 5 * (2 * ChallengeUnionBound.tauTerm c.indexBits)
        + ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
            * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hsubcell : ∀ i : Fin 5,
      adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL c s
          S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf i cols
        ⊆ AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S
            hbS
            (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
          ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS i
              cols :=
    fun i => adaptive_assembly_failure_with_subset u gdec hash khash P c₀ pin
      chain L hL c s S hbS wq pre post gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf
      i cols
  have hBmass : ∀ i : Fin 5, oracleProbability (boundedQueries L)
      (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS i cols
        ∩ stageNoClash L hL OuterInitial.zeroDigest
            (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
            (ReducedIndexLanes.indexStage c.degreeBits))
      ≤ 2 * ChallengeUnionBound.tauTerm c.indexBits := by
    intro i
    have hBeq : adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
          i cols
        = RawIndexLanes.rawIndexBadEvent L hL c s S (constantClaims u) c.degreeBits
            c.indexBits hbE i (ReducedEngineIndex.committedOf cols i) := by
      rw [adaptive_index_bad_event_with_is_raw_engine_index_bad_event u gdec hash khash P c₀ L hL c s S
        c.degreeBits hbE hbS i cols,
        RawIndexLanes.raw_engine_index_bad_event_eq gdec hash khash P c₀ L hL c s S hS
          (constantClaims u) c.degreeBits
          (constant_claims_causal u c.degreeBits) hbE hbS rfl hdb i cols]
    rw [hBeq]
    exact RawIndexLanes.raw_index_bad_event_no_clash_mass_le L hL c s S
      (constantClaims u) c.degreeBits c.indexBits
      (constant_claims_causal u c.degreeBits) hbE i
      (ReducedEngineIndex.committedOf cols i) hbu
  have hsub := five_union_subset L
    (adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL c s
      S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 0 cols)
    (adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL c s
      S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 1 cols)
    (adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL c s
      S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 2 cols)
    (adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL c s
      S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 3 cols)
    (adaptiveAssemblyFailureEventWith u gdec hash khash P c₀ pin chain L hL c s
      S hbS wq pre post gate s0 sLast xg cells gateTruths coeffsOf 4 cols)
    (AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS
      (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 0 cols)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 1 cols)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 2 cols)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 3 cols)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 4 cols)
    (hsubcell 0) (hsubcell 1) (hsubcell 2) (hsubcell 3) (hsubcell 4)
  have hmass := oracle_probability_mono (boundedQueries L) _ _ hsub
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS
          (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
        ∪ ((((adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              0
              cols
            ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              1
              cols)
            ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              2
              cols)
            ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              3
              cols)
            ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              4
              cols))
      (stageNoClash L hL OuterInitial.zeroDigest
        (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
        (ReducedIndexLanes.indexStage c.degreeBits)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    ((AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS
          (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
        ∪ ((((adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              0
              cols
            ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              1
              cols)
            ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              2
              cols)
            ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              3
              cols)
            ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS
              4
              cols))
      ∩ stageNoClash L hL OuterInitial.zeroDigest
          (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
          (ReducedIndexLanes.indexStage c.degreeBits))
    ((stageNoClash L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits))ᶜ)
  have hs1 := ReducedEngineIndex.inter_union_mass_le L
    (AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S hbS
      (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf)
    ((((adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 0 cols
        ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 1
          cols)
        ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 2
          cols)
        ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 3
          cols)
        ∪ adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 4
          cols)
    (stageNoClash L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits))
  have hBB := five_union_inter_mass_le L
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 0 cols)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 1 cols)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 2 cols)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 3 cols)
    (adaptiveIndexBadEventWith u gdec hash khash P c₀ L hL c s S hbS 4 cols)
    (stageNoClash L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits))
    (2 * ChallengeUnionBound.tauTerm c.indexBits)
    (hBmass 0) (hBmass 1) (hBmass 2) (hBmass 3) (hBmass 4)
  have hnest := raw_extended_no_clash_subset L hL c s S (constantClaims u)
    c.degreeBits hbE hbS
  have hAeq : AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S
        hbS (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
      = rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
          c.degreeBits (2 ^ c.degreeBits)
          (AdaptiveAssemblyFailure.constantLogLane S logTruths
            (JointChallengeSpace.logCompareOf t pr))
          (AdaptiveAssemblyFailure.engineGateLane S gateTruths
            (engineEndpoint c (pre ++ gate :: post)
              (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0))
          (EngineTauDiagonal.engineGate c (pre ++ gate :: post)
            (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0.tables)
          coeffsOf :=
    (AdaptiveAssemblyFailure.engine_all_own_bad_event_is_assembly_outer_bad_event gdec hash khash
      P c₀ th0 L hL c s S hS hbS (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf).symm
  have hAsub : AdaptiveAssemblyFailure.adaptiveEngineOuterBadEvent gdec hash khash P c₀ L hL c s S
          hbS (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
        ∩ stageNoClash L hL OuterInitial.zeroDigest
            (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
            (ReducedIndexLanes.indexStage c.degreeBits)
      ⊆ rawEngineAllOwnBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
            c.degreeBits (2 ^ c.degreeBits)
            (AdaptiveAssemblyFailure.constantLogLane S logTruths
              (JointChallengeSpace.logCompareOf t pr))
            (AdaptiveAssemblyFailure.engineGateLane S gateTruths
              (engineEndpoint c (pre ++ gate :: post)
                (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0))
            (EngineTauDiagonal.engineGate c (pre ++ gate :: post)
              (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0.tables)
            coeffsOf
        ∩ stageNoClash L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
            (22 + 5 * c.degreeBits) := by
    rw [hAeq]
    exact Finset.inter_subset_inter (Finset.Subset.refl _) hnest
  have hAmass := le_trans (oracle_probability_mono (boundedQueries L) _ _ hAsub)
    (raw_engine_all_own_no_clash_mass_le L hL OuterInitial.zeroDigest (strategicShape c s S) hbS
      c.degreeBits q (2 ^ c.degreeBits) constraints
      (AdaptiveAssemblyFailure.constantLogLane S logTruths
        (JointChallengeSpace.logCompareOf t pr))
      (AdaptiveAssemblyFailure.engineGateLane S gateTruths
        (engineEndpoint c (pre ++ gate :: post)
          (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0))
      (AdaptiveAssemblyFailure.constant_log_lane_causal S hS logTruths
        (JointChallengeSpace.logCompareOf t pr))
      (AdaptiveAssemblyFailure.engine_gate_lane_causal S hS gateTruths
        (engineEndpoint c (pre ++ gate :: post)
          (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0))
      (AdaptiveAssemblyFailure.constant_log_lane_bounded S logTruths
        (JointChallengeSpace.logCompareOf t pr) 5 hSlog hlenlog)
      (AdaptiveAssemblyFailure.engine_gate_lane_bounded S gateTruths
        (engineEndpoint c (pre ++ gate :: post)
          (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0)
        (q + 2) hSgate hlengate)
      (EngineTauDiagonal.engineGate c (pre ++ gate :: post)
        (AdaptiveAssemblyFailure.enginePublicHash gdec hash khash P c₀ th0 s) s0.tables)
      coeffsOf hdu hclen (22 + 5 * c.degreeBits)
      (by rw [ReducedFullTransport.deriveStage]; omega)
      (fun r hr => round_stage_le r c.degreeBits hr))
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL OuterInitial.zeroDigest
        (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
        (ReducedIndexLanes.indexStage c.degreeBits))ᶜ)
      ≤ ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
          * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL OuterInitial.zeroDigest
      (RawIndexLanes.rawExtendedShape c s S (constantClaims u) c.degreeBits) hbE
      (ReducedIndexLanes.indexStage c.degreeBits)
  rw [adaptiveAllCellsFailureEventWith, ChallengeUnionBound.combinedBound]
  linarith

open Classical in
/-- (6) **THE SAME AT THE FIXTURE USED CLAIMS.**  READ THE HEADER'S VACUITY BULLET: each
of the five adopted per-cell events carries acceptance as a conjunct, so at the fixture
record this union too is empty outside the degenerate configuration
(`adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`, cell by cell). -/
theorem adaptive_all_cells_failure_mass_le (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S)
    (hbE : StrategyBounded L
      (RawIndexLanes.rawExtendedShape c s S (constantClaims defaultClaims) c.degreeBits))
    (hbS : StrategyBounded L (strategicShape c s S)) (hdb : c.degreeBits ≤ 13)
    (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element)) (q constraints : Nat)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ v ∈ logTruths, v.length ≤ 5)
    (hlengate : ∀ v ∈ gateTruths, v.length ≤ q + 2)
    (hdu : 12 + 6 * c.degreeBits < Transcript.u64Limit)
    (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (adaptiveAllCellsFailureEvent gdec hash khash P c₀ pin chain L hL c s S hbS wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + 5 * (2 * ChallengeUnionBound.tauTerm c.indexBits)
        + ((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ)
            * (((ReducedIndexLanes.indexStage c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  adaptive_all_cells_failure_mass_le_at_claims defaultClaims gdec hash khash P c₀ pin chain th0 L
    hL c s S hS hbE hbS hdb wq pre post gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf
    cols q constraints hSlog hSgate hlenlog hlengate hdu hbu hclen


theorem adaptive_all_cells_constant_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 5 * (2 * ChallengeUnionBound.tauTerm 8)
        + 4560 / (Fintype.card Block : ℚ) < 1 :=
  RawIndexLanes.raw_index_engine_bound_at_thirteen_all_cells_lt_one

open Classical in

/-- (6) **THE FIVE-CELL CLOSED INSTANCE AT THE ENVELOPE.** -/
theorem adaptive_all_cells_bound_at_thirteen (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (m : Verifier.CoupledMessage) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element)) (hc13 : c.degreeBits = 13) (hcidx : c.indexBits = 8)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (adaptiveAllCellsFailureEvent gdec hash khash P c₀ pin chain L
          (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) wq pre post
          gate s0 sLast xg cells [] coeffsOf cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 5 * (2 * ChallengeUnionBound.tauTerm 8) + 4560 / (Fintype.card Block : ℚ) := by
  have h := adaptive_all_cells_failure_mass_le gdec hash khash P c₀ pin chain th0 L
    (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
    (challenge_truncated_round_causal m)
    (default_claims_extended_bounded L c s (challengeTruncatedMessage m) c.degreeBits
      (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) (by omega))
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) (by omega)
    wq pre post gate s0 sLast xg cells [] [] t pr coeffsOf cols 8 123
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hmlog)
    (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
    (fun _ hu => absurd hu (List.not_mem_nil _))
    (fun _ hu => absurd hu (List.not_mem_nil _))
    (by rw [hc13]; exact ReducedFullTransport.thirteen_counter_budget)
    (by rw [hcidx]; exact ReducedIndexLanes.eight_index_counter_budget)
    (by rw [hc13]; exact hclen)
  rw [hc13, hcidx] at h
  have harith : ((ReducedIndexLanes.indexStage 13 : Nat) : ℚ)
      * (((ReducedIndexLanes.indexStage 13 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [ReducedIndexLanes.index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

open Classical in
/-- (6) **THE FIVE-CELL CLOSED INSTANCE OF THE REPAIRED LINE**, at a used-claims record
whose shape matches `c`.  Same envelope, same one clash term; the acceptance conjunct of
each of the five per-cell events is no longer refuted by length arithmetic
(`shape_satisfiable_at_matching_claims`).  ACCEPTANCE IS STILL NEVER EXHIBITED. -/
theorem adaptive_all_cells_bound_at_thirteen_at_matching_claims (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (th0 : Transcript.Hash) (L W : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (m : Verifier.CoupledMessage) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element)) (hc13 : c.degreeBits = 13) (hcidx : c.indexBits = 8)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hcon : c.numConstants + c.numRouted ≤ W) (hwir : c.numWires ≤ W)
    (hrou : 2 * c.numRouted ≤ W) (hLW : 69 + 24 * W ≤ L)
    (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (adaptiveAllCellsFailureEventWith (matchingClaims c) gdec hash khash P c₀ pin chain L
          (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) wq pre post
          gate s0 sLast xg cells [] coeffsOf cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 5 * (2 * ChallengeUnionBound.tauTerm 8) + 4560 / (Fintype.card Block : ℚ) := by
  have h := adaptive_all_cells_failure_mass_le_at_claims (matchingClaims c) gdec hash khash P c₀
    pin chain th0 L (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
    (challenge_truncated_round_causal m)
    (matching_claims_extended_bounded L W c s (challengeTruncatedMessage m) c.degreeBits
      (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) hcon hwir hrou hLW
      (by omega))
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq) (by omega)
    wq pre post gate s0 sLast xg cells [] [] t pr coeffsOf cols 8 123
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hmlog)
    (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
    (fun _ hu => absurd hu (List.not_mem_nil _))
    (fun _ hu => absurd hu (List.not_mem_nil _))
    (by rw [hc13]; exact ReducedFullTransport.thirteen_counter_budget)
    (by rw [hcidx]; exact ReducedIndexLanes.eight_index_counter_budget)
    (by rw [hc13]; exact hclen)
  rw [hc13, hcidx] at h
  have harith : ((ReducedIndexLanes.indexStage 13 : Nat) : ℚ)
      * (((ReducedIndexLanes.indexStage 13 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [ReducedIndexLanes.index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

end Audit.Wire3.IndexHalfTransport
