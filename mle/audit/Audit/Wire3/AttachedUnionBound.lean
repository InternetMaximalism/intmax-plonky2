import Audit.Wire3.ChallengeUnionBound
import Audit.Wire3.GateDerivedRejection

/-!
# Attaching the challenge union bound to the accepted execution's own tables

## The gap this module closes

The adopted `Audit.Wire3.ChallengeUnionBound.accepted_combined_union_bound`
bounds a sum of three masses, but its own docstring records the defect:

> IMPORTANT: the parameters `n`, `g` and `coeffsOf` of the tau and alpha
> summands are FREE in this theorem.  They are NOT tied to the accepted
> execution's gate tables or to `degreeBits`; only the outer summand is
> connected to the proof and configuration.

So the adopted statement is, on its tau and alpha halves, a bound on the mass of
an ARBITRARY set indexed by an ARBITRARY family: instantiating `g := fun _ => 0`
and `coeffsOf := fun _ => []` satisfies it with both masses zero, and nothing in
it points at the execution that was accepted.

Meanwhile the adopted `Audit.Wire3.GateDerivedRejection` fixes exactly the
objects the tau and alpha bad sets should be indexed by: the reduced,
challenge-free `DerivedGateAssumptions` (nine fields), the DERIVED memberships
`GoodDerivedTau` / `GoodDerivedAlpha`, and the strongest gate statement
`derived_selected_gate_constraints_vanish`.

This module joins the two.  Every set whose mass is bounded above is built from
the accepted execution's own data — `hash`, the engine `e`, the configuration
`vc`, the proof `p`, the decoded gate list and the extracted state `s0` — and
the arity of the tau lane is the configuration's own `vc.degreeBits`, DERIVED
through the adopted `GateDerivedRejection.derived_gate_tau_width` /
`TranscriptProvenance.derived_column_lengths`, never assumed.

## THE NUMBER PROVED HERE IS NOT THE SYSTEM'S SOUNDNESS ERROR

Repeated, in the same words the adopted `ChallengeUnionBound` uses, because
attaching the bound to a real execution makes it MORE quotable and therefore
MORE dangerous to quote:

`attached_combined_bound_numeric` ends at `combinedBound 13 8 13 123 ≤ 2^(-172)`
by the adopted exact rational theorem.  READ THAT AS WHAT IT IS.  It covers ONLY
(i) the outer sumcheck round-agreement events, (ii) the gate tau multilinear
zero check and (iii) the gate alpha zero check, each counted under an EXPLICIT
IDEAL UNIFORM LAW on an explicit finite space.  It EXCLUDES the entire
WHIR/Merkle contribution — proximity/list decoding, the query-repetition
profile, and Merkle collision resistance — which is the DOMINANT term.  The
deployed design point is around 100 BITS, not 172.  Quoting `2^-172` as the
wire-v3 soundness error would be wrong by roughly seventy bits.

HEADROOM.  The verification review of the adopted `ChallengeUnionBound` computed
the three terms exactly outside Lean: outer `~2^-184.39`, alpha `~2^-172.07`,
tau `~2^-188.30`, total `~2^-172.069`.  The alpha union DOMINATES the three, and
the bound `≤ 2^-172` holds with only about **0.07 bits (about 5%) of headroom**;
it is TIGHT to the envelope extremes.  `degreeBits = 14`, or `129` gate
constraints, would break it.  That finding is recorded here because this module
is the one that ties the alpha union's row count to `2 ^ vc.degreeBits` and its
list length to `vc.numGateConstraints`, i.e. to the two parameters the headroom
is tight in.

## THE DETERMINISTIC / PROBABILISTIC SEAM

In the same words as the adopted `Audit.Wire3.CommitmentOrder`: reading these
masses as probabilities of the real transcript has two halves.

* **(A) DETERMINISTIC.** The tables are fixed by transcript material that
  PRECEDES the challenge squeezes, so an adaptive prover cannot choose tables
  after seeing the challenge.  `CommitmentOrder` PROVES (A) for the gate lane,
  MODULO the visible `CommittedTables` extraction join.
* **(B) PROBABILISTIC.** The squeezes are uniform and independent of that
  preceding material.  **HALF (B) IS A HASH ASSUMPTION THIS AUDIT DOES NOT AND
  CANNOT PROVE.**  `Transcript.Hash` is an ARBITRARY deterministic function
  `Bytes → Digest`; for a fixed such function the gate challenge is a FUNCTION
  of the transcript prefix, so "uniform and independent given the prefix" is not
  even expressible here.  ONLY WITH (B) does an `hgood` hypothesis become a
  probability event.

Everything below is therefore: a DETERMINISTIC implication whose hypotheses are
two avoidance facts about the derived tau and the derived alpha, plus a COUNTING
statement about how large the corresponding bad sets are under an explicit ideal
law.  The bridge between them is (B), and it is absent.

## WHAT IS PROVED

1. `attachedRowValues` / `attachedTauBadSet` / `attachedTauTuple`: the tau lane
   at `n := vc.degreeBits` and `g :=` the row-aggregate family of the extracted
   state `s0` at the derived gate alpha — literally the family
   `GateDerivedRejection.GoodDerivedTau`'s bad set is indexed by.
   `attached_tau_tuple_ofFn` shows the attached tuple IS the derived tau column;
   `attached_tau_avoidance_iff` identifies avoiding the attached set with the
   adopted `GoodDerivedTau`; `attached_tau_mass_bound` is the instantiated mass.
2. `attachedSlotCoeffs` / `attachedAlphaUnion`: the alpha union at
   `coeffsOf :=` the per-row slot coefficients of `s0`'s tables and
   `rows := 2 ^ vc.degreeBits`.  `attached_slot_coeffs_spec` proves the family is
   the real one (the adopted `AlphaZeroCheck.configured_slot_coefficients` at
   every row); `attached_alpha_union_card_bound` and
   `attached_alpha_union_mass_bound` are the instantiated counts, with
   `vc.numGateConstraints ≤ 123` DERIVED from acceptance through
   `GateClaimChain.accepted_gate_configuration_valid` and
   `Gates.validateConfiguration`, not assumed;
   `attached_alpha_all_rows_good` turns ONE alpha outside the union into
   `GoodDerivedAlpha` on EVERY row simultaneously.
3. `attached_combined_union_bound`: the attached sum, whose only free objects are
   those of `DerivedGateAssumptions`, those of the norm-lane
   `ConditionalSoundness.Assumptions`, and acceptance.
   `outer_term_mono`, `alpha_term_mono`, `tau_term_mono` and
   `combined_bound_mono` prove monotonicity of `combinedBound` in EACH of its
   four arguments (the tau lane needs `1 ≤ |F| * (⌈2^256/p⌉/2^256)^3`, proved as
   `one_le_card_mul_ratio_cube`), and `attached_combined_bound_at_envelope` /
   `attached_combined_bound_numeric` specialise to `combinedBound 13 8 13 123`
   and then to `2^-172`.
4. `attached_all_rows_slots_vanish`, `attached_all_rows_selected_constraints_vanish`
   and `attached_seam`: the deterministic conclusion at every row, and the seam
   theorem carrying it together with the counting bound.
5. Examples at `vc.degreeBits = 1` only.

## BOUNDARIES

* THE THREE MASSES ARE NOT THE MASS OF A DISJUNCTION.  As the adopted
  `ChallengeUnionBound.combined_union_bound` says, the three summands live on
  three different sample spaces — one digest triple, an `n`-tuple of digest
  triples, one digest triple — and NO JOINT LAW is formalized.  `attached_seam`
  therefore states the SUM of the three separately bounded quantities, NOT the
  mass of the complement of the deterministic conjunction: that complement is
  not an event of any space this audit builds.  Stating it would be stating more
  than is proved.
* `failure` REMAINS A FREE RATIONAL, bounded above only, exactly as in
  `ConditionalSoundness`; `failure := 0, law := 0` satisfies the assumptions.
* THE THREE EVENTS ARE NEVER SHOWN TO BE THE ONLY BAD EVENTS.  `hfree`
  (`ConditionalSoundness.BadEventFree` on the gate lane) is a THIRD
  challenge-side hypothesis, on the per-round sumcheck challenges, and it is
  assumed here, not counted.
* ADAPTIVITY IS HALF (B), see above.  `DerivedGateAssumptions` is not shown to
  be inhabited, and the extraction join (`cellsMatchClaims`,
  `extractedStateConsistent`, `extractedTruthChain`, `eqCellBinding`) is open
  exactly as in the adopted modules.
* No WHIR/PCS/Merkle, gas, memory-refinement or Rust/Solidity claim.
* Tactic note, inherited: no NUMERAL-EVALUATING tactic may see
  `Fintype.card Element` (`ring` / `exact_mod_cast` do see it as an opaque atom,
  which is harmless); the only numeral evaluation is `norm_num
  [Arithmetic.modulus]` on ℚ literals built from
  `Arithmetic.modulus` and `2 ^ 256`.  No tuple `Finset` is instantiated at a
  literal arity `≥ 2`; the alpha family is the adopted named
  `ChallengeUnionBound.alphaFamily` (through `alphaUnionBadSet`), never an inline
  lambda over `alphaBadSet`.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace Audit.Wire3.AttachedUnionBound

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.GateTerminalBinding (ProverState Cells publicHashFunction)
open Audit.Wire3.TranscriptProvenance (Hash DerivedInitial gateTauColumn gateAlphaElement)

/-! ## 0. Two trivial configuration identities

`Integrated.gateConfig` copies three of the `Verifier.Config` fields the bound is
stated in; these are `rfl`, and are named only so the statements below can be
read in `Verifier.Config` quantities. -/

theorem gateConfig_numGateConstraints (vc : Verifier.Config) :
    (Integrated.gateConfig vc).numGateConstraints = vc.numGateConstraints := rfl

theorem gateConfig_quotientDegree (vc : Verifier.Config) :
    (Integrated.gateConfig vc).quotientDegree = vc.quotientDegree := rfl

/-! ## 1. THE TAU LANE, ATTACHED

The adopted tau term is `tauTerm n` for a free `n` and the bad set is
`zeroCheckBadSet n g` for a free `g`.  Here `n := vc.degreeBits`, DERIVED from
the adopted `GateDerivedRejection.derived_gate_tau_width` (itself the adopted
`TranscriptProvenance.derived_column_lengths`), and `g` is the row-aggregate
family of the extracted state `s0` at the DERIVED gate alpha — exactly the
family the adopted `GoodDerivedTau` names. -/

/-- THE ROW-AGGREGATE FAMILY OF THE ACCEPTED EXECUTION.  Row `i`'s gate
aggregate, read off the extracted state's own tables at the transcript-derived
gate alpha.  This is the `g` of `GateDerivedRejection.GoodDerivedTau` and of the
adopted `ZeroCheckSemantics.gate_rows_vanish_of_derived_tau`. -/
def attachedRowValues (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState) : Nat → Element :=
  ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) (gateAlphaElement hash vc p) s0.tables

theorem attachedRowValues_apply (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState) :
    attachedRowValues hash e vc p gates s0 =
      ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) (gateAlphaElement hash vc p)
        s0.tables := rfl

/-- (1) THE ATTACHED TAU BAD SET.  The adopted `ZeroCheckSemantics.zeroCheckBadSet`
at the CONFIGURATION'S OWN arity `vc.degreeBits` and at the accepted execution's
row-aggregate family.  Nothing here is free but the objects of
`DerivedGateAssumptions`. -/
noncomputable def attachedTauBadSet (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState) :
    Finset (ZeroCheckSemantics.Tuple vc.degreeBits) :=
  ZeroCheckSemantics.zeroCheckBadSet vc.degreeBits (attachedRowValues hash e vc p gates s0)

/-- The DERIVED tau column as a `vc.degreeBits`-tuple.  The transport is along
the adopted width `derived_gate_tau_width`, so the arity is derived, not
assumed. -/
noncomputable def attachedTauTuple (hash : Hash) (vc : Verifier.Config) (p : Verifier.Proof) :
    ZeroCheckSemantics.Tuple vc.degreeBits :=
  cast (congrArg ZeroCheckSemantics.Tuple (GateDerivedRejection.derived_gate_tau_width hash vc p))
    (ZeroCheckSemantics.tupleOf (gateTauColumn hash vc p))

/-- Transport of a bad-set membership along an equality of arities. -/
theorem transport_mem_zeroCheckBadSet {n m : Nat} (h : n = m) (g : Nat → Element)
    (r : ZeroCheckSemantics.Tuple n) :
    cast (congrArg ZeroCheckSemantics.Tuple h) r ∈ ZeroCheckSemantics.zeroCheckBadSet m g
      ↔ r ∈ ZeroCheckSemantics.zeroCheckBadSet n g := by
  subst h
  exact Iff.rfl

theorem ofFn_cast {n m : Nat} (h : n = m) (r : ZeroCheckSemantics.Tuple n) :
    List.ofFn (cast (congrArg ZeroCheckSemantics.Tuple h) r) = List.ofFn r := by
  subst h
  rfl

/-- (1) THE ATTACHED TUPLE IS THE TRANSCRIPT'S OWN TAU COLUMN.  Nothing was
invented by the transport: reading the tuple back off gives the adopted
`TranscriptProvenance.gateTauColumn` verbatim. -/
theorem attached_tau_tuple_ofFn (hash : Hash) (vc : Verifier.Config) (p : Verifier.Proof) :
    List.ofFn (attachedTauTuple hash vc p) = gateTauColumn hash vc p := by
  rw [attachedTauTuple, ofFn_cast (GateDerivedRejection.derived_gate_tau_width hash vc p)]
  exact ZeroCheckSemantics.ofFn_tupleOf _

/-- (1) AVOIDING THE ATTACHED SET *IS* THE ADOPTED `GoodDerivedTau`.  The
instantiated statement is neither weaker nor stronger than the adopted
challenge-side hypothesis; it is the same proposition at the derived arity. -/
theorem attached_tau_avoidance_iff (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState) :
    attachedTauTuple hash vc p ∉ attachedTauBadSet hash e vc p gates s0
      ↔ GateDerivedRejection.GoodDerivedTau hash vc p (attachedRowValues hash e vc p gates s0) :=
  not_congr (transport_mem_zeroCheckBadSet (GateDerivedRejection.derived_gate_tau_width hash vc p)
    (attachedRowValues hash e vc p gates s0) (ZeroCheckSemantics.tupleOf (gateTauColumn hash vc p)))

theorem attached_good_derived_tau (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState)
    (h : attachedTauTuple hash vc p ∉ attachedTauBadSet hash e vc p gates s0) :
    GateDerivedRejection.GoodDerivedTau hash vc p (attachedRowValues hash e vc p gates s0) :=
  (attached_tau_avoidance_iff hash e vc p gates s0).mp h

/-- (1) THE INSTANTIATED TAU MASS BOUND.  The adopted
`ChallengeUnionBound.tau_product_mass_bound` at `n := vc.degreeBits` and at the
accepted execution's own row family: the mass of the attached tau bad set under
the adopted `uniformProductProbability` on `Fin vc.degreeBits → DigestTriple` is
at most `tauTerm vc.degreeBits`.  The law is the EXPLICIT ideal product law of
the adopted module; its product structure IS the independence assumption. -/
theorem attached_tau_mass_bound (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState) :
    ChallengeUnionBound.uniformProductProbability vc.degreeBits
        (attachedTauBadSet hash e vc p gates s0)
      ≤ ChallengeUnionBound.tauTerm vc.degreeBits :=
  ChallengeUnionBound.tau_product_mass_bound vc.degreeBits (attachedRowValues hash e vc p gates s0)

/-! ## 2. THE ALPHA LANE, ATTACHED

The adopted alpha union is over a free family `coeffsOf` and a free row count.
Here the family is the per-row slot coefficient list of the extracted state's own
tables — the list `GateDerivedRejection.GoodDerivedAlpha`'s bad set is indexed by
at row `i` — and the row count is `2 ^ vc.degreeBits`, the cube of the derived
tau width. -/

/-- THE PER-ROW SLOT COEFFICIENTS OF THE ACCEPTED EXECUTION'S TABLES.  Total by
the adopted `Option.getD`; `attached_slot_coeffs_spec` shows the fallback branch
is never taken under acceptance. -/
noncomputable def attachedSlotCoeffs (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState) (i : Nat) :
    List Element :=
  (AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) gates
    (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
    (publicHashFunction (e.publicInputsHash p.publicInputs))).getD []

/-- (2) THE FAMILY IS THE REAL ONE.  Under acceptance-derived configuration
validity and the two table widths of the adopted field 2 (`Consistent`), the
adopted `AlphaZeroCheck.slotCoefficients` SUCCEEDS at every row and returns
exactly `attachedSlotCoeffs`, of length `vc.numGateConstraints`. -/
theorem attached_slot_coeffs_spec (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState)
    (hv : Gates.validateConfiguration (Integrated.gateConfig vc) gates = some ())
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0) (i : Nat) :
    AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) gates
        (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        = some (attachedSlotCoeffs e vc p gates s0 i) ∧
      (attachedSlotCoeffs e vc p gates s0 i).length = vc.numGateConstraints := by
  obtain ⟨hw, hc⟩ := GateDerivedRejection.derived_table_widths vc s0 hcons
  obtain ⟨coeffs, hs, hlen⟩ := AlphaZeroCheck.configured_slot_coefficients
    (Integrated.gateConfig vc) gates (AlphaZeroCheck.rowWires s0.tables i)
    (AlphaZeroCheck.rowConstants s0.tables i)
    (publicHashFunction (e.publicInputsHash p.publicInputs)) hv
    (by rw [AlphaZeroCheck.rowWires_length]; exact hw)
    (by rw [AlphaZeroCheck.rowConstants_length]; exact hc)
  have hgetD : attachedSlotCoeffs e vc p gates s0 i = coeffs := by
    rw [attachedSlotCoeffs, hs]
    rfl
  exact ⟨by rw [hgetD]; exact hs, by rw [hgetD]; exact hlen⟩

/-- (2) THE ATTACHED ALPHA UNION.  The adopted
`ChallengeUnionBound.alphaUnionBadSet` over the `2 ^ vc.degreeBits` Boolean rows
of the accepted execution's cube, at the accepted execution's own per-row slot
lists.  It is built from the adopted NAMED family `alphaFamily` (through
`alphaUnionBadSet`); no inline lambda over `alphaBadSet` appears anywhere. -/
noncomputable def attachedAlphaUnion (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState) : Finset Element :=
  ChallengeUnionBound.alphaUnionBadSet (2 ^ vc.degreeBits) (attachedSlotCoeffs e vc p gates s0)

/-- (2) THE INSTANTIATED CARDINALITY.  With `vc.numGateConstraints ≤ 123` DERIVED
from acceptance through `Gates.validateConfiguration`, the attached union has at
most `2 ^ vc.degreeBits * (vc.numGateConstraints - 1) ≤ 122 * 2 ^ vc.degreeBits`
points of the field. -/
theorem attached_alpha_union_card_bound (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState)
    (hv : Gates.validateConfiguration (Integrated.gateConfig vc) gates = some ())
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0) :
    (attachedAlphaUnion e vc p gates s0).card
        ≤ 2 ^ vc.degreeBits * (vc.numGateConstraints - 1) ∧
      vc.numGateConstraints ≤ 123 ∧
      (attachedAlphaUnion e vc p gates s0).card ≤ 122 * 2 ^ vc.degreeBits := by
  obtain ⟨hw, hc⟩ := GateDerivedRejection.derived_table_widths vc s0 hcons
  exact ChallengeUnionBound.alpha_union_configured_card_bound (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) s0.tables (2 ^ vc.degreeBits)
    (attachedSlotCoeffs e vc p gates s0) hv hw hc
    (fun i _ => (attached_slot_coeffs_spec e vc p gates s0 hv hcons i).1)

/-- (2) THE INSTANTIATED MASS.  Under the adopted single digest-triple law of
`OuterChallenge` — the SAME law the outer terms of `ConditionalSoundness` live
under — the attached union costs
`2 ^ vc.degreeBits * (vc.numGateConstraints - 1) * (⌈2^256/p⌉ / 2^256)^3`. -/
theorem attached_alpha_union_mass_bound (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState)
    (hv : Gates.validateConfiguration (Integrated.gateConfig vc) gates = some ())
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0) :
    OuterChallenge.uniformTupleProbability (attachedAlphaUnion e vc p gates s0)
      ≤ ChallengeUnionBound.alphaTerm (2 ^ vc.degreeBits) vc.numGateConstraints :=
  ChallengeUnionBound.alpha_union_mass_bound (2 ^ vc.degreeBits) vc.numGateConstraints
    (attachedSlotCoeffs e vc p gates s0)
    (fun i _ => le_of_eq (attached_slot_coeffs_spec e vc p gates s0 hv hcons i).2)

/-- (2) ONE ALPHA, EVERY ROW.  An alpha outside the attached union satisfies the
adopted `GateDerivedRejection.GoodDerivedAlpha` at EVERY row of the cube
simultaneously — which is what the adopted per-row hypothesis needed and what
the adopted module never supplied. -/
theorem attached_alpha_all_rows_good (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState)
    (hgood : gateAlphaElement hash vc p ∉ attachedAlphaUnion e vc p gates s0) :
    ∀ i, i < 2 ^ vc.degreeBits →
      GateDerivedRejection.GoodDerivedAlpha hash vc p (attachedSlotCoeffs e vc p gates s0 i) :=
  fun i hi => ChallengeUnionBound.alpha_outside_union (2 ^ vc.degreeBits)
    (attachedSlotCoeffs e vc p gates s0) (gateAlphaElement hash vc p) hgood i hi

/-! ## 3. Monotonicity of the adopted `combinedBound`

The envelope specialisation needs `combinedBound` to be monotone in each of its
four arguments over the ranges the envelope allows.  IT IS, and each part is
proved rather than assumed.  The only nontrivial part is the tau term:
`tauTerm n = n * (|F| * r^3)^n / |F|` with `r = ⌈2^256/p⌉ / 2^256`, which is
monotone precisely because the ceiling makes `|F| * r^3 ≥ 1`. -/

/-- The adopted digest ratio cubed times the field size is at least one: the
modulo-reduction CEILING never loses, `p * ⌈2^256/p⌉ ≥ 2^256`.  Proved by exact
rational arithmetic on ℚ literals built from `Arithmetic.modulus` and `2 ^ 256`;
`Fintype.card Element` is eliminated by the adopted `cardinality_exact` BEFORE
any numeral tactic runs. -/
theorem one_le_card_mul_ratio_cube :
    (1 : ℚ) ≤ (Fintype.card Element : ℚ)
      * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  rw [cardinality_exact, ChallengeUnionBound.digest_ratio_explicit]
  norm_num [Arithmetic.modulus]

/-- `tauTerm n = n * (|F| * r^3)^n / |F|`: the geometric form the monotonicity
argument runs on. -/
theorem tau_term_geometric (n : Nat) :
    ChallengeUnionBound.tauTerm n
      = (n : ℚ) * ((Fintype.card Element : ℚ)
          * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3) ^ n
        / (Fintype.card Element : ℚ) := by
  rw [ChallengeUnionBound.tauTerm, pow_mul, mul_pow]
  ring

/-- (3) MONOTONICITY OF THE TAU TERM.  Proved, not assumed. -/
theorem tau_term_mono {n m : Nat} (h : n ≤ m) :
    ChallengeUnionBound.tauTerm n ≤ ChallengeUnionBound.tauTerm m := by
  have hF : (0 : ℚ) < (Fintype.card Element : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := Element)
  have hc : (1 : ℚ) ≤ (Fintype.card Element : ℚ)
      * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 :=
    one_le_card_mul_ratio_cube
  have hnum : (n : ℚ) * ((Fintype.card Element : ℚ)
        * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3) ^ n
      ≤ (m : ℚ) * ((Fintype.card Element : ℚ)
        * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3) ^ m := by
    refine mul_le_mul (by exact_mod_cast h) (pow_le_pow_right hc h)
      (pow_nonneg (le_trans zero_le_one hc) n) (Nat.cast_nonneg _)
  rw [tau_term_geometric, tau_term_geometric]
  exact div_le_div_of_nonneg_right hnum hF.le

/-- (3) MONOTONICITY OF THE OUTER TERM in both of its arguments. -/
theorem outer_term_mono {db qd db' qd' : Nat} (hdb : db ≤ db') (hqd : qd ≤ qd') :
    ChallengeUnionBound.outerTerm db qd ≤ ChallengeUnionBound.outerTerm db' qd' := by
  rw [ChallengeUnionBound.outerTerm, ChallengeUnionBound.outerTerm]
  refine mul_le_mul_of_nonneg_right ?_ ChallengeUnionBound.digest_ratio_cube_nonneg
  have hn : 5 * db + (qd + 2) * db ≤ 5 * db' + (qd' + 2) * db' :=
    Nat.add_le_add (Nat.mul_le_mul_left 5 hdb) (Nat.mul_le_mul (by omega) hdb)
  exact_mod_cast hn

/-- (3) MONOTONICITY OF THE ALPHA TERM in both of its arguments. -/
theorem alpha_term_mono {rows rows' c c' : Nat} (hr : rows ≤ rows') (hc : c ≤ c') :
    ChallengeUnionBound.alphaTerm rows c ≤ ChallengeUnionBound.alphaTerm rows' c' := by
  rw [ChallengeUnionBound.alphaTerm, ChallengeUnionBound.alphaTerm]
  refine mul_le_mul_of_nonneg_right ?_ ChallengeUnionBound.digest_ratio_cube_nonneg
  have hn : rows * (c - 1) ≤ rows' * (c' - 1) :=
    Nat.mul_le_mul hr (Nat.sub_le_sub_right hc 1)
  exact_mod_cast hn

/-- (3) `combinedBound` IS MONOTONE IN EACH ARGUMENT, everywhere — not merely on
the envelope range.  This is what licenses replacing an execution's own
`degreeBits`, `quotientDegree` and `numGateConstraints` by the envelope
extremes. -/
theorem combined_bound_mono {db qd n c db' qd' n' c' : Nat}
    (hdb : db ≤ db') (hqd : qd ≤ qd') (hn : n ≤ n') (hc : c ≤ c') :
    ChallengeUnionBound.combinedBound db qd n c
      ≤ ChallengeUnionBound.combinedBound db' qd' n' c' := by
  rw [ChallengeUnionBound.combinedBound, ChallengeUnionBound.combinedBound]
  exact add_le_add (add_le_add (outer_term_mono hdb hqd) (tau_term_mono hn))
    (alpha_term_mono (Nat.pow_le_pow_right (by norm_num) hn) hc)

/-! ## 4. THE ATTACHED COMBINED BOUND

The theorem the module exists for.  Its only free objects are those of
`GateDerivedRejection.DerivedGateAssumptions`, those of the norm-lane
`ConditionalSoundness.Assumptions`, and acceptance.  There is NO free `n`, NO
free `g` and NO free `coeffsOf`. -/

section Attached
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {gates : List Gates.GateInfo} {s0 sLast : ProverState}
  {xg : Element} {k : Cells} {gateTruths : List (List Element)}
  {t tLast : NormDenseRound.Tables} {pr : NormDenseRound.Prepared}
  {constants extra : List Verifier.Ext3} {xn : Element}
  {logTruths gateCompareRounds : List (List Element)} {gateCompare : Element} {fixedness : Prop}
  {law : Finset Element → ℚ} {failure : ℚ}

/-- Configuration validity of the gate lane, DERIVED from acceptance. -/
theorem attached_configuration_valid (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p gates s0 sLast xg k
      gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ()) :
    Gates.validateConfiguration (Integrated.gateConfig vc) gates = some () :=
  GateClaimChain.accepted_gate_configuration_valid e decode pin chain vc p gates hacc D.gatesDecode

/-- (3) **THE ATTACHED COMBINED BOUND.**

`failure` (the free rational of the adopted `ConditionalSoundness`, bounded
ABOVE only) plus the product mass of the ATTACHED tau bad set plus the digest
mass of the ATTACHED alpha union is at most
`combinedBound vc.degreeBits vc.quotientDegree vc.degreeBits vc.numGateConstraints`,
every parameter read from the configuration of the accepted execution.

WHAT THIS IS NOT.  It is not the probability of a disjunction: the three
summands live on three different explicit finite spaces and no joint law is
formalized.  It is not a soundness error: the WHIR/Merkle term is absent.  And
`failure` is not lower-bounded by anything. -/
theorem attached_combined_union_bound (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p gates s0 sLast xg k
      gateTruths)
    (A : ConditionalSoundness.Assumptions e decode vc p t tLast pr constants extra xn logTruths
      gateCompareRounds gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ()) :
    failure
        + ChallengeUnionBound.uniformProductProbability vc.degreeBits
            (attachedTauBadSet hash e vc p gates s0)
        + OuterChallenge.uniformTupleProbability (attachedAlphaUnion e vc p gates s0)
      ≤ ChallengeUnionBound.combinedBound vc.degreeBits vc.quotientDegree vc.degreeBits
          vc.numGateConstraints := by
  have hv := attached_configuration_valid hash pin chain D hacc
  exact ChallengeUnionBound.accepted_combined_union_bound pin chain A hacc vc.degreeBits
    vc.numGateConstraints (attachedRowValues hash e vc p gates s0)
    (attachedSlotCoeffs e vc p gates s0)
    (fun i _ => le_of_eq
      (attached_slot_coeffs_spec e vc p gates s0 hv D.extractedStateConsistent i).2)

/-- (3) THE ENVELOPE SPECIALISATION.  Under the adopted `Verifier.envelope`
(`degreeBits ≤ 13`, `quotientDegree + 2 ≤ 10`) and the acceptance-derived
`numGateConstraints ≤ 123`, the attached bound is at most the closed form at the
extremes.  Monotonicity is PROVED (`combined_bound_mono`), not assumed. -/
theorem attached_combined_bound_at_envelope (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p gates s0 sLast xg k
      gateTruths)
    (A : ConditionalSoundness.Assumptions e decode vc p t tLast pr constants extra xn logTruths
      gateCompareRounds gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (henv : Verifier.envelope vc = true) :
    failure
        + ChallengeUnionBound.uniformProductProbability vc.degreeBits
            (attachedTauBadSet hash e vc p gates s0)
        + OuterChallenge.uniformTupleProbability (attachedAlphaUnion e vc p gates s0)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 := by
  obtain ⟨hdb, hqd⟩ := ConditionalSoundness.envelope_parameter_bounds vc henv
  have hv := attached_configuration_valid hash pin chain D hacc
  have h123 : vc.numGateConstraints ≤ 123 :=
    (attached_alpha_union_card_bound e vc p gates s0 hv D.extractedStateConsistent).2.1
  refine (attached_combined_union_bound hash pin chain D A hacc).trans ?_
  exact combined_bound_mono hdb (by omega) hdb h123

/-- (3) …AND THE NUMBER, by the adopted exact rational theorem.

**`2^-172` IS NOT THE SYSTEM'S SOUNDNESS ERROR.**  It omits the WHIR/Merkle
term, which DOMINATES; the deployed design point is around 100 bits.  It also
holds with only about 0.07 bits of headroom at the envelope extremes (the alpha
union dominates the three counted terms), so it is tight: `degreeBits = 14` or
`129` gate constraints (the first count at which it fails; 123..128 still
pass) would break it. -/
theorem attached_combined_bound_numeric (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p gates s0 sLast xg k
      gateTruths)
    (A : ConditionalSoundness.Assumptions e decode vc p t tLast pr constants extra xn logTruths
      gateCompareRounds gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (henv : Verifier.envelope vc = true) :
    failure
        + ChallengeUnionBound.uniformProductProbability vc.degreeBits
            (attachedTauBadSet hash e vc p gates s0)
        + OuterChallenge.uniformTupleProbability (attachedAlphaUnion e vc p gates s0)
      ≤ (1 : ℚ) / 2 ^ 172 :=
  (attached_combined_bound_at_envelope hash pin chain D A hacc henv).trans
    ChallengeUnionBound.combined_bound_at_extremes_numeric

end Attached

/-! ## 5. THE DETERMINISTIC SIDE AT EVERY ROW, AND THE SEAM -/

section Deterministic
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {gates : List Gates.GateInfo} {s0 sLast : ProverState}
  {xg : Element} {k : Cells} {gateTruths : List (List Element)}

/-- (4) EVERY SLOT OF EVERY ROW.  Acceptance, the reduced transcript-derived gate
assumption list, gate-lane `BadEventFree`, the derived tau outside the ATTACHED
tau bad set and the derived alpha outside the ATTACHED alpha union force every
constraint slot of every Boolean row of the cube to vanish.

The two avoidance hypotheses are now SINGLE facts about the accepted execution's
own bad sets — one tuple, one field element — rather than a per-row family of
hypotheses about free objects. -/
theorem attached_all_rows_slots_vanish (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (hderiv : DerivedInitial hash e vc p)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p gates s0 sLast xg k
      gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0)
      (ConditionalSoundness.gateLaneOf e vc p gateTruths))
    (hTau : attachedTauTuple hash vc p ∉ attachedTauBadSet hash e vc p gates s0)
    (hAlpha : gateAlphaElement hash vc p ∉ attachedAlphaUnion e vc p gates s0) :
    ∀ i, i < 2 ^ vc.degreeBits → ∀ j, j < vc.numGateConstraints →
      AlphaZeroCheck.slotValue (Integrated.gateConfig vc) gates
        (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
        (publicHashFunction (e.publicInputsHash p.publicInputs)) j = 0 := by
  intro i hi
  have hv := GateClaimChain.accepted_gate_configuration_valid e decode pin chain vc p gates hacc
    D.gatesDecode
  exact GateDerivedRejection.derived_gate_slots_vanish hash pin chain hderiv D hacc hfree
    (attached_good_derived_tau hash e vc p gates s0 hTau) i hi
    (attachedSlotCoeffs e vc p gates s0 i)
    (attached_slot_coeffs_spec e vc p gates s0 hv D.extractedStateConsistent i).1
    (attached_alpha_all_rows_good hash e vc p gates s0 hAlpha i hi)

end Deterministic

section Selected
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {pre post : List Gates.GateInfo} {g : Gates.GateInfo}
  {s0 sLast : ProverState} {xg : Element} {k : Cells} {gateTruths : List (List Element)}
  {t tLast : NormDenseRound.Tables} {pr : NormDenseRound.Prepared}
  {constants extra : List Verifier.Ext3} {xn : Element}
  {logTruths gateCompareRounds : List (List Element)} {gateCompare : Element} {fixedness : Prop}
  {law : Finset Element → ℚ} {failure : ℚ}

/-- (4) EVERY SELECTED GATE CONSTRAINT OF EVERY ROW.  The adopted
`GateDerivedRejection.derived_selected_gate_constraints_vanish` at the ATTACHED
bad sets: at any row where `g` is the selected gate (all other filters zero,
`g`'s filter nonzero) the gate's evaluator succeeds and every one of its
constraint terms is the field zero. -/
theorem attached_all_rows_selected_constraints_vanish (hash : Hash) (pin : Verifier.Pinned)
    (chain : Nat)
    (hderiv : DerivedInitial hash e vc p)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p (pre ++ g :: post) s0
      sLast xg k gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ g :: post)
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0)
      (ConditionalSoundness.gateLaneOf e vc p gateTruths))
    (hTau : attachedTauTuple hash vc p ∉ attachedTauBadSet hash e vc p (pre ++ g :: post) s0)
    (hAlpha : gateAlphaElement hash vc p ∉ attachedAlphaUnion e vc p (pre ++ g :: post) s0) :
    ∀ i, i < 2 ^ vc.degreeBits →
      (∀ g' ∈ pre,
        GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero) →
      (∀ g' ∈ post,
        GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero) →
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero →
      ∃ terms, GatesComplete.evaluateUnfiltered g (AlphaZeroCheck.rowWires s0.tables i)
          (AlphaZeroCheck.rowConstants s0.tables i)
          (publicHashFunction (e.publicInputsHash p.publicInputs))
          (Integrated.gateConfig vc).numSelectors = some terms ∧
        ∀ y ∈ terms, y = Verifier.zero := by
  intro i hi hpre hpost hactive
  have hv := GateClaimChain.accepted_gate_configuration_valid e decode pin chain vc p
    (pre ++ g :: post) hacc D.gatesDecode
  exact GateDerivedRejection.derived_selected_gate_constraints_vanish hash pin chain hderiv D hacc
    hfree (attached_good_derived_tau hash e vc p (pre ++ g :: post) s0 hTau) i hi
    (attachedSlotCoeffs e vc p (pre ++ g :: post) s0 i)
    (attached_slot_coeffs_spec e vc p (pre ++ g :: post) s0 hv D.extractedStateConsistent i).1
    (attached_alpha_all_rows_good hash e vc p (pre ++ g :: post) s0 hAlpha i hi)
    hpre hpost hactive

/-- (4) **THE DETERMINISTIC–PROBABILISTIC SEAM**, in one theorem with every
hypothesis visible.

GIVEN: an accepting `Integrated.verify` run; the reduced transcript-derived gate
assumption list `D`; the norm-lane `ConditionalSoundness.Assumptions` `A`;
gate-lane `BadEventFree`; the DERIVED tau outside the ATTACHED tau bad set; the
DERIVED alpha outside the ATTACHED alpha union.

THEN, simultaneously:

* **the deterministic half** — at every Boolean row of the cube, every
  constraint of the gate selected at that row vanishes and its evaluator
  succeeds; and
* **the counting half** — `failure` plus the mass of the attached tau bad set
  plus the mass of the attached alpha union is at most
  `combinedBound vc.degreeBits vc.quotientDegree vc.degreeBits vc.numGateConstraints`,
  under the EXPLICIT uniform laws: `uniformProductProbability` on the
  `(2^768)^(vc.degreeBits)` tuples of digest triples for the tau set, and
  `OuterChallenge.uniformTupleProbability` on the `2^768` digest triples for the
  alpha union.

**THE SECOND CONJUNCT IS A SUM OF THREE MASSES, NOT THE MASS OF THE COMPLEMENT
OF THE FIRST.**  The three quantities live on three different explicit finite
spaces and this audit formalizes no joint law over them, so "the probability
that the deterministic half fails" is not an expressible event here; the union
bound is the strongest honest form and is what is stated.  Likewise `failure`
remains the free, above-bounded rational of `ConditionalSoundness`, and `hfree`
is a THIRD challenge-side hypothesis (on the per-round sumcheck challenges) that
is assumed, not counted.

**AND READING THESE MASSES AS PROBABILITIES OF THE REAL TRANSCRIPT IS HALF (B),
A HASH ASSUMPTION.**  In the words of the adopted `CommitmentOrder`: half (A),
DETERMINISTIC — the tables are fixed by transcript material that PRECEDES the
challenge squeezes — is proved there for the gate lane modulo the visible
extraction join; half (B), PROBABILISTIC — the squeezes are uniform and
independent of that preceding material — **IS A HASH ASSUMPTION THIS AUDIT DOES
NOT AND CANNOT PROVE**, since `Transcript.Hash` is an ARBITRARY deterministic
function and `CommitmentOrder.separation_fails_for_a_deterministic_hash` refutes
even the weaker deterministic shadow of (B).  ONLY WITH (B) does an avoidance
hypothesis become a probability event.

**AND THE FIGURE EXCLUDES THE DOMINANT WHIR/MERKLE TERM AND IS NOT THE SYSTEM'S
SOUNDNESS ERROR.** -/
theorem attached_seam (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (hderiv : DerivedInitial hash e vc p)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p (pre ++ g :: post) s0
      sLast xg k gateTruths)
    (A : ConditionalSoundness.Assumptions e decode vc p t tLast pr constants extra xn logTruths
      gateCompareRounds gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ g :: post)
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0)
      (ConditionalSoundness.gateLaneOf e vc p gateTruths))
    (hTau : attachedTauTuple hash vc p ∉ attachedTauBadSet hash e vc p (pre ++ g :: post) s0)
    (hAlpha : gateAlphaElement hash vc p ∉ attachedAlphaUnion e vc p (pre ++ g :: post) s0) :
    (∀ i, i < 2 ^ vc.degreeBits →
        (∀ g' ∈ pre,
          GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero) →
        (∀ g' ∈ post,
          GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero) →
        GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero →
        ∃ terms, GatesComplete.evaluateUnfiltered g (AlphaZeroCheck.rowWires s0.tables i)
            (AlphaZeroCheck.rowConstants s0.tables i)
            (publicHashFunction (e.publicInputsHash p.publicInputs))
            (Integrated.gateConfig vc).numSelectors = some terms ∧
          ∀ y ∈ terms, y = Verifier.zero)
      ∧ failure
          + ChallengeUnionBound.uniformProductProbability vc.degreeBits
              (attachedTauBadSet hash e vc p (pre ++ g :: post) s0)
          + OuterChallenge.uniformTupleProbability
              (attachedAlphaUnion e vc p (pre ++ g :: post) s0)
        ≤ ChallengeUnionBound.combinedBound vc.degreeBits vc.quotientDegree vc.degreeBits
            vc.numGateConstraints :=
  ⟨attached_all_rows_selected_constraints_vanish hash pin chain hderiv D hacc hfree hTau hAlpha,
    attached_combined_union_bound hash pin chain D A hacc⟩

end Selected

/-! ## 6. Examples at a literal `vc.degreeBits = 1` only

No tuple `Finset` is instantiated at a literal arity `≥ 2`.  The alpha union is a
`Finset Element`, so its row count may be literal; the tau arity may not. -/

/-- At a one-bit cube the attached tau mass costs exactly one adopted
digest-triple ratio factor. -/
theorem attached_tau_mass_bound_one_bit (hash : Hash) (e : Verifier.Engine)
    (vc : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState)
    (hdb : vc.degreeBits = 1) :
    ChallengeUnionBound.uniformProductProbability vc.degreeBits
        (attachedTauBadSet hash e vc p gates s0)
      ≤ ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  refine (attached_tau_mass_bound hash e vc p gates s0).trans ?_
  rw [hdb, ChallengeUnionBound.tau_term_one]

/-- At a one-bit cube the attached alpha union covers two rows, so it has at most
`2 * (vc.numGateConstraints - 1)` points. -/
theorem attached_alpha_union_card_one_bit (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : ProverState)
    (hv : Gates.validateConfiguration (Integrated.gateConfig vc) gates = some ())
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0)
    (hdb : vc.degreeBits = 1) :
    (attachedAlphaUnion e vc p gates s0).card ≤ 2 * (vc.numGateConstraints - 1) := by
  have h := (attached_alpha_union_card_bound e vc p gates s0 hv hcons).1
  rw [hdb] at h
  simpa using h

end Audit.Wire3.AttachedUnionBound
