import Audit.Wire3.GateRejectionPower
import Audit.Wire3.AlphaZeroCheck

/-!
# The gate lane's rejection power AT THE TRANSCRIPT-DERIVED CHALLENGES (wire v3)

## The gap this module closes

The adopted `Audit.Wire3.GateRejectionPower` gives the gate lane's conclusion
teeth, but its own header records that it does so with `tau` as a FREE
universally quantified variable:

> `tau` IS NOT TIED TO THE TRANSCRIPT.  Throughout this module `tau` is a free
> universally quantified variable, never identified with
> `(e.initialTranscript vc p).gateTau`.  So an adversary choosing `tau` AFTER
> fixing the tables is excluded only by the `hgood` hypothesis.

The same header defers "THE eqCell REPLACEMENT BRIDGE" — deriving the adopted
`GateClaimChain.Assumptions` field 8 from the full-table `GateEqProvenance` —
because that needs `tau = (e.initialTranscript vc p).gateTau` and the
identification of the binding steps with the derived `gatePoint`.  On the alpha
side the adopted `Audit.Wire3.AlphaZeroCheck` composition theorems likewise take
`alpha` free, and its `gate_constraints_vanish_at_derived_challenges` is
explicitly flagged as WEAKER than the state-based derived form because it takes
its eq premise as a raw `heq` on a bare `GateSuffixPolynomial.Tables`.

This module removes the free challenges FROM SECTIONS 3 AND 4 and from the
reduced assumption list.  SECTION 2 IS THE EXCEPTION AND SAYS SO: its four
theorems keep `alpha` as an implicit free variable pinned only through the
adopted `alphaMatches` field, and they merely INSTANTIATE `tau` at the list
`gateTauColumn hash vc p` without any premise that the engine used it; the
transcript tie arrives only in sections 3 and 4 through `hderiv`.  Those later
statements fix

* `tau := TranscriptProvenance.gateTauColumn hash vc p`, and
* `alpha := TranscriptProvenance.gateAlphaElement hash vc p`,

under the single transcript premise `TranscriptProvenance.DerivedInitial`, and
takes its eq premise through `EqTableProvenance.GateEqProvenance` on an actual
`GateTerminalBinding.ProverState`, never as a raw table equation.

## Adopted Lean reused, never re-implemented

`Audit.Wire3.GateRejectionPower` (`StrongAssumptions`,
`strong_gate_cube_sum_vanishes`, `rowFilter`),
`Audit.Wire3.GateClaimChain` (`Assumptions`, `TruthChain`, `endpointSum`,
`accepted_gate_cube_sum_vanishes`, `accepted_gate_configuration_valid`),
`Audit.Wire3.ZeroCheckSemantics` (`gate_rows_vanish_of_derived_tau`,
`zeroCheckBadSet`, `tupleOf`, `gateValue`),
`Audit.Wire3.AlphaZeroCheck` (`gate_constraints_vanish_of_tau_and_alpha`,
`selected_gate_constraints_vanish_of_tau_and_alpha`, `slotCoefficients`,
`slotValue`, `alphaBadSet`, `rowWires`, `rowConstants`, `element_mk_eq_zero`),
`Audit.Wire3.TranscriptProvenance` (`DerivedInitial`, `gateTauColumn`,
`gateAlphaElement`, `gatePointColumn`, `liftList`, `derived_column_lengths`,
`values_gate_tau_column`, `gate_alpha_element_matches`,
`gate_eq_cell_of_derived_table`, `derived_columns_at_source_counters`,
`Example.fixture_column_widths`),
`Audit.Wire3.EqTableProvenance` (`GateEqProvenance`, `bound_gate_eq_cell`, via
the previous item), `Audit.Wire3.OuterAdapter` (`fixtureConfig`,
`fixtureProof`), `Audit.Wire3.OuterInitial` (`withInitial`, `ext3At`,
`relationState`), `Audit.Wire3.GateSlotCommutation` (`rowFilter`).
Nothing above is restated or re-proved; the transcript derivation is NOT
re-derived here.

## What is proved

1. (1) SECTION 2, THE DERIVED-TAU RESTATEMENTS.  `derived_gate_cube_sum_vanishes`,
   `derived_gate_rows_vanish`, `derived_nonzero_row_forces_bad_tau` and
   `derived_assumptions_reject` are the adopted `strong_gate_cube_sum_vanishes`,
   `strong_gate_rows_vanish`, `nonzero_row_forces_bad_tau` and
   `strong_assumptions_reject` with `tau` INSTANTIATED at
   `gateTauColumn hash vc p`.  The eq-provenance field of `StrongAssumptions` is
   then literally `GateEqProvenance s0 (gateTauColumn hash vc p)`, and the cube
   index is `2 ^ vc.degreeBits`: the widths are DERIVED from the adopted
   `TranscriptProvenance.derived_column_lengths` (`derived_gate_tau_width`,
   `derived_eq_numVars`), never assumed.
2. (4) SECTION 3, THE eqCell REPLACEMENT.  `eq_cell_of_provenance` proves the
   adopted field 8 FROM `GateEqProvenance` at the derived tau, `DerivedInitial`
   and `EqCellBinding` (the structural fact that `s0` is bound along the
   verifier's own derived gate point onto the cell tuple `k`), through the
   adopted `TranscriptProvenance.gate_eq_cell_of_derived_table` /
   `EqTableProvenance.bound_gate_eq_cell`.  `derived_alpha_matches` proves the
   adopted field 7.  `DerivedGateAssumptions` is the resulting REDUCED list, and
   `adopted_assumptions_of_derived` / `strongAssumptions_of_derived` show it
   delivers the adopted eight-field and ten-field lists.
3. (2) SECTION 4, THE STRONGEST GATE STATEMENT.
   `derived_selected_gate_constraints_vanish`: acceptance, the reduced assumption
   list, gate-lane `BadEventFree`, the derived tau outside its zero-check bad set
   and the derived alpha outside the row's alpha bad set together force EVERY
   constraint of the gate selected at that row to be zero (and assert that its
   evaluator succeeds there).  `derived_gate_slots_vanish` is the per-slot form.
   Configuration validity, both table widths and the vanishing cube sum are all
   DERIVED here (from acceptance, from the adopted field 2 `Consistent`, and from
   `accepted_gate_cube_sum_vanishes`), not assumed.
4. (3) SECTION 5, NO FREE CHALLENGE REMAINS.  `adopted_alpha_is_derived_alpha`
   and `adopted_tau_is_derived_tau` prove that ANY `alpha` / `tau` satisfying the
   adopted transcript-matching premises IS the derived one, so the adopted free
   variables were never free once those premises were present.
   `challenge_hypotheses_are_source_squeezes` pins the two derived values to the
   source's own counter blocks (`9 + 3*degreeBits` for gate alpha,
   `12 + 3*degreeBits + 3*i` for gate tau coordinate `i`), and
   `only_two_challenge_hypotheses_remain` is the strongest per-slot theorem
   with the two `hgood` memberships curried past the colon: an INVENTORY, not
   a theorem about the hypothesis set.  Read literally it shows that, once the
   other premises are fixed, the two memberships `GoodDerivedTau` and
   `GoodDerivedAlpha` (both about DERIVED values) suffice.  It does NOT show
   they are the only challenge-side premises: `hfree` (adopted
   `BadEventFree`) is itself a per-round avoidance hypothesis on the
   gate-lane SUMCHECK challenges, so there are THREE challenge-side premises
   in total — two about tau/alpha and one about the round challenges.
5. (5) SECTION 6, THE FIXTURE.  `Example.fixture_derived` discharges
   `DerivedInitial` by `rfl` on the adopted `OuterAdapter.fixtureConfig` /
   `fixtureProof` for every `hash`; `Example.fixture_gate_slots_vanish`
   instantiates the strongest per-slot conclusion there, with the derivation
   premise gone.

## THE REDUCED FIELD LIST (before / after)

BEFORE — `GateRejectionPower.StrongAssumptions e decode vc p gates s0 sLast x k
alpha gateTruths tau`, with `alpha` and `tau` FREE, TEN fields:
`base.gatesDecode`, `base.extractedStateConsistent`, `base.extractedTruthChain`,
`base.gateConstraintsPositive`, `base.lastCells`, `base.cellsMatchClaims`,
`base.alphaMatches`, `base.eqCell`, `eqProvenance`, `activeFilter`.

AFTER — `DerivedGateAssumptions hash e decode vc p gates s0 sLast x k gateTruths`,
NO free challenge, NINE fields: `gatesDecode`, `extractedStateConsistent`,
`extractedTruthChain`, `gateConstraintsPositive`, `lastCells`,
`cellsMatchClaims`, `eqProvenance`, `eqCellBinding`, `activeFilter`.

* `alphaMatches` REMOVED — proved by `derived_alpha_matches` from `DerivedInitial`.
* `eqCell` REMOVED — proved by `eq_cell_of_provenance`.  So `eqProvenance`
  REPLACES field 8 rather than merely adding to it; the adopted header's
  "field 8 is KEPT rather than replaced" no longer applies.
* `eqCellBinding` ADDED.  It is binding data (which columns were bound, and
  along which challenge list) and it is what the adopted `bound_gate_eq_cell`
  consumes.  Note that its clause `steps.map Prod.snd = gatePointColumn e vc p`
  IS an equation on challenge values (the bound round-challenge list equals the
  verifier's derived gate point); it does not mention tau or alpha and does not
  contain the conclusion, but it is not challenge-free.  What would discharge
  it: threading the same extractor that supplies `extractedTruthChain` — the
  chain already binds `s0` along the drawn gate challenges — into the `bindAll`
  form.  That refactor is NOT done here.

## WHAT IS STILL OPEN AFTER THIS MODULE

* THE TWO `hgood` MEMBERSHIPS ARE HYPOTHESES, NOT EVENTS.  `GoodDerivedTau` and
  `GoodDerivedAlpha` are now about the DERIVED challenges, which is strictly more
  than the adopted free-variable form said — but they carry NO PROBABILITY and NO
  FIAT--SHAMIR argument.  `Transcript.Hash` remains an arbitrary deterministic
  function; nothing here says the derived tau or alpha is uniform, unpredictable,
  or independent of the prover's tables.  The adopted
  `ZeroCheckSemantics.zeroCheckBadSet_density_bound` and
  `AlphaZeroCheck.alphaBadSet_density_bound` are ideal-law counting statements
  over `(Element)^n` and `Element`, and NEITHER is composed with an `hgood`
  premise anywhere below.  ADAPTIVITY IS NOT ADDRESSED: both bad sets are indexed
  by the PROVER'S OWN TABLES, and the obligation to fix those tables by transcript
  material preceding the gate-alpha block (counter `9 + 3*degreeBits`) is exactly
  the obligation `ZeroCheckSemantics` and `AlphaZeroCheck` record, and is
  untouched here.
* PARTIAL SELECTOR ZEROING SURVIVES.  The adopted
  `GateRejectionPower.selector_forgery_survives_eq_provenance` exhibits a
  validated, constraint-positive state with a genuine eq table whose every row's
  gate aggregate is zero because every filter is zero; `activeFilter` excludes
  only that extreme.  Zeroing the filters on the rows that matter while leaving
  some gate active elsewhere satisfies `activeFilter` and is NOT excluded.
  Excluding it is a CONSTANTS-PROVENANCE obligation (the constants columns must be
  the committed preprocessed columns), part of the open extraction join.  Like the
  adopted field 4, `activeFilter` is a guard and NOT sufficient.
* THE EXTRACTION JOIN remains open exactly as in the adopted modules: field
  `cellsMatchClaims` (adopted assumption 6) is assumed outright, and nothing
  connects the values the WHIR/Merkle check bound to the cells of the extracted
  tables.  `extractedStateConsistent` and `extractedTruthChain` are the same
  extraction-boundary observations.
* CIRCUIT TRUTH IS OUTSIDE THE MODEL.  That the circuit's gate constraints are in
  fact zero at the honest witness is not proved, claimed or needed here; the
  conclusions are implications from acceptance.
* `DerivedGateAssumptions` IS NOT SHOWN TO BE INHABITED, since the adopted
  `GateClaimChain.Assumptions` is not.  Section 6 discharges the DERIVATION
  premise on a concrete fixture but exhibits no inhabitant of the assumption set.
* ROW INDICES AND COLUMN LENGTHS.  As in the adopted `AlphaZeroCheck`, the
  composition theorems use only the two WIDTH clauses of `TableShape`; a row index
  at or past a column's length reads the `List.getD … 0` padding, so on such an
  index the conclusion is a true statement about a ZERO row.  That is inherited
  verbatim from the adopted `gateValue` totalisation and is not an extra
  assumption; `derived_table_widths` supplies only the two width clauses, from the
  adopted field 2.
* No Rust/Solidity refinement, gas, WHIR profile, PCS, Merkle or memory claim.

Tactic note, inherited: `simp` / `ring` / `norm_num` must never see
`Fintype.card Element`, and `zeroCheckBadSet` is never stated at a literal arity —
its arity is always `(gateTauColumn hash vc p).length`, a generic term.  Nothing
below mentions `Fintype.card Element`.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace Audit.Wire3.GateDerivedRejection

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.EqTableProvenance Audit.Wire3.ZeroCheckSemantics
open Audit.Wire3.GateSuffixPolynomial Audit.Wire3.GateDenseRound
open Audit.Wire3.ConditionalSoundness
open Audit.Wire3.GateTerminalBinding (ProverState Cells publicHashFunction)
open Audit.Wire3.TranscriptProvenance (Hash DerivedInitial gateTauColumn gateAlphaElement
  gatePointColumn)
open Audit.Wire3.GateRejectionPower (StrongAssumptions)

/-! ## 1. Widths, DERIVED -/

theorem derived_gate_tau_width (hash : Hash) (vc : Verifier.Config) (p : Verifier.Proof) :
    (gateTauColumn hash vc p).length = vc.degreeBits :=
  (TranscriptProvenance.derived_column_lengths hash vc p).2

theorem derived_eq_numVars (hash : Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : ProverState) (hprov : GateEqProvenance s0 (gateTauColumn hash vc p)) :
    s0.eq.numVars = vc.degreeBits := by
  rw [← hprov.2]
  exact derived_gate_tau_width hash vc p

/-! ## 2. The derived-tau restatements -/

section DerivedTau
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {gates : List Gates.GateInfo} {s0 sLast : ProverState} {x : Element}
  {k : Cells} {alpha : Element} {gateTruths : List (List Element)}

theorem derived_gate_cube_sum_vanishes (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (A : StrongAssumptions e decode vc p gates s0 sLast x k alpha gateTruths
      (gateTauColumn hash vc p))
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths)) :
    cubeSum (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables
      (2 ^ vc.degreeBits) = 0 := by
  rw [← derived_gate_tau_width hash vc p]
  exact GateRejectionPower.strong_gate_cube_sum_vanishes pin chain A hacc hfree

theorem derived_gate_rows_vanish (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (A : StrongAssumptions e decode vc p gates s0 sLast x k alpha gateTruths
      (gateTauColumn hash vc p))
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths))
    (hgood : tupleOf (gateTauColumn hash vc p) ∉
      zeroCheckBadSet (gateTauColumn hash vc p).length
        (gateValue (Integrated.gateConfig vc) gates
          (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables)) :
    ∀ i, i < 2 ^ vc.degreeBits →
      gateValue (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i = 0 ∧
      rowElement (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i = 0 ∧
      ∀ v, rowTerm (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i = some v →
        v = Verifier.zero :=
  ZeroCheckSemantics.gate_rows_vanish_of_derived_tau hash vc p (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0 A.eqProvenance
    (derived_gate_cube_sum_vanishes hash pin chain A hacc hfree) hgood

theorem derived_nonzero_row_forces_bad_tau (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (A : StrongAssumptions e decode vc p gates s0 sLast x k alpha gateTruths
      (gateTauColumn hash vc p))
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths))
    (i : Nat) (hi : i < 2 ^ vc.degreeBits)
    (hnz : gateValue (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i ≠ 0) :
    tupleOf (gateTauColumn hash vc p) ∈
      zeroCheckBadSet (gateTauColumn hash vc p).length
        (gateValue (Integrated.gateConfig vc) gates
          (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables) := by
  by_contra hgood
  exact hnz ((derived_gate_rows_vanish hash pin chain A hacc hfree hgood i hi).1)

theorem derived_assumptions_reject (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (i : Nat) (hi : i < 2 ^ vc.degreeBits)
    (hnz : gateValue (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i ≠ 0)
    (hgood : tupleOf (gateTauColumn hash vc p) ∉
      zeroCheckBadSet (gateTauColumn hash vc p).length
        (gateValue (Integrated.gateConfig vc) gates
          (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables)) :
    ¬ (Integrated.verify e decode pin chain vc p = .ok () ∧
        StrongAssumptions e decode vc p gates s0 sLast x k alpha gateTruths
          (gateTauColumn hash vc p) ∧
        BadEventFree 0
          (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
            (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
          (gateLaneOf e vc p gateTruths)) := by
  rintro ⟨hacc, A, hfree⟩
  exact hgood (derived_nonzero_row_forces_bad_tau hash pin chain A hacc hfree i hi hnz)

end DerivedTau

/-! ## 3. The eq-cell REPLACEMENT and the reduced assumption list -/

section Reduced
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {gates : List Gates.GateInfo} {s0 sLast : ProverState} {x : Element}
  {k : Cells} {gateTruths : List (List Element)}

/-- THE BINDING DATA the eq-cell replacement needs, and nothing more: the fresh
gate state is bound, variable by variable, along the verifier's OWN derived gate
point, and the resulting tables are the cell tuple `k`.  Its second clause is an
equation on the bound challenge LIST (it equals the verifier's derived gate
point), so it is not challenge-free; what it is NOT is an equation on the eq
cell's VALUE, which the adopted field 8 it replaces was. -/
def EqCellBinding (e : Verifier.Engine) (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : ProverState) (k : Cells) : Prop :=
  ∃ (t : ProverState) (steps : List (List Verifier.Ext3 × Element)),
    steps.length = s0.eq.numVars ∧
    GateTerminalBinding.bindAll s0 steps = some t ∧
    t.tables = k.tables ∧
    steps.map Prod.snd = gatePointColumn e vc p

/-- (4) THE REPLACEMENT.  The full-table field `GateEqProvenance s0 (gateTauColumn …)`
IMPLIES the adopted `GateClaimChain.Assumptions.eqCell`, given `DerivedInitial`
and the binding data.  This is the bridge the adopted `GateRejectionPower`
header explicitly says it does NOT build. -/
theorem eq_cell_of_provenance (hash : Hash)
    (hderiv : DerivedInitial hash e vc p)
    (hprov : GateEqProvenance s0 (gateTauColumn hash vc p))
    (hbind : EqCellBinding e vc p s0 k) :
    k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript vc p).gateTau
        (Verifier.derivedRounds e vc p).gatePoint := by
  obtain ⟨t, steps, hsteps, hb, hkt, hpoint⟩ := hbind
  exact TranscriptProvenance.gate_eq_cell_of_derived_table hash e vc p s0.eq.numVars s0 t steps k
    hderiv rfl hsteps hprov hb hkt hpoint

/-- (4) The adopted field 7 (`alphaMatches`) at the derived alpha is the adopted
`TranscriptProvenance.gate_alpha_element_matches`; it is not a hypothesis any
more. -/
theorem derived_alpha_matches (hash : Hash) (hderiv : DerivedInitial hash e vc p) :
    (gateAlphaElement hash vc p).toVerifier = (e.initialTranscript vc p).gateAlpha :=
  TranscriptProvenance.gate_alpha_element_matches hash e vc p hderiv

/-- THE REDUCED GATE ASSUMPTION LIST.  `GateRejectionPower.StrongAssumptions` has
TEN fields (the adopted eight plus `eqProvenance` and `activeFilter`) and a FREE
`tau` and a FREE `alpha`.  This structure has NINE, no free challenge at all, and
the two challenge-valued fields of the adopted list are GONE:

* adopted field 7 `alphaMatches` — REMOVED, derived from `DerivedInitial`;
* adopted field 8 `eqCell` — REMOVED, derived from `eqProvenance` + `eqCellBinding`
  + `DerivedInitial` (`eq_cell_of_provenance`);
* `eqCellBinding` — ADDED: binding data whose second clause equates the bound
  challenge list with the derived gate point (a challenge-list equation, not an
  eq-cell value equation).

NOT PROVED, and inherited unchanged from the adopted list: `gatesDecode`,
`extractedStateConsistent`, `extractedTruthChain`, `gateConstraintsPositive`,
`lastCells`, `cellsMatchClaims`, `eqProvenance`, `activeFilter`.  Nothing here
makes any of them derivable; see the module header. -/
structure DerivedGateAssumptions (hash : Hash) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (vc : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 sLast : ProverState) (x : Element) (k : Cells)
    (gateTruths : List (List Element)) : Prop where
  /-- Adopted field 1, unchanged. -/
  gatesDecode : decode vc.gatesEncoding = some gates
  /-- Adopted field 2, unchanged. -/
  extractedStateConsistent : Consistent (Integrated.gateConfig vc) s0
  /-- Adopted field 3, unchanged except that `alpha` is now the DERIVED gate
  alpha rather than a free variable. -/
  extractedTruthChain : GateClaimChain.TruthChain (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) (gateAlphaElement hash vc p)
    sLast x s0 (gateLaneOf e vc p gateTruths)
  /-- Adopted field 4, unchanged. -/
  gateConstraintsPositive : 0 < vc.numGateConstraints
  /-- Adopted field 5, unchanged. -/
  lastCells : GateTerminalBinding.bindTables sLast.tables x = k.tables
  /-- Adopted field 6, unchanged: THE OPEN EXTRACTION JOIN. -/
  cellsMatchClaims : GateTerminalBinding.CellsMatchClaims vc k
    (GateTerminalBinding.gateTerminalInput p)
  /-- Strengthened field S1, now at the DERIVED gate tau. -/
  eqProvenance : GateEqProvenance s0 (gateTauColumn hash vc p)
  /-- The binding data that turns S1 into the adopted field 8. -/
  eqCellBinding : EqCellBinding e vc p s0 k
  /-- Strengthened field S2, at the derived width `vc.degreeBits`. -/
  activeFilter : ∃ i, i < 2 ^ vc.degreeBits ∧ ∃ g ∈ gates,
    GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero

/-- (4) The reduced list really does deliver the ADOPTED eight-field list, with
fields 7 and 8 PROVED rather than assumed. -/
theorem adopted_assumptions_of_derived (hash : Hash) (hderiv : DerivedInitial hash e vc p)
    (D : DerivedGateAssumptions hash e decode vc p gates s0 sLast x k gateTruths) :
    GateClaimChain.Assumptions e decode vc p gates s0 sLast x k (gateAlphaElement hash vc p)
      gateTruths :=
  { gatesDecode := D.gatesDecode
    extractedStateConsistent := D.extractedStateConsistent
    extractedTruthChain := D.extractedTruthChain
    gateConstraintsPositive := D.gateConstraintsPositive
    lastCells := D.lastCells
    cellsMatchClaims := D.cellsMatchClaims
    alphaMatches := derived_alpha_matches hash hderiv
    eqCell := eq_cell_of_provenance hash hderiv D.eqProvenance D.eqCellBinding }

/-- (4) …and the adopted STRENGTHENED list at `tau := gateTauColumn` and
`alpha := gateAlphaElement`, so every theorem of section 2 applies to it. -/
theorem strongAssumptions_of_derived (hash : Hash) (hderiv : DerivedInitial hash e vc p)
    (D : DerivedGateAssumptions hash e decode vc p gates s0 sLast x k gateTruths) :
    StrongAssumptions e decode vc p gates s0 sLast x k (gateAlphaElement hash vc p) gateTruths
      (gateTauColumn hash vc p) := by
  have hact : ∃ i, i < 2 ^ (gateTauColumn hash vc p).length ∧ ∃ g ∈ gates,
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero := by
    rw [derived_gate_tau_width hash vc p]
    exact D.activeFilter
  exact
    { base := adopted_assumptions_of_derived hash hderiv D
      eqProvenance := D.eqProvenance
      activeFilter := hact }

end Reduced

/-! ## 4. The alpha side at the derived alpha: the strongest gate statement -/

section Strongest
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {gates : List Gates.GateInfo} {s0 sLast : ProverState} {x : Element}
  {k : Cells} {gateTruths : List (List Element)}

/-- The two table WIDTHS the alpha step needs are DERIVED from the adopted field 2
(`Consistent`), not assumed. -/
theorem derived_table_widths (vc : Verifier.Config) (s0 : ProverState)
    (hcons : Consistent (Integrated.gateConfig vc) s0) :
    s0.tables.wires.length = (Integrated.gateConfig vc).numWires ∧
    s0.tables.constants.length = (Integrated.gateConfig vc).numConstants := by
  refine ⟨?_, ?_⟩
  · show (s0.wires.map DenseMleIndexed.State.evaluations).length = _
    rw [List.length_map]
    exact hcons.1.1
  · show (s0.constants.map DenseMleIndexed.State.evaluations).length = _
    rw [List.length_map]
    exact hcons.1.2.1

/-- The selector filter of `GateRejectionPower` (`Verifier.Ext3`-valued, read from
the supplied constants columns at a Boolean row) and the one `AlphaZeroCheck`
consumes (`Element`-valued, read from that row's constants list) are the SAME
read. -/
theorem rowFilter_eq_mk (c : Gates.Config) (g : Gates.GateInfo) (t : Tables) (i : Nat) :
    GateSlotCommutation.rowFilter c g (AlphaZeroCheck.rowConstants t i)
      = ⟨GateRejectionPower.rowFilter c g t i⟩ := rfl

theorem rowFilter_zero_iff (c : Gates.Config) (g : Gates.GateInfo) (t : Tables) (i : Nat) :
    GateSlotCommutation.rowFilter c g (AlphaZeroCheck.rowConstants t i) = 0
      ↔ GateRejectionPower.rowFilter c g t i = Verifier.zero := by
  rw [rowFilter_eq_mk]
  exact AlphaZeroCheck.element_mk_eq_zero _

/-- CHALLENGE-SIDE HYPOTHESIS 1, and the ONLY one on the tau side: the DERIVED
gate tau column avoids the adopted zero-check bad set of the supplied row values.
No probability, no Fiat--Shamir; see the module header. -/
def GoodDerivedTau (hash : Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (g : Nat → Element) : Prop :=
  tupleOf (gateTauColumn hash vc p) ∉ zeroCheckBadSet (gateTauColumn hash vc p).length g

/-- CHALLENGE-SIDE HYPOTHESIS 2, and the ONLY one on the alpha side: the DERIVED
gate alpha avoids the adopted alpha bad set of THIS row's slot list. -/
def GoodDerivedAlpha (hash : Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (coeffs : List Element) : Prop :=
  gateAlphaElement hash vc p ∉ AlphaZeroCheck.alphaBadSet coeffs

/-- (2) THE COMPOSITION AT BOTH DERIVED CHALLENGES, per slot.  Acceptance, the
reduced assumption list, gate-lane bad-event freedom, the derived tau outside its
zero-check bad set and the derived alpha outside this row's alpha bad set force
EVERY constraint slot of that row to be zero.

Everything the adopted `AlphaZeroCheck.gate_constraints_vanish_at_derived_challenges`
took as a raw hypothesis is DERIVED here: configuration validity from acceptance,
both table widths from `Consistent`, the eq table from `GateEqProvenance` (not a
raw `heq` on a bare `Tables`), and the vanishing cube sum from the adopted
`GateClaimChain.accepted_gate_cube_sum_vanishes`. -/
theorem derived_gate_slots_vanish (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (hderiv : DerivedInitial hash e vc p)
    (D : DerivedGateAssumptions hash e decode vc p gates s0 sLast x k gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0)
      (gateLaneOf e vc p gateTruths))
    (hgoodTau : GoodDerivedTau hash vc p
      (gateValue (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0.tables))
    (i : Nat) (hi : i < 2 ^ vc.degreeBits) (coeffs : List Element)
    (hcoeffs : AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) gates
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (publicHashFunction (e.publicInputsHash p.publicInputs)) = some coeffs)
    (hgoodAlpha : GoodDerivedAlpha hash vc p coeffs) :
    ∀ j, j < vc.numGateConstraints →
      AlphaZeroCheck.slotValue (Integrated.gateConfig vc) gates
        (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
        (publicHashFunction (e.publicInputsHash p.publicInputs)) j = 0 := by
  have hlen := derived_gate_tau_width hash vc p
  have hwidths := derived_table_widths vc s0 D.extractedStateConsistent
  have hsum : cubeSum (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) (gateAlphaElement hash vc p)
      s0.tables (2 ^ (gateTauColumn hash vc p).length) = 0 := by
    rw [hlen]
    exact derived_gate_cube_sum_vanishes hash pin chain
      (strongAssumptions_of_derived hash hderiv D) hacc hfree
  exact AlphaZeroCheck.gate_constraints_vanish_of_tau_and_alpha (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) (gateAlphaElement hash vc p)
    s0.tables (gateTauColumn hash vc p)
    (GateClaimChain.accepted_gate_configuration_valid e decode pin chain vc p gates hacc
      D.gatesDecode)
    hwidths.1 hwidths.2 D.eqProvenance.1 hsum hgoodTau i (by rw [hlen]; exact hi) coeffs hcoeffs
    hgoodAlpha

end Strongest

section StrongestSelected
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {pre post : List Gates.GateInfo} {g : Gates.GateInfo}
  {s0 sLast : ProverState} {x : Element} {k : Cells} {gateTruths : List (List Element)}

/-- (2) THE STRONGEST GATE STATEMENT THIS AUDIT CAN CURRENTLY MAKE.

An accepting `Integrated.verify` run, the reduced (transcript-derived) gate
assumption list, gate-lane `BadEventFree`, the DERIVED gate tau outside its
zero-check bad set and the DERIVED gate alpha outside this row's alpha bad set
together force EVERY constraint of the gate that is selected at that row to be
zero — and also ASSERT that the gate's evaluator succeeds there.

NO CHALLENGE IS UNIVERSALLY QUANTIFIED: `tau` and `alpha` are both the values the
adopted `TranscriptProvenance` derivation produces from `hash`, `vc` and `p`. -/
theorem derived_selected_gate_constraints_vanish (hash : Hash) (pin : Verifier.Pinned)
    (chain : Nat)
    (hderiv : DerivedInitial hash e vc p)
    (D : DerivedGateAssumptions hash e decode vc p (pre ++ g :: post) s0 sLast x k gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ g :: post)
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0)
      (gateLaneOf e vc p gateTruths))
    (hgoodTau : GoodDerivedTau hash vc p
      (gateValue (Integrated.gateConfig vc) (pre ++ g :: post)
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0.tables))
    (i : Nat) (hi : i < 2 ^ vc.degreeBits) (coeffs : List Element)
    (hcoeffs : AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) (pre ++ g :: post)
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (publicHashFunction (e.publicInputsHash p.publicInputs)) = some coeffs)
    (hgoodAlpha : GoodDerivedAlpha hash vc p coeffs)
    (hpre : ∀ g' ∈ pre,
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero)
    (hpost : ∀ g' ∈ post,
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero)
    (hactive :
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero) :
    ∃ terms, GatesComplete.evaluateUnfiltered g (AlphaZeroCheck.rowWires s0.tables i)
        (AlphaZeroCheck.rowConstants s0.tables i)
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (Integrated.gateConfig vc).numSelectors = some terms ∧
      ∀ y ∈ terms, y = Verifier.zero := by
  have hlen := derived_gate_tau_width hash vc p
  have hwidths := derived_table_widths vc s0 D.extractedStateConsistent
  have hsum : cubeSum (Integrated.gateConfig vc) (pre ++ g :: post)
      (publicHashFunction (e.publicInputsHash p.publicInputs)) (gateAlphaElement hash vc p)
      s0.tables (2 ^ (gateTauColumn hash vc p).length) = 0 := by
    rw [hlen]
    exact derived_gate_cube_sum_vanishes hash pin chain
      (strongAssumptions_of_derived hash hderiv D) hacc hfree
  exact AlphaZeroCheck.selected_gate_constraints_vanish_of_tau_and_alpha
    (Integrated.gateConfig vc) pre g post
    (publicHashFunction (e.publicInputsHash p.publicInputs)) (gateAlphaElement hash vc p)
    s0.tables (gateTauColumn hash vc p)
    (GateClaimChain.accepted_gate_configuration_valid e decode pin chain vc p (pre ++ g :: post)
      hacc D.gatesDecode)
    hwidths.1 hwidths.2 D.eqProvenance.1 hsum hgoodTau i (by rw [hlen]; exact hi) coeffs hcoeffs
    hgoodAlpha
    (fun g' hg' => (rowFilter_zero_iff _ g' _ i).2 (hpre g' hg'))
    (fun g' hg' => (rowFilter_zero_iff _ g' _ i).2 (hpost g' hg'))
    (fun hz => hactive ((rowFilter_zero_iff _ g _ i).1 hz))

end StrongestSelected

/-! ## 5. (3) NOTHING IN SECTIONS 2-4 QUANTIFIES OVER A FREE CHALLENGE -/

section NoFreeChallenge

/-- `NormDenseRound.values` (the verifier-side read) is inverted by
`TranscriptProvenance.liftList` (the prover-side lift). -/
theorem liftList_values (xs : List Element) :
    TranscriptProvenance.liftList (NormDenseRound.values xs) = xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      show OuterRound.lift y.toVerifier ::
        TranscriptProvenance.liftList (NormDenseRound.values ys) = y :: ys
      rw [ih]
      rfl

theorem values_injective (xs ys : List Element)
    (h : NormDenseRound.values xs = NormDenseRound.values ys) : xs = ys := by
  rw [← liftList_values xs, ← liftList_values ys, h]

/-- (3) THE ADOPTED FREE `alpha` WAS NEVER FREE.  Any `alpha` satisfying the
adopted `GateClaimChain.Assumptions.alphaMatches` IS the derived gate alpha. -/
theorem adopted_alpha_is_derived_alpha (hash : Hash) (e : Verifier.Engine)
    (vc : Verifier.Config) (p : Verifier.Proof) (hderiv : DerivedInitial hash e vc p)
    (alpha : Element) (halpha : alpha.toVerifier = (e.initialTranscript vc p).gateAlpha) :
    alpha = gateAlphaElement hash vc p :=
  GoldilocksExt3Field.element_eq _ _
    (halpha.trans (TranscriptProvenance.gate_alpha_element_matches hash e vc p hderiv).symm)

/-- (3) THE ADOPTED FREE `tau` WAS NEVER FREE EITHER.  Any `tau` satisfying the
adopted gate `htau` of `EqTableProvenance.bound_terminal_is_engine_gate_terminal_of_eq_table`
IS the derived gate tau column. -/
theorem adopted_tau_is_derived_tau (hash : Hash) (e : Verifier.Engine)
    (vc : Verifier.Config) (p : Verifier.Proof) (hderiv : DerivedInitial hash e vc p)
    (tau : List Element)
    (htau : NormDenseRound.values tau = (e.initialTranscript vc p).gateTau) :
    tau = gateTauColumn hash vc p :=
  values_injective tau _
    (htau.trans (TranscriptProvenance.values_gate_tau_column hash e vc p hderiv).symm)

/-- (3) BOTH AT ONCE. -/
theorem challenges_are_pinned_to_the_derivation (hash : Hash) (e : Verifier.Engine)
    (vc : Verifier.Config) (p : Verifier.Proof) (hderiv : DerivedInitial hash e vc p)
    (alpha : Element) (tau : List Element)
    (halpha : alpha.toVerifier = (e.initialTranscript vc p).gateAlpha)
    (htau : NormDenseRound.values tau = (e.initialTranscript vc p).gateTau) :
    alpha = gateAlphaElement hash vc p ∧ tau = gateTauColumn hash vc p :=
  ⟨adopted_alpha_is_derived_alpha hash e vc p hderiv alpha halpha,
   adopted_tau_is_derived_tau hash e vc p hderiv tau htau⟩

/-- `List.get?` commutes with the lift, by structural recursion (the Mathlib
`List.get?_map` is deprecated in this toolchain). -/
theorem get_map_lift : ∀ (xs : List Verifier.Ext3) (i : Nat),
    (xs.map OuterRound.lift).get? i = (xs.get? i).map OuterRound.lift
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => get_map_lift xs i

/-- (3) AND THE TWO SURVIVING CHALLENGE-SIDE HYPOTHESES ARE ABOUT SOURCE
SQUEEZES: the alpha they mention is the derivation's squeeze at counter block
`9 + 3*degreeBits` after the relation domain separator, and entry `i` of the tau
column they mention is its squeeze at `12 + 3*degreeBits + 3*i`.  Both are read
off the adopted `TranscriptProvenance.derived_columns_at_source_counters`. -/
theorem challenge_hypotheses_are_source_squeezes (hash : Hash) (vc : Verifier.Config)
    (p : Verifier.Proof) (i : Nat) (hi : i < vc.degreeBits) :
    gateAlphaElement hash vc p =
      OuterRound.lift (OuterInitial.ext3At hash
        (OuterInitial.relationState hash vc (Verifier.statement p)).digest
        (9 + 3 * vc.degreeBits)) ∧
    (gateTauColumn hash vc p).get? i =
      some (OuterRound.lift (OuterInitial.ext3At hash
        (OuterInitial.relationState hash vc (Verifier.statement p)).digest
        (12 + 3 * vc.degreeBits + 3 * i))) := by
  obtain ⟨-, halpha, htau⟩ :=
    TranscriptProvenance.derived_columns_at_source_counters hash vc p i hi
  refine ⟨congrArg OuterRound.lift halpha, ?_⟩
  show ((TranscriptProvenance.derived hash vc p).gateTau.map OuterRound.lift).get? i = _
  rw [get_map_lift, htau]
  rfl

end NoFreeChallenge

section Inventory
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {gates : List Gates.GateInfo} {s0 sLast : ProverState} {x : Element}
  {k : Cells} {gateTruths : List (List Element)}

/-- (3) THE HYPOTHESIS INVENTORY, AS ONE THEOREM.  With everything that is NOT
about a challenge fixed in advance — the derivation premise, the reduced
assumption list, acceptance, bad-event freedom, the row index and that row's slot
list — the strongest per-slot conclusion follows from TWO further hypotheses,
both memberships of DERIVED values.  This is an INVENTORY by currying, not a
theorem about the hypothesis set, and it does not make `hfree` disappear:
`BadEventFree` is a third challenge-side premise, on the gate-lane sumcheck
round challenges rather than on tau or alpha. -/
theorem only_two_challenge_hypotheses_remain (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (hderiv : DerivedInitial hash e vc p)
    (D : DerivedGateAssumptions hash e decode vc p gates s0 sLast x k gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0)
      (gateLaneOf e vc p gateTruths))
    (i : Nat) (hi : i < 2 ^ vc.degreeBits) (coeffs : List Element)
    (hcoeffs : AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) gates
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (publicHashFunction (e.publicInputsHash p.publicInputs)) = some coeffs) :
    GoodDerivedTau hash vc p
        (gateValue (Integrated.gateConfig vc) gates
          (publicHashFunction (e.publicInputsHash p.publicInputs))
          (gateAlphaElement hash vc p) s0.tables) →
      GoodDerivedAlpha hash vc p coeffs →
        ∀ j, j < vc.numGateConstraints →
          AlphaZeroCheck.slotValue (Integrated.gateConfig vc) gates
            (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
            (publicHashFunction (e.publicInputsHash p.publicInputs)) j = 0 :=
  fun hgoodTau hgoodAlpha =>
    derived_gate_slots_vanish hash pin chain hderiv D hacc hfree hgoodTau i hi coeffs hcoeffs
      hgoodAlpha

end Inventory

/-! ## 6. (5) A concrete instance on the adopted fixture, for EVERY hash

The adopted `Integrated.exampleEngine` uses a constant stand-in
`initialObservation`, so it cannot satisfy `DerivedInitial`; exactly as in
`TranscriptProvenance.Example`, the instance below is built on
`OuterInitial.withInitial hash e`, which satisfies it by `rfl`, over the adopted
`OuterAdapter.fixtureConfig` / `fixtureProof` (`degreeBits = 1`, so the Boolean
cube has two rows).

WHAT THIS SECTION DOES AND DOES NOT SHOW.  It shows the derivation premise is
DISCHARGED on a concrete configuration and proof, for every `hash`, and it
instantiates the strongest conclusion there.  It does NOT exhibit an inhabitant
of `DerivedGateAssumptions`: the adopted `GateClaimChain.Assumptions` is not
shown inhabited either (its extraction fields are boundary observations), so the
fixture instance is conditional in exactly the same way.  Nothing here is a
non-vacuity proof of the assumption set. -/

namespace Example

open Audit.Wire3.OuterAdapter (fixtureConfig fixtureProof)

/-- The fixture engine: any engine whose initial hook is the source derivation. -/
def engineOf (hash : Hash) (e : Verifier.Engine) : Verifier.Engine :=
  OuterInitial.withInitial hash e

/-- The single transcript premise of this whole module, DISCHARGED by `rfl`. -/
theorem fixture_derived (hash : Hash) (e : Verifier.Engine) :
    DerivedInitial hash (engineOf hash e) fixtureConfig fixtureProof := rfl

/-- The derived gate tau column is one coordinate wide on the fixture. -/
theorem fixture_gate_tau_width (hash : Hash) :
    (gateTauColumn hash fixtureConfig fixtureProof).length = 1 :=
  (TranscriptProvenance.Example.fixture_column_widths hash).2

/-- The Boolean cube the conclusion ranges over has two rows on the fixture. -/
theorem fixture_cube_rows : 2 ^ fixtureConfig.degreeBits = 2 := rfl

/-- Both surviving challenge-side hypotheses, on the fixture, speak about the
source's own squeezes: gate alpha at counter block `12` and the single gate tau
coordinate at counter block `15`, after the relation domain separator. -/
theorem fixture_challenges_are_source_squeezes (hash : Hash) :
    gateAlphaElement hash fixtureConfig fixtureProof =
      OuterRound.lift (OuterInitial.ext3At hash
        (OuterInitial.relationState hash fixtureConfig (Verifier.statement fixtureProof)).digest
        (9 + 3 * fixtureConfig.degreeBits)) ∧
    (gateTauColumn hash fixtureConfig fixtureProof).get? 0 =
      some (OuterRound.lift (OuterInitial.ext3At hash
        (OuterInitial.relationState hash fixtureConfig (Verifier.statement fixtureProof)).digest
        (12 + 3 * fixtureConfig.degreeBits + 3 * 0))) :=
  challenge_hypotheses_are_source_squeezes hash fixtureConfig fixtureProof 0 (by decide)

/-- (5) THE STRONGEST PER-SLOT CONCLUSION, INSTANTIATED ON THE FIXTURE, for every
`hash` and every engine whose remaining hooks are unconstrained.  The derivation
premise is gone (it is `fixture_derived`); the two `hgood` memberships remain, and
both are about the derived values pinned by `fixture_challenges_are_source_squeezes`. -/
theorem fixture_gate_slots_vanish (hash : Hash) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (gates : List Gates.GateInfo) (s0 sLast : ProverState) (x : Element) (k : Cells)
    (gateTruths : List (List Element))
    (D : DerivedGateAssumptions hash (engineOf hash e) decode fixtureConfig fixtureProof gates
      s0 sLast x k gateTruths)
    (hacc : Integrated.verify (engineOf hash e) decode pin chain fixtureConfig fixtureProof
      = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig fixtureConfig) gates
        (publicHashFunction
          ((engineOf hash e).publicInputsHash fixtureProof.publicInputs))
        (gateAlphaElement hash fixtureConfig fixtureProof) s0)
      (gateLaneOf (engineOf hash e) fixtureConfig fixtureProof gateTruths))
    (hgoodTau : GoodDerivedTau hash fixtureConfig fixtureProof
      (gateValue (Integrated.gateConfig fixtureConfig) gates
        (publicHashFunction
          ((engineOf hash e).publicInputsHash fixtureProof.publicInputs))
        (gateAlphaElement hash fixtureConfig fixtureProof) s0.tables))
    (i : Nat) (hi : i < 2) (coeffs : List Element)
    (hcoeffs : AlphaZeroCheck.slotCoefficients (Integrated.gateConfig fixtureConfig) gates
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (publicHashFunction
        ((engineOf hash e).publicInputsHash fixtureProof.publicInputs)) = some coeffs)
    (hgoodAlpha : GoodDerivedAlpha hash fixtureConfig fixtureProof coeffs) :
    ∀ j, j < fixtureConfig.numGateConstraints →
      AlphaZeroCheck.slotValue (Integrated.gateConfig fixtureConfig) gates
        (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
        (publicHashFunction
          ((engineOf hash e).publicInputsHash fixtureProof.publicInputs)) j = 0 :=
  derived_gate_slots_vanish hash pin chain (fixture_derived hash e) D hacc hfree hgoodTau i hi
    coeffs hcoeffs hgoodAlpha

end Example

end Audit.Wire3.GateDerivedRejection
