import Audit.Wire3.SoundnessAssembly

/-!
# Audit.Wire3.ExtractorConstruction -- the extraction join, BY CONSTRUCTION

## What this module is

`SoundnessAssembly.AssemblyResidue` ASSUMES nineteen things about an accepted
run, and thirteen of them describe an EXTRACTED gate prover state `s0`, an
extracted cell tuple, and an extracted column family.  In a soundness argument
those objects are not assumed: they are DEFINED from what the verifier accepted
-- the used claims `p.used`, the challenges the transcript derives, and (under
R1b) the committed columns the WHIR tail authenticated.  This module writes that
extractor down and proves the residue fields for it.

Ten of the nineteen fields are discharged.  Nine of those ten were R2/R3
extraction assumptions; the tenth, `foldLevelOpening`, becomes a consequence of
R1b rather than a separate hypothesis.

## What is proved

1. **Section 2, the extracted state.**  `extractedState` is a
   `GateTerminalBinding.ProverState` whose wire columns are the extractor's
   cell-4 family and whose constant columns are its cell-3 family (the gate
   lane's witness and preprocessed groups in the adopted `OpenedClaimFold`
   numbering), each fitted by `fitColumn` to the row point's height and indexed
   by the width the accepted call's `Verifier.shape` already pins, and whose eq
   column is the adopted `EqTableProvenance.eqTable` AT THE DERIVED GATE TAU.
   Its `rounds` and `point` are BOTH `[]`: in the adopted semantics those two
   fields are the already-bound HISTORY that `bindChallenge` appends to and
   `intoProofAndPoint` returns, so a state before any bind has both empty.
   `extracted_eq_provenance` and `extracted_state_consistent` then hold with no
   hypothesis at all: the first is `⟨rfl, rfl⟩`, the second reads every clause
   of `GateDenseRound.Consistent` off the construction.  Neither asserts
   ANYTHING about column provenance: `fitColumn` pads and truncates, so
   consistency is a shape fact; the identification of those columns with the
   run's own claims is item 6 below and needs R1b.
2. **Section 3, the extracted cells.**  `extractedCells` is the proof's OWN
   claimed cells, so `extracted_cells_match_claims` -- the adopted extraction
   join `CellsMatchClaims` -- is a lift roundtrip.
3. **Section 4, the truth chain.**  `truth_chain_of_consistent_state` builds
   `GateClaimChain.TruthChain` for ANY consistent state whose live variable
   count matches the number of coupled rounds.  This is possible because
   `TruthChain` NEVER MENTIONS THE PROVER'S MESSAGES: it says each lane round's
   `truth` is `GateDenseRound.stateRound` of the current state and that the
   states advance by `bindChallenge` AT THAT TRUTH.  It is the DEFINITIONAL
   truth chain of the extracted tables, not the honest-prover statement
   "messages = truths".  Message/truth disagreement is absorbed by the OUTER bad
   event OFF THE DIAGONAL OF RUNNING CLAIMS: `ConditionalSoundness.roundBadSet a
   b r` is `∅` when `a = b`, and only when the two running claims DIFFER is it
   `outerAgreementPoints a b r.message r.truth`.  That is by design of
   `ConditionalSoundness.chain_separates`, which consumes the bad set only where
   the claims have already been separated; on the diagonal there is nothing to
   separate and the round contributes no bad points at all.
4. **Section 5, the slot coefficients.**  `slotCoefficientsOf` is a function of
   the extracted tables and `slot_coefficients_total` proves the residue's
   `some` from `Gates.validateConfiguration` (from acceptance) and the two row
   widths (from `Consistent`).
5. **Section 6, R1b.**  `committed_columns_of_tail_extraction` runs the proof of
   `SoundnessAssembly.fold_level_opening_of_tail_extraction` at the STRONGER
   adopted shape `InstalledWhirTail.TailExtractsCommittedTables`, keeping the
   per-column `opened` field.  `fold_level_of_openings` recovers
   `foldLevelOpening`; `committed_width_of_openings` shows `committedWidth` --
   recorded in the adopted inventory as not discharged, because the ENVELOPE
   gives only a capacity inequality -- follows from `opened` being an equation
   between the opened cell list and a `List.map`.
6. **Section 7, THE JOIN.**  `extracted_tables_bind_to_claims`: the fully bound
   extracted gate columns ARE the accepted call's claimed cells.  This is the
   adopted `lastCells` plus the last clause of
   `GateDerivedRejection.EqCellBinding`, and it is DERIVED from R1b's `opened`
   through `GateTerminalBinding.bound_column_is_packed_fold` and
   `EqTableProvenance.eq_table_packed_fold`.
7. **Sections 8-9.**  `assembly_residue_of_extraction` builds the whole adopted
   residue for the constructed data, and `explicit_good_draw_of_extraction`
   restates `SoundnessAssembly.explicit_good_draw_assembly` over it.  The
   hypothesis list of that theorem is the new residue inventory.

## What is NOT proved, and is not weakened

* **R1b itself.**  `InstalledWhirTail.TailExtractsCommittedTables` posits a
  FIXED extractor, reading the run's three commitment roots (one
  deployment-pinned, two from the proof) and the round-one opening, whose
  columns open the accepted claims.  That is WHIR proximity /
  list decoding plus sumcheck soundness: PROBABILISTIC, cryptographic, and NOT
  DISCHARGED anywhere in this tree.  Everything section 6 and section 7 derive
  is derived FROM it.
* **Joint satisfiability.**  `hacc` together with the hypotheses of
  `explicit_good_draw_of_extraction` is not exhibited at any concrete run;
  producing one would need an accepting proof for the explicit engine, which
  this module does not build and the adopted tree does not contain.
* **`gateConstraintsPositive`.**  `Verifier.envelope` caps `numGateConstraints`
  at 123 and never demands positivity, so it stays a hypothesis.
* **`activeFilter`.**  The all-zero-selector exclusion is a property of the
  EXTRACTED constants columns; a family whose selector filters vanish at every
  row satisfies everything else here, so it stays a hypothesis.  Under
  `ConstantsProvenance.SuppliedConstantsAreCommitted` it becomes a deployment
  property; that predicate is not assumed here.
* **`gatesDecode`.**  That SOME gate list decodes is a theorem of acceptance
  (`ExplicitEngine.accepted_gate_rows_are_the_decoded_length`); that it is this
  `pre ++ gate :: post` split is definitional pinning of the distinguished gate.
* **Circuit truth.**  The conclusion is constraint vanishing on the EXTRACTED
  tables at a good draw, not "the circuit is satisfied by a witness".
* **Hash security.**  `hash`, `thash` and `khash` are arbitrary deterministic
  functions; keccak is not modelled, and `PinnedWhirProfile.TableIsCanonical`
  carries the keccak idealisation for the two transcribed profile rows.
* **A soundness error.**  `hdraw` and `hidx` are facts about two fixed points of
  two explicit finite spaces; no theorem says the run's draws follow either law.
  The adopted mass bounds exclude the dominant WHIR/Merkle term and are NOT the
  system's soundness error.  The deployed wire-v3 profile is around the 100-bit
  design point.  Nothing here is a 125-bit claim.

## Adopted material used

`Audit.Wire3.SoundnessAssembly` (`engine`, `tailBase`, `AssemblyResidue`,
`explicit_good_draw_assembly`, `explicit_accepted_run_facts`,
`explicit_pinned_profile_row`), `Audit.Wire3.GateTerminalBinding`
(`ProverState`, `Cells`, `CellsMatchClaims`, `bindAll`, `bind_all_columns`,
`bound_column_is_packed_fold`, `mapOption` lemmas), `Audit.Wire3.GateDenseRound`
(`Consistent`, `stateRound`, `current_round_shaped`, `bind_challenge_consistent`),
`Audit.Wire3.GateClaimChain` (`TruthChain`, `honest_message_length`,
`truth_chain_numvars`), `Audit.Wire3.ConditionalSoundness` (`lane`, `LaneRound`,
`gateLaneOf`, `envelope_degree_bits_positive`), `Audit.Wire3.EqTableProvenance`
(`GateEqProvenance`, `eqTable`, `eq_table_length`, `eq_table_packed_fold`),
`Audit.Wire3.TranscriptProvenance` (`gateTauColumn`, `gatePointColumn`,
`gateAlphaElement`, `derived_column_lengths`), `Audit.Wire3.GatePointZeroCheck`
(`gate_point_column_is_the_gate_lane_challenges`),
`Audit.Wire3.OpenedClaimFold` (`boundCell`, `cellRow`, `rowOpenings`,
`CellOpensFullTable`, `expected_claim_cell_is_full_table_evaluation`),
`Audit.Wire3.IntegratedTerminalChain` (`HonestOpenings`),
`Audit.Wire3.InstalledWhirTail` (`TailExtractsCommittedTables`),
`Audit.Wire3.AlphaZeroCheck` (`slotCoefficients`, `configured_slot_coefficients`),
`Audit.Wire3.GateDerivedRejection` (`EqCellBinding`, `derived_table_widths`),
`Audit.Wire3.ExplicitEngine`.  Nothing above is restated or re-proved.
-/

namespace Audit.Wire3.ExtractorConstruction

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. Fitting an extracted column to the row point -/

def fitColumn (n : Nat) (col : List Element) : List Element :=
  (List.range (2 ^ n)).map (fun i => col.getD i 0)

theorem fit_column_length (n : Nat) (col : List Element) :
    (fitColumn n col).length = 2 ^ n := by
  rw [fitColumn, List.length_map, List.length_range]

theorem range_map_getD (l : List Element) :
    (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_get l 0 h2, List.get_eq_getElem]

theorem fit_column_of_full (n : Nat) (col : List Element) (h : col.length = 2 ^ n) :
    fitColumn n col = col := by
  have hr : fitColumn n col = (List.range col.length).map (fun i => col.getD i 0) := by
    rw [fitColumn, h]
  rw [hr, range_map_getD]

/-! ## 2. The extracted column family as a gate prover state -/

def extractedColumns (n w : Nat) (cols : List (List Element)) :
    List DenseMleIndexed.State :=
  (List.range w).map (fun i => ⟨n, fitColumn n (cols.getD i [])⟩)

theorem extracted_columns_length (n w : Nat) (cols : List (List Element)) :
    (extractedColumns n w cols).length = w := by
  rw [extractedColumns, List.length_map, List.length_range]

theorem extracted_columns_shape (n w : Nat) (cols : List (List Element)) :
    ∀ column ∈ extractedColumns n w cols, GateTerminalBinding.ColumnShape n column := by
  intro column hm
  rcases List.mem_map.mp hm with ⟨i, -, hc⟩
  subst hc
  exact ⟨fit_column_length n _, rfl⟩

theorem extracted_columns_evals_map (n w : Nat) (cols : List (List Element)) :
    (extractedColumns n w cols).map DenseMleIndexed.State.evaluations
      = (List.range w).map (fun i => fitColumn n (cols.getD i [])) := by
  rw [extractedColumns, List.map_map]
  rfl

theorem extracted_columns_evaluations (n w : Nat) (cols : List (List Element))
    (hw : cols.length = w) (hfull : ∀ col ∈ cols, col.length = 2 ^ n) :
    (extractedColumns n w cols).map DenseMleIndexed.State.evaluations = cols := by
  rw [extracted_columns_evals_map]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, hw]
  · intro i h1 h2
    have hlen : (cols.getD i []).length = 2 ^ n := by
      rw [List.getD_eq_get cols [] h2, List.get_eq_getElem]
      exact hfull _ (List.getElem_mem _ _ _)
    rw [List.getElem_map, List.getElem_range, fit_column_of_full n _ hlen,
      List.getD_eq_get cols [] h2, List.get_eq_getElem]

/-- **THE EXTRACTED GATE PROVER STATE.** Its wire columns are the extractor's
cell-4 family (`gateWitness`) and its constant columns the cell-3 family
(`gatePreprocessed`), each fitted to the row point's height and indexed by the
width the accepted call's own `Verifier.shape` pins; its eq column is the adopted
`EqTableProvenance.eqTable` AT THE DERIVED GATE TAU, so `GateEqProvenance` holds
by definition; and its `degree` is the configuration's. NOTHING HERE IS ASSUMED
ABOUT THE EXTRACTOR: `extract`, `roots` and `opening` are arbitrary.

`rounds` and `point` are BOTH EMPTY because this is the state BEFORE any
challenge is bound. In the adopted semantics those two fields are the
ALREADY-BOUND HISTORY, not a target: `GateTerminalBinding.bindChallenge` appends
one round message and one challenge per step, and `intoProofAndPoint` returns
the pair `(s.rounds, s.point)` it accumulated. A fresh state therefore has both
`[]` -- exactly the `hr`/`hp` hypotheses of
`GateClaimChain.honest_run_is_derived_rounds`. The derived gate point
`TranscriptProvenance.gatePointColumn` is NOT installed here; it is what the
bound run reproduces, and it enters only through the challenges of the lane.

**WITHOUT `hop`, THIS DEFINITION IDENTIFIES NOTHING ABOUT COMMITTED COLUMNS.**
`fitColumn` PADS WITH ZEROS AND TRUNCATES, so `extractedState` is total in
`extract` and `extracted_state_consistent` below holds for a family of any
shape whatsoever -- it is a shape fact, not a provenance fact. The
identification of these columns with the run's claims is
`extracted_tables_bind_to_claims`, and it is available only under `hop` (R1b),
where `fit_column_of_full` makes `fitColumn` the identity because the extracted
columns are already full tables for the row point. -/
def extractedState (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening) :
    GateTerminalBinding.ProverState :=
  { wires := extractedColumns (TranscriptProvenance.gateTauColumn thash c p).length c.numWires
      (extract roots opening 4)
    constants := extractedColumns (TranscriptProvenance.gateTauColumn thash c p).length
      c.numConstants (extract roots opening 3)
    eq := ⟨(TranscriptProvenance.gateTauColumn thash c p).length,
      EqTableProvenance.eqTable (TranscriptProvenance.gateTauColumn thash c p)⟩
    degree := c.quotientDegree + 2
    rounds := []
    point := [] }

theorem extracted_state_eq_numvars (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening) :
    (extractedState thash c p extract roots opening).eq.numVars
      = (TranscriptProvenance.gateTauColumn thash c p).length := rfl

/-- **`eqProvenance` HOLDS BY DEFINITION.** The extracted eq column IS the
adopted eq table at the derived gate tau. -/
theorem extracted_eq_provenance (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening) :
    EqTableProvenance.GateEqProvenance (extractedState thash c p extract roots opening)
      (TranscriptProvenance.gateTauColumn thash c p) :=
  ⟨rfl, rfl⟩

/-- **`extractedStateConsistent` HOLDS BY CONSTRUCTION.** Every clause of
`GateDenseRound.Consistent` is read off the construction: the two widths from
`List.range`, the three column shapes from `fitColumn`, the eq column's validity
from `EqTableProvenance.eq_table_length`, the degree from the literal, and the
`rounds`/`point` pairing -- the only clause `GateDenseRound.Consistent` imposes
on those two fields, namely `s.rounds.length = s.point.length` -- from both
being the empty history of a state before any bind. No fact about the extractor
and no fact about the run is used, and NO COLUMN PROVENANCE IS ASSERTED: see the
`extractedState` docstring on why `fitColumn` makes this a shape fact only. -/
theorem extracted_state_consistent (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening) :
    GateDenseRound.Consistent (Integrated.gateConfig c)
      (extractedState thash c p extract roots opening) := by
  refine ⟨⟨extracted_columns_length _ _ _, extracted_columns_length _ _ _, ⟨?_, rfl⟩,
    extracted_columns_shape _ _ _, extracted_columns_shape _ _ _⟩, rfl, rfl⟩
  show (EqTableProvenance.eqTable (TranscriptProvenance.gateTauColumn thash c p)).length
    = 2 ^ (TranscriptProvenance.gateTauColumn thash c p).length
  exact EqTableProvenance.eq_table_length _

/-! ## 3. The extracted cells ARE the accepted claims -/

theorem lift_toVerifier (xs : List Verifier.Ext3) :
    (OpenedClaimFold.lift xs).map Element.toVerifier = xs := by
  rw [OpenedClaimFold.lift, List.map_map]
  exact List.map_id _

/-- **THE EXTRACTED CELL TUPLE.** Its wire and constant entries are the accepted
call's OWN claimed cells (`p.used.gateWitness`, `p.used.gatePreprocessed.take
numConstants`), lifted; its eq entry is the verifier's own eq evaluation at the
derived gate tau and the derived gate point. Nothing is chosen freely. -/
def extractedCells (c : Verifier.Config) (p : Verifier.Proof) (tau point : List Element) :
    GateTerminalBinding.Cells :=
  { wires := OpenedClaimFold.lift p.used.gateWitness
    constants := OpenedClaimFold.lift (p.used.gatePreprocessed.take c.numConstants)
    eq := ⟨Norm.eqEvaluation (NormDenseRound.values tau) (NormDenseRound.values point)⟩ }

/-- **`cellsMatchClaims` HOLDS BY DEFINITION.** The adopted extraction join is
the statement that the bound wire and constant cells ARE the proof's claimed
`gateWitness` and `gatePreprocessed.take numConstants`; the extracted cell tuple
is defined to be exactly those, so the join is a lift roundtrip. WHAT THIS DOES
NOT DO is show that those cells are the fully bound columns of the extracted
state: that is the separate join of section 6. -/
theorem extracted_cells_match_claims (c : Verifier.Config) (p : Verifier.Proof)
    (tau point : List Element) :
    GateTerminalBinding.CellsMatchClaims c (extractedCells c p tau point)
      (GateTerminalBinding.gateTerminalInput p) :=
  ⟨lift_toVerifier _, lift_toVerifier _⟩

/-! ## 4. The truth chain of the extracted tables, BY CONSTRUCTION -/

/-- The extracted state's own round polynomial exists at every incomplete,
consistent state of a validated configuration. This is the adopted
`GateDenseRound.current_round_shaped` read back through
`GateDenseRound.currentRound`'s `Option.map`. -/
theorem state_round_total (cfg : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (s : GateTerminalBinding.ProverState)
    (hv : Gates.validateConfiguration cfg gates = some ())
    (hc : GateDenseRound.Consistent cfg s) (hn : ¬ GateDenseRound.isComplete s) :
    ∃ truth, GateDenseRound.stateRound cfg gates publicHash alpha s = some truth := by
  obtain ⟨message, hm, -, -⟩ :=
    GateDenseRound.current_round_shaped cfg gates publicHash alpha s hv hc hn
  cases hsr : GateDenseRound.stateRound cfg gates publicHash alpha s with
  | none =>
      rw [GateDenseRound.currentRound, hsr, Option.map_none'] at hm
      exact Option.noConfusion hm
  | some truth => exact ⟨truth, rfl⟩

/-- **THE TRUTH CHAIN IS DEFINITIONAL, NOT AN HONEST-PROVER ASSUMPTION.**
`GateClaimChain.TruthChain` never mentions the lane's `message` field: it says
that each lane round's `truth` IS `GateDenseRound.stateRound` of the current
extracted state and that the states advance by the source's own `bindChallenge`
AT THAT TRUTH. So for ANY consistent extracted state whose live variable count
matches the number of coupled rounds, the truth list is DETERMINED and the chain
holds. The prover's messages enter the soundness argument only through
`ConditionalSoundness.roundBadSet a b r`, which is `∅` on the diagonal `a = b`
and is the agreement set of MESSAGE against TRUTH only when the two running
claims DIFFER -- i.e. message/truth disagreement is absorbed by the outer bad
event OFF THE DIAGONAL OF RUNNING CLAIMS, which is exactly where
`ConditionalSoundness.chain_separates` consumes it. Nothing here assumes the
prover was honest. -/
theorem truth_chain_of_consistent_state (cfg : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hv : Gates.validateConfiguration cfg gates = some ())
    (commit : Verifier.CommitRound) (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3) :
    ∀ (ms : List Verifier.CoupledMessage) (st : Verifier.RoundState)
      (s : GateTerminalBinding.ProverState), GateDenseRound.Consistent cfg s →
      s.eq.numVars = ms.length → ms ≠ [] →
      ∃ (truths : List (List Element)) (sLast : GateTerminalBinding.ProverState) (x : Element),
        GateClaimChain.TruthChain cfg gates publicHash alpha sLast x s
          (ConditionalSoundness.lane commit sel pick truths st ms)
  | [], _, _, _, _, hne => absurd rfl hne
  | [m], st, s, hc, hnum, _ => by
      have hn : ¬ GateDenseRound.isComplete s := by
        unfold GateDenseRound.isComplete; rw [hnum]; simp
      obtain ⟨truth, htruth⟩ := state_round_total cfg gates publicHash alpha s hv hc hn
      refine ⟨[truth], s, OuterRound.lift (pick (commit st.transcript st.roundIndex m.1 m.2)), ?_⟩
      exact ⟨htruth, hnum, rfl, rfl⟩
  | m :: m2 :: rest, st, s, hc, hnum, _ => by
      have hlen : s.eq.numVars = rest.length + 2 := by rw [hnum]; simp
      have hn : ¬ GateDenseRound.isComplete s := by
        unfold GateDenseRound.isComplete; omega
      obtain ⟨truth, htruth⟩ := state_round_total cfg gates publicHash alpha s hv hc hn
      have htlen := GateClaimChain.honest_message_length cfg gates publicHash alpha s truth hv hc
        hn htruth
      obtain ⟨t, hb, hcons, hnv, -, -, -, -⟩ := GateDenseRound.bind_challenge_consistent cfg s
        (truth.map Element.toVerifier)
        (OuterRound.lift (pick (commit st.transcript st.roundIndex m.1 m.2))) hc hn
        (by rw [List.length_map, htlen, hc.2.1])
      obtain ⟨truths, sLast, x, hrec⟩ :=
        truth_chain_of_consistent_state cfg gates publicHash alpha hv commit sel pick
          (m2 :: rest) (Verifier.roundStep commit st m) t hcons (by simp; omega)
          (by exact List.cons_ne_nil _ _)
      exact ⟨truth :: truths, sLast, x, htruth, by omega, t, hb, hrec⟩

/-! ## 5. The slot coefficients of the extracted tables, BY CONSTRUCTION -/

/-- The alpha-side slot coefficient list of a row of the extracted tables. It is
a FUNCTION of the tables, not a choice. -/
def slotCoefficientsOf (cfg : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (s : GateTerminalBinding.ProverState) (i : Nat) :
    List Element :=
  (AlphaZeroCheck.slotCoefficients cfg gates (AlphaZeroCheck.rowWires s.tables i)
    (AlphaZeroCheck.rowConstants s.tables i) publicHash).getD []

/-- **`slotCoefficients` HOLDS BY CONSTRUCTION.** `AlphaZeroCheck.slotCoefficients`
is total on a validated configuration once the two row widths match, and both
widths come from `GateDenseRound.Consistent` through the adopted
`GateDerivedRejection.derived_table_widths`. The row bound is not used. -/
theorem slot_coefficients_total (c : Verifier.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (s : GateTerminalBinding.ProverState)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig c) s) (i : Nat) :
    AlphaZeroCheck.slotCoefficients (Integrated.gateConfig c) gates
      (AlphaZeroCheck.rowWires s.tables i) (AlphaZeroCheck.rowConstants s.tables i) publicHash
      = some (slotCoefficientsOf (Integrated.gateConfig c) gates publicHash s i) := by
  obtain ⟨hw, hc⟩ := GateDerivedRejection.derived_table_widths c s hcons
  obtain ⟨coeffs, hco, -⟩ := AlphaZeroCheck.configured_slot_coefficients (Integrated.gateConfig c)
    gates (AlphaZeroCheck.rowWires s.tables i) (AlphaZeroCheck.rowConstants s.tables i) publicHash
    hv (by rw [AlphaZeroCheck.rowWires_length]; exact hw)
    (by rw [AlphaZeroCheck.rowConstants_length]; exact hc)
  rw [slotCoefficientsOf, hco]
  rfl

/-! ## 6. R1b: the committed column family of THIS run -/

/-- **WHAT R1b GIVES ON THIS RUN.** `InstalledWhirTail.TailExtractsCommittedTables`
-- WHIR proximity / list decoding plus sumcheck soundness, a PROBABILISTIC
cryptographic assumption that is NOT discharged anywhere in the adopted tree --
names a fixed extractor from the run's three commitment roots (one
deployment-pinned, two from the proof) and the round-one opening. On an
accepted call of the explicit engine at a canonical profile row it yields
`OpeningBinding.OpensCommittedTable`, i.e. the adopted
`IntegratedTerminalChain.HonestOpenings`: the extracted columns are FULL tables
for the cell's row point (`full`), the family fits the index capacity
(`capacity`), and each opened claim cell is the per-column row fold of that
family (`opened`).

This is the proof of `SoundnessAssembly.fold_level_opening_of_tail_extraction`
run at the STRONGER of the two adopted R1b shapes, so that `opened` -- the
per-column identification the fold-level shape discards -- is available to the
join of section 7. -/
theorem committed_columns_of_tail_extraction (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (hT : PinnedWhirProfile.TableIsCanonical P)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hyp : InstalledWhirTail.TailExtractsCommittedTables hash wq)
    (hacc : Integrated.verify (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin
      chain c p = .ok ()) :
    ∃ (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
        List (List Element)) (roots : List Spongefish.Digest)
      (opening : WhirIntermediate.Opening),
      IntegratedTerminalChain.HonestOpenings c p
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
        (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
        (extract roots opening) := by
  obtain ⟨hwq, -, hrounds⟩ :=
    SoundnessAssembly.explicit_pinned_profile_row gdec hash thash khash P c₀ pin chain c p wq hT
      hrow hacc
  subst hwq
  obtain ⟨extract, hex⟩ := hyp
  have hacc2 : Integrated.verify (InstalledWhirTail.installedEngine
      (SoundnessAssembly.tailBase hash thash khash P c₀) gdec hash
      (PinnedWhirProfile.pinnedParams P c₀)) gdec pin chain c p = .ok () := hacc
  obtain ⟨r, hrun, -, -, -, -, -⟩ :=
    InstalledWhirTail.installed_acceptance_runs_the_concrete_tail
      (SoundnessAssembly.tailBase hash thash khash P c₀) gdec hash
      (PinnedWhirProfile.pinnedParams P c₀) pin chain c p hacc2
  obtain ⟨opening, hopen⟩ := InstalledWhirTail.tail_success_has_round_one_opening hash
    (PinnedWhirProfile.pinnedParams P c₀) _ _ _ hrounds r hrun
  refine ⟨extract, r.retained.origin.initial.commitments.map (fun x => x.root), opening, ?_⟩
  exact hex (SoundnessAssembly.tailBase hash thash khash P c₀) gdec pin chain c p r opening hacc2
    hrun hopen

/-- **`foldLevelOpening` FROM R1b's THREE FIELDS.** The adopted
`OpenedClaimFold.expected_claim_cell_is_full_table_evaluation` at each of the
five cells. -/
theorem fold_level_of_openings (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (cols : Fin 5 → List (List Element))
    (hop : IntegratedTerminalChain.HonestOpenings c p (Verifier.derivedRounds E c p)
      (Verifier.derivedIndices E c p) cols) (i : Fin 5) :
    OpenedClaimFold.CellOpensFullTable
      (Verifier.whirContext Connections.packedFold c p (Verifier.derivedRounds E c p)
        (Verifier.derivedIndices E c p))
      i.val (OpenedClaimFold.cellPoint i) (cols i)
      (OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds E c p) i))
      (OpenedClaimFold.lift
        (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices E c p) i).2) :=
  OpenedClaimFold.expected_claim_cell_is_full_table_evaluation c p _ _ i (cols i)
    (hop.full i) (hop.capacity i) (hop.opened i)

/-- **`committedWidth` IS DERIVABLE FROM R1b, NOT IRREDUCIBLE.** The adopted
inventory records it as not discharged because the ENVELOPE gives only a capacity
inequality. But `OpensCommittedTable.opened` is an equation between the opened
cell list and `rowOpenings`, which is a `List.map` over the columns, so the two
lengths agree. The residue keeps `committedWidth` only under the R3-free
`TailExtractsFoldLevel`, which drops `opened`. -/
theorem committed_width_of_openings (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (cols : Fin 5 → List (List Element))
    (hop : IntegratedTerminalChain.HonestOpenings c p (Verifier.derivedRounds E c p)
      (Verifier.derivedIndices E c p) cols) (i : Fin 5) :
    (cols i).length =
      (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices E c p) i).1.length := by
  have h := congrArg List.length (hop.opened i)
  rw [List.length_map, OpenedClaimFold.rowOpenings, List.length_map] at h
  exact h.symm

/-! ## 7. The join: the fully bound extracted columns ARE the accepted cells -/

theorem extracted_columns_take (n w : Nat) (cols : List (List Element))
    (hw : w ≤ cols.length) (hfull : ∀ col ∈ cols, col.length = 2 ^ n) :
    (extractedColumns n w cols).map DenseMleIndexed.State.evaluations = cols.take w := by
  rw [extracted_columns_evals_map]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.length_take]
    omega
  · intro i h1 h2
    have hiw : i < w := by rw [List.length_map, List.length_range] at h1; exact h1
    have hic : i < cols.length := by omega
    have hlen : (cols.getD i []).length = 2 ^ n := by
      rw [List.getD_eq_get cols [] hic, List.get_eq_getElem]
      exact hfull _ (List.getElem_mem _ _ _)
    rw [List.getElem_map, List.getElem_range, fit_column_of_full n _ hlen,
      List.getD_eq_get cols [] hic, List.get_eq_getElem]
    exact List.getElem_take cols hic hiw

theorem values_inj : ∀ (vs : List Element) (claims : List Verifier.Ext3),
    vs.map (fun v => v.toVerifier.val) = claims.map Subtype.val →
    vs = OpenedClaimFold.lift claims
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | v :: vs, cl :: cls, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      have hv : v = ⟨cl⟩ := GoldilocksExt3Field.element_eq v ⟨cl⟩ (Subtype.eq h.1)
      show _ = (cl :: cls).map Element.mk
      rw [List.map_cons, hv]
      exact congrArg _ (values_inj vs cls h.2)

/-- Binding a whole column list over a full point leaves one cell per column,
and the raw list of those cells IS the adopted `OpenedClaimFold.rowOpenings` of
the original columns at the point. The adopted
`GateTerminalBinding.bound_column_is_packed_fold`, lifted from one column to the
list. -/
theorem bound_columns_map (point : List Element) (n : Nat) (hp : point.length = n) :
    ∀ (source bound : List DenseMleIndexed.State),
      (∀ column ∈ source, GateTerminalBinding.ColumnShape n column) →
      GateTerminalBinding.mapOption (DenseMleIndexed.bindMany point) source = some bound →
      ∃ vs : List Element,
        bound.map DenseMleIndexed.State.evaluations = vs.map (fun v => [v]) ∧
        vs.map (fun v => v.toVerifier.val)
          = OpenedClaimFold.rowOpenings (source.map DenseMleIndexed.State.evaluations) point
  | [], bound, _, hb => by
      rw [GateTerminalBinding.map_option_nil_success _ _ hb]
      exact ⟨[], rfl, rfl⟩
  | column :: rest, bound, hs, hb => by
      obtain ⟨b, bs, hbc, hbr, hbe⟩ :=
        GateTerminalBinding.map_option_cons_success _ _ _ _ hb
      subst hbe
      obtain ⟨v, hv, -, hraw⟩ := GateTerminalBinding.bound_column_is_packed_fold n column b point
        (hs column (List.mem_cons_self _ _)) hp hbc
      obtain ⟨vs, h1, h2⟩ := bound_columns_map point n hp rest bs
        (fun col hc => hs col (List.mem_cons_of_mem _ hc)) hbr
      refine ⟨v :: vs, ?_, ?_⟩
      · rw [List.map_cons, List.map_cons, h1, hv]
      · rw [List.map_cons, hraw, h2]
        rfl

def stepOf (r : ConditionalSoundness.LaneRound) : List Verifier.Ext3 × Element :=
  (r.truth.map Element.toVerifier, r.challenge)

theorem step_challenges (rs : List ConditionalSoundness.LaneRound) :
    (rs.map stepOf).map Prod.snd = rs.map ConditionalSoundness.LaneRound.challenge := by
  rw [List.map_map]
  rfl

/-- **THE TRUTH CHAIN IS A `bindAll` OF THE EXTRACTED STATE ALONG THE DRAWN
CHALLENGES.** Every step of `GateClaimChain.TruthChain` is one source
`bindChallenge`, so the whole chain composes into the source's own `bindAll` over
the lane's steps, the final state stays `Consistent`, and the chain's
`bindTables sLast.tables x` IS that final state's tables. -/
theorem truth_chain_bind_all (cfg : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (sLast : GateTerminalBinding.ProverState) (x : Element)
    (hv : Gates.validateConfiguration cfg gates = some ()) :
    ∀ (rs : List ConditionalSoundness.LaneRound) (s : GateTerminalBinding.ProverState),
      GateDenseRound.Consistent cfg s →
      GateClaimChain.TruthChain cfg gates publicHash alpha sLast x s rs →
      ∃ t, GateTerminalBinding.bindAll s (rs.map stepOf) = some t ∧
        GateDenseRound.Consistent cfg t ∧
        GateTerminalBinding.bindTables sLast.tables x = t.tables
  | [], _, _, h => absurd h not_false
  | [r], s, hc, hh => by
      have hn : ¬ GateDenseRound.isComplete s := by
        have h1 := hh.2.1; unfold GateDenseRound.isComplete; omega
      have hlen := GateClaimChain.honest_message_length cfg gates publicHash alpha s r.truth hv hc
        hn hh.1
      obtain ⟨t, hb, hcons, -, -, -, -, htab⟩ := GateDenseRound.bind_challenge_consistent cfg s
        (r.truth.map Element.toVerifier) r.challenge hc hn
        (by rw [List.length_map, hlen, hc.2.1])
      refine ⟨t, ?_, hcons, ?_⟩
      · simp only [List.map_cons, List.map_nil, GateTerminalBinding.bindAll, stepOf,
          Option.bind_eq_bind, hb, Option.some_bind]
      · rw [hh.2.2.1, hh.2.2.2]
        exact htab.symm
  | r :: r2 :: rest, s, hc, hh => by
      have hn : ¬ GateDenseRound.isComplete s := by
        have h1 := hh.2.1; unfold GateDenseRound.isComplete; omega
      have hlen := GateClaimChain.honest_message_length cfg gates publicHash alpha s r.truth hv hc
        hn hh.1
      obtain ⟨t0, hb0, hrec⟩ := hh.2.2
      obtain ⟨t1, hb1, hcons1, -, -, -, -, -⟩ := GateDenseRound.bind_challenge_consistent cfg s
        (r.truth.map Element.toVerifier) r.challenge hc hn
        (by rw [List.length_map, hlen, hc.2.1])
      have ht : t1 = t0 := Option.some.inj (hb1.symm.trans hb0)
      subst ht
      obtain ⟨t, hbt, hconsT, htab⟩ := truth_chain_bind_all cfg gates publicHash alpha sLast x hv
        (r2 :: rest) t1 hcons1 hrec
      refine ⟨t, ?_, hconsT, htab⟩
      simp only [List.map_cons, GateTerminalBinding.bindAll, stepOf, Option.bind_eq_bind, hb0,
        Option.some_bind]
      exact hbt

theorem bound_cell_four (p : Verifier.Proof) (idx : Verifier.IndexPoints) :
    (OpenedClaimFold.boundCell p.used idx 4).1 = p.used.gateWitness := rfl

theorem bound_cell_three (p : Verifier.Proof) (idx : Verifier.IndexPoints) :
    (OpenedClaimFold.boundCell p.used idx 3).1 = p.used.gatePreprocessed := rfl

theorem cell_row_gate (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (i : Fin 5) (hi : i = 3 ∨ i = 4) :
    OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds E c p) i)
      = TranscriptProvenance.gatePointColumn E c p := by
  rcases hi with rfl | rfl <;> rfl

/-- **THE JOIN, DERIVED FROM R1b.** The fully bound extracted gate columns ARE
the accepted call's own claimed cells. This is the adopted residue's
`lastCells` together with the last clause of `GateDerivedRejection.EqCellBinding`,
and it is NOT assumed here: it is R1b's `opened` field (the per-column
identification of the opened claim cells with the row folds of the extracted
family) read through the adopted
`GateTerminalBinding.bound_column_is_packed_fold`, plus the eq column's own
`EqTableProvenance.eq_table_packed_fold`. -/
theorem extracted_tables_bind_to_claims (thash : Transcript.Hash) (E : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening)
    (t : GateTerminalBinding.ProverState) (steps : List (List Verifier.Ext3 × Element))
    (hop : IntegratedTerminalChain.HonestOpenings c p (Verifier.derivedRounds E c p)
      (Verifier.derivedIndices E c p) (extract roots opening))
    (hwidth : (TranscriptProvenance.gatePointColumn E c p).length = c.degreeBits)
    (htau : (TranscriptProvenance.gateTauColumn thash c p).length = c.degreeBits)
    (hgw : p.used.gateWitness.length = c.numWires)
    (hgp : c.numConstants ≤ p.used.gatePreprocessed.length)
    (hsteps : steps.map Prod.snd = TranscriptProvenance.gatePointColumn E c p)
    (hb : GateTerminalBinding.bindAll (extractedState thash c p extract roots opening) steps
      = some t) :
    t.tables = (extractedCells c p (TranscriptProvenance.gateTauColumn thash c p)
      (TranscriptProvenance.gatePointColumn E c p)).tables := by
  have hplen : (steps.map Prod.snd).length
      = (TranscriptProvenance.gateTauColumn thash c p).length := by
    rw [hsteps, hwidth, htau]
  have hrow4 : OpenedClaimFold.lift
      (OpenedClaimFold.cellRow (Verifier.derivedRounds E c p) 4)
      = TranscriptProvenance.gatePointColumn E c p := cell_row_gate E c p 4 (Or.inr rfl)
  have hrow3 : OpenedClaimFold.lift
      (OpenedClaimFold.cellRow (Verifier.derivedRounds E c p) 3)
      = TranscriptProvenance.gatePointColumn E c p := cell_row_gate E c p 3 (Or.inl rfl)
  have hrl4 : (OpenedClaimFold.cellRow (Verifier.derivedRounds E c p) 4).length
      = (TranscriptProvenance.gateTauColumn thash c p).length := by
    have h := congrArg List.length hrow4
    rw [OpenedClaimFold.lift, List.length_map] at h
    rw [h, hwidth, htau]
  have hrl3 : (OpenedClaimFold.cellRow (Verifier.derivedRounds E c p) 3).length
      = (TranscriptProvenance.gateTauColumn thash c p).length := by
    have h := congrArg List.length hrow3
    rw [OpenedClaimFold.lift, List.length_map] at h
    rw [h, hwidth, htau]
  have hfull4 : ∀ col ∈ extract roots opening 4,
      col.length = 2 ^ (TranscriptProvenance.gateTauColumn thash c p).length := by
    intro col hc
    rw [hop.full 4 col hc, hrl4]
  have hfull3 : ∀ col ∈ extract roots opening 3,
      col.length = 2 ^ (TranscriptProvenance.gateTauColumn thash c p).length := by
    intro col hc
    rw [hop.full 3 col hc, hrl3]
  have hop4 : p.used.gateWitness.map Subtype.val
      = OpenedClaimFold.rowOpenings (extract roots opening 4)
          (TranscriptProvenance.gatePointColumn E c p) := by
    have h := hop.opened 4
    rw [bound_cell_four, hrow4] at h
    exact h
  have hop3 : p.used.gatePreprocessed.map Subtype.val
      = OpenedClaimFold.rowOpenings (extract roots opening 3)
          (TranscriptProvenance.gatePointColumn E c p) := by
    have h := hop.opened 3
    rw [bound_cell_three, hrow3] at h
    exact h
  have hw4 : (extract roots opening 4).length = c.numWires := by
    have h := congrArg List.length hop4
    rw [List.length_map, OpenedClaimFold.rowOpenings, List.length_map] at h
    rw [← h]; exact hgw
  have hw3 : c.numConstants ≤ (extract roots opening 3).length := by
    have h := congrArg List.length hop3
    rw [List.length_map, OpenedClaimFold.rowOpenings, List.length_map] at h
    rw [← h]; exact hgp
  have hsw : (extractedState thash c p extract roots opening).wires.map
      DenseMleIndexed.State.evaluations = extract roots opening 4 :=
    extracted_columns_evaluations _ c.numWires _ hw4 hfull4
  have hsc : (extractedState thash c p extract roots opening).constants.map
      DenseMleIndexed.State.evaluations = (extract roots opening 3).take c.numConstants :=
    extracted_columns_take _ c.numConstants _ hw3 hfull3
  obtain ⟨hbw, hbc, hbe⟩ := GateTerminalBinding.bind_all_columns _ t steps hb
  obtain ⟨vsw, hvw1, hvw2⟩ := bound_columns_map (steps.map Prod.snd) _ hplen
    (extractedState thash c p extract roots opening).wires t.wires
    (extracted_columns_shape _ _ _) hbw
  obtain ⟨vsc, hvc1, hvc2⟩ := bound_columns_map (steps.map Prod.snd) _ hplen
    (extractedState thash c p extract roots opening).constants t.constants
    (extracted_columns_shape _ _ _) hbc
  obtain ⟨ve, hve1, -, hve2⟩ := GateTerminalBinding.bound_column_is_packed_fold
    (TranscriptProvenance.gateTauColumn thash c p).length
    (extractedState thash c p extract roots opening).eq t.eq (steps.map Prod.snd)
    ⟨EqTableProvenance.eq_table_length _, rfl⟩ hplen hbe
  have hvw : vsw = OpenedClaimFold.lift p.used.gateWitness := by
    refine values_inj vsw p.used.gateWitness ?_
    rw [hvw2, hsw, hsteps, ← hop4]
  have hvc : vsc = OpenedClaimFold.lift (p.used.gatePreprocessed.take c.numConstants) := by
    refine values_inj vsc _ ?_
    rw [hvc2, hsc, hsteps, OpenedClaimFold.rowOpenings, List.map_take,
      ← OpenedClaimFold.rowOpenings, ← hop3, List.map_take]
  have hveq : ve = ⟨Norm.eqEvaluation
      (NormDenseRound.values (TranscriptProvenance.gateTauColumn thash c p))
      (NormDenseRound.values (TranscriptProvenance.gatePointColumn E c p))⟩ := by
    refine GoldilocksExt3Field.element_eq _ _ (Subtype.eq ?_)
    rw [hve2]
    show Packed.fold
      (DenseMleIndexed.raw (EqTableProvenance.eqTable
        (TranscriptProvenance.gateTauColumn thash c p)))
      (DenseMleIndexed.raw (steps.map Prod.snd)) = _
    rw [hsteps, EqTableProvenance.eq_table_packed_fold _ _ (by rw [hwidth, htau])]
  have hres : t.tables = ⟨t.wires.map DenseMleIndexed.State.evaluations,
      t.constants.map DenseMleIndexed.State.evaluations, t.eq.evaluations⟩ := rfl
  rw [hres, hvw1, hvc1, hve1, hvw, hvc, hveq]
  rfl

/-! ## 8. The residue of the CONSTRUCTED extraction -/

/-- **THE RESIDUE, WITH TEN OF ITS NINETEEN FIELDS DISCHARGED.**

For the extracted state of section 2 and the extracted cells of section 3, at the
column family R1b hands this run, `SoundnessAssembly.AssemblyResidue` holds with
only the following still assumed: the two KECCAK fields, the four
deployment/ABI fields, the gate-list pinning `gatesDecode`, the envelope gap
`gateConstraintsPositive`, the all-zero-selector exclusion `activeFilter`, and
R1b itself (entering as `hop`). Everything else -- `extractedStateConsistent`,
`extractedTruthChain`, `lastCells`, `cellsMatchClaims`, `eqProvenance`,
`eqCellBinding`, `slotCoefficients`, `foldLevelOpening`, `extractedColumnHeight`,
`committedWidth` -- is PROVED here.

`gateTruths`, `sLast` and `xg` are not free: they are the truth list and the
final round data the extracted state itself determines along the challenges this
run drew, which is why they appear existentially rather than as parameters. -/
theorem assembly_residue_of_extraction (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams) (gates : List Gates.GateInfo)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening)
    (cellIndex : Fin 5)
    (hacc : Integrated.verify (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin
      chain c p = .ok ())
    (hop : IntegratedTerminalChain.HonestOpenings c p
      (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
      (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
      (extract roots opening))
    (hT : PinnedWhirProfile.TableIsCanonical P)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hdeploy : pin.configDigest = khash (ExplicitEngine.encodeConfig c₀))
    (hbounded : ExplicitEngine.Bounded c₀)
    (hgb : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hwb : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hdec : gdec c.gatesEncoding = some gates)
    (hpos : 0 < c.numGateConstraints)
    (hactive : ∃ i, i < 2 ^ c.degreeBits ∧ ∃ g ∈ gates,
      GateRejectionPower.rowFilter (Integrated.gateConfig c) g
        (extractedState thash c p extract roots opening).tables i ≠ Verifier.zero) :
    ∃ (gateTruths : List (List Element)) (sLast : GateTerminalBinding.ProverState)
      (xg : Element),
      SoundnessAssembly.AssemblyResidue gdec hash thash khash P c₀ pin c p wq gates
        (extractedState thash c p extract roots opening)
        sLast xg
        (extractedCells c p (TranscriptProvenance.gateTauColumn thash c p)
          (TranscriptProvenance.gatePointColumn
            (SoundnessAssembly.engine gdec hash thash khash P c₀) c p))
        gateTruths
        (slotCoefficientsOf (Integrated.gateConfig c) gates
          (GateTerminalBinding.publicHashFunction
            ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash
              p.publicInputs))
          (extractedState thash c p extract roots opening))
        cellIndex (extract roots opening) := by
  obtain ⟨henv, hsh, -, hlr, hgr, -, -, hgpw, -⟩ :=
    SoundnessAssembly.explicit_accepted_run_facts gdec hash thash khash P c₀ pin chain c p [] hacc
  obtain ⟨gates2, hdec2, -, hv2⟩ := ExplicitEngine.accepted_gate_rows_are_the_decoded_length gdec
    hash thash khash P c₀ pin chain c p hacc
  have hgates : gates2 = gates := Option.some.inj (hdec2.symm.trans hdec)
  rw [hgates] at hv2
  have hgw : p.used.gateWitness.length = c.numWires := by
    simp only [Verifier.shape, decide_eq_true_eq] at hsh
    tauto
  have hgpre : p.used.gatePreprocessed.length = c.numConstants + c.numRouted := by
    simp only [Verifier.shape, decide_eq_true_eq] at hsh
    tauto
  have htau := TranscriptProvenance.derived_column_lengths thash c p
  have hcons := extracted_state_consistent thash c p extract roots opening
  have hmslen : (p.logRounds.zip p.gateRounds).length = c.degreeBits := by
    rw [List.length_zip, hlr, hgr, Nat.min_self]
  have hmsne : p.logRounds.zip p.gateRounds ≠ [] := by
    intro hc0
    have := ConditionalSoundness.envelope_degree_bits_positive c henv
    rw [hc0] at hmslen
    simp only [List.length_nil] at hmslen
    omega
  obtain ⟨gateTruths, sLast, xg, hchain⟩ := truth_chain_of_consistent_state
    (Integrated.gateConfig c) gates
    (GateTerminalBinding.publicHashFunction
      ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash p.publicInputs))
    (TranscriptProvenance.gateAlphaElement thash c p) hv2
    (SoundnessAssembly.engine gdec hash thash khash P c₀).commitRound Prod.snd
    Verifier.RoundChallenges.gate (p.logRounds.zip p.gateRounds)
    (Verifier.start ((SoundnessAssembly.engine gdec hash thash khash P c₀).initialTranscript c p))
    _ hcons (by rw [extracted_state_eq_numvars, htau.2, hmslen]) hmsne
  have hchain2 : GateClaimChain.TruthChain (Integrated.gateConfig c) gates
      (GateTerminalBinding.publicHashFunction
        ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash p.publicInputs))
      (TranscriptProvenance.gateAlphaElement thash c p) sLast xg
      (extractedState thash c p extract roots opening)
      (ConditionalSoundness.gateLaneOf (SoundnessAssembly.engine gdec hash thash khash P c₀) c p
        gateTruths) := hchain
  obtain ⟨tFinal, hbindAll, -, hlast⟩ := truth_chain_bind_all (Integrated.gateConfig c) gates
    (GateTerminalBinding.publicHashFunction
      ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash p.publicInputs))
    (TranscriptProvenance.gateAlphaElement thash c p) sLast xg hv2 _ _ hcons hchain2
  have hstepsPoint : ((ConditionalSoundness.gateLaneOf
      (SoundnessAssembly.engine gdec hash thash khash P c₀) c p gateTruths).map stepOf).map
      Prod.snd = TranscriptProvenance.gatePointColumn
        (SoundnessAssembly.engine gdec hash thash khash P c₀) c p := by
    rw [step_challenges,
      ← GatePointZeroCheck.gate_point_column_is_the_gate_lane_challenges
        (SoundnessAssembly.engine gdec hash thash khash P c₀) c p gateTruths]
  have hjoin := extracted_tables_bind_to_claims thash
    (SoundnessAssembly.engine gdec hash thash khash P c₀) c p extract roots opening tFinal _ hop
    hgpw htau.2 hgw (by omega) hstepsPoint hbindAll
  have hstepsLen : ((ConditionalSoundness.gateLaneOf
      (SoundnessAssembly.engine gdec hash thash khash P c₀) c p gateTruths).map stepOf).length
      = (extractedState thash c p extract roots opening).eq.numVars := by
    rw [List.length_map]
    exact (GateClaimChain.truth_chain_numvars (Integrated.gateConfig c) gates _ _ sLast xg _ _
      hchain2).symm
  refine ⟨gateTruths, sLast, xg,
    { tableCanonical := hT
      canonicalRow := hrow
      deployment := hdeploy
      deployedBounded := hbounded
      gatesEncodingBound := hgb
      whirEncodingBound := hwb
      foldLevelOpening := fun i => fold_level_of_openings _ c p _ hop i
      extractedColumnHeight := hop.full cellIndex
      committedWidth := committed_width_of_openings _ c p _ hop cellIndex
      gatesDecode := hdec
      extractedStateConsistent := hcons
      extractedTruthChain := hchain2
      gateConstraintsPositive := hpos
      lastCells := hlast.trans hjoin
      cellsMatchClaims := extracted_cells_match_claims c p _ _
      eqProvenance := extracted_eq_provenance thash c p extract roots opening
      eqCellBinding := ⟨tFinal, _, hstepsLen, hbindAll, hjoin, hstepsPoint⟩
      activeFilter := hactive
      slotCoefficients := fun i _ => slot_coefficients_total c gates _ _ hv2 hcons i }⟩

/-! ## 9. THE RESTATED GOOD-DRAW THEOREM -/

/-- **`explicit_good_draw_assembly` WITH TEN RESIDUE FIELDS REMOVED.**

The hypothesis list below IS the new residue inventory. Beyond acceptance and
the two good-draw conditions it is:

* `hop` -- **R1b for this run**: the extracted column family of
  `InstalledWhirTail.TailExtractsCommittedTables`, delivered by
  `committed_columns_of_tail_extraction` from that predicate together with
  `hacc`, `hT` and `hrow`. WHIR proximity / list decoding plus sumcheck
  soundness; PROBABILISTIC and NOT DISCHARGED anywhere in the adopted tree.
* `hT`, `hrow` -- the two KECCAK idealisations about the pinned profile table.
* `hdeploy`, `hbounded`, `hgb`, `hwb` -- the deployment constructor fact and
  three ABI word bounds.
* `hdec` -- the gate-list PINNING. That SOME decoded list exists is a theorem
  (`ExplicitEngine.accepted_gate_rows_are_the_decoded_length`); that it is this
  particular `pre ++ gate :: post` split is definitional pinning of the
  distinguished gate.
* `hpos` -- `0 < c.numGateConstraints`. NOT DERIVABLE: `Verifier.envelope` caps
  `numGateConstraints` at 123 and never demands positivity.
* `hactive` -- the ALL-ZERO-SELECTOR EXCLUSION on the extracted constants
  columns. NOT DERIVABLE in general: a family whose selector filters all vanish
  at every row satisfies every other hypothesis here.

Nine fields of `SoundnessAssembly.AssemblyResidue` that this theorem's
predecessor assumed are GONE: `extractedStateConsistent`, `extractedTruthChain`,
`lastCells`, `cellsMatchClaims`, `eqProvenance`, `eqCellBinding`,
`slotCoefficients`, `extractedColumnHeight` and `committedWidth`, plus
`foldLevelOpening` which is now `hop`'s consequence rather than a separate
assumption.

**`logTruths`, `tb` AND `pr` ARE PHANTOM FOR THE GATE-SIDE CONCLUSION.** They
are universally quantified after the three existentials and do not appear in any
conjunct below; all they do is shape the LOG LANE inside
`SoundnessAssembly.outerBadEvent`, which the consumer must avoid. A poor choice
of them ENLARGES that bad event and so makes `hdraw` harder to satisfy, but it
can never make the conclusion vacuous: the gate-side conclusion is the same
statement for every choice, and the `∀` means the consumer may pick whichever
triple makes the bad event smallest.

**WHAT IS STILL NOT CLAIMED.** Joint satisfiability of `hacc` with these
hypotheses is not exhibited: no accepting proof for the explicit engine is built
here or anywhere in the adopted tree. The conclusion is GOOD-DRAW-CONDITIONAL
CONSTRAINT VANISHING ON THE EXTRACTED TABLES plus a per-column identification --
not circuit truth, not soundness of the deployed system, and not a probability
statement: `hdraw` and `hidx` are facts about two fixed points of two explicit
finite spaces, and nothing says the run's draws are distributed by either law.
No hash is modelled. The adopted mass bounds exclude the dominant WHIR/Merkle
term and are NOT the system's soundness error; the deployed wire-v3 profile sits
at around the 100-bit design point. There is no 125-bit claim anywhere. -/
theorem explicit_good_draw_of_extraction (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening)
    (cellIndex : Fin 5)
    (hacc : Integrated.verify (SoundnessAssembly.engine gdec hash thash khash P c₀) gdec pin
      chain c p = .ok ())
    (hop : IntegratedTerminalChain.HonestOpenings c p
      (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
      (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
      (extract roots opening))
    (hT : PinnedWhirProfile.TableIsCanonical P)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hdeploy : pin.configDigest = khash (ExplicitEngine.encodeConfig c₀))
    (hbounded : ExplicitEngine.Bounded c₀)
    (hgb : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hwb : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hdec : gdec c.gatesEncoding = some (pre ++ gate :: post))
    (hpos : 0 < c.numGateConstraints)
    (hactive : ∃ i, i < 2 ^ c.degreeBits ∧ ∃ g ∈ pre ++ gate :: post,
      GateRejectionPower.rowFilter (Integrated.gateConfig c) g
        (extractedState thash c p extract roots opening).tables i ≠ Verifier.zero) :
    ∃ (gateTruths : List (List Element)) (sLast : GateTerminalBinding.ProverState)
      (xg : Element),
      ∀ (logTruths : List (List Element)) (tb : NormDenseRound.Tables)
        (pr : NormDenseRound.Prepared),
      SoundnessAssembly.actualDigestDraw thash c p ∉ SoundnessAssembly.outerBadEvent thash
        (SoundnessAssembly.engine gdec hash thash khash P c₀) c p (pre ++ gate :: post)
        (extractedState thash c p extract roots opening)
        logTruths gateTruths tb pr
        (slotCoefficientsOf (Integrated.gateConfig c) (pre ++ gate :: post)
          (GateTerminalBinding.publicHashFunction
            ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash
              p.publicInputs))
          (extractedState thash c p extract roots opening)) →
      SoundnessAssembly.actualIndexDraw thash c p ∉ SoundnessAssembly.indexBadEvent c.indexBits
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
          (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
          cellIndex).1)
        (IndexPointZeroCheck.openedCells (extract roots opening cellIndex)
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow
            (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
            cellIndex))) →
      (∀ row, row < 2 ^ c.degreeBits →
          (∀ g2 ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig c) g2
            (extractedState thash c p extract roots opening).tables row = Verifier.zero) →
          (∀ g2 ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig c) g2
            (extractedState thash c p extract roots opening).tables row = Verifier.zero) →
          GateRejectionPower.rowFilter (Integrated.gateConfig c) gate
            (extractedState thash c p extract roots opening).tables row ≠ Verifier.zero →
          ∃ terms, GatesComplete.evaluateUnfiltered gate
              (AlphaZeroCheck.rowWires
                (extractedState thash c p extract roots opening).tables row)
              (AlphaZeroCheck.rowConstants
                (extractedState thash c p extract roots opening).tables row)
              (GateTerminalBinding.publicHashFunction
                ((SoundnessAssembly.engine gdec hash thash khash P c₀).publicInputsHash
                  p.publicInputs))
              (Integrated.gateConfig c).numSelectors = some terms ∧
            ∀ y ∈ terms, y = Verifier.zero)
        ∧ OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
              (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash thash khash P c₀) c p)
              cellIndex).1
            = IndexPointZeroCheck.openedCells (extract roots opening cellIndex)
                (OpenedClaimFold.lift (OpenedClaimFold.cellRow
                  (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash thash khash P c₀)
                    c p) cellIndex))
        ∧ (PinnedWhirProfile.pinnedParams P c₀ = wq ∧ 0 < wq.inDomainSamples ∧ wq.rounds ≠ [])
        ∧ (ExplicitEngine.core c = ExplicitEngine.core c₀
            ∨ ExplicitEngine.KhashCollision khash) := by
  obtain ⟨gateTruths, sLast, xg, H⟩ := assembly_residue_of_extraction gdec hash thash khash P c₀
    pin chain c p wq (pre ++ gate :: post) extract roots opening cellIndex hacc hop hT hrow
    hdeploy hbounded hgb hwb hdec hpos hactive
  refine ⟨gateTruths, sLast, xg, fun logTruths tb pr hdraw hidx => ?_⟩
  exact SoundnessAssembly.explicit_good_draw_assembly gdec hash thash khash P c₀ pin chain c p wq
    pre post gate _ sLast xg _ logTruths gateTruths tb pr _ cellIndex _ hacc H hdraw hidx

end Audit.Wire3.ExtractorConstruction
