import Audit.Wire3.CommitmentOrder
import Audit.Wire3.JointChallengeSpace
import Audit.Wire3.ExtractorConstruction
import Audit.Wire3.RawIndexLanes

/-!
# Audit.Wire3.CommitmentOrderSurvey -- what the "FIXED DATA" residue actually is

The ROM line of work (`ReducedFullTransport`, `ReducedIndexLanes`,
`ReducedEngineIndex`, `RawBlockLanes`, `RawIndexLanes`, `RunLevelTransportAudit`)
repeatedly states that the zero-check table `g`, the row coefficients `coeffsOf`
and the committed columns `cols` are FIXED DATA, bound outside the oracle law,
and that identifying them with the deployed tables is "the adopted
`CommitmentOrder` reading with its open `CommittedTables` join".  This module
determines what that residue IS, by separating five different things that the
one phrase covers.

## The five categories, and where each argument of the bad events lands

    (a) DEPLOYMENT / VK data, fixed by the constructor-time configuration digest.
    (b) STATEMENT data, absorbed RAW into the twenty-two-frame prefix.
    (c) R1b EXTRACTOR OUTPUT -- a function of the commitment roots AND of the
        round-one WHIR opening.
    (d) A GENUINELY OPEN JOIN -- `CommitmentOrder.CommittedTables` and its kin.
    (e) A SQUEEZED CHALLENGE AT AN EARLIER COUNTER OF THE SAME DIGEST.  This
        category is the one the first reading of this module collapsed into (b),
        and it is not (b): a value here is a function of the prefix digest
        BECAUSE THE PREFIX DIGEST IS WHAT IT WAS SQUEEZED FROM.  It is oracle
        OUTPUT, not absorbed material.  The gate alpha is its only inhabitant
        below, and everything written in terms of the gate alpha -- the tau
        table `g` above all -- is therefore a function of a CHALLENGE.

`SoundnessAssembly.outerBadEvent` (SoundnessAssembly.lean 610-620) is the adopted
assembly's bad event.  Its tau argument is

    ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates
      (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
      (TranscriptProvenance.gateAlphaElement thash c p) s0.tables

and its alpha argument `coeffsOf` is pinned by the residue field
`SoundnessAssembly.AssemblyResidue.slotCoefficients` (SoundnessAssembly.lean
448-453) to

    AlphaZeroCheck.slotCoefficients (Integrated.gateConfig c) gates
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))

So, argument by argument:

* `Integrated.gateConfig c` and `gates` -- CATEGORY (a), DEPLOYMENT DATA, up to
  the config digest.  `gates = gdec c.gatesEncoding` (residue field
  `gatesDecode`), and `ExplicitEngine.accepted_configuration_is_the_deployed_one`
  pins `core c` to `core c₀` up to a `khash` collision.  `gatesEncoding` is a
  `core` field, so the gate list really is deployment data on that route.
* `E.publicInputsHash p.publicInputs` -- CATEGORY (b), STATEMENT DATA.
  `p.publicInputs` is absorbed RAW at prefix frame 3 (CommitmentOrder.lean 69),
  so it is fixed before every challenge.
* `TranscriptProvenance.gateAlphaElement thash c p` -- CATEGORY (e), AND THIS IS
  THE CORRECTION.  IT IS A CHALLENGE COORDINATE, NOT PREFIX DATA.  It is the
  block-0 coordinate `JointChallengeSpace.Draw.gateAlpha`, squeezed from the
  twenty-two-frame prefix digest at counter `9+3·degreeBits`
  (CommitmentOrder.lean 329-334); the adopted
  `JointChallengeSpace.DrawEncodesRun.alphaDrawn` is the seam field that says the
  run's gate alpha IS the reduction of that drawn coordinate.  Section 1 proves
  only that it FACTORS THROUGH the prefix digest -- read the name
  `gate_alpha_is_prefix_data` in that narrow sense, "determined by the prefix
  digest", never "absorbed in the prefix".  Its counter is strictly below every
  gate tau counter `12+3·degreeBits+3i`
  (`CommitmentOrder.gate_alpha_precedes_every_gate_tau_coordinate`,
  CommitmentOrder.lean 463-464), and section 2's
  `gate_alpha_counter_is_outside_every_gate_tau_triple` upgrades that ordering to
  the disjointness of digest triples the diagonal argument would need.
* `s0.tables` -- THE RESIDUE, categories (c)/(d).  In `AssemblyResidue` `s0` is a
  free parameter; in
  `ExtractorConstruction.extractedState` (ExtractorConstruction.lean 225-238) it
  is `extract roots opening`, the R1b extractor applied to the three commitment
  roots AND the round-one opening.

## The finding

The roots ARE prefix data: `CommitmentOrder.three_roots_inside_the_prefix`
(CommitmentOrder.lean 273-281) puts them at frames 13, 15 and 19 of 22.  THE
ROUND-ONE OPENING IS NOT.  `Verifier.statement` (Verifier.lean 294-295) drops
`whirTranscript`, `whirHints`, `used`, `logRounds` and `gateRounds`, so the
twenty-two frames are literally constant in the two byte fields the WHIR tail is
parsed from (`prefix_ignores_the_whir_tail`); and the WHIR context the tail runs
in is built from `Verifier.derivedIndices` (Verifier.lean 249-254), which
`InstalledIndexSampler` squeezes at chain stage `ReducedIndexLanes.indexStage d =
22 + 5d + 8`, far AFTER the gate squeeze at `ReducedFullTransport.deriveStage =
22`.  So the extractor reads material absorbed after every challenge whose bad
set it indexes.  Section 4 makes that constructive:
`extracted_state_moves_with_the_opening` exhibits an `extract` and two openings
over the SAME roots whose extracted gate prover states differ.

THIS IS NOT A CLAIM THAT THE DEPLOYED SYSTEM IS BROKEN.  It is a claim about
where the assumption sits: "fixed data" is a FACT for the configuration
(category (a)) and the statement (category (b)); it is NOT the right description
of the gate alpha, which is category (e) -- a challenge, merely one determined by
the prefix digest; and it is an ASSUMPTION for the columns (section 6 writes that
assumption down as `CommittedTablesJoin` and proves it is exactly what removes
the opening dependence).

## What the category (e) correction costs the ROM line

Because the assembly's tau table is
`ZeroCheckSemantics.gateValue … (gateAlphaElement thash c p) …`, and the gate
alpha is a squeezed coordinate, `g` IS A FUNCTION OF A CHALLENGE.  Hence:

* every ROM tau event stated at a FIXED `g` -- `ReducedFullTransport.gateTauBadEvent
  … g` with `g` a free parameter, and the `ReducedIndexLanes`,
  `ReducedEngineIndex`, `RawIndexLanes` and `RawBlockLanes` headlines that
  inherit it -- is the CONSTANT-ALPHA SLICE of the engine's own tau event, not
  that event itself;
* THE ENGINE'S OWN TAU EVENT, whose target `g` moves with the alpha triple the
  same oracle table answers at `ReducedFullTransport.alphaBase d`, IS BOUNDED
  NOWHERE IN THE ADOPTED TREE.  It is true in principle: the alpha counter lies
  outside every tau triple (section 2's
  `gate_alpha_counter_is_outside_every_gate_tau_triple`), so the adopted
  `OuterLaneTransport.stage_triple_target_mass_le` in its diagonal form -- `targ`
  may depend on the table provided it is unmoved by the three tested cells --
  would carry it at the same `tauTerm`.  THAT ARGUMENT IS NOT PERFORMED HERE.
  The adopted `EngineTauDiagonal` is what addresses it.
* `ReducedEngineIndex` bounds the engine's own INDEX event together with
  `ReducedFullTransport`'s FIXED-DATA tau and alpha events; it does not bound the
  engine's own tau event.  The `RawIndexLanes` headline docstring "THE FULL
  ADAPTIVE BOUND ON THE ENGINE'S OWN EVENTS" is overstated for the same reason:
  the engine's own event it covers is the INDEX event.

The alpha side is untouched by all this: `coeffsOf` is pinned to
`AlphaZeroCheck.slotCoefficients`, which takes NO challenge argument at all, so
on that lane the fixed-data reading is correct and no diagonal is needed.

## What is proved

1. Sections 1-2: the prefix is constant in the WHIR tail and in the used claims;
   the gate alpha factors through the prefix digest (but is squeezed from it, not
   absorbed into it); the assembly's tau table is a function of the
   configuration, the statement, the tables and THAT ONE CHALLENGE COORDINATE
   (`assembly_tau_table_factors_through_the_prefix_alpha`,
   `outer_bad_event_tau_table_factors_through_the_prefix_alpha`); and the alpha
   counter is disjoint from every tau triple
   (`gate_alpha_counter_is_outside_every_gate_tau_triple`).
2. Section 3: the alpha coefficients mention NO challenge at all, and are
   determined by the tables (`coefficients_are_determined_by_the_tables`,
   `alpha_bad_event_determined_by_the_tables`), with a concrete instance at which
   the pinning hypothesis is known satisfiable (`survey_coefficients_exist`).
3. Section 4: the adopted extractor reads exactly two of the five cells, and its
   output genuinely moves with the round-one opening.
4. Section 5: the absorption-stage inventory, in the adopted stage numbering.
5. Section 6: `CommittedTablesJoin`, its satisfiability at a concrete (degenerate)
   instance, and the two consequences that make it the right residue.

## What is NOT proved

* Nothing here discharges R1b, `CommitmentOrder.CommittedTables`, or any part of
  `AssemblyResidue`.  `CommittedTablesJoin` is a HYPOTHESIS everywhere it appears,
  and its exhibited witness uses a CONSTANT extractor: it shows the predicate is
  not self-contradictory, NOT that the deployed extractor satisfies it.
* THE ENGINE'S OWN TAU EVENT -- the diagonal over the alpha triple described
  above -- IS NOT BOUNDED HERE.  Section 2 supplies only the counter-disjointness
  fact that such an argument would start from; the sibling candidate
  the adopted `EngineTauDiagonal` is where the argument itself is carried out.
* No probability, no uniformity, no Fiat--Shamir soundness, no hash assumption.
  Half (B) of `CommitmentOrder`'s header is untouched.
* No acceptance is exhibited; `Integrated.verify` is never invoked below.
* The mass constants of the ROM modules are not the system's soundness error;
  the deployed design point is around a hundred bits.

## Adopted material used

`Audit.Wire3.CommitmentOrder` (`gateChallengeFrames`, `prefixDigest`,
`gate_alpha_from_prefix`, `three_roots_inside_the_prefix`, `CommittedTables`),
`Audit.Wire3.TranscriptProvenance` (`gateAlphaElement`, `gateTauColumn`),
`Audit.Wire3.ZeroCheckSemantics` (`gateValue`), `Audit.Wire3.AlphaZeroCheck`
(`slotCoefficients`, `rowWires`, `rowConstants`, `configured_slot_coefficients`),
`Audit.Wire3.ChallengeUnionBound` (`alphaUnionBadSet`, `mem_alphaUnionBadSet`,
`alphaFamily_apply`), `Audit.Wire3.JointChallengeSpace` (`alphaBadEvent`),
`Audit.Wire3.SoundnessAssembly` (`outerBadEvent`, `logLane`, `gateLane`),
`Audit.Wire3.ExtractorConstruction` (`extractedState`, `extractedColumns`,
`fitColumn`), `Audit.Wire3.GateDenseRound` (`exampleConfig`, `exampleGates`,
`example_configuration`), `Audit.Wire3.ReducedFullTransport` (`deriveStage`,
`alphaBase`, `tauBase`), `Audit.Wire3.OuterLaneTransport` (`tripleCounters`),
`Audit.Wire3.ReducedIndexLanes` (`indexStage`).  Nothing above is restated or
re-proved.
-/

namespace Audit.Wire3.CommitmentOrderSurvey

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. What the twenty-two-frame prefix is, and is not, a function of -/

/-- (1) **THE PREFIX IS CONSTANT IN THE WHIR TAIL.** `Verifier.statement` keeps
only the circuit digest, the public inputs and the three roots, so the twenty-two
frames `CommitmentOrder.gateChallengeFrames` absorbs do not mention the two byte
fields the WHIR session -- and with it the round-one opening the R1b extractor
reads -- is parsed from. -/
theorem prefix_ignores_the_whir_tail (c : Verifier.Config) (p : Verifier.Proof)
    (wt wh : Verifier.Bytes) :
    CommitmentOrder.gateChallengeFrames c
        (Verifier.statement { p with whirTranscript := wt, whirHints := wh })
      = CommitmentOrder.gateChallengeFrames c (Verifier.statement p) := rfl

/-- (1) **THE PREFIX IS CONSTANT IN THE USED CLAIMS AND THE ROUND MESSAGES.**
Those are absorbed later -- the round messages at the coupled-round stages, the
used claims in the eight frames `InstalledIndexSampler` absorbs before the index
squeeze -- and none of them is a prefix frame. -/
theorem prefix_ignores_the_used_claims_and_the_round_messages (c : Verifier.Config)
    (p : Verifier.Proof) (u : Verifier.UsedClaims) (lr gr : List (List Verifier.Ext3)) :
    CommitmentOrder.gateChallengeFrames c
        (Verifier.statement { p with used := u, logRounds := lr, gateRounds := gr })
      = CommitmentOrder.gateChallengeFrames c (Verifier.statement p) := rfl

/-- (1) Hence both gate challenges are blind to the WHIR tail. -/
theorem gate_challenges_ignore_the_whir_tail (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (wt wh : Verifier.Bytes) :
    TranscriptProvenance.gateAlphaElement thash c
        { p with whirTranscript := wt, whirHints := wh }
      = TranscriptProvenance.gateAlphaElement thash c p ∧
    TranscriptProvenance.gateTauColumn thash c
        { p with whirTranscript := wt, whirHints := wh }
      = TranscriptProvenance.gateTauColumn thash c p :=
  ⟨rfl, rfl⟩

/-- The gate alpha as a function of the prefix digest and the configured width
alone -- the adopted `CommitmentOrder.gateChallengesAt` first component, lifted
into `Element` the way `TranscriptProvenance.gateAlphaElement` does.  This is a
SQUEEZE OUTPUT at counter `9+3·degreeBits`: it is the adopted
`JointChallengeSpace.sourceCounter c.degreeBits JointChallengeSpace.Draw.gateAlpha`,
i.e. the block-0 coordinate of the joint challenge space.  Category (e). -/
def prefixAlpha (thash : Transcript.Hash) (c : Verifier.Config)
    (s : Verifier.Statement) : Element :=
  OuterRound.lift (OuterInitial.ext3At thash (CommitmentOrder.prefixDigest thash c s)
    (9 + 3 * c.degreeBits))

/-- (1) **THE GATE ALPHA FACTORS THROUGH THE PREFIX DIGEST, AS A FACT.**  Routed
through the adopted `CommitmentOrder.gate_alpha_from_prefix`; nothing is assumed.

READ THE NAME NARROWLY.  "Prefix data" here means "a function of the prefix
digest", and NOT "material the prefix absorbed".  The prefix does not absorb this
value, it SQUEEZES it: the right-hand side is the block-0 challenge coordinate
`JointChallengeSpace.Draw.gateAlpha` at the prefix digest's counter
`9+3·degreeBits`, and the adopted `JointChallengeSpace.DrawEncodesRun.alphaDrawn`
identifies the run's gate alpha with the reduction of exactly that coordinate.
Category (e) of the header.  So anything downstream that is written in terms of
this value -- section 2's tau table above all -- is a function of a CHALLENGE. -/
theorem gate_alpha_is_prefix_data (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) :
    TranscriptProvenance.gateAlphaElement thash c p
      = prefixAlpha thash c (Verifier.statement p) :=
  congrArg OuterRound.lift
    (CommitmentOrder.gate_alpha_from_prefix thash c (Verifier.statement p))

/-- (1) Equal prefix digests therefore give equal gate alphas. -/
theorem equal_prefix_digests_give_equal_gate_alpha (thash : Transcript.Hash)
    (c : Verifier.Config) (p q : Verifier.Proof)
    (h : CommitmentOrder.prefixDigest thash c (Verifier.statement p)
      = CommitmentOrder.prefixDigest thash c (Verifier.statement q)) :
    TranscriptProvenance.gateAlphaElement thash c p
      = TranscriptProvenance.gateAlphaElement thash c q := by
  rw [gate_alpha_is_prefix_data, gate_alpha_is_prefix_data, prefixAlpha, prefixAlpha, h]

/-! ## 2. The tau table `g` -/

/-- **THE TAU TABLE, WRITTEN AS A FUNCTION OF THE TABLES AND THE ONE SQUEEZED
COORDINATE IT READS.**  The alpha argument is `prefixAlpha` rather than a free
parameter -- but `prefixAlpha` is itself a CHALLENGE, the block-0 coordinate at
counter `9+3·degreeBits`.  Writing it this way pins WHICH challenge the table
reads and shows no other one enters; it does not make the table fixed data. -/
def prefixTauTable (thash : Transcript.Hash) (c : Verifier.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (s : Verifier.Statement) (t : GateSuffixPolynomial.Tables) : Nat → Element :=
  ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates publicHash
    (prefixAlpha thash c s) t

/-- (2) **`tau_alpha_tables_are_prefix_data`, TAU HALF -- WITH THE CORRECTED
CLASSIFICATION.**  The `g` the adopted assembly's bad event is indexed by IS
`prefixTauTable`: a function of the gate configuration, the decoded gate list,
the public-input hash of the absorbed public inputs, the PREFIX DIGEST, and the
tables.  The prefix digest enters ONLY through the squeeze at counter
`9+3·degreeBits`, so what this theorem establishes is a FACTORISATION, not a
fixed-data verdict: `g` is a function of the tables AND of one challenge
coordinate, the block-0 `JointChallengeSpace.Draw.gateAlpha`.  What is genuinely
excluded is everything else -- no other challenge appears, and the gate tau
column does not appear at all.

CONSEQUENCE FOR THE ROM LINE.  Every adopted ROM tau event stated at a fixed `g`
(`ReducedFullTransport.gateTauBadEvent … g` with `g` free, and the
`ReducedIndexLanes` / `ReducedEngineIndex` / `RawIndexLanes` / `RawBlockLanes`
headlines inheriting it) is the CONSTANT-ALPHA SLICE of the engine's own tau
event.  The engine's own event -- target moving with the alpha triple at
`ReducedFullTransport.alphaBase d` -- is bounded nowhere in the adopted tree; see
the header, and `gate_alpha_counter_is_outside_every_gate_tau_triple` below for
the one ingredient this module does supply. -/
theorem assembly_tau_table_factors_through_the_prefix_alpha
    (thash : Transcript.Hash) (E : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) :
    ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash c p) s0.tables
      = prefixTauTable thash c gates
          (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
          (Verifier.statement p) s0.tables := by
  unfold prefixTauTable
  rw [gate_alpha_is_prefix_data]

/-- (2) The same, inside the adopted `SoundnessAssembly.outerBadEvent`: the
event's third argument is the prefix-alpha table, verbatim.  Same classification
caveat as the previous theorem -- this REWRITES `g`, it does not make `g` fixed
data. -/
theorem outer_bad_event_tau_table_factors_through_the_prefix_alpha (thash : Transcript.Hash)
    (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    SoundnessAssembly.outerBadEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf
      = OuterSequentialConditioning.adaptiveJointBadEvent c.degreeBits
          (SoundnessAssembly.logLane E c p logTruths t pr)
          (SoundnessAssembly.gateLane thash E c p gates s0 gateTruths)
          (prefixTauTable thash c gates
            (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
            (Verifier.statement p) s0.tables)
          (2 ^ c.degreeBits) coeffsOf := by
  unfold SoundnessAssembly.outerBadEvent
  rw [assembly_tau_table_factors_through_the_prefix_alpha]

/-- (2) **THE GATE ALPHA COUNTER LIES OUTSIDE EVERY GATE TAU TRIPLE.**  The
adopted `CommitmentOrder.gate_alpha_precedes_every_gate_tau_coordinate` records
the ordering of the counters -- alpha at `9+3d`, every tau coordinate at
`12+3d+3i`.  This is the form the diagonal argument would consume: the adopted
`ReducedFullTransport.alphaBase d` is not one of the three counters the adopted
`ReducedFullTransport.tauBase d i` triple occupies, so a tau target that MOVES
with the alpha cell is still unmoved by the three cells the tau lane tests.

WHY IT MATTERS.  The previous theorem shows the assembly's `g` is a function of
the alpha cell, so the engine's own tau event is a ONE-COORDINATE DIAGONAL over
that cell, and the adopted `OuterLaneTransport.stage_triple_target_mass_le` --
whose `targ` may depend on the table provided it is unmoved by the tested cells
-- is exactly the lemma shaped to carry it, at the same `tauTerm`.  THIS MODULE
DOES NOT PERFORM THAT ARGUMENT and proves nothing about the engine's own tau
event; the adopted `EngineTauDiagonal` is where it is carried out. -/
theorem gate_alpha_counter_is_outside_every_gate_tau_triple (d i : Nat) :
    ReducedFullTransport.alphaBase d
      ∉ OuterLaneTransport.tripleCounters (ReducedFullTransport.tauBase d i) := by
  simp only [ReducedFullTransport.alphaBase, ReducedFullTransport.tauBase,
    OuterLaneTransport.tripleCounters, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- (2) The eq column is not an input of the tau table: the adopted
`ZeroCheckSemantics.gateValue` reads only the wire and constant columns. -/
theorem prefix_tau_table_ignores_the_eq_column (thash : Transcript.Hash)
    (c : Verifier.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (s : Verifier.Statement) (t : GateSuffixPolynomial.Tables) (col : List Element) :
    prefixTauTable thash c gates publicHash s { t with eq := col }
      = prefixTauTable thash c gates publicHash s t := rfl

/-- (2) **THE TAU-SIDE CONGRUENCE LEMMA.**  The table argument enters only
through the wire and constant columns -- i.e. through exactly the two committed
groups the preprocessed and witness roots name. -/
theorem prefix_tau_table_depends_only_on_wires_and_constants (thash : Transcript.Hash)
    (c : Verifier.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (s : Verifier.Statement) (t u : GateSuffixPolynomial.Tables)
    (hw : t.wires = u.wires) (hc : t.constants = u.constants) :
    prefixTauTable thash c gates publicHash s t = prefixTauTable thash c gates publicHash s u := by
  funext index
  unfold prefixTauTable ZeroCheckSemantics.gateValue
  rw [hw, hc]

/-- (2) Hence the adopted `JointChallengeSpace.tauBadEvent` is a function of the
wire and constant columns. -/
theorem tau_bad_event_of_wires_and_constants (thash : Transcript.Hash) (c : Verifier.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base) (s : Verifier.Statement)
    (d : Nat) (t u : GateSuffixPolynomial.Tables)
    (hw : t.wires = u.wires) (hc : t.constants = u.constants) :
    JointChallengeSpace.tauBadEvent d (prefixTauTable thash c gates publicHash s t)
      = JointChallengeSpace.tauBadEvent d (prefixTauTable thash c gates publicHash s u) := by
  rw [prefix_tau_table_depends_only_on_wires_and_constants thash c gates publicHash s t u hw hc]

/-- (2) **THE ROOT-LEVEL STATEMENT.**  Under the adopted, still open
`CommitmentOrder.CommittedTables` join, two prover states committed by the same
statement give the same tau bad event.  The roots are absorbed at prefix frames
13 and 15; the join from root to table is NOT discharged here and is not
discharged anywhere in the adopted tree. -/
theorem tau_bad_event_determined_by_the_roots (thash : Transcript.Hash) (c : Verifier.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base) (d : Nat)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (s : Verifier.Statement) (t u : GateSuffixPolynomial.Tables)
    (ht : CommitmentOrder.CommittedTables tablesOf s t)
    (hu : CommitmentOrder.CommittedTables tablesOf s u) :
    JointChallengeSpace.tauBadEvent d (prefixTauTable thash c gates publicHash s t)
      = JointChallengeSpace.tauBadEvent d (prefixTauTable thash c gates publicHash s u) :=
  tau_bad_event_of_wires_and_constants thash c gates publicHash s d t u
    (ht.wires.trans hu.wires.symm) (ht.constants.trans hu.constants.symm)

/-! ## 3. The alpha coefficients `coeffsOf` -/

/-- **THE COEFFICIENT TABLE.**  The adopted `AssemblyResidue.slotCoefficients`
pins `coeffsOf i` to this value.  IT MENTIONS NO CHALLENGE AT ALL -- it takes
neither a `Transcript.Hash` nor a `Verifier.Proof`, so neither the gate alpha nor
the gate tau column can be an argument -- so on the alpha side "fixed data"
reduces entirely to the provenance of the tables.  CONTRAST `prefixTauTable`,
which does read the gate alpha: the category (e) correction bites on the tau lane
and not on this one. -/
def prefixCoeffTable (c : Verifier.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (t : GateSuffixPolynomial.Tables) :
    Nat → Option (List Element) :=
  fun i => AlphaZeroCheck.slotCoefficients (Integrated.gateConfig c) gates
    (AlphaZeroCheck.rowWires t i) (AlphaZeroCheck.rowConstants t i) publicHash

/-- (3) The eq column is not an input of the coefficient table either. -/
theorem prefix_coefficients_ignore_the_eq_column (c : Verifier.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (t : GateSuffixPolynomial.Tables) (col : List Element) :
    prefixCoeffTable c gates publicHash { t with eq := col }
      = prefixCoeffTable c gates publicHash t := rfl

/-- (3) **THE ALPHA-SIDE CONGRUENCE LEMMA.** -/
theorem prefix_coefficients_depend_only_on_wires_and_constants (c : Verifier.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (t u : GateSuffixPolynomial.Tables) (hw : t.wires = u.wires) (hc : t.constants = u.constants) :
    prefixCoeffTable c gates publicHash t = prefixCoeffTable c gates publicHash u := by
  funext i
  unfold prefixCoeffTable AlphaZeroCheck.rowWires AlphaZeroCheck.rowConstants
  rw [hw, hc]

/-- (3) **`tau_alpha_tables_are_prefix_data`, ALPHA HALF.**  Two coefficient
families pinned by the SAME tables at the same configuration, gate list and
public-input hash give literally the same adopted
`ChallengeUnionBound.alphaUnionBadSet`.  The two hypotheses are known satisfiable:
`survey_coefficients_exist` exhibits a configuration, gate list and table pair at
which `prefixCoeffTable` really does return `some`. -/
theorem coefficients_are_determined_by_the_tables (c : Verifier.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (t : GateSuffixPolynomial.Tables) (rows : Nat) (coeffsOf coeffsTwo : Nat → List Element)
    (h1 : ∀ i, i < rows → prefixCoeffTable c gates publicHash t i = some (coeffsOf i))
    (h2 : ∀ i, i < rows → prefixCoeffTable c gates publicHash t i = some (coeffsTwo i)) :
    ChallengeUnionBound.alphaUnionBadSet rows coeffsOf
      = ChallengeUnionBound.alphaUnionBadSet rows coeffsTwo := by
  have hEq : ∀ i, i < rows → coeffsOf i = coeffsTwo i := by
    intro i hi
    exact Option.some.inj ((h1 i hi).symm.trans (h2 i hi))
  have hfam : ∀ i ∈ Finset.range rows,
      ChallengeUnionBound.alphaFamily coeffsOf i = ChallengeUnionBound.alphaFamily coeffsTwo i := by
    intro i hi
    rw [ChallengeUnionBound.alphaFamily_apply, ChallengeUnionBound.alphaFamily_apply,
      hEq i (Finset.mem_range.mp hi)]
  unfold ChallengeUnionBound.alphaUnionBadSet ChallengeUnionBound.rowUnion
  exact Finset.biUnion_congr rfl hfam

/-- (3) The same at the adopted `JointChallengeSpace.alphaBadEvent`. -/
theorem alpha_bad_event_determined_by_the_tables (d : Nat) (c : Verifier.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (t : GateSuffixPolynomial.Tables) (rows : Nat) (coeffsOf coeffsTwo : Nat → List Element)
    (h1 : ∀ i, i < rows → prefixCoeffTable c gates publicHash t i = some (coeffsOf i))
    (h2 : ∀ i, i < rows → prefixCoeffTable c gates publicHash t i = some (coeffsTwo i)) :
    JointChallengeSpace.alphaBadEvent d rows coeffsOf
      = JointChallengeSpace.alphaBadEvent d rows coeffsTwo := by
  unfold JointChallengeSpace.alphaBadEvent
  rw [coefficients_are_determined_by_the_tables c gates publicHash t rows coeffsOf coeffsTwo h1 h2]

/-- A configuration whose gate configuration is the adopted
`GateDenseRound.exampleConfig`, so that the adopted
`GateDenseRound.example_configuration` applies to it. -/
def surveyConfig : Verifier.Config :=
  { Verifier.testConfig with
      numConstants := 3, numWires := 4, numSelectors := 1, numGateConstraints := 1,
      quotientDegree := 2 }

/-- Tables of the widths that configuration demands: four wire columns, three
constant columns.  The columns themselves are empty, so every row value is the
adopted zero -- this is a SATISFIABILITY witness, not a deployment. -/
def surveyTables : GateSuffixPolynomial.Tables :=
  ⟨List.replicate 4 [], List.replicate 3 [], []⟩

theorem survey_gate_config :
    Integrated.gateConfig surveyConfig = GateDenseRound.exampleConfig := rfl

/-- (3) **THE PINNING HYPOTHESIS IS SATISFIABLE.**  At `surveyConfig`, the adopted
`GateDenseRound.exampleGates` and `surveyTables`, `prefixCoeffTable` returns
`some` at EVERY row, so the two hypotheses of
`coefficients_are_determined_by_the_tables` hold for the family this produces.
Routed through the adopted `AlphaZeroCheck.configured_slot_coefficients`. -/
theorem survey_coefficients_exist (publicHash : Nat → Verifier.Base) (i : Nat) :
    ∃ coeffs, prefixCoeffTable surveyConfig GateDenseRound.exampleGates publicHash surveyTables i
      = some coeffs := by
  have hw : (AlphaZeroCheck.rowWires surveyTables i).length
      = (Integrated.gateConfig surveyConfig).numWires := by
    rw [AlphaZeroCheck.rowWires_length]
    rfl
  have hc : (AlphaZeroCheck.rowConstants surveyTables i).length
      = (Integrated.gateConfig surveyConfig).numConstants := by
    rw [AlphaZeroCheck.rowConstants_length]
    rfl
  obtain ⟨coeffs, hco, -⟩ := AlphaZeroCheck.configured_slot_coefficients
    (Integrated.gateConfig surveyConfig) GateDenseRound.exampleGates
    (AlphaZeroCheck.rowWires surveyTables i) (AlphaZeroCheck.rowConstants surveyTables i)
    publicHash GateDenseRound.example_configuration hw hc
  exact ⟨coeffs, hco⟩

/-! ## 4. The committed columns: what the adopted extractor actually reads -/

/-- (4) **THE ADOPTED EXTRACTOR READS EXACTLY TWO OF THE FIVE CELLS.**  The
extracted gate prover state's wire columns are cell 4 and its constant columns
cell 3; its eq column is the adopted eq table at the derived gate tau, which is
prefix data by section 1.  So the WHOLE table-provenance question is the
provenance of `extract roots opening 4` and `extract roots opening 3`. -/
theorem extracted_state_depends_only_on_two_cells (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (exOne exTwo : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (rootsOne rootsTwo : List Spongefish.Digest)
    (openingOne openingTwo : WhirIntermediate.Opening)
    (h4 : exOne rootsOne openingOne 4 = exTwo rootsTwo openingTwo 4)
    (h3 : exOne rootsOne openingOne 3 = exTwo rootsTwo openingTwo 3) :
    ExtractorConstruction.extractedState thash c p exOne rootsOne openingOne
      = ExtractorConstruction.extractedState thash c p exTwo rootsTwo openingTwo := by
  unfold ExtractorConstruction.extractedState
  rw [h4, h3]

/-- A deterministic extractor that reads the round-one opening.  It is as
admissible as any other function of the two arguments
`InstalledWhirTail.TailExtractsCommittedTables` hands `extract`. -/
def demoExtract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
    List (List Element) :=
  fun _ o _ =>
    match o.indices with
    | [] => [[(0 : Element)]]
    | _ :: _ => [[(1 : Element)]]

def demoOpeningA : WhirIntermediate.Opening := ⟨[], []⟩

def demoOpeningB : WhirIntermediate.Opening := ⟨[0], []⟩

theorem demo_openings_differ : demoOpeningA ≠ demoOpeningB := by
  intro h
  have h2 : ([] : List Nat) = [0] := congrArg WhirIntermediate.Opening.indices h
  exact List.noConfusion h2

/-- (4) The demo extractor's output really moves with the opening, at the SAME
commitment roots. -/
theorem demo_extract_moves_with_the_opening (roots : List Spongefish.Digest) (i : Fin 5) :
    demoExtract roots demoOpeningA i ≠ demoExtract roots demoOpeningB i := by
  intro h
  have h2 : ([[(0 : Element)]] : List (List Element)) = [[(1 : Element)]] := h
  have h3 : (0 : Element) = 1 :=
    congrArg (fun l => (l.getD 0 []).getD 0 (0 : Element)) h2
  exact zero_ne_one h3

theorem fit_column_head (n : Nat) (x : Element) :
    (ExtractorConstruction.fitColumn n [x]).getD 0 0 = x := by
  have hlen : 0 < ((List.range (2 ^ n)).map
      (fun i => ([x] : List Element).getD i 0)).length := by
    rw [List.length_map, List.length_range]
    exact Nat.two_pow_pos n
  rw [ExtractorConstruction.fitColumn, List.getD_eq_get _ _ hlen, List.get_eq_getElem,
    List.getElem_map, List.getElem_range]
  rfl

theorem extracted_columns_head (n w : Nat) (cols : List (List Element)) (hw : 0 < w) :
    ((ExtractorConstruction.extractedColumns n w cols).getD 0 ⟨0, []⟩).evaluations
      = ExtractorConstruction.fitColumn n (cols.getD 0 []) := by
  have hlen : 0 < ((List.range w).map
      (fun i => (⟨n, ExtractorConstruction.fitColumn n (cols.getD i [])⟩ :
        DenseMleIndexed.State))).length := by
    rw [List.length_map, List.length_range]
    exact hw
  rw [ExtractorConstruction.extractedColumns, List.getD_eq_get _ _ hlen, List.get_eq_getElem,
    List.getElem_map, List.getElem_range]

/-- (4) **THE COMMITTED COLUMNS ARE NOT PREFIX DATA FOR THE ADOPTED EXTRACTOR.**
Two runs with the SAME commitment roots -- hence the same twenty-two absorbed
frames, the same prefix digest and the same gate challenges -- but different
round-one openings get DIFFERENT extracted gate prover states, for a
deterministic `extract` that this model allows.  The opening is parsed from
`p.whirTranscript` / `p.whirHints`, which `prefix_ignores_the_whir_tail` shows
the prefix never absorbs, and the WHIR session it belongs to is entered only
after the index squeeze (section 5).

So the sentence "the extracted columns are fixed data, absorbed in the
twenty-two-frame prefix" is NOT available as a fact: the ROOTS are absorbed
there, the COLUMNS are not, and the step between them is the open join of
section 6.

SIDE CONDITION.  `0 < c.numWires` is required and is a hypothesis: the
separation is read off wire column 0, and at `c.numWires = 0` the adopted
`ExtractorConstruction.extractedColumns` returns the empty list on both sides and
the two extracted states coincide.  Every deployed configuration has positive
wire width, so this excludes nothing real; it is stated rather than assumed. -/
theorem extracted_state_moves_with_the_opening (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) (roots : List Spongefish.Digest)
    (hw : 0 < c.numWires) :
    ExtractorConstruction.extractedState thash c p demoExtract roots demoOpeningA
      ≠ ExtractorConstruction.extractedState thash c p demoExtract roots demoOpeningB := by
  intro h
  have hwires := congrArg GateTerminalBinding.ProverState.wires h
  have hhead := congrArg
    (fun l => ((l.getD 0 ⟨0, []⟩ : DenseMleIndexed.State).evaluations).getD 0 (0 : Element)) hwires
  rw [show ((fun (l : List DenseMleIndexed.State) =>
      ((l.getD 0 ⟨0, []⟩ : DenseMleIndexed.State).evaluations).getD 0 (0 : Element))
      (ExtractorConstruction.extractedState thash c p demoExtract roots demoOpeningA).wires)
      = (0 : Element) from by
        show (((ExtractorConstruction.extractedColumns
          (TranscriptProvenance.gateTauColumn thash c p).length c.numWires
          [[(0 : Element)]]).getD 0 ⟨0, []⟩).evaluations).getD 0 (0 : Element) = 0
        rw [extracted_columns_head _ _ _ hw]
        exact fit_column_head _ _,
    show ((fun (l : List DenseMleIndexed.State) =>
      ((l.getD 0 ⟨0, []⟩ : DenseMleIndexed.State).evaluations).getD 0 (0 : Element))
      (ExtractorConstruction.extractedState thash c p demoExtract roots demoOpeningB).wires)
      = (1 : Element) from by
        show (((ExtractorConstruction.extractedColumns
          (TranscriptProvenance.gateTauColumn thash c p).length c.numWires
          [[(1 : Element)]]).getD 0 ⟨0, []⟩).evaluations).getD 0 (0 : Element) = 1
        rw [extracted_columns_head _ _ _ hw]
        exact fit_column_head _ _] at hhead
  exact zero_ne_one hhead

/-! ## 5. The absorption order, in the adopted stage numbering -/

/-- (5) **THE ABSORPTION-STAGE INVENTORY.**  The three commitment roots sit at
frames 13, 15 and 19 of the twenty-two-frame prefix; the prefix ends at the
adopted `ReducedFullTransport.deriveStage = 22`, which is where the gate alpha
and the gate tau block are squeezed; and the index lanes are squeezed at the
adopted `ReducedIndexLanes.indexStage d = 22 + 5d + 8`, strictly later.  The WHIR
session -- and with it the round-one opening the R1b extractor reads -- is
entered only after that, because `Verifier.whirContext` takes
`Verifier.derivedIndices` as an argument. -/
theorem absorption_order_of_the_extractor_inputs (c : Verifier.Config)
    (s : Verifier.Statement) (d : Nat) :
    (CommitmentOrder.gateChallengeFrames c s).get? 13 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes s.preprocessedRoot)) ∧
    (CommitmentOrder.gateChallengeFrames c s).get? 15 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes s.witnessRoot)) ∧
    (CommitmentOrder.gateChallengeFrames c s).get? 19 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes s.normInverseRoot)) ∧
    (CommitmentOrder.gateChallengeFrames c s).length = ReducedFullTransport.deriveStage ∧
    ReducedFullTransport.deriveStage < ReducedIndexLanes.indexStage d := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [ReducedFullTransport.deriveStage, ReducedIndexLanes.indexStage]
  omega

/-! ## 6. `CommittedTablesJoin`: the residue, written down -/

/-- **THE REMAINING OPEN JOIN.**

Three clauses, each naming one link that is missing between "the assembly's
tables" and "the deployed circuit's tables".

* `rootDetermined` is the R1b half: the extracted gate columns are the ones the
  statement's preprocessed and witness roots name -- the adopted
  `CommitmentOrder.CommittedTables` -- so the round-one opening DROPS OUT.
  Section 4 shows this is exactly the clause that is missing: without it the
  extracted state moves with the opening.  `Audit.Wire3.OpeningBinding` proves
  BINDING, not EXTRACTION, and `InstalledWhirTail.TailExtractsCommittedTables`
  posits the extractor rather than building it.
* `preprocessedPinned` is the deployment half on the Solidity path: the run's
  preprocessed root is the constructor-pinned one.  `Verifier.shape` forces it on
  an accepted call, which is why it is written as an equation rather than as a
  hypothesis about a hash.
* `configDeployed` is the configuration half: the called configuration's
  `ExplicitEngine.core` IS the deployed one's.  The adopted
  `ExplicitEngine.accepted_configuration_is_the_deployed_one` reaches it only up
  to a `khash` collision and only under the constructor-time hypothesis
  `pin.configDigest = khash (encodeConfig c₀)`, and
  `ExplicitEngine.residue_fields_are_not_encoded` shows six configuration fields
  are outside `core` entirely.  The Rust entry point has a DIFFERENT boundary --
  `RustCallBoundary.rustDeployment` takes no deployed constant at all, and
  `RustCallBoundary.solidity_pins_are_not_implied_by_rust_checks` exhibits
  configurations passing every Rust check that differ in what the Solidity pin
  fixes -- so on that path this clause is a statement about the provenance of the
  `(common_data, vk)` pair, which is outside the model.
  `Audit.Wire3.CanonicalProofCheck` is the adopted per-call proof-shape boundary
  on the same route.

WHAT IS STILL NOT WRITTEN DOWN HERE is the CommonCircuitData mirror itself: that
the gate list `gdec c.gatesEncoding` and the preprocessed columns the root commits
to are the ones the deployed `CommonCircuitData` describes.  No predicate in the
adopted tree connects a `Verifier.Root` to a column list at all
(`OpeningBinding.opening_relation_ignores_the_commitment`), so that mirror cannot
even be stated at this level; `rootDetermined` is the closest the model reaches,
and it stops at "the columns are a function of the roots". -/
structure CommittedTablesJoin
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (thash : Transcript.Hash) (c c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 → List (List Element))
    (p : Verifier.Proof) (roots : List Spongefish.Digest)
    (opening : WhirIntermediate.Opening) : Prop where
  rootDetermined : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
    (ExtractorConstruction.extractedState thash c p extract roots opening).tables
  preprocessedPinned : p.preprocessedRoot = pin.preprocessedRoot
  configDeployed : ExplicitEngine.core c = ExplicitEngine.core c₀

/-- A constant extractor: it reads neither the roots nor the opening.  Used only
to witness that `CommittedTablesJoin` is not self-contradictory. -/
def trivialExtract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
    List (List Element) :=
  fun _ _ _ => []

def trivialTablesOf (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables :=
  fun _ _ => (ExtractorConstruction.extractedState thash c p trivialExtract [] ⟨[], []⟩).tables

/-- (6) **THE JOIN IS SATISFIABLE.**  At the constant extractor, the table map it
induces, the called configuration taken as the deployed one, and a pinned record
carrying the run's own preprocessed root, every clause holds by `rfl`.

THIS WITNESS IS DEGENERATE ON PURPOSE.  It shows the predicate is inhabited, so
that the theorems below have non-vacuous hypotheses.  It says NOTHING about the
deployed extractor, whose `extract` does read the opening
(`InstalledWhirTail.TailExtractsCommittedTables`), and nothing about any accepted
run. -/
theorem committed_tables_join_is_satisfiable (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (pin : Verifier.Pinned) (roots : List Spongefish.Digest)
    (opening : WhirIntermediate.Opening) :
    CommittedTablesJoin (trivialTablesOf thash c p) thash c c
      { pin with preprocessedRoot := p.preprocessedRoot } trivialExtract p roots opening :=
  ⟨⟨rfl, rfl⟩, rfl, rfl⟩

/-- (6) **THE JOIN IS EXACTLY WHAT REMOVES THE OPENING DEPENDENCE.**  Under it,
two runs of the same extractor at the same statement -- whatever their roots
arguments and whatever their round-one openings -- have the same extracted wire
and constant columns.  Contrast `extracted_state_moves_with_the_opening`, which
shows this fails without the join. -/
theorem committed_tables_join_removes_the_opening_dependence
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (thash : Transcript.Hash) (c c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 → List (List Element))
    (p : Verifier.Proof) (rootsOne rootsTwo : List Spongefish.Digest)
    (openingOne openingTwo : WhirIntermediate.Opening)
    (h1 : CommittedTablesJoin tablesOf thash c c₀ pin extract p rootsOne openingOne)
    (h2 : CommittedTablesJoin tablesOf thash c c₀ pin extract p rootsTwo openingTwo) :
    (ExtractorConstruction.extractedState thash c p extract rootsOne openingOne).tables.wires
        = (ExtractorConstruction.extractedState thash c p extract rootsTwo openingTwo).tables.wires ∧
    (ExtractorConstruction.extractedState thash c p extract rootsOne openingOne).tables.constants
        = (ExtractorConstruction.extractedState thash c p extract rootsTwo
            openingTwo).tables.constants :=
  ⟨h1.rootDetermined.wires.trans h2.rootDetermined.wires.symm,
   h1.rootDetermined.constants.trans h2.rootDetermined.constants.symm⟩

/-- (6) **AND HENCE THE TAU TABLE'S TABLE ARGUMENT BECOMES PREFIX DATA.**
Composing the join with the section-2 congruence: under `CommittedTablesJoin` the
adopted assembly's `g` is a function of the configuration, the gate list, the
public-input hash, the prefix digest and the STATEMENT'S ROOTS.

READ THE SCOPE EXACTLY.  What the join removes is the dependence on the ROUND-ONE
OPENING; the roots it leaves behind really are absorbed in the twenty-two frames.
IT DOES NOT MAKE `g` FIXED DATA, and the prefix does not absorb its own squeeze
output: even under `CommittedTablesJoin`, `g` remains a function of the block-0
gate alpha cell, because `prefixTauTable` feeds `prefixAlpha` to
`ZeroCheckSemantics.gateValue`.  So the ROM HONESTY sentence needs TWO things,
not one: this join for the tables, AND the alpha diagonal for the challenge
coordinate -- the latter is not proved anywhere in the adopted tree, nor here
(see `gate_alpha_counter_is_outside_every_gate_tau_triple` and the header). -/
theorem committed_tables_join_fixes_the_tau_table
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (thash : Transcript.Hash) (c c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 → List (List Element))
    (p : Verifier.Proof) (rootsOne rootsTwo : List Spongefish.Digest)
    (openingOne openingTwo : WhirIntermediate.Opening)
    (h1 : CommittedTablesJoin tablesOf thash c c₀ pin extract p rootsOne openingOne)
    (h2 : CommittedTablesJoin tablesOf thash c c₀ pin extract p rootsTwo openingTwo) :
    prefixTauTable thash c gates publicHash (Verifier.statement p)
        (ExtractorConstruction.extractedState thash c p extract rootsOne openingOne).tables
      = prefixTauTable thash c gates publicHash (Verifier.statement p)
        (ExtractorConstruction.extractedState thash c p extract rootsTwo openingTwo).tables := by
  obtain ⟨hw, hc⟩ := committed_tables_join_removes_the_opening_dependence tablesOf thash c c₀ pin
    extract p rootsOne rootsTwo openingOne openingTwo h1 h2
  exact prefix_tau_table_depends_only_on_wires_and_constants thash c gates publicHash
    (Verifier.statement p) _ _ hw hc

/-- (6) The alpha side of the same composition. -/
theorem committed_tables_join_fixes_the_coefficients
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (thash : Transcript.Hash) (c c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 → List (List Element))
    (p : Verifier.Proof) (rootsOne rootsTwo : List Spongefish.Digest)
    (openingOne openingTwo : WhirIntermediate.Opening)
    (h1 : CommittedTablesJoin tablesOf thash c c₀ pin extract p rootsOne openingOne)
    (h2 : CommittedTablesJoin tablesOf thash c c₀ pin extract p rootsTwo openingTwo) :
    prefixCoeffTable c gates publicHash
        (ExtractorConstruction.extractedState thash c p extract rootsOne openingOne).tables
      = prefixCoeffTable c gates publicHash
        (ExtractorConstruction.extractedState thash c p extract rootsTwo openingTwo).tables := by
  obtain ⟨hw, hc⟩ := committed_tables_join_removes_the_opening_dependence tablesOf thash c c₀ pin
    extract p rootsOne rootsTwo openingOne openingTwo h1 h2
  exact prefix_coefficients_depend_only_on_wires_and_constants c gates publicHash _ _ hw hc

end Audit.Wire3.CommitmentOrderSurvey
