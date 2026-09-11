import Audit.Wire3.ExplicitEngine
import Audit.Wire3.IndexPointZeroCheck
import Audit.Wire3.AdaptiveAgreementFamily
import Audit.Wire3.ConstantsProvenance

/-!
# Good-draw assembly: the deterministic and counting results for the explicit engine

**THIS IS THE ASSEMBLY OF THE DETERMINISTIC AND COUNTING RESULTS INTO ONE
STATEMENT; THE NUMBERS ARE MASSES UNDER EXPLICIT IDEAL UNIFORM LAWS AND ARE
*NOT* THE SYSTEM'S SOUNDNESS ERROR; THE WHIR/MERKLE TERM (DOMINANT, AROUND THE
100-BIT DESIGN POINT) IS EXCLUDED; NO "125".**

**THE NAME IS A PIPELINE NAME.** The file, the namespace and the `olean` stay
`SoundnessAssembly` so that the build, the axiom audit and the adoption batch
keep naming one artefact; the heading above is what the module actually
establishes, and `explicit_good_draw_assembly`'s docstring says again that this
is not soundness.

Nothing below is new proof content. Every deterministic implication is an
adopted theorem instantiated at `ExplicitEngine.explicitEngine`, every mass is
an adopted counting bound, and the only work done here is composition,
arithmetic on bounds and bookkeeping. What the module adds is a single place in
which the residue is visible: `AssemblyResidue` is the exact list of things
still assumed for the explicit engine at a fixed accepted call, and
`explicit_good_draw_assembly` is the one statement collecting what a GOOD DRAW
buys, whose hypothesis list is that inventory plus acceptance plus two
non-membership facts about the run's own draws.

## WHAT THE PREVIOUS REVISION GOT WRONG, AND WHAT WAS DONE ABOUT IT

**THE PREVIOUS REVISION'S MAIN THEOREM WAS VACUOUS, AND ITS FRAMING WAS A
FORGERY FRAMING.** Both defects are fixed here and both fixes are visible in the
statements.

1. `indexBadEvent` was the UNGUARDED union of the two adopted pullbacks of
   `IndexPointZeroCheck.cellAgreementSet`. That set is the plain filter
   `extension A r = extension B r`, so at `A = B` it is EVERYTHING
   (`IndexPointZeroCheck.agreement_set_of_equal_cells`). Since the theorem's own
   conclusion proved `A = B` for the very lists `hidx` was stated on, `hidx`
   became `draw ∉ Finset.univ` and the hypotheses were jointly inconsistent: the
   reviewer's probe derived `False` from them. `indexBadEvent` is now GUARDED by
   `IndexPointZeroCheck.CellsDifferOnCube`, exactly as the adopted
   `ZeroCheckSemantics.zeroCheckBadSet` is guarded by `CubeZero`, with the
   agreement case empty (`index_bad_event_of_cube_agreement`). The reviewer's
   refutation no longer typechecks: its first step
   `w ∈ indexBadEvent bits A A` is now refuted by
   `index_bad_event_of_equal_cells_is_empty`.
2. `columnNonDegeneracy` -- a premise that is FALSE for every honest constants
   column (`AdaptiveAgreementFamily.escape_kills_hnondeg` even exhibits genuine
   forgeries for which it fails) -- sat inside the residue inventory, so every
   conclusion of the main theorem was conditioned on the run carrying a forged
   constants column. That field and its five indexing companions are GONE from
   `AssemblyResidue`. The constants attack is now a SEPARATE, EXPLICITLY
   LABELLED conditional corollary,
   `constants_forgery_forces_join_or_opening_off_bad_set`, whose forgery-side
   hypotheses are written out in its own signature.

**JOINT SATISFIABILITY IS STILL NOT EXHIBITED.** Nothing here produces an
accepting proof for the explicit engine, so nothing here shows that acceptance
and `AssemblyResidue` can hold together. `explicit_good_draw_assembly` states a
CONDITIONAL SHAPE only. What the guard fix buys is that the hypotheses are no
longer REFUTABLE by the theorem's own conclusion.

For the joint-space half the evidence is now positive rather than merely
negative: `honest_outer_bad_event_empty` shows that an HONEST extraction -- lane
messages equal to the truths, both compare values zero, a cube-zero gate value
and vanishing slot coefficients -- makes `outerBadEvent` EMPTY, so `hdraw` holds
at every point of the joint space. That upgrades `hdraw` from "not refutable by
our own conclusion" to "satisfied by every honest extraction". It does NOT
upgrade the conjunction: no accepting `p` is exhibited alongside such data.

## What the two mass figures are, and are not

`bad_event_mass_le` bounds the mass of an EXPLICIT finite subset of
`JointChallengeSpace.JointSpace c.degreeBits` under the EXPLICIT counting law
`JointChallengeSpace.jointProbability`. `index_bad_event_mass_le` bounds the mass
of an EXPLICIT finite subset of `InstalledIndexSampler.IndexSpace c.indexBits`
under `IndexPointZeroCheck.indexProbability`. **The two live on different finite
spaces and are NOT merged.** Merging them would require a joint law over the
outer challenge block and the constituent-index block together, and no such law
is formalized anywhere in the adopted tree; the schedules are related only by the
documented-not-derived block labels of `JointChallengeSpace.sourceBlock` and
`InstalledIndexSampler.indexSchedulePosition`. So this module states TWO mass
bounds and never adds them.

**No theorem anywhere says the run's actual draw is distributed by either law.**
That is half (B) of the Fiat--Shamir reading, unformalized here and in every
adopted module; `JointChallengeSpace.DrawEncodesRun` at the actual digests is a
THEOREM (`ComposedEngine.composed_actual_digest_draw_encodes_run`), but it is a
COORDINATE statement, and the corresponding statement for the index lanes
(`InstalledIndexSampler.index_points_are_space_coordinates`) is likewise a
coordinate statement. Consequently `hdraw` and `hidx` below are HYPOTHESES about
one point of an explicit finite space, not probabilistic assumptions that anyone
has discharged.

## What is NOT concluded

* **Circuit truth.** "Every selected gate's constraints vanish at row `i` of the
  EXTRACTED tables" is not "the circuit is satisfied by a real witness". The
  tables `s0` are supplied by the extraction hypotheses, not produced.
* **WHIR/Merkle proximity and sumcheck soundness (R1b).** Assumed, as
  `foldLevelOpening`; `InstalledWhirTail.TailExtractsFoldLevel` is the adopted
  named form and `fold_level_opening_of_tail_extraction` links the two.
* **Extraction (R2/R3).** The gate-side join `CellsMatchClaims`, the truth chain,
  the consistency of the extracted state, the constants-column identification
  (`ConstantsProvenance.SuppliedConstantsAreCommitted`) and the committed width
  are all assumed.
* **Hash security.** `hash`, `thash` and `khash` are arbitrary deterministic
  functions; keccak is not modelled. `PinnedWhirProfile.TableIsCanonical` carries
  the keccak idealisation for the two transcribed profile rows, and nineteen rows
  ship as digests only.
* **Rust / Yul / Solidity refinement.** `Verifier.verify` is a manual
  success-boundary model, `InstalledWhirTail.installedTail` a manual execution
  model of the tail, and `ExplicitEngine.explicitDeployment` models the SOLIDITY
  runtime path only -- the Rust entry point re-validates per call and none of
  that is modelled.
* **The two digest residues.** `ExplicitEngine.encodeConfig` does not encode
  `circuitDigest` or `circuitConfigDigest`
  (`ExplicitEngine.accepted_call_pins_everything_but_the_two_digests`).
* **Deployment semantics.** `deployment` below is a constructor fact about what a
  deployer pinned; nothing in the model establishes it.
-/

namespace Audit.Wire3.SoundnessAssembly

open Audit.Wire3 GoldilocksExt3Field

abbrev Profile := PinnedWhirProfile.Profile
abbrev VkParams := InstalledWhirTail.VkParams

/-! ## 1. The engine, and the two identities every transfer below uses -/

/-- The explicit engine of `ExplicitEngine`, abbreviated. Reducible, so every
adopted theorem instantiated at one of its equal forms applies to it. -/
abbrev engine (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) : Verifier.Engine :=
  ExplicitEngine.explicitEngine gdec hash thash khash P c₀

/-- The base at which `InstalledInitialTranscript`'s theorems are instantiated
for the explicit engine. -/
def initialBase (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    Verifier.Engine :=
  ComposedEngine.initialBase (ExplicitEngine.explicitBase hash khash P c₀) thash P c₀

/-- The base at which `InstalledWhirTail`'s theorems are instantiated for the
explicit engine. -/
def tailBase (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    Verifier.Engine :=
  ComposedEngine.outerInstalled
    (PinnedWhirProfile.pinnedBase P (ExplicitEngine.explicitBase hash khash P c₀) c₀) thash

/-- The explicit engine IS `InstalledInitialTranscript.installedInitialEngine`
over `initialBase`, by composing the two adopted `rfl` identities
`ExplicitEngine.explicit_is_composed_over_the_explicit_base` and
`ComposedEngine.composed_is_the_installed_initial_engine`. -/
theorem explicit_is_the_installed_initial_engine (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    engine gdec hash thash khash P c₀ =
      InstalledInitialTranscript.installedInitialEngine (initialBase hash thash khash P c₀) gdec
        hash (PinnedWhirProfile.pinnedParams P c₀) thash := rfl

/-- The explicit engine IS `InstalledWhirTail.installedEngine` over `tailBase`. -/
theorem explicit_is_the_installed_tail_engine (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    engine gdec hash thash khash P c₀ =
      InstalledWhirTail.installedEngine (tailBase hash thash khash P c₀) gdec hash
        (PinnedWhirProfile.pinnedParams P c₀) := rfl

/-- The explicit engine IS `ComposedEngine.composedEngine` over the explicit
base, so every `ComposedEngine` theorem is available at it. -/
theorem explicit_is_the_composed_engine (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    engine gdec hash thash khash P c₀ =
      ComposedEngine.composedEngine (ExplicitEngine.explicitBase hash khash P c₀) gdec hash thash
        P c₀ := rfl

/-! ## 2. What acceptance alone gives

Everything in this section is DISCHARGED, not assumed: each item is an adopted
result read at the explicit engine. They are collected so that the residue
inventory of section 3 can be seen to exclude them. -/

/-- Acceptance supplies the envelope, the shape, the degree bound, the two round
lengths, the two outer lane lengths and the derived gate point's width. None of
these is a residual hypothesis. -/
theorem explicit_accepted_run_facts (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (truths : List (List Element))
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ()) :
    Verifier.envelope c = true ∧ Verifier.shape pin c p = true ∧
    c.degreeBits ≤ 13 ∧
    p.logRounds.length = c.degreeBits ∧ p.gateRounds.length = c.degreeBits ∧
    (ConditionalSoundness.logLaneOf (engine gdec hash thash khash P c₀) c p truths).length
      = c.degreeBits ∧
    (ConditionalSoundness.gateLaneOf (engine gdec hash thash khash P c₀) c p truths).length
      = c.degreeBits ∧
    (TranscriptProvenance.gatePointColumn (engine gdec hash thash khash P c₀) c p).length
      = c.degreeBits ∧
    p.preprocessedRoot = pin.preprocessedRoot := by
  have hes := ComposedEngine.composed_acceptance_envelope_and_shape
    (ExplicitEngine.explicitBase hash khash P c₀) gdec hash thash P c₀ pin chain c p hacc
  have hdb := ComposedEngine.composed_acceptance_bounds_degree_bits
    (ExplicitEngine.explicitBase hash khash P c₀) gdec hash thash P c₀ pin chain c p hacc
  have hlane := ConditionalSoundness.lane_length_of_shape
    (engine gdec hash thash khash P c₀) c p truths hdb.2.2.1 hdb.2.2.2
  exact ⟨hes.1, hes.2, hdb.1, hdb.2.2.1, hdb.2.2.2, hlane.1, hlane.2,
    GatePointZeroCheck.accepted_gate_point_width _ gdec pin chain c p hacc,
    ConstantsProvenance.accepted_root_is_pinned _ gdec pin chain c p hacc⟩

/-- `TranscriptProvenance.DerivedInitial` holds UNCONDITIONALLY for the explicit
engine: its initial observation IS the adopted derivation. Discharged, not
assumed (`ComposedEngine.composed_initial_is_derived`). -/
theorem explicit_initial_is_derived (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (c : Verifier.Config) (p : Verifier.Proof) :
    TranscriptProvenance.DerivedInitial thash (engine gdec hash thash khash P c₀) c p :=
  ComposedEngine.composed_initial_is_derived (ExplicitEngine.explicitBase hash khash P c₀) gdec
    hash thash P c₀ c p

/-- The point of `JointChallengeSpace.JointSpace` the run actually produces: the
adopted `InstalledRoundCommit.actualDigestDraw` at the run's own digest chain. -/
noncomputable def actualDigestDraw (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) : JointChallengeSpace.JointSpace c.degreeBits :=
  InstalledRoundCommit.actualDigestDraw thash c p

/-- `ComposedEngine.composed_actual_digest_draw_encodes_run` at the explicit
engine: the actual-digest draw encodes the run. A COORDINATE statement; no law
is attached to it here or anywhere. -/
theorem explicit_actual_digest_draw_encodes_run (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (logTruths gateTruths : List (List Element))
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ()) :
    JointChallengeSpace.DrawEncodesRun thash (engine gdec hash thash khash P c₀) c p
      logTruths gateTruths (actualDigestDraw thash c p) := by
  have h := ComposedEngine.composed_acceptance_bounds_degree_bits
    (ExplicitEngine.explicitBase hash khash P c₀) gdec hash thash P c₀ pin chain c p hacc
  exact ComposedEngine.composed_actual_digest_draw_encodes_run
    (ExplicitEngine.explicitBase hash khash P c₀) gdec hash thash P c₀ c p logTruths gateTruths
    h.1 h.2.2.1 h.2.2.2

/-- The point of `InstalledIndexSampler.IndexSpace` the run actually produces:
the adopted `InstalledIndexSampler.actualIndexDraw` at the post-claims digest of
the run's own decoded rounds snapshot. -/
noncomputable def actualIndexDraw (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) : InstalledIndexSampler.IndexSpace c.indexBits :=
  InstalledIndexSampler.actualIndexDraw thash
    (InstalledIndexSampler.indexDigest thash
      (InstalledRoundCommit.concreteFinal thash
        (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)) p.used) c.indexBits

/-- The index-space counterpart of `explicit_actual_digest_draw_encodes_run`,
assembled from `ComposedEngine.composed_accepted_sampled_indices_absorb_used_claims`
and `ComposedEngine.composed_accepted_snapshot_decodes`: both derived index lanes
have length `c.indexBits` and carry, coordinate by coordinate, the reductions of
`actualIndexDraw`. Again a COORDINATE statement. -/
theorem explicit_index_lanes_are_draw_coordinates (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ()) :
    (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p).log.length = c.indexBits ∧
    (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p).gate.length = c.indexBits ∧
    (∀ i : Fin c.indexBits,
      (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p).log.get? i.val =
        some (OuterChallenge.reduceTriple
          (actualIndexDraw thash c p (InstalledIndexSampler.IndexDraw.log i))).toVerifier) ∧
    (∀ i : Fin c.indexBits,
      (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p).gate.get? i.val =
        some (OuterChallenge.reduceTriple
          (actualIndexDraw thash c p (InstalledIndexSampler.IndexDraw.gate i))).toVerifier) := by
  obtain ⟨st, hst, -, -, hlogLen, hgateLen, hlog, hgate⟩ :=
    ComposedEngine.composed_accepted_sampled_indices_absorb_used_claims
      (ExplicitEngine.explicitBase hash khash P c₀) gdec hash thash P c₀ pin chain c p hacc
  have hdec := (ComposedEngine.composed_accepted_snapshot_decodes
    (ExplicitEngine.explicitBase hash khash P c₀) gdec hash thash P c₀ pin chain c p hacc).1
  have hsteq : st = InstalledRoundCommit.concreteFinal thash
      (OuterInitial.derive thash c (Verifier.statement p)).state 0
      (p.logRounds.zip p.gateRounds) := Option.some.inj (hst.symm.trans hdec)
  subst hsteq
  exact ⟨hlogLen, hgateLen, fun i => hlog i.val i.isLt, fun i => hgate i.val i.isLt⟩

/-! ## 3. THE RESIDUE INVENTORY -/

/-- **THE EXACT LIST OF WHAT IS STILL ASSUMED**, at a fixed deployment
`(gdec, hash, thash, khash, P, c₀)` and a fixed accepted call
`(pin, chain, c, p)`, for the explicit engine.

**THIS IS NOT AN EXTRACTION-ONLY LIST, AND THE STRUCTURE IS NAMED
`AssemblyResidue` RATHER THAN `ExtractionResidue` BECAUSE OF IT.** Six of the
nineteen fields say nothing about an extractor: `tableCanonical` and
`canonicalRow` are KECCAK idealisations about the pinned profile table,
`deployment` and `deployedBounded` are CONSTRUCTOR facts about what a deployer
pinned, and `gatesEncodingBound` and `whirEncodingBound` are ABI facts about
Solidity word bounds. The remaining thirteen are the R1b / R2 / R3 extraction
residue proper.

**JOINT SATISFIABILITY WITH ACCEPTANCE IS NOT EXHIBITED.** Exhibiting it would require an accepting
proof for the explicit engine -- a witness this module does not build and the
adopted tree does not contain -- so `explicit_good_draw_assembly` states only the
CONDITIONAL SHAPE. What IS established is that the inventory is not refutable by
the assembly's own conclusions: the reviewer's refutation of the previous
revision went through the unguarded index bad event, which is now guarded.

Every field is either an adopted named residue or an adopted hypothesis about
data the extraction is supposed to produce. Nothing here is about an HONEST
prover: the statement being assembled is the SOUNDNESS direction, so no
`HonestNormProver` field, no `zeroSum`, and no honest-truth-length field appears.
Nothing here is about a FORGING prover either: the previous revision carried
`columnNonDegeneracy`, `suppliedColumn`, `committedColumn`, `constIndexLt`,
`cutLe` and `constantsColumnsOfRoot`, and the first of those is FALSE for an
honest constants column, so every conclusion was silently conditioned on a
forgery. Those six live in
`constants_forgery_forces_join_or_opening_off_bad_set` now, where the condition
is written down. What acceptance already gives is in
`explicit_accepted_run_facts` and is NOT repeated here.

**EVERY FIELD IS CONSUMED BY `explicit_good_draw_assembly`, AND EVERY FIELD
REACHES ONE OF ITS FOUR CONCLUSIONS**; section 7 maps each one to the conjunct
that uses it. The two are not the same test, and the previous revision passed
only the first: `slotCoefficientsLength` and `logLaneDegree` were consumed, but
only through the MASS half of a composed theorem whose mass half the proof
discarded with `.2`, so neither reached a conclusion. Conjunct (1) now goes
through the DETERMINISTIC adopted theorem
`JointChallengeSpace.derived_selected_gate_constraints_vanish_at_a_good_draw`,
which needs neither of them nor any gate-lane degree bound, and both fields are
GONE from the inventory. They remain explicit hypotheses of `bad_event_mass_le`,
where they are what the counting argument actually consumes. -/
structure AssemblyResidue (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (c : Verifier.Config) (p : Verifier.Proof)
    (wq : VkParams) (gates : List Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells)
    (gateTruths : List (List Element)) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) : Prop where
  /-- (a) The profile table really is the generated canonical table, and keccak
  separates canonical targets. NOT DISCHARGED: keccak is not modelled anywhere in
  the adopted tree, and nineteen of the twenty-one rows ship only as digests. -/
  tableCanonical : PinnedWhirProfile.TableIsCanonical P
  /-- (a) The accepted call's packed dimension is one of the two TRANSCRIBED
  rows. NOT DISCHARGED for the other nineteen dimensions, which are not in the
  repository in record form. -/
  canonicalRow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq
  /-- (b) The constructor-time deployment fact: the pinned configuration digest
  was computed from `c₀`. NOT DISCHARGED: nothing in the model establishes what a
  deployer pinned. -/
  deployment : pin.configDigest = khash (ExplicitEngine.encodeConfig c₀)
  /-- (b) The deployed configuration's ABI words fit in `uint256`. NOT
  DISCHARGED for `c₀`, whose envelope the runtime never rechecks. -/
  deployedBounded : ExplicitEngine.Bounded c₀
  /-- (b) The first of the two opaque byte-length bounds
  `ExplicitEngine.bounded_of_acceptance` needs. -/
  gatesEncodingBound : c.gatesEncoding.length < ExplicitEngine.wordBound
  /-- (b) The second opaque byte-length bound. -/
  whirEncodingBound : c.whirEncoding.length < ExplicitEngine.wordBound
  /-- (c) **R1b, AT THE FOLD LEVEL, FOR THIS RUN.** Each of the five bound cells
  is a claim about a table the extractor produces, evaluated at the cell's packed
  point. This is the conclusion `InstalledWhirTail.TailExtractsFoldLevel` delivers
  (`fold_level_opening_of_tail_extraction`); it is WHIR proximity plus sumcheck
  soundness and is NOT DISCHARGED anywhere in this tree. -/
  foldLevelOpening : ∀ i : Fin 5, OpenedClaimFold.CellOpensFullTable
    (Verifier.whirContext Connections.packedFold c p
      (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p)
      (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p))
    i.val (OpenedClaimFold.cellPoint i) (cols i)
    (OpenedClaimFold.lift (OpenedClaimFold.cellRow
      (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) i))
    (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
      (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) i).2)
  /-- (f) The extracted columns are FULL tables for the row point. A width fact
  about extractor output; NOT DISCHARGED. -/
  extractedColumnHeight : ∀ col ∈ cols cellIndex, col.length =
    2 ^ (OpenedClaimFold.cellRow
      (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex).length
  /-- (f) **THE COMMITTED WIDTH.** The extracted family has exactly as many
  columns as the run supplied cells. Kept as a field here so the assembly is
  usable under the R3-free fold-level predicate alone, where only the capacity
  clause of `Verifier.envelope` is available (`≤ 2 ^ c.indexBits` on each side,
  `IndexPointZeroCheck.bound_cell_supplied_width_le`, and
  `IndexPointZeroCheck.padding_hides_unequal_widths` shows that gap is real).
  Under the R1b honest-openings relation it IS derivable: the `opened` field is a
  `List.map`, so the widths agree — `ExtractorConstruction.committed_width_of_openings`
  discharges this field from `HonestOpenings`. -/
  committedWidth : (cols cellIndex).length =
    (OpenedClaimFold.boundCell p.used
      (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1.length
  /-- (d) R2 field 1: the supplied gate split IS the decoded gate list. The
  EXISTENCE of a decoded list is a theorem
  (`ExplicitEngine.accepted_gate_rows_are_the_decoded_length`); that it is this
  particular split is definitional pinning. -/
  gatesDecode : gdec c.gatesEncoding = some gates
  /-- (d) R2 field 2: the extracted state has the widths and shapes the gate
  configuration demands. About extractor output; NOT DISCHARGED. -/
  extractedStateConsistent : GateDenseRound.Consistent (Integrated.gateConfig c) s0
  /-- (d) R2 field 3: the extracted sumcheck truth chain, at the DERIVED gate
  alpha. About extractor output; NOT DISCHARGED. -/
  extractedTruthChain : GateClaimChain.TruthChain (Integrated.gateConfig c) gates
    (GateTerminalBinding.publicHashFunction
      ((engine gdec hash thash khash P c₀).publicInputsHash p.publicInputs))
    (TranscriptProvenance.gateAlphaElement thash c p) sLast xg s0
    (ConditionalSoundness.gateLaneOf (engine gdec hash thash khash P c₀) c p gateTruths)
  /-- (d) R2 field 4. NOT DISCHARGED: `Verifier.envelope` caps
  `numGateConstraints` at 123 but never demands positivity. -/
  gateConstraintsPositive : 0 < c.numGateConstraints
  /-- (d) R2 field 5: the last extracted state's tables bind to the cells. -/
  lastCells : GateTerminalBinding.bindTables sLast.tables xg = cells.tables
  /-- (d) R2 field 6: **THE EXTRACTION JOIN.** The bound cells ARE the accepted
  claims. This is the adopted open join; NOT DISCHARGED. -/
  cellsMatchClaims : GateTerminalBinding.CellsMatchClaims c cells
    (GateTerminalBinding.gateTerminalInput p)
  /-- (d) R2 field 7 (strengthened S1): the extracted eq table is the one the
  DERIVED gate tau names. -/
  eqProvenance : EqTableProvenance.GateEqProvenance s0
    (TranscriptProvenance.gateTauColumn thash c p)
  /-- (d) R2 field 8: the binding data turning S1 into the adopted eq-cell field. -/
  eqCellBinding : GateDerivedRejection.EqCellBinding (engine gdec hash thash khash P c₀) c p s0
    cells
  /-- (d) R2 field 9 (strengthened S2): some row of the extracted tables actually
  selects a gate. Under `ConstantsProvenance.SuppliedConstantsAreCommitted` this
  becomes a deployment property
  (`ConstantsProvenance.activeFilter_is_a_deployment_property`); without it, NOT
  DISCHARGED. -/
  activeFilter : ∃ i, i < 2 ^ c.degreeBits ∧ ∃ g ∈ gates,
    GateRejectionPower.rowFilter (Integrated.gateConfig c) g s0.tables i ≠ Verifier.zero
  /-- (d) **THE LAST FIELD.** The alpha-side slot coefficients of every Boolean
  row exist. About extractor output; NOT DISCHARGED.

  **NO DEGREE-BOUND AND NO COEFFICIENT-WIDTH FIELD FOLLOWS IT.** The previous
  revision carried `slotCoefficientsLength` and `logLaneDegree` after this one.
  Neither reaches a conclusion of `explicit_good_draw_assembly`: the
  deterministic adopted theorem behind conjunct (1) needs no lane degree bound
  and no bound on `(coeffsOf i).length`, and the composed theorem that does need
  them needs them only for its MASS half, which this module's proof discards.
  Both are now explicit hypotheses of `bad_event_mass_le` -- `hlen` and
  `hlogDeg` -- where the counting argument really consumes them, and neither is
  assumed by the main theorem. -/
  slotCoefficients : ∀ i, i < 2 ^ c.degreeBits →
    AlphaZeroCheck.slotCoefficients (Integrated.gateConfig c) gates
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (GateTerminalBinding.publicHashFunction
        ((engine gdec hash thash khash P c₀).publicInputsHash p.publicInputs))
      = some (coeffsOf i)

/-- The nine gate-side fields really are the adopted
`GateDerivedRejection.DerivedGateAssumptions`, field for field. -/
def toDerivedGateAssumptions {gdec : Integrated.DecodeGates} {hash : Spongefish.Hash}
    {thash : Transcript.Hash} {khash : Verifier.Bytes → Verifier.Root} {P : Profile}
    {c₀ : Verifier.Config} {pin : Verifier.Pinned} {c : Verifier.Config} {p : Verifier.Proof}
    {wq : VkParams} {gates : List Gates.GateInfo}
    {s0 sLast : GateTerminalBinding.ProverState} {xg : Element}
    {cells : GateTerminalBinding.Cells} {gateTruths : List (List Element)}
    {coeffsOf : Nat → List Element} {cellIndex : Fin 5} {cols : Fin 5 → List (List Element)}
    (H : AssemblyResidue gdec hash thash khash P c₀ pin c p wq gates s0 sLast xg cells
      gateTruths coeffsOf cellIndex cols) :
    GateDerivedRejection.DerivedGateAssumptions thash (engine gdec hash thash khash P c₀) gdec c p
      gates s0 sLast xg cells gateTruths :=
  { gatesDecode := H.gatesDecode
    extractedStateConsistent := H.extractedStateConsistent
    extractedTruthChain := H.extractedTruthChain
    gateConstraintsPositive := H.gateConstraintsPositive
    lastCells := H.lastCells
    cellsMatchClaims := H.cellsMatchClaims
    eqProvenance := H.eqProvenance
    eqCellBinding := H.eqCellBinding
    activeFilter := H.activeFilter }

/-- **THE GATE LANE'S DEGREE BOUND IS DERIVED, NOT ASSUMED.** An earlier revision
carried it as a field `gateLaneDegree`. It is redundant: the MESSAGE half is
`ConditionalSoundness.gate_lane_message_lengths` from `Verifier.shape`, and the
TRUTH half is
`GateClaimChain.truth_chain_lengths`, which reads the length off the inventory's
own `extractedTruthChain` and `extractedStateConsistent` once acceptance has
supplied `Gates.validateConfiguration`
(`ExplicitEngine.accepted_gate_rows_are_the_decoded_length`, pinned to the
inventory's split by `gatesDecode`).

**IT IS NOT USED BY `explicit_good_draw_assembly` EITHER.** Conjunct (1) runs
through the DETERMINISTIC adopted theorem, which takes no lane degree bound at
all. This theorem exists so that `bad_event_mass_le`'s `hgateDeg` can be supplied
from the inventory rather than assumed; the LOG lane's twin has no such route --
there is no extracted truth chain for the log truths -- and stays an explicit
hypothesis `hlogDeg` of that mass bound. -/
theorem gate_lane_degree_of_extraction (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : VkParams) (gates : List Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ())
    (H : AssemblyResidue gdec hash thash khash P c₀ pin c p wq gates s0 sLast xg cells
      gateTruths coeffsOf cellIndex cols) :
    ∀ r ∈ ConditionalSoundness.gateLaneOf (engine gdec hash thash khash P c₀) c p gateTruths,
      r.message.length ≤ c.quotientDegree + 2 ∧ r.truth.length ≤ c.quotientDegree + 2 := by
  obtain ⟨-, hsh, -, -, -, -, -, -, -⟩ :=
    explicit_accepted_run_facts gdec hash thash khash P c₀ pin chain c p gateTruths hacc
  obtain ⟨-, -, -, hga⟩ := ConditionalSoundness.shape_round_lengths pin c p hsh
  obtain ⟨gates', hdec, -, hv⟩ := ExplicitEngine.accepted_gate_rows_are_the_decoded_length gdec
    hash thash khash P c₀ pin chain c p hacc
  have hgates : gates' = gates := Option.some.inj (hdec.symm.trans H.gatesDecode)
  subst hgates
  intro r hr
  refine ⟨le_of_eq (ConditionalSoundness.gate_lane_message_lengths
    (engine gdec hash thash khash P c₀) c p gateTruths hga r hr), le_of_eq ?_⟩
  exact GateClaimChain.truth_chain_lengths (Integrated.gateConfig c) gates'
    (GateTerminalBinding.publicHashFunction
      ((engine gdec hash thash khash P c₀).publicInputsHash p.publicInputs))
    (TranscriptProvenance.gateAlphaElement thash c p) sLast xg hv
    (ConditionalSoundness.gateLaneOf (engine gdec hash thash khash P c₀) c p gateTruths) s0
    H.extractedStateConsistent H.extractedTruthChain r hr

/-- **THE DEPLOYED PROFILE ROW, FROM THE TWO KECCAK FIELDS.** `tableCanonical`
and `canonicalRow` are not decoration: together with acceptance they pin the
parameter record the tail actually runs at, and give the two positivity facts the
deployed WHIR route needs -- `0 < wq.inDomainSamples` from
`ExplicitEngine.explicit_acceptance_summary`, `wq.rounds ≠ []` from
`PinnedWhirProfile.canonical_rows_are_sampled`, i.e. the deployed route is round
one and not `WhirTail`'s finalsplit branch. -/
theorem explicit_pinned_profile_row (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : VkParams) (hT : PinnedWhirProfile.TableIsCanonical P)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ()) :
    PinnedWhirProfile.pinnedParams P c₀ = wq ∧ 0 < wq.inDomainSamples ∧ wq.rounds ≠ [] := by
  obtain ⟨-, -, hpin, hsamples, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    ExplicitEngine.explicit_acceptance_summary gdec hash thash khash P hT c₀ pin chain c p wq hrow
      hacc
  exact ⟨hpin, hsamples,
    (PinnedWhirProfile.canonical_rows_are_sampled (c.degreeBits + c.indexBits) wq hrow).2.1⟩

/-- **R1b IN ITS ADOPTED NAMED FORM DELIVERS `foldLevelOpening`.**
`InstalledWhirTail.TailExtractsFoldLevel hash wq`, plus acceptance and the
deployed round-one route, produces a column family for which the field holds. So
the field is not a weakening of the adopted residue: it is what that residue
gives on this run.

The two facts about `wq` are NOT free hypotheses: they are `explicit_pinned_profile_row`
at the inventory's own `tableCanonical` and `canonicalRow`. -/
theorem fold_level_opening_of_tail_extraction (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (wq : VkParams) (hT : PinnedWhirProfile.TableIsCanonical P)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hyp : InstalledWhirTail.TailExtractsFoldLevel hash wq)
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ()) :
    ∃ cols : Fin 5 → List (List Element), ∀ i : Fin 5, OpenedClaimFold.CellOpensFullTable
      (Verifier.whirContext Connections.packedFold c p
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p)
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p))
      i.val (OpenedClaimFold.cellPoint i) (cols i)
      (OpenedClaimFold.lift (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) i))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) i).2) := by
  obtain ⟨hwq, -, hrounds⟩ :=
    explicit_pinned_profile_row gdec hash thash khash P c₀ pin chain c p wq hT hrow hacc
  subst hwq
  obtain ⟨extract, hex⟩ := hyp
  have hacc' : Integrated.verify (InstalledWhirTail.installedEngine
      (tailBase hash thash khash P c₀) gdec hash (PinnedWhirProfile.pinnedParams P c₀)) gdec pin
      chain c p = .ok () := hacc
  obtain ⟨r, hrun, -, -, -, -, -⟩ :=
    InstalledWhirTail.installed_acceptance_runs_the_concrete_tail
      (tailBase hash thash khash P c₀) gdec hash (PinnedWhirProfile.pinnedParams P c₀) pin chain
      c p hacc'
  obtain ⟨opening, hopen⟩ := InstalledWhirTail.tail_success_has_round_one_opening hash
    (PinnedWhirProfile.pinnedParams P c₀) _ _ _ hrounds r hrun
  refine ⟨extract (r.retained.origin.initial.commitments.map (fun x => x.root)) opening, ?_⟩
  exact hex (tailBase hash thash khash P c₀) gdec pin chain c p r opening hacc' hrun hopen

/-! ## 4. THE BAD EVENT ON THE JOINT SPACE, AND ITS MASS -/

/-- The FROZEN log `Lane` of the run, at the adopted log compare value. Its
messages read only the round index; `AdaptiveAgreementFamily.frozen_log_walk`
identifies its adaptive event with the adopted `laneEvent` at an encoding
draw. -/
noncomputable def logLane (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (logTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) : OuterSequentialConditioning.Lane :=
  AdaptiveAgreementFamily.frozenLane (ConditionalSoundness.logLaneOf E c p logTruths) 0
    (JointChallengeSpace.logCompareOf t pr) true

/-- The FROZEN gate `Lane` of the run, at the adopted gate compare value. -/
noncomputable def gateLane (thash : Transcript.Hash) (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (gateTruths : List (List Element)) : OuterSequentialConditioning.Lane :=
  AdaptiveAgreementFamily.frozenLane (ConditionalSoundness.gateLaneOf E c p gateTruths) 0
    (GateClaimChain.endpointSum (Integrated.gateConfig c) gates
      (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
      (TranscriptProvenance.gateAlphaElement thash c p) s0) false

/-- **THE FOUR-FAMILY OUTER BAD EVENT ON THE ONE JOINT SPACE**: the adopted
`OuterSequentialConditioning.adaptiveJointBadEvent` at the run's two frozen lanes
-- adaptive outer coupled rounds, the gate tau zero-check family, the gate alpha
family. This is the ONLY half `explicit_good_draw_assembly` needs; the fifth
family below belongs to the constants attack. -/
noncomputable def outerBadEvent (thash : Transcript.Hash) (E : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  OuterSequentialConditioning.adaptiveJointBadEvent c.degreeBits (logLane E c p logTruths t pr)
    (gateLane thash E c p gates s0 gateTruths)
    (ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates
      (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
      (TranscriptProvenance.gateAlphaElement thash c p) s0.tables)
    (2 ^ c.degreeBits) coeffsOf

/-- **THE FULL FIVE-FAMILY BAD EVENT**: `outerBadEvent` united with the adopted
`AdaptiveAgreementFamily.adaptiveAgreementEvent`, the fifth family, at the
constants column a FORGER supplies after `cut` gate coordinates. Only the mass
bound and the constants attack corollary use this; the fifth family is about an
attack, so it is not in the good-draw hypothesis of the main theorem. -/
noncomputable def badEvent (thash : Transcript.Hash) (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) (cut : Nat)
    (colOf : List Element → List Element) (committedCol : List Element) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  outerBadEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf
    ∪ AdaptiveAgreementFamily.adaptiveAgreementEvent c.degreeBits cut colOf committedCol

/-- The two halves of `badEvent`, separated once so that no later proof has to
unfold the union. -/
theorem not_mem_badEvent_parts (thash : Transcript.Hash) (E : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cut : Nat) (colOf : List Element → List Element) (committedCol : List Element)
    (draw : JointChallengeSpace.JointSpace c.degreeBits)
    (hgood : draw ∉
      badEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf cut colOf committedCol) :
    draw ∉ outerBadEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf ∧
    draw ∉ AdaptiveAgreementFamily.adaptiveAgreementEvent c.degreeBits cut colOf committedCol := by
  simp only [badEvent, Finset.mem_union, not_or] at hgood
  exact hgood

/-- A frozen lane inherits the degree bound of the executed lane it replays. -/
theorem frozen_lane_bounded (rs : List ConditionalSoundness.LaneRound) (a b : Element)
    (own : Bool) (n : Nat) (h : ∀ r ∈ rs, r.message.length ≤ n ∧ r.truth.length ≤ n) :
    (AdaptiveAgreementFamily.frozenLane rs a b own).Bounded n := by
  intro xs
  constructor
  · show (((rs.get? (AdaptiveAgreementFamily.halfLength xs)).map
      ConditionalSoundness.LaneRound.message).getD []).length ≤ n
    cases hg : rs.get? (AdaptiveAgreementFamily.halfLength xs) with
    | none => simp
    | some r => simpa using (h r (List.get?_mem hg)).1
  · show (((rs.get? (AdaptiveAgreementFamily.halfLength xs)).map
      ConditionalSoundness.LaneRound.truth).getD []).length ≤ n
    cases hg : rs.get? (AdaptiveAgreementFamily.halfLength xs) with
    | none => simp
    | some r => simpa using (h r (List.get?_mem hg)).2

/-- **THE FIRST MASS BOUND.** Under the explicit joint counting law the bad event
has mass at most `combinedBound degreeBits quotientDegree degreeBits
numGateConstraints + tauTerm degreeBits`, by the adopted
`AdaptiveAgreementFamily.adaptive_joint_union_bound_with_agreement`. The two
summands are kept separate: the fifth family is not one of `combinedBound`'s
three.

**THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR.** It is the mass of an explicit
subset of an explicit finite space under an explicit uniform counting law, it
excludes the dominant WHIR/Merkle term, and nothing says the run's draw is
distributed by that law. -/
theorem bad_event_mass_le (thash : Transcript.Hash) (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) (cut : Nat)
    (colOf : List Element → List Element) (committedCol : List Element)
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf E c p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf E c p gateTruths,
      r.message.length ≤ c.quotientDegree + 2 ∧ r.truth.length ≤ c.quotientDegree + 2)
    (hlen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ c.numGateConstraints)
    (hcut : cut ≤ c.degreeBits) :
    JointChallengeSpace.jointProbability c.degreeBits
        (badEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf cut colOf committedCol)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits c.quotientDegree c.degreeBits
          c.numGateConstraints + ChallengeUnionBound.tauTerm c.degreeBits :=
  AdaptiveAgreementFamily.adaptive_joint_union_bound_with_agreement c.degreeBits c.quotientDegree
    c.numGateConstraints cut (logLane E c p logTruths t pr)
    (gateLane thash E c p gates s0 gateTruths)
    (ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates
      (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
      (TranscriptProvenance.gateAlphaElement thash c p) s0.tables)
    coeffsOf colOf committedCol
    (frozen_lane_bounded _ _ _ _ 5 hlogDeg) rfl
    (frozen_lane_bounded _ _ _ _ (c.quotientDegree + 2) hgateDeg) rfl hlen hcut

/-- **THE OUTER BAD EVENT DOMINATES THE ADOPTED `runBadEvent` AT AN ENCODING
DRAW.** The three families of `JointChallengeSpace.runBadEvent` are matched one
for one: the outer event by
`AdaptiveAgreementFamily.frozen_lane_matches_laneEvent_at_encoding_draw`, the tau
and alpha events verbatim. So a draw outside `outerBadEvent` is outside
`runBadEvent`, which is what the adopted composed theorem consumes. The fifth
family is not needed and is not assumed away. -/
theorem not_mem_run_bad_event (thash : Transcript.Hash) (E : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (draw : JointChallengeSpace.JointSpace c.degreeBits)
    (hdraw : JointChallengeSpace.DrawEncodesRun thash E c p logTruths gateTruths draw)
    (hlogLen : (ConditionalSoundness.logLaneOf E c p logTruths).length = c.degreeBits)
    (hgateLen : (ConditionalSoundness.gateLaneOf E c p gateTruths).length = c.degreeBits)
    (hgood : draw ∉ outerBadEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf) :
    draw ∉ JointChallengeSpace.runBadEvent thash E c p gates s0 logTruths gateTruths t pr
      coeffsOf := by
  have houterGood := hgood
  simp only [outerBadEvent, OuterSequentialConditioning.adaptiveJointBadEvent,
    OuterSequentialConditioning.adaptiveOuterEvent, Finset.mem_union, not_or] at houterGood
  obtain ⟨⟨⟨hlog, hgate⟩, htau⟩, halpha⟩ := houterGood
  simp only [JointChallengeSpace.runBadEvent, JointChallengeSpace.jointBadEvent,
    JointChallengeSpace.outerEvent, Finset.mem_union, not_or]
  refine ⟨⟨⟨fun h => hlog ?_, fun h => hgate ?_⟩, htau⟩, halpha⟩
  · exact (AdaptiveAgreementFamily.frozen_lane_matches_laneEvent_at_encoding_draw thash
      E c p logTruths gateTruths draw hdraw hlogLen hgateLen 0
      (JointChallengeSpace.logCompareOf t pr)).1.mpr h
  · exact (AdaptiveAgreementFamily.frozen_lane_matches_laneEvent_at_encoding_draw thash
      E c p logTruths gateTruths draw hdraw hlogLen hgateLen 0
      (GateClaimChain.endpointSum (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash c p) s0)).2.mpr h


/-! ### NON-VACUITY OF `hdraw`: AN HONEST EXTRACTION MISSES THE OUTER BAD EVENT

The guard fix of section 5 upgraded `hidx` from REFUTABLE to "not refutable by
our own conclusion". The five results below do strictly better for `hdraw`: they
exhibit a class of extraction data -- an HONEST one, whose lane messages ARE the
truths, whose two compare values are `0`, whose gate value is cube-zero and whose
slot coefficients all vanish -- at which `outerBadEvent` is EMPTY, so that `hdraw`
holds at EVERY point of the joint space and in particular at the run's own draw.
`hdraw` is therefore SATISFIED BY EVERY HONEST EXTRACTION, not merely
unrefuted.

**THIS IS NOT JOINT SATISFIABILITY.** Nothing here produces an accepting proof
`p` for the explicit engine, so nothing here shows that `hacc` and
`AssemblyResidue` can hold together with these honest data; what is exhibited is
that the good-draw hypothesis alone has a large and natural solution set. -/

/-- A walk whose per-state bad set is empty along an invariant preserved by every
step has an empty adaptive event. The recursion is on the key list. -/
theorem adaptive_event_empty_of_invariant {ι A σ : Type} [Fintype ι] [DecidableEq ι] [Fintype A]
    [DecidableEq A] (bad : σ → Finset A) (step : σ → A → σ) (Q : σ → Prop)
    (hbad : ∀ s, Q s → bad s = ∅) (hstep : ∀ s a, Q s → Q (step s a)) :
    ∀ (ks : List ι) (s : σ), Q s →
      OuterSequentialConditioning.adaptiveEvent bad step s ks = ∅
  | [], s, _ => OuterSequentialConditioning.adaptiveEvent_nil bad step s
  | k :: ks, s, hs => by
      apply Finset.eq_empty_of_forall_not_mem
      intro w hw
      rw [OuterSequentialConditioning.mem_adaptiveEvent_cons] at hw
      rcases hw with h | h
      · rw [hbad s hs] at h
        exact Finset.not_mem_empty _ h
      · rw [adaptive_event_empty_of_invariant bad step Q hbad hstep ks _ (hstep s (w k) hs)] at h
        exact Finset.not_mem_empty _ h

/-- **AN HONEST LANE**: the running claim IS the running truth claim, and the
message function IS the truth function. This is what an extraction that tells the
truth in a lane looks like, stated on the adopted
`OuterSequentialConditioning.Lane`. -/
def LaneHonest (L : OuterSequentialConditioning.Lane) : Prop :=
  L.claim = L.truthClaim ∧ L.message = L.truth

/-- An honest lane has an empty per-round bad set: the adopted
`ConditionalSoundness.roundBadSet` takes its `∅` branch exactly when claim and
truth claim agree. -/
theorem lane_bad_empty_of_honest (L : OuterSequentialConditioning.Lane) (h : LaneHonest L) :
    OuterSequentialConditioning.laneBad L = ∅ := by
  have hb : L.badSet = ∅ := by
    unfold OuterSequentialConditioning.Lane.badSet
    split
    · rw [ConditionalSoundness.roundBadSet, if_pos h.1]
    · rfl
  ext ds
  simp only [OuterSequentialConditioning.laneBad, hb, JointChallengeSpace.mem_tupleEvent,
    Finset.not_mem_empty]

/-- Honesty is a WALK INVARIANT: one adopted `laneStep` at any digest triple
preserves it, because both halves are the same function of claim and message. -/
theorem lane_step_honest (L : OuterSequentialConditioning.Lane)
    (ds : OuterChallenge.DigestTriple) (h : LaneHonest L) :
    LaneHonest (OuterSequentialConditioning.laneStep L ds) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · show (if L.ownsNext then
        OuterRound.evaluate L.claim (L.message []) (OuterChallenge.reduceTriple ds) else L.claim)
      = (if L.ownsNext then
        OuterRound.evaluate L.truthClaim (L.truth []) (OuterChallenge.reduceTriple ds)
        else L.truthClaim)
    rw [h1, h2]
  · funext xs
    show L.message (OuterChallenge.reduceTriple ds :: xs)
      = L.truth (OuterChallenge.reduceTriple ds :: xs)
    rw [h2]

/-- The two previous results at the adopted adaptive lane event: an honest lane
contributes nothing to the outer family, at any depth. -/
theorem adaptive_lane_event_empty_of_honest (d : Nat) (L : OuterSequentialConditioning.Lane)
    (h : LaneHonest L) : OuterSequentialConditioning.adaptiveLaneEvent d L = ∅ := by
  rw [OuterSequentialConditioning.adaptiveLaneEvent]
  exact adaptive_event_empty_of_invariant _ _ LaneHonest lane_bad_empty_of_honest
    (fun L ds hL => lane_step_honest L ds hL) _ L h

/-- The frozen lane this module builds is honest whenever the executed lane it
replays has `message = truth` in every round and the two compare values agree --
which for `logLane` and `gateLane` means the compare value is `0`, since the
frozen lane is built at `0` on the left. -/
theorem frozen_lane_honest (rs : List ConditionalSoundness.LaneRound) (a : Element) (own : Bool)
    (h : ∀ r ∈ rs, r.message = r.truth) :
    LaneHonest (AdaptiveAgreementFamily.frozenLane rs a a own) := by
  refine ⟨rfl, ?_⟩
  funext xs
  show ((rs.get? (AdaptiveAgreementFamily.halfLength xs)).map
      ConditionalSoundness.LaneRound.message).getD []
    = ((rs.get? (AdaptiveAgreementFamily.halfLength xs)).map
      ConditionalSoundness.LaneRound.truth).getD []
  cases hg : rs.get? (AdaptiveAgreementFamily.halfLength xs) with
  | none => rfl
  | some r => simpa using h r (List.get?_mem hg)

/-- The tau family is empty when the gate value really is zero on the cube: the
adopted `ZeroCheckSemantics.zeroCheckBadSet` is guarded by exactly that. -/
theorem tau_bad_event_empty_of_cube_zero (d : Nat) (g : Nat → Element)
    (h : ZeroCheckSemantics.CubeZero d g) : JointChallengeSpace.tauBadEvent d g = ∅ := by
  ext w
  simp only [JointChallengeSpace.tauBadEvent, JointChallengeSpace.mem_tauEvent,
    ZeroCheckSemantics.zeroCheckBadSet_empty d g h, Finset.not_mem_empty]

/-- The alpha family is empty when every row's slot coefficients all vanish: each
row's adopted `AlphaZeroCheck.alphaBadSet` is then `∅`, and the union over rows
of empty sets is empty. -/
theorem alpha_bad_event_empty_of_all_zero (d rows : Nat) (coeffsOf : Nat → List Element)
    (h : ∀ i, i < rows → AlphaZeroCheck.AllSlotsZero (coeffsOf i)) :
    JointChallengeSpace.alphaBadEvent d rows coeffsOf = ∅ := by
  have hu : ChallengeUnionBound.alphaUnionBadSet rows coeffsOf = ∅ := by
    rw [ChallengeUnionBound.alphaUnionBadSet, ChallengeUnionBound.rowUnion]
    refine Finset.subset_empty.mp (Finset.biUnion_subset.mpr ?_)
    intro i hi
    rw [ChallengeUnionBound.alphaFamily_apply,
      AlphaZeroCheck.alphaBadSet_empty _ (h i (Finset.mem_range.mp hi))]
  rw [JointChallengeSpace.alphaBadEvent, hu]
  exact JointChallengeSpace.coord_event_empty d _

/-- **FOR AN HONEST EXTRACTION THE FOUR-FAMILY OUTER BAD EVENT IS EMPTY.** All
four families vanish at once: both frozen lanes are honest, the tau family is
killed by cube-zero of the gate value and the alpha family by the vanishing of
every row's slot coefficients.

This is POSITIVE evidence about `hdraw`, and it is strictly stronger than the
guard fix of `hidx`: `hdraw` is not merely unrefuted, it is SATISFIED by every
extraction of this shape. It says nothing about whether such an extraction can
accompany an ACCEPTING proof -- that is joint satisfiability, still not
exhibited. -/
theorem honest_outer_bad_event_empty (thash : Transcript.Hash) (E : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (hlogMsg : ∀ r ∈ ConditionalSoundness.logLaneOf E c p logTruths, r.message = r.truth)
    (hlogCmp : JointChallengeSpace.logCompareOf t pr = 0)
    (hgateMsg : ∀ r ∈ ConditionalSoundness.gateLaneOf E c p gateTruths, r.message = r.truth)
    (hgateCmp : GateClaimChain.endpointSum (Integrated.gateConfig c) gates
      (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
      (TranscriptProvenance.gateAlphaElement thash c p) s0 = 0)
    (htau : ZeroCheckSemantics.CubeZero c.degreeBits
      (ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash c p) s0.tables))
    (halpha : ∀ i, i < 2 ^ c.degreeBits → AlphaZeroCheck.AllSlotsZero (coeffsOf i)) :
    outerBadEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf = ∅ := by
  have h1 : OuterSequentialConditioning.adaptiveLaneEvent c.degreeBits
      (logLane E c p logTruths t pr) = ∅ := by
    unfold logLane
    rw [hlogCmp]
    exact adaptive_lane_event_empty_of_honest _ _ (frozen_lane_honest _ _ _ hlogMsg)
  have h2 : OuterSequentialConditioning.adaptiveLaneEvent c.degreeBits
      (gateLane thash E c p gates s0 gateTruths) = ∅ := by
    unfold gateLane
    rw [hgateCmp]
    exact adaptive_lane_event_empty_of_honest _ _ (frozen_lane_honest _ _ _ hgateMsg)
  unfold outerBadEvent OuterSequentialConditioning.adaptiveJointBadEvent
    OuterSequentialConditioning.adaptiveOuterEvent
  rw [h1, h2, tau_bad_event_empty_of_cube_zero _ _ htau,
    alpha_bad_event_empty_of_all_zero _ _ _ halpha]
  simp

/-- The good-draw hypothesis of `explicit_good_draw_assembly`, at an honest
extraction, holds at EVERY point of the joint space -- in particular at the run's
own actual-digest draw. No law and no counting argument is involved. -/
theorem honest_extraction_misses_outer_bad_event (thash : Transcript.Hash)
    (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (hlogMsg : ∀ r ∈ ConditionalSoundness.logLaneOf E c p logTruths, r.message = r.truth)
    (hlogCmp : JointChallengeSpace.logCompareOf t pr = 0)
    (hgateMsg : ∀ r ∈ ConditionalSoundness.gateLaneOf E c p gateTruths, r.message = r.truth)
    (hgateCmp : GateClaimChain.endpointSum (Integrated.gateConfig c) gates
      (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
      (TranscriptProvenance.gateAlphaElement thash c p) s0 = 0)
    (htau : ZeroCheckSemantics.CubeZero c.degreeBits
      (ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash c p) s0.tables))
    (halpha : ∀ i, i < 2 ^ c.degreeBits → AlphaZeroCheck.AllSlotsZero (coeffsOf i))
    (w : JointChallengeSpace.JointSpace c.degreeBits) :
    w ∉ outerBadEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf := by
  rw [honest_outer_bad_event_empty thash E c p gates s0 logTruths gateTruths t pr coeffsOf
    hlogMsg hlogCmp hgateMsg hgateCmp htau halpha]
  exact Finset.not_mem_empty w

/-! ## 5. THE BAD EVENT ON THE INDEX SPACE, AND ITS MASS

**A DIFFERENT FINITE SPACE, A DIFFERENT LAW, A SEPARATE BOUND.** The
constituent-index lanes are squeezed from the post-claims digest, not from the
coupled-round chain, and `InstalledIndexSampler.IndexSpace c.indexBits` is not a
factor of `JointChallengeSpace.JointSpace c.degreeBits`. No joint law over the
two is formalized in the adopted tree -- the only link is the
DOCUMENTED-NOT-DERIVED block labelling of
`InstalledIndexSampler.indexSchedulePosition` -- so the two masses are stated
separately and never added. -/

open Classical in
/-- **THE BAD EVENT ON THE INDEX SPACE**, at ONE bound cell: the adopted
per-lane pullbacks of `IndexPointZeroCheck.cellAgreementSet`, GUARDED by
`IndexPointZeroCheck.CellsDifferOnCube`. Both lanes are included because
`OpenedClaimFold.boundCell` assigns cells `0, 1, 2` to the log lane and `3, 4` to
the gate lane.

**THE GUARD IS NOT COSMETIC.** `cellAgreementSet` is the plain filter
"the two families have the same packed fold at this index point", so when the two
families AGREE ON THE CUBE it is all of `Finset.univ`
(`IndexPointZeroCheck.agreement_set_of_equal_cells`) and the unguarded union would be
the whole index space. A hypothesis "the run's index draw is outside the
unguarded union" is then FALSE whenever the supplied cells are the opened cells
-- which is exactly what `run_per_column_identification` concludes -- so the
previous revision's hypothesis list was refutable by its own conclusion. Guarded,
the agreement case contributes `∅`, whose mass is `0`, so
`index_bad_event_mass_le` needs no side condition at all. This is verbatim the
adopted `ZeroCheckSemantics.zeroCheckBadSet` pattern, whose `CubeZero` branch is
likewise `∅`. -/
noncomputable def indexBadEvent (bits : Nat) (suppliedCells committedCells : List Element) :
    Finset (InstalledIndexSampler.IndexSpace bits) :=
  if IndexPointZeroCheck.CellsDifferOnCube bits suppliedCells committedCells then
    IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells ∪
      IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells
  else ∅

/-- The guard's live branch, mirroring
`ZeroCheckSemantics.zeroCheckBadSet_of_not_cube_zero`. -/
theorem index_bad_event_of_differ (bits : Nat) (suppliedCells committedCells : List Element)
    (h : IndexPointZeroCheck.CellsDifferOnCube bits suppliedCells committedCells) :
    indexBadEvent bits suppliedCells committedCells =
      IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells ∪
        IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells := by
  rw [indexBadEvent, if_pos h]

/-- The guard's dead branch, mirroring `ZeroCheckSemantics.zeroCheckBadSet_empty`:
when the two cell families agree on the whole index cube there is nothing for the
index point to detect, so the event is empty. -/
theorem index_bad_event_of_cube_agreement (bits : Nat)
    (suppliedCells committedCells : List Element)
    (h : ¬ IndexPointZeroCheck.CellsDifferOnCube bits suppliedCells committedCells) :
    indexBadEvent bits suppliedCells committedCells = ∅ := by
  rw [indexBadEvent, if_neg h]

/-- **THE GUARD, AT THE EXACT POINT THE REVIEWER'S REFUTATION ATTACKED.** At
equal cell families the event is EMPTY, not everything. The previous revision's
`indexBadEvent bits A A` was `Finset.univ`, and that is what made the
hypotheses of the main statement jointly inconsistent. -/
theorem index_bad_event_of_equal_cells_is_empty (bits : Nat) (cells : List Element) :
    indexBadEvent bits cells cells = ∅ :=
  index_bad_event_of_cube_agreement bits cells cells (fun ⟨_, _, hne⟩ => hne rfl)

/-- `tauTerm` is a product of nonnegative rationals. Needed only so that the
empty branch of the guard can be bounded; no tactic evaluates
`Fintype.card Element`. -/
theorem tau_term_nonneg (n : Nat) : (0 : ℚ) ≤ ChallengeUnionBound.tauTerm n := by
  rw [ChallengeUnionBound.tauTerm]
  refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) ?_
  · exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  · exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

/-- **THE SECOND MASS BOUND.** Under the explicit index counting law the index
bad event has mass at most `2 * tauTerm indexBits`, one `tauTerm` per lane, by
`IndexPointZeroCheck.log_index_agreement_mass_bound` and its gate twin.

NO `CellsDifferOnCube` SIDE CONDITION: on the agreement branch the event is empty
and its mass is `0`. Same caveats as the first bound, and again nothing says the
run's index draw is distributed by this law. -/
theorem index_bad_event_mass_le (bits : Nat) (suppliedCells committedCells : List Element) :
    IndexPointZeroCheck.indexProbability bits (indexBadEvent bits suppliedCells committedCells)
      ≤ 2 * ChallengeUnionBound.tauTerm bits := by
  have hpos : (0 : ℚ) < (Fintype.card (InstalledIndexSampler.IndexSpace bits) : ℚ) := by
    have h : 0 < (OuterChallenge.wordSize ^ 3) ^ (2 * bits) :=
      pow_pos (pow_pos OuterChallenge.word_size_positive 3) _
    rw [InstalledIndexSampler.index_space_card]
    exact_mod_cast h
  have htau : (0 : ℚ) ≤ ChallengeUnionBound.tauTerm bits := tau_term_nonneg bits
  by_cases hdiff : IndexPointZeroCheck.CellsDifferOnCube bits suppliedCells committedCells
  · rw [index_bad_event_of_differ bits suppliedCells committedCells hdiff]
    have hcard : (IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells ∪
        IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells).card ≤
        (IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells).card +
          (IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells).card :=
      Finset.card_union_le _ _
    have hsplit : IndexPointZeroCheck.indexProbability bits
        (IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells ∪
          IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells) ≤
        IndexPointZeroCheck.indexProbability bits
          (IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells) +
        IndexPointZeroCheck.indexProbability bits
          (IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells) := by
      unfold IndexPointZeroCheck.indexProbability
      rw [div_add_div_same]
      exact JointChallengeSpace.div_le_div_num _ _ _ (by exact_mod_cast hcard) hpos
    have h1 := IndexPointZeroCheck.log_index_agreement_mass_bound bits suppliedCells committedCells
      hdiff
    have h2 := IndexPointZeroCheck.gate_index_agreement_mass_bound bits suppliedCells committedCells
      hdiff
    linarith
  · rw [index_bad_event_of_cube_agreement bits suppliedCells committedCells hdiff]
    unfold IndexPointZeroCheck.indexProbability
    rw [Finset.card_empty, Nat.cast_zero, zero_div]
    linarith

/-- **THE INDEX SIDE, ASSEMBLED AT ONE BOUND CELL.** The adopted
`IndexPointZeroCheck.run_fold_level_gives_per_column_off_bad_set` is a dichotomy:
per-column identification, OR the run's index point sits in a set of density at
most `indexBits / |F|`. A run whose actual index draw misses `indexBadEvent`
lands in the first branch. The three R1b/width hypotheses are exactly the
corresponding fields of `AssemblyResidue`; the capacity bound and the two lane
lengths come from acceptance.

**THE GUARD IS CONSUMED HERE, NOT ASSUMED.** The dichotomy's second branch
delivers `CellsDifferOnCube` itself, which is exactly the guard of
`indexBadEvent`, so the transport unfolds the `if` with a hypothesis the branch
produced. On the first branch `hidx` is never used at all -- and it is the
previous revision's use of an UNGUARDED `hidx` on the first branch that made the
statement refutable. -/
theorem run_per_column_identification (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ())
    (hopen : OpenedClaimFold.CellOpensFullTable
      (Verifier.whirContext Connections.packedFold c p
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p)
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p))
      cellIndex.val (OpenedClaimFold.cellPoint cellIndex) (cols cellIndex)
      (OpenedClaimFold.lift (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).2))
    (hheight : ∀ col ∈ cols cellIndex, col.length =
      2 ^ (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex).length)
    (hcolsW : (cols cellIndex).length =
      (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1.length)
    (hidx : actualIndexDraw thash c p ∉ indexBadEvent c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1)
      (IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex)))) :
    OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1
      = IndexPointZeroCheck.openedCells (cols cellIndex)
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow
            (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex)) := by
  obtain ⟨henv, hsh, -, -, -, -, -, -, -⟩ :=
    explicit_accepted_run_facts gdec hash thash khash P c₀ pin chain c p [] hacc
  obtain ⟨hlogLen, hgateLen, hlogGet, hgateGet⟩ :=
    explicit_index_lanes_are_draw_coordinates gdec hash thash khash P c₀ pin chain c p hacc
  have hcap := IndexPointZeroCheck.bound_cell_supplied_width_le pin c p
    (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex hsh henv
  have hlane : (OpenedClaimFold.boundCell p.used
      (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).2.length
      = c.indexBits := by
    fin_cases cellIndex
    exacts [hlogLen, hlogLen, hlogLen, hgateLen, hgateLen]
  rcases IndexPointZeroCheck.run_fold_level_gives_per_column_off_bad_set c p
    (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p)
    (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex (cols cellIndex)
    ((OpenedClaimFold.boundCell p.used
      (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1.length)
    hlane hheight rfl hcolsW hcap hopen with h | ⟨hdiff, hmem, -⟩
  · exact h
  · rw [index_bad_event_of_differ c.indexBits _ _ hdiff] at hidx
    simp only [Finset.mem_union, not_or] at hidx
    obtain ⟨hlogGood, hgateGood⟩ := hidx
    refine absurd hmem ?_
    fin_cases cellIndex
    exacts [IndexPointZeroCheck.log_index_point_off_agreement_of_draw _ _ _ _ _ hlogGet hlogGood,
      IndexPointZeroCheck.log_index_point_off_agreement_of_draw _ _ _ _ _ hlogGet hlogGood,
      IndexPointZeroCheck.log_index_point_off_agreement_of_draw _ _ _ _ _ hlogGet hlogGood,
      IndexPointZeroCheck.gate_index_point_off_agreement_of_draw _ _ _ _ _ hgateGet hgateGood,
      IndexPointZeroCheck.gate_index_point_off_agreement_of_draw _ _ _ _ _ hgateGet hgateGood]


/-- **CONJUNCT (2) AND `hidx` ARE THE SAME STATEMENT.** Under acceptance and the
three fold/width fields of `AssemblyResidue`, the good-draw hypothesis on the
index space is EQUIVALENT to the identification it is used to prove: forwards by
`run_per_column_identification`, backwards because the GUARD makes
`indexBadEvent bits A A` empty, so once the two cell families are equal no index
point can be in it.

**WHAT THIS MEANS FOR THE MAIN THEOREM.** `hidx` is not refutable (that was the
previous revision's defect, now fixed), but it is also not informative: conjunct
(2) carries no content beyond the transport of a hypothesis. The index side's
real content is the CONTRAPOSITIVE mass statement `index_bad_event_mass_le` --
the set of index points at which a genuinely DIFFERING cell family would still
pass is small under the explicit index law -- and that statement, like every mass
here, is not attached to the run's actual draw by anything in the adopted
tree. -/
theorem index_good_draw_iff_identification (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ())
    (hopen : OpenedClaimFold.CellOpensFullTable
      (Verifier.whirContext Connections.packedFold c p
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p)
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p))
      cellIndex.val (OpenedClaimFold.cellPoint cellIndex) (cols cellIndex)
      (OpenedClaimFold.lift (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).2))
    (hheight : ∀ col ∈ cols cellIndex, col.length =
      2 ^ (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex).length)
    (hcolsW : (cols cellIndex).length =
      (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1.length) :
    (actualIndexDraw thash c p ∉ indexBadEvent c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1)
      (IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex))))
    ↔ (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1
      = IndexPointZeroCheck.openedCells (cols cellIndex)
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow
            (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex))) := by
  constructor
  · intro hidx
    exact run_per_column_identification gdec hash thash khash P c₀ pin chain c p cellIndex cols
      hacc hopen hheight hcolsW hidx
  · intro h
    rw [h, index_bad_event_of_equal_cells_is_empty]
    exact Finset.not_mem_empty _

/-! ## 6. THE ASSEMBLY -/

/-- **WHAT A GOOD DRAW BUYS FOR THE EXPLICIT ENGINE.**

From an accepting `Integrated.verify` call under the base-free
`ExplicitEngine.explicitEngine`, the residue inventory `AssemblyResidue`, and
the two non-membership facts about the run's OWN draws -- the actual-digest draw
on the joint space and the actual index draw on the index space -- four things
follow simultaneously:

1. **THE GATE SIDE.** At every Boolean row of the extracted tables at which the
   distinguished gate is the selected one, every constraint of that gate
   vanishes, and the gate's evaluator succeeds there. This is the DETERMINISTIC
   adopted theorem
   `JointChallengeSpace.derived_selected_gate_constraints_vanish_at_a_good_draw`,
   which takes the nine `DerivedGateAssumptions` fields, `slotCoefficients`,
   acceptance and `hdraw` and NOTHING ELSE -- no lane degree bound, no bound on
   `(coeffsOf i).length`. Those belong to the MASS half of
   `JointChallengeSpace.composed_gate_constraints_vanish_on_the_joint_space`,
   which this statement does not use.
2. **THE INDEX SIDE (R3, one cell).** The supplied cell family at `cellIndex` IS
   the per-column opening family of the extracted columns at the row point --
   the FIRST disjunct of `IndexPointZeroCheck.run_fold_level_gives_per_column_off_bad_set`,
   the second being killed by `hidx` through the GUARD of `indexBadEvent`.

   **THIS CONJUNCT CARRIES NO CONTENT BEYOND A TAUTOLOGICAL TRANSPORT.** Given
   `foldLevelOpening` and the two width/height fields,
   `index_good_draw_iff_identification` shows that `hidx` and conjunct (2) are
   EQUIVALENT: the guard makes `indexBadEvent bits A A = ∅`, so the identification
   gives `hidx` back. The real content of the index side is the CONTRAPOSITIVE
   mass statement -- `index_bad_event_mass_le`, which bounds the mass of the set
   of index points at which a genuinely differing cell family could still pass.
3. **THE DEPLOYED PROFILE ROW.** The pinned parameter record IS the canonical row
   of the accepted packed dimension, it samples a positive number of in-domain
   queries and it runs at least one intermediate round -- so the deployed route
   is round one, not `WhirTail`'s finalsplit branch
   (`explicit_pinned_profile_row`).
4. **THE DEPLOYED CONFIGURATION.** The accepted configuration's core IS the
   deployed one, or `khash` collides
   (`ExplicitEngine.accepted_configuration_is_the_deployed_one_from_lengths`).

**THE NAME.** This is NOT called a soundness assembly. It concludes constraint
vanishing on the EXTRACTED tables plus a per-column identification, under a good
draw; that is not soundness of the deployed system, and calling it so would
misdescribe the statement.

**WHAT THIS IS NOT.** It is not "the circuit is satisfied": the tables are the
extraction's, not a witness's. It is not a probability statement: `hdraw` and
`hidx` are facts about two fixed points of two explicit finite spaces, and
nothing here or in the adopted tree says the run's draws are distributed by
either law. The masses of `bad_event_mass_le` and `index_bad_event_mass_le`
exclude the dominant WHIR/Merkle term and are NOT the system's soundness error;
the deployed wire-v3 profile is around the 100-bit design point.

**`t` AND `pr` ARE PHANTOM HERE.** They occur in no conclusion. Their only role
is to name the log lane's compare value `JointChallengeSpace.logCompareOf t pr`
inside `hdraw`'s log family, and they are carried because the adopted
`AdaptiveAgreementFamily` shape names the frozen log lane that way; the statement
is otherwise independent of them.

**AND IT IS NOT A SATISFIABILITY CLAIM.** `hacc` together with `H` is not
exhibited at any concrete run: producing one would need an accepting proof for
the explicit engine. The previous revision's hypothesis list was worse than
unexhibited -- it was REFUTABLE, because the unguarded `indexBadEvent` let
conjunct (2) contradict `hidx`. That defect is fixed; unexhibitedness remains. -/
theorem explicit_good_draw_assembly (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ())
    (H : AssemblyResidue gdec hash thash khash P c₀ pin c p wq (pre ++ gate :: post) s0 sLast
      xg cells gateTruths coeffsOf cellIndex cols)
    (hdraw : actualDigestDraw thash c p ∉ outerBadEvent thash
      (engine gdec hash thash khash P c₀) c p (pre ++ gate :: post) s0 logTruths gateTruths t pr
      coeffsOf)
    (hidx : actualIndexDraw thash c p ∉ indexBadEvent c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1)
      (IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex)))) :
    (∀ row, row < 2 ^ c.degreeBits →
        (∀ g' ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig c) g' s0.tables row
          = Verifier.zero) →
        (∀ g' ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig c) g' s0.tables row
          = Verifier.zero) →
        GateRejectionPower.rowFilter (Integrated.gateConfig c) gate s0.tables row
          ≠ Verifier.zero →
        ∃ terms, GatesComplete.evaluateUnfiltered gate (AlphaZeroCheck.rowWires s0.tables row)
            (AlphaZeroCheck.rowConstants s0.tables row)
            (GateTerminalBinding.publicHashFunction
              ((engine gdec hash thash khash P c₀).publicInputsHash p.publicInputs))
            (Integrated.gateConfig c).numSelectors = some terms ∧
          ∀ y ∈ terms, y = Verifier.zero)
      ∧ OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
            (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) cellIndex).1
          = IndexPointZeroCheck.openedCells (cols cellIndex)
              (OpenedClaimFold.lift (OpenedClaimFold.cellRow
                (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p) cellIndex))
      ∧ (PinnedWhirProfile.pinnedParams P c₀ = wq ∧ 0 < wq.inDomainSamples ∧ wq.rounds ≠ [])
      ∧ (ExplicitEngine.core c = ExplicitEngine.core c₀
          ∨ ExplicitEngine.KhashCollision khash) := by
  obtain ⟨-, -, -, hlr, hgr, -, -, -, -⟩ :=
    explicit_accepted_run_facts gdec hash thash khash P c₀ pin chain c p logTruths hacc
  have hlogLen := (ConditionalSoundness.lane_length_of_shape
    (engine gdec hash thash khash P c₀) c p logTruths hlr hgr).1
  have hgateLen := (ConditionalSoundness.lane_length_of_shape
    (engine gdec hash thash khash P c₀) c p gateTruths hlr hgr).2
  have hencode := explicit_actual_digest_draw_encodes_run gdec hash thash khash P c₀ pin chain c p
    logTruths gateTruths hacc
  have hrun := not_mem_run_bad_event thash (engine gdec hash thash khash P c₀) c p
    (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf
    (actualDigestDraw thash c p) hencode hlogLen hgateLen hdraw
  -- (1) the gate side
  have hgateSide : ∀ row, row < 2 ^ c.degreeBits →
      (∀ g' ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig c) g' s0.tables row
        = Verifier.zero) →
      (∀ g' ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig c) g' s0.tables row
        = Verifier.zero) →
      GateRejectionPower.rowFilter (Integrated.gateConfig c) gate s0.tables row ≠ Verifier.zero →
      ∃ terms, GatesComplete.evaluateUnfiltered gate (AlphaZeroCheck.rowWires s0.tables row)
          (AlphaZeroCheck.rowConstants s0.tables row)
          (GateTerminalBinding.publicHashFunction
            ((engine gdec hash thash khash P c₀).publicInputsHash p.publicInputs))
          (Integrated.gateConfig c).numSelectors = some terms ∧
        ∀ y ∈ terms, y = Verifier.zero := by
    intro row hrow hpre hpost hactive
    exact JointChallengeSpace.derived_selected_gate_constraints_vanish_at_a_good_draw thash pin
      chain (engine gdec hash thash khash P c₀) gdec c p pre post gate s0 sLast xg cells logTruths
      gateTruths t pr coeffsOf row (actualDigestDraw thash c p)
      (explicit_initial_is_derived gdec hash thash khash P c₀ c p) (toDerivedGateAssumptions H)
      hacc H.slotCoefficients hrow hpre hpost hactive hencode hrun
  -- (2) the index side
  have hindex := run_per_column_identification gdec hash thash khash P c₀ pin chain c p cellIndex
    cols hacc (H.foldLevelOpening cellIndex) H.extractedColumnHeight H.committedWidth hidx
  exact ⟨hgateSide, hindex,
    explicit_pinned_profile_row gdec hash thash khash P c₀ pin chain c p wq H.tableCanonical
      H.canonicalRow hacc,
    ExplicitEngine.accepted_configuration_is_the_deployed_one_from_lengths gdec hash thash khash P
      c₀ pin chain c p H.deployment H.gatesEncodingBound H.whirEncodingBound H.deployedBounded
      hacc⟩

/-- **ATTACK THEOREM, CONDITIONAL ON A FORGED CONSTANTS COLUMN.**

**EVERY HYPOTHESIS BELOW BEYOND `hacc` AND `AssemblyResidue` DESCRIBES A
FORGERY**, and they are written out here rather than hidden in the inventory,
because the previous revision put them (and the non-degeneracy premise) inside
`ResidualHypotheses` and thereby conditioned its MAIN theorem on the run
carrying a forged constants column. The forgery-side hypotheses are:

* `hcolsOfRoot` -- the R3 map from a `Verifier.Root` to the columns it commits
  to. The adopted `OpeningBinding` contains no such map; NOT DISCHARGED.
* `hsupplied` -- the supplied constants column at `constIndex` is the one the
  forger chose after reading the first `cut` gate coordinates. At `cut = 0` it is
  a fixed column (`AdaptiveAgreementFamily.cut_zero_is_fixed_column`).
* `hcommitted`, `hconstLt` -- which committed column it is claimed to be, and
  that the index is a constants index.
* `hnondeg`, in the second conjunct only -- **THE NON-DEGENERACY OF THE
  FORGERY.** NOT GENERICALLY TRUE. It is FALSE for an HONEST column, where the
  bound difference is identically zero, and
  `AdaptiveAgreementFamily.escape_kills_hnondeg` exhibits, for every `d ≥ 1`, a
  genuine width-`2 ^ d` forgery for which it is false at every gate point and
  every `cut ≥ 1`. It is the residual branch of the adopted dichotomy; excluding
  it is R2/R3's job, and nothing here does it.

The two conclusions are the adopted dichotomy
(`GatePointZeroCheck.accepted_column_forgery_forces_join_or_opening_off_bad_set_of_consistent`
with its root branch closed by `ConstantsProvenance.accepted_root_is_pinned` and
its join branch by `cellsMatchClaims`), and the same with `¬ PointAgrees`
delivered by the fifth family
(`AdaptiveAgreementFamily.gate_point_off_adaptive_agreement_of_joint`) at a draw
outside `AdaptiveAgreementFamily.adaptiveAgreementEvent`. -/
theorem constants_forgery_forces_join_or_opening_off_bad_set (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (wq : VkParams) (gates : List Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (constCols : Fin 5 → List (List Element))
    (committedBy : Verifier.Root → List (List Element)) (constIndex cut : Nat)
    (colOf : List Element → List Element) (committedCol : List Element)
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ())
    (H : AssemblyResidue gdec hash thash khash P c₀ pin c p wq gates s0 sLast xg cells
      gateTruths coeffsOf cellIndex cols)
    (hcolsOfRoot : ConstantsProvenance.ConstantsColumnsOfRoot committedBy p constCols)
    (hsupplied : s0.tables.constants.get? constIndex =
      some (colOf ((TranscriptProvenance.gatePointColumn
        (engine gdec hash thash khash P c₀) c p).take cut)))
    (hcommitted : (committedBy pin.preprocessedRoot).get? constIndex = some committedCol)
    (hconstLt : constIndex < c.numConstants) :
    (GatePointZeroCheck.PointAgrees
        (colOf ((TranscriptProvenance.gatePointColumn
          (engine gdec hash thash khash P c₀) c p).take cut)) committedCol
        (TranscriptProvenance.gatePointColumn (engine gdec hash thash khash P c₀) c p)
      ∨ ¬ OpeningBinding.OpensCommittedTable c p
          (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p)
          (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) constCols)
    ∧ (¬ ZeroCheckSemantics.CubeZero (c.degreeBits - cut)
          (AdaptiveAgreementFamily.bindPrefix
            ((TranscriptProvenance.gatePointColumn
              (engine gdec hash thash khash P c₀) c p).take cut)
            (GatePointZeroCheck.diffColumn
              (colOf ((TranscriptProvenance.gatePointColumn
                (engine gdec hash thash khash P c₀) c p).take cut)) committedCol)) →
        actualDigestDraw thash c p ∉
          AdaptiveAgreementFamily.adaptiveAgreementEvent c.degreeBits cut colOf committedCol →
        ¬ OpeningBinding.OpensCommittedTable c p
            (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p)
            (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) constCols) := by
  obtain ⟨-, -, -, -, -, -, -, hwidth, -⟩ :=
    explicit_accepted_run_facts gdec hash thash khash P c₀ pin chain c p gateTruths hacc
  have hconst : ¬ GatePointZeroCheck.PointAgrees
      (colOf ((TranscriptProvenance.gatePointColumn
        (engine gdec hash thash khash P c₀) c p).take cut)) committedCol
      (TranscriptProvenance.gatePointColumn (engine gdec hash thash khash P c₀) c p) →
      ¬ OpeningBinding.OpensCommittedTable c p
        (Verifier.derivedRounds (engine gdec hash thash khash P c₀) c p)
        (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p) constCols := by
    intro hna
    rcases GatePointZeroCheck.accepted_column_forgery_forces_join_or_opening_off_bad_set_of_consistent
      (engine gdec hash thash khash P c₀) gdec pin chain c p s0 cells constCols committedBy
      constIndex _ committedCol hconstLt hacc H.extractedStateConsistent H.eqCellBinding
      hcolsOfRoot hsupplied hcommitted hna with h | h
    · exact absurd H.cellsMatchClaims h
    · exact h
  refine ⟨?_, ?_⟩
  · by_cases hp : GatePointZeroCheck.PointAgrees
        (colOf ((TranscriptProvenance.gatePointColumn
          (engine gdec hash thash khash P c₀) c p).take cut)) committedCol
        (TranscriptProvenance.gatePointColumn (engine gdec hash thash khash P c₀) c p)
    · exact Or.inl hp
    · exact Or.inr (hconst hp)
  · intro hnondeg hgood
    have hencode := explicit_actual_digest_draw_encodes_run gdec hash thash khash P c₀ pin chain
      c p logTruths gateTruths hacc
    exact hconst (AdaptiveAgreementFamily.gate_point_off_adaptive_agreement_of_joint
      (engine gdec hash thash khash P c₀) c p gateTruths cut colOf committedCol
      (actualDigestDraw thash c p) hwidth hencode.gateDrawn hnondeg hgood)

/-! ## 7. THE RESIDUE INVENTORY IS EXACT, AND THE ENVELOPE FIGURES

### Exactness, in both directions

**NO FIELD IS UNUSED, AND EVERY FIELD REACHES A CONCLUSION.** Each of the
nineteen fields of `AssemblyResidue` is consumed by `explicit_good_draw_assembly`
ON THE ROUTE TO ONE OF ITS FOUR CONJUNCTS; the table below names, for each one,
that conjunct and the adopted theorem doing the work. Two earlier defects are now
gone. Revision 1 had seven DEAD entries (`tableCanonical`, `canonicalRow`,
`deployment`, `deployedBounded`, `gatesEncodingBound`, `whirEncodingBound`,
`cutLe`), a phantom parameter `wq`, one derivable field (`gateLaneDegree`) and six
forgery premises; the dead ones are used by conjuncts (3) and (4), `wq` is pinned
by conjunct (3), the derivable one is `gate_lane_degree_of_extraction`, and the
forgery premises are in `constants_forgery_forces_join_or_opening_off_bad_set`.
Revision 2 had two entries that were consumed but reached NOTHING --
`slotCoefficientsLength` and `logLaneDegree`, which fed only the MASS half of
`JointChallengeSpace.composed_gate_constraints_vanish_on_the_joint_space`, and
that half was discarded with `.2`. Conjunct (1) now goes straight through the
deterministic
`JointChallengeSpace.derived_selected_gate_constraints_vanish_at_a_good_draw`,
and both fields are GONE from the inventory; they are explicit hypotheses
`hlen` and `hlogDeg` of `bad_event_mass_le` instead, which is where the counting
argument actually uses them. `logTruths` went with them: it was a parameter of
the structure only because `logLaneDegree` mentioned it.

**NO DISCHARGED FACT IS ASSUMED.** `residue_inventory_is_exact` states, from
ACCEPTANCE ALONE, the facts a reader might otherwise expect to find in the
inventory; each is a cited adopted theorem.

| field | consumed by | adopted theorem |
| --- | --- | --- |
| `tableCanonical` | conjunct (3) | `ExplicitEngine.explicit_acceptance_summary` |
| `canonicalRow` | conjunct (3) | `explicit_acceptance_summary` + `PinnedWhirProfile.canonical_rows_are_sampled` |
| `deployment` | conjunct (4) | `ExplicitEngine.accepted_configuration_is_the_deployed_one_from_lengths` |
| `deployedBounded` | conjunct (4) | the same |
| `gatesEncodingBound` | conjunct (4) | the same, through `ExplicitEngine.bounded_of_acceptance` |
| `whirEncodingBound` | conjunct (4) | the same |
| `foldLevelOpening` | conjunct (2) | `IndexPointZeroCheck.run_fold_level_gives_per_column_off_bad_set` |
| `extractedColumnHeight` | conjunct (2) | the same (`hc`) |
| `committedWidth` | conjunct (2) | the same (`hcolsW`) |
| `gatesDecode` | conjunct (1) | `GateDerivedRejection.DerivedGateAssumptions` field 1; also `gate_lane_degree_of_extraction` |
| `extractedStateConsistent` | conjunct (1) | field 2; also the truth half of the gate lane bound |
| `extractedTruthChain` | conjunct (1) | field 3; also `GateClaimChain.truth_chain_lengths` |
| `gateConstraintsPositive` | conjunct (1) | field 4 |
| `lastCells` | conjunct (1) | field 5 |
| `cellsMatchClaims` | conjunct (1) | field 6 |
| `eqProvenance` | conjunct (1) | field 7 |
| `eqCellBinding` | conjunct (1) | field 8 |
| `activeFilter` | conjunct (1) | field 9 |
| `slotCoefficients` | conjunct (1) | `JointChallengeSpace.derived_selected_gate_constraints_vanish_at_a_good_draw` (`hcoeffs`) |

Nineteen rows, nineteen fields. Conjunct (1)'s adopted theorem takes the nine
`DerivedGateAssumptions` fields, `slotCoefficients`, `hacc` and `hdraw` and
nothing else.

### Why each remaining field is still assumed

| field | residue class | why it is still assumed |
| --- | --- | --- |
| `tableCanonical` | keccak | the profile table ships as digests; keccak is not modelled anywhere in the adopted tree |
| `canonicalRow` | keccak | only the rows `n = 10` and `n = 21` are transcribed; nineteen rows exist only as digests |
| `deployment` | constructor fact | nothing in the model says what a deployer pinned |
| `deployedBounded` | constructor fact | the runtime never rechecks `c₀`'s envelope |
| `gatesEncodingBound`, `whirEncodingBound` | ABI | Lean `Nat` is unbounded; Solidity `uint256` is not |
| `foldLevelOpening` | R1b | WHIR proximity plus sumcheck soundness; `InstalledWhirTail.TailExtractsFoldLevel` is the adopted named form |
| `extractedColumnHeight` | R1b / width | a shape fact about extractor output |
| `committedWidth` | width | irreducible only under the fold-level predicate (capacity gives `≤`); derivable from `HonestOpenings.opened` (`ExtractorConstruction.committed_width_of_openings`) |
| `gatesDecode` | bookkeeping | the EXISTENCE of the decoded list is a theorem; pinning the split is definitional |
| `extractedStateConsistent`, `extractedTruthChain`, `lastCells`, `cellsMatchClaims`, `eqProvenance`, `eqCellBinding`, `activeFilter` | R2 | extraction: the adopted open join and the data it is supposed to produce |
| `gateConstraintsPositive` | envelope gap | `Verifier.envelope` caps `numGateConstraints` but never demands positivity |
| `slotCoefficients` | R2 | totality of the alpha-side coefficients of every Boolean row of the extracted tables |

NEITHER LANE'S DEGREE BOUND IS IN THIS TABLE, and neither is the width of
`coeffsOf i`. The main theorem needs none of the three. The GATE lane's bound is
derived from the inventory in `gate_lane_degree_of_extraction`; the LOG lane's
bound (`hlogDeg`) and the coefficient width (`hlen`) are explicit hypotheses of
`bad_event_mass_le`, the only statement in the module that consumes them, and the
truth half of the log bound is genuinely open -- there is no extracted truth
chain for the log truths.

Neither is anything about a forged constants column: `constantsColumnsOfRoot`,
`suppliedColumn`, `committedColumn`, `constIndexLt`, `cutLe` and
`columnNonDegeneracy` are hypotheses of
`constants_forgery_forces_join_or_opening_off_bad_set` and appear nowhere in the
inventory. The last of them is FALSE for an honest column, so keeping it in the
inventory -- as the previous revision did -- silently conditioned every
conclusion on the run carrying a forgery.

`hdraw` and `hidx` are the Fiat--Shamir half (B): `DrawEncodesRun` at the actual
digests is a THEOREM, and so is the index-lane coordinate statement, but "the
actual draw is `jointProbability`-distributed" (respectively
`indexProbability`-distributed) is NOT, here or anywhere in the adopted tree.

### What is NOT concluded

Circuit truth (constraints vanishing on EXTRACTED tables is not satisfaction by a
real witness); WHIR/Merkle proximity; hash security of `hash`, `thash`, `khash`;
Rust / Yul / Solidity refinement; the two digest residues `circuitDigest` and
`circuitConfigDigest` that `ExplicitEngine.encodeConfig` does not encode; and the
Solidity-only reading of `ExplicitEngine.explicitDeployment`, which drops
everything the Rust entry point re-validates per call.

**AND JOINT SATISFIABILITY.** No accepting proof for the explicit engine is
exhibited anywhere, so nothing shows `hacc` and `AssemblyResidue` can hold
together; `explicit_good_draw_assembly` is a conditional shape. -/

/-- **THE DISCHARGED SIDE OF THE LEDGER.** Everything listed here follows from
ACCEPTANCE ALONE, which is exactly why none of it appears in
`AssemblyResidue`. Read together with the tables above, this is the sense in
which the inventory is exact: the fields are what is left after these are
removed, and every field that is left is consumed by
`explicit_good_draw_assembly`.

Conjunct by conjunct, all adopted: `ComposedEngine.composed_initial_is_derived`;
`ComposedEngine.composed_acceptance_envelope_and_shape`;
`ComposedEngine.composed_acceptance_bounds_degree_bits`;
`ConditionalSoundness.lane_length_of_shape`;
`GatePointZeroCheck.accepted_gate_point_width`;
`ConstantsProvenance.accepted_root_is_pinned` -- which is what CLOSES branch (C)
of the three-way constants attack rather than assuming it away;
`ComposedEngine.composed_actual_digest_draw_encodes_run`;
`ComposedEngine.composed_accepted_sampled_indices_absorb_used_claims`; and
`ExplicitEngine.accepted_gate_rows_are_the_decoded_length`, which also supplies
the `Gates.validateConfiguration` that `gate_lane_degree_of_extraction` needs.

The deployment disjunct `core c = core c₀ ∨ KhashCollision khash` is NOT here: it
is conjunct (4) of `explicit_good_draw_assembly`, because it consumes four fields
of the inventory rather than acceptance alone. -/
theorem residue_inventory_is_exact (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (truths : List (List Element))
    (hacc : Integrated.verify (engine gdec hash thash khash P c₀) gdec pin chain c p = .ok ()) :
    TranscriptProvenance.DerivedInitial thash (engine gdec hash thash khash P c₀) c p ∧
    Verifier.envelope c = true ∧ Verifier.shape pin c p = true ∧
    c.degreeBits ≤ 13 ∧
    (ConditionalSoundness.logLaneOf (engine gdec hash thash khash P c₀) c p truths).length
      = c.degreeBits ∧
    (ConditionalSoundness.gateLaneOf (engine gdec hash thash khash P c₀) c p truths).length
      = c.degreeBits ∧
    (TranscriptProvenance.gatePointColumn (engine gdec hash thash khash P c₀) c p).length
      = c.degreeBits ∧
    p.preprocessedRoot = pin.preprocessedRoot ∧
    JointChallengeSpace.DrawEncodesRun thash (engine gdec hash thash khash P c₀) c p truths truths
      (actualDigestDraw thash c p) ∧
    (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p).log.length = c.indexBits ∧
    (Verifier.derivedIndices (engine gdec hash thash khash P c₀) c p).gate.length = c.indexBits ∧
    (∃ gates, gdec c.gatesEncoding = some gates ∧ gates.length = c.gateRows ∧
      Gates.validateConfiguration (Integrated.gateConfig c) gates = some ()) := by
  obtain ⟨henv, hsh, hdb, -, -, hlogLen, hgateLen, hwidth, hroot⟩ :=
    explicit_accepted_run_facts gdec hash thash khash P c₀ pin chain c p truths hacc
  obtain ⟨hilog, higate, -, -⟩ :=
    explicit_index_lanes_are_draw_coordinates gdec hash thash khash P c₀ pin chain c p hacc
  exact ⟨explicit_initial_is_derived gdec hash thash khash P c₀ c p, henv, hsh, hdb, hlogLen,
    hgateLen, hwidth, hroot,
    explicit_actual_digest_draw_encodes_run gdec hash thash khash P c₀ pin chain c p truths truths
      hacc,
    hilog, higate,
    ExplicitEngine.accepted_gate_rows_are_the_decoded_length gdec hash thash khash P c₀ pin chain
      c p hacc⟩

/-- **THE JOINT-SPACE FIGURE AT THE ENVELOPE EXTREMES**, restated from
`AdaptiveAgreementFamily.combined_with_agreement_at_extremes`: at
`degreeBits = 13`, `quotientDegree = 8`, `numGateConstraints = 123` the
five-family bound is at most `2 ^ (-171)`.

`2^-171` IS NOT THE SYSTEM'S SOUNDNESS ERROR. It omits the WHIR/Merkle term,
which dominates; the deployed design point is around 100 bits, so quoting it as
the wire-v3 soundness error would be wrong by roughly seventy bits. -/
theorem joint_mass_at_the_envelope :
    ChallengeUnionBound.combinedBound 13 8 13 123 + ChallengeUnionBound.tauTerm 13
      ≤ (1 : ℚ) / 2 ^ 171 :=
  AdaptiveAgreementFamily.combined_with_agreement_at_extremes

/-- **THE INDEX-SPACE FIGURE AT THE ENVELOPE CAP.** `Verifier.envelope` caps
`c.indexBits` at 8, and at every admitted value the two index families together
cost at most `2 ^ (-187)`. Computed by exact rational arithmetic from
`ChallengeUnionBound.tau_term_explicit`; no `decide`, no `native_decide`, and no
tactic ever sees `Fintype.card Element`.

**THIS IS A SECOND MASS ON A SECOND SPACE AND IS NOT ADDED TO THE FIRST.** -/
theorem index_mass_at_the_envelope (bits : Nat) (h : bits ≤ 8) :
    2 * ChallengeUnionBound.tauTerm bits ≤ (1 : ℚ) / 2 ^ 187 := by
  interval_cases bits <;>
    rw [ChallengeUnionBound.tau_term_explicit] <;> norm_num [Arithmetic.modulus]

/-- The two envelope figures side by side, with the reason they are not one
number: they are masses of subsets of two DIFFERENT finite spaces under two
DIFFERENT explicit uniform laws, and no joint law over the outer-challenge block
and the constituent-index block is formalized anywhere in the adopted tree. -/
theorem assembly_masses_at_the_envelope (bits : Nat) (h : bits ≤ 8) :
    ChallengeUnionBound.combinedBound 13 8 13 123 + ChallengeUnionBound.tauTerm 13
        ≤ (1 : ℚ) / 2 ^ 171 ∧
      2 * ChallengeUnionBound.tauTerm bits ≤ (1 : ℚ) / 2 ^ 187 :=
  ⟨joint_mass_at_the_envelope, index_mass_at_the_envelope bits h⟩

end Audit.Wire3.SoundnessAssembly
