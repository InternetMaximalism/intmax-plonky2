import Audit.Wire3.ConstantsProvenance
import Audit.Wire3.InstalledIndexSampler
import Audit.Wire3.PublicInputHashBinding
import Audit.Wire3.CommitmentOrder
import Audit.Wire3.AttachedUnionBound
import Audit.Wire3.JointChallengeSpace

/-!
# Installing the concrete initial transcript and public-input hash

## The gap this module closes

Two `Verifier.Engine` fields are consumed at the very START of the protocol and
were still OBSERVATIONS on every installed engine of the adopted tree:

* `initialObservation : Config -> Statement -> Initial` (Verifier.lean:348),
  read through `Engine.initialTranscript` (Verifier.lean 359-360) by
  `Verifier.derivedRounds` (386-387), `Verifier.gateTerminal` (395-399) and
  `Verifier.verify` (417-425);
* `publicInputsHash : List Base -> List Base` (Verifier.lean:353), read by
  `Verifier.gateTerminal` (399) and `Integrated.gateResult` (Integrated.lean
  51-54).

Because `initialObservation` was abstract, the adopted
`TranscriptProvenance.DerivedInitial thash e c p` -- "this engine's initial
transcript IS the adopted `OuterInitial` derivation" -- had to be carried as a
HYPOTHESIS by every gate/challenge theorem downstream: `GateDerivedRejection`,
`AttachedUnionBound`, `JointChallengeSpace`, `CommitmentOrder`,
`ConstantsProvenance` and the nineteen restatements inside
`TranscriptProvenance` itself. Because `publicInputsHash` was abstract, the
adopted `PublicInputHashBinding` -- which already models the concrete Poseidon
`hash_no_pad` sponge -- had to carry `hsub : e.publicInputsHash = hashNoPad`.

`installedInitialEngine e gdec hash wp thash` installs BOTH. It is
`InstalledIndexSampler.installedSamplerEngine e gdec hash wp thash` (so the
composition chain is `Integrated.modelEngine` -> `InstalledWhirTail` ->
`InstalledIndexSampler` -> this) with

    initialObservation := fun c s => OuterInitial.toInitial (OuterInitial.derive thash c s)
    publicInputsHash   := PublicInputHashBinding.hashNoPad

Both right-hand sides are ADOPTED functions. Nothing is re-modelled here: the
derivation is the adopted `OuterInitial.derive` (the engine is literally the
adopted installer `OuterInitial.withInitial` composed with the adopted
`PublicInputHashBinding.withPublicInputsHash`, see
`installed_initial_is_sampler_of_with_initial`).

**WHAT IS NOT NEW HERE.** That `DerivedInitial` holds with no hypothesis of an
engine carrying the adopted initial installer is ALREADY an adopted theorem:
`TranscriptProvenance.withInitial_derived` (TranscriptProvenance.lean 190-192,
`rfl`, for EVERY engine `e`), with
`OuterInitial.engine_initial_is_same_statement` (OuterInitial.lean 431-433) as
its field-level form. Likewise a hypothesis-free concrete-hash gate terminal
already exists as
`PublicInputHashBinding.gate_terminal_of_with_public_inputs_hash`
(PublicInputHashBinding.lean 665-672), resting on
`with_public_inputs_hash_substitution` (635). No new transcript fact and no new
hash fact is claimed here: `installed_initial_is_derived` below IS
`withInitial_derived` instantiated at this engine, and its proof term says so
literally.

**WHAT IS NEW** is compositional, and is two things:

1. THE COMPOSITION. ONE engine carrying all EIGHT installed fields at once
   (`installed_fields`): `foldClaim`, `normEvaluation`, `eqEvaluation` and
   `gateEvaluation` from `Integrated.modelEngine`, `whirTail` from
   `InstalledWhirTail`, `sampleIndices` from `InstalledIndexSampler`, and the
   two installed here. `installed_initial_is_sampler_of_with_initial` proves by
   `rfl` that stacking the two adopted installers under the adopted sampler
   engine is exactly this engine, which is what lets the adopted unconditional
   facts about each installer hold SIMULTANEOUSLY of one engine.
2. THE DOWNSTREAM DISCHARGE. The 36 adopted `hderiv` sites and the
   `PublicInputHashBinding` `hsub` sites become unconditional FOR THIS ENGINE:
   eleven are restated below with `hderiv` (respectively `hsub`) DELETED and
   everything else verbatim, and the rest are discharged pointwise by passing
   `installed_initial_is_derived`.

**This module does NOT depend on `InstalledRoundCommit`,** which is being built
concurrently: the engine's `commitRound` is still `e.commitRound`, i.e. still an
observation. Composing this engine with a concrete `commitRound` is a LATER
step; every statement below that mentions `Verifier.derivedRounds` therefore
still ranges over whatever rounds the abstract `commitRound` produces.

## What the sources say, with citations

Snapshot of the reference worktree `/Users/andropov/repos/intmax-plonky2-lean-wire3`.

Initial transcript:

* `mle/src/verifier_v2.rs` 232-275 -- `PoseidonHash::hash_no_pad(&proof.public_inputs)`
  at 232, then `absorb_v2_statement_and_base_roots(...)` at 234;
  `mle/src/prover_v2.rs` 90-142 -- the twenty-two absorbed frames and the seven
  squeezes, in the order the adopted `OuterInitial.derive` models.
* `mle/contracts/src/MleVerifierV2.sol` 305 (`_deriveInitialTranscript` call),
  394-480 (its body); `mle/contracts/src/TranscriptV2.sol` `create`,
  `domainSeparate`, `absorbBytes`, `bindWhirIdentifiers`, `squeezeChallenge`
  219-234 and `squeezeExt3` 236-240.
* `mle/src/transcript_v2.rs` 43-53 (`absorb_frame` resets the counter), 98-107
  (`squeeze_challenge` hashes `CHALLENGE_PREFIX || state || counter_u64_le` and
  bumps the counter), 113-121 (`squeeze_ext3` is three consecutive squeezes).

The counter layout the adopted model already pins
(`TranscriptProvenance.derived_columns_at_source_counters`,
`CommitmentOrder.gate_challenge_counters`), all from the digest of frame 21:
`lambda 0, rho 3, kappa 6`, `log tau i` at `9 + 3i`, GATE ALPHA at
`9 + 3*degreeBits`, GATE TAU `i` at `12 + 3*degreeBits + 3i`. The three Merkle
roots sit at prefix positions 13 (preprocessed), 15 (witness) and 19
(norm-inverse) of the twenty-two-frame `CommitmentOrder.gateChallengeFrames`.

Public-input hash:

* `mle/contracts/src/MleVerifierV2.sol` 382-391 --
  `PoseidonPublicInputsHash.hashNoPad(proof.publicInputs)` feeding
  `Plonky2GateEvaluatorExt3.evalCombinedPrevalidated`;
  `mle/contracts/src/PoseidonPublicInputsHash.sol` 1-14 -- the library boundary.
* `mle/src/verifier_v2.rs` 232 and 427 -- the Rust side.

All of that is the adopted `PublicInputHashBinding` model. This module installs
it; it re-proves nothing about Poseidon.

The adopted model records two Rust/Solidity divergences on that boundary, and
they are NOT both merely inherited here. The 256-public-input cap
(`MAX_PUBLIC_INPUTS_V2`) is CLOSED for accepted proofs: `Verifier.shape` forces
`p.publicInputs.length = c.numPublicInputs` and `Verifier.envelope` forces
`c.numPublicInputs <= 256`, so on every accepting run the raw Solidity-side
`PublicInputHashBinding.rawPublicInputsHash` returns exactly the typed sponge
this engine computes -- proved as `accepted_public_inputs_within_solidity_cap`,
not merely remarked. The canonical-range scans remain a Solidity-side guard
with no typed counterpart: `Verifier.Base` values are in range by construction,
so nothing here says anything about a raw word outside the field.

## Installed vs still-observed AFTER this module

INSTALLED (concrete, executable): `foldClaim`, `normEvaluation`, `eqEvaluation`,
`gateEvaluation` (from `Integrated.modelEngine`), `whirTail` (from
`InstalledWhirTail`), `sampleIndices` (from `InstalledIndexSampler`), and NEW
HERE `initialObservation` (hence `initialTranscript`) and `publicInputsHash`.

STILL OBSERVATIONS, unchanged and opaque, carried through from `e`:

1. `commitRound` -- the coupled-round transcript step. Being installed
   concurrently in a separate candidate module; NOT depended on here.
2. `parseWhir` -- the WHIR transcript parser.
3. `configurationHash` -- the config digest; its provenance from the config/VK
   frames is not modelled anywhere in the adopted tree.
4. `deploymentValid` -- the deployment predicate.

## What this does NOT discharge

The PROVER-SIDE challenge equality `hch : pr.challenges = logChallenges thash c p`
(`TranscriptProvenance` 411, 439, 452, 473, 574, 593, 754) is NOT discharged by
installing the verifier's derivation, and cannot be. `DerivedInitial` is about
the VERIFIER engine's own hook; `hch` says the PROVER's `NormDenseRound.Prepared`
record was built from those same seven challenges. Nothing in this model connects
a prover-side record to the verifier's transcript, so `hch` remains a hypothesis
of every theorem that had it. Likewise `hpt` / `GateChainResidue`, the
`CommittedTables` extraction join, `HonestNormProver.zeroSum`,
`GateChainHypotheses.grid` and `HonestOpenings.opened` are untouched.

## Manual-model caveat and boundaries

`thash` (transcript) and `hash` (WHIR/Merkle) are ARBITRARY DETERMINISTIC
FUNCTIONS. In the source both are Keccak; nothing in the Lean model ties them or
assumes anything about either. No injectivity, no collision resistance, no
uniformity, no unpredictability, no random-oracle property, no Fiat--Shamir
soundness, no WHIR/PCS soundness, no Rust/Yul/Solidity refinement, no gas or
exception-ordering claim. What is installed is an ORDER-AND-PLUMBING IDENTITY:
the engine's initial hook computes the frames and squeezes the sources compute,
in that order, and its gate hash is the Poseidon sponge the sources call. That
is half (A) of the Fiat--Shamir reading only.

**HALF (B) IS UNFORMALIZED**, here and anywhere in the adopted tree: that the
squeezes are uniform and independent of the absorbed prefix is a hash
assumption, and the adopted
`CommitmentOrder.separation_fails_for_a_deterministic_hash` REFUTES even its
weaker deterministic shadow for a general deterministic hash. Only with (B) does
an avoidance hypothesis (`hgood`, `hTau`, `hAlpha`) become a probability event.

`JointChallengeSpace.DrawEncodesRun` is a COORDINATE STATEMENT -- it says the
challenges the run drew ARE the coordinatewise reductions of the joint sample
point; it is not a distributional claim and does not supply (B).

No figure restated below is the deployed system's soundness error. The
`combinedBound` envelope excludes the dominant WHIR/Merkle term. The wire-v3
WHIR profile this tree models is the approximately 100-bit design point; nothing
here is a security level, and in particular nothing here says "125".
-/

namespace Audit.Wire3.InstalledInitialTranscript

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The two concrete field values -/

abbrev VkParams := InstalledIndexSampler.VkParams

/-- **THE CONCRETE INITIAL TRANSCRIPT.** The adopted `OuterInitial` derivation
on this proof's statement, presented as a `Verifier.Initial` -- literally the
right-hand side of the adopted `TranscriptProvenance.DerivedInitial`, and
literally what the adopted installer `OuterInitial.withInitial` puts in the
engine. It has the shape `Config -> Proof -> Verifier.Initial` because that is
what `Engine.initialTranscript` (Verifier.lean 359-360) exposes. -/
def concreteInitialTranscript (thash : Transcript.Hash) :
    Verifier.Config → Verifier.Proof → Verifier.Initial :=
  fun c p => OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p))

/-- The same object at the FIELD's own type: `Engine.initialObservation`
(Verifier.lean:348) takes a `Verifier.Statement`, not a `Verifier.Proof`. -/
def concreteInitialObservation (thash : Transcript.Hash) :
    Verifier.Config → Verifier.Statement → Verifier.Initial :=
  fun c s => OuterInitial.toInitial (OuterInitial.derive thash c s)

/-- The concrete transcript is the adopted `TranscriptProvenance.derived` object
in `Verifier.Initial` clothing. -/
theorem concrete_initial_is_the_adopted_derivation (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) :
    concreteInitialTranscript thash c p =
      OuterInitial.toInitial (TranscriptProvenance.derived thash c p) := rfl

theorem concrete_observation_at_statement (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) :
    concreteInitialObservation thash c (Verifier.statement p) =
      concreteInitialTranscript thash c p := rfl

/-- **THE CONCRETE PUBLIC-INPUT HASH.** The adopted `PublicInputHashBinding`
Poseidon `hash_no_pad` sponge; no property of Poseidon is claimed or used. -/
def concretePublicInputsHash : List Verifier.Base → List Verifier.Base :=
  PublicInputHashBinding.hashNoPad

theorem concrete_public_inputs_hash_is_the_adopted_sponge :
    concretePublicInputsHash = PublicInputHashBinding.hashNoPad := rfl

/-! ## 2. The engine -/

/-- **THE ENGINE OF THIS MODULE.** The adopted
`InstalledIndexSampler.installedSamplerEngine` -- itself
`Integrated.modelEngine`, then `InstalledWhirTail.installedEngine`, then the
concrete constituent-index sampler -- with the initial transcript and the
public-input hash installed. `hash` is the WHIR/Merkle hash, `thash` the outer
transcript hash; both are arbitrary deterministic functions and nothing in the
model ties them. `commitRound` is NOT installed here. -/
def installedInitialEngine (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) : Verifier.Engine :=
  { InstalledIndexSampler.installedSamplerEngine e gdec hash wp thash with
    initialObservation := concreteInitialObservation thash,
    publicInputsHash := concretePublicInputsHash }

/-- Installing these two fields is the same as building the adopted sampler
engine on top of the two adopted installers, so every adopted theorem quantified
over an arbitrary engine applies with `e` replaced by that wrapper. -/
theorem installed_initial_is_sampler_of_with_initial (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) :
    installedInitialEngine e gdec hash wp thash =
      InstalledIndexSampler.installedSamplerEngine
        (PublicInputHashBinding.withPublicInputsHash (OuterInitial.withInitial thash e))
        gdec hash wp thash := rfl

/-- The engine is its own `Integrated.modelEngine`, so the adopted glue that
speaks of `modelEngine` applies to it unchanged. -/
theorem installed_initial_is_its_own_model_engine (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) :
    Integrated.modelEngine (installedInitialEngine e gdec hash wp thash) gdec =
      installedInitialEngine e gdec hash wp thash := rfl

/-- The complete installed-field list after this module: EIGHT fields, all
concrete, on a single engine. This simultaneity is the compositional content of
the module; each individual field was installed by an adopted installer. -/
theorem installed_fields (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) :
    (installedInitialEngine e gdec hash wp thash).initialObservation =
        concreteInitialObservation thash ∧
    (installedInitialEngine e gdec hash wp thash).publicInputsHash = concretePublicInputsHash ∧
    (installedInitialEngine e gdec hash wp thash).sampleIndices =
        InstalledIndexSampler.concreteSampleIndices thash ∧
    (installedInitialEngine e gdec hash wp thash).whirTail =
        InstalledWhirTail.installedTail hash wp ∧
    (installedInitialEngine e gdec hash wp thash).foldClaim = Connections.packedFold ∧
    (installedInitialEngine e gdec hash wp thash).normEvaluation = Norm.normEvaluation ∧
    (installedInitialEngine e gdec hash wp thash).eqEvaluation = Norm.eqEvaluation ∧
    (installedInitialEngine e gdec hash wp thash).gateEvaluation =
        fun c wires constants publicHash alpha =>
          (Integrated.evaluateGate gdec c wires constants publicHash alpha).getD Verifier.zero :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (e) **THE REMAINING OBSERVATIONS**, verbatim: the four fields this module
does not touch are still `e`'s own opaque hooks. `commitRound` is the one being
installed concurrently; `parseWhir`, `configurationHash` and `deploymentValid`
are not addressed by any candidate module. -/
theorem remaining_observations (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) :
    (installedInitialEngine e gdec hash wp thash).commitRound = e.commitRound ∧
    (installedInitialEngine e gdec hash wp thash).parseWhir = e.parseWhir ∧
    (installedInitialEngine e gdec hash wp thash).configurationHash = e.configurationHash ∧
    (installedInitialEngine e gdec hash wp thash).deploymentValid = e.deploymentValid :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The engine's `initialTranscript` (the derived reader, Verifier.lean 359-360)
IS the concrete derivation. -/
theorem installed_initial_transcript_is_concrete (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (vc : Verifier.Config) (p : Verifier.Proof) :
    (installedInitialEngine e gdec hash wp thash).initialTranscript vc p =
      concreteInitialTranscript thash vc p := rfl

/-! ## 3. (a) `DerivedInitial`, for THIS engine -/

/-- (a) The premise every downstream gate and challenge theorem carries --
`TranscriptProvenance.DerivedInitial` -- holds for this engine for EVERY
configuration and EVERY proof, with no hypothesis.

**PRIOR ART, NOT A NEW FACT.** This is the adopted
`TranscriptProvenance.withInitial_derived` (TranscriptProvenance.lean 190-192),
which is already unconditional and already `rfl` for EVERY engine wrapped by
`OuterInitial.withInitial`; `OuterInitial.engine_initial_is_same_statement`
(OuterInitial.lean 431-433) is the same fact at the field. The proof below is
literally that adopted theorem applied to
`PublicInputHashBinding.withPublicInputsHash e`, so the provenance is visible
rather than hidden behind `rfl`. What this module adds is that the SAME engine
also carries the concrete public-input hash, WHIR tail, index sampler and gate
evaluation (`installed_fields`), and that the downstream restatements below can
therefore drop `hderiv` and `hsub` at once. -/
theorem installed_initial_is_derived (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash)
    (vc : Verifier.Config) (p : Verifier.Proof) :
    TranscriptProvenance.DerivedInitial thash (installedInitialEngine e gdec hash wp thash) vc p :=
  TranscriptProvenance.withInitial_derived thash
    (PublicInputHashBinding.withPublicInputsHash e) vc p

/-- The seven challenges, the two derived columns and the gate alpha of the
adopted `TranscriptProvenance` are now unconditional facts about this engine. -/
theorem installed_initial_columns (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash)
    (vc : Verifier.Config) (p : Verifier.Proof) :
    Norm.challengesFromInitial
        ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p) =
      TranscriptProvenance.logChallenges thash vc p ∧
    NormDenseRound.values (TranscriptProvenance.gateTauColumn thash vc p) =
      ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateTau ∧
    (TranscriptProvenance.gateAlphaElement thash vc p).toVerifier =
      ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateAlpha ∧
    ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).logChallenges.length
      = 7 ∧
    ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).logTau.length
      = vc.degreeBits ∧
    ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateTau.length
      = vc.degreeBits :=
  ⟨TranscriptProvenance.challenges_from_initial_is_derived thash _ vc p
      (installed_initial_is_derived e gdec hash wp thash vc p),
   TranscriptProvenance.values_gate_tau_column thash _ vc p
      (installed_initial_is_derived e gdec hash wp thash vc p),
   TranscriptProvenance.gate_alpha_element_matches thash _ vc p
      (installed_initial_is_derived e gdec hash wp thash vc p),
   TranscriptProvenance.derived_seven_challenges thash _ vc p
      (installed_initial_is_derived e gdec hash wp thash vc p),
   TranscriptProvenance.derived_log_tau_length thash _ vc p
      (installed_initial_is_derived e gdec hash wp thash vc p),
   TranscriptProvenance.derived_gate_tau_length thash _ vc p
      (installed_initial_is_derived e gdec hash wp thash vc p)⟩

/-! ## 4. (c) The public-input hash -/

/-- (c) The engine's `publicInputsHash` IS the adopted concrete Poseidon
`hash_no_pad` sponge of `PublicInputHashBinding`, as a function, not merely
pointwise.

**PRIOR ART, NOT A NEW FACT.** The substitution itself is the adopted
`PublicInputHashBinding.with_public_inputs_hash_substitution`
(PublicInputHashBinding.lean 635), and the adopted tree ALREADY has a
hypothesis-free concrete-hash gate terminal built on it,
`PublicInputHashBinding.gate_terminal_of_with_public_inputs_hash` (665-672).
What is new below is only that the same engine simultaneously carries the
installed initial transcript, so `hsub` and `hderiv` disappear together. -/
theorem installed_public_input_hash_is_concrete (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) :
    (installedInitialEngine e gdec hash wp thash).publicInputsHash =
      PublicInputHashBinding.hashNoPad := rfl

/-- (c) The four-limb length that `Integrated.evaluateGate` (Integrated.lean:40)
and `Plonky2GateEvaluatorExt3.sol` 91-93 demand, with the adopted
`PublicInputHashBinding.hash_length_discharged`'s `hsub` hypothesis GONE. -/
theorem installed_public_input_hash_length (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (p : Verifier.Proof) :
    ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs).length = 4 :=
  PublicInputHashBinding.hash_length_discharged (installedInitialEngine e gdec hash wp thash) p rfl

/-- (c) The adopted
`PublicInputHashBinding.bound_terminal_is_engine_gate_terminal_concrete_hash`
with its `hsub : e.publicInputsHash = hashNoPad` hypothesis REMOVED. Every other
hypothesis (the gate decode, the row count, the configuration validation, the
cell/claim correspondence, the two widths, the alpha and eq cells) is verbatim
the adopted one; this changes nothing about them. -/
theorem installed_bound_terminal_is_engine_gate_terminal_concrete_hash
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (decode : Integrated.DecodeGates) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (k : GateTerminalBinding.Cells)
    (alpha : GoldilocksExt3Field.Element)
    (hd : decode c.gatesEncoding = some gates) (hr : gates.length = c.gateRows)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hk : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p))
    (hw : k.wires.length = c.numWires) (hc : k.constants.length = c.numConstants)
    (halpha : alpha.toVerifier =
      ((installedInitialEngine e gdec hash wp thash).initialTranscript c p).gateAlpha)
    (heq : k.eq.toVerifier =
      Norm.eqEvaluation
        ((installedInitialEngine e gdec hash wp thash).initialTranscript c p).gateTau
        (Verifier.derivedRounds (installedInitialEngine e gdec hash wp thash) c p).gatePoint) :
    ∃ gate,
      Integrated.gateResult
        (Integrated.modelEngine (installedInitialEngine e gdec hash wp thash) decode)
        decode c p = some gate ∧
      GateTerminalBinding.boundTerminal (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction
          (PublicInputHashBinding.hashNoPad p.publicInputs)) alpha k =
        some (Verifier.mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal
        (Integrated.modelEngine (installedInitialEngine e gdec hash wp thash) decode) c p =
        Verifier.mul k.eq.toVerifier gate :=
  PublicInputHashBinding.bound_terminal_is_engine_gate_terminal_concrete_hash
    (installedInitialEngine e gdec hash wp thash) decode c p gates k alpha rfl hd hr hv hk hw hc
    halpha heq

/-- (c) The adopted `PublicInputHashBinding.gate_terminal_uses_concrete_hash`
with `hsub` REMOVED: this engine's gate terminal (Verifier.lean 395-399)
evaluates the gate table at the actual Poseidon digest of the proof's public
inputs, and at its own derived gate tau and gate alpha. -/
theorem installed_gate_terminal_uses_concrete_hash
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (decode : Integrated.DecodeGates) (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.gateTerminal
        (Integrated.modelEngine (installedInitialEngine e gdec hash wp thash) decode) c p =
      Verifier.mul
        (Norm.eqEvaluation
          ((installedInitialEngine e gdec hash wp thash).initialTranscript c p).gateTau
          (Verifier.derivedRounds (installedInitialEngine e gdec hash wp thash) c p).gatePoint)
        ((Integrated.evaluateGate decode c p.used.gateWitness
          (p.used.gatePreprocessed.take c.numConstants)
          (PublicInputHashBinding.hashNoPad p.publicInputs)
          ((installedInitialEngine e gdec hash wp thash).initialTranscript c p).gateAlpha).getD
            Verifier.zero) :=
  PublicInputHashBinding.gate_terminal_uses_concrete_hash
    (installedInitialEngine e gdec hash wp thash) decode c p rfl

/-- (c) **THE 256-CAP DIVERGENCE IS CLOSED ON ACCEPTED PROOFS.** The adopted
`PublicInputHashBinding` records that the Solidity side rejects more than
`MAX_PUBLIC_INPUTS_V2 = 256` public inputs while the typed sponge is total. For
an ACCEPTING `Integrated.verify` run on this engine that gap cannot be reached:
`Verifier.shape` forces `p.publicInputs.length = c.numPublicInputs` and
`Verifier.envelope` forces `c.numPublicInputs <= 256`, so the raw Solidity-side
`rawPublicInputsHash` is defined and equals the digest this engine computes.

This says nothing about the OTHER recorded divergence, the canonical-range
scans: `Verifier.Base` values are in range by construction, so the typed path
has no counterpart to them, and nothing here claims a raw word outside the
field behaves in any particular way. -/
theorem accepted_public_inputs_within_solidity_cap (e : Verifier.Engine)
    (gdec decode : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (installedInitialEngine e gdec hash wp thash) decode pin chain c p
      = .ok ()) :
    p.publicInputs.length ≤ PublicInputHashBinding.maxPublicInputs ∧
    PublicInputHashBinding.rawPublicInputsHash (p.publicInputs.map Fin.val) =
      some ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs) := by
  have hv : Verifier.verify
      (Integrated.modelEngine (installedInitialEngine e gdec hash wp thash) decode)
      pin chain c p = .ok () := by
    simp only [Integrated.verify] at hacc
    split at hacc
    · cases hacc
    · split at hacc
      · cases hacc
      · exact hacc
  obtain ⟨-, -, henv, -, hshape, -⟩ := Verifier.verify_success_checks _ pin chain c p hv
  simp only [Verifier.envelope, decide_eq_true_eq] at henv
  simp only [Verifier.shape, decide_eq_true_eq] at hshape
  have hlen : p.publicInputs.length ≤ 256 := by
    rw [hshape.2.2.2.1]; exact henv.2.2.2.2.2.2.1
  exact ⟨hlen, PublicInputHashBinding.raw_hash_of_typed p.publicInputs hlen⟩

/-! ## 5. (b) The headline gate theorems, restated with `hderiv` deleted

Each statement below is the adopted theorem with the engine specialised to
`installedInitialEngine e gdec hash wp thash` and the single hypothesis
`hderiv : DerivedInitial thash e vc p` DELETED. NOTHING ELSE IS CHANGED: the
assumption bundles `D`, `A`, the acceptance hypothesis, the bad-event-free
hypotheses, the tau/alpha avoidance hypotheses, the row conditions and the
conclusions are all verbatim. In particular the avoidance hypotheses remain
HYPOTHESES about the particular run; turning them into probability events is
half (B), which this audit does not prove.

One qualification on "verbatim": `hacc` is acceptance BY THIS ENGINE, i.e. by
the concrete index sampler, WHIR tail and initial derivation, which is a
STRICTLY STRONGER premise than acceptance by an arbitrary engine -- a proof an
abstract engine accepts need not be accepted here. `commitRound` and
`parseWhir` are still abstract, so `hacc` is not yet acceptance by the deployed
verifier either. -/

/-- (b) The adopted
`GateDerivedRejection.derived_selected_gate_constraints_vanish` on this engine,
with `hderiv` GONE.

THE STRONGEST GATE STATEMENT of the adopted tree: an accepting
`Integrated.verify` run, the reduced transcript-derived gate assumption list,
gate-lane `BadEventFree`, the derived gate tau outside its zero-check bad set
and the derived gate alpha outside this row's alpha bad set together force EVERY
constraint of the gate selected at that row to be zero, and assert that the
gate's evaluator succeeds there. No challenge is universally quantified: tau and
alpha are the values the derivation produces -- and now they are the values THIS
ENGINE actually observes, by construction rather than by assumption. -/
theorem installed_derived_selected_gate_constraints_vanish
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (decode : Integrated.DecodeGates) (vc : Verifier.Config) (p : Verifier.Proof)
    (pre post : List Gates.GateInfo) (g : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (x : GoldilocksExt3Field.Element)
    (k : GateTerminalBinding.Cells) (gateTruths : List (List GoldilocksExt3Field.Element))
    (pin : Verifier.Pinned) (chain : Nat)
    (D : GateDerivedRejection.DerivedGateAssumptions thash
      (installedInitialEngine e gdec hash wp thash) decode vc p (pre ++ g :: post)
      s0 sLast x k gateTruths)
    (hacc : Integrated.verify (installedInitialEngine e gdec hash wp thash) decode pin chain vc p
      = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ g :: post)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash vc p) s0)
      (ConditionalSoundness.gateLaneOf (installedInitialEngine e gdec hash wp thash) vc p
        gateTruths))
    (hgoodTau : GateDerivedRejection.GoodDerivedTau thash vc p
      (ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) (pre ++ g :: post)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash vc p) s0.tables))
    (i : Nat) (hi : i < 2 ^ vc.degreeBits) (coeffs : List GoldilocksExt3Field.Element)
    (hcoeffs : AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) (pre ++ g :: post)
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (GateTerminalBinding.publicHashFunction
        ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
      = some coeffs)
    (hgoodAlpha : GateDerivedRejection.GoodDerivedAlpha thash vc p coeffs)
    (hpre : ∀ g' ∈ pre,
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero)
    (hpost : ∀ g' ∈ post,
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero)
    (hactive :
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero) :
    ∃ terms, GatesComplete.evaluateUnfiltered g (AlphaZeroCheck.rowWires s0.tables i)
        (AlphaZeroCheck.rowConstants s0.tables i)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (Integrated.gateConfig vc).numSelectors = some terms ∧
      ∀ y ∈ terms, y = Verifier.zero :=
  GateDerivedRejection.derived_selected_gate_constraints_vanish thash pin chain
    (installed_initial_is_derived e gdec hash wp thash vc p) D hacc hfree hgoodTau i hi coeffs
    hcoeffs hgoodAlpha hpre hpost hactive

/-- (b) The adopted `AttachedUnionBound.attached_seam` on this engine, with
`hderiv` GONE.

THE SEAM: the deterministic half (every selected gate constraint vanishes at
every Boolean row) AND the counting half (`failure` plus the attached tau mass
plus the attached alpha mass is at most `combinedBound`), simultaneously.

**THE SECOND CONJUNCT IS A SUM OF THREE MASSES ON THREE DIFFERENT EXPLICIT
FINITE SPACES, NOT THE MASS OF THE COMPLEMENT OF THE FIRST**, and reading those
masses as probabilities of the real transcript is half (B), a hash assumption
this audit does not prove. `combinedBound` EXCLUDES the dominant WHIR/Merkle
term and IS NOT THE SYSTEM'S SOUNDNESS ERROR. -/
theorem installed_attached_seam
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (decode : Integrated.DecodeGates) (vc : Verifier.Config) (p : Verifier.Proof)
    (pre post : List Gates.GateInfo) (g : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : GoldilocksExt3Field.Element)
    (k : GateTerminalBinding.Cells) (gateTruths : List (List GoldilocksExt3Field.Element))
    (t tLast : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (constants extra : List Verifier.Ext3) (xn : GoldilocksExt3Field.Element)
    (logTruths gateCompareRounds : List (List GoldilocksExt3Field.Element))
    (gateCompare : GoldilocksExt3Field.Element) (fixedness : Prop)
    (law : Finset GoldilocksExt3Field.Element → ℚ) (failure : ℚ)
    (pin : Verifier.Pinned) (chain : Nat)
    (D : GateDerivedRejection.DerivedGateAssumptions thash
      (installedInitialEngine e gdec hash wp thash) decode vc p (pre ++ g :: post) s0
      sLast xg k gateTruths)
    (A : ConditionalSoundness.Assumptions (installedInitialEngine e gdec hash wp thash) decode vc p
      t tLast pr constants extra xn logTruths gateCompareRounds gateCompare fixedness law failure)
    (hacc : Integrated.verify (installedInitialEngine e gdec hash wp thash) decode pin chain vc p
      = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ g :: post)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash vc p) s0)
      (ConditionalSoundness.gateLaneOf (installedInitialEngine e gdec hash wp thash) vc p
        gateTruths))
    (hTau : AttachedUnionBound.attachedTauTuple thash vc p ∉
      AttachedUnionBound.attachedTauBadSet thash (installedInitialEngine e gdec hash wp thash)
        vc p (pre ++ g :: post) s0)
    (hAlpha : TranscriptProvenance.gateAlphaElement thash vc p ∉
      AttachedUnionBound.attachedAlphaUnion (installedInitialEngine e gdec hash wp thash)
        vc p (pre ++ g :: post) s0) :
    (∀ i, i < 2 ^ vc.degreeBits →
        (∀ g' ∈ pre,
          GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero) →
        (∀ g' ∈ post,
          GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero) →
        GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero →
        ∃ terms, GatesComplete.evaluateUnfiltered g (AlphaZeroCheck.rowWires s0.tables i)
            (AlphaZeroCheck.rowConstants s0.tables i)
            (GateTerminalBinding.publicHashFunction
              ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
            (Integrated.gateConfig vc).numSelectors = some terms ∧
          ∀ y ∈ terms, y = Verifier.zero)
      ∧ failure
          + ChallengeUnionBound.uniformProductProbability vc.degreeBits
              (AttachedUnionBound.attachedTauBadSet thash
                (installedInitialEngine e gdec hash wp thash) vc p (pre ++ g :: post) s0)
          + OuterChallenge.uniformTupleProbability
              (AttachedUnionBound.attachedAlphaUnion (installedInitialEngine e gdec hash wp thash)
                vc p (pre ++ g :: post) s0)
        ≤ ChallengeUnionBound.combinedBound vc.degreeBits vc.quotientDegree vc.degreeBits
            vc.numGateConstraints :=
  AttachedUnionBound.attached_seam thash pin chain
    (installed_initial_is_derived e gdec hash wp thash vc p) D A hacc hfree hTau hAlpha

/-- (b) The adopted
`JointChallengeSpace.composed_gate_constraints_vanish_on_the_joint_space` on this
engine, with `hderiv` GONE. `U : DrawEncodesRun` stays: it is a COORDINATE
statement identifying the run's challenges with the joint point's coordinates,
not a distributional claim, and installing the verifier's derivation does not
supply it. The mass figure excludes the dominant WHIR/Merkle term and is not the
system's soundness error; the deployed design point is around 100 bits. -/
theorem installed_composed_gate_constraints_vanish_on_the_joint_space
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (pin : Verifier.Pinned) (chain : Nat)
    (decode : Integrated.DecodeGates) (vc : Verifier.Config)
    (p : Verifier.Proof) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (x : GoldilocksExt3Field.Element)
    (cells : GateTerminalBinding.Cells)
    (logTruths gateTruths : List (List GoldilocksExt3Field.Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List GoldilocksExt3Field.Element) (row : Nat)
    (draw : JointChallengeSpace.JointSpace vc.degreeBits)
    (D : GateDerivedRejection.DerivedGateAssumptions thash
      (installedInitialEngine e gdec hash wp thash) decode vc p (pre ++ gate :: post)
      s0 sLast x cells gateTruths)
    (hacc : Integrated.verify (installedInitialEngine e gdec hash wp thash) decode pin chain vc p
      = .ok ())
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf
        (installedInitialEngine e gdec hash wp thash) vc p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf
        (installedInitialEngine e gdec hash wp thash) vc p gateTruths,
      r.message.length ≤ vc.quotientDegree + 2 ∧ r.truth.length ≤ vc.quotientDegree + 2)
    (hcoeffs : ∀ i, i < 2 ^ vc.degreeBits →
      AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) (pre ++ gate :: post)
        (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
          = some (coeffsOf i))
    (hclen : ∀ i, i < 2 ^ vc.degreeBits → (coeffsOf i).length ≤ vc.numGateConstraints)
    (hrow : row < 2 ^ vc.degreeBits)
    (hpre : ∀ h ∈ pre,
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) h s0.tables row = Verifier.zero)
    (hpost : ∀ h ∈ post,
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) h s0.tables row = Verifier.zero)
    (hactive : GateRejectionPower.rowFilter (Integrated.gateConfig vc) gate s0.tables row
      ≠ Verifier.zero)
    (U : JointChallengeSpace.DrawEncodesRun thash (installedInitialEngine e gdec hash wp thash)
      vc p logTruths gateTruths draw) :
    1 - ChallengeUnionBound.combinedBound vc.degreeBits vc.quotientDegree vc.degreeBits
          vc.numGateConstraints
        ≤ JointChallengeSpace.jointProbability vc.degreeBits
            (JointChallengeSpace.goodEvent vc.degreeBits
              (JointChallengeSpace.runBadEvent thash (installedInitialEngine e gdec hash wp thash)
                vc p (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf))
      ∧ (draw ∉ JointChallengeSpace.runBadEvent thash
            (installedInitialEngine e gdec hash wp thash) vc p (pre ++ gate :: post) s0
            logTruths gateTruths t pr coeffsOf →
          ∃ terms, GatesComplete.evaluateUnfiltered gate (AlphaZeroCheck.rowWires s0.tables row)
              (AlphaZeroCheck.rowConstants s0.tables row)
              (GateTerminalBinding.publicHashFunction
                ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
              (Integrated.gateConfig vc).numSelectors = some terms ∧
            ∀ y ∈ terms, y = Verifier.zero) :=
  JointChallengeSpace.composed_gate_constraints_vanish_on_the_joint_space thash pin chain
    (installedInitialEngine e gdec hash wp thash) decode vc p pre post gate s0 sLast x cells
    logTruths gateTruths t pr coeffsOf row draw
    (installed_initial_is_derived e gdec hash wp thash vc p) D hacc hlogDeg hgateDeg hcoeffs hclen
    hrow hpre hpost hactive U

/-- (b) The adopted `GateDerivedRejection.derived_gate_slots_vanish` on this
engine, with `hderiv` GONE: the per-slot form of the statement above, for an
arbitrary gate list rather than a split one. -/
theorem installed_derived_gate_slots_vanish
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (decode : Integrated.DecodeGates) (vc : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (x : GoldilocksExt3Field.Element)
    (k : GateTerminalBinding.Cells) (gateTruths : List (List GoldilocksExt3Field.Element))
    (pin : Verifier.Pinned) (chain : Nat)
    (D : GateDerivedRejection.DerivedGateAssumptions thash
      (installedInitialEngine e gdec hash wp thash) decode vc p gates s0 sLast x k gateTruths)
    (hacc : Integrated.verify (installedInitialEngine e gdec hash wp thash) decode pin chain vc p
      = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash vc p) s0)
      (ConditionalSoundness.gateLaneOf (installedInitialEngine e gdec hash wp thash) vc p
        gateTruths))
    (hgoodTau : GateDerivedRejection.GoodDerivedTau thash vc p
      (ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) gates
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash vc p) s0.tables))
    (i : Nat) (hi : i < 2 ^ vc.degreeBits) (coeffs : List GoldilocksExt3Field.Element)
    (hcoeffs : AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) gates
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (GateTerminalBinding.publicHashFunction
        ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
      = some coeffs)
    (hgoodAlpha : GateDerivedRejection.GoodDerivedAlpha thash vc p coeffs) :
    ∀ j, j < vc.numGateConstraints →
      AlphaZeroCheck.slotValue (Integrated.gateConfig vc) gates
        (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs)) j = 0 :=
  GateDerivedRejection.derived_gate_slots_vanish thash pin chain
    (installed_initial_is_derived e gdec hash wp thash vc p) D hacc hfree hgoodTau i hi coeffs
    hcoeffs hgoodAlpha

/-- (b) The adopted
`AttachedUnionBound.attached_all_rows_selected_constraints_vanish` on this
engine, with `hderiv` GONE: the deterministic half of the seam at every row. -/
theorem installed_attached_all_rows_selected_constraints_vanish
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (decode : Integrated.DecodeGates) (vc : Verifier.Config) (p : Verifier.Proof)
    (pre post : List Gates.GateInfo) (g : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : GoldilocksExt3Field.Element)
    (k : GateTerminalBinding.Cells) (gateTruths : List (List GoldilocksExt3Field.Element))
    (pin : Verifier.Pinned) (chain : Nat)
    (D : GateDerivedRejection.DerivedGateAssumptions thash
      (installedInitialEngine e gdec hash wp thash) decode vc p (pre ++ g :: post) s0
      sLast xg k gateTruths)
    (hacc : Integrated.verify (installedInitialEngine e gdec hash wp thash) decode pin chain vc p
      = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ g :: post)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash vc p) s0)
      (ConditionalSoundness.gateLaneOf (installedInitialEngine e gdec hash wp thash) vc p
        gateTruths))
    (hTau : AttachedUnionBound.attachedTauTuple thash vc p ∉
      AttachedUnionBound.attachedTauBadSet thash (installedInitialEngine e gdec hash wp thash)
        vc p (pre ++ g :: post) s0)
    (hAlpha : TranscriptProvenance.gateAlphaElement thash vc p ∉
      AttachedUnionBound.attachedAlphaUnion (installedInitialEngine e gdec hash wp thash)
        vc p (pre ++ g :: post) s0) :
    ∀ i, i < 2 ^ vc.degreeBits →
      (∀ g' ∈ pre,
        GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero) →
      (∀ g' ∈ post,
        GateRejectionPower.rowFilter (Integrated.gateConfig vc) g' s0.tables i = Verifier.zero) →
      GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero →
      ∃ terms, GatesComplete.evaluateUnfiltered g (AlphaZeroCheck.rowWires s0.tables i)
          (AlphaZeroCheck.rowConstants s0.tables i)
          (GateTerminalBinding.publicHashFunction
            ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
          (Integrated.gateConfig vc).numSelectors = some terms ∧
        ∀ y ∈ terms, y = Verifier.zero :=
  AttachedUnionBound.attached_all_rows_selected_constraints_vanish thash pin chain
    (installed_initial_is_derived e gdec hash wp thash vc p) D hacc hfree hTau hAlpha

/-- (b) The adopted
`ConstantsProvenance.provenanced_selected_gate_constraints_vanish` on this
engine, with `hderiv` GONE. The selector conditions are read off the DEPLOYED
constants (`pinnedConstantsTables`), and the extraction residue
`hident : SuppliedConstantsAreCommitted` stays a visible hypothesis; nothing
here discharges or weakens it. -/
theorem installed_provenanced_selected_gate_constraints_vanish
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (decode : Integrated.DecodeGates) (vc : Verifier.Config) (p : Verifier.Proof)
    (pre post : List Gates.GateInfo) (g : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (x : GoldilocksExt3Field.Element)
    (k : GateTerminalBinding.Cells) (gateTruths : List (List GoldilocksExt3Field.Element))
    (pin : Verifier.Pinned) (chain : Nat)
    (committedBy : Verifier.Root → List (List GoldilocksExt3Field.Element))
    (D : GateDerivedRejection.DerivedGateAssumptions thash
      (installedInitialEngine e gdec hash wp thash) decode vc p (pre ++ g :: post) s0
      sLast x k gateTruths)
    (hacc : Integrated.verify (installedInitialEngine e gdec hash wp thash) decode pin chain vc p
      = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ g :: post)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash vc p) s0)
      (ConditionalSoundness.gateLaneOf (installedInitialEngine e gdec hash wp thash) vc p
        gateTruths))
    (hgoodTau : GateDerivedRejection.GoodDerivedTau thash vc p
      (ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) (pre ++ g :: post)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement thash vc p) s0.tables))
    (i : Nat) (hi : i < 2 ^ vc.degreeBits) (coeffs : List GoldilocksExt3Field.Element)
    (hcoeffs : AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) (pre ++ g :: post)
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (GateTerminalBinding.publicHashFunction
        ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
      = some coeffs)
    (hgoodAlpha : GateDerivedRejection.GoodDerivedAlpha thash vc p coeffs)
    (hident : ConstantsProvenance.SuppliedConstantsAreCommitted committedBy pin s0)
    (hpre : ∀ g' ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig vc) g'
      (ConstantsProvenance.pinnedConstantsTables committedBy pin s0.tables) i = Verifier.zero)
    (hpost : ∀ g' ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig vc) g'
      (ConstantsProvenance.pinnedConstantsTables committedBy pin s0.tables) i = Verifier.zero)
    (hactive : GateRejectionPower.rowFilter (Integrated.gateConfig vc) g
      (ConstantsProvenance.pinnedConstantsTables committedBy pin s0.tables) i ≠ Verifier.zero) :
    ∃ terms, GatesComplete.evaluateUnfiltered g (AlphaZeroCheck.rowWires s0.tables i)
        (AlphaZeroCheck.rowConstants s0.tables i)
        (GateTerminalBinding.publicHashFunction
          ((installedInitialEngine e gdec hash wp thash).publicInputsHash p.publicInputs))
        (Integrated.gateConfig vc).numSelectors = some terms ∧
      ∀ y ∈ terms, y = Verifier.zero :=
  ConstantsProvenance.provenanced_selected_gate_constraints_vanish thash pin chain committedBy
    (installed_initial_is_derived e gdec hash wp thash vc p) D hacc hfree hgoodTau i hi coeffs
    hcoeffs hgoodAlpha hident hpre hpost hactive

/-! ### 5a. No free challenge, and two observation conjuncts

The adopted `GateDerivedRejection` "no free challenge" family and two of the
`IntegratedTerminalChain.ObservationOnly` conjuncts also had `hderiv` as their
only transcript premise. -/

/-- Any `alpha` satisfying the adopted `alphaMatches` IS this engine's derived
gate alpha, with no premise. -/
theorem installed_adopted_alpha_is_derived_alpha
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (alpha : GoldilocksExt3Field.Element)
    (halpha : alpha.toVerifier =
      ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateAlpha) :
    alpha = TranscriptProvenance.gateAlphaElement thash vc p :=
  GateDerivedRejection.adopted_alpha_is_derived_alpha thash _ vc p
    (installed_initial_is_derived e gdec hash wp thash vc p) alpha halpha

/-- Any `tau` satisfying the adopted gate `htau` IS this engine's derived gate
tau column, with no premise. -/
theorem installed_adopted_tau_is_derived_tau
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (tau : List GoldilocksExt3Field.Element)
    (htau : NormDenseRound.values tau =
      ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateTau) :
    tau = TranscriptProvenance.gateTauColumn thash vc p :=
  GateDerivedRejection.adopted_tau_is_derived_tau thash _ vc p
    (installed_initial_is_derived e gdec hash wp thash vc p) tau htau

/-- Both at once: on this engine neither gate challenge is free. -/
theorem installed_challenges_are_pinned_to_the_derivation
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (alpha : GoldilocksExt3Field.Element) (tau : List GoldilocksExt3Field.Element)
    (halpha : alpha.toVerifier =
      ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateAlpha)
    (htau : NormDenseRound.values tau =
      ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateTau) :
    alpha = TranscriptProvenance.gateAlphaElement thash vc p ∧
    tau = TranscriptProvenance.gateTauColumn thash vc p :=
  GateDerivedRejection.challenges_are_pinned_to_the_derivation thash _ vc p
    (installed_initial_is_derived e gdec hash wp thash vc p) alpha tau halpha htau

/-- The adopted `TranscriptProvenance.derived_norm_shape_valid` with `hderiv`
GONE: the shrunken `NormShapeResidue` is enough for this engine. -/
theorem installed_derived_norm_shape_valid
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3)
    (hr : TranscriptProvenance.NormShapeResidue c t point) :
    Norm.shapeValid c
      (Norm.challengesFromInitial
        ((installedInitialEngine e gdec hash wp thash).initialTranscript c p)) t point = true :=
  TranscriptProvenance.derived_norm_shape_valid thash _ c p t point
    (installed_initial_is_derived e gdec hash wp thash c p) hr

/-- The adopted `TranscriptProvenance.observationOnly_of_derived` with `hderiv`
GONE: the nine-conjunct `ObservationOnlyDerived` builds the twelve-conjunct
adopted `IntegratedTerminalChain.ObservationOnly` for this engine. The three
deleted conjuncts (`logTau`, `gateTau`, `sevenChallenges`) are supplied by the
installed derivation. -/
theorem installed_observation_only
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (o : TranscriptProvenance.ObservationOnlyDerived
      (installedInitialEngine e gdec hash wp thash) decode pin chain c p) :
    IntegratedTerminalChain.ObservationOnly (installedInitialEngine e gdec hash wp thash)
      decode pin chain c p :=
  TranscriptProvenance.observationOnly_of_derived thash _ decode pin chain c p
    (installed_initial_is_derived e gdec hash wp thash c p) o

/-! ## 6. (d) The absorbed prefix IS `CommitmentOrder`'s twenty-two frames -/

/-- (d) **THE PREFIX, FOR THIS ENGINE'S OWN INITIAL TRANSCRIPT, WITH NO
`DerivedInitial` PREMISE.** The state at which this engine's gate alpha and gate
tau are squeezed is the fold of the adopted `CommitmentOrder.gateChallengeFrames`
-- twenty-two frames -- with the preprocessed, witness and norm-inverse roots at
positions 13, 15 and 19, and the only frames after the last root being the two
fixed domain separators. The pair (gate alpha, gate tau) is `gateChallengesAt` of
the prefix DIGEST and the configured width alone.

The FIRST conjunct carries no content: it is the definition of
`CommitmentOrder.prefixState` (CommitmentOrder.lean 235-236) unfolded, and is
listed only so the fold the later conjuncts speak about is written out. The
content is in conjuncts two through seven. -/
theorem installed_initial_prefix_is_commitment_order
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash) (vc : Verifier.Config) (p : Verifier.Proof) :
    CommitmentOrder.prefixState thash vc (Verifier.statement p) =
        OuterInitial.absorbMessages thash OuterInitial.startState
          (CommitmentOrder.gateChallengeFrames vc (Verifier.statement p)) ∧
    (CommitmentOrder.gateChallengeFrames vc (Verifier.statement p)).length = 22 ∧
    (CommitmentOrder.gateChallengeFrames vc (Verifier.statement p)).get? 13 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.preprocessedRoot)) ∧
    (CommitmentOrder.gateChallengeFrames vc (Verifier.statement p)).get? 15 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.witnessRoot)) ∧
    (CommitmentOrder.gateChallengeFrames vc (Verifier.statement p)).get? 19 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.normInverseRoot)) ∧
    (CommitmentOrder.gateChallengeFrames vc (Verifier.statement p)).drop 20 =
        [OuterInitial.domainMessage "public-input-mix-challenge-v3",
         OuterInitial.domainMessage "outer-relation-challenges-v3"] ∧
    (((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateAlpha,
        ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateTau)
      = CommitmentOrder.gateChallengesAt thash
          (CommitmentOrder.prefixDigest thash vc (Verifier.statement p)) vc.degreeBits := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (CommitmentOrder.three_roots_inside_the_prefix vc (Verifier.statement p)).1
  · exact (CommitmentOrder.three_roots_inside_the_prefix vc (Verifier.statement p)).2.1
  · exact (CommitmentOrder.three_roots_inside_the_prefix vc (Verifier.statement p)).2.2.1
  · exact CommitmentOrder.only_two_domain_separators_after_the_last_root vc
      (Verifier.statement p)
  · exact CommitmentOrder.gate_challenges_factor_through_prefix thash vc (Verifier.statement p)

/-- (d) The source counters, on this engine's own transcript and with no
premise: gate alpha at `9 + 3 * degreeBits`, gate tau coordinate `i` at
`12 + 3 * degreeBits + 3i`, both from the prefix digest. -/
theorem installed_initial_gate_challenge_counters
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (i : Nat) (hi : i < vc.degreeBits) :
    ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateAlpha =
        OuterInitial.ext3At thash
          (CommitmentOrder.prefixDigest thash vc (Verifier.statement p)) (9 + 3 * vc.degreeBits) ∧
    (((installedInitialEngine e gdec hash wp thash).initialTranscript vc p).gateTau).get? i =
        some (OuterInitial.ext3At thash
          (CommitmentOrder.prefixDigest thash vc (Verifier.statement p))
          (12 + 3 * vc.degreeBits + 3 * i)) :=
  CommitmentOrder.gate_challenge_counters thash vc p i hi

/-- (d) The adopted `CommitmentOrder.deterministic_adaptivity` -- HALF (A) of the
Fiat--Shamir adaptivity argument -- restated for this engine with `hderiv` GONE.
The extraction join `CommittedTables` stays a visible hypothesis; nothing here
discharges or weakens it.

**HALF (B) IS NOT INCLUDED AND IS NOT PROVED.** That the squeeze at those
counters is uniform and independent of the prefix is a hash assumption;
`CommitmentOrder.separation_fails_for_a_deterministic_hash` shows even its
deterministic shadow fails for a general deterministic hash. Only with (B) does
`hgood` become a probability event. -/
theorem installed_deterministic_adaptivity
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (c : Verifier.Config) (p : Verifier.Proof)
    (gc : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha : GoldilocksExt3Field.Element) (n : Nat) (t : GateSuffixPolynomial.Tables)
    (hcom : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p) t) :
    (((installedInitialEngine e gdec hash wp thash).initialTranscript c p).gateAlpha,
        ((installedInitialEngine e gdec hash wp thash).initialTranscript c p).gateTau)
        = CommitmentOrder.gateChallengesAt thash
            (CommitmentOrder.prefixDigest thash c (Verifier.statement p)) c.degreeBits ∧
    ((CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).get? 13 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.preprocessedRoot)) ∧
      (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).get? 15 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.witnessRoot)) ∧
      (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).get? 19 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.normInverseRoot)) ∧
      (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).length = 22) ∧
    (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).drop 20 =
        [OuterInitial.domainMessage "public-input-mix-challenge-v3",
         OuterInitial.domainMessage "outer-relation-challenges-v3"] ∧
    (∀ (u : GateSuffixPolynomial.Tables),
        CommitmentOrder.CommittedTables tablesOf (Verifier.statement p) u →
        CommitmentOrder.gateBadSet gc gates publicHash alpha u n =
          CommitmentOrder.gateBadSet gc gates publicHash alpha t n) ∧
    (∀ (c2 : Verifier.Config) (s2 : Verifier.Statement) (u : GateSuffixPolynomial.Tables),
        CommitmentOrder.CommittedTables tablesOf s2 u →
        (u.wires ≠ t.wires ∨ u.constants ≠ t.constants) →
        CommitmentOrder.prefixDigest thash c2 s2 =
          CommitmentOrder.prefixDigest thash c (Verifier.statement p) →
        CommitmentOrder.TranscriptCollision thash) :=
  CommitmentOrder.deterministic_adaptivity thash tablesOf
    (installedInitialEngine e gdec hash wp thash) c p gc gates publicHash alpha n t
    (installed_initial_is_derived e gdec hash wp thash c p) hcom

/-! ## 7. (e) What the transcript observation still leaves open

`remaining_observations` (section 2) is the field-level list: `commitRound`,
`parseWhir`, `configurationHash`, `deploymentValid`. `commitRound` is the one a
concurrent candidate module is installing; the other three have no candidate.

The PROVER-SIDE challenge equality is a different kind of gap and is NOT closed
here. The adopted `TranscriptProvenance` carries
`hch : pr.challenges = TranscriptProvenance.logChallenges thash c p` in eight
places (411, 439, 452, 473, 574, 593, 754 and the honest-prover glue). That
hypothesis is about the PROVER's `NormDenseRound.Prepared` record, not about the
verifier engine's hook: it says the prover built its tables from those seven
challenges. `DerivedInitial` says only what the VERIFIER computes. The statement
below makes the asymmetry explicit: the verifier-side identity is unconditional
for this engine, while the prover-side one is an extra constraint on `pr` that
merely lets the two be identified once assumed. -/

/-- (e) The verifier-side identity, together with what an ASSUMED prover-side
challenge equality buys on top of it. Conjunct 1 is the verifier-side fact,
unconditional -- it is a restatement of `installed_initial_is_derived` and adds
nothing to it. Conjunct 2 is the asymmetry made visible: for a prover record
`pr` the identification of `pr.challenges` with what this engine observes holds
only UNDER the hypothesis `pr.challenges = logChallenges thash vc p`, which this
module neither discharges nor weakens. A theorem cannot assert that something
is still a hypothesis; the prose above, and the explicit binder on `pr` below,
are where that reading lives. -/
theorem installed_verifier_identity_with_assumed_prover_challenges
    (e : Verifier.Engine) (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (wp : VkParams) (thash : Transcript.Hash) (vc : Verifier.Config) (p : Verifier.Proof) :
    TranscriptProvenance.DerivedInitial thash
        (installedInitialEngine e gdec hash wp thash) vc p ∧
    (∀ pr : NormDenseRound.Prepared,
        pr.challenges = TranscriptProvenance.logChallenges thash vc p →
        Norm.challengesFromInitial
            ((installedInitialEngine e gdec hash wp thash).initialTranscript vc p)
          = pr.challenges) :=
  ⟨installed_initial_is_derived e gdec hash wp thash vc p,
   fun pr hch => by
     rw [hch]
     exact TranscriptProvenance.challenges_from_initial_is_derived thash _ vc p
       (installed_initial_is_derived e gdec hash wp thash vc p)⟩

/-! ## 8. Examples on the adopted fixture

`OuterAdapter.fixtureConfig` / `fixtureProof` (one coupled round, one index
coordinate, `degreeBits = 1`), the same fixture the adopted
`TranscriptProvenance.Example` and `CommitmentOrder.Example` use. Every statement
is universally quantified over BOTH hashes and over the engine whose remaining
hooks are unconstrained. The fixture is NOT a valid gate/WHIR deployment and NOT
an accepting proof; nothing here says otherwise. No `decide` runs over a digest
space: the only decidable checks are on list lengths. -/

namespace Example

open OuterAdapter

/-- (4) On the fixture: the seven challenges EXIST (length 7, the source's
seven-slot layout), both tau columns have the fixture's `degreeBits = 1` width,
and the transcript snapshot is the source's forty bytes. -/
theorem fixture_initial_shape (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) :
    ((installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig
        fixtureProof).logChallenges.length = 7 ∧
    ((installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig
        fixtureProof).logTau.length = 1 ∧
    ((installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig
        fixtureProof).gateTau.length = 1 ∧
    ((installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig
        fixtureProof).transcript.length = 40 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (installed_initial_columns e gdec hash wp thash fixtureConfig fixtureProof).2.2.2.1
  · exact (installed_initial_columns e gdec hash wp thash fixtureConfig fixtureProof).2.2.2.2.1
  · exact (installed_initial_columns e gdec hash wp thash fixtureConfig fixtureProof).2.2.2.2.2
  · exact (OuterInitial.derived_initial_shape thash fixtureConfig
      (Verifier.statement fixtureProof)).2.2.2

/-- (4) On the fixture the seven challenges are exactly the source's slot list,
so each of the seven is present by name. -/
theorem fixture_seven_challenges_exist (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) :
    ((installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig
        fixtureProof).logChallenges =
      [(TranscriptProvenance.logChallenges thash fixtureConfig fixtureProof).eta,
       (TranscriptProvenance.logChallenges thash fixtureConfig fixtureProof).beta,
       (TranscriptProvenance.logChallenges thash fixtureConfig fixtureProof).gamma,
       (TranscriptProvenance.logChallenges thash fixtureConfig fixtureProof).xi,
       (TranscriptProvenance.logChallenges thash fixtureConfig fixtureProof).lambda,
       (TranscriptProvenance.logChallenges thash fixtureConfig fixtureProof).rho,
       (TranscriptProvenance.logChallenges thash fixtureConfig fixtureProof).kappa] :=
  OuterInitial.initial_has_exact_seven_challenge_layout
    (TranscriptProvenance.derived thash fixtureConfig fixtureProof)

/-- (4) On the fixture the twenty-two-frame prefix is literal, and the gate
alpha/tau pair factors through the prefix digest at the fixture's width. -/
theorem fixture_prefix (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) :
    (CommitmentOrder.gateChallengeFrames fixtureConfig
        (Verifier.statement fixtureProof)).length = 22 ∧
    (((installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig
          fixtureProof).gateAlpha,
        ((installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig
          fixtureProof).gateTau)
      = CommitmentOrder.gateChallengesAt thash
          (CommitmentOrder.prefixDigest thash fixtureConfig (Verifier.statement fixtureProof))
          fixtureConfig.degreeBits := by
  have h := installed_initial_prefix_is_commitment_order e gdec hash wp thash fixtureConfig
    fixtureProof
  exact ⟨h.2.1, h.2.2.2.2.2.2⟩

/-- (4) **THE ABSTRACT OBSERVATION IS NOT THIS FUNCTION.**
`Verifier.testEngine.initialObservation` (Verifier.lean 602-611) is a constant
stand-in with an EMPTY challenge list and an EMPTY transcript snapshot;
`Integrated.exampleEngine.initialObservation` (Integrated.lean 197-204) is a
seven-slot constant whose snapshot is also empty. The installed initial
transcript differs from both in SHAPE: forty snapshot bytes against zero. -/
theorem fixture_abstract_observation_differs (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) :
    (Verifier.testEngine.initialTranscript fixtureConfig fixtureProof).logChallenges.length = 0 ∧
    (Verifier.testEngine.initialTranscript fixtureConfig fixtureProof).transcript.length = 0 ∧
    (Integrated.exampleEngine.initialTranscript fixtureConfig fixtureProof).transcript.length
      = 0 ∧
    (installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig fixtureProof
      ≠ Verifier.testEngine.initialTranscript fixtureConfig fixtureProof ∧
    (installedInitialEngine e gdec hash wp thash).initialTranscript fixtureConfig fixtureProof
      ≠ Integrated.exampleEngine.initialTranscript fixtureConfig fixtureProof := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro h
    have hl := (fixture_initial_shape e gdec hash wp thash).2.2.2
    rw [h] at hl
    exact absurd hl (by decide)
  · intro h
    have hl := (fixture_initial_shape e gdec hash wp thash).2.2.2
    rw [h] at hl
    exact absurd hl (by decide)

/-- (4) The public-input hash of the fixture's public-input list is the concrete
Poseidon digest, four limbs long -- not `Verifier.testEngine`'s empty list. -/
theorem fixture_public_input_hash (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) :
    ((installedInitialEngine e gdec hash wp thash).publicInputsHash
        fixtureProof.publicInputs).length = 4 ∧
    (Verifier.testEngine.publicInputsHash fixtureProof.publicInputs).length = 0 ∧
    (installedInitialEngine e gdec hash wp thash).publicInputsHash fixtureProof.publicInputs
      ≠ Verifier.testEngine.publicInputsHash fixtureProof.publicInputs := by
  refine ⟨installed_public_input_hash_length e gdec hash wp thash fixtureProof, rfl, ?_⟩
  intro h
  have hl := installed_public_input_hash_length e gdec hash wp thash fixtureProof
  rw [h] at hl
  exact absurd hl (by decide)

end Example

end Audit.Wire3.InstalledInitialTranscript
