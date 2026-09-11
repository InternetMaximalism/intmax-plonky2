import Audit.Wire3.InstalledRoundCommit
import Audit.Wire3.InstalledInitialTranscript
import Audit.Wire3.PinnedWhirProfile

/-!
# The composed outer engine: ten installed fields, two observations left

## The gap this module closes

Three sibling modules each installed one more `Verifier.Engine` field on top of
the adopted `InstalledIndexSampler.installedSamplerEngine` /
`InstalledWhirTail.installedEngine` stack, and each said in its own header that
composing with the others was a LATER step:

* `InstalledInitialTranscript.installedInitialEngine` installs
  `initialObservation` (as `fun c s => OuterInitial.toInitial (OuterInitial.derive thash c s)`)
  and `publicInputsHash` (as `PublicInputHashBinding.hashNoPad`). Its header:
  "Composing this engine with a concrete `commitRound` is a LATER step".
* `InstalledRoundCommit.installedRoundEngine` installs `commitRound` (as
  `concreteCommitRound thash`). Its header: "That composition is NOT performed
  here ... the one-line glue statement naming the composed engine is a LATER
  step". NINE of its sections 6-8 theorems carry the hypothesis
  `hi : e.initialTranscript c p = OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p))`
  -- InstalledRoundCommit.lean 649, 670, 688, 706, 740, 799, 850, 956, 1063.
  The one section 6-8 theorem that does NOT carry it is
  `failed_path_passes_index_guard_at_index_bits_zero`, which is about an engine
  whose initial transcript is precisely not the derived one. Seven of the nine
  `hi`-carrying theorems are restated here at the composed engine.
* `PinnedWhirProfile.pinnedEngine` makes `deploymentValid` concrete
  (`pinnedDeployment`) on `InstalledWhirTail.installedEngine` with the WHIR
  parameter record fixed to `pinnedParams P c₀`, the record decoded from the
  deployed configuration's own WHIR bytes.

This module performs the composition. `composedEngine e gdec hash thash P c₀`
carries ALL of them at once, and the composition is what discharges
`InstalledRoundCommit`'s `hi`: the engine's own `initialObservation` IS the
derivation, so `hi` is `rfl` and `TranscriptProvenance.DerivedInitial` holds for
the composed engine with no hypothesis at all.

**NO NEW PROOF CONTENT.** Every theorem below is an ADOPTED theorem
instantiated at the composed engine, or a conjunction of such. The only original
steps are (i) the `rfl` identities of section 1, which say the composed engine
IS each sibling's engine over the right base, and (ii) routing acceptance
through `Verifier.verify_success_checks` to supply `c.degreeBits ≤ 13`. Nothing
here re-models a transcript frame, a hash, a Merkle path or a WHIR round.

## The migration rule, applied

Both installers state their own migration rule, and both are used below exactly
as written. `InstalledIndexSampler.installed_sampler_is_installed_tail_of_resampled`
says the sampler engine IS the tail engine over `resampled e thash`;
`InstalledRoundCommit.installed_round_is_installed_sampler_of_recommitted` says
the round engine IS the sampler engine over `recommitted e thash`;
`InstalledInitialTranscript.installed_initial_is_sampler_of_with_initial` says
the initial engine IS the sampler engine over
`PublicInputHashBinding.withPublicInputsHash (OuterInitial.withInitial thash e)`.
Section 1 chains all four rules, so an adopted theorem quantified over an
arbitrary `Verifier.Engine` is applied here by instantiating it at the
CORRESPONDING BASE, never at the user's `e`:

| adopted module | base to instantiate at |
|---|---|
| `InstalledRoundCommit` | `roundBase e thash P c₀` |
| `InstalledInitialTranscript` | `initialBase e thash P c₀` |
| `PinnedWhirProfile` | `outerInstalled e thash` |
| `InstalledWhirTail` | `outerInstalled (PinnedWhirProfile.pinnedBase P e c₀) thash` |

This matters for section 3 in particular. ACCEPTANCE UNDER THE COMPOSED ENGINE
IS A DIFFERENT PREDICATE from acceptance under `PinnedWhirProfile.pinnedEngine P e …`:
the composed engine's `commitRound`, `initialObservation`, `publicInputsHash`
and `sampleIndices` are concrete, so its `derivedRounds`, `derivedIndices`,
`derivedContext`, `logTerminal` and `gateTerminal` all differ from that engine's.
No acceptance fact is TRANSPORTED between the two. Instead the adopted
`PinnedWhirProfile` theorems -- which are quantified over an arbitrary base
engine `e` -- are instantiated at `outerInstalled e thash`, for which the pinned
engine IS the composed engine by `rfl`.

## Field table after composition

INSTALLED (ten, all concrete and executable):

| field | value | installed by |
|---|---|---|
| `foldClaim` | `Connections.packedFold` | `Integrated.modelEngine` |
| `normEvaluation` | `Norm.normEvaluation` | `Integrated.modelEngine` |
| `eqEvaluation` | `Norm.eqEvaluation` | `Integrated.modelEngine` |
| `gateEvaluation` | `Integrated.evaluateGate gdec …` | `Integrated.modelEngine` |
| `whirTail` | `InstalledWhirTail.installedTail hash (pinnedParams P c₀)` | `InstalledWhirTail` |
| `sampleIndices` | `InstalledIndexSampler.concreteSampleIndices thash` | `InstalledIndexSampler` |
| `initialObservation` | `InstalledInitialTranscript.concreteInitialObservation thash` | `InstalledInitialTranscript` |
| `publicInputsHash` | `PublicInputHashBinding.hashNoPad` | `InstalledInitialTranscript` |
| `commitRound` | `InstalledRoundCommit.concreteCommitRound thash` | `InstalledRoundCommit` |
| `deploymentValid` | `PinnedWhirProfile.pinnedDeployment P e c₀` | `PinnedWhirProfile` |

STILL OBSERVATIONS -- exactly two, and `composed_remaining_observations` states
them: `parseWhir` and `configurationHash`.

## What this does NOT do

**`parseWhir` IS STILL AN OBSERVATION, AND SO IS `configurationHash`.** These
are the only two fields left, and neither is touched here.

The `parseWhir` boundary is worth stating precisely, because it is easy to
oversell in either direction. `Verifier.verifyWhir` (Verifier.lean 365-368)
calls `e.parseWhir` and then `Verifier.rootsAndClaimsMatch ctx parsed`
(Verifier.lean 312-314), which compares BOTH of the parser's root copies with
`ctx.roots` -- the triple the OUTER VERIFIER itself assembled,
`[p.preprocessedRoot, p.witnessRoot, p.normInverseRoot]` (Verifier.lean 250-251)
-- and compares the parser's claims with `ctx.expectedClaims`.

Exactly ONE of the three roots is DEPLOYMENT-pinned: `Verifier.shape`
(Verifier.lean 136) forces `p.preprocessedRoot = pin.preprocessedRoot`, so the
first entry is the verification key's own preprocessed root and the theorems
below write it as `pin.preprocessedRoot`. The other two, `p.witnessRoot` and
`p.normInverseRoot`, are the PROOF'S OWN declared commitments: nothing in the
adopted tree says they commit to anything in particular, and nothing here
claims they are the "right" roots.

The WHIR context's roots and claims therefore come from the OUTER verifier, not
from `parseWhir`: the parser only has to REPRODUCE them. Independently,
`InstalledWhirTail.installed_acceptance_runs_the_concrete_tail` pins the
roots the CONCRETE TAIL reads for itself out of the WHIR transcript, through
`WhirInitial`, to the same triple. So what is stated below is a CONSISTENCY
statement -- neither the parser nor the concrete tail can substitute a root
other than the ones the outer verifier bound the context to -- and NOT a
statement that the witness roots are correct:

* an abstract `parseWhir` CAN still make a perfectly good proof fail (it is an
  arbitrary function and may return `none` or a mismatching record), and
* an abstract `parseWhir` CANNOT swap in a DIFFERENT root: whatever it returns,
  acceptance forces `parsed.actualRoots = parsed.boundRoots = ctx.roots`, and
  the tail's own `WhirInitial` reading of the commitments equals that same
  triple.

`composed_parse_whir_cannot_pass_a_wrong_root` is that statement. What is NOT
claimed is that the parser's OTHER outputs are pinned: `ParsedWhir` fields not
compared by `rootsAndClaimsMatch` are unconstrained, and the tail's `_` argument
ignores the parsed record entirely (`InstalledWhirTail.installedTail`), so the
composed engine gets its WHIR content from `tailRun`, not from `parseWhir`.
`configurationHash` is compared only against `pin.configDigest` (Verifier.lean
413); its provenance from the config/VK frames is modelled nowhere in the
adopted tree, and `PinnedWhirProfile`'s conjunct (i) stands in for it as an
explicit keccak-injectivity assumption.

**The `indexBits = 0` failure branch of `InstalledRoundCommit` is DEAD here.**
That module's `failed_path_passes_index_guard_at_index_bits_zero` documents a
real gap for an engine whose `initialObservation` is not the derived one: the
concrete commit returns `failedRound`, the sampler returns empty index lanes,
and at `c.indexBits = 0` -- which `Verifier.envelope` ADMITS, see
`InstalledRoundCommit.envelope_admits_index_bits_zero_iff_width_one` -- those
empty lanes satisfy the verifier's index-length guard. For the COMPOSED engine
`DerivedInitial` is `rfl`, so under `c.degreeBits ≤ 13` every snapshot of the
run decodes and that branch cannot be entered:
`composed_snapshots_always_decode` states it. This removes the gap for THIS
engine only; the adopted statement about a general engine is unchanged, and
nothing here says what `Verifier.verify` does on the branch for some other
engine.

**Everything else the siblings disclaim is disclaimed here, unchanged.** The
R1b, R2 and R3 families of `InstalledWhirTail` are untouched. Half (B) of the
Fiat--Shamir reading -- that the squeezes are uniform and independent of the
absorbed prefix -- is UNFORMALIZED here and anywhere in the adopted tree; the
adopted `CommitmentOrder.separation_fails_for_a_deterministic_hash` refutes even
its weaker deterministic shadow for a general deterministic hash.
`JointChallengeSpace.DrawEncodesRun` remains a COORDINATE statement even at
`InstalledRoundCommit.actualDigestDraw`: the run's own digest triples inhabit
it, but no law, uniform or otherwise, is attached to any coordinate.
`JointChallengeSpace.sourceBlock`'s block NUMBERING is still a label.

`thash` and `hash` are ARBITRARY DETERMINISTIC FUNCTIONS. Keccak is not
modelled, so `PinnedWhirProfile.TableIsCanonical` (the generated table row is
the digest of the canonical record, and the digest separates records) and
conjunct (i) of `pinnedDeployment` (the deployed WHIR bytes pin) remain
ASSUMPTIONS, carried visibly by every theorem that needs them. No collision
resistance, no random-oracle property, no Fiat--Shamir soundness, no WHIR/PCS
soundness, no sumcheck soundness, no Rust/Yul/Solidity refinement, no gas or
exception-order claim. `Verifier.verify` is a manual success-boundary model.

Nothing here is the deployed system's soundness error. The wire-v3 WHIR profile
this tree models is the approximately 100-bit design point. No figure in this
module is a security level, and in particular nothing here says "125".
-/

namespace Audit.Wire3.ComposedEngine

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The composed engine, and the four bases -/

abbrev VkParams := InstalledIndexSampler.VkParams

abbrev Profile := PinnedWhirProfile.Profile

/-- **THE ENGINE OF THIS MODULE.** `Integrated.modelEngine` -- which installs
`foldClaim`, `normEvaluation`, `eqEvaluation` and `gateEvaluation` -- with the
six further installed fields written out explicitly: the WHIR tail at the pinned
parameter record, the concrete constituent-index sampler, the concrete initial
transcript, the concrete public-input hash, the concrete coupled-round commit,
and the pinned deployment predicate. `hash` is the WHIR/Merkle hash and `thash`
the outer transcript hash; in the sources both are Keccak, but nothing in the
Lean model ties them and both are arbitrary deterministic functions. `c₀` is the
DEPLOYED configuration, the one whose WHIR bytes the parameter record is decoded
from. -/
def composedEngine (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config) :
    Verifier.Engine :=
  { Integrated.modelEngine e gdec with
    deploymentValid := PinnedWhirProfile.pinnedDeployment P e c₀,
    initialObservation := InstalledInitialTranscript.concreteInitialObservation thash,
    publicInputsHash := InstalledInitialTranscript.concretePublicInputsHash,
    commitRound := InstalledRoundCommit.concreteCommitRound thash,
    sampleIndices := InstalledIndexSampler.concreteSampleIndices thash,
    whirTail := InstalledWhirTail.installedTail hash (PinnedWhirProfile.pinnedParams P c₀) }

/-- The base at which `PinnedWhirProfile`'s theorems are instantiated: the
user's engine with the FOUR outer fields installed and the deployment predicate
still `e`'s own, since `PinnedWhirProfile.pinnedBase` supplies that itself. -/
def outerInstalled (e : Verifier.Engine) (thash : Transcript.Hash) : Verifier.Engine :=
  { e with
    initialObservation := InstalledInitialTranscript.concreteInitialObservation thash,
    publicInputsHash := InstalledInitialTranscript.concretePublicInputsHash,
    commitRound := InstalledRoundCommit.concreteCommitRound thash,
    sampleIndices := InstalledIndexSampler.concreteSampleIndices thash }

/-- The base at which `InstalledRoundCommit`'s theorems are instantiated: the
pinned base carrying the two adopted installers `OuterInitial.withInitial` and
`PublicInputHashBinding.withPublicInputsHash`. Its `initialTranscript` is the
adopted derivation by `rfl` (`composed_initial_hypothesis_holds_at_the_round_base`),
which is precisely how `InstalledRoundCommit`'s `hi` is discharged. -/
def roundBase (e : Verifier.Engine) (thash : Transcript.Hash) (P : Profile)
    (c₀ : Verifier.Config) : Verifier.Engine :=
  PublicInputHashBinding.withPublicInputsHash
    (OuterInitial.withInitial thash (PinnedWhirProfile.pinnedBase P e c₀))

/-- The base at which `InstalledInitialTranscript`'s theorems are instantiated:
the pinned base with `InstalledRoundCommit`'s own migration wrapper
`recommitted` applied. -/
def initialBase (e : Verifier.Engine) (thash : Transcript.Hash) (P : Profile)
    (c₀ : Verifier.Config) : Verifier.Engine :=
  InstalledRoundCommit.recommitted (PinnedWhirProfile.pinnedBase P e c₀) thash

/-- (1) The composed engine IS `PinnedWhirProfile.pinnedEngine` over the
four-field base, so every `PinnedWhirProfile` theorem applies to it by
instantiating that module's arbitrary base engine at `outerInstalled e thash`.
This is the identity section 3 uses instead of transporting acceptance. -/
theorem composed_is_the_pinned_engine (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config) :
    composedEngine e gdec hash thash P c₀ =
      PinnedWhirProfile.pinnedEngine P (outerInstalled e thash) gdec hash c₀ := rfl

/-- (1) The composed engine IS
`InstalledInitialTranscript.installedInitialEngine` over `initialBase`, at the
pinned parameter record. -/
theorem composed_is_the_installed_initial_engine (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) :
    composedEngine e gdec hash thash P c₀ =
      InstalledInitialTranscript.installedInitialEngine (initialBase e thash P c₀) gdec hash
        (PinnedWhirProfile.pinnedParams P c₀) thash := rfl

/-- (1) The composed engine IS `InstalledRoundCommit.installedRoundEngine` over
`roundBase`, at the pinned parameter record. Together with the previous identity
this is the statement that the two installers COMMUTE. -/
theorem composed_is_the_installed_round_engine (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) :
    composedEngine e gdec hash thash P c₀ =
      InstalledRoundCommit.installedRoundEngine (roundBase e thash P c₀) gdec hash
        (PinnedWhirProfile.pinnedParams P c₀) thash := rfl

/-- (1) The composed engine IS
`InstalledIndexSampler.installedSamplerEngine` and IS
`InstalledWhirTail.installedEngine`, both over the pinned base carrying all four
outer installers. The second form is the one `InstalledWhirTail`'s acceptance
theorems are instantiated at. -/
theorem composed_is_the_sampler_and_tail_engine (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) :
    composedEngine e gdec hash thash P c₀ =
      InstalledIndexSampler.installedSamplerEngine
        (outerInstalled (PinnedWhirProfile.pinnedBase P e c₀) thash) gdec hash
        (PinnedWhirProfile.pinnedParams P c₀) thash ∧
    composedEngine e gdec hash thash P c₀ =
      InstalledWhirTail.installedEngine
        (outerInstalled (PinnedWhirProfile.pinnedBase P e c₀) thash) gdec hash
        (PinnedWhirProfile.pinnedParams P c₀) :=
  ⟨rfl, rfl⟩

/-- (1) The composed engine is its own `Integrated.modelEngine`, so the adopted
glue that speaks of `modelEngine` applies to it unchanged. -/
theorem composed_is_its_own_model_engine (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config) :
    Integrated.modelEngine (composedEngine e gdec hash thash P c₀) gdec =
      composedEngine e gdec hash thash P c₀ := rfl

/-- (1) **THE TEN INSTALLED FIELDS**, on ONE engine. Four come from
`Integrated.modelEngine`, one from `InstalledWhirTail` at the record decoded
from the deployed configuration, one from `InstalledIndexSampler`, two from
`InstalledInitialTranscript`, one from `InstalledRoundCommit` and one from
`PinnedWhirProfile`. The simultaneity is the whole content of this module; each
individual field was installed by a sibling. -/
theorem composed_installed_fields (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config) :
    (composedEngine e gdec hash thash P c₀).foldClaim = Connections.packedFold ∧
    (composedEngine e gdec hash thash P c₀).normEvaluation = Norm.normEvaluation ∧
    (composedEngine e gdec hash thash P c₀).eqEvaluation = Norm.eqEvaluation ∧
    (composedEngine e gdec hash thash P c₀).gateEvaluation =
      (fun c wires constants publicHash alpha =>
        (Integrated.evaluateGate gdec c wires constants publicHash alpha).getD Verifier.zero) ∧
    (composedEngine e gdec hash thash P c₀).whirTail =
      InstalledWhirTail.installedTail hash (PinnedWhirProfile.pinnedParams P c₀) ∧
    (composedEngine e gdec hash thash P c₀).sampleIndices =
      InstalledIndexSampler.concreteSampleIndices thash ∧
    (composedEngine e gdec hash thash P c₀).initialObservation =
      InstalledInitialTranscript.concreteInitialObservation thash ∧
    (composedEngine e gdec hash thash P c₀).publicInputsHash =
      PublicInputHashBinding.hashNoPad ∧
    (composedEngine e gdec hash thash P c₀).commitRound =
      InstalledRoundCommit.concreteCommitRound thash ∧
    (composedEngine e gdec hash thash P c₀).deploymentValid =
      PinnedWhirProfile.pinnedDeployment P e c₀ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (1) **THE TWO REMAINING OBSERVATIONS.** After the composition exactly two
`Verifier.Engine` fields are still the user's opaque hooks. See the header for
what `parseWhir` can and cannot do, and
`composed_parse_whir_cannot_pass_a_wrong_root` for the precise statement. -/
theorem composed_remaining_observations (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config) :
    (composedEngine e gdec hash thash P c₀).parseWhir = e.parseWhir ∧
    (composedEngine e gdec hash thash P c₀).configurationHash = e.configurationHash :=
  ⟨rfl, rfl⟩

/-- (1) The derived transcript objects of the composed engine, written out: the
initial transcript is the adopted derivation and the rounds are the concrete run
of `InstalledRoundCommit.concreteCommitRound` started from it. Both are `rfl`;
they are what makes the two installers interact at all. -/
theorem composed_derived_objects (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config)
    (c : Verifier.Config) (p : Verifier.Proof) :
    (composedEngine e gdec hash thash P c₀).initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)) ∧
    Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p =
      Verifier.runRounds (InstalledRoundCommit.concreteCommitRound thash)
        (Verifier.start (OuterInitial.toInitial (OuterInitial.derive thash c
          (Verifier.statement p)))) (p.logRounds.zip p.gateRounds) :=
  ⟨rfl, rfl⟩

/-! ## 2. The discharged `hi`: `DerivedInitial` is `rfl` for the composed engine -/

/-- (2) The exact hypothesis `hi` that every section-6-to-8 theorem of
`InstalledRoundCommit` carries, at the base that module is instantiated at. It
is `rfl`, and that single fact is what the whole of section 2 below rests on. -/
theorem composed_initial_hypothesis_holds_at_the_round_base (e : Verifier.Engine)
    (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config) (c : Verifier.Config)
    (p : Verifier.Proof) :
    (roundBase e thash P c₀).initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)) := rfl

/-- (2) **THE COMPOSED ENGINE'S INITIAL TRANSCRIPT IS THE DERIVATION.** The
adopted `TranscriptProvenance.DerivedInitial` premise, which 36 adopted sites
carry as a hypothesis, holds unconditionally. This is
`InstalledInitialTranscript.installed_initial_is_derived` at `initialBase`,
which is in turn the adopted `TranscriptProvenance.withInitial_derived`; the
proof term shows the provenance rather than hiding it behind `rfl`. -/
theorem composed_initial_is_derived (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config)
    (vc : Verifier.Config) (p : Verifier.Proof) :
    TranscriptProvenance.DerivedInitial thash (composedEngine e gdec hash thash P c₀) vc p :=
  InstalledInitialTranscript.installed_initial_is_derived (initialBase e thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash vc p

/-- (2) The seven challenges, the two derived columns and the gate alpha, all
unconditional for the composed engine. Restated from
`InstalledInitialTranscript.installed_initial_columns`. -/
theorem composed_initial_columns (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config)
    (vc : Verifier.Config) (p : Verifier.Proof) :
    Norm.challengesFromInitial
        ((composedEngine e gdec hash thash P c₀).initialTranscript vc p) =
      TranscriptProvenance.logChallenges thash vc p ∧
    NormDenseRound.values (TranscriptProvenance.gateTauColumn thash vc p) =
      ((composedEngine e gdec hash thash P c₀).initialTranscript vc p).gateTau ∧
    (TranscriptProvenance.gateAlphaElement thash vc p).toVerifier =
      ((composedEngine e gdec hash thash P c₀).initialTranscript vc p).gateAlpha ∧
    ((composedEngine e gdec hash thash P c₀).initialTranscript vc p).logChallenges.length = 7 ∧
    ((composedEngine e gdec hash thash P c₀).initialTranscript vc p).logTau.length =
      vc.degreeBits ∧
    ((composedEngine e gdec hash thash P c₀).initialTranscript vc p).gateTau.length =
      vc.degreeBits :=
  InstalledInitialTranscript.installed_initial_columns (initialBase e thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash vc p

/-- (2) **THE DECODED SNAPSHOT, WITH `hi` GONE.**
`InstalledRoundCommit.decoded_snapshot_unconditional` for the composed engine:
only `c.degreeBits ≤ 13` remains, and `InstalledRoundCommit.concreteFinal` names
the decoded state exactly. -/
theorem composed_decoded_snapshot (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config)
    (c : Verifier.Config) (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13) :
    OuterAdapter.decode
        (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).transcript =
      some (InstalledRoundCommit.concreteFinal thash
        (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)) :=
  InstalledRoundCommit.decoded_snapshot_unconditional (roundBase e thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash c p rfl hdb

/-- (2) **THE `indexBits = 0` FAILURE BRANCH IS DEAD FOR THIS ENGINE.**
`InstalledRoundCommit.failed_path_passes_index_guard_at_index_bits_zero` records
a real gap: for an engine whose initial observation is NOT the derived one the
concrete commit returns `failedRound`, the installed sampler returns EMPTY index
lanes, and at `c.indexBits = 0` -- which the adopted `Verifier.envelope` admits
(`InstalledRoundCommit.envelope_admits_index_bits_zero_iff_width_one`) -- those
empty lanes SATISFY the verifier's index-length guard (Verifier.lean 420-421).
Composition closes it here: the hypothesis of that theorem is UNSATISFIABLE for
the composed engine under `c.degreeBits ≤ 13`, because `DerivedInitial` is `rfl`
and every snapshot of the run therefore decodes.

This is a statement about the COMPOSED engine only. The adopted statement about
a general engine is unchanged, and nothing here says what `Verifier.verify` does
on that branch for an engine that can reach it. -/
theorem composed_snapshots_always_decode (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config)
    (c : Verifier.Config) (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13) :
    OuterAdapter.decode
        (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).transcript ≠ none ∧
    ∃ st, OuterAdapter.decode
      (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).transcript = some st := by
  have h := composed_decoded_snapshot e gdec hash thash P c₀ c p hdb
  exact ⟨by rw [h]; exact Option.noConfusion, ⟨_, h⟩⟩

/-- (2) **THE ROUNDS ARE THE ADOPTED CHECKED EXECUTION, WITH `hi` GONE.**
`InstalledRoundCommit.installed_rounds_are_the_checked_execution` for the
composed engine. The adopted
`OuterAdapter.execute_matches_existing_derived_context` takes four
compatibility hypotheses; `CommitAgrees` and `SamplesAgree` are theorems of the
siblings, `foldClaim = Connections.packedFold` is `rfl`, and the initial
transcript hypothesis is now `rfl` too. Only `c.degreeBits ≤ 13` and success of
the checked execution itself remain. -/
theorem composed_rounds_are_the_checked_execution (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (c : Verifier.Config) (p : Verifier.Proof)
    (result : OuterAdapter.Execution) (hdb : c.degreeBits ≤ 13)
    (h : OuterAdapter.execute thash c p = some result) :
    result.rounds = Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p ∧
    result.initial = (composedEngine e gdec hash thash P c₀).initialTranscript c p ∧
    result.indices.points = Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p ∧
    result.context = Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p :=
  InstalledRoundCommit.installed_rounds_are_the_checked_execution (roundBase e thash P c₀) gdec
    hash (PinnedWhirProfile.pinnedParams P c₀) thash c p result rfl hdb h

/-- (2) **THE ROUND DIGESTS CHAIN AFTER THE TWENTY-TWO-FRAME PREFIX, WITH `hi`
GONE.** `InstalledRoundCommit.round_digests_chain_after_prefix` for the composed
engine: the state the first round commits onto is the adopted
`OuterInitial.derive` state, whose digest is the fold of
`CommitmentOrder.gateChallengeFrames` -- twenty-two frames -- over
`OuterInitial.startState`; each round's commit digest is the five-frame fold
`InstalledRoundCommit.roundFrames`; round `r`'s digest is that fold applied to
the state left by rounds `< r`; and the two point lists are the coordinatewise
reductions of the chain at counters `0` and `3`.

WHAT IS STILL A LABEL. `JointChallengeSpace.sourceBlock`'s NUMBERING of the
blocks and `InstalledIndexSampler.indexSchedulePosition`'s `degreeBits + 1` are
untouched, exactly as in the sibling. -/
theorem composed_round_digests_chain_after_prefix (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) :
    (OuterInitial.derive thash c (Verifier.statement p)).state.digest =
        (OuterInitial.absorbMessages thash OuterInitial.startState
          (CommitmentOrder.gateChallengeFrames c (Verifier.statement p))).digest ∧
    (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).length = 22 ∧
    (∀ (st : Transcript.State) (i : Nat) (m : Verifier.CoupledMessage),
      OuterAdapter.roundCommitted thash st i m.1 m.2 =
          OuterInitial.absorbMessages thash st (InstalledRoundCommit.roundFrames i m) ∧
        (InstalledRoundCommit.roundFrames i m).length = 5) ∧
    (∀ (r : Nat) (hr : r < (p.logRounds.zip p.gateRounds).length),
      (InstalledRoundCommit.actualChain thash c p).get? r =
        some (OuterAdapter.roundCommitted thash
          (InstalledRoundCommit.concreteFinal thash
            (OuterInitial.derive thash c (Verifier.statement p)).state 0
            ((p.logRounds.zip p.gateRounds).take r)) r
          ((p.logRounds.zip p.gateRounds).get ⟨r, hr⟩).1
          ((p.logRounds.zip p.gateRounds).get ⟨r, hr⟩).2).digest) ∧
    (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).logPoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.logChallengeOf thash) ∧
    (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).gatePoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.gateChallengeOf thash) :=
  InstalledRoundCommit.round_digests_chain_after_prefix (roundBase e thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash c p rfl hdb

/-- (2) **THE LANES ARE CONCRETE SQUEEZES, WITH `hi` GONE.**
`InstalledRoundCommit.lanes_are_concrete` for the composed engine: the challenge
columns of the adopted `ConditionalSoundness.logLaneOf` and `gateLaneOf` ARE the
coordinatewise `OuterChallenge.reduceTriple` reductions of the run's own digest
chain, lifted by `OuterRound.lift`. The lane truth columns are still supplied
and the bad sets they index are still the adopted ones. -/
theorem composed_lanes_are_concrete (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile) (c₀ : Verifier.Config)
    (c : Verifier.Config) (p : Verifier.Proof) (logTruths gateTruths : List (List Element))
    (hdb : c.degreeBits ≤ 13) :
    (ConditionalSoundness.logLaneOf (composedEngine e gdec hash thash P c₀) c p logTruths).map
        ConditionalSoundness.LaneRound.challenge =
      (InstalledRoundCommit.actualChain thash c p).map
        (fun d => OuterRound.lift (InstalledRoundCommit.logChallengeOf thash d)) ∧
    (ConditionalSoundness.gateLaneOf (composedEngine e gdec hash thash P c₀) c p gateTruths).map
        ConditionalSoundness.LaneRound.challenge =
      (InstalledRoundCommit.actualChain thash c p).map
        (fun d => OuterRound.lift (InstalledRoundCommit.gateChallengeOf thash d)) :=
  InstalledRoundCommit.lanes_are_concrete (roundBase e thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash c p logTruths gateTruths rfl hdb

/-- (2) **THE SEAM IS INHABITED AT THE RUN'S OWN DIGESTS, WITH `hi` GONE.**
`InstalledRoundCommit.actual_digest_draw_encodes_run` for the composed engine.

WHAT THIS DOES NOT DO, verbatim from the sibling:
`JointChallengeSpace.DrawEncodesRun` is still a COORDINATE statement. No law,
uniform or otherwise, is attached to any coordinate, and half (B) of the
Fiat--Shamir reading is untouched. The shape hypotheses `hlr` and `hgr` are the
adopted `Verifier.shape` conjuncts. -/
theorem composed_actual_digest_draw_encodes_run (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (c : Verifier.Config) (p : Verifier.Proof)
    (logTruths gateTruths : List (List Element)) (hdb : c.degreeBits ≤ 13)
    (hlr : p.logRounds.length = c.degreeBits) (hgr : p.gateRounds.length = c.degreeBits) :
    JointChallengeSpace.DrawEncodesRun thash (composedEngine e gdec hash thash P c₀) c p
      logTruths gateTruths (InstalledRoundCommit.actualDigestDraw thash c p) :=
  InstalledRoundCommit.actual_digest_draw_encodes_run (roundBase e thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash c p logTruths gateTruths rfl hdb hlr hgr

/-- (2) **THE INDEX LANES ABSORB THE USED CLAIMS, UNCONDITIONALLY.**
`InstalledIndexSampler.sampled_indices_absorb_used_claims` carries a decode
hypothesis; `InstalledRoundCommit` discharged it under `hi` plus
`c.degreeBits ≤ 13`; here `hi` is gone too. The claim block is still the eight
adopted `InstalledIndexSampler.claimFrames`, both lanes still have length
`c.indexBits`, and the coordinates are still the reductions at counters
`3i, 3i+1, 3i+2` (log) and `3b+3i, +1, +2` (gate) of the post-claims digest. -/
theorem composed_sampled_indices_absorb_used_claims (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) :
    ∃ st, OuterAdapter.decode
        (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).transcript =
          some st ∧
      OuterAdapter.claimsCommitted thash st p.used =
        OuterInitial.absorbMessages thash st (InstalledIndexSampler.claimFrames p.used) ∧
      (InstalledIndexSampler.claimFrames p.used).length = 8 ∧
      (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).log.length =
        c.indexBits ∧
      (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).gate.length =
        c.indexBits ∧
      (∀ i, i < c.indexBits →
        (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).log.get? i =
          some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
            ⟨InstalledIndexSampler.indexDigest thash st p.used, 3 * i⟩)).toVerifier) ∧
      (∀ i, i < c.indexBits →
        (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).gate.get? i =
          some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
            ⟨InstalledIndexSampler.indexDigest thash st p.used,
              3 * c.indexBits + 3 * i⟩)).toVerifier) :=
  InstalledRoundCommit.sampled_indices_absorb_used_claims_unconditional (roundBase e thash P c₀)
    gdec hash (PinnedWhirProfile.pinnedParams P c₀) thash c p rfl hdb

/-- (2) The verifier's own index-length guard (Verifier.lean 420-421), satisfied
unconditionally by the composed engine under `c.degreeBits ≤ 13`. -/
theorem composed_index_lanes_have_index_bits_length (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) :
    (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).log.length =
      c.indexBits ∧
    (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).gate.length =
      c.indexBits :=
  InstalledRoundCommit.index_lanes_have_index_bits_length_unconditional (roundBase e thash P c₀)
    gdec hash (PinnedWhirProfile.pinnedParams P c₀) thash c p rfl hdb

/-! ## 3. Acceptance supplies the one remaining hypothesis -/

/-- (3) Acceptance under the composed engine yields the adopted envelope and
shape predicates, through `Integrated.accepted_preflights_and_original_verifier`
and the adopted `Verifier.verify_success_checks`. -/
theorem composed_acceptance_envelope_and_shape (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    Verifier.envelope c = true ∧ Verifier.shape pin c p = true := by
  obtain ⟨_, _, _, _, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier (composedEngine e gdec hash thash P c₀)
      gdec pin chain c p hacc
  have hall := Verifier.verify_success_checks
    (Integrated.modelEngine (composedEngine e gdec hash thash P c₀) gdec) pin chain c p hv
  exact ⟨hall.2.2.1, hall.2.2.2.2.1⟩

/-- (3) **ACCEPTANCE BOUNDS THE DEGREE.** `Verifier.envelope` demands
`c.degreeBits ≤ 13` (Verifier.lean 98), so the single hypothesis that section 2
still carries is supplied by acceptance itself. The round shape conjuncts come
from `Verifier.shape` (Verifier.lean 142). -/
theorem composed_acceptance_bounds_degree_bits (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    c.degreeBits ≤ 13 ∧ 0 < c.degreeBits ∧
    p.logRounds.length = c.degreeBits ∧ p.gateRounds.length = c.degreeBits := by
  obtain ⟨he, hs⟩ :=
    composed_acceptance_envelope_and_shape e gdec hash thash P c₀ pin chain c p hacc
  simp only [Verifier.envelope, decide_eq_true_eq] at he
  simp only [Verifier.shape, decide_eq_true_eq] at hs
  exact ⟨he.2.1, he.1, hs.2.2.2.2.2.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- (3) `composed_decoded_snapshot` and `composed_snapshots_always_decode` in
acceptance-conditioned form: the last hypothesis is gone, so an accepted call
under the composed engine has a decoding rounds snapshot outright, and the
`indexBits = 0` failure branch of `InstalledRoundCommit` is unreachable on it.
-/
theorem composed_accepted_snapshot_decodes (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    OuterAdapter.decode
        (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).transcript =
      some (InstalledRoundCommit.concreteFinal thash
        (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)) ∧
    OuterAdapter.decode
        (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).transcript ≠ none :=
  ⟨composed_decoded_snapshot e gdec hash thash P c₀ c p
      (composed_acceptance_bounds_degree_bits e gdec hash thash P c₀ pin chain c p hacc).1,
   (composed_snapshots_always_decode e gdec hash thash P c₀ c p
      (composed_acceptance_bounds_degree_bits e gdec hash thash P c₀ pin chain c p hacc).1).1⟩

/-- (3) `composed_round_digests_chain_after_prefix` in acceptance-conditioned
form: only the two `PinnedWhirProfile`-free conjuncts that section 6 quotes are
kept, since the full statement is available from the unconditioned theorem. -/
theorem composed_accepted_round_digests_chain_after_prefix (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    (OuterInitial.derive thash c (Verifier.statement p)).state.digest =
        (OuterInitial.absorbMessages thash OuterInitial.startState
          (CommitmentOrder.gateChallengeFrames c (Verifier.statement p))).digest ∧
    (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).length = 22 ∧
    (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).logPoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.logChallengeOf thash) ∧
    (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).gatePoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.gateChallengeOf thash) := by
  have h := composed_round_digests_chain_after_prefix e gdec hash thash P c₀ c p
    (composed_acceptance_bounds_degree_bits e gdec hash thash P c₀ pin chain c p hacc).1
  exact ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- (3) `composed_sampled_indices_absorb_used_claims` in acceptance-conditioned
form. -/
theorem composed_accepted_sampled_indices_absorb_used_claims (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ st, OuterAdapter.decode
        (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).transcript =
          some st ∧
      OuterAdapter.claimsCommitted thash st p.used =
        OuterInitial.absorbMessages thash st (InstalledIndexSampler.claimFrames p.used) ∧
      (InstalledIndexSampler.claimFrames p.used).length = 8 ∧
      (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).log.length =
        c.indexBits ∧
      (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).gate.length =
        c.indexBits ∧
      (∀ i, i < c.indexBits →
        (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).log.get? i =
          some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
            ⟨InstalledIndexSampler.indexDigest thash st p.used, 3 * i⟩)).toVerifier) ∧
      (∀ i, i < c.indexBits →
        (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).gate.get? i =
          some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
            ⟨InstalledIndexSampler.indexDigest thash st p.used,
              3 * c.indexBits + 3 * i⟩)).toVerifier) :=
  composed_sampled_indices_absorb_used_claims e gdec hash thash P c₀ c p
    (composed_acceptance_bounds_degree_bits e gdec hash thash P c₀ pin chain c p hacc).1

/-- (3) `composed_lanes_are_concrete` and
`composed_actual_digest_draw_encodes_run` in acceptance-conditioned form: the
shape hypotheses `hlr` and `hgr` of the latter are `Verifier.shape` conjuncts,
so acceptance discharges those too. -/
theorem composed_accepted_lanes_are_concrete (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) (logTruths gateTruths : List (List Element))
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    (ConditionalSoundness.logLaneOf (composedEngine e gdec hash thash P c₀) c p logTruths).map
        ConditionalSoundness.LaneRound.challenge =
      (InstalledRoundCommit.actualChain thash c p).map
        (fun d => OuterRound.lift (InstalledRoundCommit.logChallengeOf thash d)) ∧
    (ConditionalSoundness.gateLaneOf (composedEngine e gdec hash thash P c₀) c p gateTruths).map
        ConditionalSoundness.LaneRound.challenge =
      (InstalledRoundCommit.actualChain thash c p).map
        (fun d => OuterRound.lift (InstalledRoundCommit.gateChallengeOf thash d)) ∧
    JointChallengeSpace.DrawEncodesRun thash (composedEngine e gdec hash thash P c₀) c p
      logTruths gateTruths (InstalledRoundCommit.actualDigestDraw thash c p) := by
  obtain ⟨hdb, _, hlr, hgr⟩ :=
    composed_acceptance_bounds_degree_bits e gdec hash thash P c₀ pin chain c p hacc
  have hl := composed_lanes_are_concrete e gdec hash thash P c₀ c p logTruths gateTruths hdb
  exact ⟨hl.1, hl.2, composed_actual_digest_draw_encodes_run e gdec hash thash P c₀ c p
    logTruths gateTruths hdb hlr hgr⟩

/-- (3) The checked execution EXISTS for an accepted call, once the deployed
verification key's two byte-length facts are supplied. `OuterAdapter.InputSizes`
(OuterInitial.lean 498-500) needs `circuitDigest.length = 4` and
`publicInputs.length ≤ 256` -- both supplied by acceptance -- plus
`c.whirProtocolId.length = 64` and `c.whirSessionId.length = 32`, which
`Verifier.envelope` does NOT pin. They are therefore explicit hypotheses here,
and the headline of section 6 states the checked-execution conjunct in the
hypothesis-free implication form instead.

`PinnedWhirProfile.canonicalProfileCheck` cannot pin the two lengths either,
even though it is the one thing acceptance does say about the identifiers. It
forces `c.whirSessionId = P.sessionId` and
`c.whirProtocolId = P.tableProtocolId wp.numVariables`
(`PinnedWhirProfile.canonical_check_exact`), but `Profile.sessionId` and
`Profile.tableProtocolId` are ABSTRACT FIELDS of the profile record -- they are
the module's observation boundary, and `TableIsCanonical` carries no length
fact about either. So acceptance relocates the two hypotheses from the
configuration to the profile; it does not discharge them.
`composed_accepted_execution_exists_of_profile_lengths` states exactly that
relocated form. -/
theorem composed_accepted_execution_exists (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hpid : c.whirProtocolId.length = 64) (hsid : c.whirSessionId.length = 32)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ result, OuterAdapter.execute thash c p = some result ∧
      result.rounds = Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p ∧
      result.initial = (composedEngine e gdec hash thash P c₀).initialTranscript c p ∧
      result.indices.points = Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p ∧
      result.context = Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p := by
  obtain ⟨he, hs⟩ :=
    composed_acceptance_envelope_and_shape e gdec hash thash P c₀ pin chain c p hacc
  have hdb := (composed_acceptance_bounds_degree_bits e gdec hash thash P c₀ pin chain c p hacc).1
  have hen := he
  simp only [Verifier.envelope, decide_eq_true_eq] at hen
  have hsh := hs
  simp only [Verifier.shape, decide_eq_true_eq] at hsh
  have hsizes : OuterInitial.InputSizes c (Verifier.statement p) := by
    refine ⟨?_, ?_, hpid, hsid⟩
    · show p.circuitDigest.length = 4
      rw [hsh.2.2.1]; exact hen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · show p.publicInputs.length ≤ 256
      rw [hsh.2.2.2.1]; exact hen.2.2.2.2.2.2.1
  obtain ⟨result, hx, _, _, _, _, _⟩ :=
    OuterAdapter.source_sized_execution_exists thash pin c p he hs hsizes
  exact ⟨result, hx,
    composed_rounds_are_the_checked_execution e gdec hash thash P c₀ c p result hdb hx⟩

/-- (3) The same existential, with the two byte-length hypotheses RELOCATED
from the accepted configuration to the deployed profile. Acceptance forces
`c.whirSessionId = P.sessionId` and
`c.whirProtocolId = P.tableProtocolId (c.degreeBits + c.indexBits)` -- by
`PinnedWhirProfile.accepted_profile_is_canonical` followed by
`PinnedWhirProfile.canonical_check_exact`, whose last conjunct is at
`wp.numVariables`, and acceptance also gives
`wp.numVariables = c.degreeBits + c.indexBits`. So the two lengths need only be
assumed of the PROFILE. They are still assumed: `Profile.sessionId` and
`Profile.tableProtocolId` are abstract fields and `TableIsCanonical` says
nothing about their lengths. This theorem relocates the assumption; it does not
remove it. -/
theorem composed_accepted_execution_exists_of_profile_lengths (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hpid : (P.tableProtocolId (c.degreeBits + c.indexBits)).length = 64)
    (hsid : P.sessionId.length = 32)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ result, OuterAdapter.execute thash c p = some result ∧
      result.rounds = Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p ∧
      result.initial = (composedEngine e gdec hash thash P c₀).initialTranscript c p ∧
      result.indices.points = Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p ∧
      result.context = Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p := by
  obtain ⟨wp, _, hcan, _, _, _, _, hnv⟩ :=
    PinnedWhirProfile.accepted_profile_is_canonical P (outerInstalled e thash) gdec hash c₀ pin
      chain c p hacc
  obtain ⟨_, _, hsess, _, hprot⟩ := (PinnedWhirProfile.canonical_check_exact P c wp).mp hcan
  refine composed_accepted_execution_exists e gdec hash thash P c₀ pin chain c p ?_ ?_ hacc
  · rw [hprot, hnv]; exact hpid
  · rw [hsess]; exact hsid

/-! ## 4. The pinned profile and the WHIR tail, at the composed engine

The theorems of `PinnedWhirProfile` are quantified over an ARBITRARY base engine
`e`. Acceptance under `composedEngine` is a strictly different predicate from
acceptance under `PinnedWhirProfile.pinnedEngine P e …` -- four fields differ,
hence so do `derivedRounds`, `derivedIndices`, `derivedContext`, `logTerminal`
and `gateTerminal` -- so no acceptance fact is transported. Instead every adopted
statement is INSTANTIATED at `outerInstalled e thash`, the base for which the
pinned engine IS the composed engine (`composed_is_the_pinned_engine`, `rfl`). -/

/-- (4) **ACCEPTANCE FORCES A CANONICAL PROFILE**, for the composed engine.
`PinnedWhirProfile.accepted_profile_is_canonical` instantiated at
`outerInstalled e thash`: the accepted call exhibits the parameter record
decoded from ITS OWN configuration, shows it passed the source's canonical
check, and shows it is the record the composed engine's WHIR tail ran under. -/
theorem composed_accepted_profile_is_canonical (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ wp, PinnedWhirProfile.paramsOfConfig P c = some wp ∧
      PinnedWhirProfile.canonicalProfileCheck P c wp = true ∧
      PinnedWhirProfile.paramsOfConfig P c₀ = some wp ∧
      PinnedWhirProfile.pinnedParams P c₀ = wp ∧
      PinnedWhirProfile.minProfileVariables ≤ wp.numVariables ∧
      wp.numVariables ≤ PinnedWhirProfile.maxProfileVariables ∧
      wp.numVariables = c.degreeBits + c.indexBits :=
  PinnedWhirProfile.accepted_profile_is_canonical P (outerInstalled e thash) gdec hash c₀ pin
    chain c p hacc

/-- (4) **ROUND-ONE MERKLE AUTHENTICATION AT EACH OF THE THREE PINNED ROOTS**,
for the composed engine. `PinnedWhirProfile.pinned_round_one_authentication`
instantiated at `outerInstalled e thash`, with both of
`InstalledWhirTail`'s parameter hypotheses (`wp.rounds ≠ []` and
`0 < wp.inDomainSamples`) already discharged there from acceptance plus
`TableIsCanonical`. `hrow` -- the accepted call's packed dimension is one of the
two transcribed rows, `n = 10` or `n = 21` -- is the only parameter hypothesis
left; the other nineteen table rows ship as keccak digests only. -/
theorem composed_round_one_authentication (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (hT : PinnedWhirProfile.TableIsCanonical P) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (wq : VkParams)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ())
    (position : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root) :
    PinnedWhirProfile.paramsOfConfig P c = some wq ∧
    PinnedWhirProfile.pinnedParams P c₀ = wq ∧ 0 < wq.inDomainSamples ∧
    ∃ (r : WhirTail.Result) (opening : WhirIntermediate.Opening) (rows : List WhirRows.RawRow)
      (offset next : Nat),
      InstalledWhirTail.tailRun hash wq
        (Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p)
        p.whirTranscript p.whirHints = some r ∧
      InstalledWhirTail.RoundOneOpening hash wq (InstalledWhirTail.outerBytes p.whirHints)
        r opening ∧
      opening.indices ≠ [] ∧
      opening.groups.get? position = some rows ∧
      Merkle.verify hash (InstalledWhirTail.rootDigest root)
        (WhirConfigured.initialOpen wq).merkleDepth opening.indices
        (WhirRows.rowHashes hash rows) (InstalledWhirTail.outerBytes p.whirHints) offset
        = some next :=
  PinnedWhirProfile.pinned_round_one_authentication P hT (outerInstalled e thash) gdec hash c₀
    pin chain c p wq hrow hacc position root hpos

/-- (4) The concrete WHIR tail of the composed engine ran, at the pinned
parameter record, on the outer verifier's own pinned root triple, and its own
`WhirInitial` reading of the commitments -- both the actual and the bound copy
-- is that triple. `InstalledWhirTail.installed_acceptance_runs_the_concrete_tail`
instantiated at the tail base. -/
theorem composed_accepted_tail_runs_the_pinned_profile (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ r, InstalledWhirTail.tailRun hash (PinnedWhirProfile.pinnedParams P c₀)
          (Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p)
          p.whirTranscript p.whirHints = some r ∧
      (PinnedWhirProfile.pinnedParams P c₀).numVariables = c.degreeBits + c.indexBits ∧
      (Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p).roots =
        [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      r.retained.origin.initial.commitments.map (·.root) =
        [InstalledWhirTail.rootDigest pin.preprocessedRoot,
         InstalledWhirTail.rootDigest p.witnessRoot,
         InstalledWhirTail.rootDigest p.normInverseRoot] ∧
      r.retained.origin.initial.commitments.map (·.boundRoot) =
        [InstalledWhirTail.rootDigest pin.preprocessedRoot,
         InstalledWhirTail.rootDigest p.witnessRoot,
         InstalledWhirTail.rootDigest p.normInverseRoot] := by
  obtain ⟨r, hrun, hvars, hroots, hact, hbound, _⟩ :=
    InstalledWhirTail.installed_acceptance_runs_the_concrete_tail
      (outerInstalled (PinnedWhirProfile.pinnedBase P e c₀) thash) gdec hash
      (PinnedWhirProfile.pinnedParams P c₀) pin chain c p hacc
  exact ⟨r, hrun, hvars, hroots, hact, hbound⟩

/-- (4) **THE `parseWhir` BOUNDARY, STATED PRECISELY.** `parseWhir` is one of
the two fields still an observation, and this is exactly what acceptance forces
of it and what it therefore cannot do.

`Verifier.verifyWhir` (Verifier.lean 365-368) calls `e.parseWhir` and then
`Verifier.rootsAndClaimsMatch` (312-314), which compares BOTH of the parser's
root copies against `ctx.roots` and the parser's claims against
`ctx.expectedClaims`. Those context fields come from the OUTER verifier
(`Verifier.whirContext`, Verifier.lean 249-254), not from the parser. So an
accepted call forces the parser's two root lists to equal the triple the outer
verifier assembled, and INDEPENDENTLY the concrete tail's own `WhirInitial`
reading of the commitments equals the same triple
(`composed_accepted_tail_runs_the_pinned_profile`).

READ THE TRIPLE CAREFULLY. Only its FIRST entry is deployment-pinned:
`Verifier.shape` (Verifier.lean 136) forces `p.preprocessedRoot =
pin.preprocessedRoot`, which is why the statement writes `pin.preprocessedRoot`
there. `p.witnessRoot` and `p.normInverseRoot` are the PROOF'S OWN declared
commitments and are pinned by nothing. This theorem is therefore a CONSISTENCY
statement -- neither the parser nor the tail can swap in a root other than the
ones the outer verifier bound the context to -- and it is NOT a statement that
the witness roots are the "right" ones for any witness.

Consequently an abstract `parseWhir` can still make a good proof FAIL -- it is
an arbitrary function and may return `none` or a mismatching record -- but it
cannot substitute a DIFFERENT root. What is NOT claimed: `ParsedWhir` fields
that `rootsAndClaimsMatch` does not compare are unconstrained, and
`InstalledWhirTail.installedTail` ignores the parsed record entirely, so the
composed engine's WHIR content comes from `tailRun`, never from `parseWhir`. -/
theorem composed_parse_whir_cannot_pass_a_wrong_root (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ parsed r,
      e.parseWhir (Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p)
          p.whirTranscript p.whirHints = some parsed ∧
      parsed.actualRoots = [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      parsed.boundRoots = [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      Verifier.claimsMatch
        (Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p).expectedClaims
        parsed.claims = true ∧
      InstalledWhirTail.tailRun hash (PinnedWhirProfile.pinnedParams P c₀)
        (Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p)
        p.whirTranscript p.whirHints = some r ∧
      r.retained.origin.initial.commitments.map (·.root) =
        [InstalledWhirTail.rootDigest pin.preprocessedRoot,
         InstalledWhirTail.rootDigest p.witnessRoot,
         InstalledWhirTail.rootDigest p.normInverseRoot] ∧
      r.retained.origin.initial.commitments.map (·.boundRoot) =
        [InstalledWhirTail.rootDigest pin.preprocessedRoot,
         InstalledWhirTail.rootDigest p.witnessRoot,
         InstalledWhirTail.rootDigest p.normInverseRoot] := by
  obtain ⟨_, _, _, _, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier (composedEngine e gdec hash thash P c₀)
      gdec pin chain c p hacc
  have hw := (Verifier.verify_success_checks
    (Integrated.modelEngine (composedEngine e gdec hash thash P c₀) gdec) pin chain c p
      hv).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨parsed, hparse, hact, hbound, hclaims, _⟩ :=
    Verifier.whir_acceptance_requires_bound_statement
      (Integrated.modelEngine (composedEngine e gdec hash thash P c₀) gdec) _ p hw
  obtain ⟨r, hrun, _, hroots, hcr, hcb⟩ :=
    composed_accepted_tail_runs_the_pinned_profile e gdec hash thash P c₀ pin chain c p hacc
  exact ⟨parsed, r, hparse, hact.trans hroots, hbound.trans hroots, hclaims, hrun, hcr, hcb⟩

/-! ## 5. The public-input hash boundary -/

/-- (5) **THE 256-CAP DIVERGENCE IS CLOSED ON ACCEPTED CALLS**, for the composed
engine. `InstalledInitialTranscript.accepted_public_inputs_within_solidity_cap`
instantiated at `initialBase`. The other recorded divergence, the Solidity-side
canonical-range scans, has no typed counterpart and nothing here claims
anything about a raw word outside the field. -/
theorem composed_accepted_public_inputs_within_solidity_cap (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    p.publicInputs.length ≤ PublicInputHashBinding.maxPublicInputs ∧
    PublicInputHashBinding.rawPublicInputsHash (p.publicInputs.map Fin.val) =
      some ((composedEngine e gdec hash thash P c₀).publicInputsHash p.publicInputs) :=
  InstalledInitialTranscript.accepted_public_inputs_within_solidity_cap
    (initialBase e thash P c₀) gdec gdec hash (PinnedWhirProfile.pinnedParams P c₀) thash pin
    chain c p hacc

/-! ## 6. The composed headline -/

/-- **THE COMPOSED HEADLINE.** Everything the composition buys, collected from
ONE acceptance hypothesis under the composed engine, plus the two
`PinnedWhirProfile` assumptions that keccak's absence forces
(`TableIsCanonical P`, and that the accepted call's packed dimension is one of
the two transcribed table rows).

The conclusion is a right-nested conjunction of SIXTEEN top-level conjuncts,
grouped below into six themes.

The conjuncts, in order:

1. `c.degreeBits ≤ 13` -- the one hypothesis section 2 still carried, supplied
   by the adopted `Verifier.envelope` through `Verifier.verify_success_checks`.
2. THE PINNED PROFILE, AND ROUND ONE. The WHIR parameter record is the one
   decoded from the accepted configuration's own bytes, it is the record the
   tail ran under, it samples a positive number of in-domain queries, and for
   EVERY position of the outer verifier's pinned root triple
   `[pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot]` the round-one
   opening's rows are Merkle-authenticated against THAT root at the round-one
   depth.
3. THE OUTER ROUNDS. Whenever the adopted checked execution succeeds, the
   composed engine's rounds, initial transcript, index points and WHIR context
   ARE its four components; and unconditionally both point lists are the
   coordinatewise reductions of the run's own digest chain at counters `0` and
   `3`.
4. THE INDEX LANES. They are squeezed from a state that absorbed the eight
   `InstalledIndexSampler.claimFrames` of `p.used`, and both have length
   `c.indexBits`.
5. THE INITIAL TRANSCRIPT. It IS the adopted `OuterInitial` derivation
   (`TranscriptProvenance.DerivedInitial`, with NO hypothesis), and its state
   digest is the fold of the twenty-two-frame
   `CommitmentOrder.gateChallengeFrames` prefix over `OuterInitial.startState`.
6. THE PUBLIC INPUTS. Within the Solidity `MAX_PUBLIC_INPUTS_V2` cap, so the
   raw Solidity-side hash is defined and equals the typed sponge this engine
   computes.

THREE OF THE SIXTEEN ARE CONSTANTS, NOT CONSEQUENCES OF ACCEPTANCE. Top-level
conjuncts 13 and 14 -- that `(OuterInitial.derive thash c (Verifier.statement
p)).state.digest` is the fold of `CommitmentOrder.gateChallengeFrames` over
`OuterInitial.startState`, and that that frame list has length `22` -- hold for
EVERY `thash`, `c` and `p`, with no engine and no acceptance in sight; they are
facts about `OuterInitial.derive` and about the frame list's shape. The same is
true of `(InstalledIndexSampler.claimFrames p.used).length = 8`, carried inside
conjunct 9. They are here because the frame counts are the numbers a reader
wants next to the digest identity, not because acceptance produced them, and
they should not be read as anything acceptance forces.

EVERY CONJUNCT IS AN APPLICATION OF AN ADOPTED THEOREM. The only glue
is routing acceptance to `c.degreeBits ≤ 13` and instantiating each sibling at
its own base. Conjunct 3's checked-execution half is stated as an IMPLICATION
because `OuterAdapter.InputSizes` needs two verification-key byte lengths that
`Verifier.envelope` does not pin; `composed_accepted_execution_exists` supplies
the existential form from those two extra hypotheses.

WHAT IS NOT HERE: `parseWhir` and `configurationHash` are still observations
(see `composed_parse_whir_cannot_pass_a_wrong_root` for exactly what the first
can and cannot do); `TableIsCanonical` and the WHIR-bytes pin are keccak
idealisations, never proved; half (B) of the Fiat--Shamir reading is
unformalized; no sumcheck, WHIR or PCS soundness is claimed; nothing here is the
deployed system's soundness error, and nothing here says "125". -/
theorem composed_acceptance_summary (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (P : Profile)
    (hT : PinnedWhirProfile.TableIsCanonical P) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : VkParams)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hacc : Integrated.verify (composedEngine e gdec hash thash P c₀) gdec pin chain c p
      = .ok ()) :
    c.degreeBits ≤ 13 ∧
    PinnedWhirProfile.paramsOfConfig P c = some wq ∧
    PinnedWhirProfile.pinnedParams P c₀ = wq ∧
    0 < wq.inDomainSamples ∧
    (∀ (position : Nat) (root : Verifier.Root),
      [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root →
      ∃ (r : WhirTail.Result) (opening : WhirIntermediate.Opening) (rows : List WhirRows.RawRow)
        (offset next : Nat),
        InstalledWhirTail.tailRun hash wq
          (Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p)
          p.whirTranscript p.whirHints = some r ∧
        InstalledWhirTail.RoundOneOpening hash wq (InstalledWhirTail.outerBytes p.whirHints)
          r opening ∧
        opening.indices ≠ [] ∧
        opening.groups.get? position = some rows ∧
        Merkle.verify hash (InstalledWhirTail.rootDigest root)
          (WhirConfigured.initialOpen wq).merkleDepth opening.indices
          (WhirRows.rowHashes hash rows) (InstalledWhirTail.outerBytes p.whirHints) offset
          = some next) ∧
    (∀ result : OuterAdapter.Execution, OuterAdapter.execute thash c p = some result →
      result.rounds = Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p ∧
      result.initial = (composedEngine e gdec hash thash P c₀).initialTranscript c p ∧
      result.indices.points =
        Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p ∧
      result.context = Verifier.derivedContext (composedEngine e gdec hash thash P c₀) c p) ∧
    (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).logPoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.logChallengeOf thash) ∧
    (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).gatePoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.gateChallengeOf thash) ∧
    (∃ st, OuterAdapter.decode
        (Verifier.derivedRounds (composedEngine e gdec hash thash P c₀) c p).transcript =
          some st ∧
      OuterAdapter.claimsCommitted thash st p.used =
        OuterInitial.absorbMessages thash st (InstalledIndexSampler.claimFrames p.used) ∧
      (InstalledIndexSampler.claimFrames p.used).length = 8) ∧
    (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).log.length =
      c.indexBits ∧
    (Verifier.derivedIndices (composedEngine e gdec hash thash P c₀) c p).gate.length =
      c.indexBits ∧
    TranscriptProvenance.DerivedInitial thash (composedEngine e gdec hash thash P c₀) c p ∧
    (OuterInitial.derive thash c (Verifier.statement p)).state.digest =
      (OuterInitial.absorbMessages thash OuterInitial.startState
        (CommitmentOrder.gateChallengeFrames c (Verifier.statement p))).digest ∧
    (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).length = 22 ∧
    p.publicInputs.length ≤ PublicInputHashBinding.maxPublicInputs ∧
    PublicInputHashBinding.rawPublicInputsHash (p.publicInputs.map Fin.val) =
      some ((composedEngine e gdec hash thash P c₀).publicInputsHash p.publicInputs) := by
  have hdb := (composed_acceptance_bounds_degree_bits e gdec hash thash P c₀ pin chain c p hacc).1
  have hround := composed_round_one_authentication e gdec hash thash P hT c₀ pin chain c p wq
    hrow hacc
  have hchain := composed_round_digests_chain_after_prefix e gdec hash thash P c₀ c p hdb
  have hidx := composed_sampled_indices_absorb_used_claims e gdec hash thash P c₀ c p hdb
  obtain ⟨st, hst, hclaims, hcount, hlog, hgate, _, _⟩ := hidx
  have hpi := composed_accepted_public_inputs_within_solidity_cap e gdec hash thash P c₀ pin
    chain c p hacc
  refine ⟨hdb, (hround 0 pin.preprocessedRoot rfl).1, (hround 0 pin.preprocessedRoot rfl).2.1,
    (hround 0 pin.preprocessedRoot rfl).2.2.1,
    fun position root hpos => (hround position root hpos).2.2.2,
    fun result hx => composed_rounds_are_the_checked_execution e gdec hash thash P c₀ c p result
      hdb hx,
    hchain.2.2.2.2.1, hchain.2.2.2.2.2, ⟨st, hst, hclaims, hcount⟩, hlog, hgate,
    composed_initial_is_derived e gdec hash thash P c₀ c p, hchain.1, hchain.2.1, hpi.1, hpi.2⟩

/-! ## 7. Examples on the adopted fixture

The constant toy hash of `InstalledRoundCommit` and the adopted
`OuterAdapter.fixtureConfig` / `fixtureProof`. Shapes only: the evaluations are
`decide` on `fixtureConfig.degreeBits` and on list lengths. Nothing below is a
fixture of the deployed profile, and no digest space is enumerated. The profile
`P` and deployed configuration `c₀` are arbitrary, because none of these facts
touches `deploymentValid`. -/

/-- (7) The composed engine's `DerivedInitial` premise on the fixture is `rfl`
for every base engine, profile and deployed configuration -- the composition's
whole point, on concrete data. -/
theorem example_fixture_initial_is_derived (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (P : Profile)
    (c₀ : Verifier.Config) :
    TranscriptProvenance.DerivedInitial InstalledRoundCommit.toyHash
      (composedEngine e gdec hash InstalledRoundCommit.toyHash P c₀)
      OuterAdapter.fixtureConfig OuterAdapter.fixtureProof := rfl

/-- (7) The adopted fixture has ONE coupled round, so the concrete run's digest
chain has exactly one entry and both point lists have length one. Lengths only.
-/
theorem example_fixture_round_shape (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (P : Profile) (c₀ : Verifier.Config) :
    (Verifier.derivedRounds (composedEngine e gdec hash InstalledRoundCommit.toyHash P c₀)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).logPoint.length = 1 ∧
    (Verifier.derivedRounds (composedEngine e gdec hash InstalledRoundCommit.toyHash P c₀)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).gatePoint.length = 1 := by
  have hall := composed_round_digests_chain_after_prefix e gdec hash
    InstalledRoundCommit.toyHash P c₀ OuterAdapter.fixtureConfig OuterAdapter.fixtureProof
    (by decide)
  have hlen : (InstalledRoundCommit.actualChain InstalledRoundCommit.toyHash
      OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).length = 1 := by
    show (InstalledRoundCommit.concreteChain InstalledRoundCommit.toyHash _ 0 _).length = 1
    rw [InstalledRoundCommit.concrete_chain_length]
    rfl
  exact ⟨by rw [hall.2.2.2.2.1, List.length_map, hlen],
    by rw [hall.2.2.2.2.2, List.length_map, hlen]⟩

/-- (7) The fixture run's final snapshot DECODES -- it is a real forty-byte
snapshot -- so the `indexBits = 0` failure branch is not entered, with no
hypothesis left. -/
theorem example_fixture_snapshot_decodes (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (P : Profile) (c₀ : Verifier.Config) :
    ∃ st, OuterAdapter.decode
      (Verifier.derivedRounds (composedEngine e gdec hash InstalledRoundCommit.toyHash P c₀)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).transcript = some st :=
  (composed_snapshots_always_decode e gdec hash InstalledRoundCommit.toyHash P c₀
    OuterAdapter.fixtureConfig OuterAdapter.fixtureProof (by decide)).2

/-- (7) Both index lanes of the fixture have the configured length `1`, with no
decode hypothesis, no `CommitAgrees` hypothesis and no initial-transcript
hypothesis remaining. -/
theorem example_fixture_index_lanes (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (P : Profile) (c₀ : Verifier.Config) :
    (Verifier.derivedIndices (composedEngine e gdec hash InstalledRoundCommit.toyHash P c₀)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).log.length = 1 ∧
    (Verifier.derivedIndices (composedEngine e gdec hash InstalledRoundCommit.toyHash P c₀)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).gate.length = 1 :=
  composed_index_lanes_have_index_bits_length e gdec hash InstalledRoundCommit.toyHash P c₀
    OuterAdapter.fixtureConfig OuterAdapter.fixtureProof (by decide)

/-- (7) The composed engine's public-input hash on the fixture is the adopted
Poseidon sponge, four limbs wide, as `Integrated.evaluateGate` and
`Plonky2GateEvaluatorExt3.sol` 91-93 demand. -/
theorem example_fixture_public_input_hash (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : Profile) (c₀ : Verifier.Config) :
    (composedEngine e gdec hash thash P c₀).publicInputsHash
        OuterAdapter.fixtureProof.publicInputs =
      PublicInputHashBinding.hashNoPad OuterAdapter.fixtureProof.publicInputs ∧
    ((composedEngine e gdec hash thash P c₀).publicInputsHash
      OuterAdapter.fixtureProof.publicInputs).length = 4 :=
  ⟨rfl, PublicInputHashBinding.hash_length_discharged
    (composedEngine e gdec hash thash P c₀) OuterAdapter.fixtureProof rfl⟩

/-- (7) The two adversarial WHIR records of `PinnedWhirProfile`'s finding F3 --
the canonical row with `inDomainSamples` set to zero, and the one with every
intermediate round deleted -- still fail the canonical-profile check under the
composed engine's deployment predicate, for every configuration. Restated from
the adopted examples; nothing new is evaluated. -/
theorem example_forged_profiles_are_rejected (P : Profile)
    (hT : PinnedWhirProfile.TableIsCanonical P) (c : Verifier.Config) :
    PinnedWhirProfile.canonicalProfileCheck P c
        { PinnedWhirProfile.canonicalRow21 with inDomainSamples := 0 } = false ∧
    PinnedWhirProfile.canonicalProfileCheck P c
        { PinnedWhirProfile.canonicalRow10 with rounds := [], numRounds := 0 } = false :=
  ⟨PinnedWhirProfile.example_zero_sample_forgery_is_rejected P hT c,
   PinnedWhirProfile.example_round_deletion_forgery_is_rejected P hT c⟩

end Audit.Wire3.ComposedEngine
