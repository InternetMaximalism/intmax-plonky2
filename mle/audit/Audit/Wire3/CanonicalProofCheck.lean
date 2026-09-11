import Audit.Wire3.ExplicitEngine

/-!
# The canonical proof check: closing `ExplicitEngine`'s two-digest residue

## The milestone

`ExplicitEngine` ends with a named residue. Of the nineteen `Verifier.Config`
fields, seventeen are pinned to the deployed configuration by an accepted call
(thirteen through the configuration digest, `indexBits` through the envelope,
`gateRows` through the gate preflight, `whirProtocolId` and `whirSessionId`
through the canonical profile table). Two are not: `circuitDigest` and
`circuitConfigDigest`. `ExplicitEngine`'s section 5 says so in as many words --
they are "ATTACKER-CHOSEN TRANSCRIPT INPUTS" in the model, while in Solidity both
are fixed by constructor immutables.

This module supplies the missing pin and proves what it buys.
`pinnedProofEngine gdec hash thash khash P c₀` is `explicitEngine` with ONE field
changed -- `deploymentValid` becomes
`explicitDeployment P c₀ c && canonicalDigestPin c₀ c` -- and
`pinned_proof_is_explicit_with_stronger_deployment` states that as one `rfl`.
Every `ExplicitEngine` theorem therefore transfers
(`pinned_acceptance_is_explicit_acceptance` moves acceptance across, and
`pinned_acceptance_summary` restates the sixteen-conjunct headline), and three
new statements close the residue:

* `accepted_configuration_is_the_deployment` -- acceptance plus the deployment
  facts gives `c = c₀` (FULL configuration equality, all nineteen fields) or an
  explicit `khash` collision. `ExplicitEngine`'s
  `accepted_configuration_matches_the_deployment_up_to_the_residue` gave
  `core c = core c₀ ∧ c.indexBits = c₀.indexBits`; this is the same statement with
  the residue removed.
* `accepted_transcript_absorbs_deployed_digests` -- the two `OuterInitial` frames
  that carry the digests (frame 2, the field vector of the statement's circuit
  digest, OuterInitial.lean 71; frame 7, the bytes of the configuration's
  `circuitConfigDigest`, OuterInitial.lean 76) are the DEPLOYED values on every
  accepted call. The transcript degree of freedom `ExplicitEngine` names is closed.
* `no_free_config_field_remains` -- all nineteen fields listed one by one.

## What the pin models, and where the model bends

`_requireCanonicalProof` (MleVerifierV2.sol 551-587) runs PER CALL inside
`verify` (MleVerifierV2.sol 196-204, call at 200) and compares the proof's four
circuit-digest words against the constructor immutables `circuitDigest0..3`
(MleVerifierV2.sol 83-86, compared at 558-561). `circuitConfigDigest`
(MleVerifierV2.sol 78) is a separate immutable that the verifier ABSORBS into its
own transcript (MleVerifierV2.sol 430) -- so the absorbed value is the deployed
one by construction, never call-time data. Rust re-establishes both per call:
`proof.circuit_digest == vk.circuit_digest` (src/verifier_v2.rs 176-179) and
`vk.circuit_config_digest == circuit_config_digest_v2(..)` (src/verifier_v2.rs
156-165), the latter recomputed from the common data rather than merely compared.

`Verifier.Engine.deploymentValid` has type `Verifier.Config → Bool`: it takes NO
proof. The proof-side comparison of MleVerifierV2.sol 558-561 therefore cannot be
written there, and the adopted model has no engine field that reads a
`Verifier.Proof`. Two routes were available.

(a) TAKEN. `Verifier.shape` (Verifier.lean 135) already forces
`p.circuitDigest = c.circuitDigest` on every accepted call, so pinning
`c.circuitDigest = c₀.circuitDigest` in `deploymentValid` pins the PROOF's digest
transitively. `accepted_proof_circuit_digest_is_deployed` proves exactly that, and
`accepted_proof_digest_matches_the_four_immutables` states it word by word, which
is the shape of the source comparison.

(b) NOT TAKEN, and recorded as a limitation. A direct transcription of
MleVerifierV2.sol 558-561 -- a boundary predicate reading the proof and the
immutables together, with no detour through the configuration -- would need a
THIRTEENTH `Verifier.Engine` field, or a change to `Verifier.verify`'s signature.
Both are modifications of adopted modules and neither is made here.
`canonicalProofCheck c₀ c p` is defined anyway, as the faithful proof-side
predicate, and `canonical_proof_check_follows_from_the_pin` relates it to the
configuration-side pin through `shape`; it is a definition plus a bridge theorem,
not an installed guard.

## The pin under the `verifyCall` reading

`Verifier.verify` is a COMBINED boundary: it re-checks `envelope` and
`deploymentValid` in line, and its own docstring (Verifier.lean 405-410) says
these are NOT repeated Solidity runtime checks -- the Solidity-runtime reading is
`Verifier.verifyCall` PLUS an explicit deployment invariant. Under that reading
`canonicalDigestPin c₀ c` is NOT derivable from the call. `verifyCall` never
projects `deploymentValid`: replacing that field by an arbitrary predicate leaves
the call DEFINITIONALLY unchanged, which
`call_boundary_ignores_the_deployment_predicate` states as one `rfl`. The pin is
therefore an item OF the deployment invariant, never a conclusion drawn from a
call.

That placement is the faithful one, not a concealed weakening. In Solidity
`c.circuitDigest` and `c.circuitConfigDigest` correspond to the constructor
immutables `circuitDigest0 .. circuitDigest3` (MleVerifierV2.sol 83-86) and
`circuitConfigDigest` (MleVerifierV2.sol 78). Neither appears in the calldata
`VerificationConfig` (MleVerifierV2.sol 109-117), which carries only `circuit`,
`publicInputWireMap`, `kIs`, `subgroupGenPowers`, `gates` and `whir`: a caller
has no way to supply either value, and the contract has no way to change one after
construction. The invariant the pin expresses is thus "the immutables are the
deployed immutables" -- a statement about deployment state, of exactly the kind
`DeployedFacts` already collects, and not a runtime guard invented here. The one
comparison Solidity genuinely does run per call, MleVerifierV2.sol 558-561, is
reproduced on the CALL side alone: `Verifier.shape`'s third conjunct
(Verifier.lean 135) forces `p.circuitDigest = c.circuitDigest` on every accepted
call, and the invariant then supplies `c.circuitDigest = c₀.circuitDigest`. So the
module assumes NO runtime check that Solidity lacks; it records as a deployment
invariant precisely what Solidity obtains from immutability, and leaves the
per-call half where Solidity puts it.

## What this does NOT mean

**Nothing here is a hash assumption.** `hash`, `thash` and `khash` remain
ARBITRARY DETERMINISTIC FUNCTIONS; keccak is unmodelled in the adopted tree and
unmodelled here. Every "the accepted configuration is the deployed one" statement
still carries `ExplicitEngine.KhashCollision khash` as an explicit disjunct. The
count is exact: of the nineteen configuration fields, FIFTEEN carry that disjunct
-- the thirteen that reach `c₀` through `ExplicitEngine.encodeConfig`, plus
`indexBits` through the envelope and `gateRows` through the gate preflight, all
fifteen sitting inside the disjunction of
`ExplicitEngine.accepted_call_pins_everything_but_the_two_digests`. The remaining
FOUR are pinned WITHOUT it: `circuitDigest` and `circuitConfigDigest` by this
module's decidable pin, and `whirProtocolId` and `whirSessionId` by the canonical
profile check, whose shared `VkParams` record is obtained from the checked
`whirEncoding` pin inside `deploymentValid` rather than through `khash`.
`ids_pinned_without_collision` states that second pair on its own, with no
collision disjunct in its conclusion.

**The deployment facts are HYPOTHESES.** `DeployedFacts` bundles five statements
about the DEPLOYED configuration that nothing in the model establishes: its
envelope, its `Bounded` bound, that the pinned digest was computed from it
(MleVerifierV2.sol 149, 180), that it passes the canonical profile check
(MleVerifierV2.sol 151-153), and that its own `gateRows` is the decoded gate-list
length. They are the Lean counterpart of "the constructor ran and the deployer
pinned this configuration", which is not a theorem about calls.

**Everything `ExplicitEngine` left open stays open.** The WHIR tail is a MANUAL
hand-transcribed execution model, not a refinement proof. The R1b family (WHIR
proximity and sumcheck soundness), R2 (extraction / PCS extractability), R3, half
(B) of the Fiat--Shamir reading -- that the squeezes are uniform and independent
of the absorbed prefix, unformalized everywhere in the adopted tree and whose
weaker deterministic shadow is REFUTED for a general deterministic hash by
`CommitmentOrder.separation_fails_for_a_deterministic_hash` -- circuit truth, and
Rust/Yul/Solidity refinement all remain OPEN. Closing the transcript degree of
freedom removes an adversary's freedom to CHOOSE the absorbed digests; it says
nothing about what absorbing them accomplishes.

**`PinnedWhirProfile.TableIsCanonical` is still an ASSUMPTION**, carried visibly
by each statement that needs it, and transcribed for `n ∈ {10, 21}` ONLY; the
other nineteen table rows ship as keccak digests and are not modelled.

**The deployment check is SOLIDITY-ONLY semantics.** `ExplicitEngine`'s header
says it: `explicitDeployment` models the Solidity runtime path, and the Rust entry
point `mle_verify_v2` (src/verifier_v2.rs 57-175) re-validates on every call what
the Solidity constructor validated once -- the coset shifts (120-123), the
canonical squared subgroup-generator powers (130-146), the gate metadata against
`collect_gate_info_v2` (148-149), the wire-map row/column bounds (150-155), the
`circuit_config_digest` RECOMPUTATION (156-165) and the WHIR identifiers
(167-175). This module adds the two digest COMPARISONS, not the recomputation:
`circuitConfigDigest` is pinned to the deployed value, never re-derived from the
circuit. Adding the comparison does not make `explicitDeployment` a model of the
Rust boundary.

**The four-word comparison is modelled on canonical field elements.** Solidity
compares four raw `uint64` immutables against `proof.circuitDigest[0..3]`, which
are `uint256` calldata words; the Lean `Verifier.Config.circuitDigest` and
`Verifier.Proof.circuitDigest` are `List Verifier.Base = List (Fin modulus)`, so a
non-reduced or oversized word is NOT REPRESENTABLE in the model and the length
constraint `CIRCUIT_DIGEST_LENGTH_V2 = 4` (MleVerifierV2.sol 557) arrives from
`Verifier.envelope` rather than from the proof boundary. That is the one place
where the transcription of MleVerifierV2.sol 557-561 is a mirror rather than a
copy.

The direction of that mirror is the SAFE one, and Solidity's own constructor says
why. `_validateConfiguration` (MleVerifierV2.sol 490, called from the constructor
at 145) takes the four digest words as `uint64[4] memory digest` and rejects the
deployment outright if any of them is out of range -- `if (uint256(digest[i]) >=
BASE_FIELD_MODULUS_V2) revert InvalidMleVerifierConfiguration();`
(MleVerifierV2.sol 514-516). The immutables `circuitDigest0 .. circuitDigest3` are
therefore CANONICAL field elements on any deployment that exists at all, so the
equality of MleVerifierV2.sol 558-561 can only ever be satisfied by four canonical
proof words: a non-reduced calldata word is compared against a canonical immutable
and reverts. The `List (Fin modulus)` model therefore drops only inputs Solidity
already reverts on -- every proof Solidity ACCEPTS has canonical digest words and
is representable, while some proofs Solidity rejects cannot be written down at
all. The modelled accept set UNDER-approximates the Solidity accept set, which is
the safe direction for statements of the form "every accepted call has property
X": no Solidity-accepted call escapes the conclusions proved here through
unrepresentability.

Nothing here is a gas, exception-order or bytecode claim; `Verifier.verify` is
still a manual success-boundary model; `encodeConfig` is still a mirror with the
three departures `ExplicitEngine` lists. The wire-v3 WHIR profile this tree models
is the approximately 100-bit design point. No figure in this module is a security
level, nothing here is the deployed system's soundness error, and in particular
nothing here says "125".
-/

namespace Audit.Wire3.CanonicalProofCheck

open Audit.Wire3

abbrev Profile := PinnedWhirProfile.Profile

abbrev VkParams := InstalledWhirTail.VkParams

/-! ## 1. The two deployed digests

The pair of immutables this module pins, read off the deployed configuration `c₀`
exactly as `ExplicitEngine.explicitDeployment` reads `c₀.whirEncoding`.

* `circuitDigest` -- `uint64 public immutable circuitDigest0 .. circuitDigest3`
  (MleVerifierV2.sol 83-86), compared against `proof.circuitDigest[0..3]` at
  MleVerifierV2.sol 558-561 inside `_requireCanonicalProof`, itself called per
  call at MleVerifierV2.sol 200. Rust: `proof.circuit_digest == vk.circuit_digest`
  (src/verifier_v2.rs 176-179), with the shape check at src/verifier_v2.rs 79-83.
  Lean type: `List Verifier.Base`, length four by `Verifier.envelope`.
* `circuitConfigDigest` -- `bytes32 public immutable circuitConfigDigest`
  (MleVerifierV2.sol 78), absorbed into the verifier's transcript at
  MleVerifierV2.sol 430. Rust recomputes it (`circuit_config_digest_v2`,
  src/vk_v2.rs 334-345) and compares at src/verifier_v2.rs 156-165. Lean type:
  `Verifier.Root`, absorbed by `OuterInitial.baseMessages` frame 7.
-/

structure DeployedDigests where
  circuitDigest : List Verifier.Base
  circuitConfigDigest : Verifier.Root
  deriving DecidableEq

def deployedDigests (c : Verifier.Config) : DeployedDigests :=
  ⟨c.circuitDigest, c.circuitConfigDigest⟩

/-- The configuration-side pin: the two residue fields of `ExplicitEngine` equal
the deployed ones. This is what `deploymentValid` can express, because it takes a
`Verifier.Config` and nothing else. -/
def canonicalDigestPin (c₀ c : Verifier.Config) : Bool :=
  decide (c.circuitDigest = c₀.circuitDigest ∧ c.circuitConfigDigest = c₀.circuitConfigDigest)

/-- The faithful proof-side predicate of MleVerifierV2.sol 558-561 together with
the transcript immutable of MleVerifierV2.sol 430: the PROOF's circuit digest is
the deployed one, and the configuration's `circuitConfigDigest` is the deployed
one. It is a definition and a bridge, not an installed guard -- see route (b) in
the header. -/
def canonicalProofCheck (c₀ c : Verifier.Config) (p : Verifier.Proof) : Bool :=
  decide (p.circuitDigest = c₀.circuitDigest ∧ c.circuitConfigDigest = c₀.circuitConfigDigest)

theorem canonical_digest_pin_exact (c₀ c : Verifier.Config) :
    canonicalDigestPin c₀ c = true ↔
      c.circuitDigest = c₀.circuitDigest ∧ c.circuitConfigDigest = c₀.circuitConfigDigest := by
  simp [canonicalDigestPin]

theorem canonical_proof_check_exact (c₀ c : Verifier.Config) (p : Verifier.Proof) :
    canonicalProofCheck c₀ c p = true ↔
      p.circuitDigest = c₀.circuitDigest ∧ c.circuitConfigDigest = c₀.circuitConfigDigest := by
  simp [canonicalProofCheck]

theorem canonical_pin_is_digest_equality (c₀ c : Verifier.Config) :
    canonicalDigestPin c₀ c = true ↔ deployedDigests c = deployedDigests c₀ := by
  rw [canonical_digest_pin_exact]
  constructor
  · intro h; simp [deployedDigests, h.1, h.2]
  · intro h
    exact ⟨congrArg DeployedDigests.circuitDigest h, congrArg DeployedDigests.circuitConfigDigest h⟩

/-- **ROUTE (a) IN ONE LINE.** `Verifier.shape` already ties the proof's circuit
digest to the configuration's (Verifier.lean 135), so the configuration-side pin
delivers the proof-side comparison. This is why `deploymentValid`'s missing proof
argument costs nothing under acceptance. -/
theorem canonical_proof_check_follows_from_the_pin (c₀ c : Verifier.Config)
    (pin : Verifier.Pinned) (p : Verifier.Proof) (hshape : Verifier.shape pin c p = true)
    (hpin : canonicalDigestPin c₀ c = true) : canonicalProofCheck c₀ c p = true := by
  simp only [Verifier.shape, decide_eq_true_eq] at hshape
  rcases (canonical_digest_pin_exact c₀ c).mp hpin with ⟨hcd, hccd⟩
  exact (canonical_proof_check_exact c₀ c p).mpr ⟨hshape.2.2.1.trans hcd, hccd⟩

/-- **THE SIGNATURE EXHIBIT FOR ROUTE (b).** The engine's deployment observation
is a predicate on configurations alone; there is no `Verifier.Proof` in its type,
which is precisely why MleVerifierV2.sol 558-561 cannot be transcribed into it.
This states the type and nothing else. -/
theorem deployment_valid_is_a_configuration_predicate (e : Verifier.Engine) :
    (Verifier.Engine.deploymentValid e : Verifier.Config → Bool) = e.deploymentValid := rfl

/-- **WHY THE PIN IS AN INVARIANT AND NOT A CONCLUSION.** `Verifier.verifyCall` --
the Solidity-runtime half of the boundary, per the `Verifier.verify` docstring
(Verifier.lean 405-410) -- never projects `deploymentValid`: swapping that field
for an ARBITRARY predicate leaves the call definitionally unchanged. No statement
about `verifyCall` alone can therefore produce `canonicalDigestPin c₀ c`, and the
pin has to be carried by the explicit deployment invariant, exactly as the header
says. In Solidity the same fact is the observation that the two digests are
constructor immutables absent from the calldata `VerificationConfig`
(MleVerifierV2.sol 78, 83-86 against 109-117). -/
theorem call_boundary_ignores_the_deployment_predicate (e : Verifier.Engine)
    (d : Verifier.Config → Bool) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) :
    Verifier.verifyCall { e with deploymentValid := d } pin chain c p =
      Verifier.verifyCall e pin chain c p := rfl

/-! ## 2. The engine

One field of `ExplicitEngine.explicitEngine` changes. `canonicalDeployment` is
`explicitDeployment` -- conjunct (i), the WHIR-bytes pin, and conjunct (ii),
`PinnedWhirProfile.profileOk` -- conjoined with the new digest pin. -/

def canonicalDeployment (P : Profile) (c₀ : Verifier.Config) : Verifier.Config → Bool :=
  fun c => ExplicitEngine.explicitDeployment P c₀ c && canonicalDigestPin c₀ c

def pinnedProofEngine (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) : Verifier.Engine :=
  { ExplicitEngine.explicitEngine gdec hash thash khash P c₀ with
      deploymentValid := canonicalDeployment P c₀ }

theorem canonical_deployment_exact (P : Profile) (c₀ c : Verifier.Config) :
    canonicalDeployment P c₀ c = true ↔
      (c.whirEncoding = c₀.whirEncoding ∧ PinnedWhirProfile.profileOk P c = true) ∧
      (c.circuitDigest = c₀.circuitDigest ∧
        c.circuitConfigDigest = c₀.circuitConfigDigest) := by
  simp only [canonicalDeployment, Bool.and_eq_true]
  rw [ExplicitEngine.explicit_deployment_exact, canonical_digest_pin_exact]

/-- **3(a) THE IDENTITY.** The engine is `explicitEngine` with `deploymentValid`
replaced and nothing else touched, as one `rfl`. No new observation, no new
parameter beyond the deployed configuration `explicitEngine` already carries. -/
theorem pinned_proof_is_explicit_with_stronger_deployment (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    pinnedProofEngine gdec hash thash khash P c₀ =
      { ExplicitEngine.explicitEngine gdec hash thash khash P c₀ with
          deploymentValid := fun c =>
            ExplicitEngine.explicitDeployment P c₀ c && canonicalDigestPin c₀ c } := rfl

theorem pinned_engine_twelve_fields (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) :
    (pinnedProofEngine gdec hash thash khash P c₀).configurationHash =
      ExplicitEngine.concreteConfigurationHash khash ∧
    (pinnedProofEngine gdec hash thash khash P c₀).deploymentValid = canonicalDeployment P c₀ ∧
    (pinnedProofEngine gdec hash thash khash P c₀).initialObservation =
      InstalledInitialTranscript.concreteInitialObservation thash ∧
    (pinnedProofEngine gdec hash thash khash P c₀).commitRound =
      InstalledRoundCommit.concreteCommitRound thash ∧
    (pinnedProofEngine gdec hash thash khash P c₀).sampleIndices =
      InstalledIndexSampler.concreteSampleIndices thash ∧
    (pinnedProofEngine gdec hash thash khash P c₀).foldClaim = Connections.packedFold ∧
    (pinnedProofEngine gdec hash thash khash P c₀).normEvaluation = Norm.normEvaluation ∧
    (pinnedProofEngine gdec hash thash khash P c₀).publicInputsHash =
      PublicInputHashBinding.hashNoPad ∧
    (pinnedProofEngine gdec hash thash khash P c₀).gateEvaluation =
      (fun c wires constants publicHash alpha =>
        (Integrated.evaluateGate gdec c wires constants publicHash alpha).getD Verifier.zero) ∧
    (pinnedProofEngine gdec hash thash khash P c₀).eqEvaluation = Norm.eqEvaluation ∧
    (pinnedProofEngine gdec hash thash khash P c₀).parseWhir =
      InstalledWhirParse.concreteParseWhir hash (PinnedWhirProfile.pinnedParams P c₀) ∧
    (pinnedProofEngine gdec hash thash khash P c₀).whirTail =
      InstalledWhirTail.installedTail hash (PinnedWhirProfile.pinnedParams P c₀) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pinned_engine_is_its_own_model_engine (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    Integrated.modelEngine (pinnedProofEngine gdec hash thash khash P c₀) gdec =
      pinnedProofEngine gdec hash thash khash P c₀ := rfl

/-- The strengthening is genuine in one direction only: the pinned deployment
implies the explicit one, never the converse. -/
theorem pinned_deployment_implies_the_explicit_one (P : Profile) (c₀ c : Verifier.Config)
    (h : canonicalDeployment P c₀ c = true) :
    ExplicitEngine.explicitDeployment P c₀ c = true :=
  (ExplicitEngine.explicit_deployment_exact P c₀ c).mpr ((canonical_deployment_exact P c₀ c).mp h).1

/-! ## 3. Transfer: every `ExplicitEngine` result, at the pinned engine

Acceptance under the pinned engine implies acceptance under the explicit one,
because the two engines differ only in `deploymentValid` and the pinned predicate
is the stronger. The argument is the one
`ExplicitEngine.weak_acceptance_gives_full_acceptance` runs in the opposite
direction: `Verifier.verifyCall` never reads `deploymentValid`, so
`Verifier.checked_boundary_agrees_with_call` moves an accepted call between the
two checked boundaries. -/

theorem pinned_acceptance_is_explicit_acceptance (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    Integrated.verify (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec pin chain
      c p = .ok () := by
  obtain ⟨norm, gate, hn, hg, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  have hs := Verifier.verify_success_checks _ pin chain c p hv
  have henv : Verifier.envelope c = true := hs.2.2.1
  have hdep : canonicalDeployment P c₀ c = true := hs.2.2.2.1
  have hexp : ExplicitEngine.explicitDeployment P c₀ c = true :=
    pinned_deployment_implies_the_explicit_one P c₀ c hdep
  have hcall := (Verifier.checked_boundary_agrees_with_call
    (Integrated.modelEngine (pinnedProofEngine gdec hash thash khash P c₀) gdec) pin chain c p
    henv hdep) ▸ hv
  have hcall2 : Verifier.verifyCall
      (Integrated.modelEngine (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec)
      pin chain c p = .ok () := hcall
  have hfull : Verifier.verify
      (Integrated.modelEngine (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec)
      pin chain c p = .ok () :=
    Verifier.call_acceptance_yields_checked_acceptance _ pin chain c p henv hexp hcall2
  have hn' : Integrated.normResult
      (Integrated.modelEngine (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec)
      c p = some norm := hn
  have hg' : Integrated.gateResult
      (Integrated.modelEngine (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec)
      gdec c p = some gate := hg
  simp only [Integrated.verify, hn', hg']
  exact hfull

/-- `ExplicitEngine.explicit_acceptance_summary` at the pinned engine. NO NEW
PROOF CONTENT: the sixteen conjuncts are the adopted ones, with the caveats
unchanged, including the three conjuncts that are CONSTANTS rather than
consequences of acceptance (the two `OuterInitial.derive` digest facts and the
frame-list lengths). -/
theorem pinned_acceptance_summary (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (hT : PinnedWhirProfile.TableIsCanonical P) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : VkParams)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
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
          (Verifier.derivedContext (pinnedProofEngine gdec hash thash khash P c₀) c p)
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
      result.rounds = Verifier.derivedRounds (pinnedProofEngine gdec hash thash khash P c₀) c p ∧
      result.initial = (pinnedProofEngine gdec hash thash khash P c₀).initialTranscript c p ∧
      result.indices.points =
        Verifier.derivedIndices (pinnedProofEngine gdec hash thash khash P c₀) c p ∧
      result.context = Verifier.derivedContext (pinnedProofEngine gdec hash thash khash P c₀) c p) ∧
    (Verifier.derivedRounds (pinnedProofEngine gdec hash thash khash P c₀) c p).logPoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.logChallengeOf thash) ∧
    (Verifier.derivedRounds (pinnedProofEngine gdec hash thash khash P c₀) c p).gatePoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.gateChallengeOf thash) ∧
    (∃ st, OuterAdapter.decode
        (Verifier.derivedRounds (pinnedProofEngine gdec hash thash khash P c₀) c p).transcript =
          some st ∧
      OuterAdapter.claimsCommitted thash st p.used =
        OuterInitial.absorbMessages thash st (InstalledIndexSampler.claimFrames p.used) ∧
      (InstalledIndexSampler.claimFrames p.used).length = 8) ∧
    (Verifier.derivedIndices (pinnedProofEngine gdec hash thash khash P c₀) c p).log.length =
      c.indexBits ∧
    (Verifier.derivedIndices (pinnedProofEngine gdec hash thash khash P c₀) c p).gate.length =
      c.indexBits ∧
    TranscriptProvenance.DerivedInitial thash (pinnedProofEngine gdec hash thash khash P c₀) c p ∧
    (OuterInitial.derive thash c (Verifier.statement p)).state.digest =
      (OuterInitial.absorbMessages thash OuterInitial.startState
        (CommitmentOrder.gateChallengeFrames c (Verifier.statement p))).digest ∧
    (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).length = 22 ∧
    p.publicInputs.length ≤ PublicInputHashBinding.maxPublicInputs ∧
    PublicInputHashBinding.rawPublicInputsHash (p.publicInputs.map Fin.val) =
      some ((pinnedProofEngine gdec hash thash khash P c₀).publicInputsHash p.publicInputs) :=
  ExplicitEngine.explicit_acceptance_summary gdec hash thash khash P hT c₀ pin chain c p wq hrow
    (pinned_acceptance_is_explicit_acceptance gdec hash thash khash P c₀ pin chain c p hacc)

theorem pinned_accepted_profile_is_canonical (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ wp, PinnedWhirProfile.paramsOfConfig P c = some wp ∧
      PinnedWhirProfile.canonicalProfileCheck P c wp = true ∧
      PinnedWhirProfile.paramsOfConfig P c₀ = some wp ∧
      PinnedWhirProfile.pinnedParams P c₀ = wp ∧
      PinnedWhirProfile.minProfileVariables ≤ wp.numVariables ∧
      wp.numVariables ≤ PinnedWhirProfile.maxProfileVariables ∧
      wp.numVariables = c.degreeBits + c.indexBits :=
  ExplicitEngine.explicit_accepted_profile_is_canonical gdec hash thash khash P c₀ pin chain c p
    (pinned_acceptance_is_explicit_acceptance gdec hash thash khash P c₀ pin chain c p hacc)

/-- The same transfer at `Verifier.verify` rather than `Integrated.verify`, for
the adopted results stated at the bare success boundary. -/
theorem pinned_verify_is_explicit_verify (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Verifier.verify (pinnedProofEngine gdec hash thash khash P c₀) pin chain c p = .ok ()) :
    Verifier.verify (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) pin chain c p
      = .ok () := by
  have hs := Verifier.verify_success_checks _ pin chain c p h
  have henv : Verifier.envelope c = true := hs.2.2.1
  have hdep : canonicalDeployment P c₀ c = true := hs.2.2.2.1
  have hexp : ExplicitEngine.explicitDeployment P c₀ c = true :=
    pinned_deployment_implies_the_explicit_one P c₀ c hdep
  have hcall := (Verifier.checked_boundary_agrees_with_call
    (pinnedProofEngine gdec hash thash khash P c₀) pin chain c p henv hdep) ▸ h
  have hcall2 : Verifier.verifyCall (ExplicitEngine.explicitEngine gdec hash thash khash P c₀)
      pin chain c p = .ok () := hcall
  exact Verifier.call_acceptance_yields_checked_acceptance _ pin chain c p henv hexp hcall2

theorem pinned_accepted_verify_first_root_is_pinned (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Verifier.verify (pinnedProofEngine gdec hash thash khash P c₀) pin chain c p = .ok ()) :
    (InstalledWhirTail.outerBytes p.whirTranscript).take 32 =
      (Transcript.le 32 pin.preprocessedRoot.val).reverse :=
  ExplicitEngine.explicit_accepted_verify_first_root_is_pinned gdec hash thash khash P c₀ pin
    chain c p (pinned_verify_is_explicit_verify gdec hash thash khash P c₀ pin chain c p h)

/-! ## 4. The two digests under acceptance

The pin is a decidable equality inside `deploymentValid`, which
`Verifier.verify_success_checks` hands back on every accepted call. No collision
disjunct appears in this section: the configuration guard is not involved. -/

theorem accepted_digests_are_the_deployed_ones (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    c.circuitDigest = c₀.circuitDigest ∧ c.circuitConfigDigest = c₀.circuitConfigDigest := by
  obtain ⟨-, -, -, -, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  have hs := Verifier.verify_success_checks _ pin chain c p hv
  have hdep : canonicalDeployment P c₀ c = true := hs.2.2.2.1
  exact ((canonical_deployment_exact P c₀ c).mp hdep).2

/-- **ROUTE (a), DISCHARGED.** The PROOF's circuit digest is the deployed one on
every accepted call -- the conclusion MleVerifierV2.sol 558-561 draws directly and
this model draws through `Verifier.shape`. The length four is
`CIRCUIT_DIGEST_LENGTH_V2` (MleVerifierV2.sol 557), supplied here by
`Verifier.envelope`. -/
theorem accepted_proof_circuit_digest_is_deployed (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    p.circuitDigest = c₀.circuitDigest ∧ p.circuitDigest.length = 4 ∧
      canonicalProofCheck c₀ c p = true := by
  obtain ⟨-, -, -, -, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  have hs := Verifier.verify_success_checks _ pin chain c p hv
  have hdep : canonicalDeployment P c₀ c = true := hs.2.2.2.1
  have hshape : Verifier.shape pin c p = true := hs.2.2.2.2.1
  have henv : Verifier.envelope c = true := hs.2.2.1
  have hpin : canonicalDigestPin c₀ c = true :=
    (canonical_digest_pin_exact c₀ c).mpr ((canonical_deployment_exact P c₀ c).mp hdep).2
  have hcheck := canonical_proof_check_follows_from_the_pin c₀ c pin p hshape hpin
  have hpd := ((canonical_proof_check_exact c₀ c p).mp hcheck).1
  simp only [Verifier.envelope, decide_eq_true_eq] at henv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlen, -, -, -⟩ := henv
  simp only [Verifier.shape, decide_eq_true_eq] at hshape
  exact ⟨hpd, by rw [hshape.2.2.1, hlen], hcheck⟩

/-- The same conclusion in the SHAPE of the source comparison: four words, one at
a time, against `circuitDigest0 .. circuitDigest3` (MleVerifierV2.sol 83-86,
compared at 558-561). The model's words are canonical field elements, not raw
`uint64`s -- see the header. -/
theorem accepted_proof_digest_matches_the_four_immutables (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    p.circuitDigest.length = 4 ∧
    p.circuitDigest.get? 0 = c₀.circuitDigest.get? 0 ∧
    p.circuitDigest.get? 1 = c₀.circuitDigest.get? 1 ∧
    p.circuitDigest.get? 2 = c₀.circuitDigest.get? 2 ∧
    p.circuitDigest.get? 3 = c₀.circuitDigest.get? 3 := by
  obtain ⟨hpd, hlen, -⟩ := accepted_proof_circuit_digest_is_deployed gdec hash thash khash P c₀
    pin chain c p hacc
  exact ⟨hlen, by rw [hpd], by rw [hpd], by rw [hpd], by rw [hpd]⟩

/-- **3(b) THE TRANSCRIPT DEGREE OF FREEDOM IS CLOSED.** `OuterInitial.baseMessages`
absorbs the circuit digest at frame 2 (OuterInitial.lean 71, through
`Verifier.statement`) and the configuration digest at frame 7 (OuterInitial.lean
76). Under acceptance both are the DEPLOYED values, which is what Solidity gets
for free from its immutables (MleVerifierV2.sol 430 absorbs the immutable, and
558-561 forces the proof's digest to be the immutable). What this does NOT say:
that absorbing the right digests achieves anything. That belongs to half (B) of
the Fiat--Shamir reading, which is unformalized here and everywhere in the adopted
tree. -/
theorem accepted_transcript_absorbs_deployed_digests (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    (Verifier.statement p).circuitDigest = c₀.circuitDigest ∧
    c.circuitConfigDigest = c₀.circuitConfigDigest ∧
    (OuterInitial.baseMessages c (Verifier.statement p)).get? 2 =
      some (OuterInitial.fieldVecMessage c₀.circuitDigest) ∧
    (OuterInitial.baseMessages c (Verifier.statement p)).get? 7 =
      some (OuterInitial.byteMessage (OuterInitial.rootBytes c₀.circuitConfigDigest)) := by
  obtain ⟨hpd, -, -⟩ := accepted_proof_circuit_digest_is_deployed gdec hash thash khash P c₀
    pin chain c p hacc
  obtain ⟨-, hccd⟩ := accepted_digests_are_the_deployed_ones gdec hash thash khash P c₀ pin
    chain c p hacc
  have hstmt : (Verifier.statement p).circuitDigest = c₀.circuitDigest := hpd
  refine ⟨hstmt, hccd, ?_, ?_⟩
  · have h2 := OuterInitial.circuit_digest_is_actual_field_vector c (Verifier.statement p)
    rw [h2, hstmt]
    rfl
  · have h7 := OuterInitial.config_digest_frame_uses_fixed_config c (Verifier.statement p)
    rw [h7, hccd]
    rfl

/-! ## 5. The deployment facts, and full configuration equality

`DeployedFacts` collects the five statements about the DEPLOYED configuration that
this development cannot prove and does not assume silently. Each is a fact about
what a deployer pinned, not about what a caller submits:

* `envelope` -- `Verifier.envelope c₀`, the numeric caps `_validateConfiguration`
  enforces in the constructor (MleVerifierV2.sol 492-502);
* `bounded` -- `ExplicitEngine.Bounded c₀`, the `uint256` fit of section 2 there;
* `pinnedDigest` -- `verificationConfigDigest = keccak256(abi.encode(config_))`
  (MleVerifierV2.sol 149, assigned 180), the Lean form being
  `pin.configDigest = khash (encodeConfig c₀)`;
* `canonicalProfile` -- `CanonicalWhirProfileV2.validateCanonical` on the deployed
  configuration (MleVerifierV2.sol 151-153). This is what pins `whirProtocolId`
  and `whirSessionId` to `c₀` rather than merely to the table;
* `decodedGateRows` -- the deployed `gateRows` is the decoded gate-list length,
  the deployment-side counterpart of what the gate preflight forces on every
  accepted call.
-/

structure DeployedFacts (gdec : Integrated.DecodeGates)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (pin : Verifier.Pinned)
    (c₀ : Verifier.Config) : Prop where
  envelope : Verifier.envelope c₀ = true
  /-- Not independent of `envelope`: `ExplicitEngine.bounded_of_envelope` derives it
  from `envelope` together with the two byte-length bounds, in the same shape as the
  `hg` / `hw` hypotheses the call-side statements carry for `c`. It is kept as its
  own field so the deployment-side hypothesis is visible at the deployment rather
  than reassembled at each use site; `example_deployed_facts_inhabited` discharges
  it that way, from `envelope` and `ExplicitEngine.zero_lt_word_bound` twice. -/
  bounded : ExplicitEngine.Bounded c₀
  pinnedDigest : pin.configDigest = khash (ExplicitEngine.encodeConfig c₀)
  canonicalProfile : PinnedWhirProfile.profileOk P c₀ = true
  decodedGateRows : ∀ gates, gdec c₀.gatesEncoding = some gates → gates.length = c₀.gateRows

theorem config_eq_of_fields {c c' : Verifier.Config}
    (h1 : c.degreeBits = c'.degreeBits) (h2 : c.numConstants = c'.numConstants)
    (h3 : c.numRouted = c'.numRouted) (h4 : c.numWires = c'.numWires)
    (h5 : c.numPublicInputs = c'.numPublicInputs) (h6 : c.numSelectors = c'.numSelectors)
    (h7 : c.numGateConstraints = c'.numGateConstraints)
    (h8 : c.quotientDegree = c'.quotientDegree) (h9 : c.gateRows = c'.gateRows)
    (h10 : c.indexBits = c'.indexBits) (h11 : c.kIs = c'.kIs)
    (h12 : c.subgroupPowers = c'.subgroupPowers)
    (h13 : c.publicInputWireMap = c'.publicInputWireMap)
    (h14 : c.gatesEncoding = c'.gatesEncoding) (h15 : c.whirEncoding = c'.whirEncoding)
    (h16 : c.circuitDigest = c'.circuitDigest)
    (h17 : c.circuitConfigDigest = c'.circuitConfigDigest)
    (h18 : c.whirProtocolId = c'.whirProtocolId) (h19 : c.whirSessionId = c'.whirSessionId) :
    c = c' := by
  cases c
  cases c'
  simp only [Verifier.Config.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-- **THE TWO IDENTIFIERS, WITH NO COLLISION DISJUNCT.** `whirProtocolId` and
`whirSessionId` are pinned to the deployment by acceptance alone, given only the
deployment-side canonical profile check. No `khash` appears in the argument: both
configurations are read against the SAME `VkParams` row, and that row is shared
because `deploymentValid` checks `c.whirEncoding = c₀.whirEncoding` outright. This
is why the collision disjunct of `no_free_config_field_remains` is carried by
fifteen fields rather than seventeen: these two, plus the two digests, are pinned
without it. -/
theorem ids_pinned_without_collision (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hP : PinnedWhirProfile.profileOk P c₀ = true)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    c.whirProtocolId = c₀.whirProtocolId ∧ c.whirSessionId = c₀.whirSessionId := by
  obtain ⟨wp, -, hcheck, hpc₀, -, -, -, -⟩ := pinned_accepted_profile_is_canonical gdec hash
    thash khash P c₀ pin chain c p hacc
  obtain ⟨wp₀, hpc₀', hcheck₀⟩ := (PinnedWhirProfile.profile_ok_exact P c₀).mp hP
  have hwp : wp₀ = wp := Option.some.inj (hpc₀'.symm.trans hpc₀)
  subst hwp
  obtain ⟨-, -, hsid, -, hpid⟩ := (PinnedWhirProfile.canonical_check_exact P c wp₀).mp hcheck
  obtain ⟨-, -, hsid₀, -, hpid₀⟩ := (PinnedWhirProfile.canonical_check_exact P c₀ wp₀).mp hcheck₀
  exact ⟨hpid.trans hpid₀.symm, hsid.trans hsid₀.symm⟩

/-- **3(c) NO FREE CONFIGURATION FIELD REMAINS.** All nineteen fields of
`Verifier.Config`, in declaration order, pinned to the deployment by one accepted
call -- or `khash` collides. Thirteen come from the configuration digest
(`ExplicitEngine.encode_config_injective`), `indexBits` from the envelope,
`gateRows` from the gate preflight, `whirProtocolId` and `whirSessionId` from the
canonical profile table, and the last two -- `circuitDigest` and
`circuitConfigDigest` -- from this module's pin, with no collision disjunct of
their own. -/
theorem no_free_config_field_remains (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    (c.degreeBits = c₀.degreeBits ∧ c.numConstants = c₀.numConstants ∧
      c.numRouted = c₀.numRouted ∧ c.numWires = c₀.numWires ∧
      c.numPublicInputs = c₀.numPublicInputs ∧ c.numSelectors = c₀.numSelectors ∧
      c.numGateConstraints = c₀.numGateConstraints ∧ c.quotientDegree = c₀.quotientDegree ∧
      c.gateRows = c₀.gateRows ∧ c.indexBits = c₀.indexBits ∧ c.kIs = c₀.kIs ∧
      c.subgroupPowers = c₀.subgroupPowers ∧ c.publicInputWireMap = c₀.publicInputWireMap ∧
      c.gatesEncoding = c₀.gatesEncoding ∧ c.whirEncoding = c₀.whirEncoding ∧
      c.circuitDigest = c₀.circuitDigest ∧ c.circuitConfigDigest = c₀.circuitConfigDigest ∧
      c.whirProtocolId = c₀.whirProtocolId ∧ c.whirSessionId = c₀.whirSessionId) ∨
    ExplicitEngine.KhashCollision khash := by
  have hexpacc := pinned_acceptance_is_explicit_acceptance gdec hash thash khash P c₀ pin chain
    c p hacc
  rcases ExplicitEngine.accepted_call_pins_everything_but_the_two_digests gdec hash thash khash
    P c₀ pin chain c p hd.envelope hd.pinnedDigest hg hw hd.bounded hexpacc with
    ⟨hcore, hib, gates, hgd, hgl⟩ | hcol
  · obtain ⟨hcd, hccd⟩ := accepted_digests_are_the_deployed_ones gdec hash thash khash P c₀ pin
      chain c p hacc
    obtain ⟨wp, -, hcheck, hpc₀, -, -, -, -⟩ := pinned_accepted_profile_is_canonical gdec hash
      thash khash P c₀ pin chain c p hacc
    obtain ⟨wp₀, hpc₀', hcheck₀⟩ := (PinnedWhirProfile.profile_ok_exact P c₀).mp hd.canonicalProfile
    have hwp : wp₀ = wp := Option.some.inj (hpc₀'.symm.trans hpc₀)
    subst hwp
    obtain ⟨-, -, hsid, -, hpid⟩ := (PinnedWhirProfile.canonical_check_exact P c wp₀).mp hcheck
    obtain ⟨-, -, hsid₀, -, hpid₀⟩ := (PinnedWhirProfile.canonical_check_exact P c₀ wp₀).mp hcheck₀
    exact Or.inl
      ⟨congrArg ExplicitEngine.Core.degreeBits hcore,
       congrArg ExplicitEngine.Core.numConstants hcore,
       congrArg ExplicitEngine.Core.numRouted hcore,
       congrArg ExplicitEngine.Core.numWires hcore,
       congrArg ExplicitEngine.Core.numPublicInputs hcore,
       congrArg ExplicitEngine.Core.numSelectors hcore,
       congrArg ExplicitEngine.Core.numGateConstraints hcore,
       congrArg ExplicitEngine.Core.quotientDegree hcore,
       hgl.symm.trans (hd.decodedGateRows gates hgd), hib,
       congrArg ExplicitEngine.Core.kIs hcore,
       congrArg ExplicitEngine.Core.subgroupPowers hcore,
       congrArg ExplicitEngine.Core.publicInputWireMap hcore,
       congrArg ExplicitEngine.Core.gatesEncoding hcore,
       congrArg ExplicitEngine.Core.whirEncoding hcore,
       hcd, hccd, hpid.trans hpid₀.symm, hsid.trans hsid₀.symm⟩
  · exact Or.inr hcol

/-- **3(a) THE RESIDUE REMOVED.** `ExplicitEngine`'s
`accepted_configuration_matches_the_deployment_up_to_the_residue` concludes
`core c = core c₀ ∧ c.indexBits = c₀.indexBits`, and its
`accepted_call_pins_everything_but_the_two_digests` adds `gateRows`; with the two
digests pinned the conclusion is FULL CONFIGURATION EQUALITY. The collision
disjunct stays, because the thirteen encoded fields still reach the deployment
only through `khash`. -/
theorem accepted_configuration_is_the_deployment (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hd : DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    c = c₀ ∨ ExplicitEngine.KhashCollision khash := by
  rcases no_free_config_field_remains gdec hash thash khash P c₀ pin chain c p hd hg hw hacc with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ | hcol
  · exact Or.inl (config_eq_of_fields h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      h17 h18 h19)
  · exact Or.inr hcol

/-- The proof-side corollary of full configuration equality: an accepted call's
proof carries the deployed circuit digest and the deployed preprocessed root, and
the configuration it was checked against IS the deployment. This is the closest
the model gets to `_requireCanonicalProof` as a whole. -/
theorem accepted_call_is_a_deployed_call (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hd : DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    (c = c₀ ∧ p.protocolVersion = 3 ∧ p.circuitDigest = c₀.circuitDigest ∧
      p.preprocessedRoot = pin.preprocessedRoot ∧ p.constituentWidth = Verifier.width c₀) ∨
    ExplicitEngine.KhashCollision khash := by
  rcases accepted_configuration_is_the_deployment gdec hash thash khash P c₀ pin chain c p hd hg
    hw hacc with heq | hcol
  · obtain ⟨-, -, -, -, hv⟩ := Integrated.accepted_preflights_and_original_verifier
      (pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
    have hs := Verifier.verify_success_checks _ pin chain c p hv
    have hshape : Verifier.shape pin c p = true := hs.2.2.2.2.1
    obtain ⟨hpd, -, -⟩ := accepted_proof_circuit_digest_is_deployed gdec hash thash khash P c₀
      pin chain c p hacc
    simp only [Verifier.shape, decide_eq_true_eq] at hshape
    exact Or.inl ⟨heq, hshape.1, hpd, hshape.2.2.2.2.1, heq ▸ hshape.2.1⟩
  · exact Or.inr hcol

/-! ## 6. Examples

The adopted `OuterAdapter` fixture as the deployed configuration, two variants
that the pin rejects, and a witness that `DeployedFacts` is satisfiable at all.
These are `decide` on SMALL LITERAL data -- the fixture's circuit digest is four
copies of `Verifier.base 0` and its `circuitConfigDigest` is `Verifier.testRoot`,
which is zero. No digest space is enumerated anywhere, and none of these is a
fixture of the deployed profile. -/

def exampleDeployedConfig : Verifier.Config := OuterAdapter.fixtureConfig

def exampleCircuitDigestVariant : Verifier.Config :=
  { OuterAdapter.fixtureConfig with circuitDigest := List.replicate 4 (Verifier.base 1) }

def exampleConfigDigestVariant : Verifier.Config :=
  { OuterAdapter.fixtureConfig with circuitConfigDigest := ⟨1, by norm_num⟩ }

def exampleVariantProof : Verifier.Proof :=
  { OuterAdapter.fixtureProof with circuitDigest := List.replicate 4 (Verifier.base 1) }

theorem example_deployment_passes_its_own_pin :
    canonicalDigestPin exampleDeployedConfig exampleDeployedConfig = true := by decide

theorem example_circuit_digest_variant_is_rejected :
    canonicalDigestPin exampleDeployedConfig exampleCircuitDigestVariant = false := by decide

theorem example_config_digest_variant_is_rejected :
    canonicalDigestPin exampleDeployedConfig exampleConfigDigestVariant = false := by decide

theorem example_variant_proof_is_rejected :
    canonicalProofCheck exampleDeployedConfig exampleCircuitDigestVariant exampleVariantProof
      = false := by decide

/-- The fixture's own proof passes the proof-side check against the fixture
configuration, so the two rejections above are separations and not a predicate
that rejects everything. -/
theorem example_fixture_proof_passes_the_proof_check :
    canonicalProofCheck exampleDeployedConfig exampleDeployedConfig OuterAdapter.fixtureProof
      = true := by decide

/-- The variants differ from the deployment ONLY in a residue field, so
`ExplicitEngine`'s configuration digest cannot separate them: the encoding is
literally equal. That is the gap this module's pin closes, exhibited on data. -/
theorem example_variants_have_the_deployment_encoding :
    ExplicitEngine.encodeConfig exampleCircuitDigestVariant =
        ExplicitEngine.encodeConfig exampleDeployedConfig ∧
    ExplicitEngine.encodeConfig exampleConfigDigestVariant =
        ExplicitEngine.encodeConfig exampleDeployedConfig := ⟨rfl, rfl⟩

theorem example_deployed_digests_are_the_fixture_ones :
    deployedDigests exampleDeployedConfig =
      ⟨List.replicate 4 (Verifier.base 0), Verifier.testRoot⟩ := rfl

/-! ### `DeployedFacts` is not vacuous

The five deployment hypotheses of section 5 are not a contradiction dressed up as
a structure: they hold together, at the fixture deployment, for a synthetic
profile and gate decoder and for the pin a deployer would have written. The
profile decodes every byte string to one parameter record and reports the
fixture's own identifiers, which is enough for `PinnedWhirProfile.profileOk`; the
decoder decodes nothing, so `decodedGateRows` is vacuous on it. Neither is the
deployed profile -- this witnesses SATISFIABILITY, nothing more, and the
conclusions of section 5 are stated for arbitrary `gdec`, `P` and `pin`. -/

def exampleProfileParams : VkParams :=
  { PinnedWhirProfile.defaultParams with numVariables := 10 }

def exampleSyntheticProfile : Profile :=
  { decodeParams := fun _ => some exampleProfileParams,
    digest := fun _ => Verifier.testRoot,
    tableDigest := fun _ => Verifier.testRoot,
    tableProtocolId := fun _ => exampleDeployedConfig.whirProtocolId,
    sessionId := exampleDeployedConfig.whirSessionId }

def exampleDecodeGates : Integrated.DecodeGates := fun _ => none

def examplePinned (khash : Verifier.Bytes → Verifier.Root) : Verifier.Pinned :=
  ⟨1, khash (ExplicitEngine.encodeConfig exampleDeployedConfig), Verifier.testRoot⟩

/-- **THE DEPLOYMENT HYPOTHESES ARE INHABITED.** All five fields of
`DeployedFacts` at once, for every `khash`. `envelope` and `canonicalProfile` are
`decide` on the fixture; `bounded` is `ExplicitEngine.bounded_of_envelope`, which
is why that field is derivable rather than independent; `pinnedDigest` is `rfl`
because `examplePinned` is defined as the digest a deployer computes; and
`decodedGateRows` holds vacuously, `exampleDecodeGates` returning `none`. -/
theorem example_deployed_facts_inhabited (khash : Verifier.Bytes → Verifier.Root) :
    DeployedFacts exampleDecodeGates khash exampleSyntheticProfile (examplePinned khash)
      exampleDeployedConfig := by
  refine ⟨by decide, ?_, rfl, by decide, ?_⟩
  · exact ExplicitEngine.bounded_of_envelope (by decide) ExplicitEngine.zero_lt_word_bound
      ExplicitEngine.zero_lt_word_bound
  · intro gates h
    cases h

end Audit.Wire3.CanonicalProofCheck
