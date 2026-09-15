import Audit.Wire3.Algebra
import Audit.Wire3.ExplicitEngine
import Audit.Wire3.NonDegenerateAcceptance
import Audit.Wire3.OpenedClaimFold

/-!
# Derived acceptance: the accepting instance moved onto the real Fiat--Shamir transcript

## **HONESTY SECTION -- READ BEFORE USING ANY THEOREM BELOW**

**WHAT THIS MODULE ESTABLISHES.**  The adopted `Audit.Wire3.NonDegenerateAcceptance`
exhibits `Verifier.verify wideEngine widePin 1 maximalConfig maximalProof = .ok ()` at a
FIXTURE engine: its derived transcript is the EMPTY byte string at every configuration and
proof, its sampler returns the ALL-ZERO index point, its terminals are the constant
`Verifier.zero`, its `whirTail` is the constant `true`, its `configurationHash` is a
constant and its `deploymentValid` is the constant `true`.  Three of the nine guards of
`Verifier.verify` (`Verifier.lean:411-425`) are real arithmetic there.

This module moves that accepting instance onto an engine TEN of whose TWELVE fields are
the adopted concrete components -- literally the fields of
`ExplicitEngine.explicitEngine`, at every `Spongefish.Hash`
(`derived_engine_is_the_explicit_engine_minus_the_whir_pair`).  The two that are NOT moved
are `parseWhir` and `whirTail`, which stay `Verifier.testEngine`'s.  The headline is

    `Verifier.verify (derivedEngine thash khash P) (derivedPin khash) 1 derivedConfig
       derivedProof = .ok ()`

for EVERY outer transcript hash `thash` and EVERY configuration hash `khash`, under the
single hypothesis `PinnedWhirProfile.profileOk P derivedConfig = true`, which is discharged
at a stand-in profile in `derived_acceptance_at_the_profile_witness` and, separately, at a
SHARP profile whose decoder rejects every nonempty WHIR encoding and whose digests are
non-constant (`probe_acceptance_at_the_sharp_profile`); and the same instance again through
the adopted `Integrated.verify` (`derived_integrated_acceptance`,
`derived_integrated_acceptance_at_the_profile_witness`).  `thash` and `khash` are
UNIVERSALLY QUANTIFIED -- no hash is chosen, and no property of any hash is used.
**Universal quantification over `thash` and `khash` makes the acceptance logically stronger
than any instantiation, and simultaneously makes the hash-dependent guards NON-BINDING:
`derivedPin` is DEFINED from `khash`, so gate 2 closes by `rfl`, and the quantifier ranges
over constant hashes at which the same pin accepts a DIFFERENT configuration
(`probe_gate_two_does_not_bind_at_a_constant_hash`).  "At every transcript and
configuration hash" is a statement about GENERALITY OF THE ACCEPTANCE, NOT about STRENGTH
OF THE GUARDS.**  The gate-metadata decoder is the adopted stand-in
`NonDegenerateAcceptance.wideDecoder`.

**WHAT THIS MODULE DOES *NOT* ESTABLISH.**

* **THIS INSTANCE DOES NOT DOMINATE THE ADOPTED `NonDegenerateAcceptance.maximalConfig`;
  THE TWO ARE INCOMPARABLE.**  This module buys four gates -- (2), (4), (7), (9) become
  computations of adopted concrete components -- and pays for them with `numRouted = 0`,
  which is literally one of the three quantities the original degeneracy forced
  (`numWires = 1 ∧ numRouted = 0 ∧ numConstants = 1`) and which the adopted `maximalConfig`
  carries at `80`.  The adopted instance is strictly better on `numRouted`, `numSelectors`,
  `numGateConstraints` and `gateRows`; this one is strictly better on the engine.  Neither
  result subsumes the other, and no conclusion may be drawn by combining them.
  `numRouted = 0` is a RETURN TO A DEGENERACY THE ADOPTED TREE HAD SPECIFICALLY REPAIRED:
  the adopted Section 5 exists precisely to lift `numRouted` off zero, and this module puts
  it back.  (`quotientDegree` is NOT part of the gap: `derivedConfig` carries the envelope
  ceiling `8`, the same value `maximalConfig` carries.  `numPublicInputs` is not part of it
  either for plain `Verifier.verify`: `probe_acceptance_at_three_public_inputs` exhibits the
  SAME engine and the SAME all-zero claim record at `numPublicInputs = 3`, the adopted
  value.  It stays `0` in `derivedConfig` only because `Integrated.verify` forces it there
  -- see the next bullet.)
* **The WHIR parse and the WHIR tail are NOT installed.**  `parseWhir` and `whirTail` are
  the adopted fixture's: the tail accepts every transcript, hint string, parse and context
  (`derived_whir_tail_is_content_free`), and the parse ignores both byte strings
  (`derived_whir_parse_ignores_the_proof_bytes`).  The adopted tree DOES contain concrete
  `by rfl` successes of `WhirConfigured.run` -- the function `InstalledWhirTail.tailRun`
  calls -- at `WhirConfigured.lean:637,646` and `WhirTail.lean:902,921`, on a toy constant
  hash.  They are NOT reusable here: they run at mask `[⟨7⟩]` with three claims, whereas
  `tailRun`'s `whirMask` is hard-wired `[⟨31⟩]` (`InstalledWhirTail.lean:187-195`) and this
  context carries five bound claims.  The missing lemma is
  `installed_tail_succeeds_on_a_concrete_transcript :
  (InstalledWhirTail.tailRun hash wp ctx t h).isSome = true` at a five-claim context -- the
  exact dual of `InstalledWhirTail.lean:1122-1130`'s `= none` -- which with
  `installed_tail_true_iff` (`InstalledWhirTail.lean:253-257`) plus
  `wp.numVariables = ctx.numVariables` gives `installedTail ... = true`; reaching
  `Verifier.verifyWhir = true` additionally needs the parse, so the route is
  `InstalledWhirParse.installedParseEngine` with `prefixRun ... = some s` and
  `rootsAndClaimsMatch`.  Note also that `WhirInitial.readClaims` binds the transcript to
  this verifier's own `packedFold` values at the DERIVED index point, so any such witness is
  `thash`-DEPENDENT and a WHIR-complete instance could NOT keep this module's universal
  quantifier over `thash`.  Three further obstructions sit on the same route: exact-EOF on
  BOTH streams (`WhirFinal.exhausted` compares the transcript cursor to `transcript.length`
  AND the hint position to `hints.length`), the three pinned roots must appear literally in
  the transcript with `Merkle.verify` succeeding against them, and the deployed profile's
  real `powThreshold`/`finalPowThreshold` (`PinnedWhirProfile.lean:382-416`) require an
  actual grinding nonce rather than the zero thresholds of a toy profile.  All of this is a
  statement about what was found and done, NOT a claim that no such byte string exists or
  that Lean cannot produce one.
* **`numRouted = 0`, and `numPublicInputs = 0` only as its downstream consequence.**  The
  routed-wire count is the price of the real norm terminal.  With `Norm.normEvaluation`
  installed (it is: the engine field is the adopted concrete one), the log-terminal guard
  demands `Norm.normEvaluation c i (normTerminalInput p) point = (derivedRounds e c p).logClaim`
  with the challenges now DERIVED from an arbitrary `thash`.  The route taken here makes
  both sides `Verifier.zero` by running the wire loop `Norm.runWires` zero times
  (`permutation_terminal_vanishes_without_routed_wires`).
  `numPublicInputs = 0` is NOT independently forced.  The module previously said that "an
  empty public-input list kills the remaining summand"; that is true but is NOT the reason
  the list had to be empty.  `Norm.piStep`'s term is
  `sub (witness.getD col zero) (embed pair.2.val)`, which is `0 - 0` at an all-zero witness
  with zero-valued public inputs, so the whole public-input summand vanishes at ANY declared
  count (`probe_public_input_binding_vanishes_at_zero_values`), and
  `probe_acceptance_at_three_public_inputs` exhibits `Verifier.verify` accepting at
  `numPublicInputs = 3`.  What DOES force `numPublicInputs = 0` is `Norm.shapeValid`, the
  predicate the checked norm adapter of `Integrated.verify` enforces: it requires every
  public input's target column to be `< c.numRouted`, which is unsatisfiable at
  `numRouted = 0` (`probe_shape_valid_forces_no_public_inputs`).  So it is forced ONLY AS A
  DOWNSTREAM CONSEQUENCE of `numRouted = 0`, and only for the INTEGRATED entry point.
  **The corrected ledger of forced fields: only `numRouted = 0` is forced by an installed
  component.  `gateRows = 2`, `numSelectors = 2` and `numGateConstraints = 1` are forced by
  the STAND-IN DECODER, not by any real component.  `numPublicInputs = 0` is forced only
  downstream of `numRouted = 0`, and only through `Integrated.verify`.  `quotientDegree` is
  forced by nothing and sits at the envelope ceiling `8`.**
* **Gate 7 and gate 9 are real FUNCTIONS whose CONTENT collapses at this instance.**  Gate
  7's field is `Norm.normEvaluation`, but at this configuration it is `Verifier.zero` at
  every observation, point and public-input-free claim record
  (`derived_log_terminal_is_zero_at_this_config`) -- i.e. it cannot distinguish any two
  proofs, and a guard that cannot distinguish any two proofs is not a guard.  Gate 9 runs
  the adopted fourteen-family dispatcher on the adopted stand-in table and really does
  return `some Verifier.zero` -- it does NOT default
  (`derived_gate_evaluation_is_a_real_dispatcher_run`) -- but the value is zero because the
  witness and constant columns of `IndexHalfTransport.matchingClaims` are zero, and
  `Verifier.zero` annihilates the `Norm.eqEvaluation` factor.  So neither gate tests the
  derived gate tau or gate alpha here, even though both evaluators are the adopted
  concrete ones.
* **`P` and the decoder are stand-ins, and here is what each stands in for.**
  `derivedProfile`'s `decodeParams` is constant and its digest/table observations are the
  fixture root.  `P` stands in for THE DEPLOYED VK-PARAMETER DECODER AND THE ON-CHAIN
  CANONICAL-PROFILE ALLOWLIST: a real one decodes actual WHIR bytes into
  `PinnedWhirProfile.VkParams` and pins the digests against the transcribed canonical rows,
  which `ExplicitEngine.lean:44ff` records are transcribed for `n ∈ {10, 21}` ONLY -- the
  other nineteen rows ship as keccak digests and are not modelled.  `derivedDecoder` is the
  adopted two-row stand-in table; it stands in for THE GATE-METADATA ABI DECODER OF
  `c.gatesEncoding`: a real one makes `gateRows`, `numSelectors` and `numGateConstraints`
  functions of deployed bytes, unlocking up to `255` rows, `123` constraints and all
  fourteen gate families -- precisely what would give gate 9 content beyond the single
  `evalConstant` row it exercises here.  Neither is deployed metadata.
* **No adaptive failure event is made non-empty.**  Nothing here claims that
  `AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent` is inhabited, and nothing here
  lifts the vacuity recorded in
  `IndexHalfTransport.adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`:
  that event is indexed by the explicit engine AND by the fixture used-claims record, and
  neither the explicit engine's WHIR pair nor that claim record appears in any accepting
  instance below.
* **Nothing here is a collision-resistance, uniformity or Fiat--Shamir SECURITY claim.**
  `thash` and `khash` are arbitrary deterministic functions.  Section 8 proves DEPENDENCE
  -- that the verifier's challenges are squeezes of the absorbed transcript -- not that
  those squeezes are unpredictable.

## THE GATE LEDGER

`Verifier.verify` has nine guards: (1) the chain identifier, (2) `configurationHash`, (3)
`envelope`, (4) `deploymentValid`, (5) `shape`, (6) the four tau/index lengths, (7) the log
terminal, (8) `verifyWhir`, (9) the gate terminal.  The adopted module has THREE real:
(3), (5), (6).  Here SEVEN are computations of adopted concrete components -- (2), (3),
(4), (5), (6), (7), (9) -- with the two collapse caveats above.  Guard (1) is a comparison
of numerals in both modules.  Guard (8) is the only one still carried by fixture engine
fields; its residual content is that the parse's six ZERO claims force the adopted
`Connections.packedFold` of all five used-claim cells, AT THE DERIVED INDEX POINT, to
vanish (`derived_whir_gate_binds_the_packed_folds`).  Through `Integrated.verify` the count
is NINE of ELEVEN: the two preflights are real as well -- the checked norm adapter enforces
the seven-challenge layout and the whole `Norm.shapeValid` predicate against the DERIVED
observation, and the gate dispatcher must produce a result.

**THE HONEST COUNT IS FOUR OF NINE, NOT SEVEN OF NINE.**  Gates (2) and (4) close by `rfl`
at the accepting instance: `derivedPin` is DEFINED as `khash (encodeConfig derivedConfig)`
and the deployment pin is reflexive at `c = derivedConfig`.  Neither could have failed.
Gate (2)'s binding content lives entirely in
`derived_config_hash_gate_binds_the_configuration`, whose `KhashCollision` disjunct is
inhabited at a constant `khash` (`probe_constant_khash_collides`) -- at which the same pin
accepts a different configuration (`probe_gate_two_does_not_bind_at_a_constant_hash`).
Gate (7) is not real in any operative sense: `derived_log_terminal_is_zero_at_this_config`
shows the terminal is `zero` for EVERY observation, EVERY point and EVERY claim record with
empty public inputs, so it cannot distinguish any two proofs; `Norm.runWires` executes `0`
of `numRouted` iterations, so `denominatorTerms`, `formalNorm`, `formalAdjugate`, the logup
pair and the lambda ladder never execute at all.  Gate (9) is real but MINIMAL: one of
fourteen gate families, two of `255` admissible rows, one of `123` admissible constraints.
Of the nine guards, FOUR -- (3), (5), (6), (9) -- carry arithmetic at this instance that
could have failed.

## WHAT MOVED, COMPONENT BY COMPONENT

`concreteInitialObservation` and `concretePublicInputsHash` (this is the substitution that
kills the empty transcript), `concreteSampleIndices`, `concreteCommitRound`,
`concreteConfigurationHash` and `explicitDeployment`, on top of `Integrated.modelEngine`'s
`packedFold`, `normEvaluation`, `eqEvaluation` and gate dispatcher.  The sampler is NOT
installable on its own: with the fixture commit round the run's snapshot is the empty byte
string, the adopted sampler's decode fails, it returns empty lanes and the index-length
guard rejects -- `probe_fixture_commit_rejects_generally`, a theorem, at EVERY pin, chain,
configuration reading at least one index bit and proof with at least one coupled round.
Reverting the initial observation, or the used-claims record, likewise makes acceptance
impossible (`fixture_observation_rejects`, `fixture_claims_reject`).

## NON-VACUITY, AND THE ONE DELIBERATE EXCEPTION

Every conditional theorem below ships a satisfiability witness, with exactly one
deliberate exception, named here.  `derived_acceptance`'s profile hypothesis is discharged
by `derived_profile_passes_the_canonical_check` and, sharply, by
`probe_sharp_profile_passes`.  `derived_transcript_depends_on_the_proof` is a
collision-producing statement; its hypothesis -- two proofs sharing a derived transcript --
is inhabited at `constantHash`, and so is its conclusion
(`derived_transcript_dependence_hypotheses_satisfiable`).  That witness is also the reason
the theorem is stated in the "or the hash collides" form: at a hash that ignores its input
the derived transcripts of two different proofs really are equal, so the unconditional form
is REFUTED at `constantHash`, and saying so is not a claim about what Lean can prove.

THE EXCEPTION.  `probe_acceptance_at_one_routed_wire_forces_a_challenge_coincidence`
assumes acceptance at `numRouted = 1`, and THAT HYPOTHESIS IS NOT KNOWN SATISFIABLE -- its
unsatisfiability is exactly the open question the theorem addresses.  It ships as a
CONDITIONAL OBSTRUCTION, not as a statement about a reachable instance, and it is not
vacuous in the weak sense either: its conclusion is shown to be a real constraint by
`probe_one_routed_wire_terminal_is_not_zero`, which exhibits challenges at which the
conclusion FAILS.
-/

namespace Audit.Wire3.DerivedAcceptance

open Verifier

/-! ## 0. Algebra of the all-zero prover message -/

theorem zero_scalar_is_zero (k : Nat) : Verifier.scalar Verifier.zero k = Verifier.zero := by
  apply Subtype.eq
  show Arithmetic.scalar Arithmetic.zero k = Arithmetic.zero
  simp [Arithmetic.scalar, Arithmetic.zero, Arithmetic.zero_mul]

theorem fold_add_over_zeros :
    ∀ (n : Nat) (acc : Verifier.Ext3), acc = Verifier.zero →
      (List.replicate n Verifier.zero).foldl Verifier.add acc = Verifier.zero := by
  intro n
  induction n with
  | zero => intro acc h; simpa using h
  | succ n ih =>
      intro acc h
      simp only [List.replicate_succ, List.foldl_cons]
      exact ih _ (by rw [h, Algebra.vadd_zero])

theorem fold_horner_over_zeros (ch : Verifier.Ext3) :
    ∀ (n : Nat) (acc : Verifier.Ext3), acc = Verifier.zero →
      (List.replicate n Verifier.zero).foldl
        (fun a c => Verifier.add (Verifier.mul a ch) c) acc = Verifier.zero := by
  intro n
  induction n with
  | zero => intro acc h; simpa using h
  | succ n ih =>
      intro acc h
      simp only [List.replicate_succ, List.foldl_cons]
      refine ih _ ?_
      rw [h, Algebra.vzero_mul, Algebra.vzero_add]

/-- The sumcheck round transition on an all-zero message keeps a zero claim. -/
theorem evaluate_round_of_zero_message (n : Nat) (ch : Verifier.Ext3) :
    Verifier.evaluateRound Verifier.zero (List.replicate n Verifier.zero) ch = Verifier.zero := by
  simp only [Verifier.evaluateRound]
  rw [fold_add_over_zeros n Verifier.zero rfl, List.reverse_replicate,
    fold_horner_over_zeros ch n Verifier.zero rfl, Algebra.vzero_mul, Algebra.vsub_self,
    zero_scalar_is_zero, Algebra.vzero_add]

theorem round_step_keeps_zero_claims (commit : Verifier.CommitRound) (s : Verifier.RoundState)
    (m : Verifier.CoupledMessage) (a b : Nat)
    (hlog : m.1 = List.replicate a Verifier.zero)
    (hgate : m.2 = List.replicate b Verifier.zero)
    (hs : s.logClaim = Verifier.zero) (ht : s.gateClaim = Verifier.zero) :
    (Verifier.roundStep commit s m).logClaim = Verifier.zero ∧
      (Verifier.roundStep commit s m).gateClaim = Verifier.zero := by
  constructor
  · show Verifier.evaluateRound s.logClaim m.1 _ = Verifier.zero
    rw [hs, hlog]
    exact evaluate_round_of_zero_message a _
  · show Verifier.evaluateRound s.gateClaim m.2 _ = Verifier.zero
    rw [ht, hgate]
    exact evaluate_round_of_zero_message b _

theorem run_rounds_keeps_zero_claims (commit : Verifier.CommitRound) :
    ∀ (ms : List Verifier.CoupledMessage) (s : Verifier.RoundState),
      (∀ m ∈ ms, (∃ a, m.1 = List.replicate a Verifier.zero) ∧
        (∃ b, m.2 = List.replicate b Verifier.zero)) →
      s.logClaim = Verifier.zero → s.gateClaim = Verifier.zero →
      (Verifier.runRounds commit s ms).logClaim = Verifier.zero ∧
        (Verifier.runRounds commit s ms).gateClaim = Verifier.zero := by
  intro ms
  induction ms with
  | nil => intro s _ hs ht; exact ⟨hs, ht⟩
  | cons m ms ih =>
      intro s hall hs ht
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hall m (by simp)
      obtain ⟨h1, h2⟩ := round_step_keeps_zero_claims commit s m a b ha hb hs ht
      exact ih _ (fun x hx => hall x (by simp [hx])) h1 h2

/-! ## 1. The configuration, the proof and the engine -/

/-- The configuration this module accepts at.  Every numeric field is at the
ceiling `Verifier.envelope` permits EXCEPT `numRouted` and `numPublicInputs`,
which are zero, and the three gate-metadata fields the stand-in decoder forces;
see the header.  `quotientDegree` sits at the envelope ceiling `8`, the same
value the adopted `NonDegenerateAcceptance.maximalConfig` carries. -/
def derivedConfig : Verifier.Config :=
  { Verifier.testConfig with
      degreeBits := 13, numConstants := 80, numRouted := 0, numWires := 160,
      numPublicInputs := 0, numSelectors := 2, numGateConstraints := 1,
      quotientDegree := 8, gateRows := 2, indexBits := 8,
      kIs := [], subgroupPowers := List.replicate 13 (Verifier.base 1),
      publicInputWireMap := [] }

/-- The proof record: the adopted `IndexHalfTransport.matchingClaims` at this
configuration, with the shape-pinned round lists.  The gate rows have the
shape-pinned width `quotientDegree + 2 = 10`. -/
def derivedProof : Verifier.Proof :=
  { Verifier.testProof with
      constituentWidth := 160,
      publicInputs := [],
      logRounds := List.replicate 13 (List.replicate 5 Verifier.zero),
      gateRounds := List.replicate 13 (List.replicate 10 Verifier.zero),
      used := IndexHalfTransport.matchingClaims derivedConfig }

/-- The gate-metadata decoder this instance is taken at: the adopted
`NonDegenerateAcceptance.wideDecoder`, a two-row stand-in table whose first row
is a constant gate with one constraint and one constant and whose second row is
the no-constraint gate.  It is NOT deployed gate metadata. -/
def derivedDecoder : Integrated.DecodeGates := NonDegenerateAcceptance.wideDecoder

/-- The pinned deployment record.  Its configuration digest is the CONCRETE
digest of `derivedConfig` under an arbitrary `khash`. -/
def derivedPin (khash : Verifier.Bytes → Verifier.Root) : Verifier.Pinned :=
  ⟨1, ExplicitEngine.concreteConfigurationHash khash derivedConfig, Verifier.testRoot⟩

/-- **THE ENGINE.**  The adopted `ExplicitEngine.explicitEngine` with exactly the
WHIR parse and the WHIR tail moved back to the fixture's. -/
def derivedEngine (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) : Verifier.Engine where
  configurationHash := ExplicitEngine.concreteConfigurationHash khash
  deploymentValid := ExplicitEngine.explicitDeployment P derivedConfig
  initialObservation := InstalledInitialTranscript.concreteInitialObservation thash
  commitRound := InstalledRoundCommit.concreteCommitRound thash
  sampleIndices := InstalledIndexSampler.concreteSampleIndices thash
  foldClaim := Connections.packedFold
  normEvaluation := Norm.normEvaluation
  publicInputsHash := InstalledInitialTranscript.concretePublicInputsHash
  gateEvaluation := fun c wires constants publicHash alpha =>
    (Integrated.evaluateGate derivedDecoder c wires constants publicHash alpha).getD Verifier.zero
  eqEvaluation := Norm.eqEvaluation
  parseWhir := Verifier.testEngine.parseWhir
  whirTail := Verifier.testEngine.whirTail

/-- The engine is the adopted explicit engine with TWO fields moved, at every
WHIR/Merkle hash. -/
theorem derived_engine_is_the_explicit_engine_minus_the_whir_pair
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    derivedEngine thash khash P =
      { ExplicitEngine.explicitEngine derivedDecoder hash thash khash P derivedConfig with
          parseWhir := Verifier.testEngine.parseWhir,
          whirTail := Verifier.testEngine.whirTail } := rfl

/-- The ten fields that are the adopted concrete components. -/
theorem derived_engine_installed_fields (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (derivedEngine thash khash P).configurationHash =
        ExplicitEngine.concreteConfigurationHash khash ∧
      (derivedEngine thash khash P).deploymentValid =
        ExplicitEngine.explicitDeployment P derivedConfig ∧
      (derivedEngine thash khash P).initialObservation =
        InstalledInitialTranscript.concreteInitialObservation thash ∧
      (derivedEngine thash khash P).commitRound =
        InstalledRoundCommit.concreteCommitRound thash ∧
      (derivedEngine thash khash P).sampleIndices =
        InstalledIndexSampler.concreteSampleIndices thash ∧
      (derivedEngine thash khash P).foldClaim = Connections.packedFold ∧
      (derivedEngine thash khash P).normEvaluation = Norm.normEvaluation ∧
      (derivedEngine thash khash P).publicInputsHash =
        PublicInputHashBinding.hashNoPad ∧
      (derivedEngine thash khash P).eqEvaluation = Norm.eqEvaluation ∧
      (derivedEngine thash khash P).gateEvaluation =
        fun c wires constants publicHash alpha =>
          (Integrated.evaluateGate derivedDecoder c wires constants publicHash alpha).getD
            Verifier.zero :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The two fields that are still the fixture's. -/
theorem derived_engine_fixture_fields (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (derivedEngine thash khash P).parseWhir = Verifier.testEngine.parseWhir ∧
      (derivedEngine thash khash P).whirTail = Verifier.testEngine.whirTail :=
  ⟨rfl, rfl⟩

/-! ## 2. The numeric gates -/

theorem derived_config_envelope : Verifier.envelope derivedConfig = true := by decide

theorem derived_shape_holds (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.shape (derivedPin khash) derivedConfig derivedProof = true := by rfl

theorem derived_config_meets_the_profile_variable_budget :
    PinnedWhirProfile.minProfileVariables ≤
        derivedConfig.degreeBits + derivedConfig.indexBits ∧
      derivedConfig.degreeBits + derivedConfig.indexBits ≤
        PinnedWhirProfile.maxProfileVariables := by decide

/-! ## 3. The derived transcript, the rounds and the index lanes -/

theorem derived_initial_is_the_adopted_derivation (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) :
    (derivedEngine thash khash P).initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)) := rfl

theorem derived_tau_lengths (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) :
    ((derivedEngine thash khash P).initialTranscript c p).logTau.length = c.degreeBits ∧
      ((derivedEngine thash khash P).initialTranscript c p).gateTau.length = c.degreeBits :=
  ⟨(OuterInitial.derived_initial_shape thash c (Verifier.statement p)).2.1,
    (OuterInitial.derived_initial_shape thash c (Verifier.statement p)).2.2.1⟩

theorem derived_transcript_has_forty_bytes (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) :
    ((derivedEngine thash khash P).initialTranscript c p).transcript.length = 40 :=
  (OuterInitial.derived_initial_shape thash c (Verifier.statement p)).2.2.2

/-- The rounds snapshot decodes, with no hypothesis beyond the source bound on
the degree bits. -/
theorem derived_rounds_snapshot_decodes (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13) :
    OuterAdapter.decode
        (Verifier.derivedRounds (derivedEngine thash khash P) c p).transcript =
      some (InstalledRoundCommit.concreteFinal thash
        (OuterInitial.derive thash c (Verifier.statement p)).state 0
        (p.logRounds.zip p.gateRounds)) := by
  have hstart : OuterAdapter.decode
      (Verifier.start ((derivedEngine thash khash P).initialTranscript c p)).transcript =
        some (OuterInitial.derive thash c (Verifier.statement p)).state :=
    InstalledRoundCommit.start_snapshot_decodes (derivedEngine thash khash P) thash c p rfl hdb
  exact InstalledRoundCommit.concrete_run_snapshot_decodes thash (p.logRounds.zip p.gateRounds)
    (Verifier.start ((derivedEngine thash khash P).initialTranscript c p)) _ hstart

theorem derived_index_lanes_are_the_sampled_ones (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) (st : Transcript.State)
    (hd : OuterAdapter.decode
      (Verifier.derivedRounds (derivedEngine thash khash P) c p).transcript = some st) :
    Verifier.derivedIndices (derivedEngine thash khash P) c p =
      (OuterAdapter.sampleResult thash st p.used c.indexBits).points := by
  show InstalledIndexSampler.concreteSampleIndices thash
      (Verifier.derivedRounds (derivedEngine thash khash P) c p).transcript p.used c.indexBits = _
  exact InstalledIndexSampler.concrete_sampler_on_decoded_snapshot thash _ st p.used c.indexBits hd

theorem derived_index_lengths (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13) :
    (Verifier.derivedIndices (derivedEngine thash khash P) c p).log.length = c.indexBits ∧
      (Verifier.derivedIndices (derivedEngine thash khash P) c p).gate.length = c.indexBits := by
  have hd := derived_rounds_snapshot_decodes thash khash P c p hdb
  rw [derived_index_lanes_are_the_sampled_ones thash khash P c p _ hd]
  exact ⟨(OuterAdapter.sample_result_shape thash _ p.used c.indexBits).1,
    (OuterAdapter.sample_result_shape thash _ p.used c.indexBits).2.1⟩

/-! ## 4. The two terminals -/

theorem derived_claims_vanish (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (derivedEngine thash khash P) derivedConfig derivedProof).logClaim =
        Verifier.zero ∧
      (Verifier.derivedRounds (derivedEngine thash khash P) derivedConfig derivedProof).gateClaim =
        Verifier.zero := by
  refine run_rounds_keeps_zero_claims _ _ _ ?_ rfl rfl
  intro m hm
  obtain ⟨hl, hg⟩ := List.of_mem_zip hm
  exact ⟨⟨5, List.eq_of_mem_replicate hl⟩, ⟨10, List.eq_of_mem_replicate hg⟩⟩

theorem run_wires_at_zero_count (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (subgroup : Verifier.Ext3) (index : Nat)
    (s : Norm.WireState) : Norm.runWires c ch t subgroup index 0 s = s := by
  simp [Norm.runWires]

/-- The adopted concrete permutation terminal vanishes identically at a
configuration with no routed wires: the wire loop runs zero times. -/
theorem permutation_terminal_vanishes_without_routed_wires (c : Verifier.Config)
    (hr : c.numRouted = 0) (ch : Norm.Challenges) (t : Verifier.NormTerminalInput)
    (point : List Verifier.Ext3) :
    Norm.permutationTerminal c ch t point = Verifier.zero := by
  simp only [Norm.permutationTerminal, hr, run_wires_at_zero_count, Norm.wireStart,
    Algebra.vmul_zero, Algebra.vadd_zero]

/-- The adopted concrete norm terminal vanishes identically at a configuration
with no routed wires, on a proof with no public inputs. -/
theorem norm_terminal_vanishes_without_routed_wires (c : Verifier.Config)
    (hr : c.numRouted = 0) (i : Verifier.Initial) (t : Verifier.NormTerminalInput)
    (hpi : t.publicInputs = []) (point : List Verifier.Ext3) :
    Norm.normEvaluation c i t point = Verifier.zero := by
  simp only [Norm.normEvaluation, Norm.evaluate,
    permutation_terminal_vanishes_without_routed_wires c hr,
    Norm.public_input_empty_is_zero c t point _ hpi, Algebra.vmul_zero, Algebra.vadd_zero]

theorem derived_log_terminal_gate (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (derivedEngine thash khash P).logTerminal derivedConfig
        ((derivedEngine thash khash P).initialTranscript derivedConfig derivedProof) derivedProof
        (Verifier.derivedRounds (derivedEngine thash khash P) derivedConfig derivedProof).logPoint =
      (Verifier.derivedRounds (derivedEngine thash khash P) derivedConfig derivedProof).logClaim := by
  rw [(derived_claims_vanish thash khash P).1]
  exact norm_terminal_vanishes_without_routed_wires derivedConfig rfl
    ((derivedEngine thash khash P).initialTranscript derivedConfig derivedProof)
    (Verifier.normTerminalInput derivedProof) rfl _

theorem read_value_of_zero_replicate (n i : Nat) :
    Gates.readValue (List.replicate n Verifier.zero) i = Verifier.zero := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- The adopted fourteen-family dispatcher, run on the deployed-shaped stand-in
table at the all-zero witness and constant columns, produces `Verifier.zero` --
for EVERY public-input hash of the pinned four-limb length and EVERY gate alpha.
Row zero's single constant constraint is `zero - zero`; row one carries no
constraint. -/
theorem derived_gate_dispatcher_vanishes (publicHash : Nat → Verifier.Base)
    (alpha : Verifier.Ext3) :
    GatesComplete.evalCombined (Integrated.gateConfig derivedConfig)
      [⟨1, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 1, 1, 2, 1, 0, 0, 0, 0⟩]
      (List.replicate 160 Verifier.zero) (List.replicate 80 Verifier.zero)
      publicHash alpha = some Verifier.zero := by
  have hv : Gates.validateConfiguration (Integrated.gateConfig derivedConfig)
      [⟨1, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 1, 1, 2, 1, 0, 0, 0, 0⟩] = some () := by decide
  have ht0 : GatesComplete.evaluateUnfiltered ⟨1, 0, 0, 1, 0, 1, 1, 0, 0⟩
      (List.replicate 160 Verifier.zero) (List.replicate 80 Verifier.zero) publicHash
      (Integrated.gateConfig derivedConfig).numSelectors = some [Verifier.zero] := by
    show some (Gates.evalConstant (List.replicate 160 Verifier.zero)
      (List.replicate 80 Verifier.zero) 2 1) = _
    simp only [Gates.evalConstant, read_value_of_zero_replicate, Algebra.vsub_self]
    rfl
  have ht1 : GatesComplete.evaluateUnfiltered ⟨0, 1, 1, 2, 1, 0, 0, 0, 0⟩
      (List.replicate 160 Verifier.zero) (List.replicate 80 Verifier.zero) publicHash
      (Integrated.gateConfig derivedConfig).numSelectors = some [] := rfl
  have hc0 : GatesComplete.contribution (Integrated.gateConfig derivedConfig)
      ⟨1, 0, 0, 1, 0, 1, 1, 0, 0⟩ (List.replicate 160 Verifier.zero)
      (List.replicate 80 Verifier.zero) publicHash alpha = some Verifier.zero := by
    simp only [GatesComplete.contribution]
    split
    · rfl
    · simp [ht0, Gates.horner, Algebra.vzero_mul, Algebra.vadd_zero, Algebra.vmul_zero]
  have hc1 : GatesComplete.contribution (Integrated.gateConfig derivedConfig)
      ⟨0, 1, 1, 2, 1, 0, 0, 0, 0⟩ (List.replicate 160 Verifier.zero)
      (List.replicate 80 Verifier.zero) publicHash alpha = some Verifier.zero := by
    simp only [GatesComplete.contribution]
    split
    · rfl
    · simp [ht1, Gates.horner, Algebra.vmul_zero]
  simp only [GatesComplete.evalCombined, List.length_replicate, bind, Option.bind]
  rw [if_neg (by simp [Integrated.gateConfig, derivedConfig]), hv]
  show GatesComplete.combineRows _ _ _ _ _ _ Verifier.zero = _
  simp only [GatesComplete.combineRows, bind, Option.bind, hc0, hc1, Algebra.vadd_zero]

theorem derived_gate_evaluation_vanishes (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    Integrated.evaluateGate derivedDecoder derivedConfig (List.replicate 160 Verifier.zero)
      (List.replicate 80 Verifier.zero) publicHash alpha = some Verifier.zero := by
  simp only [Integrated.evaluateGate, derivedDecoder, NonDegenerateAcceptance.wideDecoder,
    bind, Option.bind]
  rw [if_neg (by simp [hp, derivedConfig])]
  exact derived_gate_dispatcher_vanishes _ alpha

theorem derived_gate_claim_columns_are_zero :
    derivedProof.used.gateWitness = List.replicate 160 Verifier.zero ∧
      derivedProof.used.gatePreprocessed.take derivedConfig.numConstants =
        List.replicate 80 Verifier.zero := ⟨rfl, rfl⟩

theorem gate_terminal_unfolds (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.gateTerminal e c p =
      Verifier.mul (e.eqEvaluation (e.initialTranscript c p).gateTau
          (Verifier.derivedRounds e c p).gatePoint)
        (e.gateEvaluation c p.used.gateWitness (p.used.gatePreprocessed.take c.numConstants)
          (e.publicInputsHash p.publicInputs) (e.initialTranscript c p).gateAlpha) := rfl

theorem derived_gate_evaluation_field (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (derivedEngine thash khash P).gateEvaluation =
      fun c wires constants publicHash alpha =>
        (Integrated.evaluateGate derivedDecoder c wires constants publicHash alpha).getD
          Verifier.zero := rfl

theorem derived_public_input_hash_field (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (derivedEngine thash khash P).publicInputsHash = PublicInputHashBinding.hashNoPad := rfl

theorem derived_gate_evaluation_at_the_proof (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (publicHash : List Verifier.Base) (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    (derivedEngine thash khash P).gateEvaluation derivedConfig derivedProof.used.gateWitness
        (derivedProof.used.gatePreprocessed.take derivedConfig.numConstants) publicHash alpha =
      Verifier.zero := by
  rw [derived_gate_evaluation_field]
  simp only []
  rw [derived_gate_claim_columns_are_zero.1, derived_gate_claim_columns_are_zero.2,
    derived_gate_evaluation_vanishes publicHash hp]
  rfl

theorem derived_gate_terminal_gate (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Verifier.gateTerminal (derivedEngine thash khash P) derivedConfig derivedProof =
      (Verifier.derivedRounds (derivedEngine thash khash P) derivedConfig derivedProof).gateClaim := by
  rw [(derived_claims_vanish thash khash P).2, gate_terminal_unfolds,
    derived_public_input_hash_field,
    derived_gate_evaluation_at_the_proof thash khash P _
      (PublicInputHashBinding.hash_no_pad_length derivedProof.publicInputs)]
  exact Algebra.vmul_zero _

/-! ## 5. The WHIR gate -/

theorem packed_fold_of_zero_claims (n w : Nat) (point : List Verifier.Ext3) :
    Connections.packedFold (List.replicate n Verifier.zero) w point = Verifier.zero := by
  apply Subtype.eq
  show Packed.fold ((List.replicate n Verifier.zero).map Subtype.val)
    (point.map Subtype.val) = Arithmetic.zero
  rw [List.map_replicate]
  exact OpenedClaimFold.fold_zero_column n _

theorem derived_expected_claims_are_zero (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (derivedEngine thash khash P) derivedConfig
      derivedProof).expectedClaims =
      [some Verifier.zero, some Verifier.zero, some Verifier.zero, some Verifier.zero,
        some Verifier.zero, none] := by
  show Verifier.expectedClaims Connections.packedFold derivedConfig derivedProof
    (Verifier.derivedIndices (derivedEngine thash khash P) derivedConfig derivedProof) = _
  simp only [Verifier.expectedClaims, List.cons.injEq, Option.some.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact packed_fold_of_zero_claims 80 _ _
  · exact packed_fold_of_zero_claims 160 _ _
  · exact packed_fold_of_zero_claims 0 _ _
  · exact packed_fold_of_zero_claims 80 _ _
  · exact packed_fold_of_zero_claims 160 _ _

theorem derived_whir_gate (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Verifier.verifyWhir (derivedEngine thash khash P)
      (Verifier.derivedContext (derivedEngine thash khash P) derivedConfig derivedProof)
      derivedProof = true := by
  simp only [Verifier.verifyWhir, Verifier.rootsAndClaimsMatch]
  rw [derived_expected_claims_are_zero thash khash P]
  rfl

/-! ## 6. Acceptance -/

/-- **THE ACCEPTANCE.**  The adopted `Verifier.verify`, at an engine ten of whose
twelve fields are the adopted concrete components, for EVERY outer transcript
hash and EVERY configuration hash. -/
theorem derived_acceptance (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P derivedConfig = true) :
    Verifier.verify (derivedEngine thash khash P) (derivedPin khash) 1 derivedConfig
      derivedProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl derived_config_envelope ?_
    (derived_shape_holds khash)
    (derived_tau_lengths thash khash P derivedConfig derivedProof).1
    (derived_tau_lengths thash khash P derivedConfig derivedProof).2
    (derived_index_lengths thash khash P derivedConfig derivedProof (by decide)).1
    (derived_index_lengths thash khash P derivedConfig derivedProof (by decide)).2
    (derived_log_terminal_gate thash khash P) (derived_whir_gate thash khash P)
    (derived_gate_terminal_gate thash khash P)
  show ExplicitEngine.explicitDeployment P derivedConfig derivedConfig = true
  simp [ExplicitEngine.explicitDeployment, hprofile]

/-! ### 6a. The profile hypothesis is satisfiable, and the closed instance -/

/-- A WHIR parameter record at the ceiling `1 ≤ numVariables ≤ 21` the adopted
`PinnedWhirProfile.canonicalProfileCheck` imposes, which is exactly
`derivedConfig.degreeBits + derivedConfig.indexBits`. -/
def derivedParams : PinnedWhirProfile.VkParams :=
  { PinnedWhirProfile.defaultParams with numVariables := 21 }

/-- A STAND-IN deployment profile: its decoder is constant, its digest and table
observations are the fixture root, and its protocol/session identifiers are
empty.  It exists to show that `derived_acceptance`'s hypothesis is inhabited;
it is not the deployed allowlist. -/
def derivedProfile : PinnedWhirProfile.Profile where
  decodeParams := fun _ => some derivedParams
  digest := fun _ => Verifier.testRoot
  tableDigest := fun _ => Verifier.testRoot
  tableProtocolId := fun _ => []
  sessionId := []

theorem derived_profile_passes_the_canonical_check :
    PinnedWhirProfile.profileOk derivedProfile derivedConfig = true := by rfl

/-- **THE CLOSED ACCEPTANCE.**  No hypothesis at all, for EVERY outer transcript
hash and EVERY configuration hash. -/
theorem derived_acceptance_at_the_profile_witness (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (derivedEngine thash khash derivedProfile) (derivedPin khash) 1
      derivedConfig derivedProof = .ok () :=
  derived_acceptance thash khash derivedProfile derived_profile_passes_the_canonical_check

/-! ### 6b. The same instance through the adopted `Integrated.verify` -/

theorem derived_engine_is_its_own_model_engine (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Integrated.modelEngine (derivedEngine thash khash P) derivedDecoder =
      derivedEngine thash khash P := rfl

theorem derived_log_point_length (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (derivedEngine thash khash P) derivedConfig
      derivedProof).logPoint.length = 13 := by
  have h := (Verifier.runRounds_lengths (InstalledRoundCommit.concreteCommitRound thash)
    (Verifier.start ((derivedEngine thash khash P).initialTranscript derivedConfig derivedProof))
    (derivedProof.logRounds.zip derivedProof.gateRounds)).2.1
  have hz : (derivedProof.logRounds.zip derivedProof.gateRounds).length = 13 := rfl
  rw [hz] at h
  exact h

theorem derived_norm_shape_valid (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Norm.shapeValid derivedConfig
        (Norm.challengesFromInitial
          ((derivedEngine thash khash P).initialTranscript derivedConfig derivedProof))
        (Verifier.normTerminalInput derivedProof)
        (Verifier.derivedRounds (derivedEngine thash khash P) derivedConfig
          derivedProof).logPoint = true := by
  have hpt := derived_log_point_length thash khash P
  have htau := (derived_tau_lengths thash khash P derivedConfig derivedProof).1
  simp only [Norm.shapeValid, decide_eq_true_eq]
  refine ⟨hpt, ?_, ?_, rfl, by decide, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show ((derivedEngine thash khash P).initialTranscript derivedConfig
      derivedProof).logTau.length = _
    rw [htau, hpt]
    rfl
  · show (List.replicate 13 (Verifier.base 1)).length = _
    rw [List.length_replicate, hpt]
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)

theorem derived_integrated_norm_result (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Integrated.normResult (derivedEngine thash khash P) derivedConfig derivedProof =
      some Verifier.zero := by
  have hchal : ((derivedEngine thash khash P).initialTranscript derivedConfig
      derivedProof).logChallenges.length = 7 :=
    (OuterInitial.derived_initial_shape thash derivedConfig (Verifier.statement derivedProof)).1
  simp only [Integrated.normResult, Norm.checkedNormEvaluation, Norm.checkedEvaluate,
    hchal, if_pos, derived_norm_shape_valid, ite_true]
  show some (Norm.normEvaluation derivedConfig _ _ _) = _
  rw [norm_terminal_vanishes_without_routed_wires derivedConfig rfl _
    (Verifier.normTerminalInput derivedProof) rfl _]

theorem derived_integrated_gate_result (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Integrated.gateResult (derivedEngine thash khash P) derivedDecoder derivedConfig
      derivedProof = some Verifier.zero := by
  show Integrated.evaluateGate derivedDecoder derivedConfig derivedProof.used.gateWitness
    (derivedProof.used.gatePreprocessed.take derivedConfig.numConstants)
    ((derivedEngine thash khash P).publicInputsHash derivedProof.publicInputs) _ = _
  rw [derived_public_input_hash_field, derived_gate_claim_columns_are_zero.1,
    derived_gate_claim_columns_are_zero.2,
    derived_gate_evaluation_vanishes _
      (PublicInputHashBinding.hash_no_pad_length derivedProof.publicInputs)]

/-- **THE INTEGRATED ACCEPTANCE.**  Both preflight gates of the adopted
`Integrated.verify` -- the checked norm adapter, which enforces the
seven-challenge layout AND the full norm shape predicate, and the gate
dispatcher, which must produce a result -- plus the whole of `Verifier.verify`,
at the same engine, the same configuration and the same proof. -/
theorem derived_integrated_acceptance (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P derivedConfig = true) :
    Integrated.verify (derivedEngine thash khash P) derivedDecoder (derivedPin khash) 1
      derivedConfig derivedProof = .ok () := by
  simp only [Integrated.verify, derived_engine_is_its_own_model_engine,
    derived_integrated_norm_result, derived_integrated_gate_result]
  exact derived_acceptance thash khash P hprofile

theorem derived_integrated_acceptance_at_the_profile_witness (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) :
    Integrated.verify (derivedEngine thash khash derivedProfile) derivedDecoder
      (derivedPin khash) 1 derivedConfig derivedProof = .ok () :=
  derived_integrated_acceptance thash khash derivedProfile
    derived_profile_passes_the_canonical_check

/-- Which of the quantities the adopted causes collapsed are restored here, and
which is NOT: `numRouted` is zero.  Stated exactly. -/
theorem derived_config_is_nondegenerate_except_for_the_routed_wires :
    1 < derivedConfig.numWires ∧ 1 < derivedConfig.numConstants ∧
      1 < derivedConfig.degreeBits ∧ 0 < derivedConfig.indexBits ∧
      derivedConfig.numRouted = 0 ∧ derivedConfig.numPublicInputs = 0 := by decide

/-- The four quantities `Verifier.verify` actually reads through the transcript
and the index lanes sit at the envelope ceiling: thirteen degree bits, a packed
width of one hundred and sixty, eight index bits, eighty constants.  The three
gate metadata fields (`gateRows`, `numGateConstraints`, `numSelectors`) are NOT
at the ceiling: they are the two-row STAND-IN DECODER's, exactly as in the
adopted Section 6.  `quotientDegree` is at the ceiling; see
`derived_config_quotient_degree_is_at_the_envelope_ceiling`. -/
theorem derived_config_sits_at_the_envelope_ceiling :
    derivedConfig.degreeBits = 13 ∧ Verifier.width derivedConfig = 160 ∧
      derivedConfig.indexBits = 8 ∧ derivedConfig.numConstants = 80 := by decide

/-- The three gate metadata fields the STAND-IN DECODER forces, stated so no
reader has to guess.  They are forced by `derivedDecoder`, not by any real
component of `Verifier.verify`. -/
theorem derived_config_gate_metadata_is_the_stand_in_table :
    derivedConfig.gateRows = 2 ∧ derivedConfig.numSelectors = 2 ∧
      derivedConfig.numGateConstraints = 1 := by decide

/-- `quotientDegree` is NOT one of them: it sits at the envelope ceiling, the
same value the adopted `NonDegenerateAcceptance.maximalConfig` carries, and the
proof's gate rows carry the matching shape-pinned width. -/
theorem derived_config_quotient_degree_is_at_the_envelope_ceiling :
    derivedConfig.quotientDegree = 8 ∧ derivedConfig.quotientDegree + 2 = 10 ∧
      derivedProof.gateRounds = List.replicate 13 (List.replicate 10 Verifier.zero) ∧
      derivedConfig.quotientDegree =
        NonDegenerateAcceptance.maximalConfig.quotientDegree :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 7. THE GATE LEDGER, AS THEOREMS -/

/-- (7) **GATE 2 IS A REAL DIGEST OF THE CONFIGURATION.**  The engine's
configuration hash is `khash` applied to the adopted concrete configuration
encoding, at every configuration; the adopted fixture's was a constant. -/
theorem derived_config_hash_gate_reads_the_configuration (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) :
    (derivedEngine thash khash P).configurationHash c = khash (ExplicitEngine.encodeConfig c) :=
  rfl

/-- (7) **AND IT BINDS.**  Acceptance at this pin forces the accepted
configuration's thirteen encoded core fields to be `derivedConfig`'s, or exhibits
a `khash` collision.  The two byte-length side conditions are the adopted
`ExplicitEngine.Bounded` ones; they say the call's own calldata fits a word
length. -/
theorem derived_config_hash_gate_binds_the_configuration (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Verifier.verify (derivedEngine thash khash P) (derivedPin khash) chain c p = .ok ()) :
    ExplicitEngine.core c = ExplicitEngine.core derivedConfig ∨
      ExplicitEngine.KhashCollision khash := by
  have hs := Verifier.verify_success_checks (derivedEngine thash khash P) (derivedPin khash)
    chain c p hacc
  refine ExplicitEngine.config_digest_binds_the_core khash c derivedConfig
    (ExplicitEngine.bounded_of_envelope hs.2.2.1 hg hw)
    (ExplicitEngine.bounded_of_envelope derived_config_envelope (by decide) (by decide)) ?_
  exact hs.2.1

/-- (7) **GATE 4 IS THE ADOPTED DEPLOYMENT PREDICATE.**  It is the WHIR-bytes pin
conjoined with the canonical-profile check, not a constant. -/
theorem derived_deployment_gate_is_the_explicit_predicate (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) :
    (derivedEngine thash khash P).deploymentValid c = true ↔
      c.whirEncoding = derivedConfig.whirEncoding ∧ PinnedWhirProfile.profileOk P c = true :=
  ExplicitEngine.explicit_deployment_exact P derivedConfig c

/-- (7) **GATE 7 IS THE ADOPTED NORM TERMINAL, AND IT IS ZERO HERE.**  The engine
field is `Norm.normEvaluation`, not a constant; but at a configuration with no
routed wires it returns `Verifier.zero` at EVERY observation, claim record with
no public inputs, and point.  This is the exact sense in which gate 7 carries no
arithmetic at THIS configuration. -/
theorem derived_log_terminal_is_zero_at_this_config (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (i : Verifier.Initial) (p : Verifier.Proof) (hpi : p.publicInputs = [])
    (point : List Verifier.Ext3) :
    (derivedEngine thash khash P).logTerminal derivedConfig i p point = Verifier.zero :=
  norm_terminal_vanishes_without_routed_wires derivedConfig rfl i
    (Verifier.normTerminalInput p) hpi point

/-- (7) **GATE 9 RUNS THE ADOPTED DISPATCHER, AND IT RETURNS ZERO HERE.**  The
gate evaluator is the adopted fourteen-family dispatcher on the adopted stand-in
two-row table; it does NOT default, and the `Option` is `some`.  Its value is
zero because the witness and constant columns of `matchingClaims` are zero, so
the equality factor `Norm.eqEvaluation` is multiplied away -- which is exactly
why the gate terminal carries no information about the derived gate tau at THIS
instance, even though the gate evaluator is real. -/
theorem derived_gate_evaluation_is_a_real_dispatcher_run (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (alpha : Verifier.Ext3) :
    Integrated.evaluateGate derivedDecoder derivedConfig derivedProof.used.gateWitness
        (derivedProof.used.gatePreprocessed.take derivedConfig.numConstants)
        ((derivedEngine thash khash P).publicInputsHash derivedProof.publicInputs) alpha =
      some Verifier.zero := by
  rw [derived_gate_claim_columns_are_zero.1, derived_gate_claim_columns_are_zero.2]
  exact derived_gate_evaluation_vanishes _ (PublicInputHashBinding.hash_no_pad_length _) alpha

/-- (7) **THE FIXTURE WHIR TAIL, KEPT VERBATIM.**  It accepts every transcript,
every hint string, every parse and every context. -/
theorem derived_whir_tail_is_content_free (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (ctx : Verifier.WhirContext) (t h : Verifier.Bytes) (parsed : Verifier.ParsedWhir) :
    (derivedEngine thash khash P).whirTail ctx t h parsed = true := rfl

/-- (7) **THE FIXTURE WHIR PARSE, KEPT VERBATIM.**  It ignores both byte strings
and returns the context's own roots with six zero claims. -/
theorem derived_whir_parse_ignores_the_proof_bytes (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (ctx : Verifier.WhirContext) (t h : Verifier.Bytes) :
    (derivedEngine thash khash P).parseWhir ctx t h =
      some ⟨ctx.roots, ctx.roots, List.replicate 6 Verifier.zero⟩ := rfl

/-- (7) **WHAT GATE 8 STILL BUYS.**  The fixture parse is content-free about the
WHIR bytes, but its six ZERO claims are not: passing gate 8 forces the adopted
`Connections.packedFold` of all five used-claim cells, at the DERIVED index
point, to vanish.  That is a real arithmetic condition on the proof's claims and
on the sampled point, and it is the only content gate 8 has here. -/
theorem derived_whir_gate_binds_the_packed_folds (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hw : Verifier.verifyWhir (derivedEngine thash khash P)
      (Verifier.derivedContext (derivedEngine thash khash P) c p) p = true) :
    Connections.packedFold p.used.logPreprocessed (Verifier.width c)
        (Verifier.derivedIndices (derivedEngine thash khash P) c p).log = Verifier.zero ∧
      Connections.packedFold p.used.logWitness (Verifier.width c)
        (Verifier.derivedIndices (derivedEngine thash khash P) c p).log = Verifier.zero ∧
      Connections.packedFold p.used.logNormInverse (Verifier.width c)
        (Verifier.derivedIndices (derivedEngine thash khash P) c p).log = Verifier.zero ∧
      Connections.packedFold p.used.gatePreprocessed (Verifier.width c)
        (Verifier.derivedIndices (derivedEngine thash khash P) c p).gate = Verifier.zero ∧
      Connections.packedFold p.used.gateWitness (Verifier.width c)
        (Verifier.derivedIndices (derivedEngine thash khash P) c p).gate = Verifier.zero := by
  obtain ⟨parsed, hp, _, _, hcl, _⟩ := Verifier.whir_acceptance_requires_bound_statement
    (derivedEngine thash khash P) _ p hw
  rw [derived_whir_parse_ignores_the_proof_bytes] at hp
  rw [← Option.some.inj hp] at hcl
  show _ ∧ _ ∧ _ ∧ _ ∧ _
  simp only [Verifier.derivedContext, Verifier.whirContext, Verifier.expectedClaims,
    List.replicate, Verifier.claimsMatch, Bool.and_eq_true, decide_eq_true_eq] at hcl
  exact ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.1, hcl.2.2.2.2.1⟩

/-! ### 7a. Negative controls: each installed component is load-bearing -/

/-- The engine of this module with ONLY the coupled-round commit reverted to the
adopted fixture's constant. -/
def fixtureCommitEngine (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) : Verifier.Engine :=
  { derivedEngine thash khash P with commitRound := Verifier.testEngine.commitRound }

theorem fixture_commit_keeps_the_empty_transcript :
    ∀ (ms : List Verifier.CoupledMessage) (s : Verifier.RoundState), s.transcript = [] →
      (Verifier.runRounds Verifier.testEngine.commitRound s ms).transcript = []
  | [], _, h => h
  | _ :: ms, _, _ => fixture_commit_keeps_the_empty_transcript ms _ rfl

theorem fixture_commit_gives_empty_transcript (m : Verifier.CoupledMessage)
    (ms : List Verifier.CoupledMessage) (s : Verifier.RoundState) :
    (Verifier.runRounds Verifier.testEngine.commitRound s (m :: ms)).transcript = [] :=
  fixture_commit_keeps_the_empty_transcript ms _ rfl

/-- (7a) With the fixture commit the run's snapshot is the EMPTY byte string, so
the adopted concrete sampler's own decode fails and it returns empty lanes -- it
invents no fallback point.  At EVERY configuration and EVERY proof with at least
one coupled round. -/
theorem probe_fixture_commit_lanes_are_empty_generally (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) (m : Verifier.CoupledMessage)
    (ms : List Verifier.CoupledMessage) (hz : p.logRounds.zip p.gateRounds = m :: ms) :
    Verifier.derivedIndices (fixtureCommitEngine thash khash P) c p = ⟨[], []⟩ := by
  have hempty : (Verifier.derivedRounds (fixtureCommitEngine thash khash P) c p).transcript
      = [] := by
    show (Verifier.runRounds Verifier.testEngine.commitRound
      (Verifier.start ((fixtureCommitEngine thash khash P).initialTranscript c p))
      (p.logRounds.zip p.gateRounds)).transcript = []
    rw [hz]
    exact fixture_commit_gives_empty_transcript _ _ _
  show InstalledIndexSampler.concreteSampleIndices thash
    (Verifier.derivedRounds (fixtureCommitEngine thash khash P) c p).transcript p.used
    c.indexBits = _
  rw [hempty]
  exact InstalledIndexSampler.concrete_sampler_rejects_malformed_snapshot thash [] _ _
    (OuterAdapter.decode_bad_length [] (by decide))

/-- (7a) **NEGATIVE CONTROL 1, AT EVERY PIN, CHAIN, CONFIGURATION AND PROOF.**
Reverting the coupled-round commit alone, keeping the concrete initial transcript
and the concrete sampler, makes acceptance IMPOSSIBLE -- and the gate that fails
is named: the index-lane length guard (`Verifier.lean:420-421`), because the lanes
come back empty.  This holds whenever the proof has at least one coupled round
and the configuration reads at least one index bit, so "installing the sampler
without the commit round is not a reachable intermediate stage" is a statement
about the components, not about this configuration and this proof. -/
theorem probe_fixture_commit_rejects_generally (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (m : Verifier.CoupledMessage) (ms : List Verifier.CoupledMessage)
    (hz : p.logRounds.zip p.gateRounds = m :: ms) (hib : 0 < c.indexBits) :
    Verifier.verify (fixtureCommitEngine thash khash P) pin chain c p ≠ .ok () := by
  intro hacc
  have h := (Verifier.verify_success_checks (fixtureCommitEngine thash khash P)
    pin chain c p hacc).2.2.2.2.2.2.2.1
  rw [probe_fixture_commit_lanes_are_empty_generally thash khash P c p m ms hz] at h
  simp only [List.length_nil] at h
  omega

/-- The coupled-round list of this proof is nonempty: thirteen rounds. -/
theorem derived_coupled_rounds_are_nonempty :
    derivedProof.logRounds.zip derivedProof.gateRounds =
      (List.replicate 5 Verifier.zero, List.replicate 10 Verifier.zero) ::
        (List.replicate 12 (List.replicate 5 Verifier.zero)).zip
          (List.replicate 12 (List.replicate 10 Verifier.zero)) := rfl

theorem fixture_commit_index_lanes_are_empty (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Verifier.derivedIndices (fixtureCommitEngine thash khash P) derivedConfig derivedProof =
      ⟨[], []⟩ :=
  probe_fixture_commit_lanes_are_empty_generally thash khash P derivedConfig derivedProof _ _
    derived_coupled_rounds_are_nonempty

/-- (7a) **NEGATIVE CONTROL 1 AT THIS INSTANCE.**  The specialisation of
`probe_fixture_commit_rejects_generally` to this configuration, this proof and
this pin. -/
theorem fixture_commit_rejects (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Verifier.verify (fixtureCommitEngine thash khash P) (derivedPin khash) 1 derivedConfig
      derivedProof ≠ .ok () :=
  probe_fixture_commit_rejects_generally thash khash P (derivedPin khash) 1 derivedConfig
    derivedProof _ _ derived_coupled_rounds_are_nonempty (by decide)

/-- (7a) **NEGATIVE CONTROL 2: THE INITIAL OBSERVATION IS LOAD-BEARING.**
Reverting it alone pins `degreeBits = 1` by the adopted
`NonDegenerateAcceptance.unit_log_tau_forces_one_degree_bit`, and this
configuration has thirteen. -/
theorem fixture_observation_rejects (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Verifier.verify
        { derivedEngine thash khash P with
            initialObservation := Verifier.testEngine.initialObservation }
        (derivedPin khash) 1 derivedConfig derivedProof ≠ .ok () := by
  intro hacc
  exact absurd (NonDegenerateAcceptance.unit_log_tau_forces_one_degree_bit
    { derivedEngine thash khash P with
        initialObservation := Verifier.testEngine.initialObservation }
    (derivedPin khash) 1 derivedConfig derivedProof (fun _ _ => rfl) hacc) (by decide)

/-- (7a) **NEGATIVE CONTROL 3: THE MATCHING USED CLAIMS ARE LOAD-BEARING.**
Reverting the claim record to the adopted fixture's pins `numWires = 1` by the
adopted `NonDegenerateAcceptance.acceptance_at_fixture_claims_forces_degenerate_config`,
and this configuration has one hundred and sixty. -/
theorem fixture_claims_reject (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Verifier.verify (derivedEngine thash khash P) (derivedPin khash) 1 derivedConfig
      { derivedProof with used := Verifier.testProof.used } ≠ .ok () := by
  intro hacc
  exact absurd (NonDegenerateAcceptance.acceptance_at_fixture_claims_forces_degenerate_config
    (derivedEngine thash khash P) (derivedPin khash) 1 derivedConfig
    { derivedProof with used := Verifier.testProof.used } rfl hacc).1 (by decide)

/-! ## 8. THE DEPENDENCE ON THE DERIVED TRANSCRIPT -/

/-- (8) **THE DERIVED TRANSCRIPT IS NOT THE EMPTY BYTE STRING.**  It is the
forty-byte snapshot of the adopted outer derivation, at every configuration,
proof and hash -- the exact negation of the adopted fixture's behaviour. -/
theorem derived_transcript_is_not_empty (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) :
    ((derivedEngine thash khash P).initialTranscript c p).transcript ≠ [] := by
  intro h
  have hlen := derived_transcript_has_forty_bytes thash khash P c p
  rw [h] at hlen
  exact absurd hlen (by decide)

/-- (8) **THE DERIVED TRANSCRIPT DEPENDS ON THE PROOF.**  Two proofs differing in
ANY of the three committed Merkle roots cannot share the derived initial
transcript unless `thash` collides -- and the collision is EXHIBITED by the
adopted `CommitmentOrder.TranscriptCollision`, not assumed away. -/
theorem derived_transcript_depends_on_the_proof (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p q : Verifier.Proof) (hdb : c.degreeBits ≤ 13)
    (hne : p.preprocessedRoot ≠ q.preprocessedRoot ∨ p.witnessRoot ≠ q.witnessRoot ∨
      p.normInverseRoot ≠ q.normInverseRoot)
    (h : ((derivedEngine thash khash P).initialTranscript c p).transcript =
      ((derivedEngine thash khash P).initialTranscript c q).transcript) :
    CommitmentOrder.TranscriptCollision thash := by
  have hbound : ∀ r : Verifier.Proof,
      (OuterInitial.derive thash c (Verifier.statement r)).state.counter <
        Transcript.u64Limit := by
    intro r
    rw [OuterInitial.derived_final_counter]
    unfold Transcript.u64Limit
    omega
  have hstate : (OuterInitial.derive thash c (Verifier.statement p)).state =
      (OuterInitial.derive thash c (Verifier.statement q)).state :=
    OuterInitial.snapshot_is_injective_bounded _ _ (hbound p) (hbound q) h
  have hpref : CommitmentOrder.prefixDigest thash c (Verifier.statement p) =
      CommitmentOrder.prefixDigest thash c (Verifier.statement q) := by
    rw [CommitmentOrder.prefixDigest, CommitmentOrder.prefixDigest,
      CommitmentOrder.prefix_state_is_relation_state,
      CommitmentOrder.prefix_state_is_relation_state,
      ← OuterInitial.derived_final_digest, ← OuterInitial.derived_final_digest, hstate]
  exact CommitmentOrder.distinct_roots_force_a_distinct_prefix_or_a_collision thash c c
    (Verifier.statement p) (Verifier.statement q) hne hpref

/-! ### 8a. A collapsing hash, as the satisfiability witness -/

def constantDigest : Transcript.Digest := ⟨List.replicate 32 ⟨1, by decide⟩, by simp⟩

/-- A deterministic hash that ignores its input.  It is legal in the model --
nothing ties `Transcript.Hash` to any property -- and it is what makes the
hypothesis of `derived_transcript_depends_on_the_proof` inhabited. -/
def constantHash : Transcript.Hash := fun _ => constantDigest

/-- (8a) **THE COLLISION HYPOTHESIS IS SATISFIABLE.**  At `constantHash` two
proofs with different norm-inverse roots DO share the derived transcript, so
`derived_transcript_depends_on_the_proof` is not vacuous; its conclusion is
witnessed too. -/
theorem constant_hash_transcript_ignores_the_statement (c : Verifier.Config)
    (s : Verifier.Statement) :
    (OuterInitial.toInitial (OuterInitial.derive constantHash c s)).transcript =
      OuterInitial.snapshot ⟨constantDigest, 12 + 6 * c.degreeBits⟩ := by
  show OuterInitial.snapshot (OuterInitial.derive constantHash c s).state = _
  have h1 : (OuterInitial.derive constantHash c s).state.digest = constantDigest := by
    rw [OuterInitial.derived_final_digest]; rfl
  have h2 : (OuterInitial.derive constantHash c s).state.counter = 12 + 6 * c.degreeBits :=
    OuterInitial.derived_final_counter constantHash c s
  congr 1
  cases hst : (OuterInitial.derive constantHash c s).state with
  | mk d n =>
      rw [hst] at h1 h2
      simp only [Transcript.State.mk.injEq]
      exact ⟨h1, h2⟩

theorem derived_transcript_dependence_hypotheses_satisfiable
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    derivedProof.normInverseRoot ≠ (⟨1, by decide⟩ : Verifier.Root) ∧
      ((derivedEngine constantHash khash P).initialTranscript derivedConfig
          derivedProof).transcript =
        ((derivedEngine constantHash khash P).initialTranscript derivedConfig
          { derivedProof with normInverseRoot := ⟨1, by decide⟩ }).transcript ∧
      CommitmentOrder.TranscriptCollision constantHash := by
  refine ⟨by decide, ?_, ⟨[], [⟨0, by decide⟩], by decide, rfl⟩⟩
  rw [derived_initial_is_the_adopted_derivation, derived_initial_is_the_adopted_derivation,
    constant_hash_transcript_ignores_the_statement,
    constant_hash_transcript_ignores_the_statement]

/-! ### 8b. The derived challenges ARE the transcript squeezes -/

/-- (8b) **THE GATE CHALLENGES ARE SQUEEZES OF THE ABSORBED PREFIX.**  The gate
alpha and every gate tau coordinate are `thash` reductions of the digest of the
adopted twenty-two frame commitment prefix, at the source counters. -/
theorem derived_challenges_depend_on_the_transcript (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) (i : Nat) (hi : i < c.degreeBits) :
    ((derivedEngine thash khash P).initialTranscript c p).gateAlpha =
        OuterInitial.ext3At thash (CommitmentOrder.prefixDigest thash c (Verifier.statement p))
          (9 + 3 * c.degreeBits) ∧
      (((derivedEngine thash khash P).initialTranscript c p).gateTau).get? i =
        some (OuterInitial.ext3At thash
          (CommitmentOrder.prefixDigest thash c (Verifier.statement p))
          (12 + 3 * c.degreeBits + 3 * i)) :=
  CommitmentOrder.gate_challenge_counters thash c p i hi

/-- (8b) **THE INDEX LANES ARE SQUEEZES OF THE RUN'S OWN SNAPSHOT.**  Each
coordinate is the `thash` reduction, at the source counter, of the digest the
run's decoded snapshot reaches after the eight adopted claim frames. -/
theorem derived_index_lane_coordinates (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) (p : Verifier.Proof) (st : Transcript.State) (i : Nat)
    (hd : OuterAdapter.decode
      (Verifier.derivedRounds (derivedEngine thash khash P) c p).transcript = some st)
    (hi : i < c.indexBits) :
    (Verifier.derivedIndices (derivedEngine thash khash P) c p).log.get? i =
        some (OuterInitial.ext3At thash
          (OuterAdapter.claimsCommitted thash st p.used).digest (3 * i)) ∧
      (Verifier.derivedIndices (derivedEngine thash khash P) c p).gate.get? i =
        some (OuterInitial.ext3At thash
          (OuterAdapter.claimsCommitted thash st p.used).digest
          (3 * c.indexBits + 3 * i)) := by
  rw [derived_index_lanes_are_the_sampled_ones thash khash P c p st hd]
  exact ⟨OuterAdapter.sampled_log_index_counter thash st p.used c.indexBits i hi,
    OuterAdapter.sampled_gate_index_counter thash st p.used c.indexBits i hi⟩

/-- (8c) **THE INDEX POINT IS NOT THE ALL-ZERO POINT.**  At the collapsing hash
of section 8a -- the WORST case for this statement, since every digest in the run
is the same -- the sampled log lane is still not `List.replicate indexBits
Verifier.zero`.  The adopted repaired sampler of
`NonDegenerateAcceptance` returned exactly that point at every argument. -/
theorem derived_index_point_is_not_all_zero (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedIndices (derivedEngine constantHash khash P) derivedConfig
      derivedProof).log ≠ List.replicate derivedConfig.indexBits Verifier.zero := by
  have hd := derived_rounds_snapshot_decodes constantHash khash P derivedConfig derivedProof
    (by decide)
  have hcoord := (derived_index_lane_coordinates constantHash khash P derivedConfig derivedProof
    _ 0 hd (by decide)).1
  intro hcontra
  rw [hcontra] at hcoord
  exact absurd hcoord (by decide)

/-! ## 9. `numPublicInputs = 0` IS NOT FORCED BY `Verifier.verify`

The header's old claim that "an empty public-input list kills the remaining summand" is
TRUE but is NOT the reason the list had to be empty.  `Norm.piStep`'s term is
`sub (witness.getD target.column zero) (embed pair.2.val)`, which is `0 - 0` at an all-zero
witness with zero-VALUED public inputs -- no matter how MANY the configuration declares.
The real reason `numPublicInputs = 0` appears in `derivedConfig` is `Norm.shapeValid`, and
that is a DOWNSTREAM CONSEQUENCE of `numRouted = 0` rather than an independent constraint;
see `probe_shape_valid_forces_no_public_inputs` at the end of this section. -/

theorem getD_replicate_zero (n i : Nat) :
    (List.replicate n Verifier.zero).getD i Verifier.zero = Verifier.zero := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem probe_embed_zero : Norm.embed (Verifier.base 0).val = Verifier.zero := by rfl

theorem probe_mem_enum_replicate {a : Verifier.Base} {k : Nat} {q : Nat × Verifier.Base}
    (hq : q ∈ (List.replicate k a).enum) : q.2 = a := by
  have h : q.2 ∈ List.replicate k a := by
    have := List.mem_map_of_mem (f := Prod.snd) hq
    rwa [List.enum_map_snd] at this
  exact List.eq_of_mem_replicate h

theorem probe_pi_fold_keeps_zero_binding (wireMap : Verifier.Bytes)
    (point : List Verifier.Ext3) (eta : Verifier.Ext3) (n : Nat) :
    ∀ (pairs : List (Nat × Verifier.Base)) (s : Norm.PiState),
      (∀ q ∈ pairs, q.2 = Verifier.base 0) → s.binding = Verifier.zero →
      (pairs.foldl (Norm.piStep wireMap (List.replicate n Verifier.zero) point eta) s).binding =
        Verifier.zero := by
  intro pairs
  induction pairs with
  | nil => intro s _ hs; simpa using hs
  | cons q qs ih =>
      intro s hall hs
      rw [List.foldl_cons]
      refine ih _ (fun x hx => hall x (List.mem_cons_of_mem _ hx)) ?_
      show Verifier.add s.binding (Verifier.mul _
        (Verifier.sub ((List.replicate n Verifier.zero).getD _ Verifier.zero)
          (Norm.embed q.2.val))) = Verifier.zero
      rw [getD_replicate_zero, hall q (List.mem_cons_self _ _), probe_embed_zero,
        Algebra.vsub_self, Algebra.vmul_zero, hs, Algebra.vadd_zero]

/-- **THE PUBLIC-INPUT SUMMAND VANISHES AT ANY DECLARED COUNT.**  The adopted
concrete norm terminal's public-input binding is `Verifier.zero` at an all-zero
witness column and all-zero public-input VALUES -- no matter how MANY public
inputs the configuration declares. -/
theorem probe_public_input_binding_vanishes_at_zero_values (c : Verifier.Config)
    (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3) (eta : Verifier.Ext3)
    (n k : Nat) (hw : t.witness = List.replicate n Verifier.zero)
    (hp : t.publicInputs = List.replicate k (Verifier.base 0)) :
    Norm.publicInputBinding c t point eta = Verifier.zero := by
  simp only [Norm.publicInputBinding, Norm.publicInputState, hw, hp]
  exact probe_pi_fold_keeps_zero_binding c.publicInputWireMap point eta n _ Norm.piStart
    (fun _ hq => probe_mem_enum_replicate hq) rfl

/-- This module's configuration with THREE public inputs -- the adopted
`NonDegenerateAcceptance.maximalConfig`'s value -- and that module's
public-input wire map.  Every other field is `derivedConfig`'s. -/
def probePublicConfig : Verifier.Config :=
  { derivedConfig with numPublicInputs := 3, publicInputWireMap := List.replicate 9 0 }

/-- The matching proof: three ZERO public-input values. -/
def probePublicProof : Verifier.Proof :=
  { derivedProof with publicInputs := List.replicate 3 (Verifier.base 0) }

def probePublicPin (khash : Verifier.Bytes → Verifier.Root) : Verifier.Pinned :=
  ⟨1, ExplicitEngine.concreteConfigurationHash khash probePublicConfig, Verifier.testRoot⟩

theorem probe_public_config_envelope : Verifier.envelope probePublicConfig = true := by decide

theorem probe_public_shape (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.shape (probePublicPin khash) probePublicConfig probePublicProof = true := by rfl

theorem probe_public_profile_ok :
    PinnedWhirProfile.profileOk derivedProfile probePublicConfig = true := by rfl

theorem probe_public_claims_vanish (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (derivedEngine thash khash P) probePublicConfig
        probePublicProof).logClaim = Verifier.zero ∧
      (Verifier.derivedRounds (derivedEngine thash khash P) probePublicConfig
        probePublicProof).gateClaim = Verifier.zero := by
  refine run_rounds_keeps_zero_claims _ _ _ ?_ rfl rfl
  intro m hm
  obtain ⟨hl, hg⟩ := List.of_mem_zip hm
  exact ⟨⟨5, List.eq_of_mem_replicate hl⟩, ⟨10, List.eq_of_mem_replicate hg⟩⟩

/-- The real norm terminal still vanishes at THREE declared public inputs. -/
theorem probe_public_log_terminal (i : Verifier.Initial) (point : List Verifier.Ext3) :
    Norm.normEvaluation probePublicConfig i (Verifier.normTerminalInput probePublicProof) point =
      Verifier.zero := by
  simp only [Norm.normEvaluation, Norm.evaluate,
    permutation_terminal_vanishes_without_routed_wires probePublicConfig rfl,
    probe_public_input_binding_vanishes_at_zero_values probePublicConfig
      (Verifier.normTerminalInput probePublicProof) point _ 160 3 rfl rfl,
    Algebra.vmul_zero, Algebra.vzero_add]

theorem probe_public_expected_claims (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (derivedEngine thash khash P) probePublicConfig
      probePublicProof).expectedClaims =
      [some Verifier.zero, some Verifier.zero, some Verifier.zero, some Verifier.zero,
        some Verifier.zero, none] := by
  show Verifier.expectedClaims Connections.packedFold probePublicConfig probePublicProof
    (Verifier.derivedIndices (derivedEngine thash khash P) probePublicConfig
      probePublicProof) = _
  simp only [Verifier.expectedClaims, List.cons.injEq, Option.some.injEq, and_true]
  exact ⟨packed_fold_of_zero_claims 80 _ _, packed_fold_of_zero_claims 160 _ _,
    packed_fold_of_zero_claims 0 _ _, packed_fold_of_zero_claims 80 _ _,
    packed_fold_of_zero_claims 160 _ _⟩

theorem probe_public_whir_gate (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Verifier.verifyWhir (derivedEngine thash khash P)
      (Verifier.derivedContext (derivedEngine thash khash P) probePublicConfig probePublicProof)
      probePublicProof = true := by
  simp only [Verifier.verifyWhir, Verifier.rootsAndClaimsMatch]
  rw [probe_public_expected_claims thash khash P]
  rfl

theorem probe_gate_eval_is_config_independent (w cst : List Verifier.Ext3)
    (ph : List Verifier.Base) (a : Verifier.Ext3) :
    Integrated.evaluateGate derivedDecoder probePublicConfig w cst ph a =
      Integrated.evaluateGate derivedDecoder derivedConfig w cst ph a := rfl

theorem probe_public_gate_columns :
    probePublicProof.used.gateWitness = List.replicate 160 Verifier.zero ∧
      probePublicProof.used.gatePreprocessed.take probePublicConfig.numConstants =
        List.replicate 80 Verifier.zero := ⟨rfl, rfl⟩

theorem probe_public_gate_evaluation_at_the_proof (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (publicHash : List Verifier.Base) (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    (derivedEngine thash khash P).gateEvaluation probePublicConfig
        probePublicProof.used.gateWitness
        (probePublicProof.used.gatePreprocessed.take probePublicConfig.numConstants)
        publicHash alpha = Verifier.zero := by
  rw [derived_gate_evaluation_field]
  simp only []
  rw [probe_public_gate_columns.1, probe_public_gate_columns.2,
    probe_gate_eval_is_config_independent, derived_gate_evaluation_vanishes publicHash hp]
  rfl

theorem probe_public_gate_terminal (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile) :
    Verifier.gateTerminal (derivedEngine thash khash P) probePublicConfig probePublicProof =
      (Verifier.derivedRounds (derivedEngine thash khash P) probePublicConfig
        probePublicProof).gateClaim := by
  rw [(probe_public_claims_vanish thash khash P).2, gate_terminal_unfolds,
    derived_public_input_hash_field,
    probe_public_gate_evaluation_at_the_proof thash khash P _
      (PublicInputHashBinding.hash_no_pad_length probePublicProof.publicInputs)]
  exact Algebra.vmul_zero _

/-- **ACCEPTANCE AT THREE PUBLIC INPUTS.**  The SAME engine, the SAME all-zero
claim record, the SAME twelve engine fields, at a configuration declaring THREE
public inputs -- the adopted `maximalConfig`'s value.  So `numPublicInputs = 0`
is NOT forced by any installed component of `Verifier.verify`; it is forced only
downstream of `numRouted = 0`, and only for `Integrated.verify`. -/
theorem probe_acceptance_at_three_public_inputs (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (derivedEngine thash khash derivedProfile) (probePublicPin khash) 1
      probePublicConfig probePublicProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl
    probe_public_config_envelope ?_ (probe_public_shape khash)
    (derived_tau_lengths thash khash derivedProfile probePublicConfig probePublicProof).1
    (derived_tau_lengths thash khash derivedProfile probePublicConfig probePublicProof).2
    (derived_index_lengths thash khash derivedProfile probePublicConfig probePublicProof
      (by decide)).1
    (derived_index_lengths thash khash derivedProfile probePublicConfig probePublicProof
      (by decide)).2
    ?_ (probe_public_whir_gate thash khash derivedProfile)
    (probe_public_gate_terminal thash khash derivedProfile)
  · exact (ExplicitEngine.explicit_deployment_exact derivedProfile derivedConfig
      probePublicConfig).mpr ⟨rfl, probe_public_profile_ok⟩
  · rw [(probe_public_claims_vanish thash khash derivedProfile).1]
    exact probe_public_log_terminal _ _

/-- **AND THIS IS WHAT ACTUALLY FORCES IT, FOR `Integrated.verify` ONLY.**  The
adopted `Norm.shapeValid` -- which the checked norm adapter of `Integrated.verify`
enforces but plain `Verifier.verify` does not -- requires every public input's
target column to be BELOW `numRouted`.  At `numRouted = 0` that condition is
unsatisfiable, so the public-input list must be empty.  `numPublicInputs = 0` is
therefore a DOWNSTREAM CONSEQUENCE of `numRouted = 0`, not an independent
regression. -/
theorem probe_shape_valid_forces_no_public_inputs (c : Verifier.Config)
    (ch : Norm.Challenges) (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3)
    (hr : c.numRouted = 0) (h : Norm.shapeValid c ch t point = true) :
    t.publicInputs = [] := by
  simp only [Norm.shapeValid, decide_eq_true_eq] at h
  cases hpi : t.publicInputs with
  | nil => rfl
  | cons a l =>
      exfalso
      have hlen : 0 < t.publicInputs.length := by rw [hpi]; simp
      have := (h.2.2.2.2.2.2.2.2.2.2 0 hlen).1
      rw [hr] at this
      exact absurd this (Nat.not_lt_zero _)

/-! ## 10. GATE 2 DOES NOT BIND UNDER THE UNIVERSAL QUANTIFIER

`derivedPin khash` is DEFINED as `khash (ExplicitEngine.encodeConfig derivedConfig)`, so
guard (2) closes by `rfl` at the accepting instance and could not have failed.  Its binding
content lives entirely in `derived_config_hash_gate_binds_the_configuration`, whose
conclusion is a DISJUNCTION with `ExplicitEngine.KhashCollision khash`.  The universal
quantifier over `khash` ranges over hashes at which that disjunct is the one that fires. -/

/-- A deterministic configuration hash that ignores its input.  Legal in the model
-- nothing ties `Verifier.Bytes → Verifier.Root` to any property -- and covered by
this module's universal quantifier over `khash`. -/
def constantKhash : Verifier.Bytes → Verifier.Root := fun _ => Verifier.testRoot

theorem probe_constant_khash_collides : ExplicitEngine.KhashCollision constantKhash :=
  ⟨[], [⟨0, by decide⟩], by decide, rfl⟩

/-- **GATE 2 IS NOT BINDING UNDER THE UNIVERSAL QUANTIFIER.**  At a constant
`khash` the SAME pin `derivedPin khash` -- computed from `derivedConfig` --
accepts a DIFFERENT configuration. -/
theorem probe_gate_two_does_not_bind_at_a_constant_hash (thash : Transcript.Hash) :
    Verifier.verify (derivedEngine thash constantKhash derivedProfile)
      (derivedPin constantKhash) 1 probePublicConfig probePublicProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl
    probe_public_config_envelope ?_ (by rfl)
    (derived_tau_lengths thash constantKhash derivedProfile probePublicConfig
      probePublicProof).1
    (derived_tau_lengths thash constantKhash derivedProfile probePublicConfig
      probePublicProof).2
    (derived_index_lengths thash constantKhash derivedProfile probePublicConfig
      probePublicProof (by decide)).1
    (derived_index_lengths thash constantKhash derivedProfile probePublicConfig
      probePublicProof (by decide)).2
    ?_ (probe_public_whir_gate thash constantKhash derivedProfile)
    (probe_public_gate_terminal thash constantKhash derivedProfile)
  · exact (ExplicitEngine.explicit_deployment_exact derivedProfile derivedConfig
      probePublicConfig).mpr ⟨rfl, probe_public_profile_ok⟩
  · rw [(probe_public_claims_vanish thash constantKhash derivedProfile).1]
    exact probe_public_log_terminal _ _

/-- The two configurations really are different, so the previous theorem is not a
restatement of this module's own acceptance. -/
theorem probe_public_config_differs : probePublicConfig ≠ derivedConfig := by
  intro h
  have : probePublicConfig.numPublicInputs = derivedConfig.numPublicInputs := by rw [h]
  exact absurd this (by decide)

/-! ## 11. THE OBSTRUCTION AT ONE ROUTED WIRE

The header used to say only that "no such instance was found here".  That is upgraded to a
POSITIVE OBSTRUCTION: at one routed wire, with the all-zero norm-inverse column the adopted
`IndexHalfTransport.matchingClaims` supplies, acceptance is EQUIVALENT to a coincidence
among the DERIVED challenges.

The mechanism.  `matchingClaims`' all-zero columns make `idHelper = sigmaHelper = 0`, so
`idZero = sigmaZero = sub zero one = -1` and `logupSum = 0`, leaving the permutation
terminal equal to `eq(tau, point) * (-(1 + rho))`, which is NOT identically zero
(`probe_one_routed_wire_terminal_is_not_zero`).

The second, independent block.  The escape -- nonzero `normInverse` entries inverting the
challenge-dependent `denominatorTerms.1` -- is closed off by gate 8: this module's own
`derived_whir_gate_binds_the_packed_folds` forces
`Connections.packedFold p.used.logNormInverse (Verifier.width c) idx.log = Verifier.zero`
at the DERIVED index point.  So a repair needs a NONZERO column whose packed fold vanishes
at a `thash`-DEPENDENT point.

Note the vacuity exception recorded in the header: the acceptance hypothesis of
`probe_acceptance_at_one_routed_wire_forces_a_challenge_coincidence` is not known
satisfiable.  It ships as a conditional obstruction, with
`probe_one_routed_wire_terminal_is_not_zero` certifying that its conclusion is a real
constraint rather than a triviality. -/

theorem run_wires_one (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (sg : Verifier.Ext3) (index : Nat) (s : Norm.WireState) :
    Norm.runWires c ch t sg index 1 s = Norm.wireStep c ch t sg index s := by
  simp [Norm.runWires]

/-- At ONE routed wire with an all-zero norm-inverse column, the adopted concrete
permutation terminal is an EXPLICIT expression:
`eq(tau, point) * ((0 - 1) + rho * (0 - 1))`. -/
theorem probe_permutation_terminal_at_one_routed_wire
    (c : Verifier.Config) (hr : c.numRouted = 1) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput)
    (h0 : t.normInverse.getD 0 Verifier.zero = Verifier.zero)
    (h1 : t.normInverse.getD 1 Verifier.zero = Verifier.zero)
    (point : List Verifier.Ext3) :
    Norm.permutationTerminal c ch t point =
      Verifier.mul (Norm.eqEvaluation ch.tau point)
        (Verifier.add (Verifier.sub Verifier.zero Norm.one)
          (Verifier.mul ch.rho (Verifier.sub Verifier.zero Norm.one))) := by
  simp only [Norm.permutationTerminal, hr, run_wires_one, Norm.wireStep, Norm.wireStart,
    hr, Nat.add_zero, h0, h1,
    Algebra.vzero_mul, Algebra.vzero_add, Algebra.vsub_self, Algebra.vmul_zero,
    Algebra.vadd_zero, Algebra.vone_mul]

/-- Concrete challenges at the shape this module's configuration uses: thirteen
tau coordinates. -/
def probeChallenges : Norm.Challenges :=
  ⟨Verifier.zero, Verifier.zero, Verifier.zero, Verifier.zero, Verifier.zero,
    Verifier.zero, Verifier.zero, List.replicate 13 Verifier.zero⟩

theorem probe_eq_at_thirteen_zero_coordinates :
    Norm.eqEvaluation (List.replicate 13 Verifier.zero) (List.replicate 13 Verifier.zero) =
      Norm.one := by rfl

/-- The explicit expression is NOT identically zero: at thirteen zero tau
coordinates, thirteen zero point coordinates and `rho = 0` it is `0 - 1`. -/
theorem probe_one_routed_wire_terminal_is_not_zero
    (c : Verifier.Config) (hr : c.numRouted = 1) (t : Verifier.NormTerminalInput)
    (h0 : t.normInverse.getD 0 Verifier.zero = Verifier.zero)
    (h1 : t.normInverse.getD 1 Verifier.zero = Verifier.zero) :
    Norm.permutationTerminal c probeChallenges t (List.replicate 13 Verifier.zero) ≠
      Verifier.zero := by
  rw [probe_permutation_terminal_at_one_routed_wire c hr probeChallenges t h0 h1 _]
  show Verifier.mul (Norm.eqEvaluation (List.replicate 13 Verifier.zero)
      (List.replicate 13 Verifier.zero)) _ ≠ _
  rw [probe_eq_at_thirteen_zero_coordinates]
  show Verifier.mul Norm.one (Verifier.add (Verifier.sub Verifier.zero Norm.one)
    (Verifier.mul Verifier.zero (Verifier.sub Verifier.zero Norm.one))) ≠ _
  rw [Algebra.vzero_mul, Algebra.vadd_zero, Algebra.vone_mul]
  intro h
  exact absurd ((Algebra.vsub_eq_zero_iff Verifier.zero Norm.one).mp h) (by decide)

/-- **THE OBSTRUCTION, QUANTIFIED.**  Acceptance at ANY configuration with one
routed wire, an all-zero norm-inverse column and no public inputs, on a proof
whose derived log claim is zero, FORCES a coincidence between the DERIVED tau,
the DERIVED sumcheck point and the DERIVED rho challenge.  So `numRouted = 0` is
not a convenience at the adopted all-zero claim record: acceptance at
`numRouted = 1` is EQUIVALENT to a challenge coincidence, not merely "not found
here". -/
theorem probe_acceptance_at_one_routed_wire_forces_a_challenge_coincidence
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (c : Verifier.Config) (p : Verifier.Proof)
    (hr : c.numRouted = 1)
    (h0 : p.used.logNormInverse.getD 0 Verifier.zero = Verifier.zero)
    (h1 : p.used.logNormInverse.getD 1 Verifier.zero = Verifier.zero)
    (hpi : p.publicInputs = [])
    (hzero : (Verifier.derivedRounds (derivedEngine thash khash P) c p).logClaim =
      Verifier.zero)
    (hacc : Verifier.verify (derivedEngine thash khash P) (derivedPin khash) 1 c p = .ok ()) :
    Verifier.mul
        (Norm.eqEvaluation
          (Norm.challengesFromInitial
            ((derivedEngine thash khash P).initialTranscript c p)).tau
          (Verifier.derivedRounds (derivedEngine thash khash P) c p).logPoint)
        (Verifier.add (Verifier.sub Verifier.zero Norm.one)
          (Verifier.mul
            (Norm.challengesFromInitial
              ((derivedEngine thash khash P).initialTranscript c p)).rho
            (Verifier.sub Verifier.zero Norm.one))) = Verifier.zero := by
  have hterm := (Verifier.verify_success_checks (derivedEngine thash khash P)
    (derivedPin khash) 1 c p hacc).2.2.2.2.2.2.2.2.2.1
  rw [hzero] at hterm
  rw [← probe_permutation_terminal_at_one_routed_wire c hr _
    (Verifier.normTerminalInput p) h0 h1 _]
  rw [← hterm]
  show _ = Norm.normEvaluation c ((derivedEngine thash khash P).initialTranscript c p)
    (Verifier.normTerminalInput p) _
  simp only [Norm.normEvaluation, Norm.evaluate,
    Norm.public_input_empty_is_zero c (Verifier.normTerminalInput p) _ _ hpi,
    Algebra.vmul_zero, Algebra.vadd_zero]

/-! ## 12. THE PROFILE HYPOTHESIS AT A SHARP PROFILE

`derived_acceptance`'s hypothesis `PinnedWhirProfile.profileOk P derivedConfig = true` is
not trivialised by `P` being a stand-in: it survives a profile whose parameter decoder
REJECTS every nonempty WHIR encoding and whose digest and table digest are NON-constant
functions.  What that shows is where the content of gate 4 actually sits -- in
`derivedConfig`'s EMPTY deployment byte strings, not in `P`. -/

/-- A profile whose parameter decoder REJECTS every nonempty WHIR encoding and
whose digest and table digest are NON-constant functions. -/
def probeSharpProfile : PinnedWhirProfile.Profile where
  decodeParams := fun b => if b = [] then some derivedParams else none
  digest := fun wp => if wp.numVariables = 21 then Verifier.testRoot else ⟨1, by decide⟩
  tableDigest := fun n => if n = 21 then Verifier.testRoot else ⟨1, by decide⟩
  tableProtocolId := fun n => if n = 21 then [] else [⟨0, by decide⟩]
  sessionId := []

theorem probe_sharp_profile_passes :
    PinnedWhirProfile.profileOk probeSharpProfile derivedConfig = true := by rfl

theorem probe_sharp_profile_rejects_nonempty_whir_bytes :
    probeSharpProfile.decodeParams [⟨0, by decide⟩] = none := by rfl

theorem probe_sharp_profile_digest_is_not_constant :
    probeSharpProfile.tableDigest 21 ≠ probeSharpProfile.tableDigest 20 := by decide

/-- **THE ACCEPTANCE AT THE SHARP PROFILE.**  Use this in place of, or beside,
`derived_acceptance_at_the_profile_witness`: the profile hypothesis is discharged
at a profile that is not a constant stand-in. -/
theorem probe_acceptance_at_the_sharp_profile (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (derivedEngine thash khash probeSharpProfile) (derivedPin khash) 1
      derivedConfig derivedProof = .ok () :=
  derived_acceptance thash khash probeSharpProfile probe_sharp_profile_passes

/-- **AND THE REASON GATE 4 IS CHEAP HERE.**  At `derivedConfig` the deployment
gate reads only EMPTY byte strings, so gate 4's content is bounded by
`derivedConfig`'s deployment bytes, not by `P`. -/
theorem probe_derived_config_deployment_bytes_are_empty :
    derivedConfig.whirEncoding = [] ∧ derivedConfig.whirProtocolId = [] ∧
      derivedConfig.whirSessionId = [] ∧ derivedConfig.gatesEncoding = [] := by decide

end Audit.Wire3.DerivedAcceptance
