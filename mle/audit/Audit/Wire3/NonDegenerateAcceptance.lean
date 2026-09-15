import Audit.Wire3.IndexHalfTransport
import Audit.Wire3.Integrated
import Audit.Wire3.Norm
import Audit.Wire3.PinnedWhirProfile

/-!
# Non-degenerate acceptance: the shape arithmetic no longer blocks it

## **HONESTY SECTION -- READ BEFORE USING ANY THEOREM BELOW**

**WHAT THIS MODULE ESTABLISHES.**  Sections 1 to 4 record, as theorems of this tree, the
FOUR independent reasons the verifier's acceptance antecedent was unsatisfiable at every
realistic configuration in the adopted adaptive line.  Section 5 then exhibits a CLOSED,
CONCRETE acceptance equation of the adopted `Verifier.verify` at the ENVELOPE-MAXIMAL
configuration

    `Verifier.verify wideEngine widePin 1 maximalConfig maximalProof = Except.ok ()`

-- `160` wires, `80` routed wires, `80` constants, `13` degree bits, `8` index bits,
`255` gate rows, `123` gate constraints, quotient degree `8`: every one of these is the
LARGEST value `Verifier.envelope` (`Verifier.lean:97-105`) permits.  The seven-wire
instance `wideConfig` is kept as the small example.  Section 6 runs the model engine
through the adopted `Integrated.verify`, at `wideConfig` and again at a fifteen-wire
configuration.

The maximal instance is not decoration.  It is the reason the field-by-field audit of
`wideEngine` below is CONCLUSIVE rather than enumerative: the same two moved fields, and
nothing else, carry acceptance from the one-wire fixture corner all the way to the
envelope ceiling, so NO unmoved fixture field pins ANY configuration quantity read inside
`Verifier.verify`.  Had some other fixture field silently pinned a width, a row count or a
degree, the maximal instance could not have closed.

**WHAT THIS MODULE DOES *NOT* ESTABLISH.**  `wideEngine` and `wideIntegratedEngine` are
MODEL engines.  `wideEngine` is the adopted `Verifier.testEngine` with exactly the two
fields moved that the length pins force to move (`sampleIndices`, `initialObservation`).
`wideIntegratedEngine` is built from `wideEngine`, NOT from `Integrated.exampleEngine`: it
borrows two field VALUES from `Integrated.exampleEngine` (`publicInputsHash`, `parseWhir`)
and keeps everything else from `wideEngine`.  Every other field of both keeps the
fixtures' deliberately trivial choices.  They are NOT the adopted
`SoundnessAssembly.engine`, and nothing below is an acceptance exhibition for the explicit
engine.  Concretely, the following are still OPEN for the explicit engine and are NOT
discharged anywhere in this module:

* **the WHIR tail.**  `wideEngine.whirTail` is the fixture's constant `true`, and
  `wideIntegratedEngine.parseWhir` echoes the context's own expected claims back at it.
  No Merkle query, out-of-domain check, WHIR sumcheck, terminal-row authentication,
  final-polynomial consistency or exact-EOF check is performed.
* **the gate evaluation.**  Section 6 does run the adopted `GatesComplete.evalCombined`
  through the adopted `Integrated.evaluateGate`, but on a two-row stand-in gate table
  supplied by a stand-in ABI decoder (`wideDecoder`), and with a stand-in public-input
  hash.  It is not the deployed gate metadata.
* **`deploymentValid`.**  `wideEngine.deploymentValid` is the fixture's constant `true`;
  canonical metadata, canonical `kIs`/subgroup powers, supported-gate validation and the
  canonical WHIR profile are therefore not checked at this instance.
* **`configurationHash c = pin.configDigest`.**  `wideEngine.configurationHash` is the
  fixture's constant `Verifier.testRoot`, so this gate is satisfied by fiat, not by a
  collision-resistant digest of the configuration.
* **`Integrated.verify`'s two extra gates** are discharged HERE (Section 6) only for the
  stand-in decoder and stand-in public-input hash just described.
* **HOW MUCH OF `Verifier.verify` IS REAL HERE.**  `Verifier.verify` (`:411-425`) has nine
  guard conditions: the chain identifier, `configurationHash`, `envelope`,
  `deploymentValid`, `shape`, the four tau/index lengths, the log terminal, `verifyWhir`,
  and the gate terminal.  In Section 5 exactly THREE of those nine are real -- `envelope`,
  `shape`, and the four tau/index lengths.  The other six are fiat.  In particular: the
  log terminal and the gate terminal are the fixture's constant `Verifier.zero` at every
  argument, and `commitRound` is the fixture's constant, so gates 7 and 9 carry no
  arithmetic; the derived transcript is the EMPTY byte string at every configuration and
  proof, so this instance has no Fiat--Shamir dependence at all; and
  `replicatedIndexSampler` returns the ALL-ZERO index point -- the repair fixes the lane
  LENGTH, not the lane CONTENT.  All three roots of `wideProof` are moreover the same
  constant `Verifier.testRoot`, which the fiat `parseWhir` cannot see but the adopted
  `InstalledWhirParse.concreteParseWhir` would.  In Section 6, of the ELEVEN guards
  (`Integrated.verify`'s two preflights plus those nine), SEVEN are real: the two
  preflights, `envelope`, `shape`, the four tau/index lengths, the log terminal and the
  gate terminal.  Gate 8 there is content-free BY CONSTRUCTION: the echoing `parseWhir`
  makes `Verifier.verifyWhir` true at every context and every proof
  (`integrated_whir_gate_is_content_free`).
* **the adopted adaptive failure events.**  This instance does NOT make
  `AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent` non-empty and does NOT lift the
  vacuity recorded in
  `IndexHalfTransport.adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`:
  that event is indexed by the adopted explicit engine and by the fixture used-claims
  record `IndexHalfTransport.defaultClaims`, neither of which appears here.

**A LESSON THIS MODULE LEARNED THE HARD WAY.**  An earlier revision asserted that the
parametric acceptance statement of Section 5 COULD NOT be shipped, because closing the
last four guards by definitional reduction with the WHIR byte strings still symbolic
exceeds Lean's default recursion depth and raising it needs a forbidden option command.
That assertion was FALSE, and it is now deleted: the statement is shipped below as
`model_acceptance_for_any_bounded_whir_bytes`, proved by not going through definitional
reduction at all -- via `verify_of_checks`, a CONSTRUCTOR companion to the adopted
destructor `Verifier.verify_success_checks`.  A claim that Lean CANNOT prove something is
the one kind of negative claim an audit module must not get wrong: unlike a positive
claim it is not checked by the kernel, so nothing but care stands behind it.  The general
rule it yields: "my tactic script did not close this goal" is evidence about the script,
never about the theorem.

**THE PRECISE CLAIM.**  *The length pins (`Verifier.shape`, `Verifier.lean:134-144`) and
the numeric envelope (`Verifier.envelope`, `:97-105`) alone no longer make acceptance
impossible at a non-degenerate configuration -- indeed not even at the widest
configuration the envelope permits.*  What this module removes is exactly the
`Verifier.shape`/`Verifier.envelope` obstruction, and ONLY that.  It does NOT localise the
residual obstruction for the explicit engine -- nothing below mentions
`ExplicitEngine.explicitEngine`.  In particular the explicit engine's `deploymentValid` is
not purely semantic: it is `ExplicitEngine.explicitDeployment` (`ExplicitEngine.lean:495-496`),
a WHIR-encoding pin conjoined with `PinnedWhirProfile.profileOk`, whose
`PinnedWhirProfile.canonicalProfileCheck` (`PinnedWhirProfile.lean:216-220`) imposes the
NUMERIC two-sided bound `1 <= wp.numVariables <= 21` with
`wp.numVariables = c.degreeBits + c.indexBits` (`ExplicitEngine.lean:722`), which is
arithmetic of the same kind as the envelope's.  That bound is satisfiable at the maximal
instance and only just: the envelope caps `degreeBits <= 13` and `indexBits <= 8`, which
sum to exactly the profile ceiling `21`.  Recorded as
`maximal_config_meets_the_profile_variable_budget`.

**NON-VACUITY.**  Sections 5 and 6's headline results are closed equations, so they carry
no hypothesis to be vacuous about.  Sections 1 to 4 are IMPOSSIBILITY results: their
antecedent is acceptance (or, in Section 4, an engine property alone), and each is shipped
with an explicit satisfiability witness -- `trivial_index_sampling_hypotheses_satisfiable`,
`fixture_claims_hypotheses_satisfiable`, `degree_bit_pin_hypotheses_satisfiable`,
`unit_index_sampling_hypotheses_satisfiable`, `empty_challenge_list_hypothesis_satisfiable`
-- pointing at the adopted `Verifier.positive_model_verification` and the adopted
`Integrated.positive_integrated_norm_helper_path`.  Their antecedents are therefore
inhabited; what the theorems prove is that they are inhabited ONLY degenerately, which is
the content rather than a defect.  Section 4's conclusion is unconditional rejection, so
its non-vacuity is of the opposite kind: `Integrated.verify` is NOT identically
`.error .configuration`, as Section 6's `integrated_acceptance_at_nondegenerate_config`
witnesses.

## The four causes, in source terms

**CAUSE 1 -- the used-claims fixture.**  `Verifier.shape` (`Verifier.lean:134-144`) pins
`p.used.logPreprocessed.length = c.numConstants + c.numRouted`,
`p.used.logWitness.length = c.numWires` and
`p.used.logNormInverse.length = 2 * c.numRouted` (`:138-139`).  The adopted
`RunLevelTransportAudit.realizedProof` (`RunLevelTransportAudit.lean:596-601`) inherits
`used` from `Verifier.testProof` (`Verifier.lean:596-600`), whose five lists have lengths
`1, 1, 0, 1, 1`.  Hence `numWires = 1`, `numRouted = 0`, `numConstants = 1`.  The adopted
`IndexHalfTransport.matchingClaims` (`IndexHalfTransport.lean:376-382`) removes exactly
this obstruction, and `IndexHalfTransport.shape_satisfiable_at_matching_claims`
(`:394-401`) is its payoff.
`IndexHalfTransport.acceptance_forces_degenerate_config_at_fixture_claims` (`:365-370`) is
the adopted statement of the same fact.  `acceptance_at_fixture_claims_forces_degenerate_config`
below is a TRANSCRIPTION of it with `IndexHalfTransport.defaultClaims` unfolded to
`Verifier.testProof.used` (the two are equal by definition, `IndexHalfTransport.lean:295`):
the two statements are definitionally interderivable and the two tactic proofs are
identical.  It is restated here only so that this module carries all causes in one place
-- it is NOT an independent proof, and it adds nothing the adopted tree did not already
have.

**CAUSE 2 -- the trivial engine's index sampling.**  This one survives cause 1's repair.
`Verifier.testEngine.sampleIndices = fun _ _ _ => ⟨[], []⟩` (`Verifier.lean:602-610`,
the field at `:606`);
`Verifier.derivedIndices e c p = e.sampleIndices (derivedRounds e c p).transcript p.used
c.indexBits` (`:389-390`); and `Verifier.verify` rejects unless
`idx.log.length = c.indexBits ∧ idx.gate.length = c.indexBits` (`:420-421`).  So the
trivial engine forces `c.indexBits = 0`.  But `Verifier.envelope` (`:97-105`), checked at
`:413`, demands `width c ≤ 2 ^ c.indexBits` (`:104`), and
`width c = max (numConstants + numRouted) (max numWires (2 * numRouted))` (`:92`).  Hence
`indexBits = 0` implies `width c ≤ 1` implies `numWires ≤ 1` -- the same degeneracy,
reached WITHOUT touching `used`.  Section 1 proves this, for an ARBITRARY engine, and the
hypothesis needed is only that the LOG lane comes back empty
(`empty_log_lane_alone_forces_one_wire`).

**CAUSE 3 -- the degree-bit pin.**  The adopted `Verifier.testEngine`'s
`initialObservation` (`Verifier.lean:604`) returns a ONE-element `logTau` and a
one-element `gateTau`, and `Verifier.verify` rejects unless
`i.logTau.length = c.degreeBits` (`:420`).  So that fixture pins `c.degreeBits = 1` at an
ARBITRARY engine, pin, chain identifier, configuration and proof, independently of causes
1 and 2.  Section 3 proves this on the log lane
(`unit_log_tau_forces_one_degree_bit`) and, separately, on the gate lane
(`unit_gate_tau_forces_one_degree_bit`), with the fixture instance
`fixture_engine_forces_one_degree_bit`.

**CAUSE 4 -- the integrated path is dead outright.**  Strictly stronger than any of the
three above.  The adopted `Norm.checkedNormEvaluation` (`Norm.lean:353`) returns `none`
unless `i.logChallenges.length = 7`, and the fixture observation's challenge list is
EMPTY (`Verifier.lean:604`).  `Integrated.verify` (`Integrated.lean:59-66`) runs
`normResult` first and returns `.error .configuration` when it is `none`.  So
`Integrated.verify Verifier.testEngine decode pin chain c p = .error .configuration`
UNCONDITIONALLY -- at every decoder, pin, chain identifier, configuration and proof.  This
is not "acceptance forces a degenerate configuration"; it is "acceptance never happens".
Section 4 proves it for an arbitrary engine with that empty list
(`empty_challenge_list_blocks_integrated_acceptance`) and instantiates it at the fixture
(`adopted_test_engine_is_integrated_dead`).  The repair is the seven-value challenge
layout `sevenValueChallenges` of Section 5, which is LITERALLY the adopted
`Integrated.exampleEngine`'s own list (`Integrated.lean:200`), not a new object -- see
`seven_value_layout_is_the_adopted_one`, proved by `rfl`.

Section 4 also records that the adopted `Integrated.exampleEngine` is DOUBLY pinned: its
`sampleIndices` returns ONE-element lanes (`Integrated.lean:201`) and its
`initialObservation` returns a one-element `logTau` (`:200`).  The first alone forces
`c.numWires ≤ 2` at an arbitrary engine (`unit_index_sampling_forces_two_wires`), the
second is cause 3.

The single adopted accepting instance of `Verifier.verify`,
`Verifier.positive_model_verification` (`Verifier.lean:612-614`) at `Verifier.testConfig`
(`:588-594`: `degreeBits 1`, `numWires 1`, `numRouted 0`, `indexBits 0`), is degenerate on
counts 1, 2 and 3; Section 2 ends by recording the first two, from the headline theorems.

Section 5's repair of cause 2 is the sampler `replicatedIndexSampler`, which returns
`List.replicate n Verifier.zero` on both lanes and therefore satisfies the `:420-421`
length gate at ANY `c.indexBits`; `Verifier.Engine.sampleIndices` receives `c.indexBits`
as its third argument, so this is a legal engine field.  Its repair of cause 3 is
`configuredInitialObservation`, which generalises `logTau` and `gateTau` the same way, to
`List.replicate c.degreeBits Verifier.zero`, and which also carries the seven-value
challenge list that repairs cause 4.
-/

namespace Audit.Wire3.NonDegenerateAcceptance

open Verifier

/-! ## 1. CAUSE 2: TRIVIAL INDEX SAMPLING FORCES A ONE-WIRE CONFIGURATION

Every theorem in this section holds for an ARBITRARY `Verifier.Engine`: nothing about the
engine is used beyond the value its `sampleIndices` field returns. -/

/-- (1) The wire count never exceeds the packed constituent width
(`Verifier.lean:92`). -/
theorem width_lower_bounds_wire_count (c : Verifier.Config) : c.numWires ≤ Verifier.width c :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- (1) **THE ENVELOPE ARITHMETIC.**  `Verifier.envelope` requires
`width c ≤ 2 ^ c.indexBits` (`Verifier.lean:104`).  At zero index bits the right-hand
side is `1`, so the configuration has at most one wire.  No engine is involved. -/
theorem envelope_at_zero_index_bits_forces_one_wire (c : Verifier.Config)
    (henv : Verifier.envelope c = true) (hzero : c.indexBits = 0) : c.numWires ≤ 1 := by
  simp only [Verifier.envelope, decide_eq_true_eq] at henv
  have hw : Verifier.width c ≤ 2 ^ c.indexBits := henv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hzero] at hw
  exact Nat.le_trans (width_lower_bounds_wire_count c) (by simpa using hw)

/-- (1) The same, straight from acceptance: the adopted `Verifier.verify_success_checks`
returns `Verifier.envelope c = true` from any accepting run.  ARBITRARY engine. -/
theorem acceptance_at_zero_index_bits_forces_one_wire (e : Verifier.Engine)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hzero : c.indexBits = 0) (hacc : Verifier.verify e pin chain c p = .ok ()) :
    c.numWires ≤ 1 :=
  envelope_at_zero_index_bits_forces_one_wire c
    (Verifier.verify_success_checks e pin chain c p hacc).2.2.1 hzero

/-- (1) **THE INDEX-LANE LENGTH GATE.**  `Verifier.verify` rejects unless the sampled log
lane has exactly `c.indexBits` entries (`Verifier.lean:420-421`), and
`Verifier.derivedIndices` is literally an application of the engine's `sampleIndices`
(`:389-390`).  An engine that returns the empty lane therefore pins `c.indexBits = 0`.
ARBITRARY engine; only the log lane of the hypothesis is used. -/
theorem trivial_index_sampling_forces_zero_index_bits (e : Verifier.Engine)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hsample : ∀ t u n, e.sampleIndices t u n = ⟨[], []⟩)
    (hacc : Verifier.verify e pin chain c p = .ok ()) : c.indexBits = 0 := by
  have hlen := (Verifier.verify_success_checks e pin chain c p hacc).2.2.2.2.2.2.2.1
  rw [Verifier.derivedIndices, hsample] at hlen
  exact hlen.symm

/-- (1) **HEADLINE OF CAUSE 2.**  An engine whose index sampler returns the empty LOG lane
can only ever accept a configuration with at most one wire -- no matter what used-claims
record the proof carries, so cause 1's repair does not touch this.  The gate lane is not
mentioned: this is the weakest hypothesis under which the argument runs, and it is what
the proof actually uses.  The quantifier achieved is the full one: ARBITRARY
`Verifier.Engine`, arbitrary `Pinned`, arbitrary chain identifier, arbitrary configuration
and arbitrary proof. -/
theorem empty_log_lane_alone_forces_one_wire (e : Verifier.Engine) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hsample : ∀ t u n, (e.sampleIndices t u n).log = [])
    (hacc : Verifier.verify e pin chain c p = .ok ()) : c.numWires ≤ 1 := by
  have hchecks := Verifier.verify_success_checks e pin chain c p hacc
  have hlen := hchecks.2.2.2.2.2.2.2.1
  rw [Verifier.derivedIndices, hsample] at hlen
  exact acceptance_at_zero_index_bits_forces_one_wire e pin chain c p hlen.symm hacc

/-- (1) The both-lanes form, for callers that have the fixture engine in hand rather than
a lane equation. -/
theorem acceptance_at_trivial_index_sampling_forces_one_wire (e : Verifier.Engine)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hsample : ∀ t u n, e.sampleIndices t u n = ⟨[], []⟩)
    (hacc : Verifier.verify e pin chain c p = .ok ()) : c.numWires ≤ 1 :=
  empty_log_lane_alone_forces_one_wire e pin chain c p
    (fun t u n => congrArg Verifier.IndexPoints.log (hsample t u n)) hacc

/-- (1) The adopted trivial engine does satisfy that hypothesis
(`Verifier.lean:606`). -/
theorem adopted_test_engine_samples_empty_index_lanes :
    ∀ t u n, Verifier.testEngine.sampleIndices t u n = ⟨[], []⟩ := fun _ _ _ => rfl

/-- (1) **NON-VACUITY OF THE SECTION.**  The antecedent of
`empty_log_lane_alone_forces_one_wire` is inhabited: the adopted
`Verifier.positive_model_verification` is an accepting run of exactly such an engine.
What the section proves is that every such run is degenerate. -/
theorem trivial_index_sampling_hypotheses_satisfiable :
    (∀ t u n, Verifier.testEngine.sampleIndices t u n = ⟨[], []⟩) ∧
      Verifier.verify Verifier.testEngine ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1
        Verifier.testConfig Verifier.testProof = .ok () :=
  ⟨adopted_test_engine_samples_empty_index_lanes, Verifier.positive_model_verification⟩

/-- (1) Applied to the only adopted accepting instance. -/
theorem adopted_positive_model_has_one_wire : Verifier.testConfig.numWires ≤ 1 :=
  acceptance_at_trivial_index_sampling_forces_one_wire Verifier.testEngine
    ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig Verifier.testProof
    adopted_test_engine_samples_empty_index_lanes Verifier.positive_model_verification

/-! ## 2. CAUSE 1: THE FIXTURE USED-CLAIMS RECORD FORCES A DEGENERATE CONFIGURATION

The adopted tree already records this as
`IndexHalfTransport.acceptance_forces_degenerate_config_at_fixture_claims`
(`IndexHalfTransport.lean:365-370`), phrased at `IndexHalfTransport.defaultClaims`, which
is BY DEFINITION `Verifier.testProof.used` (`:295`).  What follows is a TRANSCRIPTION of
that statement with `defaultClaims` unfolded: the two statements are definitionally
interderivable and the two tactic proofs are identical modulo that one identifier.  It is
restated here only so that this module carries all four causes in one place.  It is NOT an
independent proof and it adds nothing the adopted tree did not already have. -/

/-- (2) The three length pins of `Verifier.shape` (`Verifier.lean:138-139`) against the
fixture's list lengths `1, 1, 0`. -/
theorem shape_at_fixture_claims_forces_degenerate_config (pin : Verifier.Pinned)
    (c : Verifier.Config) (p : Verifier.Proof) (hu : p.used = Verifier.testProof.used)
    (hs : Verifier.shape pin c p = true) :
    c.numWires = 1 ∧ c.numRouted = 0 ∧ c.numConstants = 1 := by
  have hlit : Verifier.testProof.used
      = ⟨[Verifier.zero], [Verifier.zero], [], [Verifier.zero], [Verifier.zero]⟩ := rfl
  simp only [Verifier.shape, decide_eq_true_eq, hu, hlit, List.length_cons,
    List.length_nil] at hs
  omega

/-- (2) **HEADLINE OF CAUSE 1 (TRANSCRIBED FROM THE ADOPTED TREE).**  Acceptance at any
proof carrying the fixture used-claims record forces `numWires = 1`, `numRouted = 0`,
`numConstants = 1`.  The quantifier achieved is the full one: ARBITRARY
`Verifier.Engine`, arbitrary `Pinned`, arbitrary chain identifier, arbitrary configuration
and arbitrary proof.  See the section docstring: this is the adopted
`IndexHalfTransport.acceptance_forces_degenerate_config_at_fixture_claims` with
`defaultClaims` unfolded, not a second proof of it. -/
theorem acceptance_at_fixture_claims_forces_degenerate_config (e : Verifier.Engine)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hu : p.used = Verifier.testProof.used)
    (hacc : Verifier.verify e pin chain c p = .ok ()) :
    c.numWires = 1 ∧ c.numRouted = 0 ∧ c.numConstants = 1 :=
  shape_at_fixture_claims_forces_degenerate_config pin c p hu
    (Verifier.verify_success_checks e pin chain c p hacc).2.2.2.2.1

/-- (2) The definitional interderivability, made explicit rather than asserted: the
adopted theorem discharges the transcription as a bare application, and conversely. -/
theorem fixture_claims_statements_are_interderivable :
    (∀ (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
        (p : Verifier.Proof), p.used = Verifier.testProof.used →
        Verifier.verify e pin chain c p = .ok () →
        c.numWires = 1 ∧ c.numRouted = 0 ∧ c.numConstants = 1) ∧
      (∀ (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
        (p : Verifier.Proof), p.used = IndexHalfTransport.defaultClaims →
        Verifier.verify e pin chain c p = .ok () →
        c.numWires = 1 ∧ c.numRouted = 0 ∧ c.numConstants = 1) :=
  ⟨IndexHalfTransport.acceptance_forces_degenerate_config_at_fixture_claims,
    acceptance_at_fixture_claims_forces_degenerate_config⟩

/-- (2) **NON-VACUITY OF THE SECTION.**  Again the antecedent is inhabited, by the adopted
positive model, whose proof record is `Verifier.testProof` itself. -/
theorem fixture_claims_hypotheses_satisfiable :
    Verifier.testProof.used = Verifier.testProof.used ∧
      Verifier.verify Verifier.testEngine ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1
        Verifier.testConfig Verifier.testProof = .ok () :=
  ⟨rfl, Verifier.positive_model_verification⟩

/-- (2) **THE ADOPTED ACCEPTING INSTANCE IS DEGENERATE ON BOTH COUNTS, INDEPENDENTLY.**
The left conjunct comes from the index sampler alone (Section 1), the right from the used
claims alone (Section 2).  Removing either cause leaves the other standing; that is why
the repair in Section 5 has to move the sampler as well as the claims. -/
theorem adopted_positive_model_is_degenerate_on_both_counts :
    Verifier.testConfig.numWires ≤ 1 ∧
      (Verifier.testConfig.numWires = 1 ∧ Verifier.testConfig.numRouted = 0 ∧
        Verifier.testConfig.numConstants = 1) :=
  ⟨adopted_positive_model_has_one_wire,
    acceptance_at_fixture_claims_forces_degenerate_config Verifier.testEngine
      ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Verifier.testConfig Verifier.testProof rfl
      Verifier.positive_model_verification⟩

/-! ## 3. CAUSE 3: THE UNIT TAU LANE PINS THE DEGREE BITS

`Verifier.verify` rejects unless `i.logTau.length = c.degreeBits` and
`i.gateTau.length = c.degreeBits` (`Verifier.lean:420`).  The adopted
`Verifier.testEngine.initialObservation` (`:604`) returns `[Verifier.zero]` on both lanes.
So the fixture engine pins `c.degreeBits = 1` -- a third cause, independent of the two
above, and one the earlier revision of this module recorded only in a docstring.  As in
Section 1, every theorem here holds at an ARBITRARY engine. -/

/-- (3) **HEADLINE OF CAUSE 3, LOG LANE.**  An engine whose initial observation returns a
one-element `logTau` forces `c.degreeBits = 1`, at an ARBITRARY engine, pin, chain
identifier, configuration and proof. -/
theorem unit_log_tau_forces_one_degree_bit (e : Verifier.Engine) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hobs : ∀ cfg s, (e.initialObservation cfg s).logTau = [Verifier.zero])
    (hacc : Verifier.verify e pin chain c p = .ok ()) : c.degreeBits = 1 := by
  have hlen := (Verifier.verify_success_checks e pin chain c p hacc).2.2.2.2.2.1
  rw [Verifier.Engine.initialTranscript, hobs] at hlen
  exact hlen.symm

/-- (3) **THE SAME PIN SITS ON THE GATE LANE.**  Either lane alone suffices, so the cause
is doubly redundant in the fixture. -/
theorem unit_gate_tau_forces_one_degree_bit (e : Verifier.Engine) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hobs : ∀ cfg s, (e.initialObservation cfg s).gateTau = [Verifier.zero])
    (hacc : Verifier.verify e pin chain c p = .ok ()) : c.degreeBits = 1 := by
  have hlen := (Verifier.verify_success_checks e pin chain c p hacc).2.2.2.2.2.2.1
  rw [Verifier.Engine.initialTranscript, hobs] at hlen
  exact hlen.symm

/-- (3) The adopted fixture engine satisfies both hypotheses (`Verifier.lean:604`). -/
theorem adopted_test_engine_has_unit_tau_lanes :
    (∀ cfg s, (Verifier.testEngine.initialObservation cfg s).logTau = [Verifier.zero]) ∧
      (∀ cfg s, (Verifier.testEngine.initialObservation cfg s).gateTau = [Verifier.zero]) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- (3) So the fixture engine pins the degree bits, independently of causes 1 and 2, at an
arbitrary pin, chain identifier, configuration and proof. -/
theorem fixture_engine_forces_one_degree_bit (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Verifier.verify Verifier.testEngine pin chain c p = .ok ()) : c.degreeBits = 1 :=
  unit_log_tau_forces_one_degree_bit _ pin chain c p adopted_test_engine_has_unit_tau_lanes.1 hacc

/-- (3) **NON-VACUITY OF THE SECTION.**  The antecedent is inhabited by the adopted
positive model, whose configuration indeed has `degreeBits = 1`. -/
theorem degree_bit_pin_hypotheses_satisfiable :
    (∀ cfg s, (Verifier.testEngine.initialObservation cfg s).logTau = [Verifier.zero]) ∧
      Verifier.verify Verifier.testEngine ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1
        Verifier.testConfig Verifier.testProof = .ok () :=
  ⟨adopted_test_engine_has_unit_tau_lanes.1, Verifier.positive_model_verification⟩

/-- (3) Applied to the only adopted accepting instance. -/
theorem adopted_positive_model_has_one_degree_bit : Verifier.testConfig.degreeBits = 1 :=
  fixture_engine_forces_one_degree_bit ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1
    Verifier.testConfig Verifier.testProof Verifier.positive_model_verification

/-! ## 4. CAUSE 4: THE INTEGRATED PATH IS DEAD OUTRIGHT AT THE FIXTURE OBSERVATION

This cause is strictly stronger than causes 1 to 3: its conclusion is not "acceptance
forces a degenerate configuration" but "acceptance never happens".  The adopted
`Norm.checkedNormEvaluation` (`Norm.lean:353`) returns `none` unless the initial
observation carries exactly SEVEN log challenges, and the adopted fixture observation
(`Verifier.lean:604`) carries NONE.  `Integrated.verify` (`Integrated.lean:59-66`) runs
that adapter first.

This section also records the double pin on the adopted `Integrated.exampleEngine`. -/

/-- (4) **HEADLINE OF CAUSE 4.**  An engine whose initial observation carries an empty
log-challenge list can never be accepted by `Integrated.verify` AT ALL -- at any decoder,
any pin, any chain identifier, any configuration and any proof.  ARBITRARY engine. -/
theorem empty_challenge_list_blocks_integrated_acceptance (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hobs : ∀ cfg s, (e.initialObservation cfg s).logChallenges = []) :
    Integrated.verify e decode pin chain c p = .error .configuration := by
  have hn : Integrated.normResult (Integrated.modelEngine e decode) c p = none := by
    refine Norm.checked_adapter_rejects_wrong_challenge_count _ _ _ _ ?_
    show ((Integrated.modelEngine e decode).initialTranscript c p).logChallenges.length ≠ 7
    rw [show (Integrated.modelEngine e decode).initialTranscript c p
        = e.initialTranscript c p from rfl, Verifier.Engine.initialTranscript, hobs]
    decide
  simp only [Integrated.verify, hn]

/-- (4) The adopted fixture engine has that empty list, so it is INTEGRATED-dead. -/
theorem adopted_test_engine_is_integrated_dead (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) :
    Integrated.verify Verifier.testEngine decode pin chain c p = .error .configuration :=
  empty_challenge_list_blocks_integrated_acceptance _ decode pin chain c p (fun _ _ => rfl)

/-- (4) **NON-VACUITY OF THE HYPOTHESIS.**  It is satisfied by the adopted fixture engine.
(The non-vacuity of the CONCLUSION is of the opposite kind and lives in Section 6:
`Integrated.verify` is not identically `.error .configuration`, as
`integrated_acceptance_at_nondegenerate_config` shows.) -/
theorem empty_challenge_list_hypothesis_satisfiable :
    ∀ cfg s, (Verifier.testEngine.initialObservation cfg s).logChallenges = [] :=
  fun _ _ => rfl

/-- (4) **THE UNIT INDEX LANE.**  An engine whose index sampler returns a ONE-element lane
pins `c.indexBits = 1`, hence `width c ≤ 2`, hence at most two wires.  ARBITRARY engine.
This is the adopted `Integrated.exampleEngine`'s behaviour (`Integrated.lean:201`). -/
theorem unit_index_sampling_forces_two_wires (e : Verifier.Engine) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hsample : ∀ t u n, e.sampleIndices t u n = ⟨[Verifier.zero], [Verifier.zero]⟩)
    (hacc : Verifier.verify e pin chain c p = .ok ()) : c.numWires ≤ 2 := by
  have hchecks := Verifier.verify_success_checks e pin chain c p hacc
  have hlen := hchecks.2.2.2.2.2.2.2.1
  rw [Verifier.derivedIndices, hsample] at hlen
  have hbits : c.indexBits = 1 := hlen.symm
  have henv := hchecks.2.2.1
  simp only [Verifier.envelope, decide_eq_true_eq] at henv
  have hw : Verifier.width c ≤ 2 ^ c.indexBits :=
    henv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hbits] at hw
  exact Nat.le_trans (width_lower_bounds_wire_count c) (by simpa using hw)

/-- (4) The adopted `Integrated.exampleEngine` is DOUBLY pinned: unit index lanes
(`Integrated.lean:201`) and unit tau (`:200`).  So it is caught by cause 3 as well as by
the wire bound just proved. -/
theorem adopted_example_engine_is_doubly_pinned :
    (∀ t u n, Integrated.exampleEngine.sampleIndices t u n
        = ⟨[Verifier.zero], [Verifier.zero]⟩) ∧
      (∀ cfg s, (Integrated.exampleEngine.initialObservation cfg s).logTau
        = [Verifier.zero]) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- (4) **NON-VACUITY OF THE UNIT-INDEX HYPOTHESIS.**  The adopted
`Integrated.positive_integrated_norm_helper_path` is an accepting integrated run of
`Integrated.exampleEngine`; the adopted
`Integrated.accepted_preflights_and_original_verifier` extracts from it an accepting run of
`Verifier.verify` at an engine with the unit index sampler.  So the antecedent of
`unit_index_sampling_forces_two_wires` is inhabited -- and, as the theorem says, only at
two wires or fewer. -/
theorem unit_index_sampling_hypotheses_satisfiable :
    (∀ t u n,
        (Integrated.modelEngine Integrated.exampleEngine Integrated.exampleDecoder).sampleIndices
          t u n = ⟨[Verifier.zero], [Verifier.zero]⟩) ∧
      Verifier.verify (Integrated.modelEngine Integrated.exampleEngine Integrated.exampleDecoder)
        ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1 Integrated.exampleConfig
        Integrated.exampleProof = .ok () := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    Integrated.exampleEngine Integrated.exampleDecoder ⟨1, Verifier.testRoot, Verifier.testRoot⟩
    1 Integrated.exampleConfig Integrated.exampleProof
    Integrated.positive_integrated_norm_helper_path
  exact hv

/-- (4) And that adopted accepting instance is indeed within the bound. -/
theorem adopted_example_config_has_at_most_two_wires :
    Integrated.exampleConfig.numWires ≤ 2 :=
  unit_index_sampling_forces_two_wires _ ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1
    Integrated.exampleConfig Integrated.exampleProof
    unit_index_sampling_hypotheses_satisfiable.1
    unit_index_sampling_hypotheses_satisfiable.2

/-! ## 5. THE REPAIR, AND ACCEPTANCE AT A NON-DEGENERATE CONFIGURATION -/

/-- (5) **THE REPAIR OF CAUSE 2.**  An index sampler that returns `c.indexBits` copies of
`Verifier.zero` on each lane.  `Verifier.Engine.sampleIndices` takes `c.indexBits` as its
third argument (`Verifier.lean:389-390`), so this is a legal field; it satisfies the
`:420-421` length gate at EVERY `c.indexBits`, not only at zero. -/
def replicatedIndexSampler : Verifier.Bytes → Verifier.UsedClaims → Nat → Verifier.IndexPoints :=
  fun _ _ n => ⟨List.replicate n Verifier.zero, List.replicate n Verifier.zero⟩

/-- (5) **THE REPAIR OF CAUSE 4.**  The adopted seven-value log-challenge layout
`[eta, beta, gamma, xi, lambda, rho, kappa]` of `Norm.challengeList`, with
`beta = Norm.one` and every other entry zero.  This is LITERALLY the adopted
`Integrated.exampleEngine`'s own challenge list (`Integrated.lean:200`), not a new object;
see `seven_value_layout_is_the_adopted_one`.  That single non-zero entry is what makes the
concrete permutation terminal of Section 6 vanish; `Verifier.verify` alone (this section)
never reads it, but `Norm.checkedNormEvaluation` counts it. -/
def sevenValueChallenges : List Verifier.Ext3 :=
  [Verifier.zero, Norm.one, Verifier.zero, Verifier.zero, Verifier.zero, Verifier.zero,
    Verifier.zero]

/-- (5) The seven-value layout is not a fresh object: it is the adopted
`Integrated.exampleEngine`'s list, by `rfl`. -/
theorem seven_value_layout_is_the_adopted_one (c : Verifier.Config) (s : Verifier.Statement) :
    sevenValueChallenges = (Integrated.exampleEngine.initialObservation c s).logChallenges := rfl

/-- (5) **THE REPAIR OF CAUSE 3.**  The adopted `Verifier.testEngine`'s initial
observation returns one-element `logTau`/`gateTau`, which pins `c.degreeBits = 1` at
`Verifier.lean:420` (Section 3).  Generalising to `List.replicate c.degreeBits
Verifier.zero` removes that pin the same way the sampler removes the index-bit pin. -/
def configuredInitialObservation : Verifier.Config → Verifier.Statement → Verifier.Initial :=
  fun c _ => ⟨[], sevenValueChallenges, List.replicate c.degreeBits Verifier.zero,
    Verifier.zero, List.replicate c.degreeBits Verifier.zero⟩

/-- (5) **THE MODEL ENGINE.**  The adopted `Verifier.testEngine` with exactly two fields
moved -- the index sampler and the initial observation.  `configurationHash`,
`deploymentValid`, `commitRound`, `foldClaim`, `normEvaluation`, `publicInputsHash`,
`gateEvaluation`, `eqEvaluation`, `parseWhir` and `whirTail` keep the fixture's trivial
choices, which is precisely why the honesty section above forbids reading any conclusion
below as an acceptance exhibition for the explicit engine. -/
def wideEngine : Verifier.Engine :=
  { Verifier.testEngine with
      sampleIndices := replicatedIndexSampler,
      initialObservation := configuredInitialObservation }

/-- (5) **THE SMALL NON-DEGENERATE CONFIGURATION.**  Seven wires, three routed wires, four
constants, two selectors, three degree bits, three index bits, two gate rows, one gate
constraint, two public inputs.  Its packed width is
`max (4 + 3) (max 7 6) = 7`, which sits strictly between `2 ^ (3 - 1)` and `2 ^ 3`, so the
two-sided index-bit condition of `Verifier.envelope` (`Verifier.lean:104-105`) holds. -/
def wideConfig : Verifier.Config :=
  { Verifier.testConfig with
      degreeBits := 3, numConstants := 4, numRouted := 3, numWires := 7,
      numPublicInputs := 2, numSelectors := 2, numGateConstraints := 1,
      quotientDegree := 1, gateRows := 2, indexBits := 3,
      kIs := List.replicate 3 (Verifier.base 1),
      subgroupPowers := List.replicate 3 (Verifier.base 1),
      publicInputWireMap := List.replicate 6 0 }

/-- (5) The pinned deployment record this module accepts against. -/
def widePin : Verifier.Pinned := ⟨1, Verifier.testRoot, Verifier.testRoot⟩

/-- (5) **THE PROOF RECORD, AT THE ADOPTED MATCHING CLAIMS.**  `used` is exactly
`IndexHalfTransport.matchingClaims wideConfig` -- the adopted repair of cause 1, not a
fresh record.  The round lists and the constituent width are the shape-pinned values at
`wideConfig`. -/
def wideProof : Verifier.Proof :=
  { Verifier.testProof with
      constituentWidth := 7,
      publicInputs := List.replicate 2 (Verifier.base 0),
      logRounds := List.replicate 3 (List.replicate 5 Verifier.zero),
      gateRounds := List.replicate 3 (List.replicate 3 Verifier.zero),
      used := IndexHalfTransport.matchingClaims wideConfig }

/-- (5) The sampler returns a full-width lane on both sides, at every index-bit count --
the exact negation of the fixture behaviour Section 1 indicts. -/
theorem model_engine_samples_configured_index_width (t : Verifier.Bytes)
    (u : Verifier.UsedClaims) (n : Nat) :
    (wideEngine.sampleIndices t u n).log.length = n ∧
      (wideEngine.sampleIndices t u n).gate.length = n :=
  ⟨List.length_replicate _ _, List.length_replicate _ _⟩

/-- (5) So `wideEngine` is outside the reach of Section 1's headline theorem at the
configuration used here. -/
theorem model_engine_is_not_trivial_index_sampling :
    ¬ (∀ t u n, wideEngine.sampleIndices t u n = ⟨[], []⟩) := by
  intro h
  have hl : (3 : Nat) = 0 :=
    congrArg (fun idx => idx.log.length) (h [] Verifier.testProof.used 3)
  exact absurd hl (by decide)

/-- (5) And outside the reach of Section 3's, since its tau lanes track `c.degreeBits`. -/
theorem model_engine_is_not_unit_tau :
    ¬ (∀ cfg s, (wideEngine.initialObservation cfg s).logTau = [Verifier.zero]) := by
  intro h
  have hl : (3 : Nat) = 1 :=
    congrArg (fun i => i.length) (h wideConfig (Verifier.statement wideProof))
  exact absurd hl (by decide)

/-- (5) `wideProof` carries the adopted matching used-claims record verbatim. -/
theorem wide_proof_uses_adopted_matching_claims :
    wideProof.used = IndexHalfTransport.matchingClaims wideConfig := rfl

/-- (5) Every conjunct of the reviewed numeric envelope (`Verifier.lean:97-105`) holds at
`wideConfig`, including the two-sided index-bit condition. -/
theorem wide_config_envelope : Verifier.envelope wideConfig = true := by decide

/-- (5) **THE CONFIGURATION IS GENUINELY NON-DEGENERATE.**  More than one wire, a positive
number of routed wires, more than one constant, more than one degree bit and a positive
number of index bits -- every quantity the causes collapsed. -/
theorem wide_config_is_nondegenerate :
    1 < wideConfig.numWires ∧ 0 < wideConfig.numRouted ∧ 1 < wideConfig.numConstants ∧
      1 < wideConfig.degreeBits ∧ 0 < wideConfig.indexBits := by
  decide

/-- (5) The complete shape gate (`Verifier.lean:134-144`) at `widePin`, `wideConfig`,
`wideProof`: protocol version, constituent width, circuit digest, public-input count,
pinned preprocessed root, the two WHIR length caps, the five used-claim lengths, the two
round-list lengths and the two per-round widths. -/
theorem wide_shape_holds : Verifier.shape widePin wideConfig wideProof = true := by rfl

/-- (5) **THE SMALL ACCEPTANCE.**  A closed, concrete accepting run of the adopted
`Verifier.verify` at a configuration with seven wires and three routed wires.  Read it
strictly with the honesty section above: `wideEngine` is a model engine, so this says that
the length pins and the envelope no longer make acceptance impossible away from the
degenerate corner -- NOT that acceptance has been exhibited for the explicit engine. -/
theorem model_acceptance_at_nondegenerate_config :
    Verifier.verify wideEngine widePin 1 wideConfig wideProof = .ok () := by rfl

/-! ### 5a. The envelope-maximal instance

The same `wideEngine` -- the same two moved fields and nothing else -- accepts at the
WIDEST configuration `Verifier.envelope` permits.  This, and not the seven-wire example, is
the module's headline.  It is also the argument that makes the field-by-field audit of
`wideEngine` conclusive rather than enumerative: if any unmoved fixture field pinned any
configuration quantity read inside `Verifier.verify`, the instance below could not close.
-/

/-- (5a) **THE ENVELOPE-MAXIMAL CONFIGURATION.**  Every numeric field is at the ceiling
`Verifier.envelope` (`Verifier.lean:97-105`) permits: `degreeBits = 13`, packed
`width = 160`, `numRouted = 80`, `numGateConstraints = 123`, `quotientDegree = 8` (so
`quotientDegree + 2 = 10`), `gateRows = 255`, `indexBits = 8`. -/
def maximalConfig : Verifier.Config :=
  { Verifier.testConfig with
      degreeBits := 13, numConstants := 80, numRouted := 80, numWires := 160,
      numPublicInputs := 3, numSelectors := 4, numGateConstraints := 123,
      quotientDegree := 8, gateRows := 255, indexBits := 8,
      kIs := List.replicate 80 (Verifier.base 1),
      subgroupPowers := List.replicate 13 (Verifier.base 1),
      publicInputWireMap := List.replicate 9 0 }

/-- (5a) The matching proof record at `maximalConfig`: `used` is again the adopted
`IndexHalfTransport.matchingClaims`, and the round lists are the shape-pinned shapes
(`13` rounds, log rows of width `5`, gate rows of width `quotientDegree + 2 = 10`). -/
def maximalProof : Verifier.Proof :=
  { Verifier.testProof with
      constituentWidth := 160,
      publicInputs := List.replicate 3 (Verifier.base 0),
      logRounds := List.replicate 13 (List.replicate 5 Verifier.zero),
      gateRounds := List.replicate 13 (List.replicate 10 Verifier.zero),
      used := IndexHalfTransport.matchingClaims maximalConfig }

/-- (5a) The full numeric envelope at the maximal configuration. -/
theorem maximal_config_envelope : Verifier.envelope maximalConfig = true := by decide

/-- (5a) Every quantity the four causes collapsed is now at its largest admissible
value. -/
theorem maximal_config_is_nondegenerate :
    1 < maximalConfig.numWires ∧ 0 < maximalConfig.numRouted ∧
      1 < maximalConfig.numConstants ∧ 1 < maximalConfig.degreeBits ∧
      0 < maximalConfig.indexBits := by decide

/-- (5a) The complete shape gate at the maximal instance. -/
theorem maximal_shape_holds : Verifier.shape widePin maximalConfig maximalProof = true := by
  rfl

/-- (5a) **THE HEADLINE ACCEPTANCE.**  The adopted `Verifier.verify`, at the
envelope-maximal configuration, with the same model engine and the same two moved fields.
Scope caveat exactly as for the seven-wire instance: `wideEngine` is a model engine. -/
theorem model_acceptance_at_the_maximal_config :
    Verifier.verify wideEngine widePin 1 maximalConfig maximalProof = .ok () := by rfl

/-- (5a) The WHIR-profile variable budget of the adopted deployment check
(`PinnedWhirProfile.canonicalProfileCheck`, `PinnedWhirProfile.lean:216-220`) is
`minProfileVariables ≤ numVariables ≤ maxProfileVariables`, i.e. `1 ≤ . ≤ 21`
(`:188`, `:191`), with `numVariables = c.degreeBits + c.indexBits`
(`ExplicitEngine.lean:722`).  The envelope caps `degreeBits ≤ 13` and `indexBits ≤ 8`,
which sum to exactly the profile ceiling; the maximal configuration sits precisely at it,
so it is still inside the deployment arithmetic -- but only just.  This is the sense in
which the residual obstruction for the explicit engine is NOT purely semantic. -/
theorem maximal_config_meets_the_profile_variable_budget :
    PinnedWhirProfile.minProfileVariables ≤ maximalConfig.degreeBits + maximalConfig.indexBits ∧
      maximalConfig.degreeBits + maximalConfig.indexBits
        ≤ PinnedWhirProfile.maxProfileVariables := by decide

/-! ### 5b. The parametric acceptance

An earlier revision of this module asserted that the statement below could not be proved.
That assertion was false; see the honesty section.  The route is to avoid definitional
reduction with symbolic bytes altogether, by supplying `Verifier.verify` with its twelve
recorded checks rather than computing it. -/

/-- (5b) **THE CONSTRUCTOR COMPANION TO `Verifier.verify_success_checks`.**  The adopted
tree carries the DESTRUCTOR -- acceptance implies the twelve checks -- but not the
converse.  This is the converse: the twelve checks are jointly SUFFICIENT for acceptance.
Nothing about the engine, the pin, the configuration or the proof is fixed. -/
theorem verify_of_checks (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (h1 : chain = pin.chainId) (h2 : e.configurationHash c = pin.configDigest)
    (h3 : Verifier.envelope c = true) (h4 : e.deploymentValid c = true)
    (h5 : Verifier.shape pin c p = true)
    (h6 : (e.initialTranscript c p).logTau.length = c.degreeBits)
    (h7 : (e.initialTranscript c p).gateTau.length = c.degreeBits)
    (h8 : (Verifier.derivedIndices e c p).log.length = c.indexBits)
    (h9 : (Verifier.derivedIndices e c p).gate.length = c.indexBits)
    (h10 : e.logTerminal c (e.initialTranscript c p) p (Verifier.derivedRounds e c p).logPoint
      = (Verifier.derivedRounds e c p).logClaim)
    (h11 : Verifier.verifyWhir e (Verifier.derivedContext e c p) p = true)
    (h12 : Verifier.gateTerminal e c p = (Verifier.derivedRounds e c p).gateClaim) :
    Verifier.verify e pin chain c p = .ok () := by
  unfold Verifier.verify
  rw [if_neg (by simp [h1])]
  rw [if_neg (by simp [h2, h3, h4])]
  rw [if_neg (by simp [h5])]
  simp only []
  rw [if_neg (by simp [h6, h7, h8, h9])]
  rw [if_neg (by simp [h10])]
  rw [if_neg (by simp [h11])]
  rw [if_neg (by simp [h12])]

/-- (5b) `wideProof` with arbitrary WHIR transcript and hint byte strings.  The model
engine's `parseWhir` and `whirTail` ignore both arguments, so this is the one dimension of
the accepted instance along which a genuinely parametric statement is available. -/
def wideProofWithWhirBytes (transcript hints : Verifier.Bytes) : Verifier.Proof :=
  { wideProof with whirTranscript := transcript, whirHints := hints }

/-- (5b) **THE SHAPE GATE CARRIES A FAMILY.**  At `wideConfig` the complete length gate of
`Verifier.shape` is satisfied by EVERY proof record whose WHIR byte strings respect the
two caps -- not by an isolated record.  Both hypotheses are satisfiable (at
`transcript = hints = []` this is `wide_shape_holds`), so the statement is not vacuous.

A version parametric in the CONFIGURATION is not stated: the acceptance proof at a fixed
configuration is a kernel computation at concrete numerals, and a variable wire count
would require re-proving the round transitions, the packed fold and the claim matcher
symbolically.  That is a statement about what has been done here, not about what Lean can
do. -/
theorem wide_shape_holds_for_any_bounded_whir_bytes (transcript hints : Verifier.Bytes)
    (htranscript : transcript.length ≤ 1904) (hhints : hints.length ≤ 112408) :
    Verifier.shape widePin wideConfig (wideProofWithWhirBytes transcript hints) = true := by
  simp only [Verifier.shape, wideProofWithWhirBytes, decide_eq_true_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, htranscript, hhints, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- (5b) **THE PARAMETRIC ACCEPTANCE.**  `wideEngine` accepts at `wideConfig` for EVERY
WHIR transcript and EVERY hint string within the two shape caps -- a family, not a point.
The proof never reduces the verifier with symbolic bytes: it takes the nine
byte-independent checks from the closed instance `model_acceptance_at_nondegenerate_config`
via the adopted destructor, replaces the shape check by the parametric
`wide_shape_holds_for_any_bounded_whir_bytes`, and reassembles with `verify_of_checks`.
Non-vacuous: at `transcript = hints = []` it is the closed instance. -/
theorem model_acceptance_for_any_bounded_whir_bytes
    (transcript hints : Verifier.Bytes)
    (htranscript : transcript.length ≤ 1904) (hhints : hints.length ≤ 112408) :
    Verifier.verify wideEngine widePin 1 wideConfig
      (wideProofWithWhirBytes transcript hints) = .ok () := by
  have base := Verifier.verify_success_checks wideEngine widePin 1 wideConfig wideProof
    model_acceptance_at_nondegenerate_config
  exact verify_of_checks wideEngine widePin 1 wideConfig _
    rfl rfl wide_config_envelope rfl
    (wide_shape_holds_for_any_bounded_whir_bytes transcript hints htranscript hhints)
    base.2.2.2.2.2.1 base.2.2.2.2.2.2.1 base.2.2.2.2.2.2.2.1 base.2.2.2.2.2.2.2.2.1
    base.2.2.2.2.2.2.2.2.2.1 base.2.2.2.2.2.2.2.2.2.2.1 base.2.2.2.2.2.2.2.2.2.2.2

/-! ## 6. THE MODEL ENGINE THROUGH THE ADOPTED `Integrated.verify`

`Integrated.verify` (`Integrated.lean:59-66`) runs `normResult` and `gateResult` before
`Verifier.verify`, and replaces the engine's `foldClaim`, `normEvaluation`, `eqEvaluation`
and `gateEvaluation` by the concrete `Connections.packedFold`, `Norm.normEvaluation`,
`Norm.eqEvaluation` and the adopted gate dispatcher.  So this section's acceptance is
carried by CONCRETE fold, norm and gate arithmetic -- but still with a stand-in ABI
decoder, a stand-in public-input hash and a stand-in WHIR parse/tail.

The proof record here is NOT Section 5's.  Exactly one lane differs: `logNormInverse`
carries six copies of `Norm.one` where `IndexHalfTransport.matchingClaims wideConfig`
carries six zeros.  All five shape-read LENGTHS are unchanged
(`wide_integrated_claims_keep_matching_lengths`), which is why `Verifier.shape` cannot
tell the two apart. -/

/-- (6) **THE INTEGRATED MODEL ENGINE.**  `wideEngine` -- not `Integrated.exampleEngine`
-- with two field VALUES borrowed from `Integrated.exampleEngine` (`Integrated.lean:202-203`):
a public-input hash of the pinned four-limb length, and a WHIR parse that echoes the
context's expected claims.  Both are stand-ins; see the honesty section. -/
def wideIntegratedEngine : Verifier.Engine :=
  { wideEngine with
      publicInputsHash := fun _ => List.replicate 4 (Verifier.base 0),
      parseWhir := fun ctx _ _ =>
        some ⟨ctx.roots, ctx.roots, ctx.expectedClaims.map (fun x => x.getD Verifier.zero)⟩ }

/-- (6) **THE PROOF RECORD FOR THE CONCRETE NORM TERMINAL.**  Identical to `wideProof`
except that the six norm-helper entries are `Norm.one` rather than `Verifier.zero`: the
adopted `Norm.wireStep` subtracts one from `helper * formalNorm`, so a zero helper cannot
make the permutation terminal vanish.  All five list LENGTHS still agree with
`IndexHalfTransport.matchingClaims wideConfig`, which is what
`Verifier.shape` reads; see `wide_integrated_claims_keep_matching_lengths`. -/
def wideIntegratedProof : Verifier.Proof :=
  { wideProof with
      used := { IndexHalfTransport.matchingClaims wideConfig with
                  logNormInverse := List.replicate 6 Norm.one } }

/-- (6) The stand-in gate-metadata decoder: a two-row table whose first row is an
arithmetic gate with one constraint and one constant, and whose second row is the
no-constraint gate.  It is NOT deployed gate metadata. -/
def wideDecoder : Integrated.DecodeGates :=
  fun _ => some [⟨1, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 1, 1, 2, 1, 0, 0, 0, 0⟩]

/-- (6) The norm-helper substitution changes no length the shape gate reads. -/
theorem wide_integrated_claims_keep_matching_lengths :
    wideIntegratedProof.used.logPreprocessed.length =
        (IndexHalfTransport.matchingClaims wideConfig).logPreprocessed.length ∧
      wideIntegratedProof.used.logWitness.length =
        (IndexHalfTransport.matchingClaims wideConfig).logWitness.length ∧
      wideIntegratedProof.used.logNormInverse.length =
        (IndexHalfTransport.matchingClaims wideConfig).logNormInverse.length ∧
      wideIntegratedProof.used.gatePreprocessed.length =
        (IndexHalfTransport.matchingClaims wideConfig).gatePreprocessed.length ∧
      wideIntegratedProof.used.gateWitness.length =
        (IndexHalfTransport.matchingClaims wideConfig).gateWitness.length := by
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  rfl

/-- (6) And exactly one lane -- `logNormInverse` -- differs as a LIST, so "the same
instance as Section 5" would be imprecise. -/
theorem wide_integrated_claims_differ_only_in_the_norm_lane :
    wideIntegratedProof.used.logNormInverse ≠
        (IndexHalfTransport.matchingClaims wideConfig).logNormInverse ∧
      wideIntegratedProof.used.logPreprocessed =
        (IndexHalfTransport.matchingClaims wideConfig).logPreprocessed ∧
      wideIntegratedProof.used.logWitness =
        (IndexHalfTransport.matchingClaims wideConfig).logWitness ∧
      wideIntegratedProof.used.gatePreprocessed =
        (IndexHalfTransport.matchingClaims wideConfig).gatePreprocessed ∧
      wideIntegratedProof.used.gateWitness =
        (IndexHalfTransport.matchingClaims wideConfig).gateWitness := by
  refine ⟨by decide, rfl, rfl, rfl, rfl⟩

/-- (6) The concrete permutation terminal of the adopted `Norm.checkedNormEvaluation`
succeeds at this instance -- its shape predicate holds at seven wires and three routed
wires, and its seven-challenge count gate (`Norm.lean:353`, cause 4) is met by
`sevenValueChallenges` -- and evaluates to `Verifier.zero`, which is the derived log
claim. -/
theorem wide_integrated_norm_result :
    Integrated.normResult (Integrated.modelEngine wideIntegratedEngine wideDecoder)
      wideConfig wideIntegratedProof = some Verifier.zero := by rfl

/-- (6) The adopted gate dispatcher produces a result on the stand-in two-row table at
`gateConfig wideConfig` (two selectors, four constants, one gate constraint, seven wires,
quotient degree one), so `Integrated.verify`'s second preflight gate is discharged rather
than defaulted. -/
theorem wide_integrated_gate_result_available :
    (Integrated.gateResult (Integrated.modelEngine wideIntegratedEngine wideDecoder)
      wideDecoder wideConfig wideIntegratedProof).isSome = true := by rfl

/-- (6) **THE INTEGRATED ACCEPTANCE.**  Both extra gates of `Integrated.verify` and the
whole of `Verifier.verify` under the concrete fold/norm/eq/gate substitution.  Same scope
caveat as Section 5: this is the model engine, with a stand-in decoder, a stand-in
public-input hash and a stand-in WHIR parse and tail.  It is also the witness that
Section 4's unconditional rejection is genuine content: `Integrated.verify` is not
identically `.error .configuration`. -/
theorem integrated_acceptance_at_nondegenerate_config :
    Integrated.verify wideIntegratedEngine wideDecoder widePin 1 wideConfig
      wideIntegratedProof = .ok () := by rfl

/-- (6) The inner `Verifier.verify` under the concrete substitution, extracted from the
integrated acceptance by the adopted
`Integrated.accepted_preflights_and_original_verifier`.  This is the sharpest statement in
the module: the engine here uses `Connections.packedFold`, `Norm.normEvaluation`,
`Norm.eqEvaluation` and the adopted gate dispatcher, and it accepts at seven wires. -/
theorem concrete_substituted_engine_accepts_at_nondegenerate_config :
    Verifier.verify (Integrated.modelEngine wideIntegratedEngine wideDecoder) widePin 1
      wideConfig wideIntegratedProof = .ok () := by
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    wideIntegratedEngine wideDecoder widePin 1 wideConfig wideIntegratedProof
    integrated_acceptance_at_nondegenerate_config
  exact hv

/-! ### 6a. The integrated instance scales too

The same `wideDecoder` and the same `wideIntegratedEngine`, at fifteen wires.  The
stand-in decoder pins two configuration fields and nothing else: `gateRows = 2`, because
`Integrated.evaluateGate` rejects unless the decoded table's length is `c.gateRows`
(`Integrated.lean:40`); and, as an OBSERVED property of this particular two-row table
rather than a proved impossibility, `numSelectors = 2`.  Both are inherited unchanged from
`wideConfig` below.  No claim is made here that other values are unreachable. -/

/-- (6a) Fifteen wires, seven routed wires, eight constants, four degree bits, four index
bits.  `gateRows`, `numSelectors`, `numGateConstraints` and `quotientDegree` are
`wideConfig`'s. -/
def widerConfig : Verifier.Config :=
  { wideConfig with
      degreeBits := 4, numConstants := 8, numRouted := 7, numWires := 15,
      indexBits := 4,
      kIs := List.replicate 7 (Verifier.base 1),
      subgroupPowers := List.replicate 4 (Verifier.base 1) }

/-- (6a) The matching proof record, with the same one-lane norm-helper substitution as
`wideIntegratedProof`. -/
def widerIntegratedProof : Verifier.Proof :=
  { wideProof with
      constituentWidth := 15,
      logRounds := List.replicate 4 (List.replicate 5 Verifier.zero),
      gateRounds := List.replicate 4 (List.replicate 3 Verifier.zero),
      used := { IndexHalfTransport.matchingClaims widerConfig with
                  logNormInverse := List.replicate 14 Norm.one } }

theorem wider_config_envelope : Verifier.envelope widerConfig = true := by decide

theorem wider_config_is_nondegenerate :
    1 < widerConfig.numWires ∧ 0 < widerConfig.numRouted ∧ 1 < widerConfig.numConstants ∧
      1 < widerConfig.degreeBits ∧ 0 < widerConfig.indexBits := by decide

/-- (6a) The concrete norm terminal still vanishes at fifteen wires and seven routed
wires. -/
theorem wider_norm_result :
    Integrated.normResult (Integrated.modelEngine wideIntegratedEngine wideDecoder)
      widerConfig widerIntegratedProof = some Verifier.zero := by rfl

/-- (6a) **THE INTEGRATED ACCEPTANCE AT FIFTEEN WIRES.**  Same engine, same decoder. -/
theorem integrated_acceptance_at_fifteen_wires :
    Integrated.verify wideIntegratedEngine wideDecoder widePin 1 widerConfig
      widerIntegratedProof = .ok () := by rfl

/-- (6) **THE OBSTRUCTION THAT REMAINS.**  Section 1's headline applies to
`Integrated.modelEngine` too, because `Integrated.modelEngine` does not touch
`sampleIndices`: had the sampler been left trivial, the integrated acceptances above would
have been impossible at seven or fifteen wires.  This is the exact sense in which the
repair was necessary, and it is all that the repair buys -- the WHIR tail, the real gate
metadata, `deploymentValid` and the real configuration digest are untouched. -/
theorem integrated_acceptance_needs_the_repaired_sampler
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hsample : ∀ t u n, e.sampleIndices t u n = ⟨[], []⟩)
    (hacc : Integrated.verify e decode pin chain c p = .ok ()) : c.numWires ≤ 1 := by
  obtain ⟨_, _, _, _, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain c p hacc
  exact acceptance_at_trivial_index_sampling_forces_one_wire
    (Integrated.modelEngine e decode) pin chain c p hsample hv

/-! ## 7. THE FIAT GATES, RECORDED AS THEOREMS

The honesty section's gate count is not an assertion: each fiat gate is exhibited below as
content-free at an ARBITRARY argument, and the negative controls confirm that the two
moved fields really are load-bearing. -/

/-- (7) Gate 2 (`configurationHash c = pin.configDigest`) holds at EVERY configuration: it
reads nothing. -/
theorem model_engine_config_hash_gate_is_content_free (c : Verifier.Config) :
    wideEngine.configurationHash c = widePin.configDigest := rfl

/-- (7) Gate 4 (`deploymentValid`) holds at EVERY configuration. -/
theorem model_engine_deployment_gate_is_content_free (c : Verifier.Config) :
    wideEngine.deploymentValid c = true := rfl

/-- (7) The WHIR tail accepts every transcript, every hint string and every parse, at every
context -- Sections 5 and 6 alike. -/
theorem model_engine_whir_tail_is_content_free (ctx : Verifier.WhirContext)
    (t h : Verifier.Bytes) (parsed : Verifier.ParsedWhir) :
    wideEngine.whirTail ctx t h parsed = true ∧
      wideIntegratedEngine.whirTail ctx t h parsed = true := ⟨rfl, rfl⟩

/-- (7) Section 6's `parseWhir` echoes the context's own expected claims, so
`Verifier.verifyWhir` holds at EVERY context and EVERY proof record: gate 8 there is
satisfied by construction and cannot fail. -/
theorem integrated_whir_gate_is_content_free (ctx : Verifier.WhirContext)
    (p : Verifier.Proof) : Verifier.verifyWhir wideIntegratedEngine ctx p = true := by
  have key : ∀ l : List (Option Verifier.Ext3),
      Verifier.claimsMatch l (l.map (fun x => x.getD Verifier.zero)) = true := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => cases x <;> simpa [Verifier.claimsMatch] using ih
  have hp : wideIntegratedEngine.parseWhir ctx p.whirTranscript p.whirHints =
      some ⟨ctx.roots, ctx.roots,
        ctx.expectedClaims.map (fun x => x.getD Verifier.zero)⟩ := rfl
  simp only [Verifier.verifyWhir, hp, Verifier.rootsAndClaimsMatch, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨?_, key _⟩, ?_⟩ <;> trivial

/-- (7) Section 5's log terminal is the constant zero at EVERY configuration, proof and
point, so gate 7 carries no arithmetic there. -/
theorem model_engine_log_terminal_is_constant (c : Verifier.Config) (i : Verifier.Initial)
    (p : Verifier.Proof) (pt : List Verifier.Ext3) :
    wideEngine.logTerminal c i p pt = Verifier.zero := rfl

/-- (7) And Section 5's gate terminal likewise, so gate 9 carries none either. -/
theorem model_engine_gate_terminal_is_constant (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.gateTerminal wideEngine c p = Verifier.zero := rfl

/-- (7) Section 5's whole WHIR gate is content-free too: constant `foldClaim` plus a
constant six-zero parse. -/
theorem model_engine_whir_claims_are_content_free (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.claimsMatch (Verifier.derivedContext wideEngine c p).expectedClaims
      (List.replicate 6 Verifier.zero) = true := rfl

/-- (7) **THE REPAIR FIXES THE LANE LENGTH, NOT THE LANE CONTENT.**  The index points the
repaired sampler produces are ALL ZERO, at every argument. -/
theorem repaired_sampler_returns_the_zero_point (t : Verifier.Bytes)
    (u : Verifier.UsedClaims) (n : Nat) :
    (wideEngine.sampleIndices t u n).log = List.replicate n Verifier.zero ∧
      (wideEngine.sampleIndices t u n).gate = List.replicate n Verifier.zero := ⟨rfl, rfl⟩

/-- (7) **NO FIAT--SHAMIR DEPENDENCE AT ALL.**  The transcript the sampler is fed is the
EMPTY byte string at every configuration and proof, because `commitRound` is the fixture's
constant. -/
theorem derived_transcript_is_empty (c : Verifier.Config) (p : Verifier.Proof) :
    (Verifier.derivedRounds wideEngine c p).transcript = [] := by
  have key : ∀ (ms : List Verifier.CoupledMessage) (s : Verifier.RoundState),
      s.transcript = [] →
        (Verifier.runRounds wideEngine.commitRound s ms).transcript = [] := by
    intro ms
    induction ms with
    | nil => intro s hs; exact hs
    | cons _ _ ih => intro s _; exact ih _ rfl
  exact key _ _ rfl

/-- (7) All three roots of `wideProof` are the SAME constant `Verifier.testRoot`.  The
fiat `parseWhir` cannot see that; the adopted `InstalledWhirParse.concreteParseWhir`
would. -/
theorem wide_proof_roots_are_the_single_fixture_root :
    wideProof.preprocessedRoot = Verifier.testRoot ∧
      wideProof.witnessRoot = Verifier.testRoot ∧
      wideProof.normInverseRoot = Verifier.testRoot := ⟨rfl, rfl, rfl⟩

/-- (7) **NEGATIVE CONTROL 1.**  Reverting the sampler, keeping everything else, destroys
the acceptance. -/
theorem fixture_sampler_rejects_wide_config :
    Verifier.verify { wideEngine with sampleIndices := Verifier.testEngine.sampleIndices }
      widePin 1 wideConfig wideProof = .error .configuration := rfl

/-- (7) **NEGATIVE CONTROL 2.**  Reverting the initial observation likewise. -/
theorem fixture_observation_rejects_wide_config :
    Verifier.verify
      { wideEngine with initialObservation := Verifier.testEngine.initialObservation }
      widePin 1 wideConfig wideProof = .error .configuration := rfl

/-- (7) **NEGATIVE CONTROL 3.**  Reverting `used` to the fixture record likewise, now at
the shape gate rather than the length gate. -/
theorem fixture_claims_reject_wide_config :
    Verifier.verify wideEngine widePin 1 wideConfig
      { wideProof with used := Verifier.testProof.used } = .error .invalidProof := rfl

end Audit.Wire3.NonDegenerateAcceptance
