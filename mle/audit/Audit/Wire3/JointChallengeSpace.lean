import Audit.Wire3.ChallengeUnionBound
import Audit.Wire3.CommitmentOrder
import Audit.Wire3.GateDerivedRejection

/-!
# ONE joint sample space for every post-prefix gate-lane challenge draw

## The gap this module closes

The adopted `Audit.Wire3.ChallengeUnionBound.combined_union_bound` adds THREE
masses that live on THREE DIFFERENT sample spaces:

* the outer sumcheck round term, on ONE `OuterChallenge.DigestTriple` (imported
  from `ConditionalSoundness.outer_failure_bound`, whose `law` is a free
  `Finset Element -> Q`);
* the gate tau zero-check term, on `ChallengeUnionBound.TripleTuple n`, an
  `n`-tuple of digest triples;
* the gate alpha term, on ONE `OuterChallenge.DigestTriple` again.

Its own verification recorded the defect verbatim: "no disjunction event exists;
no joint event or law is formalized; this is an arithmetic inequality between
three independently derived quotients, not the probability of a union."

THIS MODULE SUPPLIES THE MISSING JOINT OBJECT.  Section 1 builds ONE explicit
finite index set -- literally the source squeeze schedule -- section 2 puts the
uniform law on the resulting product space, section 3 proves the product-measure
projection facts, section 4 pulls each of the three adopted bad sets back to its
own coordinates of that ONE space, and section 5 proves the GENUINE UNION BOUND:
the mass of an actual disjunction event is at most the adopted `combinedBound`.

## THE NUMBER IS STILL NOT THE SYSTEM'S SOUNDNESS ERROR

`ChallengeUnionBound.combined_bound_at_extremes_numeric` proves
`combinedBound 13 8 13 123 <= 2^(-172)`.  READ THAT AS WHAT IT IS.  It covers
ONLY (i) the outer sumcheck round-agreement events, (ii) the gate tau multilinear
zero check and (iii) the gate alpha zero check.  It EXCLUDES the entire
WHIR/Merkle contribution -- proximity/list decoding, the query-repetition
profile, and Merkle collision resistance -- which is the DOMINANT term.  The
deployed design point is around 100 BITS, not 172.  Quoting `2^-172` as the
wire-v3 soundness error would be wrong by roughly seventy bits.  Making the
three masses into one honest probability, as this module does, changes which
events are covered; it does not change which events dominate, and it adds
nothing at all to the WHIR/Merkle side.

THE ENVELOPE FIGURE HAS ABOUT 0.07 BITS OF HEADROOM.  The two digest-triple
terms contribute `999619 * (ceil(2^256/p) / 2^256)^3`, and `999619` is about
`2^19.93` while the cubed ratio is about `2^-192`, so the closed form sits at
roughly `2^-172.07`.  `combined_bound_at_extremes_between_two_powers` proves the
two-sided statement `2^(-173) <= combinedBound 13 8 13 123 <= 2^(-172)`.  WHAT
THE MARGIN ACTUALLY BUYS, in exact rational arithmetic on the same closed form:
each additional gate constraint adds `2^degreeBits * (ceil(2^256/p)/2^256)^3`,
about `2^-179`, so at `degreeBits = 13`, `quotientDegree = 8` the `<= 2^-172`
claim still holds at 124, 127 and 128 constraints and FIRST FAILS at 129, while
raising `degreeBits` to 14 breaks it outright (the closed form there is about
`2^-171.07`).  None of that is reachable inside the reviewed envelope anyway:
`Verifier.envelope` caps `numGateConstraints` at 123 and `degreeBits` at 13.

## THE SEAM IS STATED EXACTLY ONCE

`DrawEncodesRun` (section 6) is the ONLY place where the real transcript meets
this space.  It says: the challenges the run actually draws after the commitment
prefix ARE the coordinatewise reductions of one point of `JointSpace`.

`DrawEncodesRun` IS NOT AN ASSUMPTION ON THE HASH, and this module PROVES that.
`reduceTriple` is surjective (`reduceTriple_surjective`), so the run's own
challenge values can always be re-encoded as 32-byte digests; the resulting
`canonicalDraw` satisfies `DrawEncodesRun` for EVERY hash, EVERY engine and
EVERY proof whose two lanes fit the schedule (`draw_encodes_run_inhabited`), and
in particular for every ACCEPTED run (`draw_encodes_run_of_accepted`).  It is a
COORDINATE STATEMENT -- "this point of the space carries the run's challenges" --
and nothing more.

WHAT IS NOT FORMALIZED HERE is the actual Fiat--Shamir half (B): the reading
that THE RUN'S ENCODING DRAW IS DISTRIBUTED BY `jointProbability`.  That
sentence is not expressed anywhere in this module, in Lean or otherwise: there is
no probability space over hashes or over runs here, only counting on
`JointSpace`.  Consequently the composed theorem of section 6 carries NO
cryptographic hypothesis at all -- its mass conjunct is a counting fact about
`JointSpace`, and its conclusion conjunct is an implication from "the run's draw
avoids the bad set" to "the constraints vanish".  Reading the two conjuncts
together AS A PROBABILITY STATEMENT ABOUT THE RUN is exactly the unformalized
step, and the adopted `CommitmentOrder.separation_fails_for_a_deterministic_hash`
shows it cannot be recovered from ordering: for the constant hash, two statements
with different absorbed prefixes get the SAME gate alpha.

## HOW MUCH OF THE JOINT LAW'S SHAPE IS JUSTIFIED

Two of the three coordinate families ARE indexed by data fixed before every one
of these squeezes.  The gate tau family (`ZeroCheckSemantics.zeroCheckBadSet`)
and the gate alpha family (`AlphaZeroCheck.alphaBadSet`) are indexed by the gate
wire/constant tables, and `CommitmentOrder`'s twenty-two-frame prefix carries the
preprocessed, witness and norm-inverse roots at positions 13, 15 and 19, with
`only_two_domain_separators_after_the_last_root` showing that the only frames
between the last root and these squeezes are two fixed domain separators.  For
THOSE two families the bad sets really are constants of the experiment.

THE OUTER FAMILY IS NOT.  `laneEvent` recurses through
`OuterRound.evaluate a r.message r.challenge` -- the run's REALIZED challenge --
and round `k`'s `ConditionalSoundness.roundBadSet` depends on `r.message`, which
is absorbed at round `k`'s own commit (`Verifier.roundStep`,
`Transcript.commitRound` via
`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`),
i.e. AFTER the block-0 squeezes and after every round `< k`.  So `outerEvent` is
RUN-RELATIVE: its bases are evaluated at the realized prefix, and it is a
prefix-frozen union of cylinders -- exactly the shape of the adopted
`ConditionalSoundness.badSets`, which is also a list of sets computed along one
realized run.  The union bound is numerically unaffected: each cylinder has the
stated mass, and `lane_event_mass_le` bounds their union by subadditivity
whatever the bases are.  What a run-relative family does NOT come with is a
justification for treating the outer coordinates under a SINGLE product law; the
honest justification would be sequential conditioning / Fubini over the rounds,
which is NOT proved here.  That is precisely what the adopted
`ConditionalSoundness` ASSUMPTION 3 (`challengeIndependent`) already flags, and
this module inherits it unchanged.  It also remains subject to
`CommitmentOrder`'s own open `CommittedTables` extraction join.

## BOUNDARIES

* NOTHING here is a probability statement about Keccak, about the deployed
  transcript, or about any deterministic hash.  Every mass is COUNTING on an
  explicit finite set, divided by that set's size.
* The three events are NEVER shown to be the only bad events.  The composed
  statement of section 6 concludes only what the adopted
  `GateDerivedRejection.derived_selected_gate_constraints_vanish` concludes, on
  the good event: the selected gate's constraints vanish at one row.  The
  norm/logUp lane, extraction, WHIR, Merkle, gas and the Rust/Solidity
  refinement are all untouched.
* The outer summand's connection to the run is exactly the adopted
  `ConditionalSoundness.badSets` recursion, pulled back round by round.  The
  log lane appears in the event only so that the bound matches the adopted
  `outerTerm`; only the GATE lane's `BadEventFree` is consumed by the composed
  conclusion.  The log lane's own `BadEventFree`, at the adopted compare value
  `logCompareOf t pr = NormPolynomial.lift (OuterClaimChain.endpointSum t pr)`,
  is delivered separately by `log_lane_badEventFree_of_good_draw`.
* Tactic note, inherited from the adopted modules: no tactic may see
  `Fintype.card Element` or `Finset.univ` on `Element`.  All Element-side
  arithmetic is routed through the adopted size-generic lemmas, and the only
  numeral evaluation happens on Q literals built from `Arithmetic.modulus` and
  `2 ^ 256`.
-/

set_option maxRecDepth 8000

namespace Audit.Wire3.JointChallengeSpace
open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The index set IS the squeeze schedule

`CommitmentOrder`'s header pins, against `TranscriptV2.sol` and
`verifier_v2.rs`, the counters at which every post-prefix challenge is squeezed.
From the digest of the twenty-second absorbed frame (`relationState`):

    lambda 0,   rho 3,   kappa 6,
    log tau  i  at  9 + 3i                 (i < degreeBits)
    GATE ALPHA  at  9 + 3 * degreeBits
    GATE TAU i  at  12 + 3 * degreeBits + 3i    (i < degreeBits)

and then, for each coupled outer round, from that round's own commit digest
(adopted `OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`):

    LOG ROUND CHALLENGE   at counter 0
    GATE ROUND CHALLENGE  at counter 3

`Draw degreeBits` is the index set of the draws a GATE-LANE run makes: the two
coupled-round challenges of each of the `degreeBits` rounds, the gate alpha, and
the `degreeBits` gate tau coordinates.  `schedulePosition` maps it injectively
into (block, counter) pairs, block `0` being the relation-prefix digest and
block `r + 1` the commit digest of coupled round `r`, so the index set is
literally the squeeze schedule in source order. -/

/-- One post-prefix challenge draw of a gate-lane run, named by its place in the
source squeeze schedule. -/
inductive Draw (degreeBits : Nat) where
  /-- The gate alpha, squeezed at counter `9 + 3 * degreeBits`. -/
  | gateAlpha : Draw degreeBits
  /-- Gate tau coordinate `i`, squeezed at counter `12 + 3 * degreeBits + 3 * i`. -/
  | gateTau : Fin degreeBits → Draw degreeBits
  /-- The log-lane challenge of coupled round `r`, counter `0` of that round's
  commit digest.  THE LABEL IS DOCUMENTED, NOT DERIVED: counter `0` is what the
  adopted `OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`
  pins for `OuterChallenge.coupledChallenges`, whereas the theorems below
  quantify over an ABSTRACT `Verifier.Engine`, whose `commitRound` is a free
  `Verifier.CommitRound`; nothing here forces that engine's round challenges to
  come from this counter. -/
  | outerLog : Fin degreeBits → Draw degreeBits
  /-- The gate-lane challenge of coupled round `r`, counter `3` of that round's
  commit digest.  Same caveat as `outerLog`: counter `3` is the adopted
  `coupled_success_uses_same_committed_digest_and_six_counters` label, documented
  against that lemma rather than derived for the abstract engine. -/
  | outerGate : Fin degreeBits → Draw degreeBits
  deriving DecidableEq

/-- A plain sum encoding, used only to get `Fintype` and the cardinality. -/
def drawEquiv (d : Nat) : Draw d ≃ Unit ⊕ Fin d ⊕ Fin d ⊕ Fin d where
  toFun k := match k with
    | Draw.gateAlpha => Sum.inl ()
    | Draw.gateTau i => Sum.inr (Sum.inl i)
    | Draw.outerLog r => Sum.inr (Sum.inr (Sum.inl r))
    | Draw.outerGate r => Sum.inr (Sum.inr (Sum.inr r))
  invFun j := match j with
    | Sum.inl _ => Draw.gateAlpha
    | Sum.inr (Sum.inl i) => Draw.gateTau i
    | Sum.inr (Sum.inr (Sum.inl r)) => Draw.outerLog r
    | Sum.inr (Sum.inr (Sum.inr r)) => Draw.outerGate r
  left_inv k := by cases k <;> rfl
  right_inv j := by rcases j with _ | i | r | r <;> rfl

instance instFintypeDraw (d : Nat) : Fintype (Draw d) := Fintype.ofEquiv _ (drawEquiv d).symm

/-- (1) THE NUMBER OF DRAWS, as a function of `degreeBits`: two per coupled
round, one gate alpha, one per gate tau coordinate. -/
theorem draw_card (d : Nat) : Fintype.card (Draw d) = 3 * d + 1 := by
  rw [Fintype.card_congr (drawEquiv d)]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

/-- Which transcript state the draw is squeezed from: `0` is the digest of the
twenty-second absorbed frame (`CommitmentOrder.prefixDigest`), `r + 1` is the
commit digest of coupled round `r`. -/
def sourceBlock (d : Nat) : Draw d → Nat
  | Draw.gateAlpha => 0
  | Draw.gateTau _ => 0
  | Draw.outerLog r => r.val + 1
  | Draw.outerGate r => r.val + 1

/-- The little-endian squeeze counter of the draw inside its block, exactly as
the adopted `TranscriptProvenance.derived_columns_at_source_counters` and
`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`
pin them. -/
def sourceCounter (d : Nat) : Draw d → Nat
  | Draw.gateAlpha => 9 + 3 * d
  | Draw.gateTau i => 12 + 3 * d + 3 * i.val
  | Draw.outerLog _ => 0
  | Draw.outerGate _ => 3

/-- The draw's place in the source squeeze schedule. -/
def schedulePosition (d : Nat) (k : Draw d) : Nat × Nat := (sourceBlock d k, sourceCounter d k)

theorem gate_alpha_position (d : Nat) :
    schedulePosition d Draw.gateAlpha = (0, 9 + 3 * d) := rfl

theorem gate_tau_position (d : Nat) (i : Fin d) :
    schedulePosition d (Draw.gateTau i) = (0, 12 + 3 * d + 3 * i.val) := rfl

theorem outer_log_position (d : Nat) (r : Fin d) :
    schedulePosition d (Draw.outerLog r) = (r.val + 1, 0) := rfl

theorem outer_gate_position (d : Nat) (r : Fin d) :
    schedulePosition d (Draw.outerGate r) = (r.val + 1, 3) := rfl

/-- (1) The gate alpha is squeezed before every gate tau coordinate, restating
the adopted `CommitmentOrder.gate_alpha_precedes_every_gate_tau_coordinate` on
this index set. -/
theorem gate_alpha_counter_precedes_gate_tau (d : Nat) (i : Fin d) :
    sourceCounter d Draw.gateAlpha < sourceCounter d (Draw.gateTau i) := by
  simp only [sourceCounter]
  omega

/-- (1) NO TWO DRAWS SHARE A SCHEDULE POSITION, so `schedulePosition` really is
injective and no two of these draws are being conflated.

HOW MUCH THAT SHOWS.  `schedulePosition` is THIS MODULE'S OWN map; injectivity
is a fact about it, not about the deployed transcript.  The alpha and tau
counters it returns ARE pinned to source by the adopted
`TranscriptProvenance.derived_columns_at_source_counters` and
`CommitmentOrder.gate_challenge_counters`, through the adopted
`TranscriptProvenance.DerivedInitial` that the section 6 theorems assume.  The
`(r + 1, 0)` and `(r + 1, 3)` labels of `outerLog` / `outerGate` are only
DOCUMENTED, against the adopted
`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`;
the theorems below quantify over an abstract `Verifier.Engine` whose
`commitRound` is free, and nothing derives those two counters for it. -/
theorem schedule_position_injective (d : Nat) : Function.Injective (schedulePosition d) := by
  intro a b h
  have hb := congrArg Prod.fst h
  have hc := congrArg Prod.snd h
  simp only [schedulePosition] at hb hc
  cases a <;> cases b <;>
    simp only [sourceBlock, sourceCounter] at hb hc <;>
    first
      | rfl
      | (exact absurd hb (by omega))
      | (exact absurd hc (by omega))
      | (exact congrArg _ (Fin.ext (by omega)))

/-! ## 2. The ONE sample space and its uniform law -/

/-- THE JOINT SAMPLE SPACE.  One `OuterChallenge.DigestTriple` per scheduled
draw: the outer coupled-round challenges of both lanes, the gate alpha and the
whole gate tau column, indexed in source counter order. -/
abbrev JointSpace (d : Nat) := Draw d → OuterChallenge.DigestTriple

theorem joint_space_card (d : Nat) :
    Fintype.card (JointSpace d) = (OuterChallenge.wordSize ^ 3) ^ (3 * d + 1) := by
  rw [Fintype.card_fun, draw_card, OuterChallenge.digest_tuple_cardinality]

/-- (1) CARDINALITY.  `(2^768)^(3 * degreeBits + 1)`: one `2^768` per scheduled
draw, and `3 * degreeBits + 1` draws. -/
theorem joint_space_card_bits (d : Nat) :
    Fintype.card (JointSpace d) = (2 ^ 768) ^ (3 * d + 1) := by
  rw [joint_space_card, OuterChallenge.word_size_is_256_bits]
  congr 1

theorem digest_triple_card_pos : 0 < Fintype.card OuterChallenge.DigestTriple := by
  rw [OuterChallenge.digest_tuple_cardinality]
  exact pow_pos OuterChallenge.word_size_positive 3

theorem word_size_cast_ne_zero : ((OuterChallenge.wordSize : ℚ)) ≠ 0 := by
  have h : (0 : ℚ) < (OuterChallenge.wordSize : ℚ) :=
    Nat.cast_pos.mpr OuterChallenge.word_size_positive
  exact ne_of_gt h

theorem word_size_cube_cast_ne_zero : ((OuterChallenge.wordSize : ℚ) ^ 3) ≠ 0 :=
  pow_ne_zero 3 word_size_cast_ne_zero

theorem joint_space_card_pos (d : Nat) : 0 < Fintype.card (JointSpace d) := by
  rw [joint_space_card]
  exact pow_pos (pow_pos OuterChallenge.word_size_positive 3) _

theorem joint_space_card_cast_pos (d : Nat) :
    (0 : ℚ) < (Fintype.card (JointSpace d) : ℚ) := by
  exact_mod_cast joint_space_card_pos d

/-- Divide both sides of a numerator inequality by the same positive number.
Written out rather than left to `gcongr`, so that no tactic ever has to look at
`Fintype.card` of the byte-based digest space. -/
theorem div_le_div_num (a b c : ℚ) (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  have hinv : (0 : ℚ) ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
  have hm := mul_le_mul_of_nonneg_right h hinv
  simpa only [div_eq_mul_inv] using hm

/-- The cylinder quotient: the free coordinates cancel exactly. -/
theorem cylinder_quotient (T W : ℚ) (m n : Nat) (hW : W ≠ 0) :
    (T * W ^ m) / (W ^ m * W ^ n) = T / W ^ n := by
  rw [mul_comm T (W ^ m)]
  exact mul_div_mul_left _ _ (pow_ne_zero m hW)

/-- THE EXPLICIT IDEAL JOINT LAW.  Same convention as the adopted
`OuterChallenge.uniformTupleProbability`: count on an explicit finite space,
then divide by its size.  The product structure over the schedule IS the
independence assumption; it is written down here, not derived from any hash. -/
noncomputable def jointProbability (d : Nat) (E : Finset (JointSpace d)) : ℚ :=
  (E.card : ℚ) / (Fintype.card (JointSpace d) : ℚ)

theorem joint_probability_nonneg (d : Nat) (E : Finset (JointSpace d)) :
    0 ≤ jointProbability d E :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem joint_probability_empty (d : Nat) : jointProbability d (∅ : Finset (JointSpace d)) = 0 := by
  rw [jointProbability, Finset.card_empty, Nat.cast_zero, zero_div]

theorem joint_probability_mono (d : Nat) (A B : Finset (JointSpace d)) (h : A ⊆ B) :
    jointProbability d A ≤ jointProbability d B := by
  have hc : (A.card : ℚ) ≤ (B.card : ℚ) := by exact_mod_cast Finset.card_le_card h
  exact div_le_div_num _ _ _ hc (joint_space_card_cast_pos d)

/-- SUBADDITIVITY: the whole point of a genuine union bound. -/
theorem joint_probability_union_le (d : Nat) (A B : Finset (JointSpace d)) :
    jointProbability d (A ∪ B) ≤ jointProbability d A + jointProbability d B := by
  unfold jointProbability
  rw [div_add_div_same]
  have hc : ((A ∪ B).card : ℚ) ≤ ((A.card + B.card : Nat) : ℚ) := by
    exact_mod_cast Finset.card_union_le A B
  have hc2 : ((A ∪ B).card : ℚ) ≤ (A.card : ℚ) + (B.card : ℚ) := by push_cast at hc; exact hc
  exact div_le_div_num _ _ _ hc2 (joint_space_card_cast_pos d)

theorem joint_probability_compl (d : Nat) (E : Finset (JointSpace d)) :
    jointProbability d (Finset.univ \ E) = 1 - jointProbability d E := by
  have hpos := joint_space_card_cast_pos d
  have hle : E.card ≤ Fintype.card (JointSpace d) := Finset.card_le_univ E
  unfold jointProbability
  rw [Finset.card_sdiff (Finset.subset_univ E), Finset.card_univ, Nat.cast_sub hle, sub_div,
    div_self (ne_of_gt hpos)]

/-! ## 3. Cylinders: the mass of a cylinder set is the mass of its base

This is the product-measure projection fact, done by counting rather than by
Mathlib's measure theory: a set of joint points constrained on SOME coordinates
and free on the rest has the base's cardinality times the free space's
cardinality, so dividing by the whole space cancels the free factor exactly. -/

/-- ONE-COORDINATE PULLBACK: the joint points whose coordinate `k` reduces into
the adopted `Finset Element` bad set `S`. -/
def coordEvent (d : Nat) (k : Draw d) (S : Finset Element) : Finset (JointSpace d) :=
  Finset.univ.filter (fun w => OuterChallenge.reduceTriple (w k) ∈ S)

theorem mem_coordEvent (d : Nat) (k : Draw d) (S : Finset Element) (w : JointSpace d) :
    w ∈ coordEvent d k S ↔ OuterChallenge.reduceTriple (w k) ∈ S := by
  simp only [coordEvent, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_tupleEvent (S : Finset Element) (ds : OuterChallenge.DigestTriple) :
    ds ∈ OuterChallenge.tupleEvent S ↔ OuterChallenge.reduceTriple ds ∈ S := by
  simp only [OuterChallenge.tupleEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The coordinatewise constraint of a one-coordinate cylinder: the base at
coordinate `k`, everything free elsewhere. -/
def coordFamily (d : Nat) (k : Draw d) (T : Finset OuterChallenge.DigestTriple)
    (j : Draw d) : Finset OuterChallenge.DigestTriple :=
  if j = k then T else Finset.univ

theorem coordFamily_self (d : Nat) (k : Draw d) (T : Finset OuterChallenge.DigestTriple) :
    coordFamily d k T k = T := by
  unfold coordFamily
  exact if_pos rfl

theorem coordFamily_other (d : Nat) (k j : Draw d) (T : Finset OuterChallenge.DigestTriple)
    (h : j ≠ k) : coordFamily d k T j = Finset.univ := by
  unfold coordFamily
  exact if_neg h

theorem coordEvent_eq_piFinset (d : Nat) (k : Draw d) (S : Finset Element) :
    coordEvent d k S = Fintype.piFinset (coordFamily d k (OuterChallenge.tupleEvent S)) := by
  ext w
  rw [mem_coordEvent, Fintype.mem_piFinset]
  constructor
  · intro h j
    by_cases hj : j = k
    · subst hj
      rw [coordFamily_self, mem_tupleEvent]
      exact h
    · rw [coordFamily_other d k j _ hj]
      simp only [Finset.mem_univ]
  · intro h
    have hk := h k
    rw [coordFamily_self, mem_tupleEvent] at hk
    exact hk

/-- (2) THE CYLINDER COUNT.  A one-coordinate cylinder has the base's count
times one free `2^768` for each of the other `3 * degreeBits` draws. -/
theorem coordEvent_card (d : Nat) (k : Draw d) (S : Finset Element) :
    (coordEvent d k S).card
      = (OuterChallenge.tupleEvent S).card * (OuterChallenge.wordSize ^ 3) ^ (3 * d) := by
  rw [coordEvent_eq_piFinset, Fintype.card_piFinset,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), coordFamily_self]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => by
      rw [coordFamily_other d k j _ (Finset.ne_of_mem_erase hj), Finset.card_univ,
        OuterChallenge.digest_tuple_cardinality]),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, draw_card]
  congr 1

/-- (2) THE PROJECTION FACT, one coordinate.  The mass of the pullback under the
JOINT uniform law EQUALS the adopted per-space mass
`OuterChallenge.uniformTupleProbability` of its base.  Nothing is lost or gained
by moving the adopted single-triple events onto the joint space. -/
theorem coord_event_mass (d : Nat) (k : Draw d) (S : Finset Element) :
    jointProbability d (coordEvent d k S) = OuterChallenge.uniformTupleProbability S := by
  unfold jointProbability OuterChallenge.uniformTupleProbability
  rw [coordEvent_card, joint_space_card, OuterChallenge.digest_tuple_cardinality]
  push_cast
  rw [pow_succ ((OuterChallenge.wordSize : ℚ) ^ 3) (3 * d)]
  simpa only [pow_one] using
    cylinder_quotient ((OuterChallenge.tupleEvent S).card : ℚ)
      ((OuterChallenge.wordSize : ℚ) ^ 3) (3 * d) 1 word_size_cube_cast_ne_zero

/-! ### The gate tau coordinates as a block -/

/-- The `degreeBits` gate tau coordinates of a joint point, reduced.  This is
the adopted `ChallengeUnionBound.reduceTuple` applied to the tau block. -/
def tauReduction (d : Nat) (w : JointSpace d) : ZeroCheckSemantics.Tuple d :=
  fun i => OuterChallenge.reduceTriple (w (Draw.gateTau i))

/-- MULTI-COORDINATE PULLBACK: the joint points whose gate tau block reduces
into a set of tau tuples. -/
def tauEvent (d : Nat) (S : Finset (ZeroCheckSemantics.Tuple d)) : Finset (JointSpace d) :=
  Finset.univ.filter (fun w => tauReduction d w ∈ S)

theorem mem_tauEvent (d : Nat) (S : Finset (ZeroCheckSemantics.Tuple d)) (w : JointSpace d) :
    w ∈ tauEvent d S ↔ tauReduction d w ∈ S := by
  simp only [tauEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The draws OTHER than the gate tau block: the gate alpha and the two
coupled-round challenges of each round. -/
abbrev TauRest (d : Nat) := Unit ⊕ Fin d ⊕ Fin d

theorem tau_rest_card (d : Nat) : Fintype.card (TauRest d) = 2 * d + 1 := by
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

theorem tau_rest_fun_card (d : Nat) :
    Fintype.card (TauRest d → OuterChallenge.DigestTriple)
      = (OuterChallenge.wordSize ^ 3) ^ (2 * d + 1) := by
  rw [Fintype.card_fun, tau_rest_card, OuterChallenge.digest_tuple_cardinality]

/-- The joint space splits as (tau block) x (everything else). -/
def tauSplit (d : Nat) :
    JointSpace d ≃ ChallengeUnionBound.TripleTuple d × (TauRest d → OuterChallenge.DigestTriple) where
  toFun w :=
    (fun i => w (Draw.gateTau i),
     fun j => match j with
       | Sum.inl _ => w Draw.gateAlpha
       | Sum.inr (Sum.inl r) => w (Draw.outerLog r)
       | Sum.inr (Sum.inr r) => w (Draw.outerGate r))
  invFun q := fun k => match k with
    | Draw.gateAlpha => q.2 (Sum.inl ())
    | Draw.gateTau i => q.1 i
    | Draw.outerLog r => q.2 (Sum.inr (Sum.inl r))
    | Draw.outerGate r => q.2 (Sum.inr (Sum.inr r))
  left_inv w := by funext k; cases k <;> rfl
  right_inv q := by
    obtain ⟨t, r⟩ := q
    refine Prod.ext ?_ ?_
    · funext i; rfl
    · funext j; rcases j with _ | i | i <;> rfl

theorem tauEvent_card (d : Nat) (S : Finset (ZeroCheckSemantics.Tuple d)) :
    (tauEvent d S).card
      = (ChallengeUnionBound.productEvent d S).card
        * (OuterChallenge.wordSize ^ 3) ^ (2 * d + 1) := by
  classical
  have hmap : tauEvent d S
      = ((ChallengeUnionBound.productEvent d S) ×ˢ
          (Finset.univ : Finset (TauRest d → OuterChallenge.DigestTriple))).map
            (tauSplit d).symm.toEmbedding := by
    ext w
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
    simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_tauEvent,
      ChallengeUnionBound.mem_productEvent]
    exact Iff.rfl
  rw [hmap, Finset.card_map, Finset.card_product, Finset.card_univ, tau_rest_fun_card]

/-- (2) THE PROJECTION FACT, the tau block.  The mass of the pullback under the
JOINT uniform law EQUALS the adopted product mass
`ChallengeUnionBound.uniformProductProbability` on `TripleTuple degreeBits`. -/
theorem tau_event_mass (d : Nat) (S : Finset (ZeroCheckSemantics.Tuple d)) :
    jointProbability d (tauEvent d S) = ChallengeUnionBound.uniformProductProbability d S := by
  unfold jointProbability ChallengeUnionBound.uniformProductProbability
  rw [tauEvent_card, joint_space_card, ChallengeUnionBound.product_space_card]
  push_cast
  rw [show 3 * d + 1 = (2 * d + 1) + d by omega,
    pow_add ((OuterChallenge.wordSize : ℚ) ^ 3) (2 * d + 1) d]
  exact cylinder_quotient ((ChallengeUnionBound.productEvent d S).card : ℚ)
    ((OuterChallenge.wordSize : ℚ) ^ 3) (2 * d + 1) d word_size_cube_cast_ne_zero

/-! ## 4. The three adopted bad sets, pulled back to THIS ONE space -/

/-- Which joint coordinate carries coupled round `k`'s LOG challenge.  Total by
construction; only `k < degreeBits` is ever used, since a run has exactly
`degreeBits` coupled rounds. -/
def logProj (d : Nat) (k : Nat) : Draw d :=
  if h : k < d then Draw.outerLog ⟨k, h⟩ else Draw.gateAlpha

/-- Which joint coordinate carries coupled round `k`'s GATE challenge. -/
def gateProj (d : Nat) (k : Nat) : Draw d :=
  if h : k < d then Draw.outerGate ⟨k, h⟩ else Draw.gateAlpha

theorem logProj_apply (d k : Nat) (h : k < d) : logProj d k = Draw.outerLog ⟨k, h⟩ := by
  rw [logProj, dif_pos h]

theorem gateProj_apply (d k : Nat) (h : k < d) : gateProj d k = Draw.outerGate ⟨k, h⟩ := by
  rw [gateProj, dif_pos h]

/-- OUTER PULLBACK, one lane.  The adopted `ConditionalSoundness.badSets`
recursion, coordinate by coordinate: round `k`'s adopted `roundBadSet` is pulled
back to the joint coordinate that carries round `k`'s challenge, and the running
claims evolve exactly as in the adopted recursion. -/
noncomputable def laneEvent (d : Nat) (proj : Nat → Draw d) :
    Element → Element → List ConditionalSoundness.LaneRound → Nat → Finset (JointSpace d)
  | _, _, [], _ => ∅
  | a, b, r :: rs, k =>
      coordEvent d (proj k) (ConditionalSoundness.roundBadSet a b r) ∪
        laneEvent d proj (OuterRound.evaluate a r.message r.challenge)
          (OuterRound.evaluate b r.truth r.challenge) rs (k + 1)

/-- (3) LANE MASS.  The joint mass of "some round of this lane agrees" is at
most the adopted per-round bound summed over the rounds, by the SAME counting
the adopted `ConditionalSoundness.bad_sets_uniform_sum` performs -- except that
here it bounds the mass of an actual union event on one space. -/
theorem lane_event_mass_le (d : Nat) (proj : Nat → Draw d) (bound : Nat) :
    ∀ (a b : Element) (rs : List ConditionalSoundness.LaneRound) (k : Nat),
      (∀ r ∈ rs, r.message.length ≤ bound ∧ r.truth.length ≤ bound) →
      jointProbability d (laneEvent d proj a b rs k) ≤
        ((bound * rs.length : Nat) : ℚ) *
          ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3
  | a, b, [], k, _ => by
      simp only [laneEvent, List.length_nil, Nat.mul_zero, Nat.cast_zero, zero_mul]
      exact le_of_eq (joint_probability_empty d)
  | a, b, r :: rs, k, hd => by
      have hhead := hd r (List.mem_cons_self _ _)
      have ih := lane_event_mass_le d proj bound (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) rs (k + 1)
        (fun q hq => hd q (List.mem_cons_of_mem _ hq))
      have hhd : jointProbability d
          (coordEvent d (proj k) (ConditionalSoundness.roundBadSet a b r))
          ≤ (bound : ℚ) *
            ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
        rw [coord_event_mass]
        exact ConditionalSoundness.round_bad_uniform a b r bound hhead.1 hhead.2
      simp only [laneEvent]
      refine (joint_probability_union_le d _ _).trans ?_
      refine (add_le_add hhd ih).trans (le_of_eq ?_)
      rw [List.length_cons]
      push_cast
      ring

/-- THE FIRST PULLBACK: the outer coupled-round bad event of BOTH lanes, on the
round coordinates of the joint space. -/
noncomputable def outerEvent (d : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) : Finset (JointSpace d) :=
  laneEvent d (logProj d) 0 logCompare logLane 0 ∪
    laneEvent d (gateProj d) 0 gateCompare gateLane 0

/-- (3) OUTER MASS.  With the adopted degree bounds (five for the log lane,
`quotientDegree + 2` for the gate lane) and `degreeBits` rounds in each, the
joint mass of the outer event is at most the adopted
`ChallengeUnionBound.outerTerm`, which is the SAME closed form
`ConditionalSoundness.outer_failure_bound` bounds its free `failure` by. -/
theorem outer_event_mass_le (d quotientDegree : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound)
    (hlogLen : logLane.length = d) (hgateLen : gateLane.length = d)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2) :
    jointProbability d (outerEvent d logCompare gateCompare logLane gateLane)
      ≤ ChallengeUnionBound.outerTerm d quotientDegree := by
  have h1 := lane_event_mass_le d (logProj d) 5 0 logCompare logLane 0 hlogDeg
  have h2 := lane_event_mass_le d (gateProj d) (quotientDegree + 2) 0 gateCompare gateLane 0
    hgateDeg
  rw [hlogLen] at h1
  rw [hgateLen] at h2
  refine (joint_probability_union_le d _ _).trans ?_
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  unfold ChallengeUnionBound.outerTerm
  push_cast
  ring

/-- THE SECOND PULLBACK: the adopted `ZeroCheckSemantics.zeroCheckBadSet` on the
gate tau coordinates. -/
noncomputable def tauBadEvent (d : Nat) (g : Nat → Element) : Finset (JointSpace d) :=
  tauEvent d (ZeroCheckSemantics.zeroCheckBadSet d g)

/-- (3) TAU MASS.  Equal to the adopted product mass, hence bounded by the
adopted `ChallengeUnionBound.tauTerm`. -/
theorem tau_bad_event_mass_le (d : Nat) (g : Nat → Element) :
    jointProbability d (tauBadEvent d g) ≤ ChallengeUnionBound.tauTerm d := by
  rw [tauBadEvent, tau_event_mass]
  exact ChallengeUnionBound.tau_product_mass_bound d g

/-- THE THIRD PULLBACK: the adopted `ChallengeUnionBound.alphaUnionBadSet` on
the single gate alpha coordinate. -/
noncomputable def alphaBadEvent (d rows : Nat) (coeffsOf : Nat → List Element) :
    Finset (JointSpace d) :=
  coordEvent d Draw.gateAlpha (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)

/-- (3) ALPHA MASS.  Equal to the adopted single-triple mass, hence bounded by
the adopted `ChallengeUnionBound.alphaTerm`. -/
theorem alpha_bad_event_mass_le (d rows constraints : Nat) (coeffsOf : Nat → List Element)
    (hlen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    jointProbability d (alphaBadEvent d rows coeffsOf)
      ≤ ChallengeUnionBound.alphaTerm rows constraints := by
  rw [alphaBadEvent, coord_event_mass]
  exact ChallengeUnionBound.alpha_union_mass_bound rows constraints coeffsOf hlen

/-! ## 5. The GENUINE union bound

Three pullbacks, ONE space, ONE law, ONE disjunction event. -/

/-- THE DISJUNCTION EVENT: some outer coupled round agrees, OR the gate tau
column lands in the zero-check bad set, OR the gate alpha lands in the union of
the per-row alpha bad sets. -/
noncomputable def jointBadEvent (d : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (rows : Nat) (coeffsOf : Nat → List Element) : Finset (JointSpace d) :=
  outerEvent d logCompare gateCompare logLane gateLane ∪ tauBadEvent d g ∪
    alphaBadEvent d rows coeffsOf

/-- (3) IT REALLY IS A DISJUNCTION.  Membership in the joint bad event is the
disjunction of the three pullback memberships -- so its complement is exactly
"all three good", coordinate by coordinate. -/
theorem mem_jointBadEvent (d : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (rows : Nat) (coeffsOf : Nat → List Element) (w : JointSpace d) :
    w ∈ jointBadEvent d logCompare gateCompare logLane gateLane g rows coeffsOf ↔
      (w ∈ outerEvent d logCompare gateCompare logLane gateLane ∨ w ∈ tauBadEvent d g ∨
        w ∈ alphaBadEvent d rows coeffsOf) := by
  simp only [jointBadEvent, Finset.mem_union, or_assoc]

/-- THE GOOD EVENT: the complement of the disjunction. -/
noncomputable def goodEvent (d : Nat) (E : Finset (JointSpace d)) : Finset (JointSpace d) :=
  Finset.univ \ E

theorem mem_goodEvent (d : Nat) (E : Finset (JointSpace d)) (w : JointSpace d) :
    w ∈ goodEvent d E ↔ w ∉ E := by
  simp only [goodEvent, Finset.mem_sdiff, Finset.mem_univ, true_and]

/-- (3) THE UNION IS THE COMPLEMENT OF "ALL THREE GOOD". -/
theorem mem_good_joint_event (d : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (rows : Nat) (coeffsOf : Nat → List Element) (w : JointSpace d) :
    w ∈ goodEvent d (jointBadEvent d logCompare gateCompare logLane gateLane g rows coeffsOf) ↔
      (w ∉ outerEvent d logCompare gateCompare logLane gateLane ∧ w ∉ tauBadEvent d g ∧
        w ∉ alphaBadEvent d rows coeffsOf) := by
  rw [mem_goodEvent, mem_jointBadEvent, not_or, not_or]

/-- (3) THE SAME, PHRASED WITHOUT `Finset.univ`.  A draw avoids the disjunction
exactly when it avoids all three pullbacks.  This form is the one consumed by
section 6: writing `w ∈ goodEvent d E` in the STATEMENT of a theorem forces the
elaborator through `Finset.univ` on the byte-based joint space, which is not
tractable, while `w ∉ E` is. -/
theorem not_mem_jointBadEvent (d : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (rows : Nat) (coeffsOf : Nat → List Element) (w : JointSpace d) :
    w ∉ jointBadEvent d logCompare gateCompare logLane gateLane g rows coeffsOf ↔
      (w ∉ outerEvent d logCompare gateCompare logLane gateLane ∧ w ∉ tauBadEvent d g ∧
        w ∉ alphaBadEvent d rows coeffsOf) := by
  rw [mem_jointBadEvent, not_or, not_or]

/-- (3) **THE GENUINE UNION BOUND.**  The mass of an ACTUAL DISJUNCTION EVENT in
ONE explicit finite sample space, under ONE explicit uniform law, is at most the
sum of the three adopted terms, i.e. at most the adopted
`ChallengeUnionBound.combinedBound`.

This is what the adopted `ChallengeUnionBound.combined_union_bound` could not
say.  Its verification recorded: "no disjunction event exists; no joint event or
law is formalized; this is an arithmetic inequality between three independently
derived quotients, not the probability of a union."  Here the three quotients
are the masses of three subsets of ONE space, and the inequality is
subadditivity of that space's uniform law.

WHAT IT STILL IS NOT.  It is not a probability about Keccak, and it does not
cover the WHIR/Merkle events, which dominate. -/
theorem joint_union_bound (d quotientDegree constraints : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hlogLen : logLane.length = d) (hgateLen : gateLane.length = d)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hlen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    jointProbability d
        (jointBadEvent d logCompare gateCompare logLane gateLane g (2 ^ d) coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d quotientDegree d constraints := by
  have h1 := outer_event_mass_le d quotientDegree logCompare gateCompare logLane gateLane
    hlogLen hgateLen hlogDeg hgateDeg
  have h2 := tau_bad_event_mass_le d g
  have h3 := alpha_bad_event_mass_le d (2 ^ d) constraints coeffsOf hlen
  unfold jointBadEvent ChallengeUnionBound.combinedBound
  refine (joint_probability_union_le d _ _).trans ?_
  refine add_le_add ((joint_probability_union_le d _ _).trans (add_le_add h1 h2)) h3

/-- (3) **THE GOOD EVENT HAS MASS AT LEAST `1 - combinedBound`.**  The
complement form of the union bound: under the explicit joint uniform law, the
probability that ALL THREE families of challenge draws are simultaneously good
is at least `1 - combinedBound degreeBits quotientDegree degreeBits
numGateConstraints`. -/
theorem joint_good_event_mass_ge (d quotientDegree constraints : Nat)
    (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hlogLen : logLane.length = d) (hgateLen : gateLane.length = d)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hlen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    1 - ChallengeUnionBound.combinedBound d quotientDegree d constraints
      ≤ jointProbability d (goodEvent d
          (jointBadEvent d logCompare gateCompare logLane gateLane g (2 ^ d) coeffsOf)) := by
  have h := joint_union_bound d quotientDegree constraints logCompare gateCompare logLane gateLane
    g coeffsOf hlogLen hgateLen hlogDeg hgateDeg hlen
  rw [goodEvent, joint_probability_compl]
  linarith

/-! ## 6. THE SEAM, STATED EXACTLY ONCE -/

open Audit.Wire3.TranscriptProvenance (Hash DerivedInitial gateTauColumn gateAlphaElement)

/-- The lane-by-lane statement that the challenges the run drew at the coupled
rounds ARE the reductions of the joint point's round coordinates, in order.
Mirrors the shape of the adopted `ConditionalSoundness.BadEventFree` recursion
so that the two can be consumed together. -/
def DrawnAt (d : Nat) (w : JointSpace d) (proj : Nat → Draw d) :
    List ConditionalSoundness.LaneRound → Nat → Prop
  | [], _ => True
  | r :: rs, k =>
      r.challenge = OuterChallenge.reduceTriple (w (proj k)) ∧ DrawnAt d w proj rs (k + 1)

/-! ### 6a. The reduction is SURJECTIVE, so a draw encoding any run exists

Everything in this subsection is hash-free: it says only that any `Element` can
be written as the modular reduction of an explicit 32-byte digest triple.  It is
what makes the seam below INHABITED rather than assumed. -/

/-- The little-endian 32-byte encoding of a natural number, as an
`OuterChallenge.DigestBlock`. -/
def encodeNat (n : Nat) : OuterChallenge.DigestBlock :=
  ⟨Transcript.le 32 n, Transcript.le_length 32 n⟩

/-- (6) The Goldilocks modulus fits in a 32-byte word, so the encoding above
never wraps. -/
theorem modulus_lt_word : Arithmetic.modulus < 256 ^ 32 := by norm_num [Arithmetic.modulus]

/-- (6) `encodeNat` is a section of "read little-endian, then reduce mod p" on
residues. -/
theorem fromLe_encodeNat_mod (n : Nat) (h : n < Arithmetic.modulus) :
    Transcript.fromLe (encodeNat n).val % Arithmetic.modulus = n := by
  show Transcript.fromLe (Transcript.le 32 n) % Arithmetic.modulus = n
  rw [Transcript.fromLe_le_roundtrip 32 n (lt_trans h modulus_lt_word), Nat.mod_eq_of_lt h]

/-- The explicit digest triple above an `Element`: encode each of the three
Goldilocks limbs little-endian into its own 32-byte block. -/
def encodeElement (x : Element) : OuterChallenge.DigestTriple :=
  (encodeNat x.toVerifier.val.c0, encodeNat x.toVerifier.val.c1, encodeNat x.toVerifier.val.c2)

/-- (6) The explicit preimage really is one: reducing `encodeElement x` returns
`x`. -/
theorem reduceTriple_encodeElement (x : Element) :
    OuterChallenge.reduceTriple (encodeElement x) = x := by
  obtain ⟨⟨⟨c0, c1, c2⟩, h0, h1, h2⟩⟩ := x
  apply element_eq
  apply Subtype.ext
  show Arithmetic.Ext3.mk (Transcript.fromLe (encodeNat c0).val % Arithmetic.modulus)
    (Transcript.fromLe (encodeNat c1).val % Arithmetic.modulus)
    (Transcript.fromLe (encodeNat c2).val % Arithmetic.modulus) = ⟨c0, c1, c2⟩
  rw [fromLe_encodeNat_mod c0 h0, fromLe_encodeNat_mod c1 h1, fromLe_encodeNat_mod c2 h2]

/-- (6) **THE ADOPTED REDUCTION IS SURJECTIVE.**  Every field element is the
modular reduction of some 32-byte digest triple.  This is a fact about the
encoding alone -- no hash, no engine, no proof appears -- and it is the reason
`DrawEncodesRun` below is inhabited rather than assumed. -/
theorem reduceTriple_surjective : Function.Surjective OuterChallenge.reduceTriple :=
  fun x => ⟨encodeElement x, reduceTriple_encodeElement x⟩

/-- (6) `DrawnAt` from a pointwise description of the lane's challenges. -/
theorem drawnAt_of_pointwise (d : Nat) (w : JointSpace d) (proj : Nat → Draw d) :
    ∀ (rs : List ConditionalSoundness.LaneRound) (k : Nat),
      (∀ j (hj : j < rs.length),
        (rs.get ⟨j, hj⟩).challenge = OuterChallenge.reduceTriple (w (proj (k + j)))) →
      DrawnAt d w proj rs k
  | [], _, _ => trivial
  | r :: rs, k, h => by
      refine ⟨?_, drawnAt_of_pointwise d w proj rs (k + 1) ?_⟩
      · have := h 0 (Nat.succ_pos _)
        simpa using this
      · intro j hj
        have := h (j + 1) (Nat.succ_lt_succ hj)
        rw [show k + 1 + j = k + (j + 1) by omega]
        exact this

/-- (6) `DrawnAt` holds at the canonical draw: if the joint point carries, at
each round coordinate, the explicit encoding of that round's own challenge, then
the lane is drawn at it. -/
theorem drawnAt_canonical (d : Nat) (rs : List ConditionalSoundness.LaneRound)
    (hlen : rs.length ≤ d) (w : JointSpace d) (proj : Nat → Draw d) (coord : Fin d → Draw d)
    (hproj : ∀ k (hk : k < d), proj k = coord ⟨k, hk⟩)
    (hw : ∀ r : Fin d, w (coord r)
      = encodeElement (((rs.get? r.val).map ConditionalSoundness.LaneRound.challenge).getD 0)) :
    DrawnAt d w proj rs 0 := by
  apply drawnAt_of_pointwise
  intro j hj
  have hjd : j < d := lt_of_lt_of_le hj hlen
  rw [Nat.zero_add, hproj j hjd, hw ⟨j, hjd⟩, reduceTriple_encodeElement, List.get?_eq_get hj,
    Option.map_some', Option.getD_some]

/-- THE CANONICAL DRAW OF A RUN: at every scheduled coordinate, the explicit
32-byte encoding of the challenge value the run itself took there.  Defined for
EVERY hash, engine and proof; no hash property is used. -/
noncomputable def canonicalDraw (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (logTruths gateTruths : List (List Element)) : JointSpace vc.degreeBits
  | Draw.gateAlpha => encodeElement (gateAlphaElement hash vc p)
  | Draw.gateTau i => encodeElement (((gateTauColumn hash vc p).get? i.val).getD 0)
  | Draw.outerLog r => encodeElement ((((ConditionalSoundness.logLaneOf e vc p logTruths).get? r.val).map
      ConditionalSoundness.LaneRound.challenge).getD 0)
  | Draw.outerGate r => encodeElement ((((ConditionalSoundness.gateLaneOf e vc p gateTruths).get? r.val).map
      ConditionalSoundness.LaneRound.challenge).getD 0)

/--
**THE SEAM: A COORDINATE STATEMENT, NOT A HASH ASSUMPTION.**

`DrawEncodesRun hash e vc p logTruths gateTruths draw` says: the challenge
values the REAL run draws after the commitment prefix are exactly the
coordinatewise modular reductions of the single joint sample point `draw` --
the two coupled-round challenges of every round at the round coordinates, the
derived gate alpha at the alpha coordinate, and every derived gate tau
coordinate at its own tau coordinate.  In one phrase: `draw` ENCODES the run.

* **IT IS INHABITED FOR EVERY ACCEPTED RUN AND FOR EVERY HASH, SO IT IS NOT AN
  ASSUMPTION ON THE HASH.**  `OuterChallenge.reduceTriple` is surjective
  (`reduceTriple_surjective`), so every challenge value the run actually took
  has a 32-byte digest triple above it; assembling those preimages coordinate by
  coordinate gives `canonicalDraw`, and `draw_encodes_run_inhabited` proves that
  this structure holds AT that draw for EVERY `hash`, EVERY `Verifier.Engine`,
  EVERY `Verifier.Proof` whose two lanes fit the schedule -- no hash property is
  used anywhere in the proof.  `draw_encodes_run_of_accepted` specialises it to
  the composed theorem's setting: under `Integrated.verify … = .ok ()` the
  lane-length side conditions are discharged, so a witnessing `draw` EXISTS
  outright.
* **WHAT IT IS NOT.**  It does NOT say that `draw` is uniform, and it does not
  say anything about a distribution.  The Fiat--Shamir half (B) -- "the run's
  encoding draw is distributed by `jointProbability`" -- is the UNFORMALIZED
  reading of this module.  Nothing here expresses or assumes it in Lean: there
  is no probability space over hashes or over runs in this development, only
  counting on `JointSpace`.  The composed theorem below therefore carries NO
  cryptographic hypothesis; joining its two conjuncts into a probability
  statement about a real run is the step this audit does not take.
* **WHY THAT STEP CANNOT BE RECOVERED FROM ORDERING.**  The adopted
  `Audit.Wire3.CommitmentOrder` proves half (A) -- the gate wire/constant tables
  behind the tau and alpha families are fixed by material absorbed BEFORE these
  squeezes -- and its `separation_fails_for_a_deterministic_hash` proves that
  even the strictly weaker deterministic shadow of (B) ("distinct prefixes give
  distinct challenges") is FALSE for a general deterministic hash: the constant
  hash gives the same gate alpha to two statements whose absorbed prefixes
  differ in the norm-inverse root frame.
* **HOW THIS SITS AGAINST `draw ∉ runBadEvent`.**  In the composed theorem the
  encoding draw is additionally required to avoid `runBadEvent`.  At the
  ENCODING draw that hypothesis is nothing but the conjunction of the adopted
  `ConditionalSoundness.BadEventFree` (gate lane),
  `GateDerivedRejection.GoodDerivedTau` and
  `GateDerivedRejection.GoodDerivedAlpha` hypotheses, re-spelled as
  non-membership in three cylinders: `badEventFree_of_lane`,
  `good_derived_tau_of_joint` and `good_derived_alpha_of_joint` are exactly the
  translations, and they use nothing but the fields of this structure.  So the
  composed theorem assumes no more than the adopted `hgood` hypotheses do.
* **THE OUTER COORDINATE LABELS ARE DOCUMENTED, NOT DERIVED.**  See
  `schedule_position_injective`: counters `0` and `3` come from the adopted
  `OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`,
  while `e.commitRound` here is an abstract `Verifier.CommitRound`. -/
structure DrawEncodesRun (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (logTruths gateTruths : List (List Element))
    (draw : JointSpace vc.degreeBits) : Prop where
  /-- Each coupled round's LOG challenge is the reduction of that round's log
  coordinate.  The coordinate is LABELLED counter `0` of the round's commit
  digest after the adopted
  `OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`;
  for the abstract `e.commitRound` quantified over here that label is
  documentation, and this field constrains only the VALUE. -/
  logDrawn : DrawnAt vc.degreeBits draw (logProj vc.degreeBits)
    (ConditionalSoundness.logLaneOf e vc p logTruths) 0
  /-- Each coupled round's GATE challenge is the reduction of that round's gate
  coordinate (labelled counter `3` of the round's commit digest, with the same
  documented-not-derived caveat as `logDrawn`). -/
  gateDrawn : DrawnAt vc.degreeBits draw (gateProj vc.degreeBits)
    (ConditionalSoundness.gateLaneOf e vc p gateTruths) 0
  /-- The derived gate alpha (counter `9 + 3 * degreeBits`) is the reduction of
  the alpha coordinate. -/
  alphaDrawn : gateAlphaElement hash vc p = OuterChallenge.reduceTriple (draw Draw.gateAlpha)
  /-- Derived gate tau coordinate `i` (counter `12 + 3 * degreeBits + 3 * i`) is
  the reduction of tau coordinate `i`. -/
  tauDrawn : ∀ i : Fin vc.degreeBits, ∀ h : i.val < (gateTauColumn hash vc p).length,
    (gateTauColumn hash vc p).get ⟨i.val, h⟩
      = OuterChallenge.reduceTriple (draw (Draw.gateTau i))

/-- (6) **THE SEAM IS INHABITED FOR EVERY HASH.**  For EVERY `hash`, EVERY
`Verifier.Engine`, EVERY `Verifier.Proof` whose two lanes have at most
`degreeBits` rounds, `DrawEncodesRun` holds AT the explicit `canonicalDraw`.

THE PROOF USES NO PROPERTY OF THE HASH.  It is `reduceTriple_surjective` applied
coordinate by coordinate: the run's own challenge values are re-encoded as
32-byte digest triples and placed at their scheduled coordinates.  Consequently
`DrawEncodesRun` IS NOT AN ASSUMPTION ON THE HASH -- it is a statement about
which point of `JointSpace` one is looking at.  What is NOT proved by this, and
is not stated anywhere in this module, is the Fiat--Shamir reading that this
draw is DISTRIBUTED by `jointProbability`. -/
theorem draw_encodes_run_inhabited (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (logTruths gateTruths : List (List Element))
    (hl : (ConditionalSoundness.logLaneOf e vc p logTruths).length ≤ vc.degreeBits)
    (hg : (ConditionalSoundness.gateLaneOf e vc p gateTruths).length ≤ vc.degreeBits) :
    DrawEncodesRun hash e vc p logTruths gateTruths
      (canonicalDraw hash e vc p logTruths gateTruths) where
  logDrawn := drawnAt_canonical _ _ hl _ _ Draw.outerLog
    (fun k hk => logProj_apply _ k hk) (fun _ => rfl)
  gateDrawn := drawnAt_canonical _ _ hg _ _ Draw.outerGate
    (fun k hk => gateProj_apply _ k hk) (fun _ => rfl)
  alphaDrawn := (reduceTriple_encodeElement _).symm
  tauDrawn := by
    intro i h
    show _ = OuterChallenge.reduceTriple (encodeElement _)
    rw [reduceTriple_encodeElement, List.get?_eq_get h, Option.getD_some]

/-- (6) **THE SEAM IS INHABITED FOR EVERY ACCEPTED RUN.**  Under acceptance of
the adopted `Integrated.verify` the two lane-length side conditions of
`draw_encodes_run_inhabited` are discharged from the adopted shape lemmas, so a
witnessing `draw` EXISTS outright -- for every hash, with no hash property used.

This is the composed theorem's own setting, so the `DrawEncodesRun` hypothesis
there costs nothing: the remaining content of that hypothesis, once a draw is
fixed, is the conjunction of the adopted `BadEventFree` / `GoodDerivedTau` /
`GoodDerivedAlpha` hypotheses re-spelled as non-membership in three cylinders. -/
theorem draw_encodes_run_of_accepted (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (vc : Verifier.Config)
    (p : Verifier.Proof) (logTruths gateTruths : List (List Element))
    (hacc : Integrated.verify e decode pin chain vc p = .ok ()) :
    ∃ draw, DrawEncodesRun hash e vc p logTruths gateTruths draw := by
  obtain ⟨-, -, -, -, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain vc p hacc
  obtain ⟨-, -, -, -, hshape, -, -, -, -, -, -, -⟩ :=
    (IntegratedTerminalChain.verify_iff_solidity_order (Integrated.modelEngine e decode)
      pin chain vc p).mp hv
  obtain ⟨hlr, hgr, -, -⟩ := ConditionalSoundness.shape_round_lengths pin vc p hshape
  obtain ⟨hlogLen, -⟩ := ConditionalSoundness.lane_length_of_shape e vc p logTruths hlr hgr
  obtain ⟨-, hgateLen⟩ := ConditionalSoundness.lane_length_of_shape e vc p gateTruths hlr hgr
  exact ⟨_, draw_encodes_run_inhabited hash e vc p logTruths gateTruths hlogLen.le hgateLen.le⟩

/-- A good outer lane coordinate gives the adopted `BadEventFree` for that lane:
round by round, the drawn challenge is outside that round's adopted
`roundBadSet`. -/
theorem badEventFree_of_lane (d : Nat) (w : JointSpace d) (proj : Nat → Draw d) :
    ∀ (a b : Element) (rs : List ConditionalSoundness.LaneRound) (k : Nat),
      DrawnAt d w proj rs k → w ∉ laneEvent d proj a b rs k →
        ConditionalSoundness.BadEventFree a b rs
  | _, _, [], _, _, _ => trivial
  | a, b, r :: rs, k, hdr, hgood => by
      simp only [laneEvent, Finset.mem_union, not_or] at hgood
      refine ⟨?_, badEventFree_of_lane d w proj _ _ rs (k + 1) hdr.2 hgood.2⟩
      intro hbad
      refine hgood.1 ?_
      rw [mem_coordEvent, ← hdr.1]
      exact hbad

/-- Transport of the tau block across the adopted derived width. -/
theorem good_derived_tau_of_joint (hash : Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (w : JointSpace vc.degreeBits) (g : Nat → Element)
    (htau : ∀ i : Fin vc.degreeBits, ∀ h : i.val < (gateTauColumn hash vc p).length,
      (gateTauColumn hash vc p).get ⟨i.val, h⟩
        = OuterChallenge.reduceTriple (w (Draw.gateTau i)))
    (hgood : w ∉ tauBadEvent vc.degreeBits g) :
    GateDerivedRejection.GoodDerivedTau hash vc p g := by
  have hw : (gateTauColumn hash vc p).length = vc.degreeBits :=
    GateDerivedRejection.derived_gate_tau_width hash vc p
  have key : ∀ (n : Nat) (col : List Element), col.length = n →
      ∀ t : ZeroCheckSemantics.Tuple n,
        (∀ i : Fin n, ∀ h : i.val < col.length, col.get ⟨i.val, h⟩ = t i) →
        ZeroCheckSemantics.tupleOf col ∈ ZeroCheckSemantics.zeroCheckBadSet col.length g →
        t ∈ ZeroCheckSemantics.zeroCheckBadSet n g := by
    intro n col hn t hget
    subst hn
    have ht : ZeroCheckSemantics.tupleOf col = t := by
      funext i
      exact hget i i.isLt
    rw [ht]
    exact id
  intro hmem
  refine hgood ?_
  rw [tauBadEvent, mem_tauEvent]
  exact key vc.degreeBits (gateTauColumn hash vc p) hw (tauReduction vc.degreeBits w)
    (fun i h => htau i h) hmem

/-- A good alpha coordinate gives the adopted `GoodDerivedAlpha` at EVERY row of
the Boolean cube at once, via the adopted
`ChallengeUnionBound.alpha_outside_union`. -/
theorem good_derived_alpha_of_joint (hash : Hash) (vc : Verifier.Config) (p : Verifier.Proof)
    (w : JointSpace vc.degreeBits) (rows : Nat) (coeffsOf : Nat → List Element)
    (halpha : gateAlphaElement hash vc p = OuterChallenge.reduceTriple (w Draw.gateAlpha))
    (hgood : w ∉ alphaBadEvent vc.degreeBits rows coeffsOf) (i : Nat) (hi : i < rows) :
    GateDerivedRejection.GoodDerivedAlpha hash vc p (coeffsOf i) := by
  have hnot : gateAlphaElement hash vc p ∉
      ChallengeUnionBound.alphaUnionBadSet rows coeffsOf := by
    intro hmem
    refine hgood ?_
    rw [alphaBadEvent, mem_coordEvent, ← halpha]
    exact hmem
  exact ChallengeUnionBound.alpha_outside_union rows coeffsOf _ hnot i hi

/-- THE LOG LANE'S COMPARE VALUE, exactly as the adopted
`ConditionalSoundness.Assumptions.challengeIndependent` writes it: the honest
endpoint sum `f(0) + f(1)` of the extracted norm prover's current round, lifted
into `Element`.  The generic statements of sections 4 and 5 quantify over an
arbitrary compare value; the RUN-LEVEL statements below use THIS one, so the
first conjunct's event is no longer indexed by an arbitrary element. -/
def logCompareOf (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) : Element :=
  NormPolynomial.lift (OuterClaimChain.endpointSum t pr)

/-- The joint bad event of one accepted gate-lane run: the three pullbacks
instantiated at the run's own lanes, tables and derived gate alpha.  The log
lane's compare value is the adopted `logCompareOf` of the extracted norm tables
`t` and prepared data `pr`, not a free `Element`. -/
noncomputable def runBadEvent (hash : Hash) (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List Element) : Finset (JointSpace vc.degreeBits) :=
  jointBadEvent vc.degreeBits (logCompareOf t pr)
    (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
      (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
      (gateAlphaElement hash vc p) s0)
    (ConditionalSoundness.logLaneOf e vc p logTruths)
    (ConditionalSoundness.gateLaneOf e vc p gateTruths)
    (ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) gates
      (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
      (gateAlphaElement hash vc p) s0.tables)
    (2 ^ vc.degreeBits) coeffsOf

/-- (4) THE MASS HALF OF THE COMPOSED STATEMENT.  Under acceptance and the
adopted degree bounds of both outer lanes (the conclusions of
`ConditionalSoundness.lane_degree_bounds`), the good event of the run's own
joint bad event has mass at least
`1 - combinedBound degreeBits quotientDegree degreeBits numGateConstraints`
under the explicit joint uniform law.

NOTE WHAT THIS THEOREM DOES NOT ASSUME.  It takes NO `DrawEncodesRun`
hypothesis and no hypothesis about the hash whatsoever: it is a COUNTING fact
about `JointSpace vc.degreeBits`, saying that a certain explicitly described
subset of that finite space is large.  It says nothing about how the run's own
challenges are distributed.

READ THE NUMBER CORRECTLY.  `combinedBound` EXCLUDES the dominant WHIR/Merkle
term and is NOT the system's soundness error; at the envelope extremes it is
about `2^-172.07`, so the `2^-172` figure has about 0.07 bits of headroom, while
the deployed design point is around 100 bits. -/
theorem run_good_event_mass_ge (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (vc : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List Element)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf e vc p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf e vc p gateTruths,
      r.message.length ≤ vc.quotientDegree + 2 ∧ r.truth.length ≤ vc.quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ vc.degreeBits → (coeffsOf i).length ≤ vc.numGateConstraints) :
    1 - ChallengeUnionBound.combinedBound vc.degreeBits vc.quotientDegree vc.degreeBits
          vc.numGateConstraints
      ≤ jointProbability vc.degreeBits (goodEvent vc.degreeBits
          (runBadEvent hash e vc p gates s0 logTruths gateTruths t pr coeffsOf)) := by
  obtain ⟨-, -, -, -, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain vc p hacc
  obtain ⟨-, -, -, -, hshape, -, -, -, -, -, -, -⟩ :=
    (IntegratedTerminalChain.verify_iff_solidity_order (Integrated.modelEngine e decode)
      pin chain vc p).mp hv
  obtain ⟨hlr, hgr, -, -⟩ := ConditionalSoundness.shape_round_lengths pin vc p hshape
  obtain ⟨hlogLen, -⟩ := ConditionalSoundness.lane_length_of_shape e vc p logTruths hlr hgr
  obtain ⟨-, hgateLen⟩ := ConditionalSoundness.lane_length_of_shape e vc p gateTruths hlr hgr
  rw [runBadEvent]
  exact joint_good_event_mass_ge vc.degreeBits vc.quotientDegree vc.numGateConstraints
    (logCompareOf t pr)
    (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
      (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
      (gateAlphaElement hash vc p) s0)
    (ConditionalSoundness.logLaneOf e vc p logTruths)
    (ConditionalSoundness.gateLaneOf e vc p gateTruths)
    (ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) gates
      (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
      (gateAlphaElement hash vc p) s0.tables)
    coeffsOf hlogLen hgateLen hlogDeg hgateDeg hclen

set_option maxHeartbeats 1000000 in
/-- (4) THE CONCLUSION HALF OF THE COMPOSED STATEMENT.

Under the adopted `TranscriptProvenance.DerivedInitial`, the adopted
`GateDerivedRejection.DerivedGateAssumptions`, acceptance of the adopted
`Integrated.verify`, and the SEAM `DrawEncodesRun`, EVERY draw outside the
run's joint bad event -- i.e. every point of the good event of
`run_good_event_mass_ge` -- yields the adopted
`GateDerivedRejection.derived_selected_gate_constraints_vanish` conclusion: the
gate selected at row `row` has its evaluator succeed there and every one of its
constraint terms is zero.

Read together with `run_good_event_mass_ge`, the adopted arithmetic inequality
has become the mass of an ACTUAL EVENT under an EXPLICIT JOINT LAW, and the
statement here is what that event's complement buys at the run's own draw.

WHAT IS ASSUMED HERE.  `DrawEncodesRun` is NOT a hash assumption: it is
inhabited for every hash and for every accepted run
(`draw_encodes_run_inhabited`, `draw_encodes_run_of_accepted`).  Given the
encoding draw, the extra hypothesis `draw ∉ runBadEvent` is exactly the
conjunction of the adopted `ConditionalSoundness.BadEventFree`,
`GateDerivedRejection.GoodDerivedTau` and
`GateDerivedRejection.GoodDerivedAlpha` hypotheses, re-spelled as non-membership
in three cylinders.  So this theorem assumes no more than the adopted
`derived_selected_gate_constraints_vanish` does.

WHAT IS NOT PROVED ANYWHERE IN THIS MODULE is the Fiat--Shamir half (B): that
the run's encoding draw is DISTRIBUTED by `jointProbability`.  That reading is
not expressed in Lean here, and combining this theorem with the mass theorem
into "the constraints vanish with probability at least `1 - combinedBound`" is
precisely the unformalized step. -/
theorem derived_selected_gate_constraints_vanish_at_a_good_draw
    (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (vc : Verifier.Config)
    (p : Verifier.Proof) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (x : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List Element) (row : Nat)
    (draw : JointSpace vc.degreeBits)
    (hderiv : DerivedInitial hash e vc p)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p (pre ++ gate :: post)
      s0 sLast x cells gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hcoeffs : ∀ i, i < 2 ^ vc.degreeBits →
      AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) (pre ++ gate :: post)
        (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
          = some (coeffsOf i))
    (hrow : row < 2 ^ vc.degreeBits)
    (hpre : ∀ h ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig vc) h s0.tables row
      = Verifier.zero)
    (hpost : ∀ h ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig vc) h s0.tables row
      = Verifier.zero)
    (hactive : GateRejectionPower.rowFilter (Integrated.gateConfig vc) gate s0.tables row
      ≠ Verifier.zero)
    (U : DrawEncodesRun hash e vc p logTruths gateTruths draw)
    (hgood : draw ∉ runBadEvent hash e vc p (pre ++ gate :: post) s0 logTruths gateTruths
      t pr coeffsOf) :
    ∃ terms, GatesComplete.evaluateUnfiltered gate (AlphaZeroCheck.rowWires s0.tables row)
        (AlphaZeroCheck.rowConstants s0.tables row)
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        (Integrated.gateConfig vc).numSelectors = some terms ∧
      ∀ y ∈ terms, y = Verifier.zero := by
  rw [runBadEvent, not_mem_jointBadEvent] at hgood
  obtain ⟨houter, htau, halpha⟩ := hgood
  have houterGate : draw ∉ laneEvent vc.degreeBits (gateProj vc.degreeBits) 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ gate :: post)
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        (gateAlphaElement hash vc p) s0)
      (ConditionalSoundness.gateLaneOf e vc p gateTruths) 0 := by
    intro hmem
    refine houter ?_
    rw [outerEvent]
    simp only [Finset.mem_union]
    exact Or.inr hmem
  have hfree := badEventFree_of_lane vc.degreeBits draw (gateProj vc.degreeBits) 0
    (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ gate :: post)
      (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
      (gateAlphaElement hash vc p) s0)
    (ConditionalSoundness.gateLaneOf e vc p gateTruths) 0 U.gateDrawn houterGate
  have hgoodTau := good_derived_tau_of_joint hash vc p draw
    (ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) (pre ++ gate :: post)
      (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
      (gateAlphaElement hash vc p) s0.tables) U.tauDrawn htau
  have hgoodAlpha := good_derived_alpha_of_joint hash vc p draw (2 ^ vc.degreeBits) coeffsOf
    U.alphaDrawn halpha row hrow
  exact GateDerivedRejection.derived_selected_gate_constraints_vanish hash pin chain hderiv D
    hacc hfree hgoodTau row hrow (coeffsOf row) (hcoeffs row hrow) hgoodAlpha hpre hpost hactive

/-- (4) WHAT THE LOG LANE'S HALF OF THE SEAM BUYS.  `DrawEncodesRun.logDrawn` is
the one field the composed theorem does not consume; here it is used.  Together
with the log half of the run's good event it delivers the adopted
`ConditionalSoundness.BadEventFree` for the LOG lane, at the adopted compare
value `logCompareOf t pr = NormPolynomial.lift (OuterClaimChain.endpointSum t pr)`
-- the same value the adopted `ConditionalSoundness.Assumptions`
`challengeIndependent` field uses.

The composed conclusion below does not need this (the adopted
`derived_selected_gate_constraints_vanish` consumes only the GATE lane's
`BadEventFree`); the log lane enters `runBadEvent` so that the mass matches the
adopted `ChallengeUnionBound.outerTerm`, and this theorem records that the
corresponding half of the seam is not idle. -/
theorem log_lane_badEventFree_of_good_draw (hash : Hash) (e : Verifier.Engine)
    (vc : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List Element) (draw : JointSpace vc.degreeBits)
    (U : DrawEncodesRun hash e vc p logTruths gateTruths draw)
    (hgood : draw ∉ runBadEvent hash e vc p gates s0 logTruths gateTruths t pr coeffsOf) :
    ConditionalSoundness.BadEventFree 0 (logCompareOf t pr)
      (ConditionalSoundness.logLaneOf e vc p logTruths) := by
  rw [runBadEvent, not_mem_jointBadEvent] at hgood
  obtain ⟨houter, -, -⟩ := hgood
  have houterLog : draw ∉ laneEvent vc.degreeBits (logProj vc.degreeBits) 0
      (logCompareOf t pr) (ConditionalSoundness.logLaneOf e vc p logTruths) 0 := by
    intro hmem
    refine houter ?_
    rw [outerEvent]
    simp only [Finset.mem_union]
    exact Or.inl hmem
  exact badEventFree_of_lane vc.degreeBits draw (logProj vc.degreeBits) 0 (logCompareOf t pr)
    (ConditionalSoundness.logLaneOf e vc p logTruths) 0 U.logDrawn houterLog

set_option maxHeartbeats 1000000 in
/-- (4) **THE COMPOSED STATEMENT, IN ONE PIECE.**

Under the adopted `TranscriptProvenance.DerivedInitial`, the adopted
`GateDerivedRejection.DerivedGateAssumptions`, acceptance of the adopted
`Integrated.verify`, the adopted degree bounds of both outer lanes, and the SEAM
`DrawEncodesRun`:

* the good event -- the complement, in the ONE joint sample space, of the
  disjunction of the three adopted bad sets pulled back to their own coordinates
  -- has mass at least `1 - combinedBound degreeBits quotientDegree degreeBits
  numGateConstraints` under the explicit joint uniform law; AND
* IF the run's draw lies in that good event, THEN the adopted
  `GateDerivedRejection.derived_selected_gate_constraints_vanish` conclusion
  holds: at row `row` the selected gate's evaluator succeeds and every one of
  its constraint terms is zero.

**READ THE TWO CONJUNCTS SEPARATELY.**  NO PROBABILITY IS ATTACHED TO THE
CONCLUSION.  The first conjunct is a counting fact about `JointSpace` and
mentions no gate constraint; the second is an implication whose hypothesis is
membership of one particular draw in the good event, and it mentions no mass.
The statement "the selected gate's constraints vanish with probability at least
`1 - combinedBound`" IS NOT PROVED HERE, and cannot be assembled from these two
conjuncts without the unformalized Fiat--Shamir half (B) -- that the run's
encoding draw is DISTRIBUTED by `jointProbability`.  That sentence appears
nowhere in this module, in Lean or as a hypothesis.

Correspondingly, THIS THEOREM CARRIES NO CRYPTOGRAPHIC HYPOTHESIS.
`DrawEncodesRun` is inhabited for every hash and every accepted run
(`draw_encodes_run_inhabited`, `draw_encodes_run_of_accepted`), so it is a
coordinate statement, not an assumption on the hash.

`combinedBound` EXCLUDES the dominant WHIR/Merkle term and is NOT the system's
soundness error; at the envelope extremes it is about `2^-172.07`, so the
`2^-172` figure has about 0.07 bits of headroom, while the deployed design point
is around 100 bits. -/
theorem composed_gate_constraints_vanish_on_the_joint_space
    (hash : Hash) (pin : Verifier.Pinned) (chain : Nat)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (vc : Verifier.Config)
    (p : Verifier.Proof) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (x : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List Element) (row : Nat)
    (draw : JointSpace vc.degreeBits)
    (hderiv : DerivedInitial hash e vc p)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p (pre ++ gate :: post)
      s0 sLast x cells gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf e vc p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf e vc p gateTruths,
      r.message.length ≤ vc.quotientDegree + 2 ∧ r.truth.length ≤ vc.quotientDegree + 2)
    (hcoeffs : ∀ i, i < 2 ^ vc.degreeBits →
      AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) (pre ++ gate :: post)
        (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
          = some (coeffsOf i))
    (hclen : ∀ i, i < 2 ^ vc.degreeBits → (coeffsOf i).length ≤ vc.numGateConstraints)
    (hrow : row < 2 ^ vc.degreeBits)
    (hpre : ∀ h ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig vc) h s0.tables row
      = Verifier.zero)
    (hpost : ∀ h ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig vc) h s0.tables row
      = Verifier.zero)
    (hactive : GateRejectionPower.rowFilter (Integrated.gateConfig vc) gate s0.tables row
      ≠ Verifier.zero)
    (U : DrawEncodesRun hash e vc p logTruths gateTruths draw) :
    1 - ChallengeUnionBound.combinedBound vc.degreeBits vc.quotientDegree vc.degreeBits
          vc.numGateConstraints
        ≤ jointProbability vc.degreeBits (goodEvent vc.degreeBits
            (runBadEvent hash e vc p (pre ++ gate :: post) s0 logTruths gateTruths t pr
              coeffsOf))
      ∧ (draw ∉ runBadEvent hash e vc p (pre ++ gate :: post) s0 logTruths gateTruths t pr
            coeffsOf →
          ∃ terms, GatesComplete.evaluateUnfiltered gate (AlphaZeroCheck.rowWires s0.tables row)
              (AlphaZeroCheck.rowConstants s0.tables row)
              (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
              (Integrated.gateConfig vc).numSelectors = some terms ∧
            ∀ y ∈ terms, y = Verifier.zero) :=
  ⟨run_good_event_mass_ge hash pin chain e decode vc p (pre ++ gate :: post) s0 logTruths
      gateTruths t pr coeffsOf hacc hlogDeg hgateDeg hclen,
   fun hgood => derived_selected_gate_constraints_vanish_at_a_good_draw hash pin chain e decode
      vc p pre post gate s0 sLast x cells logTruths gateTruths t pr coeffsOf row draw
      hderiv D hacc hcoeffs hrow hpre hpost hactive U hgood⟩

/-! ## 7. The envelope, restated with its warnings

Everything in this section is the adopted `ChallengeUnionBound` arithmetic; it is
restated here only so that the joint statements of sections 5 and 6 carry their
number with them. -/

/-- (5) THE ENVELOPE MASS OF THE GOOD EVENT.  At the envelope extremes
(`degreeBits = 13`, `quotientDegree = 8`, `numGateConstraints = 123`) the good
event of the ONE joint space has mass at least `1 - 2^(-172)`.

`2^-172` IS NOT THE SYSTEM'S SOUNDNESS ERROR.  It omits the WHIR/Merkle term,
which dominates; the deployed design point is around 100 bits, so quoting this
as the wire-v3 soundness error would be wrong by roughly seventy bits. -/
theorem joint_good_event_mass_at_extremes (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hlogLen : logLane.length = 13) (hgateLen : gateLane.length = 13)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ 8 + 2 ∧ r.truth.length ≤ 8 + 2)
    (hlen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) :
    1 - (1 : ℚ) / 2 ^ 172
      ≤ jointProbability 13 (goodEvent 13
          (jointBadEvent 13 logCompare gateCompare logLane gateLane g (2 ^ 13) coeffsOf)) := by
  have h := joint_good_event_mass_ge 13 8 123 logCompare gateCompare logLane gateLane g coeffsOf
    hlogLen hgateLen hlogDeg hgateDeg hlen
  have hnum := ChallengeUnionBound.combined_bound_at_extremes_numeric
  linarith

/-- (5) HOW MUCH HEADROOM THE `2^-172` FIGURE HAS: less than one bit.  The
closed form at the extremes lies between `2^-173` and `2^-172`; numerically it is
about `2^-172.07`, because the two digest-triple terms contribute
`999619 * (ceil(2^256/p) / 2^256)^3` with `999619` about `2^19.93` and the cubed
ratio about `2^-192`.

WHAT THE MARGIN ACTUALLY BUYS, in the same exact rational arithmetic: one extra
gate constraint adds `2^degreeBits * (ceil(2^256/p)/2^256)^3`, about `2^-179`,
so with `degreeBits = 13`, `quotientDegree = 8` the `<= 2^-172` bound still
holds at 124, at 127 and at 128 constraints, and FIRST FAILS at 129; raising
`degreeBits` to 14 breaks it outright (about `2^-171.07` there).  Both are
outside the reviewed envelope regardless: `Verifier.envelope` caps
`numGateConstraints` at 123 and `degreeBits` at 13.

Proved by exact rational arithmetic on Q literals built from
`Arithmetic.modulus` and `2 ^ 256`; no `decide`, no `native_decide`, no floating
point, and no tactic sees `Fintype.card Element`. -/
theorem combined_bound_at_extremes_between_two_powers :
    (1 : ℚ) / 2 ^ 173 ≤ ChallengeUnionBound.combinedBound 13 8 13 123 ∧
      ChallengeUnionBound.combinedBound 13 8 13 123 ≤ (1 : ℚ) / 2 ^ 172 := by
  refine ⟨?_, ChallengeUnionBound.combined_bound_at_extremes_numeric⟩
  rw [ChallengeUnionBound.combined_bound_at_extremes, ChallengeUnionBound.digest_ratio_explicit,
    ChallengeUnionBound.tau_term_explicit]
  norm_num [Arithmetic.modulus]

/-! ## 8. Small examples

No `Finset` over an Element-valued tuple space is ever instantiated at a literal
size, and no `decide` is used on the digest space. -/

/-- With no coupled rounds and no tau coordinates there is exactly one draw: the
gate alpha. -/
theorem draw_card_zero : Fintype.card (Draw 0) = 1 := by
  rw [draw_card]

/-- One coupled round: four draws (log round, gate round, gate alpha, one tau
coordinate). -/
theorem draw_card_one : Fintype.card (Draw 1) = 4 := by
  rw [draw_card]

/-- At `degreeBits = 1` the schedule positions are the source ones: gate alpha at
counter `12` of the prefix digest and the single tau coordinate at counter `15`,
matching the adopted `CommitmentOrder.fixture_gate_challenge_counters`. -/
theorem fixture_schedule_positions :
    schedulePosition 1 Draw.gateAlpha = (0, 12) ∧
      schedulePosition 1 (Draw.gateTau ⟨0, by omega⟩) = (0, 15) ∧
      schedulePosition 1 (Draw.outerLog ⟨0, by omega⟩) = (1, 0) ∧
      schedulePosition 1 (Draw.outerGate ⟨0, by omega⟩) = (1, 3) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The empty pullback is empty, so the good event is everything: no bad set, no
mass. -/
theorem coord_event_empty (d : Nat) (k : Draw d) : coordEvent d k (∅ : Finset Element) = ∅ := by
  ext w
  simp only [mem_coordEvent, Finset.not_mem_empty]

theorem coord_event_empty_mass (d : Nat) (k : Draw d) :
    jointProbability d (coordEvent d k (∅ : Finset Element)) = 0 := by
  rw [coord_event_empty, joint_probability_empty]

/-- A lane with no rounds contributes nothing to the joint bad event. -/
theorem lane_event_nil (d : Nat) (proj : Nat → Draw d) (a b : Element) (k : Nat) :
    laneEvent d proj a b [] k = ∅ := rfl

end Audit.Wire3.JointChallengeSpace
