import Audit.Wire3.JointChallengeSpace

/-!
# SEQUENTIAL CONDITIONING FOR THE OUTER COORDINATES

## The gap this module closes

The adopted `Audit.Wire3.JointChallengeSpace` builds ONE uniform counting space
`JointSpace d := Draw d -> OuterChallenge.DigestTriple` and proves
`joint_union_bound`: the mass of `jointBadEvent` is at most
`ChallengeUnionBound.combinedBound`.  Its own header records the defect that this
module repairs, verbatim: THE OUTER FAMILY IS RUN-RELATIVE.  `laneEvent` recurses
through `OuterRound.evaluate a r.message r.challenge` -- the run's REALIZED
challenge -- and round `k`'s `ConditionalSoundness.roundBadSet` depends on
`r.message`, which is absorbed at round `k`'s own commit
(`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`),
i.e. AFTER the block-0 squeezes and after every round `< k`.  The adopted outer
event is therefore a PREFIX-FROZEN union of cylinders, and, as that header says,
"the honest justification would be sequential conditioning / Fubini over the
rounds, which is NOT proved here".

THIS MODULE PROVES THE SEQUENTIAL CONDITIONING.

## What is proved

1. A GENERAL FINITE-PRODUCT THEOREM, pure combinatorics, no run in sight
   (`walk_union_card_bound`, `walk_union_mass_bound`; textbook `Fin m` form
   `adaptive_union_card_bound`, `adaptive_union_mass_bound`).  For a finite
   alphabet `A`, a finite index type, and a list of DISTINCT coordinates visited
   in order, an ADAPTIVE family of bad sets -- coordinate `k`'s bad set may
   depend on every earlier realized coordinate, hence on a message the adversary
   chooses AFTER seeing them -- with per-coordinate fibre bound `c k`, satisfies
       card E / card (Fin m -> A)  <=  (sum of c k) / card A.
   The proof is the Fubini decomposition: peel the first coordinate, count its
   cylinder exactly, and fibre the rest, using that the remaining event is
   invariant in the peeled coordinate (`invariant_fiber_card`,
   `adaptiveEvent_update_of_not_mem`).  Distinctness of the coordinate list is
   what makes that invariance true and is a hypothesis of the theorem.
   `PrefixDependent` says exactly that `B k` reads only the first `k` entries;
   this is the only sense in which the family is constrained.

2. THE INSTANTIATION FOR THE OUTER LANES (`adaptive_outer_event_mass_le`).  The
   adaptive prover is modelled abstractly by `Lane`: its round message and the
   honest round message are FUNCTIONS OF THE EARLIER REALIZED CHALLENGES, and its
   running claims advance by the adopted `OuterRound.evaluate`.  Round `k`'s bad
   set is the ADOPTED `ConditionalSoundness.roundBadSet` at those claims and that
   message, its cardinality bound is the ADOPTED
   `ConditionalSoundness.round_bad_set_card` (log lane `5`, gate lane
   `quotientDegree + 2`, uniformly over all prefixes), and it is pushed to the
   digest-triple alphabet by the ADOPTED `OuterChallenge.tupleEvent` /
   `fixed_point_set_preimage_bound` fibre count, exactly as
   `JointChallengeSpace.coord_event_mass` does for one coordinate.  The resulting
   mass is `5 * degreeBits * ratio^3` for the log lane and
   `(quotientDegree + 2) * degreeBits * ratio^3` for the gate lane, i.e. together
   the ADOPTED `ChallengeUnionBound.outerTerm degreeBits quotientDegree` -- THE
   SAME NUMBER the prefix-frozen version got.

3. THE JOINT STATEMENT (`adaptive_joint_union_bound`).  On the adopted ONE joint
   space, the mass of "adaptive outer event OR adopted gate tau event OR adopted
   gate alpha event" is at most the adopted `combinedBound`.  The tau and alpha
   families are the adopted ones, reused verbatim: they are indexed by the gate
   wire/constant tables, which the adopted `CommitmentOrder` pins to material
   absorbed BEFORE these squeezes, so a prefix-frozen family is the right model
   for them.  Only the outer family needed repair.

4. THE FROZEN FAMILY IS THE SPECIAL CASE (`frozen_is_adaptive_special_case`).
   The adopted `JointChallengeSpace.laneEvent` -- the union of cylinders over one
   realized run's `ConditionalSoundness.badSets` -- IS the adaptive event of the
   family whose `step` discards the realized value.  Feeding that instance to the
   general theorem gives `frozen_lane_mass_le`, which is the adopted
   `JointChallengeSpace.lane_event_mass_le` specialized to `k = 0` and carrying
   two extra hypotheses the adopted statement does not have (`hinj`, that the
   lane's coordinate projection is injective below `d`, and `rs.length ≤ d`); and
   it gives the adopted `joint_union_bound` itself
   (`joint_union_bound_recovered`), with no appeal to the adopted proofs.

## THE COORDINATE ORDER, AND WHY IT MATCHES THE SOURCE

The outer schedule used here is

    log 0, gate 0, log 1, gate 1, ..., log (degreeBits-1), gate (degreeBits-1)

(`outerCoords`, built from the adopted `JointChallengeSpace.logProj` /
`gateProj`).  The adopted
`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters` pins
BOTH coupled challenges of round `r` to the SAME committed digest -- log at
counter `0`, gate at counter `3` -- and that digest is the commit of round `r`'s
own message, absorbed after every challenge of every round `< r`
(`Verifier.roundStep`, `Transcript.commitRound`).  So a prover on this schedule
may choose round `r`'s log message after seeing all challenges of rounds `< r` OF
BOTH LANES, which is exactly what the real prover can do.  It may in addition
choose round `r`'s GATE message after seeing round `r`'s LOG challenge, which the
real prover CANNOT do, both being squeezed from the same commit.  THE ADVERSARY
MODELLED HERE IS THEREFORE AT LEAST AS STRONG AS THE DEPLOYED ONE, and the bound
covers it.  The per-lane order used in section 5, `proj 0, proj 1, ...`, is the
order the adopted `laneEvent` itself visits.

The counter labels `0` and `3` are DOCUMENTED, NOT DERIVED, for the abstract
`Verifier.Engine` the adopted module quantifies over; this module inherits that
caveat from `JointChallengeSpace.schedule_position_injective` unchanged.

## WHAT IS **NOT** PROVED HERE

* THE LAW IS STILL AN IDEAL UNIFORM LAW WRITTEN DOWN BY HAND.  Everything is
  COUNTING on the adopted explicit finite `JointSpace`, divided by its size.  No
  probability space over hashes or over runs exists in this development.  What
  sequential conditioning buys is that the outer summand no longer needs the
  round bad sets to be constants of the experiment; it does NOT derive the
  product law from anything, and it says NOTHING about Keccak.
* THE FIAT--SHAMIR HALF (B) REMAINS UNFORMALIZED.  The adopted
  `JointChallengeSpace.DrawEncodesRun` is a COORDINATE STATEMENT -- "this point
  of the space carries the run's challenges" -- inhabited for every hash and
  every accepted run, NOT an assumption on the hash.  The reading that THE RUN'S
  ENCODING DRAW IS DISTRIBUTED BY `jointProbability` is not expressed anywhere,
  in Lean or as a hypothesis, here or in the adopted module.  Joining a mass
  statement to a statement about one particular draw into "the constraints vanish
  with probability at least `1 - combinedBound`" is precisely the step this audit
  does not take.
* THE HASH IS NOT MODELLED AS A RANDOM ORACLE.  `Lane.message` is an abstract
  function of the EARLIER CHALLENGES -- which is exactly the shape of a
  Fiat--Shamir adaptive prover -- but nothing here derives that shape from the
  transcript, and nothing here shows the squeezes are fresh given the prefix.
  NO CLAIM OF INDEPENDENCE FROM THE HASH IS MADE ANYWHERE IN THIS MODULE: the
  adopted `CommitmentOrder.separation_fails_for_a_deterministic_hash` shows that
  even the deterministic shadow of (B) is false for a general hash.
* THIS MODULE DOES NOT CONSTRUCT THE `Lane` OF A DEPLOYED PROVER.  The theorems
  quantify over every `Lane` meeting the adopted degree bounds; section 5 shows
  the adopted prefix-frozen family is an instance of the GENERAL ENGINE of §1
  (state `List (Finset Element)`, `frozenBad` / `frozenStep`), NOT an instance of
  `Lane`.  A `Lane`-level frozen comparison -- a `Lane` whose `message` ignores
  its prefix still advances its claims along the DRAW's own coordinates and
  coincides with the adopted `laneEvent` only at a draw satisfying
  `DrawEncodesRun` -- is NOT proved here.  Extraction, the `CommittedTables`
  join, and the adopted `ConditionalSoundness` assumption list are untouched --
  in particular ASSUMPTION 3 (`challengeIndependent`) is a bound on a FREE
  rational `failure` by a sum of a FREE `law`, and nothing here instantiates it.
* WHIR AND MERKLE ARE EXCLUDED, as in every module of this cohort: proximity /
  list decoding, the query-repetition profile and Merkle collision resistance --
  the DOMINANT terms -- appear nowhere.
* NOTHING HERE IS THE SYSTEM'S SOUNDNESS ERROR.  `combinedBound` covers only the
  outer round-agreement, gate tau and gate alpha events.  The `2^-172` figure of
  `ChallengeUnionBound.combined_bound_at_extremes_numeric` is UNCHANGED by this
  module and is STILL NOT the soundness error: the deployed design point is
  around 100 bits, so quoting `2^-172` as the wire-v3 soundness error would be
  wrong by roughly seventy bits.  Sequential conditioning changes WHICH PROVERS
  the outer summand covers, not which events dominate.

## Tactic note

Inherited from the adopted modules: no tactic may see `Fintype.card Element`, no
theorem statement may mention `Finset.univ` on the joint space or on
`DigestTriple`, and no tuple `Finset` is instantiated at a literal arity `>= 2`.
Emptiness of the digest-level bad set of a lane that does not own the coordinate
(`ownsNext = false`) is obtained through the adopted preimage bound
(`laneBad_card_of_inactive`, whose theorem name is kept for stability) rather
than by inspecting the digest space, for exactly that reason.
-/

set_option maxRecDepth 8000

namespace Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The general adaptive (sequential-conditioning) union bound -/

section General

variable {ι A σ : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

open Classical in
/-- THE ADAPTIVE BAD EVENT.  `ks` is the ordered list of coordinates that carry
the adaptive family, `s` is the adversary's state before the first of them, and
`step` advances that state by the REALIZED value of the coordinate just read. -/
noncomputable def adaptiveEvent (bad : σ → Finset A) (step : σ → A → σ) :
    σ → List ι → Finset (ι → A)
  | _, [] => ∅
  | s, k :: ks =>
      Finset.univ.filter fun w => w k ∈ bad s ∨ w ∈ adaptiveEvent bad step (step s (w k)) ks

theorem adaptiveEvent_nil (bad : σ → Finset A) (step : σ → A → σ) (s : σ) :
    adaptiveEvent bad step s ([] : List ι) = ∅ := rfl

theorem mem_adaptiveEvent_cons (bad : σ → Finset A) (step : σ → A → σ) (s : σ) (k : ι)
    (ks : List ι) (w : ι → A) :
    w ∈ adaptiveEvent bad step s (k :: ks) ↔
      (w k ∈ bad s ∨ w ∈ adaptiveEvent bad step (step s (w k)) ks) := by
  show w ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The set of points whose coordinate `k` lies in `S`, everything else free. -/
def coordCylinder (k : ι) (S : Finset A) : Finset (ι → A) :=
  Finset.univ.filter (fun w => w k ∈ S)

theorem mem_coordCylinder (k : ι) (S : Finset A) (w : ι → A) :
    w ∈ coordCylinder k S ↔ w k ∈ S := by
  simp only [coordCylinder, Finset.mem_filter, Finset.mem_univ, true_and]

theorem coordCylinder_eq_piFinset (k : ι) (S : Finset A) :
    coordCylinder k S = Fintype.piFinset (fun j => if j = k then S else Finset.univ) := by
  ext w
  rw [mem_coordCylinder, Fintype.mem_piFinset]
  constructor
  · intro h j
    by_cases hj : j = k
    · subst hj; simpa only [if_pos rfl] using h
    · simp only [if_neg hj, Finset.mem_univ]
  · intro h
    simpa only [if_pos rfl] using h k

/-- (1) THE ONE-COORDINATE CYLINDER COUNT, written multiplicatively so that no
division ever appears on the `Nat` side. -/
theorem coordCylinder_card (k : ι) (S : Finset A) :
    (coordCylinder k S).card * Fintype.card A = S.card * Fintype.card (ι → A) := by
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨k⟩
  rw [coordCylinder_eq_piFinset, Fintype.card_piFinset,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  rw [Finset.prod_congr rfl (fun j hj => by
      rw [if_neg (Finset.ne_of_mem_erase hj), Finset.card_univ]),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
    if_pos rfl, Fintype.card_fun, mul_assoc, ← pow_succ]
  congr 2
  omega

/-- (1) UNIFORM FIBRES.  If a set is invariant under changing coordinate `k`,
each of its `k`-fibres carries exactly a `1 / card A` share of it. -/
theorem invariant_fiber_card (k : ι) (T : Finset (ι → A))
    (hinv : ∀ (w : ι → A) (b : A), Function.update w k b ∈ T ↔ w ∈ T) (a : A) :
    (T.filter (fun w => w k = a)).card * Fintype.card A = T.card := by
  classical
  have hsum : T.card = ∑ b : A, (T.filter (fun w => w k = b)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun w : ι → A => w k)
      (t := (Finset.univ : Finset A)) (fun x _ => Finset.mem_univ _)
  have hconst : ∀ b : A,
      (T.filter (fun w => w k = b)).card = (T.filter (fun w => w k = a)).card := by
    intro b
    have himg : T.filter (fun w => w k = b)
        = (T.filter (fun w => w k = a)).image (fun w => Function.update w k b) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hv, hvk⟩
        refine ⟨Function.update v k a, ⟨(hinv v a).mpr hv, Function.update_same _ _ _⟩, ?_⟩
        rw [Function.update_idem, ← hvk, Function.update_eq_self]
      · rintro ⟨w, ⟨hw, -⟩, rfl⟩
        exact ⟨(hinv w b).mpr hw, Function.update_same _ _ _⟩
    rw [himg]
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    have hxk := (Finset.mem_filter.mp hx).2
    have hyk := (Finset.mem_filter.mp hy).2
    funext j
    by_cases hj : j = k
    · subst hj; rw [hxk, hyk]
    · have hcf := congrFun hxy j
      simpa only [Function.update_noteq hj] using hcf
  rw [hsum, Finset.sum_congr rfl (fun b _ => hconst b), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm]

/-- (1) The adaptive event of a coordinate list does not look at any coordinate
outside that list. -/
theorem adaptiveEvent_update_of_not_mem (bad : σ → Finset A) (step : σ → A → σ) (k : ι) :
    ∀ (ks : List ι), k ∉ ks → ∀ (s : σ) (w : ι → A) (b : A),
      (Function.update w k b ∈ adaptiveEvent bad step s ks ↔ w ∈ adaptiveEvent bad step s ks)
  | [], _, s, w, b => by
      rw [adaptiveEvent_nil]
      simp only [Finset.not_mem_empty]
  | k' :: ks, hk, s, w, b => by
      have hne : k' ≠ k := fun h => hk (by rw [h]; exact List.mem_cons_self _ _)
      have hk' : k ∉ ks := fun h => hk (List.mem_cons_of_mem _ h)
      rw [mem_adaptiveEvent_cons, mem_adaptiveEvent_cons, Function.update_noteq hne]
      exact or_congr Iff.rfl (adaptiveEvent_update_of_not_mem bad step k ks hk' _ w b)

/-- The per-coordinate fibre bounds, stated ALONG THE WALK: `cs` lists the bound
at each coordinate of `ks`, and the bound at coordinate `j` must hold for EVERY
state the adversary can be in after reading the first `j` coordinates. -/
def AdaptiveBounded (bad : σ → Finset A) (step : σ → A → σ) : σ → List Nat → Prop
  | _, [] => True
  | s, c :: cs => (bad s).card ≤ c ∧ ∀ x : A, AdaptiveBounded bad step (step s x) cs

theorem adaptiveBounded_nil (bad : σ → Finset A) (step : σ → A → σ) (s : σ) :
    AdaptiveBounded bad step s ([] : List Nat) := trivial

theorem adaptiveBounded_cons (bad : σ → Finset A) (step : σ → A → σ) (s : σ) (c : Nat)
    (cs : List Nat) :
    AdaptiveBounded bad step s (c :: cs) ↔
      ((bad s).card ≤ c ∧ ∀ x : A, AdaptiveBounded bad step (step s x) cs) := Iff.rfl

/-- (1) **THE SEQUENTIAL UNION BOUND, COUNTING FORM.** -/
theorem walk_union_card_bound (bad : σ → Finset A) (step : σ → A → σ) :
    ∀ (ks : List ι) (cs : List Nat) (s : σ), ks.length = cs.length → ks.Nodup →
      AdaptiveBounded bad step s cs →
        (adaptiveEvent bad step s ks).card * Fintype.card A
          ≤ cs.sum * Fintype.card (ι → A)
  | [], [], s, _, _, _ => by
      rw [adaptiveEvent_nil]
      simp only [Finset.card_empty, Nat.zero_mul, List.sum_nil, Nat.zero_mul, le_refl]
  | [], _ :: _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, hlen, _, _ => by simp at hlen
  | k :: ks, c :: cs, s, hlen, hnd, hb => by
      classical
      rcases Nat.eq_zero_or_pos (Fintype.card A) with hA | hA
      · simp only [hA, Nat.mul_zero, Nat.zero_le]
      have hkks : k ∉ ks := (List.nodup_cons.mp hnd).1
      have hnd' : ks.Nodup := (List.nodup_cons.mp hnd).2
      have hlen' : ks.length = cs.length := by simpa using hlen
      have hG : (Finset.univ.filter
          (fun w : ι → A => w ∈ adaptiveEvent bad step (step s (w k)) ks)).card
            * Fintype.card A ≤ cs.sum * Fintype.card (ι → A) := by
        set G := Finset.univ.filter
          (fun w : ι → A => w ∈ adaptiveEvent bad step (step s (w k)) ks) with hGdef
        have hfib : G.card = ∑ a : A, (G.filter (fun w => w k = a)).card :=
          Finset.card_eq_sum_card_fiberwise (f := fun w : ι → A => w k)
            (t := (Finset.univ : Finset A)) (fun x _ => Finset.mem_univ _)
        have heq : ∀ a : A, G.filter (fun w => w k = a)
            = (adaptiveEvent bad step (step s a) ks).filter (fun w => w k = a) := by
          intro a
          ext w
          simp only [hGdef, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hw, hwk⟩
            exact ⟨by rw [← hwk]; exact hw, hwk⟩
          · rintro ⟨hw, hwk⟩
            exact ⟨by rw [hwk]; exact hw, hwk⟩
        have hfibre : ∀ a : A, (G.filter (fun w => w k = a)).card * Fintype.card A
            = (adaptiveEvent bad step (step s a) ks).card := by
          intro a
          rw [heq a]
          exact invariant_fiber_card k _
            (fun w b => adaptiveEvent_update_of_not_mem bad step k ks hkks (step s a) w b) a
        have hstep : ∀ a : A, (adaptiveEvent bad step (step s a) ks).card * Fintype.card A
            ≤ cs.sum * Fintype.card (ι → A) := fun a =>
          walk_union_card_bound bad step ks cs (step s a) hlen' hnd' (hb.2 a)
        have hmul : (G.card * Fintype.card A) * Fintype.card A
            ≤ (cs.sum * Fintype.card (ι → A)) * Fintype.card A := by
          have h1 : (G.card * Fintype.card A) * Fintype.card A
              = ∑ a : A, ((G.filter (fun w => w k = a)).card * Fintype.card A)
                  * Fintype.card A := by
            rw [hfib, Finset.sum_mul, Finset.sum_mul]
          rw [h1]
          have h2 : ∀ a : A, ((G.filter (fun w => w k = a)).card * Fintype.card A)
              * Fintype.card A ≤ cs.sum * Fintype.card (ι → A) := by
            intro a
            rw [hfibre a]
            exact hstep a
          refine (Finset.sum_le_sum (fun a _ => h2 a)).trans ?_
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
        exact Nat.le_of_mul_le_mul_right hmul hA
      have hHcard : (coordCylinder k (bad s)).card * Fintype.card A
          ≤ c * Fintype.card (ι → A) := by
        rw [coordCylinder_card]
        exact Nat.mul_le_mul_right _ hb.1
      have hsub : adaptiveEvent bad step s (k :: ks) ⊆
          coordCylinder k (bad s) ∪ Finset.univ.filter
            (fun w : ι → A => w ∈ adaptiveEvent bad step (step s (w k)) ks) := by
        intro w hw
        rw [mem_adaptiveEvent_cons] at hw
        rcases hw with h | h
        · exact Finset.mem_union_left _ ((mem_coordCylinder k (bad s) w).mpr h)
        · refine Finset.mem_union_right _ ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h
      have hcard : (adaptiveEvent bad step s (k :: ks)).card
          ≤ (coordCylinder k (bad s)).card + (Finset.univ.filter
            (fun w : ι → A => w ∈ adaptiveEvent bad step (step s (w k)) ks)).card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      calc (adaptiveEvent bad step s (k :: ks)).card * Fintype.card A
          ≤ ((coordCylinder k (bad s)).card + (Finset.univ.filter
              (fun w : ι → A => w ∈ adaptiveEvent bad step (step s (w k)) ks)).card)
                * Fintype.card A := Nat.mul_le_mul_right _ hcard
        _ = (coordCylinder k (bad s)).card * Fintype.card A
              + (Finset.univ.filter
                (fun w : ι → A => w ∈ adaptiveEvent bad step (step s (w k)) ks)).card
                * Fintype.card A := by rw [Nat.add_mul]
        _ ≤ c * Fintype.card (ι → A) + cs.sum * Fintype.card (ι → A) := add_le_add hHcard hG
        _ = (c :: cs).sum * Fintype.card (ι → A) := by rw [List.sum_cons, Nat.add_mul]

/-- The uniform counting law on the explicit finite product space. -/
noncomputable def uniformMass (E : Finset (ι → A)) : ℚ :=
  (E.card : ℚ) / (Fintype.card (ι → A) : ℚ)

/-- (1) **THE SEQUENTIAL UNION BOUND, MASS FORM.** -/
theorem walk_union_mass_bound (bad : σ → Finset A) (step : σ → A → σ)
    (ks : List ι) (cs : List Nat) (s : σ) (hlen : ks.length = cs.length) (hnd : ks.Nodup)
    (hb : AdaptiveBounded bad step s cs) (hA : 0 < Fintype.card A) :
    uniformMass (adaptiveEvent bad step s ks) ≤ (cs.sum : ℚ) / (Fintype.card A : ℚ) := by
  have hcard := walk_union_card_bound bad step ks cs s hlen hnd hb
  have hN : 0 < Fintype.card (ι → A) := by
    rw [Fintype.card_fun]
    exact pow_pos hA _
  have hNQ : (0 : ℚ) < (Fintype.card (ι → A) : ℚ) := by exact_mod_cast hN
  have hAQ : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast hA
  rw [uniformMass, div_le_div_iff hNQ hAQ]
  exact_mod_cast hcard

end General

/-! ## 2. The textbook form: `Fin m` coordinates, prefix-indexed bad sets -/

section FinPrefix

variable {A : Type} [Fintype A] [DecidableEq A]

/-- ADAPTIVITY, STATED AS DEPENDENCE ON THE PREFIX ONLY.  `B k` is the bad set at
coordinate `k`; it may read the coordinates BEFORE `k` (`xs.take k`) and nothing
else.  A family given in the equivalent dependent shape
`B' : (k : Fin m) → (Fin k → A) → Finset A` becomes such a `B` by reading the
first `k` entries of the list. -/
def PrefixDependent (B : Nat → List A → Finset A) : Prop :=
  ∀ (k : Nat) (xs ys : List A), xs.take k = ys.take k → B k xs = B k ys

open Classical in
/-- THE EVENT `E = {w | ∃ k, w k ∈ B k (w restricted to < k)}`, with the prefix
presented as the initial segment of the realized draw. -/
noncomputable def prefixEvent (m : Nat) (B : Nat → List A → Finset A) : Finset (Fin m → A) :=
  Finset.univ.filter (fun w => ∃ k : Fin m, w k ∈ B k.val (List.ofFn w))

theorem mem_prefixEvent (m : Nat) (B : Nat → List A → Finset A) (w : Fin m → A) :
    w ∈ prefixEvent m B ↔ ∃ k : Fin m, w k ∈ B k.val (List.ofFn w) := by
  show w ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The coordinates `j, j+1, …` of `Fin m`, `n` of them, in increasing order. -/
def tailCoords (m : Nat) : Nat → Nat → List (Fin m)
  | _, 0 => []
  | j, n + 1 => if h : j < m then (⟨j, h⟩ : Fin m) :: tailCoords m (j + 1) n else []

/-- The matching list of per-coordinate fibre bounds. -/
def tailBounds (c : Nat → Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | j, n + 1 => c j :: tailBounds c (j + 1) n

theorem mem_tailCoords (m : Nat) : ∀ (n j : Nat) (x : Fin m), x ∈ tailCoords m j n → j ≤ x.val
  | 0, j, x, hx => by simp only [tailCoords, List.not_mem_nil] at hx
  | n + 1, j, x, hx => by
      by_cases h : j < m
      · rw [tailCoords, dif_pos h] at hx
        rcases List.mem_cons.mp hx with h1 | h1
        · rw [h1]
        · exact Nat.le_of_succ_le (mem_tailCoords m n (j + 1) x h1)
      · rw [tailCoords, dif_neg h] at hx
        simp only [List.not_mem_nil] at hx

theorem tailCoords_nodup (m : Nat) : ∀ (n j : Nat), (tailCoords m j n).Nodup
  | 0, _ => by simp only [tailCoords, List.nodup_nil]
  | n + 1, j => by
      by_cases h : j < m
      · rw [tailCoords, dif_pos h]
        refine List.nodup_cons.mpr ⟨?_, tailCoords_nodup m n (j + 1)⟩
        intro hmem
        have h2 : j + 1 ≤ j := mem_tailCoords m n (j + 1) _ hmem
        omega
      · rw [tailCoords, dif_neg h]
        exact List.nodup_nil

theorem tailCoords_length (m : Nat) : ∀ (n j : Nat), j + n ≤ m → (tailCoords m j n).length = n
  | 0, _, _ => by simp only [tailCoords, List.length_nil]
  | n + 1, j, h => by
      have hj : j < m := by omega
      rw [tailCoords, dif_pos hj, List.length_cons, tailCoords_length m n (j + 1) (by omega)]

theorem tailBounds_length (c : Nat → Nat) : ∀ (n j : Nat), (tailBounds c j n).length = n
  | 0, _ => rfl
  | n + 1, j => by rw [tailBounds, List.length_cons, tailBounds_length c n (j + 1)]

theorem tailBounds_sum (c : Nat → Nat) :
    ∀ (n j : Nat), (tailBounds c j n).sum = ∑ i ∈ Finset.range n, c (j + i)
  | 0, _ => by simp only [tailBounds, List.sum_nil, Finset.range_zero, Finset.sum_empty]
  | n + 1, j => by
      rw [tailBounds, List.sum_cons, tailBounds_sum c n (j + 1), Finset.sum_range_succ']
      have hcong : ∀ i ∈ Finset.range n, c (j + 1 + i) = c (j + (i + 1)) := by
        intro i _
        congr 1
        omega
      rw [Finset.sum_congr rfl hcong]
      simp only [Nat.add_zero]
      omega

/-- The adversary's state is the prefix of the draw it has already seen. -/
def prefixStep (s : List A) (x : A) : List A := s ++ [x]

/-- The bad set the prefix-indexed family assigns to that state. -/
noncomputable def prefixBad (m : Nat) (B : Nat → List A → Finset A) (s : List A) : Finset A :=
  if s.length < m then B s.length s else ∅

theorem prefixBad_card_le (m : Nat) (B : Nat → List A → Finset A) (c : Nat → Nat)
    (hc : ∀ k xs, (B k xs).card ≤ c k) (s : List A) :
    (prefixBad m B s).card ≤ c s.length := by
  unfold prefixBad
  split
  · exact hc _ _
  · simp only [Finset.card_empty, Nat.zero_le]

theorem prefix_adaptiveBounded (m : Nat) (B : Nat → List A → Finset A) (c : Nat → Nat)
    (hc : ∀ k xs, (B k xs).card ≤ c k) :
    ∀ (n j : Nat) (s : List A), s.length = j →
      AdaptiveBounded (prefixBad m B) prefixStep s (tailBounds c j n)
  | 0, _, _, _ => by
      show AdaptiveBounded (prefixBad m B) prefixStep _ []
      trivial
  | n + 1, j, s, hs => by
      refine ⟨?_, ?_⟩
      · have h := prefixBad_card_le m B c hc s
        rwa [hs] at h
      · intro x
        exact prefix_adaptiveBounded m B c hc n (j + 1) (prefixStep s x)
          (by simp only [prefixStep, List.length_append, List.length_singleton, hs])

/-- (2) SEQUENTIAL WALK = PREFIX EVENT.  Walking the coordinates `j, j+1, …` with
the state "the prefix already read" hits the bad set of some coordinate `≥ j`
exactly when the draw is in the prefix-indexed event from `j` on. -/
theorem prefix_walk (m : Nat) (B : Nat → List A → Finset A) (hdep : PrefixDependent B) :
    ∀ (n j : Nat) (w : Fin m → A), j + n = m →
      (w ∈ adaptiveEvent (prefixBad m B) prefixStep ((List.ofFn w).take j) (tailCoords m j n) ↔
        ∃ k : Fin m, j ≤ k.val ∧ w k ∈ B k.val (List.ofFn w))
  | 0, j, w, hj => by
      rw [tailCoords, adaptiveEvent_nil]
      simp only [Finset.not_mem_empty, false_iff, not_exists]
      intro k hk
      exact absurd k.isLt (by omega)
  | n + 1, j, w, hj => by
      have hjm : j < m := by omega
      have hlen : ((List.ofFn w).take j).length = j := by
        rw [List.length_take, List.length_ofFn]
        omega
      have hget : (List.ofFn w)[j]? = some (w ⟨j, hjm⟩) := by
        rw [List.getElem?_ofFn, List.ofFnNthVal, dif_pos hjm]
      have hstep : prefixStep ((List.ofFn w).take j) (w ⟨j, hjm⟩) = (List.ofFn w).take (j + 1) := by
        rw [prefixStep, List.take_succ, hget]
        rfl
      have hbad : prefixBad m B ((List.ofFn w).take j) = B j (List.ofFn w) := by
        rw [prefixBad, hlen, if_pos hjm]
        exact hdep j _ _ (by rw [List.take_take, Nat.min_self])
      rw [tailCoords, dif_pos hjm, mem_adaptiveEvent_cons, hbad, hstep,
        prefix_walk m B hdep n (j + 1) w (by omega)]
      constructor
      · rintro (h | ⟨k, hk1, hk2⟩)
        · exact ⟨⟨j, hjm⟩, le_refl _, h⟩
        · exact ⟨k, by omega, hk2⟩
      · rintro ⟨k, hk1, hk2⟩
        rcases Nat.eq_or_lt_of_le hk1 with h | h
        · left
          have : k = ⟨j, hjm⟩ := Fin.ext h.symm
          rw [this] at hk2
          exact hk2
        · exact Or.inr ⟨k, h, hk2⟩

theorem prefixEvent_eq_adaptiveEvent (m : Nat) (B : Nat → List A → Finset A)
    (hdep : PrefixDependent B) :
    prefixEvent m B = adaptiveEvent (prefixBad m B) prefixStep [] (tailCoords m 0 m) := by
  ext w
  have h := prefix_walk m B hdep m 0 w (by omega)
  rw [List.take_zero] at h
  rw [mem_prefixEvent, h]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Nat.zero_le _, hk⟩
  · rintro ⟨k, -, hk⟩
    exact ⟨k, hk⟩

/-- (2) **THE ADAPTIVE UNION BOUND, COUNTING FORM.**  For an ADAPTIVE family of
bad sets over `m` coordinates -- coordinate `k`'s bad set may depend on every
earlier coordinate, hence on a message the adversary chooses after seeing them --
with per-coordinate fibre bound `c k`, the event "some coordinate lands in its
own bad set" satisfies `card E * card A ≤ (∑ c) * card (Fin m → A)`. -/
theorem adaptive_union_card_bound (m : Nat) (B : Nat → List A → Finset A) (c : Nat → Nat)
    (hdep : PrefixDependent B) (hc : ∀ k xs, (B k xs).card ≤ c k) :
    (prefixEvent m B).card * Fintype.card A
      ≤ (∑ k ∈ Finset.range m, c k) * Fintype.card (Fin m → A) := by
  have hsum : (tailBounds c 0 m).sum = ∑ k ∈ Finset.range m, c k := by
    rw [tailBounds_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.zero_add])
  have h := walk_union_card_bound (prefixBad m B) prefixStep (tailCoords m 0 m)
    (tailBounds c 0 m) [] (by rw [tailCoords_length m m 0 (by omega), tailBounds_length])
    (tailCoords_nodup m m 0) (prefix_adaptiveBounded m B c hc m 0 [] rfl)
  rw [← prefixEvent_eq_adaptiveEvent m B hdep, hsum] at h
  exact h

/-- (2) **THE ADAPTIVE UNION BOUND, MASS FORM.**  `card E / card (Fin m → A) ≤
(∑ k, c k) / card A`: the classical union bound over `m` rounds, with the round
messages allowed to depend on all earlier realized coordinates.  This is the
sequential-conditioning (Fubini) statement; the frozen family is the special
case in which `B k` ignores its prefix. -/
theorem adaptive_union_mass_bound (m : Nat) (B : Nat → List A → Finset A) (c : Nat → Nat)
    (hdep : PrefixDependent B) (hc : ∀ k xs, (B k xs).card ≤ c k) (hA : 0 < Fintype.card A) :
    uniformMass (prefixEvent m B)
      ≤ ((∑ k ∈ Finset.range m, c k : Nat) : ℚ) / (Fintype.card A : ℚ) := by
  have hcard := adaptive_union_card_bound m B c hdep hc
  have hN : 0 < Fintype.card (Fin m → A) := by
    rw [Fintype.card_fun]
    exact pow_pos hA _
  have hNQ : (0 : ℚ) < (Fintype.card (Fin m → A) : ℚ) := by exact_mod_cast hN
  have hAQ : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast hA
  rw [uniformMass, div_le_div_iff hNQ hAQ]
  exact_mod_cast hcard

end FinPrefix

/-! ## 3. The adaptive outer prover -/

/-- ONE OUTER LANE OF AN ADAPTIVE PROVER.  `message` and `truth` are functions of
the challenges the run has ALREADY revealed, in the order they were revealed --
OLDEST FIRST.  `Lane.step` prepends the newly realized challenge to the ARGUMENT
of the previous function, so after two coordinates
`((L.step x).step y).message [] = L.message [x, y]` holds by `rfl`, with the
EARLIER challenge `x` at the HEAD of the list.  This is exactly the Fiat--Shamir
adaptive-prover shape, in which round `k`'s absorbed message may be chosen after
seeing every earlier squeeze.  `claim` and `truthClaim` are the running claims of
the adopted `ConditionalSoundness.claimedRun` / `truthRun` recursions. -/
structure Lane where
  message : List Element → List Element
  truth : List Element → List Element
  claim : Element
  truthClaim : Element
  /-- phase bit of the interleaved walk [log 0, gate 0, log 1, gate 1, …]:
  `ownsNext = true` means this lane owns the next coordinate; the log lane starts
  with `true` (even coordinates), the gate lane with `false` (odd coordinates).
  It does NOT disable a lane: the gate lane's adopted `roundBadSet` appears at
  every gate coordinate (see `Lane.badSet`). -/
  ownsNext : Bool

/-- THE ROUND BAD SET OF THE LANE, at its own coordinates: the ADOPTED
`ConditionalSoundness.roundBadSet` of the two running claims and the message the
prover chose after the prefix it has seen.  Empty at the other lane's
coordinates. -/
noncomputable def Lane.badSet (L : Lane) : Finset Element :=
  if L.ownsNext then
    ConditionalSoundness.roundBadSet L.claim L.truthClaim
      ⟨L.message [], L.truth [], 0⟩
  else ∅

/-- ONE SCHEDULED COORDINATE LATER.  Both lanes absorb EVERY realized challenge
(so each lane's later messages may depend on the other lane's earlier
challenges); the running claims advance by the ADOPTED `OuterRound.evaluate` only
at this lane's own coordinates. -/
def Lane.step (L : Lane) (x : Element) : Lane where
  message := fun xs => L.message (x :: xs)
  truth := fun xs => L.truth (x :: xs)
  claim := if L.ownsNext then OuterRound.evaluate L.claim (L.message []) x else L.claim
  truthClaim := if L.ownsNext then OuterRound.evaluate L.truthClaim (L.truth []) x else L.truthClaim
  ownsNext := !L.ownsNext

namespace Lane
theorem step_active (L : Lane) (x : Element) : (L.step x).ownsNext = !L.ownsNext := rfl
end Lane

/-- THE ADOPTED DEGREE BOUND, uniform over the prover's choices: whatever prefix
it has seen, its round message and the honest round message have at most `b`
coefficients.  For the log lane the adopted value is `5`
(`ConditionalSoundness.lane_degree_bounds`), for the gate lane
`quotientDegree + 2`. -/
def Lane.Bounded (L : Lane) (b : Nat) : Prop :=
  ∀ xs, (L.message xs).length ≤ b ∧ (L.truth xs).length ≤ b

namespace Lane
theorem bounded_step (L : Lane) (b : Nat) (h : L.Bounded b) (x : Element) :
    (L.step x).Bounded b := fun xs => h (x :: xs)
end Lane

namespace Lane
/-- (3) THE ADOPTED PER-ROUND CARDINALITY BOUND, reused verbatim: whatever the
prefix, the round bad set has at most `b` points
(`ConditionalSoundness.round_bad_set_card`). -/
theorem badSet_card_le (L : Lane) (b : Nat) (h : L.Bounded b) : L.badSet.card ≤ b := by
  unfold Lane.badSet
  split
  · exact ConditionalSoundness.round_bad_set_card L.claim L.truthClaim
      ⟨L.message [], L.truth [], 0⟩ b (h []).1 (h []).2
  · simp only [Finset.card_empty, Nat.zero_le]
end Lane

namespace Lane
theorem badSet_of_inactive (L : Lane) (h : L.ownsNext = false) :
    L.badSet = (∅ : Finset Element) := by
  rw [Lane.badSet, if_neg (by rw [h]; exact Bool.false_ne_true)]
end Lane

/-- THE LANE'S BAD SET ON THE DIGEST-TRIPLE ALPHABET, through the ADOPTED
`OuterChallenge.reduceTriple` pullback `OuterChallenge.tupleEvent`. -/
noncomputable def laneBad (L : Lane) : Finset OuterChallenge.DigestTriple :=
  OuterChallenge.tupleEvent L.badSet

/-- The state transition on the digest-triple alphabet: the lane absorbs the
REDUCTION of the digest triple actually drawn at the coordinate. -/
noncomputable def laneStep (L : Lane) (ds : OuterChallenge.DigestTriple) : Lane :=
  L.step (OuterChallenge.reduceTriple ds)

theorem laneStep_active (L : Lane) (ds : OuterChallenge.DigestTriple) :
    (laneStep L ds).ownsNext = !L.ownsNext := rfl

theorem laneStep_bounded (L : Lane) (b : Nat) (h : L.Bounded b)
    (ds : OuterChallenge.DigestTriple) : (laneStep L ds).Bounded b :=
  Lane.bounded_step L b h _

/-- (3) THE ADOPTED FIBRE BOUND, reused: at most `⌈2^256/p⌉^3` digest triples per
bad field point (`OuterChallenge.fixed_point_set_preimage_bound`). -/
theorem laneBad_card_le (L : Lane) (b : Nat) (h : L.Bounded b) :
    (laneBad L).card ≤ b * OuterChallenge.fiberCeiling ^ 3 :=
  (OuterChallenge.fixed_point_set_preimage_bound _).trans
    (Nat.mul_le_mul_right _ (L.badSet_card_le b h))

/-- (3) At the OTHER lane's coordinates this lane contributes nothing.  Proved
through the adopted preimage bound rather than by inspecting the digest space, so
that no tactic ever elaborates `Finset.univ` on `DigestTriple`. -/
theorem laneBad_card_of_inactive (L : Lane) (h : L.ownsNext = false) : (laneBad L).card ≤ 0 := by
  have hb : L.badSet = (∅ : Finset Element) := L.badSet_of_inactive h
  have hbound := OuterChallenge.fixed_point_set_preimage_bound L.badSet
  rw [hb, Finset.card_empty, Nat.zero_mul] at hbound
  show (OuterChallenge.tupleEvent L.badSet).card ≤ 0
  rw [hb]
  exact hbound

/-- Fibre bounds for a lane whose rounds sit at the EVEN coordinates of the
interleaved schedule (the log lane). -/
def altBounds (b : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => b :: 0 :: altBounds b n

/-- Fibre bounds for a lane whose rounds sit at the ODD coordinates (the gate
lane). -/
def coBounds (b : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: b :: coBounds b n

theorem altBounds_length (b : Nat) : ∀ n, (altBounds b n).length = 2 * n
  | 0 => rfl
  | n + 1 => by rw [altBounds, List.length_cons, List.length_cons, altBounds_length b n]; omega

theorem coBounds_length (b : Nat) : ∀ n, (coBounds b n).length = 2 * n
  | 0 => rfl
  | n + 1 => by rw [coBounds, List.length_cons, List.length_cons, coBounds_length b n]; omega

theorem altBounds_sum (b : Nat) : ∀ n, (altBounds b n).sum = b * n
  | 0 => by simp only [altBounds, List.sum_nil, Nat.mul_zero]
  | n + 1 => by
      rw [altBounds, List.sum_cons, List.sum_cons, altBounds_sum b n, Nat.mul_succ]
      omega

theorem coBounds_sum (b : Nat) : ∀ n, (coBounds b n).sum = b * n
  | 0 => by simp only [coBounds, List.sum_nil, Nat.mul_zero]
  | n + 1 => by
      rw [coBounds, List.sum_cons, List.sum_cons, coBounds_sum b n, Nat.mul_succ]
      omega

/-- (3) THE FIBRE BOUNDS HOLD ALONG EVERY WALK, for a lane that owns the even
coordinates: at its own rounds the adopted per-round bound applies whatever the
prover chose after the prefix, and at the other lane's coordinates its bad set
is empty. -/
theorem adaptiveBounded_alt (b : Nat) : ∀ (n : Nat) (L : Lane), L.Bounded b → L.ownsNext = true →
    AdaptiveBounded laneBad laneStep L (altBounds (b * OuterChallenge.fiberCeiling ^ 3) n)
  | 0, _, _, _ => trivial
  | n + 1, L, hb, ha => by
      refine ⟨laneBad_card_le L b hb, fun x => ⟨?_, fun y => ?_⟩⟩
      · have hoff : (laneStep L x).ownsNext = false := by rw [laneStep_active, ha]; rfl
        exact laneBad_card_of_inactive _ hoff
      · have hon : (laneStep (laneStep L x) y).ownsNext = true := by
          rw [laneStep_active, laneStep_active, ha]; rfl
        exact adaptiveBounded_alt b n _ (laneStep_bounded _ b (laneStep_bounded L b hb x) y) hon

/-- (3) The same for a lane that owns the odd coordinates. -/
theorem adaptiveBounded_co (b : Nat) : ∀ (n : Nat) (L : Lane), L.Bounded b → L.ownsNext = false →
    AdaptiveBounded laneBad laneStep L (coBounds (b * OuterChallenge.fiberCeiling ^ 3) n)
  | 0, _, _, _ => trivial
  | n + 1, L, hb, ha => by
      refine ⟨?_, fun x => ⟨?_, fun y => ?_⟩⟩
      · exact laneBad_card_of_inactive L ha
      · exact laneBad_card_le _ b (laneStep_bounded L b hb x)
      · have hoff : (laneStep (laneStep L x) y).ownsNext = false := by
          rw [laneStep_active, laneStep_active, ha]; rfl
        exact adaptiveBounded_co b n _ (laneStep_bounded _ b (laneStep_bounded L b hb x) y) hoff

/-! ### The interleaved coordinate schedule

`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`
pins BOTH coupled-round challenges of round `r` to the SAME committed digest --
the log challenge at counter `0`, the gate challenge at counter `3` -- and that
digest is the commit of round `r`'s own message, absorbed AFTER every challenge
of every round `< r`.  The schedule below is therefore

    log 0, gate 0, log 1, gate 1, …, log (d-1), gate (d-1)

in source order.  A prover placed on this schedule may choose round `r`'s log
message after seeing all challenges of rounds `< r` (both lanes), which is what
the real prover can do, and it may in addition choose round `r`'s GATE message
after seeing round `r`'s LOG challenge, which the real prover CANNOT do (both are
squeezed from the same commit).  The adversary modelled here is therefore at
least as strong as the deployed one. -/

/-- The coordinates of rounds `j, j+1, …`, `n` rounds, log before gate. -/
def roundCoords (d : Nat) : Nat → Nat → List (JointChallengeSpace.Draw d)
  | _, 0 => []
  | j, n + 1 => JointChallengeSpace.logProj d j :: JointChallengeSpace.gateProj d j :: roundCoords d (j + 1) n

/-- THE WHOLE OUTER SCHEDULE of a `degreeBits`-round run. -/
def outerCoords (d : Nat) : List (JointChallengeSpace.Draw d) := roundCoords d 0 d

theorem roundCoords_length (d : Nat) : ∀ (n j : Nat), (roundCoords d j n).length = 2 * n
  | 0, _ => rfl
  | n + 1, j => by
      rw [roundCoords, List.length_cons, List.length_cons, roundCoords_length d n (j + 1)]
      omega

theorem mem_roundCoords (d : Nat) : ∀ (n j : Nat) (x : JointChallengeSpace.Draw d), x ∈ roundCoords d j n →
    ∃ i, j ≤ i ∧ i < j + n ∧ (x = JointChallengeSpace.logProj d i ∨ x = JointChallengeSpace.gateProj d i)
  | 0, _, _, hx => by simp only [roundCoords, List.not_mem_nil] at hx
  | n + 1, j, x, hx => by
      rcases List.mem_cons.mp hx with h | h
      · exact ⟨j, le_refl _, by omega, Or.inl h⟩
      rcases List.mem_cons.mp h with h1 | h1
      · exact ⟨j, le_refl _, by omega, Or.inr h1⟩
      obtain ⟨i, hi1, hi2, hi3⟩ := mem_roundCoords d n (j + 1) x h1
      exact ⟨i, by omega, by omega, hi3⟩

theorem log_ne_gate (d i j : Nat) (hi : i < d) (hj : j < d) : JointChallengeSpace.logProj d i ≠ JointChallengeSpace.gateProj d j := by
  rw [JointChallengeSpace.logProj_apply d i hi, JointChallengeSpace.gateProj_apply d j hj]
  exact fun h => JointChallengeSpace.Draw.noConfusion h

theorem log_ne_log (d i j : Nat) (hi : i < d) (hj : j < d) (h : i ≠ j) :
    JointChallengeSpace.logProj d i ≠ JointChallengeSpace.logProj d j := by
  rw [JointChallengeSpace.logProj_apply d i hi, JointChallengeSpace.logProj_apply d j hj]
  intro heq
  exact h (congrArg Fin.val (JointChallengeSpace.Draw.outerLog.inj heq))

theorem gate_ne_gate (d i j : Nat) (hi : i < d) (hj : j < d) (h : i ≠ j) :
    JointChallengeSpace.gateProj d i ≠ JointChallengeSpace.gateProj d j := by
  rw [JointChallengeSpace.gateProj_apply d i hi, JointChallengeSpace.gateProj_apply d j hj]
  intro heq
  exact h (congrArg Fin.val (JointChallengeSpace.Draw.outerGate.inj heq))

/-- (3) THE SCHEDULE VISITS EACH COORDINATE ONCE -- the hypothesis the sequential
bound needs, and the reason no coordinate is double-counted. -/
theorem roundCoords_nodup (d : Nat) : ∀ (n j : Nat), j + n ≤ d → (roundCoords d j n).Nodup
  | 0, _, _ => List.nodup_nil
  | n + 1, j, h => by
      have hj : j < d := by omega
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, roundCoords_nodup d n (j + 1)
        (by omega)⟩⟩
      · intro hmem
        rcases List.mem_cons.mp hmem with h1 | h1
        · exact log_ne_gate d j j hj hj h1
        · obtain ⟨i, hi1, hi2, hi3⟩ := mem_roundCoords d n (j + 1) _ h1
          have hid : i < d := by omega
          rcases hi3 with h2 | h2
          · exact log_ne_log d j i hj hid (by omega) h2
          · exact log_ne_gate d j i hj hid h2
      · intro hmem
        obtain ⟨i, hi1, hi2, hi3⟩ := mem_roundCoords d n (j + 1) _ hmem
        have hid : i < d := by omega
        rcases hi3 with h2 | h2
        · exact (log_ne_gate d i j hid hj h2.symm).elim
        · exact gate_ne_gate d j i hj hid (by omega) h2

theorem outerCoords_nodup (d : Nat) : (outerCoords d).Nodup := roundCoords_nodup d d 0 (by omega)

theorem outerCoords_length (d : Nat) : (outerCoords d).length = 2 * d := roundCoords_length d d 0

/-! ### The adaptive outer event and its mass -/

/-- THE ADAPTIVE BAD EVENT OF ONE OUTER LANE, on the joint sample space of the
adopted `JointChallengeSpace`. -/
noncomputable def adaptiveLaneEvent (d : Nat) (L : Lane) : Finset (JointChallengeSpace.JointSpace d) :=
  adaptiveEvent laneBad laneStep L (outerCoords d)

theorem jointProbability_eq_uniformMass (d : Nat) (E : Finset (JointChallengeSpace.JointSpace d)) :
    JointChallengeSpace.jointProbability d E = uniformMass E := rfl

theorem digest_card_pos : 0 < Fintype.card OuterChallenge.DigestTriple :=
  JointChallengeSpace.digest_triple_card_pos

/-- (3) THE MASS OF ONE ADAPTIVE LANE.  With the adopted degree bound `b` holding
at EVERY prefix, the joint mass of "some round of this lane agrees" is at most
`b * degreeBits * (⌈2^256/p⌉ / 2^256)^3` -- the SAME number the prefix-frozen
`JointChallengeSpace.lane_event_mass_le` gets, now for a prover whose round
messages may depend on all earlier realized challenges. -/
theorem adaptive_lane_mass_le (d b : Nat) (L : Lane) (hb : L.Bounded b) (ha : L.ownsNext = true) :
    JointChallengeSpace.jointProbability d (adaptiveLaneEvent d L)
      ≤ ((b * d : Nat) : ℚ)
        * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  have h := walk_union_mass_bound laneBad laneStep (outerCoords d)
    (altBounds (b * OuterChallenge.fiberCeiling ^ 3) d) L
    (by rw [outerCoords_length, altBounds_length]) (outerCoords_nodup d)
    (adaptiveBounded_alt b d L hb ha) digest_card_pos
  rw [jointProbability_eq_uniformMass, adaptiveLaneEvent]
  refine h.trans (le_of_eq ?_)
  rw [altBounds_sum, OuterChallenge.digest_tuple_cardinality]
  push_cast
  ring

/-- (3) The same for a lane whose rounds sit at the odd coordinates. -/
theorem adaptive_lane_mass_le_odd (d b : Nat) (L : Lane) (hb : L.Bounded b)
    (ha : L.ownsNext = false) :
    JointChallengeSpace.jointProbability d (adaptiveLaneEvent d L)
      ≤ ((b * d : Nat) : ℚ)
        * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  have h := walk_union_mass_bound laneBad laneStep (outerCoords d)
    (coBounds (b * OuterChallenge.fiberCeiling ^ 3) d) L
    (by rw [outerCoords_length, coBounds_length]) (outerCoords_nodup d)
    (adaptiveBounded_co b d L hb ha) digest_card_pos
  rw [jointProbability_eq_uniformMass, adaptiveLaneEvent]
  refine h.trans (le_of_eq ?_)
  rw [coBounds_sum, OuterChallenge.digest_tuple_cardinality]
  push_cast
  ring

/-- THE ADAPTIVE OUTER EVENT: some coupled round of either lane agrees, for a
prover that chooses each round's message after seeing every earlier challenge. -/
noncomputable def adaptiveOuterEvent (d : Nat) (logLane gateLane : Lane) :
    Finset (JointChallengeSpace.JointSpace d) :=
  adaptiveLaneEvent d logLane ∪ adaptiveLaneEvent d gateLane

/-- (3) **THE ADAPTIVE OUTER MASS IS THE ADOPTED `outerTerm`.**  Sequential
conditioning over the interleaved schedule gives the ADAPTIVE outer event exactly
the number the prefix-frozen version got: `5 * degreeBits` for the log lane plus
`(quotientDegree + 2) * degreeBits` for the gate lane, times the cubed digest
ratio.

`hlogOwns` / `hgateOwns` fix the phase bit of the interleaved walk
[log 0, gate 0, log 1, gate 1, …]: `ownsNext = true` means this lane owns the
next coordinate; the log lane starts with `true` (even coordinates), the gate
lane with `false` (odd coordinates).  It does NOT disable a lane: the gate
lane's adopted `roundBadSet` appears at every gate coordinate (see
`Lane.badSet`). -/
theorem adaptive_outer_event_mass_le (d q : Nat) (logLane gateLane : Lane)
    (hlog : logLane.Bounded 5) (hlogOwns : logLane.ownsNext = true)
    (hgate : gateLane.Bounded (q + 2)) (hgateOwns : gateLane.ownsNext = false) :
    JointChallengeSpace.jointProbability d (adaptiveOuterEvent d logLane gateLane)
      ≤ ChallengeUnionBound.outerTerm d q := by
  have h1 := adaptive_lane_mass_le d 5 logLane hlog hlogOwns
  have h2 := adaptive_lane_mass_le_odd d (q + 2) gateLane hgate hgateOwns
  refine (JointChallengeSpace.joint_probability_union_le d _ _).trans ?_
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  unfold ChallengeUnionBound.outerTerm
  push_cast
  ring

/-! ## 4. The genuine joint union bound, with an ADAPTIVE outer family

The tau and alpha families are the adopted ones and are reused verbatim: they
are indexed by the gate wire/constant tables, which the adopted
`CommitmentOrder` pins to material absorbed BEFORE any of these squeezes, so for
them a prefix-frozen family is the right model.  Only the outer family is
run-relative, and only it is replaced by its adaptive version here. -/

/-- THE DISJUNCTION EVENT WITH AN ADAPTIVE OUTER FAMILY: some coupled round of
either lane agrees for a prover whose round messages may depend on every earlier
realized challenge, OR the gate tau column lands in the adopted zero-check bad
set, OR the gate alpha lands in the adopted union of the per-row alpha bad
sets. -/
noncomputable def adaptiveJointBadEvent (d : Nat) (logLane gateLane : Lane) (g : Nat → Element)
    (rows : Nat) (coeffsOf : Nat → List Element) : Finset (JointChallengeSpace.JointSpace d) :=
  adaptiveOuterEvent d logLane gateLane ∪ JointChallengeSpace.tauBadEvent d g ∪
    JointChallengeSpace.alphaBadEvent d rows coeffsOf

theorem mem_adaptiveJointBadEvent (d : Nat) (logLane gateLane : Lane) (g : Nat → Element)
    (rows : Nat) (coeffsOf : Nat → List Element) (w : JointChallengeSpace.JointSpace d) :
    w ∈ adaptiveJointBadEvent d logLane gateLane g rows coeffsOf ↔
      (w ∈ adaptiveOuterEvent d logLane gateLane ∨ w ∈ JointChallengeSpace.tauBadEvent d g ∨
        w ∈ JointChallengeSpace.alphaBadEvent d rows coeffsOf) := by
  simp only [adaptiveJointBadEvent, Finset.mem_union, or_assoc]

/-- (4) A draw avoids the adaptive disjunction exactly when it avoids all three
pullbacks.  Stated with `∉` rather than through `Finset.univ`, as the adopted
`JointChallengeSpace.not_mem_jointBadEvent` is. -/
theorem not_mem_adaptiveJointBadEvent (d : Nat) (logLane gateLane : Lane) (g : Nat → Element)
    (rows : Nat) (coeffsOf : Nat → List Element) (w : JointChallengeSpace.JointSpace d) :
    w ∉ adaptiveJointBadEvent d logLane gateLane g rows coeffsOf ↔
      (w ∉ adaptiveOuterEvent d logLane gateLane ∧ w ∉ JointChallengeSpace.tauBadEvent d g ∧
        w ∉ JointChallengeSpace.alphaBadEvent d rows coeffsOf) := by
  rw [mem_adaptiveJointBadEvent, not_or, not_or]

/-- (4) **THE JOINT UNION BOUND FOR AN ADAPTIVE PROVER.**  On the adopted ONE
joint sample space, under the adopted uniform counting law, the mass of the
disjunction of

* the ADAPTIVE outer coupled-round event (round messages chosen after every
  earlier realized challenge, on the interleaved log/gate schedule),
* the adopted gate tau zero-check event, and
* the adopted gate alpha event

is at most the adopted `ChallengeUnionBound.combinedBound` -- the SAME number the
prefix-frozen `JointChallengeSpace.joint_union_bound` gets.  Sequential
conditioning is what licenses the outer summand; it is proved, not assumed.

`hlogOwns` / `hgateOwns` fix the phase bit of the interleaved walk
[log 0, gate 0, log 1, gate 1, …]: `ownsNext = true` means this lane owns the
next coordinate; the log lane starts with `true` (even coordinates), the gate
lane with `false` (odd coordinates).  It does NOT disable a lane: the gate
lane's adopted `roundBadSet` appears at every gate coordinate (see
`Lane.badSet`). -/
theorem adaptive_joint_union_bound (d q constraints : Nat) (logLane gateLane : Lane)
    (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hlog : logLane.Bounded 5) (hlogOwns : logLane.ownsNext = true)
    (hgate : gateLane.Bounded (q + 2)) (hgateOwns : gateLane.ownsNext = false)
    (hlen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    JointChallengeSpace.jointProbability d
        (adaptiveJointBadEvent d logLane gateLane g (2 ^ d) coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints := by
  have h1 := adaptive_outer_event_mass_le d q logLane gateLane hlog hlogOwns hgate hgateOwns
  have h2 := JointChallengeSpace.tau_bad_event_mass_le d g
  have h3 := JointChallengeSpace.alpha_bad_event_mass_le d (2 ^ d) constraints coeffsOf hlen
  unfold adaptiveJointBadEvent ChallengeUnionBound.combinedBound
  refine (JointChallengeSpace.joint_probability_union_le d _ _).trans ?_
  exact add_le_add ((JointChallengeSpace.joint_probability_union_le d _ _).trans
    (add_le_add h1 h2)) h3

/-- (4) THE COMPLEMENT FORM: under the explicit joint uniform law the good event
of the ADAPTIVE disjunction has mass at least `1 - combinedBound`. -/
theorem adaptive_joint_good_event_mass_ge (d q constraints : Nat) (logLane gateLane : Lane)
    (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hlog : logLane.Bounded 5) (hlogOwns : logLane.ownsNext = true)
    (hgate : gateLane.Bounded (q + 2)) (hgateOwns : gateLane.ownsNext = false)
    (hlen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    1 - ChallengeUnionBound.combinedBound d q d constraints
      ≤ JointChallengeSpace.jointProbability d (JointChallengeSpace.goodEvent d
          (adaptiveJointBadEvent d logLane gateLane g (2 ^ d) coeffsOf)) := by
  have h := adaptive_joint_union_bound d q constraints logLane gateLane g coeffsOf hlog
    hlogOwns hgate hgateOwns hlen
  rw [JointChallengeSpace.goodEvent, JointChallengeSpace.joint_probability_compl]
  linarith

/-! ## 5. The prefix-frozen family is the special case -/

/-- THE FROZEN FAMILY.  Its state is the list of bad sets already computed along
one realized run -- exactly the adopted `ConditionalSoundness.badSets` -- and its
`step` DISCARDS the realized value.  A family that ignores its prefix is a family
of this shape. -/
noncomputable def frozenBad : List (Finset Element) → Finset OuterChallenge.DigestTriple
  | [] => ∅
  | S :: _ => OuterChallenge.tupleEvent S

/-- The frozen step throws the realized challenge away: this is what
"prefix-frozen" means. -/
def frozenStep (l : List (Finset Element)) (_ : OuterChallenge.DigestTriple) :
    List (Finset Element) := l.tail

/-- The coordinates of one lane, `n` of them, in the order the adopted
`JointChallengeSpace.laneEvent` visits them. -/
def projCoords (d : Nat) (proj : Nat → JointChallengeSpace.Draw d) :
    Nat → Nat → List (JointChallengeSpace.Draw d)
  | _, 0 => []
  | k, n + 1 => proj k :: projCoords d proj (k + 1) n

theorem projCoords_length (d : Nat) (proj : Nat → JointChallengeSpace.Draw d) :
    ∀ (n k : Nat), (projCoords d proj k n).length = n
  | 0, _ => rfl
  | n + 1, k => by rw [projCoords, List.length_cons, projCoords_length d proj n (k + 1)]

theorem mem_projCoords (d : Nat) (proj : Nat → JointChallengeSpace.Draw d) :
    ∀ (n k : Nat) (x : JointChallengeSpace.Draw d), x ∈ projCoords d proj k n →
      ∃ i, k ≤ i ∧ i < k + n ∧ x = proj i
  | 0, _, _, hx => by simp only [projCoords, List.not_mem_nil] at hx
  | n + 1, k, x, hx => by
      rcases List.mem_cons.mp hx with h | h
      · exact ⟨k, le_refl _, by omega, h⟩
      · obtain ⟨i, hi1, hi2, hi3⟩ := mem_projCoords d proj n (k + 1) x h
        exact ⟨i, by omega, by omega, hi3⟩

theorem projCoords_nodup (d : Nat) (proj : Nat → JointChallengeSpace.Draw d)
    (hinj : ∀ i j, i < d → j < d → proj i = proj j → i = j) :
    ∀ (n k : Nat), k + n ≤ d → (projCoords d proj k n).Nodup
  | 0, _, _ => List.nodup_nil
  | n + 1, k, h => by
      refine List.nodup_cons.mpr ⟨?_, projCoords_nodup d proj hinj n (k + 1) (by omega)⟩
      intro hmem
      obtain ⟨i, hi1, hi2, hi3⟩ := mem_projCoords d proj n (k + 1) _ hmem
      have := hinj k i (by omega) (by omega) hi3
      omega

/-- (5) **THE PREFIX-FROZEN LANE EVENT IS AN ADAPTIVE EVENT.**  The adopted
`JointChallengeSpace.laneEvent` -- the union of cylinders over the bad sets of
ONE realized run, which is what the adopted `ConditionalSoundness.badSets`
recursion produces -- is literally the adaptive event of the family that IGNORES
its prefix.  So the frozen construction is the special case, and everything
proved above about adaptive families applies to it. -/
theorem frozen_is_adaptive_special_case (d : Nat) (proj : Nat → JointChallengeSpace.Draw d) :
    ∀ (a b : Element) (rs : List ConditionalSoundness.LaneRound) (k : Nat),
      JointChallengeSpace.laneEvent d proj a b rs k
        = adaptiveEvent frozenBad frozenStep (ConditionalSoundness.badSets a b rs)
            (projCoords d proj k rs.length)
  | _, _, [], _ => by
      rw [JointChallengeSpace.lane_event_nil]
      simp only [List.length_nil, projCoords, adaptiveEvent_nil]
  | a, b, r :: rs, k => by
      ext w
      rw [List.length_cons, projCoords, ConditionalSoundness.bad_sets_cons,
        mem_adaptiveEvent_cons]
      show w ∈ JointChallengeSpace.coordEvent d (proj k) _ ∪ _ ↔ _
      rw [Finset.mem_union, JointChallengeSpace.mem_coordEvent,
        frozen_is_adaptive_special_case d proj (OuterRound.evaluate a r.message r.challenge)
          (OuterRound.evaluate b r.truth r.challenge) rs (k + 1)]
      exact or_congr (JointChallengeSpace.mem_tupleEvent _ _).symm Iff.rfl

/-- (5) The frozen family's fibre bounds are the ADOPTED per-round digest-triple
counts (`ConditionalSoundness.round_bad_triples_card`). -/
theorem frozen_adaptiveBounded (bound : Nat) :
    ∀ (a b : Element) (rs : List ConditionalSoundness.LaneRound),
      (∀ r ∈ rs, r.message.length ≤ bound ∧ r.truth.length ≤ bound) →
        AdaptiveBounded frozenBad frozenStep (ConditionalSoundness.badSets a b rs)
          (List.replicate rs.length (bound * OuterChallenge.fiberCeiling ^ 3))
  | _, _, [], _ => trivial
  | a, b, r :: rs, hd => by
      have hhead := hd r (List.mem_cons_self _ _)
      rw [List.length_cons, List.replicate_succ, ConditionalSoundness.bad_sets_cons]
      refine ⟨ConditionalSoundness.round_bad_triples_card a b r bound hhead.1 hhead.2, fun _ => ?_⟩
      exact frozen_adaptiveBounded bound (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) rs (fun q hq => hd q (List.mem_cons_of_mem _ hq))

/-- (5) **THE ADOPTED PER-LANE BOUND, RE-DERIVED THROUGH THE SEQUENTIAL
THEOREM.**  Applying the general adaptive bound of §1 to the frozen family gives
the adopted `JointChallengeSpace.lane_event_mass_le` specialized to `k = 0`, with
two hypotheses the adopted statement does not carry: `hinj` (the lane's
coordinate projection is injective below `d`, which is what makes the visited
coordinate list `Nodup`) and `rs.length ≤ d`.  Note that the instance fed to the
engine is the GENERAL ENGINE state `List (Finset Element)` with `frozenBad` /
`frozenStep`, not a `Lane`. -/
theorem frozen_lane_mass_le (d : Nat) (proj : Nat → JointChallengeSpace.Draw d)
    (hinj : ∀ i j, i < d → j < d → proj i = proj j → i = j) (bound : Nat) (a b : Element)
    (rs : List ConditionalSoundness.LaneRound) (hlen : rs.length ≤ d)
    (hd : ∀ r ∈ rs, r.message.length ≤ bound ∧ r.truth.length ≤ bound) :
    JointChallengeSpace.jointProbability d (JointChallengeSpace.laneEvent d proj a b rs 0)
      ≤ ((bound * rs.length : Nat) : ℚ)
        * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  have h := walk_union_mass_bound frozenBad frozenStep (projCoords d proj 0 rs.length)
    (List.replicate rs.length (bound * OuterChallenge.fiberCeiling ^ 3))
    (ConditionalSoundness.badSets a b rs)
    (by rw [projCoords_length, List.length_replicate])
    (projCoords_nodup d proj hinj rs.length 0 (by omega))
    (frozen_adaptiveBounded bound a b rs hd) digest_card_pos
  rw [jointProbability_eq_uniformMass, frozen_is_adaptive_special_case d proj a b rs 0]
  refine h.trans (le_of_eq ?_)
  rw [List.sum_replicate, smul_eq_mul, OuterChallenge.digest_tuple_cardinality]
  push_cast
  ring

theorem logProj_injective (d i j : Nat) (hi : i < d) (hj : j < d)
    (h : JointChallengeSpace.logProj d i = JointChallengeSpace.logProj d j) : i = j := by
  by_contra hne
  exact log_ne_log d i j hi hj hne h

theorem gateProj_injective (d i j : Nat) (hi : i < d) (hj : j < d)
    (h : JointChallengeSpace.gateProj d i = JointChallengeSpace.gateProj d j) : i = j := by
  by_contra hne
  exact gate_ne_gate d i j hi hj hne h

/-- (5) **THE ADOPTED JOINT UNION BOUND, RE-DERIVED.**  The adopted
`JointChallengeSpace.joint_union_bound` -- the prefix-frozen statement -- follows
from the sequential theorem applied to the frozen family, with no appeal to the
adopted proof.  Same event, same number. -/
theorem joint_union_bound_recovered (d q constraints : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hlogLen : logLane.length = d) (hgateLen : gateLane.length = d)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ q + 2 ∧ r.truth.length ≤ q + 2)
    (hlen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    JointChallengeSpace.jointProbability d
        (JointChallengeSpace.jointBadEvent d logCompare gateCompare logLane gateLane g
          (2 ^ d) coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints := by
  have h1 := frozen_lane_mass_le d (JointChallengeSpace.logProj d)
    (fun i j hi hj h => logProj_injective d i j hi hj h) 5 0 logCompare logLane
    (le_of_eq hlogLen) hlogDeg
  have h2 := frozen_lane_mass_le d (JointChallengeSpace.gateProj d)
    (fun i j hi hj h => gateProj_injective d i j hi hj h) (q + 2) 0 gateCompare gateLane
    (le_of_eq hgateLen) hgateDeg
  rw [hlogLen] at h1
  rw [hgateLen] at h2
  have houter : JointChallengeSpace.jointProbability d
      (JointChallengeSpace.outerEvent d logCompare gateCompare logLane gateLane)
        ≤ ChallengeUnionBound.outerTerm d q := by
    refine (JointChallengeSpace.joint_probability_union_le d _ _).trans ?_
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    unfold ChallengeUnionBound.outerTerm
    push_cast
    ring
  have h3 := JointChallengeSpace.tau_bad_event_mass_le d g
  have h4 := JointChallengeSpace.alpha_bad_event_mass_le d (2 ^ d) constraints coeffsOf hlen
  unfold JointChallengeSpace.jointBadEvent ChallengeUnionBound.combinedBound
  refine (JointChallengeSpace.joint_probability_union_le d _ _).trans ?_
  exact add_le_add ((JointChallengeSpace.joint_probability_union_le d _ _).trans
    (add_le_add houter h3)) h4

/-! ## 6. The envelope figure, restated with its warnings -/

/-- (6) THE ENVELOPE MASS OF THE ADAPTIVE GOOD EVENT.  At the envelope extremes
(`degreeBits = 13`, `quotientDegree = 8`, `numGateConstraints = 123`) the good
event of the ADAPTIVE disjunction on the ONE joint space has mass at least
`1 - 2^(-172)`.

`2^-172` IS NOT THE SYSTEM'S SOUNDNESS ERROR, and this module does not change
that by one bit.  It omits the WHIR/Merkle term, which dominates; the deployed
design point is around 100 bits.  What has changed is only WHICH outer provers
the outer summand covers: adaptive ones as well as prefix-frozen ones.

`hlogOwns` / `hgateOwns` fix the phase bit of the interleaved walk
[log 0, gate 0, log 1, gate 1, …]: `ownsNext = true` means this lane owns the
next coordinate; the log lane starts with `true` (even coordinates), the gate
lane with `false` (odd coordinates).  It does NOT disable a lane: the gate
lane's adopted `roundBadSet` appears at every gate coordinate (see
`Lane.badSet`). -/
theorem adaptive_good_event_mass_at_extremes (logLane gateLane : Lane) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hlog : logLane.Bounded 5) (hlogOwns : logLane.ownsNext = true)
    (hgate : gateLane.Bounded (8 + 2)) (hgateOwns : gateLane.ownsNext = false)
    (hlen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) :
    1 - (1 : ℚ) / 2 ^ 172
      ≤ JointChallengeSpace.jointProbability 13 (JointChallengeSpace.goodEvent 13
          (adaptiveJointBadEvent 13 logLane gateLane g (2 ^ 13) coeffsOf)) := by
  have h := adaptive_joint_good_event_mass_ge 13 8 123 logLane gateLane g coeffsOf hlog
    hlogOwns hgate hgateOwns hlen
  have hnum := ChallengeUnionBound.combined_bound_at_extremes_numeric
  linarith

/-! ## 7. Small examples: the statements are not vacuous -/

/-- A lane whose message function GENUINELY READS ITS PREFIX -- it echoes the
FIRST realized challenge, the prefix list being OLDEST FIRST -- and still
satisfies the adopted degree bound.  Concretely
`((echoLane.step x).step y).message [] = [x]` by `rfl`: the message is the
EARLIER of the two realized challenges, not the more recent one.  So
`Lane.Bounded` is satisfiable by prefix-dependent provers, and the adaptive
statements above are not vacuous. -/
def echoLane : Lane where
  message := fun xs => xs.take 1
  truth := fun _ => []
  claim := 0
  truthClaim := 0
  ownsNext := true

theorem echoLane_bounded : echoLane.Bounded 5 := by
  intro xs
  refine ⟨?_, ?_⟩
  · show (xs.take 1).length ≤ 5
    rw [List.length_take]
    exact le_trans (Nat.min_le_left _ _) (by omega)
  · exact Nat.zero_le _

theorem echoLane_reads_its_prefix (x : Element) (xs : List Element) :
    echoLane.message (x :: xs) = [x] := rfl

/-- (7) THE ADAPTIVE LANE EVENT IS NOT EMPTY BY CONSTRUCTION: any draw whose
FIRST log coordinate reduces into the lane's own round-zero bad set is in it. -/
theorem adaptive_lane_event_first_round (n : Nat) (L : Lane)
    (w : JointChallengeSpace.JointSpace (n + 1))
    (hw : OuterChallenge.reduceTriple (w (JointChallengeSpace.logProj (n + 1) 0)) ∈ L.badSet) :
    w ∈ adaptiveLaneEvent (n + 1) L := by
  rw [adaptiveLaneEvent, outerCoords, roundCoords, mem_adaptiveEvent_cons, laneBad,
    JointChallengeSpace.mem_tupleEvent]
  exact Or.inl hw

/-- (7) With no rounds there is no outer event at all. -/
theorem adaptive_lane_event_zero (L : Lane) :
    adaptiveLaneEvent 0 L = (∅ : Finset (JointChallengeSpace.JointSpace 0)) := by
  rw [adaptiveLaneEvent, outerCoords, roundCoords, adaptiveEvent_nil]

/-- (7) The interleaved schedule of one round is `log 0, gate 0`, in that
order. -/
theorem outerCoords_one :
    outerCoords 1 = [JointChallengeSpace.logProj 1 0, JointChallengeSpace.gateProj 1 0] := rfl

end Audit.Wire3.OuterSequentialConditioning
