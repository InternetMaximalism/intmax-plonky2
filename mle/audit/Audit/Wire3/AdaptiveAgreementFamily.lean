import Audit.Wire3.OuterSequentialConditioning
import Audit.Wire3.GatePointZeroCheck

/-!
# THE ADAPTIVE AGREEMENT FAMILY: SEQUENTIAL SCHWARTZ--ZIPPEL FOR THE GATE POINT,
# AND THE LANE-LEVEL FROZEN COMPARISON

## The two gaps this module closes

**GAP 1.**  The adopted `Audit.Wire3.GatePointZeroCheck.columnAgreementSet d col
committedCol` is a JOINT condition on all `d` gate-point coordinates -- the
vanishing set of a multilinear extension -- so it does not fit the
per-coordinate adaptive engine of the adopted
`Audit.Wire3.OuterSequentialConditioning`, and `col` is a FIXED parameter there.
That module's header admits the consequence verbatim: "The density reading of
§2/§3 is meaningful only with `col` FIXED BEFORE the point."  This module proves
the SEQUENTIAL form of the same Schwartz--Zippel bound: walking the gate
coordinates in BINDING ORDER, coordinate `k` carries a bad set of at most ONE
point (`sequential_agreement_fibre_le_one`), the joint agreement event is
CONTAINED in the per-coordinate union (`agreement_subset_prefixEvent`), and the
adopted `OuterSequentialConditioning.adaptive_union_mass_bound` then gives the
mass (`adaptive_agreement_mass_bound`) -- with the supplied column allowed to be
a FUNCTION of the coordinates already drawn.

**WHAT THAT BUYS, STATED AS A DICHOTOMY AND NOT AS A COVERAGE CLAIM.**  For a
column `colOf` read at the first `cut` coordinates, EXACTLY ONE of the following
holds at a realized gate point:

* the difference column, bound by the realized first `cut` coordinates, is
  IDENTICALLY ZERO on the remaining cube -- the supplied column's extension
  coincides with the committed one on the whole affine slice through that
  prefix.  This is a STRUCTURAL COLLISION, not a lucky draw, and the forger can
  FORCE it by construction: §5c exhibits, for every `d ≥ 1`, every committed
  column and every gate point, a width-`2 ^ d` column that differs from the
  committed one on the cube yet is killed by binding ONE coordinate
  (`escape_not_in_family`, `escape_agrees_everywhere`,
  `escape_is_a_genuine_forgery`).  Such a forger is charged NOTHING here, at
  ANY `cut ≥ 1`, and the residue class handed to R2/R3 is exactly "columns whose
  extension coincides with the committed one on the realized slice";
* or the point lies in `adaptiveAgreementSet`, a set of mass at most the adopted
  `ChallengeUnionBound.tauTerm d`.

So the density reading of the adopted `OuterSequentialConditioning` holds here IN
THE DICHOTOMY FORM -- NOT as "the density reading now holds with `col` chosen
adaptively", which would be false.  The genuinely new coverage is over adaptive
selections that KEEP A RESIDUAL: for instance a forger choosing among many
columns that all still differ on the remaining cube pays `tauTerm d` once, not
`#choices * tauTerm d`.  It is not coverage of adaptivity as such.

**GAP 2.**  The adopted `OuterSequentialConditioning` header records: "A
`Lane`-level frozen comparison -- a `Lane` whose `message` ignores its prefix
still advances its claims along the DRAW's own coordinates and coincides with
the adopted `laneEvent` only at a draw satisfying `DrawEncodesRun` -- is NOT
proved here."  §6-§7 prove it
(`frozen_lane_matches_laneEvent_at_encoding_draw`).

## WHAT IS PROVED

1. **THE BINDING ALGEBRA** (§1).  `bindHead x g` is the value family of the
   extension after its HEAD coordinate is set to `x`; `extensionOf_cons_bindHead`
   is the adopted `ZeroCheckSemantics.extensionOf_cons` recombined through the
   adopted `GatePointZeroCheck.extensionOf_affine`, and `extensionOf_bindPrefix`
   iterates it.  No new evaluation function is introduced.

2. **THE PER-COORDINATE ROOT SET** (§2).  `stepBad m h` is EMPTY when the family
   `h` already vanishes on the whole remaining cube -- that prefix was bad
   earlier, and is charged to an earlier coordinate -- and is otherwise the
   adopted `ZeroCheckSemantics.rootPoints` of ONE index pair chosen by
   `searchNonzero`.  `stepBad_card_le_one` is the adopted
   `ZeroCheckSemantics.card_root_le_one` at that pair.

3. **THE WALK** (§3).  `walk_finds_bad`: if the extension vanishes at the drawn
   point while the family is still nonzero on the cube after the first `cut`
   coordinates, then some coordinate `k ≥ cut` of the draw lands in
   `stepBad (d - k)` of the family bound by the coordinates before it.  This is
   the honest induction: at each step the restriction is affine in the head
   coordinate, and is either identically zero on the remaining cube -- in which
   case the previous coordinate is charged -- or has at most one root at the
   witnessed index pair.

4. **THE ADAPTIVE FAMILY** (§4).  `sequentialAgreementBad d cut colOf
   committedCol` is `PrefixDependent` in the adopted sense
   (`sequentialAgreementBad_prefixDependent`), has fibre card at most `1`
   (`sequential_agreement_fibre_le_one`), and CONTAINS the agreement event
   (`agreement_subset_prefixEvent`).  The adopted
   `OuterSequentialConditioning.adaptive_union_card_bound` then gives
   `card * |F| ≤ d * |F|^d` (`adaptive_agreement_card_bound`), i.e. density at
   most `d / |F|` -- the SAME count the adopted
   `ZeroCheckSemantics.vanishing_card_bound` gets for a FIXED column.

5. **THE MASS, PULLED BACK TO DIGEST TRIPLES** (§5).  Exactly as the adopted
   `OuterSequentialConditioning` does for the lanes, the count is pushed to the
   digest alphabet through the adopted
   `ChallengeUnionBound.uniform_product_probability_bound`, giving
   `adaptive_agreement_mass_bound : uniformProductProbability d
   (adaptiveAgreementSet …) ≤ ChallengeUnionBound.tauTerm d` -- the SAME closed
   form the adopted `GatePointZeroCheck.gate_point_agreement_mass_bound` gets for
   a fixed column, now for an adaptively supplied one.

6. **THE FIFTH FAMILY ON THE ONE JOINT SPACE** (§5).  `adaptiveAgreementEvent` is
   the adopted `GatePointZeroCheck.gatePointEvent` pullback of that set to the
   `outerGate` block, and `adaptive_joint_union_bound_with_agreement` adds it to
   the adopted `OuterSequentialConditioning.adaptiveJointBadEvent`, giving
   `combinedBound d q d constraints + tauTerm d`.  THE TWO SUMMANDS ARE KEPT
   SEPARATE, exactly as stated: the fifth family is NOT folded into
   `combinedBound`.

7. **THE TRANSPORT** (§5).  `gate_point_off_adaptive_agreement_of_joint` and
   `gate_point_off_agreement_set_of_joint` reproduce the adopted
   `GatePointZeroCheck.gate_point_off_agreement_of_joint` for the fifth family,
   so a draw outside it yields exactly the `hpoint` hypothesis of the adopted
   `GatePointZeroCheck.column_forgery_forces_one_of_three_off_bad_set`, with
   `col := colOf (realized prefix)`
   (`adaptive_column_forgery_forces_one_of_three`).

8. **THE RESIDUE OF THE ADAPTIVE READING, EXHIBITED** (§5c).  `escapeColOf` is,
   for every `d ≥ 1` and every committed column, an adaptive column that reads
   ONE gate coordinate and is a genuine width-`2 ^ d` forgery
   (`escape_is_a_genuine_forgery`) which nevertheless AGREES at every gate point
   (`escape_agrees_everywhere`) and lies OUTSIDE the fifth family at every gate
   point (`escape_not_in_family`), so `escape_kills_hnondeg` shows the
   transports of §5b have a FALSE hypothesis against it.  The two boundaries of
   the cut are recorded with it: `cut_eq_d_empty` (at `cut = d` the event is
   empty for EVERY `colOf`, so the bound is vacuous) and
   `cut_zero_is_fixed_column` (at `cut = 0` with a constant `colOf` the event is
   exactly the adopted `GatePointZeroCheck` fixed-column reading).  This is the
   §5 analogue of the adopted
   `ConstantsProvenance.bound_cell_agreement_is_not_column_equality`.

9. **THE LANE-LEVEL FROZEN COMPARISON** (§6-§7).  `frozenLane rs a b own` is a
   `Lane` whose `message`/`truth` READ NOTHING OF THE REALIZED VALUES: they are
   functions of the ROUND INDEX only, recovered from the length of the prefix
   the adopted `Lane.step` accumulates (two entries per coupled round on the
   interleaved schedule).  Its claims nevertheless advance along the DRAW's own
   coordinates, by the adopted `OuterRound.evaluate`.
   `frozen_lane_matches_laneEvent_at_encoding_draw` proves that at a draw
   satisfying the corresponding field of the adopted
   `JointChallengeSpace.DrawEncodesRun` -- `logDrawn` for the log lane,
   `gateDrawn` for the gate lane -- the adopted
   `OuterSequentialConditioning.adaptiveLaneEvent` of that frozen `Lane` and the
   adopted `JointChallengeSpace.laneEvent` of the run's own lane are the SAME
   EVENT, as a two-sided IFF, ONE LANE AT A TIME.

## THE COORDINATE ORDER, AND ITS EVIDENCE

The walk visits gate-point coordinates `0, 1, …, d-1` in that order, and this is
the order every adopted notion uses:

* the adopted `ZeroCheckSemantics.extensionOf_cons` peels the HEAD coordinate of
  the point list, with the two halves of the value family as its `0`/`1`
  endpoints -- so coordinate `0` of `List.ofFn w` binds first;
* the adopted `GatePointZeroCheck.cell_bindColumn_eq_extension` identifies that
  extension with the adopted fold
  `NormTerminalBinding.cell (NormTerminalBinding.bindColumn col point)`, so
  `bindColumn` folds in the same order;
* the adopted
  `GatePointZeroCheck.gate_point_column_is_the_gate_lane_challenges` proves the
  point list IS the gate lane's challenge list in ROUND order, and the adopted
  `GatePointZeroCheck.gate_point_coordinates_are_outerGate_draws` puts entry `i`
  of it at joint coordinate `JointChallengeSpace.Draw.outerGate i`.

So "coordinate `k` of the walk" is round `k`'s gate challenge, which is squeezed
after every challenge of every round `< k`.  That is what makes the walk of §3
legitimate: the coordinates `≥ cut` are still unread when the column is fixed.

It is NOT a statement that a column chosen after the first `cut` coordinates is
covered.  Reading even ONE coordinate already lets the forger leave the event
altogether by making the bound difference identically zero (§5c); what the walk
covers is the OTHER branch of the dichotomy above -- adaptive selections that
still leave a residual on the remaining cube.  A column chosen after ALL `d`
coordinates is not covered either, and at `cut = d` the event is literally EMPTY
(`cut_eq_d_empty`), so the bound is vacuous there.

## WHAT IS **NOT** PROVED HERE

* **THE LAW IS STILL AN IDEAL UNIFORM COUNTING LAW WRITTEN DOWN BY HAND.**
  Everything is COUNTING on the adopted explicit finite spaces
  (`ZeroCheckSemantics.Tuple d`, `ChallengeUnionBound.TripleTuple d`,
  `JointChallengeSpace.JointSpace d`), divided by their sizes.  No probability
  space over hashes or over runs exists in this development, and nothing here
  says anything about Keccak.
* **`DrawEncodesRun` IS A COORDINATE STATEMENT, NOT A HASH ASSUMPTION.**  It is
  inhabited for every hash and every accepted run (adopted
  `JointChallengeSpace.draw_encodes_run_inhabited` /
  `draw_encodes_run_of_accepted`).  §7 uses it only to identify the draw's
  coordinates with the run's realized challenges; it does not and cannot make
  the encoding draw uniform.
* **THE FIAT--SHAMIR HALF (B) REMAINS UNFORMALIZED.**  The reading that THE
  RUN'S ENCODING DRAW IS DISTRIBUTED BY `jointProbability` is not expressed
  anywhere, in Lean or as a hypothesis, here or in any adopted module.  Joining
  a mass statement to a statement about one particular draw is precisely the
  step this audit does not take.
* **ADAPTIVITY IS NOT COVERED; ONLY THE RESIDUAL BRANCH OF THE DICHOTOMY IS.**
  `sequentialAgreementBad` and `adaptiveAgreementSet` read `colOf` at
  `xs.take cut` and NOWHERE ELSE, so the prefix-dependence is structural.  But
  the event also carries a NON-DEGENERACY conjunct -- after the first `cut`
  coordinates are bound, the difference column must still be nonzero on the
  REMAINING cube -- and that conjunct is not a technicality: it is the whole
  limit.  FOR EVERY `cut ≥ 1` AND EVERY `d ≥ 1` there is a genuine
  width-`2 ^ d` forgery for which the event is EMPTY at every gate point, so the
  mass bound says nothing about it: §5c constructs it
  (`escapeColOf`, `escape_not_in_family`, `escape_agrees_everywhere`,
  `escape_is_a_genuine_forgery`, `escape_kills_hnondeg`).  After ONE coordinate
  `x0` the residual `(1 - x0) * x0 - x0 * (1 - x0)` is identically zero.  So a
  forger that can force a structural collision on the realized slice -- and one
  that simply waits until all `d` gate coordinates are out -- is NOT EXCLUDED
  HERE.  What IS covered is the complementary branch: adaptive choices that keep
  a residual on the remaining cube, and those cost `tauTerm d` in total rather
  than once per choice.
* **THE COLLIDING COLUMN IS THE EXTRACTION JOIN'S RESIDUE.**  Excluding the
  structurally colliding columns of §5c -- and, a fortiori, a column chosen
  after the whole point -- is the job of the adopted
  `GatePointZeroCheck` residues R2 (`OpeningBinding.OpensCommittedTable` is a
  visible hypothesis) and R3 (`ConstantsProvenance.ConstantsColumnsOfRoot` is a
  supplied root-to-columns map) -- the two branches the composed theorem of §5
  consumes.  **R1 IS UNCHANGED** (no link from the engine's WHIR observation to a
  concrete `WhirRows`/`Merkle` execution), and so are R2/R3 themselves: this
  module narrows WHEN the column may be chosen, not what the join proves.
* **WHIR AND MERKLE ARE EXCLUDED**, as in every module of this cohort:
  proximity / list decoding, the query-repetition profile and Merkle collision
  resistance -- the DOMINANT terms -- appear nowhere.
* **NOTHING HERE IS THE SYSTEM'S SOUNDNESS ERROR.**  `combinedBound + tauTerm d`
  covers only outer round agreement, gate tau, gate alpha and the gate-point
  column agreement.  At the envelope extremes it is still about `2^-172`:
  §8 proves `combinedBound 13 8 13 123 + tauTerm 13 ≤ 2^-171`, i.e. the fifth
  family costs strictly less than one bit, because `tauTerm 13` is itself one of
  `combinedBound`'s three summands and is around `2^-188`.  The deployed design
  point is around 100 bits, so quoting either figure as the wire-v3 soundness
  error would be wrong by roughly seventy bits.
* **THE LANE-LEVEL COMPARISON OF §7 IS ONE LANE AT A TIME.**  Each half of
  `frozen_lane_matches_laneEvent_at_encoding_draw` is a two-sided IFF for a
  SINGLE lane's frozen `Lane` against that lane's adopted `laneEvent`, on the
  interleaved schedule, at a draw satisfying that lane's `DrawEncodesRun` field
  and with that lane of full length `degreeBits`.  NO statement is made about the
  UNION of the two frozen lanes, and no `Lane` of a deployed prover is
  constructed.
* **THE COUNTER LABELS ARE DOCUMENTED, NOT DERIVED**, inherited unchanged from
  the adopted `JointChallengeSpace.schedule_position_injective` (RES-4 of the
  adopted `GatePointZeroCheck`).
* **ONE COLUMN AT A TIME** (adopted RES-3): the composed theorem is indexed by
  ONE constants index; no union over `numConstants` columns is taken.

## Tactic note

Inherited from the adopted modules: no tactic may see `Fintype.card Element`;
`Finset.univ` on the joint space, on `OuterChallenge.DigestTriple` or on a tuple
space never appears in a statement, only inside a definition; and no tuple
`Finset` is instantiated at a literal arity `≥ 2` -- the examples of §9 are at
`d = 1`.  Emptiness of the digest-level bad set of an inactive lane is obtained
through the ADOPTED `OuterSequentialConditioning.laneBad_card_of_inactive`
rather than by inspecting the digest space, for exactly that reason.

TWO REDUCTION HAZARDS FOUND AND AVOIDED HERE, recorded so they are not
reintroduced.  (i) `rfl` through the adopted `Lane.badSet` explodes: its `if`
branches are `Finset Element` values whose comparison drives the kernel into
`Finset.univ` on `Element`.  Every such step is routed through `if_pos` and
`congrArg` (`frozenLane_badSet_owned` / `frozenLane_laneBad_owned`) instead.
(ii) Membership facts about the adopted `columnAgreementSet` at a LITERAL point
are re-derived from the adopted bridge rather than transported through
`mem_columnAgreementSet` (`residue_point_agrees`), for the same reason.  The
frozen `Lane` indexes its round by the structural `halfLength`, not by
`xs.length / 2`, so that no `Nat.div` ever has to reduce.
-/

set_option maxRecDepth 8000

namespace Audit.Wire3.AdaptiveAgreementFamily

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. Binding one coordinate of the adopted multilinear extension

The adopted `ZeroCheckSemantics.extensionOf_cons` splits the extension affinely
in its HEAD coordinate, with the even/odd halves of the value family as the
`0`/`1` endpoints.  The adopted `GatePointZeroCheck.extensionOf_affine` -- the
extension is linear in the VALUE family -- recombines that split into a single
extension of a BOUND value family.  Iterating gives the restriction of the
extension after a prefix of coordinates is realized. -/

/-- The value family of the extension after its HEAD coordinate is set to `x`:
the adopted low-bit convention, even index at `0`, odd index at `1`. -/
def bindHead (x : Element) (g : Nat → Element) : Nat → Element :=
  fun k => (1 - x) * g (2 * k) + x * g (2 * k + 1)

/-- The value family after a whole prefix of coordinates is realized, OLDEST
FIRST -- the same order the adopted `NormTerminalBinding.bindColumn` folds and
the adopted `ZeroCheckSemantics.extensionOf_cons` peels. -/
def bindPrefix : List Element → (Nat → Element) → (Nat → Element)
  | [], g => g
  | x :: xs, g => bindPrefix xs (bindHead x g)

theorem bindPrefix_nil (g : Nat → Element) : bindPrefix [] g = g := rfl

theorem bindPrefix_cons (x : Element) (xs : List Element) (g : Nat → Element) :
    bindPrefix (x :: xs) g = bindPrefix xs (bindHead x g) := rfl

theorem bindPrefix_append : ∀ (xs ys : List Element) (g : Nat → Element),
    bindPrefix (xs ++ ys) g = bindPrefix ys (bindPrefix xs g)
  | [], _, _ => rfl
  | x :: xs, ys, g => by
      rw [List.cons_append, bindPrefix_cons, bindPrefix_cons, bindPrefix_append xs ys]

theorem bindPrefix_snoc (xs : List Element) (x : Element) (g : Nat → Element) :
    bindPrefix (xs ++ [x]) g = bindHead x (bindPrefix xs g) := by
  rw [bindPrefix_append]
  rfl

/-- (1) ONE COORDINATE OF THE ADOPTED EXTENSION, BOUND.  This is the adopted
`ZeroCheckSemantics.extensionOf_cons` recombined by the adopted
`GatePointZeroCheck.extensionOf_affine`; no new evaluation function appears. -/
theorem extensionOf_cons_bindHead (g : Nat → Element) (x : Element) (u : List Element) :
    ZeroCheckSemantics.extensionOf g (x :: u)
      = ZeroCheckSemantics.extensionOf (bindHead x g) u := by
  have hb : bindHead x g
      = fun i => (1 - x) * (fun k => g (2 * k)) i + x * (fun k => g (2 * k + 1)) i := rfl
  rw [ZeroCheckSemantics.extensionOf_cons, hb, GatePointZeroCheck.extensionOf_affine]

/-- (1) A WHOLE PREFIX, BOUND.  The extension at a point split as
`prefix ++ rest` is the extension of the bound family at `rest`. -/
theorem extensionOf_bindPrefix : ∀ (xs u : List Element) (g : Nat → Element),
    ZeroCheckSemantics.extensionOf g (xs ++ u)
      = ZeroCheckSemantics.extensionOf (bindPrefix xs g) u
  | [], _, _ => rfl
  | x :: xs, u, g => by
      rw [List.cons_append, extensionOf_cons_bindHead, bindPrefix_cons,
        extensionOf_bindPrefix xs u]

/-! ## 2. The per-coordinate root set, with fibre at most one -/

/-- A CUBE INDEX AT WHICH THE FAMILY IS NONZERO, if there is one below the
bound.  Any witness serves; this one is the largest. -/
noncomputable def searchNonzero (h : Nat → Element) : Nat → Nat
  | 0 => 0
  | n + 1 => if h n = 0 then searchNonzero h n else n

theorem searchNonzero_zero (h : Nat → Element) : searchNonzero h 0 = 0 := rfl

theorem searchNonzero_succ (h : Nat → Element) (n : Nat) :
    searchNonzero h (n + 1) = if h n = 0 then searchNonzero h n else n := rfl

theorem searchNonzero_lt (h : Nat → Element) : ∀ (n : Nat), 0 < n → searchNonzero h n < n
  | 0, hn => absurd hn (by omega)
  | n + 1, _ => by
      rw [searchNonzero_succ]
      by_cases hn : h n = 0
      · rw [if_pos hn]
        rcases Nat.eq_zero_or_pos n with hz | hp
        · rw [hz, searchNonzero_zero]
          omega
        · exact Nat.lt_succ_of_lt (searchNonzero_lt h n hp)
      · rw [if_neg hn]
        omega

theorem searchNonzero_spec (h : Nat → Element) : ∀ (n : Nat), (∃ i, i < n ∧ h i ≠ 0) →
    h (searchNonzero h n) ≠ 0
  | 0, hex => by
      obtain ⟨i, hi, -⟩ := hex
      omega
  | n + 1, hex => by
      rw [searchNonzero_succ]
      by_cases hn : h n = 0
      · rw [if_pos hn]
        refine searchNonzero_spec h n ?_
        obtain ⟨i, hi, hne⟩ := hex
        rcases Nat.lt_or_ge i n with h1 | h1
        · exact ⟨i, h1, hne⟩
        · exfalso
          apply hne
          rw [show i = n by omega]
          exact hn
      · rw [if_neg hn]
        exact hn

/-- Turn the adopted `ZeroCheckSemantics.CubeZero` failure into a witness. -/
theorem exists_nonzero_of_not_cubeZero (m : Nat) (h : Nat → Element)
    (hz : ¬ ZeroCheckSemantics.CubeZero m h) : ∃ i, i < 2 ^ m ∧ h i ≠ 0 := by
  by_contra hc
  refine hz (fun j hj => ?_)
  by_contra hne
  exact hc ⟨j, hj, hne⟩

open Classical in
/-- **THE PER-COORDINATE BAD SET OF THE WALK.**  `h` is the value family after
the coordinates before this one have been realized, on the cube of the `m`
coordinates that remain.

* If `h` already vanishes on that whole cube, THIS coordinate is charged
  NOTHING: the prefix was bad before, and the walk charges it to the earlier
  coordinate at which the family died.
* Otherwise a cube index at which `h` is nonzero is witnessed, and the bad set
  is the adopted `ZeroCheckSemantics.rootPoints` of the affine form whose two
  endpoints are the even and odd halves of the family at that index pair -- at
  most ONE point, by the adopted `ZeroCheckSemantics.card_root_le_one`. -/
noncomputable def stepBad (m : Nat) (h : Nat → Element) : Finset Element :=
  if ZeroCheckSemantics.CubeZero m h then ∅
  else ZeroCheckSemantics.rootPoints (h (2 * (searchNonzero h (2 ^ m) / 2)))
        (h (2 * (searchNonzero h (2 ^ m) / 2) + 1)) Finset.univ

theorem stepBad_of_cubeZero (m : Nat) (h : Nat → Element)
    (hz : ZeroCheckSemantics.CubeZero m h) : stepBad m h = ∅ := by
  rw [stepBad, if_pos hz]

theorem stepBad_of_not_cubeZero (m : Nat) (h : Nat → Element)
    (hz : ¬ ZeroCheckSemantics.CubeZero m h) :
    stepBad m h = ZeroCheckSemantics.rootPoints (h (2 * (searchNonzero h (2 ^ m) / 2)))
        (h (2 * (searchNonzero h (2 ^ m) / 2) + 1)) Finset.univ := by
  rw [stepBad, if_neg hz]

/-- (2) **THE FIBRE IS AT MOST ONE POINT.**  The adopted
`ZeroCheckSemantics.card_root_le_one` applied at the witnessed index pair: the
witness lies in that pair, so the two endpoints are not both zero. -/
theorem stepBad_card_le_one (m : Nat) (h : Nat → Element) : (stepBad m h).card ≤ 1 := by
  by_cases hz : ZeroCheckSemantics.CubeZero m h
  · rw [stepBad_of_cubeZero m h hz, Finset.card_empty]
    omega
  · rw [stepBad_of_not_cubeZero m h hz]
    refine ZeroCheckSemantics.card_root_le_one _ _ ?_ _
    have hne := searchNonzero_spec h (2 ^ m) (exists_nonzero_of_not_cubeZero m h hz)
    rintro ⟨h0, h1⟩
    have hsplit : searchNonzero h (2 ^ m) = 2 * (searchNonzero h (2 ^ m) / 2)
        ∨ searchNonzero h (2 ^ m) = 2 * (searchNonzero h (2 ^ m) / 2) + 1 := by omega
    rcases hsplit with hh | hh
    · exact hne (by rw [hh]; exact h0)
    · exact hne (by rw [hh]; exact h1)

/-- (2) **THE COORDINATE THAT KILLS THE FAMILY IS IN THE BAD SET.**  If the
family is still alive on the remaining cube but dies once this coordinate is
bound to `x`, then `x` is one of the at most one roots. -/
theorem mem_stepBad_of_bindHead_cubeZero (n : Nat) (h : Nat → Element) (x : Element)
    (hz : ¬ ZeroCheckSemantics.CubeZero (n + 1) h)
    (hb : ZeroCheckSemantics.CubeZero n (bindHead x h)) :
    x ∈ stepBad (n + 1) h := by
  rw [stepBad_of_not_cubeZero (n + 1) h hz]
  have hpos : 0 < (2 : Nat) ^ (n + 1) := pow_pos (by omega) _
  have h1 : searchNonzero h (2 ^ (n + 1)) < 2 ^ (n + 1) :=
    searchNonzero_lt h (2 ^ (n + 1)) hpos
  have hlt : searchNonzero h (2 ^ (n + 1)) / 2 < 2 ^ n := by omega
  have hzero := hb _ hlt
  simp only [ZeroCheckSemantics.rootPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hzero

/-! ## 3. The walk: a vanishing evaluation charges some coordinate -/

/-- Peeling one entry off the realized prefix, in the shape the adopted
`OuterSequentialConditioning.prefix_walk` uses. -/
theorem take_succ_ofFn (d : Nat) (w : ZeroCheckSemantics.Tuple d) (k : Nat) (hk : k < d) :
    (List.ofFn w).take (k + 1) = (List.ofFn w).take k ++ [w ⟨k, hk⟩] := by
  have hget : (List.ofFn w)[k]? = some (w ⟨k, hk⟩) := by
    rw [List.getElem?_ofFn, List.ofFnNthVal, dif_pos hk]
  rw [List.take_succ, hget]
  rfl

/-- (3) **THE SEQUENTIAL SCHWARTZ--ZIPPEL WALK.**  Suppose the adopted extension
of `g` vanishes at the realized point, while `g` bound by the first `k`
coordinates is still nonzero somewhere on the remaining cube.  Then some
coordinate `i ≥ k` of the realized point lies in `stepBad` of the family bound
by the coordinates BEFORE it -- a set of at most one point.

The induction is the honest one: at each step the restriction is affine in the
head coordinate; either it dies on the whole remaining cube, in which case THIS
coordinate is charged, or it survives and the walk continues. -/
theorem walk_finds_bad (d : Nat) (g : Nat → Element) (w : ZeroCheckSemantics.Tuple d)
    (hzero : ZeroCheckSemantics.extensionOf g (List.ofFn w) = 0) :
    ∀ (n k : Nat), k + n = d →
      ¬ ZeroCheckSemantics.CubeZero n (bindPrefix ((List.ofFn w).take k) g) →
      ∃ i : Fin d, k ≤ i.val ∧
        w i ∈ stepBad (d - i.val) (bindPrefix ((List.ofFn w).take i.val) g)
  | 0, k, hk, hnz => by
      exfalso
      refine hnz (fun j hj => ?_)
      simp only [pow_zero] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      have htake : (List.ofFn w).take k = List.ofFn w :=
        List.take_all_of_le (by rw [List.length_ofFn]; omega)
      rw [htake]
      have hsplit := extensionOf_bindPrefix (List.ofFn w) [] g
      rw [List.append_nil, ZeroCheckSemantics.extensionOf_nil] at hsplit
      rw [← hsplit]
      exact hzero
  | n + 1, k, hk, hnz => by
      have hkd : k < d := by omega
      have hstep : bindPrefix ((List.ofFn w).take (k + 1)) g
          = bindHead (w ⟨k, hkd⟩) (bindPrefix ((List.ofFn w).take k) g) := by
        rw [take_succ_ofFn d w k hkd, bindPrefix_snoc]
      by_cases hb : ZeroCheckSemantics.CubeZero n
          (bindHead (w ⟨k, hkd⟩) (bindPrefix ((List.ofFn w).take k) g))
      · refine ⟨⟨k, hkd⟩, le_refl _, ?_⟩
        show w ⟨k, hkd⟩ ∈ stepBad (d - k) (bindPrefix ((List.ofFn w).take k) g)
        rw [show d - k = n + 1 by omega]
        exact mem_stepBad_of_bindHead_cubeZero n _ _ hnz hb
      · obtain ⟨i, hi, hmem⟩ :=
          walk_finds_bad d g w hzero n (k + 1) (by omega) (by rw [hstep]; exact hb)
        exact ⟨i, by omega, hmem⟩

/-! ## 4. The adaptive per-coordinate agreement family

`cut` is the number of gate coordinates the forger is allowed to see BEFORE it
must fix its constants column.  `colOf` is read at `xs.take cut` AND NOWHERE
ELSE, so the prefix-dependence of the adopted
`OuterSequentialConditioning.PrefixDependent` is built into the definition
rather than assumed.  `cut = 0` is the non-adaptive case of the adopted
`GatePointZeroCheck` (`cut_zero_is_fixed_column`), and `cut = d` is the empty
case (`cut_eq_d_empty`).

READ THE EVENT AS THE SECOND BRANCH OF A DICHOTOMY, NOT AS COVERAGE OF
ADAPTIVITY.  The non-degeneracy conjunct below is a real condition on the
forger, not bookkeeping: §5c builds, for every `cut ≥ 1`, a genuine forgery for
which it FAILS at every gate point. -/

/-- **THE ADAPTIVE PER-COORDINATE BAD FAMILY.**  Before the cut the family is
empty -- the column is not yet fixed, and nothing is charged.  From the cut on,
coordinate `k` carries the at-most-one root set of the difference column bound
by the coordinates before `k`. -/
noncomputable def sequentialAgreementBad (d cut : Nat) (colOf : List Element → List Element)
    (committedCol : List Element) (k : Nat) (xs : List Element) : Finset Element :=
  if cut ≤ k then
    stepBad (d - k) (bindPrefix (xs.take k)
      (GatePointZeroCheck.diffColumn (colOf (xs.take cut)) committedCol))
  else ∅

/-- (4) **THE FIBRE BOUND: AT MOST ONE POINT PER COORDINATE.** -/
theorem sequential_agreement_fibre_le_one (d cut : Nat) (colOf : List Element → List Element)
    (committedCol : List Element) (k : Nat) (xs : List Element) :
    (sequentialAgreementBad d cut colOf committedCol k xs).card ≤ 1 := by
  unfold sequentialAgreementBad
  split
  · exact stepBad_card_le_one _ _
  · rw [Finset.card_empty]
    omega

/-- (4) **THE FAMILY READS ONLY THE PREFIX**, in the adopted sense.  Coordinate
`k`'s bad set is a function of the first `k` realized coordinates: the bound
family reads `xs.take k`, and the column reads `xs.take cut` with `cut ≤ k`. -/
theorem sequentialAgreementBad_prefixDependent (d cut : Nat)
    (colOf : List Element → List Element) (committedCol : List Element) :
    OuterSequentialConditioning.PrefixDependent
      (sequentialAgreementBad d cut colOf committedCol) := by
  intro k xs ys h
  unfold sequentialAgreementBad
  by_cases hk : cut ≤ k
  · have hmin : min cut k = cut := Nat.min_eq_left hk
    have h1 : (xs.take k).take cut = xs.take cut := by rw [List.take_take, hmin]
    have h2 : (ys.take k).take cut = ys.take cut := by rw [List.take_take, hmin]
    have hc : xs.take cut = ys.take cut := by rw [← h1, ← h2, h]
    rw [if_pos hk, if_pos hk, h, hc]
  · rw [if_neg hk, if_neg hk]

open Classical in
/-- **THE ADAPTIVE AGREEMENT EVENT, ON THE TUPLE SPACE.**  A point is in it when

* the difference column, BOUND BY THE FIRST `cut` COORDINATES, is still nonzero
  somewhere on the remaining cube -- the honest non-degeneracy condition, and
  the exact relativization of the adopted
  `GatePointZeroCheck.ColumnsDifferOnCube` to the walk position; and
* the supplied column, chosen after those `cut` coordinates, has the same bound
  cell as the committed column at the whole point -- the adopted
  `GatePointZeroCheck.PointAgrees`.

WITHOUT the first conjunct there is nothing to prove -- and the first conjunct
is NOT a mild side condition.  It fails identically, at EVERY gate point, for
the escaping column of §5c, which reads ONE coordinate and is still a genuine
forgery.  So membership in this set is the RESIDUAL branch of the dichotomy of
the header: either the bound difference dies on the whole remaining slice, in
which case nothing here charges the forger, or the point is in this set, whose
mass is at most `ChallengeUnionBound.tauTerm d`. -/
noncomputable def adaptiveAgreementSet (d cut : Nat) (colOf : List Element → List Element)
    (committedCol : List Element) : Finset (ZeroCheckSemantics.Tuple d) :=
  Finset.univ.filter (fun w =>
    ¬ ZeroCheckSemantics.CubeZero (d - cut)
        (bindPrefix ((List.ofFn w).take cut)
          (GatePointZeroCheck.diffColumn (colOf ((List.ofFn w).take cut)) committedCol))
      ∧ GatePointZeroCheck.PointAgrees (colOf ((List.ofFn w).take cut)) committedCol
          (List.ofFn w))

theorem mem_adaptiveAgreementSet (d cut : Nat) (colOf : List Element → List Element)
    (committedCol : List Element) (w : ZeroCheckSemantics.Tuple d) :
    w ∈ adaptiveAgreementSet d cut colOf committedCol ↔
      (¬ ZeroCheckSemantics.CubeZero (d - cut)
          (bindPrefix ((List.ofFn w).take cut)
            (GatePointZeroCheck.diffColumn (colOf ((List.ofFn w).take cut)) committedCol))
        ∧ GatePointZeroCheck.PointAgrees (colOf ((List.ofFn w).take cut)) committedCol
            (List.ofFn w)) := by
  simp only [adaptiveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- (4) **THE JOINT AGREEMENT EVENT IS CONTAINED IN THE PER-COORDINATE UNION.**
This is the content of GAP 1: a joint condition on all `d` coordinates -- the
vanishing of a multilinear extension -- is dominated by an ADAPTIVE
per-coordinate family of the shape the adopted `OuterSequentialConditioning`
engine consumes.  The containment is of the event AS DEFINED, non-degeneracy
conjunct included; it is not a containment of "every adaptive agreement". -/
theorem agreement_subset_prefixEvent (d cut : Nat) (hcut : cut ≤ d)
    (colOf : List Element → List Element) (committedCol : List Element) :
    adaptiveAgreementSet d cut colOf committedCol
      ⊆ OuterSequentialConditioning.prefixEvent d
          (sequentialAgreementBad d cut colOf committedCol) := by
  intro w hw
  rw [mem_adaptiveAgreementSet] at hw
  obtain ⟨hnz, hagree⟩ := hw
  have hvan : ZeroCheckSemantics.extensionOf
      (GatePointZeroCheck.diffColumn (colOf ((List.ofFn w).take cut)) committedCol)
      (List.ofFn w) = 0 := by
    have hmem : w ∈ GatePointZeroCheck.columnAgreementSet d
        (colOf ((List.ofFn w).take cut)) committedCol :=
      (GatePointZeroCheck.mem_columnAgreementSet d _ committedCol w).mpr hagree
    rw [GatePointZeroCheck.columnAgreementSet_eq_vanishingSet,
      ZeroCheckSemantics.mem_vanishingSet] at hmem
    exact hmem
  obtain ⟨i, hi, hmem⟩ := walk_finds_bad d _ w hvan (d - cut) cut (by omega) hnz
  rw [OuterSequentialConditioning.mem_prefixEvent]
  refine ⟨i, ?_⟩
  unfold sequentialAgreementBad
  rw [if_pos hi]
  exact hmem

/-- The size of the adopted gate-point tuple space, written without ever
handing `Fintype.card Element` to a simp set. -/
theorem tuple_space_card (d : Nat) :
    Fintype.card (Fin d → Element) = Fintype.card Element ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin]

/-- (4) **THE COUNT.**  The adopted
`OuterSequentialConditioning.adaptive_union_card_bound` at fibre bound `1` per
coordinate: the adaptive agreement event has `card * |F| ≤ d * |F|^d`, i.e.
density at most `d / |F|` -- the SAME count the adopted
`ZeroCheckSemantics.vanishing_card_bound` gets for a column fixed in advance. -/
theorem adaptive_agreement_card_bound (d cut : Nat) (hcut : cut ≤ d)
    (colOf : List Element → List Element) (committedCol : List Element) :
    (adaptiveAgreementSet d cut colOf committedCol).card * Fintype.card Element
      ≤ d * Fintype.card Element ^ d := by
  have hsub := Finset.card_le_card (agreement_subset_prefixEvent d cut hcut colOf committedCol)
  have hmain := OuterSequentialConditioning.adaptive_union_card_bound d
    (sequentialAgreementBad d cut colOf committedCol) (fun _ => 1)
    (sequentialAgreementBad_prefixDependent d cut colOf committedCol)
    (fun k xs => sequential_agreement_fibre_le_one d cut colOf committedCol k xs)
  have hsum : (∑ _k ∈ Finset.range d, 1) = d := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
  rw [hsum, tuple_space_card] at hmain
  exact le_trans (Nat.mul_le_mul_right _ hsub) hmain

/-! ## 5. The mass, the fifth family, and the transport -/

/-- The pull-back of a count on the gate-point tuple space to the digest-triple
alphabet, exactly as the adopted `ChallengeUnionBound.tau_product_mass_bound`
performs it for the tau block. -/
theorem product_mass_of_card_bound (n : Nat) (S : Finset (ZeroCheckSemantics.Tuple n))
    (hcard : S.card * Fintype.card Element ≤ n * Fintype.card Element ^ n) :
    ChallengeUnionBound.uniformProductProbability n S ≤ ChallengeUnionBound.tauTerm n := by
  have hq : (0 : ℚ) < (Fintype.card Element : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := Element)
  have hcardQ : (S.card : ℚ) * (Fintype.card Element : ℚ)
      ≤ (n : ℚ) * (Fintype.card Element : ℚ) ^ n := by exact_mod_cast hcard
  have hle : (S.card : ℚ)
      ≤ (n : ℚ) * ((Fintype.card Element : ℚ) ^ n / (Fintype.card Element : ℚ)) := by
    rw [mul_div_assoc', le_div_iff hq]
    exact hcardQ
  refine (ChallengeUnionBound.uniform_product_probability_bound n S S.card le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_right hle
    (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)

/-- (5) **THE ADAPTIVE AGREEMENT MASS.**  On the SAME explicit uniform law the
adopted `ChallengeUnionBound` puts on a `d`-coordinate challenge column, the
mass of "a constants column chosen after the first `cut` gate coordinates is
invisible at the whole gate point, while still differing on the remaining cube"
is at most the adopted `ChallengeUnionBound.tauTerm d` -- LITERALLY the bound
the adopted `GatePointZeroCheck.gate_point_agreement_mass_bound` gets for a
column fixed in advance.

NOT a probability over runs: the gate point is derived from the transcript. -/
theorem adaptive_agreement_mass_bound (d cut : Nat) (hcut : cut ≤ d)
    (colOf : List Element → List Element) (committedCol : List Element) :
    ChallengeUnionBound.uniformProductProbability d
        (adaptiveAgreementSet d cut colOf committedCol)
      ≤ ChallengeUnionBound.tauTerm d :=
  product_mass_of_card_bound d _ (adaptive_agreement_card_bound d cut hcut colOf committedCol)

/-- **THE FIFTH FAMILY ON THE ONE ADOPTED JOINT SPACE**: the adaptive agreement
set, pulled back to the `outerGate` block by the adopted
`GatePointZeroCheck.gatePointEvent`. -/
noncomputable def adaptiveAgreementEvent (d cut : Nat) (colOf : List Element → List Element)
    (committedCol : List Element) : Finset (JointChallengeSpace.JointSpace d) :=
  GatePointZeroCheck.gatePointEvent d (adaptiveAgreementSet d cut colOf committedCol)

/-- (5) THE FIFTH FAMILY'S JOINT MASS, by the adopted
`GatePointZeroCheck.gate_point_event_mass` cylinder split. -/
theorem adaptive_agreement_joint_mass_bound (d cut : Nat) (hcut : cut ≤ d)
    (colOf : List Element → List Element) (committedCol : List Element) :
    JointChallengeSpace.jointProbability d (adaptiveAgreementEvent d cut colOf committedCol)
      ≤ ChallengeUnionBound.tauTerm d := by
  rw [adaptiveAgreementEvent, GatePointZeroCheck.gate_point_event_mass]
  exact adaptive_agreement_mass_bound d cut hcut colOf committedCol

/-- (5) **THE JOINT UNION BOUND WITH THE FIFTH FAMILY.**  On the adopted ONE
joint sample space, under the adopted uniform counting law, the mass of

* the adopted `OuterSequentialConditioning.adaptiveJointBadEvent` -- adaptive
  outer coupled rounds, gate tau, gate alpha -- OR
* the ADAPTIVE gate-point column agreement of a constants column chosen after
  the first `cut` gate coordinates

is at most `combinedBound d q d constraints + tauTerm d`.  THE TWO SUMMANDS ARE
KEPT SEPARATE: the fifth family is not folded into `combinedBound`, because it
is a fifth event and not one of `combinedBound`'s three.

`hlogOwns` / `hgateOwns` fix the phase bit of the adopted interleaved walk, as
in the adopted `OuterSequentialConditioning.adaptive_joint_union_bound`. -/
theorem adaptive_joint_union_bound_with_agreement (d q constraints cut : Nat)
    (logLane gateLane : OuterSequentialConditioning.Lane) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (colOf : List Element → List Element)
    (committedCol : List Element)
    (hlog : logLane.Bounded 5) (hlogOwns : logLane.ownsNext = true)
    (hgate : gateLane.Bounded (q + 2)) (hgateOwns : gateLane.ownsNext = false)
    (hlen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints)
    (hcut : cut ≤ d) :
    JointChallengeSpace.jointProbability d
        (OuterSequentialConditioning.adaptiveJointBadEvent d logLane gateLane g (2 ^ d) coeffsOf
          ∪ adaptiveAgreementEvent d cut colOf committedCol)
      ≤ ChallengeUnionBound.combinedBound d q d constraints + ChallengeUnionBound.tauTerm d := by
  refine (JointChallengeSpace.joint_probability_union_le d _ _).trans ?_
  exact add_le_add
    (OuterSequentialConditioning.adaptive_joint_union_bound d q constraints logLane gateLane g
      coeffsOf hlog hlogOwns hgate hgateOwns hlen)
    (adaptive_agreement_joint_mass_bound d cut hcut colOf committedCol)

/-! ### 5b. Transport: a good joint draw puts the run's gate point off the set -/

/-- A list is recovered from a tuple that reads its entries. -/
theorem ofFn_of_get (n : Nat) (point : List Element) (hn : point.length = n)
    (t : Fin n → Element)
    (hget : ∀ i : Fin n, ∀ h : i.val < point.length, point.get ⟨i.val, h⟩ = t i) :
    List.ofFn t = point := by
  subst hn
  have ht : ZeroCheckSemantics.tupleOf point = t := by
    funext i
    exact hget i i.isLt
  rw [← ht, ZeroCheckSemantics.ofFn_tupleOf]

/-- (5) THE RUN'S GATE POINT IS THE DRAW'S `outerGate` BLOCK, as a LIST.  The
adopted `GatePointZeroCheck.gate_point_coordinates_are_outerGate_draws`, read
back as an equality of lists. -/
theorem gate_point_is_the_draw (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) (w : JointChallengeSpace.JointSpace c.degreeBits)
    (hwidth : (TranscriptProvenance.gatePointColumn e c p).length = c.degreeBits)
    (hdrawn : JointChallengeSpace.DrawnAt c.degreeBits w
      (JointChallengeSpace.gateProj c.degreeBits)
      (ConditionalSoundness.gateLaneOf e c p truths) 0) :
    List.ofFn (GatePointZeroCheck.gateReduction c.degreeBits w)
      = TranscriptProvenance.gatePointColumn e c p :=
  ofFn_of_get c.degreeBits _ hwidth _
    (GatePointZeroCheck.gate_point_coordinates_are_outerGate_draws e c p truths w
      (GatePointZeroCheck.gate_lane_length_of_gate_point_width e c p truths hwidth) hdrawn)

/-- (5) **THE COMPOSED TRANSPORT.**  A joint draw outside the FIFTH family,
whose `outerGate` coordinates carry the run's own gate challenges, and whose
partially bound difference column is still alive on the remaining cube, puts the
run's derived gate point OFF the adopted agreement condition -- for the column
`colOf` supplies after the first `cut` gate coordinates.

`hnondeg` CANNOT BE DROPPED, AND IT IS NOT GENERICALLY TRUE.  It is the residual
branch of the header's dichotomy, and §5c exhibits a genuine forgery for which
it is FALSE at every gate point and every `cut ≥ 1`
(`escape_kills_hnondeg`).  For such a column this theorem says nothing at all;
excluding it is R2/R3's job, not this module's. -/
theorem gate_point_off_adaptive_agreement_of_joint (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (truths : List (List Element)) (cut : Nat)
    (colOf : List Element → List Element) (committedCol : List Element)
    (w : JointChallengeSpace.JointSpace c.degreeBits)
    (hwidth : (TranscriptProvenance.gatePointColumn e c p).length = c.degreeBits)
    (hdrawn : JointChallengeSpace.DrawnAt c.degreeBits w
      (JointChallengeSpace.gateProj c.degreeBits)
      (ConditionalSoundness.gateLaneOf e c p truths) 0)
    (hnondeg : ¬ ZeroCheckSemantics.CubeZero (c.degreeBits - cut)
      (bindPrefix ((TranscriptProvenance.gatePointColumn e c p).take cut)
        (GatePointZeroCheck.diffColumn
          (colOf ((TranscriptProvenance.gatePointColumn e c p).take cut)) committedCol)))
    (hgood : w ∉ adaptiveAgreementEvent c.degreeBits cut colOf committedCol) :
    ¬ GatePointZeroCheck.PointAgrees
        (colOf ((TranscriptProvenance.gatePointColumn e c p).take cut)) committedCol
        (TranscriptProvenance.gatePointColumn e c p) := by
  intro hagree
  refine hgood ?_
  rw [adaptiveAgreementEvent, GatePointZeroCheck.mem_gatePointEvent,
    mem_adaptiveAgreementSet, gate_point_is_the_draw e c p truths w hwidth hdrawn]
  exact ⟨hnondeg, hagree⟩

/-- (5) THE SAME, IN THE EXACT SHAPE THE ADOPTED COMPOSED THEOREM CONSUMES: the
`hpoint` hypothesis of the adopted
`GatePointZeroCheck.column_forgery_forces_one_of_three_off_bad_set`, with
`col := colOf (realized prefix)`.  `hnondeg` carries the same caveat as above:
it is FALSE for the escaping column of §5c. -/
theorem gate_point_off_agreement_set_of_joint (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (truths : List (List Element)) (cut : Nat)
    (colOf : List Element → List Element) (committedCol : List Element)
    (w : JointChallengeSpace.JointSpace c.degreeBits)
    (hwidth : (TranscriptProvenance.gatePointColumn e c p).length = c.degreeBits)
    (hdrawn : JointChallengeSpace.DrawnAt c.degreeBits w
      (JointChallengeSpace.gateProj c.degreeBits)
      (ConditionalSoundness.gateLaneOf e c p truths) 0)
    (hnondeg : ¬ ZeroCheckSemantics.CubeZero (c.degreeBits - cut)
      (bindPrefix ((TranscriptProvenance.gatePointColumn e c p).take cut)
        (GatePointZeroCheck.diffColumn
          (colOf ((TranscriptProvenance.gatePointColumn e c p).take cut)) committedCol)))
    (hgood : w ∉ adaptiveAgreementEvent c.degreeBits cut colOf committedCol) :
    ZeroCheckSemantics.tupleOf (TranscriptProvenance.gatePointColumn e c p)
      ∉ GatePointZeroCheck.columnAgreementSet
          (TranscriptProvenance.gatePointColumn e c p).length
          (colOf ((TranscriptProvenance.gatePointColumn e c p).take cut)) committedCol := by
  intro hin
  exact gate_point_off_adaptive_agreement_of_joint e c p truths cut colOf committedCol w
    hwidth hdrawn hnondeg hgood
    ((GatePointZeroCheck.mem_columnAgreementSet_tupleOf _ _ _).mp hin)

/-- (5) **THE COMPOSED ATTACK THEOREM, WITH AN ADAPTIVELY SUPPLIED COLUMN.**
The adopted `GatePointZeroCheck.column_forgery_forces_one_of_three_off_bad_set`,
fed from the FIFTH family: a joint draw outside it forces the same three-way
disjunction, for a constants column the forger chose after seeing the first
`cut` gate coordinates.

Residues R1/R2/R3 of the adopted `OpeningBinding` still sit inside branches (A)
and (B); this is not a probability statement about any run.  And `hnondeg` is a
REAL hypothesis: for the escaping column of §5c it is false at every gate point,
so no disjunction is forced against that forger. -/
theorem adaptive_column_forgery_forces_one_of_three (e : Verifier.Engine)
    (pin : Verifier.Pinned) (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (idx cut : Nat) (colOf : List Element → List Element) (committedCol : List Element)
    (truths : List (List Element)) (w : JointChallengeSpace.JointSpace vc.degreeBits)
    (hidx : idx < vc.numConstants)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsProvenance.ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? idx
      = some (colOf ((TranscriptProvenance.gatePointColumn e vc p).take cut)))
    (hcc : (committedBy pin.preprocessedRoot).get? idx = some committedCol)
    (hcolWidth : (colOf ((TranscriptProvenance.gatePointColumn e vc p).take cut)).length
      = 2 ^ (TranscriptProvenance.gatePointColumn e vc p).length)
    (hwidth : (TranscriptProvenance.gatePointColumn e vc p).length = vc.degreeBits)
    (hdrawn : JointChallengeSpace.DrawnAt vc.degreeBits w
      (JointChallengeSpace.gateProj vc.degreeBits)
      (ConditionalSoundness.gateLaneOf e vc p truths) 0)
    (hnondeg : ¬ ZeroCheckSemantics.CubeZero (vc.degreeBits - cut)
      (bindPrefix ((TranscriptProvenance.gatePointColumn e vc p).take cut)
        (GatePointZeroCheck.diffColumn
          (colOf ((TranscriptProvenance.gatePointColumn e vc p).take cut)) committedCol)))
    (hgood : w ∉ adaptiveAgreementEvent vc.degreeBits cut colOf committedCol) :
    p.preprocessedRoot ≠ pin.preprocessedRoot ∨
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols :=
  GatePointZeroCheck.column_forgery_forces_one_of_three_off_bad_set e pin vc p s0 k cols
    committedBy idx _ committedCol hidx hbind hcols hcol hcc hcolWidth
    (gate_point_off_agreement_set_of_joint e vc p truths cut colOf committedCol w hwidth hdrawn
      hnondeg hgood)

/-! ### 5c. THE RESIDUE OF THE ADAPTIVE READING, AND THE TWO BOUNDARIES OF THE CUT

The mass bound of §5 is a statement about the event of §4, NON-DEGENERACY
CONJUNCT INCLUDED.  This subsection shows that the conjunct is a genuine
restriction on the forger rather than bookkeeping, in the same spirit as the
adopted `ConstantsProvenance.bound_cell_agreement_is_not_column_equality`: it
exhibits, for every `d ≥ 1` and every committed column, an adaptive column that
reads ONE gate coordinate, is a genuine width-`2 ^ d` forgery, agrees at EVERY
gate point, and lies OUTSIDE the fifth family at every gate point -- so the
bound of §5 and the transports of §5b say nothing whatever about it.

The mechanism is one line of algebra.  Bind the head coordinate to the realized
`x0`; the adopted low-bit convention makes the bound value at cube index `k`
equal `(1 - x0) * h (2 * k) + x0 * h (2 * k + 1)`.  Taking the difference family
to be `x0` at even indices and `-(1 - x0)` at odd ones gives
`(1 - x0) * x0 + x0 * (-(1 - x0)) = 0` at every `k`.  So after ONE coordinate the
residual is identically zero on the whole remaining slice, while the column
itself differs from the committed one on the cube.

WHAT THIS DOES AND DOES NOT SAY.  It does NOT contradict any theorem above: §5
bounds the mass of a set, and this construction simply never enters that set.
It says that the correct reading of §1-§5 is the DICHOTOMY of the header --
either the bound difference dies on the realized slice (a structural collision,
forceable by construction, and the residue class R2/R3 must exclude), or the
point falls in a set of mass at most `ChallengeUnionBound.tauTerm d`.  It is NOT
"the density reading now holds with the column chosen adaptively". -/

/-- The escape DIFFERENCE family for a realized head coordinate `x0`: `x0` at the
even cube indices, `-(1 - x0)` at the odd ones. -/
def escapeDiff (x0 : Element) : Nat → Element :=
  fun i => if i % 2 = 0 then x0 else -(1 - x0)

/-- (5c) BINDING ONE COORDINATE KILLS THE ESCAPE FAMILY, at every cube index. -/
theorem bindHead_escapeDiff (x0 : Element) (k : Nat) : bindHead x0 (escapeDiff x0) k = 0 := by
  simp only [bindHead, escapeDiff]
  have h0 : (2 * k) % 2 = 0 := by omega
  have h1 : ¬ ((2 * k + 1) % 2 = 0) := by omega
  rw [if_pos h0, if_neg h1]
  ring

/-- The escape COLUMN: the committed column plus the escape difference, at the
width `2 ^ d` the composed theorem of §5b asks for. -/
def escapeCol (cc : List Element) (d : Nat) (x0 : Element) : List Element :=
  List.ofFn (fun i : Fin (2 ^ d) => cc.getD i 0 + escapeDiff x0 i)

theorem getD_ofFn_lt {n : Nat} (f : Fin n → Element) (i : Nat) (h : i < n) :
    (List.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  have hget : (List.ofFn f)[i]? = some (f ⟨i, h⟩) := by
    rw [List.getElem?_ofFn, List.ofFnNthVal, dif_pos h]
  show ((List.ofFn f).get? i).getD 0 = f ⟨i, h⟩
  rw [List.get?_eq_getElem?, hget]
  rfl

theorem escapeCol_length (cc : List Element) (d : Nat) (x0 : Element) :
    (escapeCol cc d x0).length = 2 ^ d := by
  rw [escapeCol, List.length_ofFn]

theorem diff_escapeCol (cc : List Element) (d : Nat) (x0 : Element) (i : Nat) (hi : i < 2 ^ d) :
    GatePointZeroCheck.diffColumn (escapeCol cc d x0) cc i = escapeDiff x0 i := by
  rw [GatePointZeroCheck.diffColumn, escapeCol, getD_ofFn_lt _ i hi]
  ring

/-- (5c) AFTER ONE COORDINATE THE RESIDUAL IS IDENTICALLY ZERO on the whole
remaining cube -- the exact negation of the non-degeneracy conjunct of §4 at
`cut = 1`. -/
theorem escape_cubeZero (cc : List Element) (d : Nat) (hd : 1 ≤ d) (x0 : Element) :
    ZeroCheckSemantics.CubeZero (d - 1)
      (bindPrefix [x0] (GatePointZeroCheck.diffColumn (escapeCol cc d x0) cc)) := by
  intro k hk
  rw [bindPrefix_cons, bindPrefix_nil]
  have h2 : 2 ^ d = 2 * 2 ^ (d - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hk0 : 2 * k < 2 ^ d := by omega
  have hk1 : 2 * k + 1 < 2 ^ d := by omega
  have := bindHead_escapeDiff x0 k
  simp only [bindHead] at this ⊢
  rw [diff_escapeCol cc d x0 _ hk0, diff_escapeCol cc d x0 _ hk1]
  exact this

/-- (5c) THE ESCAPE COLUMN IS A REAL FORGERY: it differs from the committed
column on the cube, in the adopted `GatePointZeroCheck.ColumnsDifferOnCube`
sense. -/
theorem escape_differs (cc : List Element) (d : Nat) (hd : 1 ≤ d) (x0 : Element) :
    GatePointZeroCheck.ColumnsDifferOnCube d (escapeCol cc d x0) cc := by
  have h2 : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
  by_cases hx : x0 = 0
  · refine ⟨1, by omega, ?_⟩
    rw [escapeCol, getD_ofFn_lt _ 1 (by omega)]
    simp only [escapeDiff, hx, Nat.one_mod, ↓reduceIte]
    intro h
    have : (1 : Element) = 0 := by linear_combination -h
    exact one_ne_zero this
  · refine ⟨0, by omega, ?_⟩
    rw [escapeCol, getD_ofFn_lt _ 0 (by omega)]
    simp only [escapeDiff, Nat.zero_mod, ↓reduceIte]
    intro h
    exact hx (by linear_combination h)

theorem extensionOf_eq_zero_of_cubeZero (g : Nat → Element) (tau : List Element)
    (hz : ZeroCheckSemantics.CubeZero tau.length g) :
    ZeroCheckSemantics.extensionOf g tau = 0 := by
  unfold ZeroCheckSemantics.extensionOf
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [List.mem_range] at hi
  rw [hz i hi, mul_zero]

theorem take_one_ofFn (d : Nat) (w : ZeroCheckSemantics.Tuple (d + 1)) :
    (List.ofFn w).take 1 = [w 0] := by
  rw [take_succ_ofFn (d + 1) w 0 (by omega)]
  rfl

/-- **THE ESCAPING ADAPTIVE COLUMN.**  Read the FIRST gate coordinate off the
realized prefix, then emit the escape column for it.  This is a legitimate
`colOf` for `cut = 1`: it reads the prefix and nothing else. -/
def escapeColOf (cc : List Element) (d : Nat) : List Element → List Element :=
  fun pre => escapeCol cc d (pre.headD 0)

theorem escapeColOf_take_one (cc : List Element) (d : Nat)
    (w : ZeroCheckSemantics.Tuple (d + 1)) :
    escapeColOf cc (d + 1) ((List.ofFn w).take 1) = escapeCol cc (d + 1) (w 0) := by
  rw [take_one_ofFn]
  rfl

/-- (5c) **THE FIFTH FAMILY IS EMPTY AGAINST THE ESCAPING FORGER.**  For every
`d ≥ 1`, every committed column and EVERY gate point, the point is NOT in
`adaptiveAgreementSet (d + 1) 1 (escapeColOf …)`.  So
`adaptive_agreement_mass_bound` is vacuous against this forger: it bounds the
mass of a set the forger never enters. -/
theorem escape_not_in_family (cc : List Element) (d : Nat)
    (w : ZeroCheckSemantics.Tuple (d + 1)) :
    w ∉ adaptiveAgreementSet (d + 1) 1 (escapeColOf cc (d + 1)) cc := by
  intro hmem
  rw [mem_adaptiveAgreementSet] at hmem
  obtain ⟨hnz, -⟩ := hmem
  apply hnz
  rw [escapeColOf_take_one, take_one_ofFn]
  exact escape_cubeZero cc (d + 1) (by omega) (w 0)

theorem escapeCol_agrees (cc : List Element) (d : Nat) (w : ZeroCheckSemantics.Tuple (d + 1)) :
    GatePointZeroCheck.PointAgrees (escapeCol cc (d + 1) (w 0)) cc (List.ofFn w) := by
  have hmemiff :=
    GatePointZeroCheck.mem_columnAgreementSet (d + 1) (escapeCol cc (d + 1) (w 0)) cc w
  rw [GatePointZeroCheck.columnAgreementSet_eq_vanishingSet,
    ZeroCheckSemantics.mem_vanishingSet] at hmemiff
  refine hmemiff.mp ?_
  have hsplit : List.ofFn w = [w 0] ++ List.ofFn (fun i : Fin d => w i.succ) := by
    rw [List.ofFn_succ]; rfl
  rw [hsplit, extensionOf_bindPrefix]
  apply extensionOf_eq_zero_of_cubeZero
  rw [List.length_ofFn]
  exact escape_cubeZero cc (d + 1) (by omega) (w 0)

/-- (5c) **THE ESCAPING FORGER AGREES AT EVERY GATE POINT.**  The adopted
`GatePointZeroCheck.PointAgrees` holds at EVERY point, not merely on a small
set: the supplied column's fully bound cell equals the committed column's
everywhere. -/
theorem escape_agrees_everywhere (cc : List Element) (d : Nat)
    (w : ZeroCheckSemantics.Tuple (d + 1)) :
    GatePointZeroCheck.PointAgrees (escapeColOf cc (d + 1) ((List.ofFn w).take 1)) cc
      (List.ofFn w) := by
  rw [escapeColOf_take_one]
  exact escapeCol_agrees cc d w

/-- (5c) **AND IT IS A GENUINE FORGERY.**  The supplied column differs from the
committed one on the cube, so this is not the trivial `col = committedCol`
case. -/
theorem escape_is_a_genuine_forgery (cc : List Element) (d : Nat)
    (w : ZeroCheckSemantics.Tuple (d + 1)) :
    GatePointZeroCheck.ColumnsDifferOnCube (d + 1)
      (escapeColOf cc (d + 1) ((List.ofFn w).take 1)) cc := by
  rw [escapeColOf_take_one]
  exact escape_differs cc (d + 1) (by omega) (w 0)

/-- (5c) The supplied column has exactly the width the `hcolWidth` hypothesis of
the composed theorem of §5b asks for, so nothing in that theorem's shape rules
this forger out. -/
theorem escape_has_the_committed_width (cc : List Element) (d : Nat)
    (w : ZeroCheckSemantics.Tuple (d + 1)) :
    (escapeColOf cc (d + 1) ((List.ofFn w).take 1)).length = 2 ^ (d + 1) := by
  rw [escapeColOf_take_one, escapeCol_length]

/-- (5c) **THE SAME ESCAPE READ THROUGH THE MODULE'S OWN TRANSPORT HYPOTHESIS.**
The `hnondeg` argument of `gate_point_off_adaptive_agreement_of_joint`,
`gate_point_off_agreement_set_of_joint` and
`adaptive_column_forgery_forces_one_of_three` is FALSE for the escaping column,
at any gate point column of width `d + 1`.  Those three theorems therefore have
NO CONTENT against this forger; excluding it is the job of residues R2/R3, not
of the mass bound. -/
theorem escape_kills_hnondeg (cc : List Element) (d : Nat) (point : List Element)
    (hlen : point.length = d + 1) :
    ¬ ¬ ZeroCheckSemantics.CubeZero ((d + 1) - 1)
      (bindPrefix (point.take 1)
        (GatePointZeroCheck.diffColumn (escapeColOf cc (d + 1) (point.take 1)) cc)) := by
  intro h
  apply h
  obtain ⟨x0, rest, rfl⟩ : ∃ x0 rest, point = x0 :: rest := by
    cases point with
    | nil => simp at hlen
    | cons x0 rest => exact ⟨x0, rest, rfl⟩
  show ZeroCheckSemantics.CubeZero ((d + 1) - 1)
    (bindPrefix [x0] (GatePointZeroCheck.diffColumn (escapeCol cc (d + 1) x0) cc))
  exact escape_cubeZero cc (d + 1) (by omega) x0

/-- (5c) **THE UPPER BOUNDARY OF THE CUT: at `cut = d` THE EVENT IS EMPTY**, for
EVERY `colOf` and every committed column.  Once all `d` coordinates are read
there is no remaining cube, and agreement at the point IS degeneracy of the
bound difference.  So `adaptive_agreement_mass_bound` at `cut = d` is a bound on
the empty set -- vacuous, as the header says. -/
theorem cut_eq_d_empty (d : Nat) (colOf : List Element → List Element) (cc : List Element)
    (w : ZeroCheckSemantics.Tuple d) : w ∉ adaptiveAgreementSet d d colOf cc := by
  intro hmem
  rw [mem_adaptiveAgreementSet] at hmem
  obtain ⟨hnz, hagree⟩ := hmem
  apply hnz
  have htake : (List.ofFn w).take d = List.ofFn w :=
    List.take_all_of_le (by rw [List.length_ofFn])
  rw [htake] at hagree
  rw [htake, Nat.sub_self]
  intro j hj
  simp only [pow_zero] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  have hvan : ZeroCheckSemantics.extensionOf
      (GatePointZeroCheck.diffColumn (colOf (List.ofFn w)) cc) (List.ofFn w) = 0 := by
    have hmem : w ∈ GatePointZeroCheck.columnAgreementSet d (colOf (List.ofFn w)) cc :=
      (GatePointZeroCheck.mem_columnAgreementSet d _ cc w).mpr hagree
    rw [GatePointZeroCheck.columnAgreementSet_eq_vanishingSet,
      ZeroCheckSemantics.mem_vanishingSet] at hmem
    exact hmem
  have hsplit := extensionOf_bindPrefix (List.ofFn w) []
    (GatePointZeroCheck.diffColumn (colOf (List.ofFn w)) cc)
  rw [List.append_nil, ZeroCheckSemantics.extensionOf_nil] at hsplit
  rw [← hsplit]
  exact hvan

/-- (5c) **THE LOWER BOUNDARY OF THE CUT: at `cut = 0` WITH A CONSTANT `colOf`
THE EVENT IS EXACTLY THE ADOPTED FIXED-COLUMN READING** -- the conjunction of
the adopted `GatePointZeroCheck.ColumnsDifferOnCube` and membership in the
adopted `GatePointZeroCheck.columnAgreementSet`.  So §1-§5 do specialize to the
adopted `GatePointZeroCheck` statement, and the two boundaries above bracket
everything the `cut` parameter can express. -/
theorem cut_zero_is_fixed_column (d : Nat) (col cc : List Element)
    (w : ZeroCheckSemantics.Tuple d) :
    w ∈ adaptiveAgreementSet d 0 (fun _ => col) cc ↔
      (GatePointZeroCheck.ColumnsDifferOnCube d col cc
        ∧ w ∈ GatePointZeroCheck.columnAgreementSet d col cc) := by
  rw [mem_adaptiveAgreementSet, GatePointZeroCheck.mem_columnAgreementSet]
  simp only [List.take_zero, bindPrefix_nil, Nat.sub_zero]
  constructor
  · rintro ⟨hnz, hag⟩
    refine ⟨?_, hag⟩
    by_contra hnd
    apply hnz
    intro j hj
    by_contra hne
    exact hnd ⟨j, hj, fun h => hne (by rw [GatePointZeroCheck.diffColumn, h, sub_self])⟩
  · rintro ⟨⟨j, hj, hne⟩, hag⟩
    refine ⟨fun hz => hne ?_, hag⟩
    have := hz j hj
    rw [GatePointZeroCheck.diffColumn] at this
    exact sub_eq_zero.mp this

/-! ## 6. The frozen `Lane`

The adopted `OuterSequentialConditioning.Lane.step` PREPENDS the realized
challenge to the argument of the previous message function, so after `j`
scheduled coordinates the argument list has length `j`.  On the adopted
interleaved schedule [log 0, gate 0, log 1, gate 1, …] a lane sees TWO
coordinates per coupled round, so `length / 2` is the ROUND INDEX.

`frozenLane` is therefore a `Lane` whose `message` and `truth` READ NOTHING OF
THE REALIZED VALUES -- only how many coordinates have gone by -- and simply
replay the messages of a fixed executed lane `rs`.  Its CLAIMS, however, advance
by the adopted `OuterRound.evaluate` at the DRAW's own coordinate values.  That
is exactly the mismatch the adopted `OuterSequentialConditioning` header names;
§7 shows the mismatch disappears at a draw that encodes the run. -/

/-- The ROUND INDEX of a prefix on the adopted interleaved schedule: two
scheduled coordinates per coupled round.  Written structurally rather than as
`xs.length / 2` so that every reduction below stays a cheap pattern match. -/
def halfLength : List Element → Nat
  | [] => 0
  | [_] => 0
  | _ :: _ :: xs => halfLength xs + 1

/-- A `Lane` whose messages are functions of the ROUND INDEX only. -/
def frozenLane (rs : List ConditionalSoundness.LaneRound) (a b : Element) (own : Bool) :
    OuterSequentialConditioning.Lane where
  message := fun xs =>
    ((rs.get? (halfLength xs)).map ConditionalSoundness.LaneRound.message).getD []
  truth := fun xs =>
    ((rs.get? (halfLength xs)).map ConditionalSoundness.LaneRound.truth).getD []
  claim := a
  truthClaim := b
  ownsNext := own

/-- Field-by-field equality for the adopted `Lane` structure. -/
theorem lane_eq (L M : OuterSequentialConditioning.Lane)
    (h1 : L.message = M.message) (h2 : L.truth = M.truth) (h3 : L.claim = M.claim)
    (h4 : L.truthClaim = M.truthClaim) (h5 : L.ownsNext = M.ownsNext) : L = M := by
  cases L
  cases M
  simp only [OuterSequentialConditioning.Lane.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- (6) ONE COUPLED ROUND OF THE INTERLEAVED WALK, FOR A LANE THAT OWNS THE
FIRST COORDINATE (the log lane).  The claims advance at the coordinate the lane
owns, with the DRAW's value `x`; the messages shift to the next round. -/
theorem frozen_step_two_owned (r : ConditionalSoundness.LaneRound)
    (rs : List ConditionalSoundness.LaneRound) (a b x y : Element) :
    ((frozenLane (r :: rs) a b true).step x).step y
      = frozenLane rs (OuterRound.evaluate a r.message x)
          (OuterRound.evaluate b r.truth x) true :=
  lane_eq _ _ (funext fun _ => rfl) (funext fun _ => rfl) rfl rfl rfl

/-- (6) THE SAME FOR A LANE THAT OWNS THE SECOND COORDINATE (the gate lane): the
claims advance with the DRAW's value `y` at the coordinate it owns. -/
theorem frozen_step_two_unowned (r : ConditionalSoundness.LaneRound)
    (rs : List ConditionalSoundness.LaneRound) (a b x y : Element) :
    ((frozenLane (r :: rs) a b false).step x).step y
      = frozenLane rs (OuterRound.evaluate a r.message y)
          (OuterRound.evaluate b r.truth y) false :=
  lane_eq _ _ (funext fun _ => rfl) (funext fun _ => rfl) rfl rfl rfl

/-- The adopted `ConditionalSoundness.roundBadSet` does not read the round's
realized challenge: it is a function of the two claims and the two round
messages alone. -/
theorem roundBadSet_ignores_challenge (a b : Element) (r : ConditionalSoundness.LaneRound) :
    ConditionalSoundness.roundBadSet a b ⟨r.message, r.truth, 0⟩
      = ConditionalSoundness.roundBadSet a b r := rfl

/-- (6) THE FROZEN LANE'S OWN BAD SET IS THE ADOPTED ROUND BAD SET, at the
coordinate a log-phase lane owns. -/
theorem frozenLane_badSet_owned (r : ConditionalSoundness.LaneRound)
    (rs : List ConditionalSoundness.LaneRound) (a b : Element) :
    (frozenLane (r :: rs) a b true).badSet = ConditionalSoundness.roundBadSet a b r := by
  have h1 : (frozenLane (r :: rs) a b true).badSet
      = ConditionalSoundness.roundBadSet a b ⟨r.message, r.truth, 0⟩ := by
    rw [OuterSequentialConditioning.Lane.badSet]
    exact if_pos rfl
  rw [h1, roundBadSet_ignores_challenge]

/-- (6) THE SAME at the coordinate a gate-phase lane owns, one step into the
interleaved walk. -/
theorem frozenLane_badSet_unowned (r : ConditionalSoundness.LaneRound)
    (rs : List ConditionalSoundness.LaneRound) (a b : Element)
    (v : OuterChallenge.DigestTriple) :
    (OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b false) v).badSet
      = ConditionalSoundness.roundBadSet a b r := by
  have h1 : (OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b false) v).badSet
      = ConditionalSoundness.roundBadSet a b ⟨r.message, r.truth, 0⟩ := by
    rw [OuterSequentialConditioning.Lane.badSet]
    exact if_pos rfl
  rw [h1, roundBadSet_ignores_challenge]

theorem frozenLane_laneBad_owned (r : ConditionalSoundness.LaneRound)
    (rs : List ConditionalSoundness.LaneRound) (a b : Element) :
    OuterSequentialConditioning.laneBad (frozenLane (r :: rs) a b true)
      = OuterChallenge.tupleEvent (ConditionalSoundness.roundBadSet a b r) :=
  congrArg OuterChallenge.tupleEvent (frozenLane_badSet_owned r rs a b)

theorem frozenLane_laneBad_unowned (r : ConditionalSoundness.LaneRound)
    (rs : List ConditionalSoundness.LaneRound) (a b : Element)
    (v : OuterChallenge.DigestTriple) :
    OuterSequentialConditioning.laneBad
        (OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b false) v)
      = OuterChallenge.tupleEvent (ConditionalSoundness.roundBadSet a b r) :=
  congrArg OuterChallenge.tupleEvent (frozenLane_badSet_unowned r rs a b v)

/-- The adopted `JointChallengeSpace.laneEvent` recursion, as a rewriting
equation. -/
theorem lane_event_cons (d : Nat) (proj : Nat → JointChallengeSpace.Draw d) (a b : Element)
    (r : ConditionalSoundness.LaneRound) (rs : List ConditionalSoundness.LaneRound) (k : Nat) :
    JointChallengeSpace.laneEvent d proj a b (r :: rs) k
      = JointChallengeSpace.coordEvent d (proj k) (ConditionalSoundness.roundBadSet a b r) ∪
        JointChallengeSpace.laneEvent d proj (OuterRound.evaluate a r.message r.challenge)
          (OuterRound.evaluate b r.truth r.challenge) rs (k + 1) := rfl

/-- The adopted `OuterSequentialConditioning.adaptiveLaneEvent`, as a rewriting
equation on the adopted interleaved schedule. -/
theorem adaptiveLaneEvent_eq (d : Nat) (L : OuterSequentialConditioning.Lane) :
    OuterSequentialConditioning.adaptiveLaneEvent d L
      = OuterSequentialConditioning.adaptiveEvent OuterSequentialConditioning.laneBad
          OuterSequentialConditioning.laneStep L
          (OuterSequentialConditioning.roundCoords d 0 d) := rfl

/-- The digest-level bad set of a lane that does not own the coordinate is
empty.  Obtained from the ADOPTED
`OuterSequentialConditioning.laneBad_card_of_inactive`, so that no tactic ever
elaborates `Finset.univ` on `OuterChallenge.DigestTriple`. -/
theorem laneBad_eq_empty_of_inactive (L : OuterSequentialConditioning.Lane)
    (h : L.ownsNext = false) : OuterSequentialConditioning.laneBad L = ∅ :=
  Finset.card_eq_zero.mp
    (Nat.le_zero.mp (OuterSequentialConditioning.laneBad_card_of_inactive L h))

theorem not_mem_laneBad_of_inactive (L : OuterSequentialConditioning.Lane)
    (h : L.ownsNext = false) (v : OuterChallenge.DigestTriple) :
    v ∉ OuterSequentialConditioning.laneBad L := by
  rw [laneBad_eq_empty_of_inactive L h]
  exact Finset.not_mem_empty _

/-! ## 7. The frozen `Lane` event IS the adopted `laneEvent`, at an encoding draw -/

/-- (7) THE LOG LANE, ROUND BY ROUND.  On the adopted interleaved schedule, the
adaptive event of the frozen log `Lane` and the adopted `laneEvent` of the run's
log lane are the same event, PROVIDED the draw carries the run's own log
challenges at the log coordinates -- the adopted
`JointChallengeSpace.DrawEncodesRun.logDrawn`. -/
theorem frozen_log_walk (d : Nat) (w : JointChallengeSpace.JointSpace d) :
    ∀ (rs : List ConditionalSoundness.LaneRound) (a b : Element) (k : Nat),
      JointChallengeSpace.DrawnAt d w (JointChallengeSpace.logProj d) rs k →
      (w ∈ OuterSequentialConditioning.adaptiveEvent OuterSequentialConditioning.laneBad
            OuterSequentialConditioning.laneStep (frozenLane rs a b true)
            (OuterSequentialConditioning.roundCoords d k rs.length)
        ↔ w ∈ JointChallengeSpace.laneEvent d (JointChallengeSpace.logProj d) a b rs k)
  | [], a, b, k, _ => by
      show (w ∈ OuterSequentialConditioning.adaptiveEvent OuterSequentialConditioning.laneBad
        OuterSequentialConditioning.laneStep (frozenLane [] a b true) []) ↔ _
      rw [OuterSequentialConditioning.adaptiveEvent_nil, JointChallengeSpace.lane_event_nil]
  | r :: rs, a, b, k, hdrawn => by
      have hx : r.challenge = OuterChallenge.reduceTriple (w (JointChallengeSpace.logProj d k)) :=
        hdrawn.1
      have hbad : w (JointChallengeSpace.logProj d k)
            ∈ OuterSequentialConditioning.laneBad (frozenLane (r :: rs) a b true)
          ↔ w ∈ JointChallengeSpace.coordEvent d (JointChallengeSpace.logProj d k)
              (ConditionalSoundness.roundBadSet a b r) := by
        rw [frozenLane_laneBad_owned, JointChallengeSpace.mem_tupleEvent,
          JointChallengeSpace.mem_coordEvent]
      have hstep2 : OuterSequentialConditioning.laneStep
            (OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b true)
              (w (JointChallengeSpace.logProj d k)))
            (w (JointChallengeSpace.gateProj d k))
          = frozenLane rs (OuterRound.evaluate a r.message r.challenge)
              (OuterRound.evaluate b r.truth r.challenge) true := by
        rw [hx]
        exact frozen_step_two_owned r rs a b _ _
      have hinactive : (OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b true)
          (w (JointChallengeSpace.logProj d k))).ownsNext = false := rfl
      have hrec := frozen_log_walk d w rs (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) (k + 1) hdrawn.2
      show (w ∈ OuterSequentialConditioning.adaptiveEvent OuterSequentialConditioning.laneBad
        OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b true)
        (OuterSequentialConditioning.roundCoords d k (rs.length + 1))) ↔ _
      rw [OuterSequentialConditioning.roundCoords,
        OuterSequentialConditioning.mem_adaptiveEvent_cons,
        OuterSequentialConditioning.mem_adaptiveEvent_cons, hbad, hstep2, hrec,
        lane_event_cons, Finset.mem_union]
      exact or_congr Iff.rfl (or_iff_right (not_mem_laneBad_of_inactive _ hinactive _))

/-- (7) THE GATE LANE, ROUND BY ROUND.  Same statement for the lane that owns the
ODD coordinates of the adopted interleaved schedule, under the adopted
`JointChallengeSpace.DrawEncodesRun.gateDrawn`. -/
theorem frozen_gate_walk (d : Nat) (w : JointChallengeSpace.JointSpace d) :
    ∀ (rs : List ConditionalSoundness.LaneRound) (a b : Element) (k : Nat),
      JointChallengeSpace.DrawnAt d w (JointChallengeSpace.gateProj d) rs k →
      (w ∈ OuterSequentialConditioning.adaptiveEvent OuterSequentialConditioning.laneBad
            OuterSequentialConditioning.laneStep (frozenLane rs a b false)
            (OuterSequentialConditioning.roundCoords d k rs.length)
        ↔ w ∈ JointChallengeSpace.laneEvent d (JointChallengeSpace.gateProj d) a b rs k)
  | [], a, b, k, _ => by
      show (w ∈ OuterSequentialConditioning.adaptiveEvent OuterSequentialConditioning.laneBad
        OuterSequentialConditioning.laneStep (frozenLane [] a b false) []) ↔ _
      rw [OuterSequentialConditioning.adaptiveEvent_nil, JointChallengeSpace.lane_event_nil]
  | r :: rs, a, b, k, hdrawn => by
      have hx : r.challenge = OuterChallenge.reduceTriple (w (JointChallengeSpace.gateProj d k)) :=
        hdrawn.1
      have hinactive : (frozenLane (r :: rs) a b false).ownsNext = false := rfl
      have hbad : w (JointChallengeSpace.gateProj d k)
            ∈ OuterSequentialConditioning.laneBad
                (OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b false)
                  (w (JointChallengeSpace.logProj d k)))
          ↔ w ∈ JointChallengeSpace.coordEvent d (JointChallengeSpace.gateProj d k)
              (ConditionalSoundness.roundBadSet a b r) := by
        rw [frozenLane_laneBad_unowned, JointChallengeSpace.mem_tupleEvent,
          JointChallengeSpace.mem_coordEvent]
      have hstep2 : OuterSequentialConditioning.laneStep
            (OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b false)
              (w (JointChallengeSpace.logProj d k)))
            (w (JointChallengeSpace.gateProj d k))
          = frozenLane rs (OuterRound.evaluate a r.message r.challenge)
              (OuterRound.evaluate b r.truth r.challenge) false := by
        rw [hx]
        exact frozen_step_two_unowned r rs a b _ _
      have hrec := frozen_gate_walk d w rs (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) (k + 1) hdrawn.2
      show (w ∈ OuterSequentialConditioning.adaptiveEvent OuterSequentialConditioning.laneBad
        OuterSequentialConditioning.laneStep (frozenLane (r :: rs) a b false)
        (OuterSequentialConditioning.roundCoords d k (rs.length + 1))) ↔ _
      rw [OuterSequentialConditioning.roundCoords,
        OuterSequentialConditioning.mem_adaptiveEvent_cons,
        OuterSequentialConditioning.mem_adaptiveEvent_cons, hbad, hstep2, hrec,
        lane_event_cons, Finset.mem_union]
      exact or_iff_right (not_mem_laneBad_of_inactive _ hinactive _)

/-- (7) **THE LANE-LEVEL FROZEN COMPARISON, THE GAP THE ADOPTED
`OuterSequentialConditioning` LEAVES OPEN.**

For a draw satisfying the adopted `JointChallengeSpace.DrawEncodesRun`, the
adopted `OuterSequentialConditioning.adaptiveLaneEvent` of the FROZEN `Lane`
built from a run's executed lane -- a `Lane` whose messages read nothing of the
realized values, only the round index, yet whose claims advance along the
DRAW's own coordinates -- and the adopted `JointChallengeSpace.laneEvent` of
that same executed lane are THE SAME EVENT.  Both halves are two-sided IFFs.

EXACTLY WHAT IS PROVED, AND NOTHING MORE:

* ONE LANE AT A TIME.  The log half uses only `DrawEncodesRun.logDrawn`, the
  gate half only `gateDrawn`.  No claim is made about the UNION of the two
  frozen lanes, nor about any joint event.
* THE LANE MUST HAVE FULL LENGTH `degreeBits` (`hlogLen` / `hgateLen`), because
  the adopted `adaptiveLaneEvent` walks the whole adopted `outerCoords`
  schedule.  Under the adopted `Integrated.verify` acceptance both follow from
  `ConditionalSoundness.lane_length_of_shape`; they are hypotheses here so that
  no acceptance is smuggled in.
* THE CORRESPONDENCE IS PROVED ONLY AT AN ENCODING DRAW.  Away from it the
  frozen `Lane` still advances its claims by the DRAW's coordinate values while
  the adopted `laneEvent` advances by the RUN's realized ones, so the two events
  NEED NOT COINCIDE.  Nothing here says they always differ -- for `a = b` both
  are empty, and other coincidences are possible; the encoding hypothesis is
  what makes the identification unconditional.
* `DrawEncodesRun` IS A COORDINATE STATEMENT, INHABITED FOR EVERY HASH (adopted
  `draw_encodes_run_inhabited`).  Nothing here says the encoding draw is
  distributed by `jointProbability`. -/
theorem frozen_lane_matches_laneEvent_at_encoding_draw (hash : TranscriptProvenance.Hash)
    (e : Verifier.Engine) (vc : Verifier.Config) (p : Verifier.Proof)
    (logTruths gateTruths : List (List Element))
    (draw : JointChallengeSpace.JointSpace vc.degreeBits)
    (hdraw : JointChallengeSpace.DrawEncodesRun hash e vc p logTruths gateTruths draw)
    (hlogLen : (ConditionalSoundness.logLaneOf e vc p logTruths).length = vc.degreeBits)
    (hgateLen : (ConditionalSoundness.gateLaneOf e vc p gateTruths).length = vc.degreeBits)
    (a b : Element) :
    (draw ∈ OuterSequentialConditioning.adaptiveLaneEvent vc.degreeBits
        (frozenLane (ConditionalSoundness.logLaneOf e vc p logTruths) a b true)
      ↔ draw ∈ JointChallengeSpace.laneEvent vc.degreeBits
          (JointChallengeSpace.logProj vc.degreeBits) a b
          (ConditionalSoundness.logLaneOf e vc p logTruths) 0)
    ∧ (draw ∈ OuterSequentialConditioning.adaptiveLaneEvent vc.degreeBits
        (frozenLane (ConditionalSoundness.gateLaneOf e vc p gateTruths) a b false)
      ↔ draw ∈ JointChallengeSpace.laneEvent vc.degreeBits
          (JointChallengeSpace.gateProj vc.degreeBits) a b
          (ConditionalSoundness.gateLaneOf e vc p gateTruths) 0) := by
  constructor
  · have h := frozen_log_walk vc.degreeBits draw
      (ConditionalSoundness.logLaneOf e vc p logTruths) a b 0 hdraw.logDrawn
    rw [hlogLen] at h
    rw [adaptiveLaneEvent_eq]
    exact h
  · have h := frozen_gate_walk vc.degreeBits draw
      (ConditionalSoundness.gateLaneOf e vc p gateTruths) a b 0 hdraw.gateDrawn
    rw [hgateLen] at h
    rw [adaptiveLaneEvent_eq]
    exact h

/-! ## 8. The envelope figure, restated with its warnings -/

theorem outerTerm_nonneg (d q : Nat) : (0 : ℚ) ≤ ChallengeUnionBound.outerTerm d q :=
  mul_nonneg (Nat.cast_nonneg _) ChallengeUnionBound.digest_ratio_cube_nonneg

theorem alphaTerm_nonneg (rows constraints : Nat) :
    (0 : ℚ) ≤ ChallengeUnionBound.alphaTerm rows constraints :=
  mul_nonneg (Nat.cast_nonneg _) ChallengeUnionBound.digest_ratio_cube_nonneg

/-- (8) The fifth family's term is ALREADY one of the adopted `combinedBound`'s
three summands -- `combinedBound` counts the gate TAU column with the same
`tauTerm`.  So adding a second copy at most doubles the bound. -/
theorem tauTerm_le_combinedBound (d q constraints : Nat) :
    ChallengeUnionBound.tauTerm d ≤ ChallengeUnionBound.combinedBound d q d constraints := by
  rw [ChallengeUnionBound.combinedBound]
  have h1 := outerTerm_nonneg d q
  have h2 := alphaTerm_nonneg (2 ^ d) constraints
  linarith

/-- (8) **THE ENVELOPE FIGURE IS UNCHANGED TO WITHIN ONE BIT.**  At the envelope
extremes (`degreeBits = 13`, `quotientDegree = 8`, `numGateConstraints = 123`)
the FIVE-family bound `combinedBound + tauTerm 13` is at most `2^-171`: the
fifth family costs strictly less than one bit, because `tauTerm 13` is itself
one of `combinedBound`'s three summands (and is itself around `2^-188`, far
below the other two).

`2^-171` IS NOT THE SYSTEM'S SOUNDNESS ERROR, and neither is `2^-172`.  Both
omit the WHIR/Merkle term, which dominates; the deployed design point is around
100 bits, so quoting either as the wire-v3 soundness error would be wrong by
roughly seventy bits. -/
theorem combined_with_agreement_at_extremes :
    ChallengeUnionBound.combinedBound 13 8 13 123 + ChallengeUnionBound.tauTerm 13
      ≤ (1 : ℚ) / 2 ^ 171 := by
  have h1 := ChallengeUnionBound.combined_bound_at_extremes_numeric
  have h2 := tauTerm_le_combinedBound 13 8 123
  have h3 : (1 : ℚ) / 2 ^ 172 + (1 : ℚ) / 2 ^ 172 = (1 : ℚ) / 2 ^ 171 := by norm_num
  linarith

/-- (8) THE COMPLEMENT FORM, on the adopted joint law: with the fifth family
added, the good event still has mass at least `1 - 2^-171`. -/
theorem good_event_with_agreement_mass_at_extremes
    (logLane gateLane : OuterSequentialConditioning.Lane) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (cut : Nat)
    (colOf : List Element → List Element) (committedCol : List Element)
    (hlog : logLane.Bounded 5) (hlogOwns : logLane.ownsNext = true)
    (hgate : gateLane.Bounded (8 + 2)) (hgateOwns : gateLane.ownsNext = false)
    (hlen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hcut : cut ≤ 13) :
    1 - (1 : ℚ) / 2 ^ 171
      ≤ JointChallengeSpace.jointProbability 13 (JointChallengeSpace.goodEvent 13
          (OuterSequentialConditioning.adaptiveJointBadEvent 13 logLane gateLane g (2 ^ 13)
              coeffsOf
            ∪ adaptiveAgreementEvent 13 cut colOf committedCol)) := by
  have h := adaptive_joint_union_bound_with_agreement 13 8 123 cut logLane gateLane g coeffsOf
    colOf committedCol hlog hlogOwns hgate hgateOwns hlen hcut
  have hnum := combined_with_agreement_at_extremes
  rw [JointChallengeSpace.goodEvent, JointChallengeSpace.joint_probability_compl]
  linarith

/-! ## 9. Small examples: the statements are not vacuous

At `d = 1` only, so that no tuple `Finset` is ever instantiated at a literal
arity `≥ 2`.  The columns are the ADOPTED residue witnesses of
`ConstantsProvenance`, reused through the adopted `GatePointZeroCheck.Example`. -/

namespace Example

open GatePointZeroCheck.Example

/-- The adopted residue columns differ on the one-variable cube, so the
difference column is not cube-zero -- the non-degeneracy conjunct of §4 at
`cut = 0`. -/
theorem residue_not_cubeZero : ¬ ZeroCheckSemantics.CubeZero 1
    (GatePointZeroCheck.diffColumn columnA columnB) := by
  obtain ⟨j, hj, hne⟩ :=
    GatePointZeroCheck.diffColumn_ne_zero 1 columnA columnB columns_differ_on_cube
  intro hz
  exact hne (hz j hj)

/-- (9) A COLUMN SUPPLIED WITH NO ADAPTIVITY (`cut = 0`) AT THE ADOPTED RESIDUE
WITNESS: the point `1` really is in the adaptive agreement event, so §4 is not
vacuous. -/
theorem residue_point_agrees : GatePointZeroCheck.PointAgrees columnA columnB
    (List.ofFn (fun _ : Fin 1 => (1 : Element))) := by
  show ZeroCheckSemantics.extension columnA (List.ofFn (fun _ : Fin 1 => (1 : Element)))
    = ZeroCheckSemantics.extension columnB (List.ofFn (fun _ : Fin 1 => (1 : Element)))
  have hofn : List.ofFn (fun _ : Fin 1 => (1 : Element)) = [1] := by simp
  rw [hofn, ← GatePointZeroCheck.cell_bindColumn_eq_extension_of_width [1] columnA widthA,
    ← GatePointZeroCheck.cell_bindColumn_eq_extension_of_width [1] columnB widthB]
  exact congrArg NormTerminalBinding.cell ConstantsProvenance.residue_columns_share_bound_cell

/-- (9) A COLUMN SUPPLIED WITH NO ADAPTIVITY (`cut = 0`) AT THE ADOPTED RESIDUE
WITNESS: the point `1` really is in the adaptive agreement event, so §4 is not
vacuous. -/
theorem one_mem_adaptiveAgreementSet :
    (fun _ : Fin 1 => (1 : Element))
      ∈ adaptiveAgreementSet 1 0 (fun _ => columnA) columnB := by
  rw [mem_adaptiveAgreementSet]
  exact ⟨residue_not_cubeZero, residue_point_agrees⟩

/-- (9) THE CONTAINMENT OF §4 APPLIES AT THAT WITNESS: the whole adaptive
agreement event of these two columns sits inside the adopted `prefixEvent` of
the sequential family, so the point above is charged to one of the coordinates.
Stated as the SUBSET, not as a membership: no `Finset` over the tuple space is
ever forced to reduce. -/
theorem example_agreement_subset :
    adaptiveAgreementSet 1 0 (fun _ => columnA) columnB
      ⊆ OuterSequentialConditioning.prefixEvent 1
          (sequentialAgreementBad 1 0 (fun _ => columnA) columnB) :=
  agreement_subset_prefixEvent 1 0 (Nat.zero_le 1) (fun _ => columnA) columnB

/-- (9) THE PER-COORDINATE FIBRE AT THE FIRST COORDINATE IS AT MOST ONE POINT,
at that witness. -/
theorem example_fibre_le_one :
    (sequentialAgreementBad 1 0 (fun _ => columnA) columnB 0 []).card ≤ 1 :=
  sequential_agreement_fibre_le_one 1 0 (fun _ => columnA) columnB 0 []

/-- (9) THE MASS BOUND AT THAT WITNESS: the adopted `tauTerm 1`, the same number
the adopted `GatePointZeroCheck.Example.example_mass_bound` gets for a column
fixed in advance. -/
theorem example_adaptive_mass_bound :
    ChallengeUnionBound.uniformProductProbability 1
        (adaptiveAgreementSet 1 0 (fun _ => columnA) columnB)
      ≤ ChallengeUnionBound.tauTerm 1 :=
  adaptive_agreement_mass_bound 1 0 (by omega) (fun _ => columnA) columnB

/-- (9) THE SAME ON THE ADOPTED JOINT SPACE, at `degreeBits = 1`. -/
theorem example_adaptive_joint_mass_bound :
    JointChallengeSpace.jointProbability 1 (adaptiveAgreementEvent 1 0 (fun _ => columnA) columnB)
      ≤ ChallengeUnionBound.tauTerm 1 :=
  adaptive_agreement_joint_mass_bound 1 0 (by omega) (fun _ => columnA) columnB

/-- (9) AN ADAPTIVE SUPPLIED COLUMN IS ALLOWED: at `cut = 1` the column may read
the FIRST gate coordinate.  The bound is the same `tauTerm 1`; what changes is
which forgers it covers. -/
theorem example_adaptive_mass_bound_at_cut_one (colOf : List Element → List Element) :
    ChallengeUnionBound.uniformProductProbability 1
        (adaptiveAgreementSet 1 1 colOf columnB)
      ≤ ChallengeUnionBound.tauTerm 1 :=
  adaptive_agreement_mass_bound 1 1 (by omega) colOf columnB

/-- (9) THE FROZEN LANE READS NOTHING OF THE REALIZED VALUES: after two
scheduled coordinates its message is still round `0`'s, whatever was drawn.
Contrast the adopted `OuterSequentialConditioning.echoLane`, whose message IS
the earlier realized challenge. -/
theorem frozenLane_ignores_values (r : ConditionalSoundness.LaneRound)
    (rs : List ConditionalSoundness.LaneRound) (a b : Element) (x y : Element) :
    ((frozenLane (r :: rs) a b true).step x).step y
      = frozenLane rs (OuterRound.evaluate a r.message x)
          (OuterRound.evaluate b r.truth x) true :=
  frozen_step_two_owned r rs a b x y

/-- (9) THE INTERLEAVED SCHEDULE OF ONE ROUND, restated: the frozen comparison
of §7 walks `log 0, gate 0`, in that order. -/
theorem outerCoords_one_round :
    OuterSequentialConditioning.outerCoords 1
      = [JointChallengeSpace.logProj 1 0, JointChallengeSpace.gateProj 1 0] := rfl

end Example

end Audit.Wire3.AdaptiveAgreementFamily
