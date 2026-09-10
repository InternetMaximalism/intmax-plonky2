import Audit.Wire3.AlphaZeroCheck
import Audit.Wire3.ConditionalSoundness

/-!
# Joining the three challenge bad-event families of the wire-v3 audit

The audit carries three bad-event families that the adopted modules explicitly
say do NOT compose:

* `Audit.Wire3.ConditionalSoundness.badSets` / `BadEventFree`: a
  `List (Finset Element)` of per-round outer-sumcheck agreement sets over
  SINGLE field challenges, with the union bound `bad_sets_union_card` /
  `bad_sets_uniform_sum` and the EXPLICIT uniform law of
  `OuterChallenge.uniformTupleProbability` over the `2^768` digest triples;
* `Audit.Wire3.ZeroCheckSemantics.zeroCheckBadSet n g`: a `Finset (Fin n → Element)`
  over n-TUPLES, with `vanishing_card_bound` (density at most `n / |F|`).
  `ZeroCheckSemantics`'s header says it does not compose with `badSets` because
  the latter ranges over single challenges, and that "an `n`-fold product
  version of `OuterChallenge.tupleEvent` is NOT done here";
* `Audit.Wire3.AlphaZeroCheck.alphaBadSet coeffs`: a `Finset Element` PER ROW of
  the Boolean cube, each row with its own coefficient list, with
  `alphaBadSet_card_bound` (at most `numGateConstraints - 1`, hence at most
  `122`).  `AlphaZeroCheck`'s header says the per-row set is never inserted into
  `badSets` and that no union over the `2^n` rows is taken.

This module supplies exactly those two missing joins and their sum, and nothing
else.

## THE NUMBER PROVED HERE IS NOT THE SYSTEM'S SOUNDNESS ERROR

`combined_bound_at_extremes_numeric` proves the closed-form envelope bound
`combinedBound 13 8 13 123 ≤ 2^(-172)` by exact rational arithmetic.  READ THAT
AS WHAT IT IS.  It covers ONLY (i) the outer sumcheck round-agreement events,
(ii) the gate tau multilinear zero check and (iii) the gate alpha zero check,
each counted under an EXPLICIT IDEAL UNIFORM LAW on an explicit finite space.
It EXCLUDES the entire WHIR/Merkle contribution -- proximity/list decoding, the
query-repetition profile, and Merkle collision resistance -- which is the
DOMINANT term.  The deployed design point is around 100 BITS, not 172.  Quoting
`2^-172` as the wire-v3 soundness error would be wrong by roughly seventy bits.
This is the same warning `ConditionalSoundness`'s header attaches to its `195 *
(⌈2^256/p⌉ / 2^256)^3`, and it applies here with the same force: adding two more
counted families to that number changes which events are covered, not which
events dominate.

## WHAT THE PROBABILITY STATEMENTS ARE, AND ARE NOT

Every mass statement below is COUNTING on an explicit finite sample space,
divided by that space's size.  Specifically:

* the outer term lives on `OuterChallenge.DigestTriple`, the `2^768` triples of
  32-byte digests, under `OuterChallenge.uniformTupleProbability`;
* the tau term lives on `TripleTuple n = Fin n → OuterChallenge.DigestTriple`,
  the `(2^768)^n` n-tuples of digest triples, under
  `uniformProductProbability`, which is the n-fold PRODUCT of that same law;
* the alpha term lives on `OuterChallenge.DigestTriple` again -- the gate alpha
  is ONE Ext3 challenge, i.e. one digest triple.

INDEPENDENCE OF THE n DRAWS IS PART OF THE EXPLICIT IDEAL LAW, NOT A THEOREM
ABOUT KECCAK.  `uniformProductProbability` is the uniform law on the product
space `Fin n → DigestTriple`; that product structure IS the independence
assumption, written down rather than derived.  Nothing here says that the
`degreeBits` gate-tau squeezes the transcript actually performs (adopted
`TranscriptProvenance.gateTauColumn`, counters `12 + 3*degreeBits + 3*i`, with
`gate_alpha` earlier at counter block `9 + 3*degreeBits`) are independent, or
uniform, or unpredictable.  Those are the same Fiat--Shamir obligations
`ConditionalSoundness`'s ASSUMPTIONS 1-3 name and assume; this module discharges
none of them and adds none of its own.

ADAPTIVITY IS NOT ADDRESSED.  As in `ZeroCheckSemantics` and `AlphaZeroCheck`,
`zeroCheckBadSet n g` and each row's `alphaBadSet (coeffsOf i)` are indexed by
the PROVER'S OWN tables.  Reading a membership in them as a probability event
requires a Fiat--Shamir argument fixing those tables by transcript material
preceding the relevant squeeze block.  Not attempted here.

`failure` REMAINS A FREE RATIONAL.  The outer summand is imported from
`ConditionalSoundness.outer_failure_bound`, whose `failure` field is bounded
ABOVE only and never below; `failure := 0, law := 0` satisfies its assumptions.
The combined statement inherits that exactly: it bounds a SUM of one free
rational and two counted masses, and nothing in it lower-bounds anything by a
real failure probability.

## WHAT IS PROVED

1. `productEvent` / `uniformProductProbability` / `product_event_card` /
   `uniform_product_probability_bound`: the n-fold product event and its mass,
   with the per-coordinate reduction fibre bound `fiberCeiling^3` taken
   COORDINATEWISE from the adopted `OuterChallenge.fixed_value_preimage_bound`.
   `tau_product_mass_bound`: composing that with the adopted
   `ZeroCheckSemantics.zeroCheckBadSet_card_bound` gives
   `tauTerm n = n * (|F|^n / |F|) * (⌈2^256/p⌉ / 2^256)^(3n)`.
2. `alphaUnionBadSet` / `alpha_union_card_bound` /
   `alpha_union_configured_card_bound` / `alpha_union_mass_bound`: the union of
   the per-row alpha bad sets over `rows` rows, `card ≤ rows * (L - 1)`, hence
   `≤ 122 * 2^n` at the configured envelope, and its mass under the single
   digest-triple law.  `all_rows_gate_slots_vanish` and
   `all_rows_constraints_vanish_of_tau_and_alpha_union` show that ONE alpha
   outside the union makes EVERY row's adopted `AlphaZeroCheck.gate_slots_vanish`
   conclusion available simultaneously.
3. `combined_union_bound` / `accepted_combined_union_bound`: the union bound for
   the SUM of three separately bounded masses; no joint event or law is
   formalized, so this is not the probability of a disjunction.
4. `envelope_digest_terms_bound` / `combined_bound_at_extremes` /
   `combined_bound_at_extremes_numeric`: the envelope closed form and its exact
   rational evaluation.
5. Examples at `n = 1` only.

## BOUNDARIES

* NOTHING here is a probability statement about Keccak, about the deployed
  transcript, or about any deterministic hash.
* The three events are NEVER shown to be the only bad events, and their
  disjunction is NEVER shown to imply soundness.  There is no theorem of the
  form `accepted ∧ ¬ bad → relation` combining all three lanes; the gate lane
  still has no analogue of `accepted_norm_cube_sum_vanishes` (see
  `ConditionalSoundness`'s "THE GATE LANE IS NOT PROVED").
* No extraction, PCS/WHIR, Merkle, gas, memory-refinement or Rust/Solidity
  compilation claim.
* Tactic note, inherited from `ZeroCheckSemantics` and `AlphaZeroCheck`: no
  tactic may see `Fintype.card Element` or `Finset.univ` on `Element`; all
  arithmetic is routed through the size-generic adopted lemmas, and the only
  numeral evaluation happens in `combined_bound_at_extremes_numeric`, on ℚ
  literals built from `Arithmetic.modulus` and `2 ^ 256`.
* Kernel note: the per-row family is packaged as the named function
  `alphaFamily` rather than an inline lambda, because a beta-redex whose body is
  the noncomputable `AlphaZeroCheck.alphaBadSet` makes kernel defeq checking
  diverge.
-/

set_option maxRecDepth 8000

namespace Audit.Wire3.ChallengeUnionBound
open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The n-fold product of the adopted digest-triple law

The adopted `OuterChallenge` law is uniform on ONE triple of 32-byte digests.
The gate tau column is `degreeBits` SEPARATE Ext3 challenges, i.e. `n` such
triples.  `TripleTuple n` is the explicit finite space of those `n` triples and
`uniformProductProbability` is the uniform law on it; the product structure IS
the independence assumption, not a derived fact. -/

/-- `n` independent digest triples: the explicit finite challenge space of an
`n`-coordinate tau column. -/
abbrev TripleTuple (n : Nat) := Fin n → OuterChallenge.DigestTriple

/-- The coordinatewise adopted reduction: coordinate `i` of the tau tuple is the
adopted `OuterChallenge.reduceTriple` of digest triple `i`. -/
def reduceTuple (n : Nat) (ds : TripleTuple n) : ZeroCheckSemantics.Tuple n :=
  fun i => OuterChallenge.reduceTriple (ds i)

/-- The n-fold analogue of the adopted `OuterChallenge.tupleEvent`: the digest
tuples whose coordinatewise reduction lands in a set of tau tuples. -/
noncomputable def productEvent (n : Nat) (S : Finset (ZeroCheckSemantics.Tuple n)) :
    Finset (TripleTuple n) :=
  open Classical in Finset.univ.filter (fun ds => reduceTuple n ds ∈ S)

theorem mem_productEvent (n : Nat) (S : Finset (ZeroCheckSemantics.Tuple n))
    (ds : TripleTuple n) : ds ∈ productEvent n S ↔ reduceTuple n ds ∈ S := by
  classical
  simp only [productEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The fibre of the coordinatewise reduction over a fixed tau tuple is the
product of the `n` per-coordinate fibres, so the adopted single-coordinate bound
`OuterChallenge.fixed_value_preimage_bound` (`≤ fiberCeiling^3`) raises to the
`n`-th power.  This is where "each `Element` coordinate is the reduction of one
digest triple" enters. -/
theorem fiber_card_bound (n : Nat) (r : ZeroCheckSemantics.Tuple n) :
    (Finset.univ.filter (fun ds : TripleTuple n => reduceTuple n ds = r)).card
      ≤ (OuterChallenge.fiberCeiling ^ 3) ^ n := by
  classical
  have hset : (Finset.univ.filter (fun ds : TripleTuple n => reduceTuple n ds = r))
      = Fintype.piFinset (fun i => Finset.univ.filter
          (fun d : OuterChallenge.DigestTriple => OuterChallenge.reduceTriple d = r i)) := by
    apply Finset.ext
    intro ds
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      exact congrFun h i
    · intro h
      funext i
      exact h i
  rw [hset, Fintype.card_piFinset]
  calc ∏ i : Fin n, (Finset.univ.filter
        (fun d : OuterChallenge.DigestTriple => OuterChallenge.reduceTriple d = r i)).card
      ≤ ∏ _i : Fin n, OuterChallenge.fiberCeiling ^ 3 :=
        Finset.prod_le_prod' (fun i _ => OuterChallenge.fixed_value_preimage_bound (r i))
    _ = (OuterChallenge.fiberCeiling ^ 3) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- COUNTING (product form).  The digest tuples that reduce into `S` number at
most `S.card * (⌈2^256/p⌉^3)^n`, out of the `(2^768)^n` tuples of
`product_space_card_bits`. -/
theorem product_event_card (n : Nat) (S : Finset (ZeroCheckSemantics.Tuple n)) :
    (productEvent n S).card ≤ S.card * (OuterChallenge.fiberCeiling ^ 3) ^ n := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := reduceTuple n) (t := S)
    (fun x hx => (mem_productEvent n S x).mp hx)]
  calc ∑ r ∈ S, ((productEvent n S).filter (fun ds => reduceTuple n ds = r)).card
      ≤ ∑ _r ∈ S, (OuterChallenge.fiberCeiling ^ 3) ^ n := by
        refine Finset.sum_le_sum (fun r _ => le_trans (Finset.card_le_card ?_) (fiber_card_bound n r))
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    _ = S.card * (OuterChallenge.fiberCeiling ^ 3) ^ n := by
        rw [Finset.sum_const, smul_eq_mul]

theorem product_space_card (n : Nat) :
    Fintype.card (TripleTuple n) = (OuterChallenge.wordSize ^ 3) ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, OuterChallenge.digest_tuple_cardinality]

/-- `N` for the tau lane: the explicit finite space of `n` digest triples has
`(2^768)^n` points, the `n`-th power of `ConditionalSoundness`'s `N`. -/
theorem product_space_card_bits (n : Nat) : Fintype.card (TripleTuple n) = (2 ^ 768) ^ n := by
  rw [product_space_card, OuterChallenge.word_size_is_256_bits]
  congr 1

/-- EXPLICIT IDEAL LAW, n-fold product form.  Same convention as the adopted
`OuterChallenge.uniformTupleProbability`: count on an explicit finite space,
then divide by its size.  The product structure is the independence assumption;
it is asserted here, not proved about any hash. -/
noncomputable def uniformProductProbability (n : Nat)
    (S : Finset (ZeroCheckSemantics.Tuple n)) : ℚ :=
  ((productEvent n S).card : ℚ) / (Fintype.card (TripleTuple n) : ℚ)

theorem uniform_product_probability_nonneg (n : Nat) (S : Finset (ZeroCheckSemantics.Tuple n)) :
    0 ≤ uniformProductProbability n S :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- MASS (product form).  A set of at most `d` tau tuples has product mass at
most `d * (⌈2^256/p⌉ / 2^256)^(3n)`: one adopted per-coordinate factor
`(fiberCeiling / wordSize)^3` for each of the `n` coordinates. -/
theorem uniform_product_probability_bound (n : Nat) (S : Finset (ZeroCheckSemantics.Tuple n))
    (d : Nat) (hd : S.card ≤ d) :
    uniformProductProbability n S ≤
      (d : ℚ) * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ (3 * n) := by
  have hb := (product_event_card n S).trans (Nat.mul_le_mul_right _ hd)
  have hr : ((productEvent n S).card : ℚ) ≤ (d : ℚ) * ((OuterChallenge.fiberCeiling : ℚ) ^ 3) ^ n := by
    exact_mod_cast hb
  have hrw : ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ (3 * n)
      = ((OuterChallenge.fiberCeiling : ℚ) ^ 3) ^ n / ((OuterChallenge.wordSize : ℚ) ^ 3) ^ n := by
    rw [pow_mul, div_pow, div_pow]
  have hpos : (0 : ℚ) < ((OuterChallenge.wordSize : ℚ) ^ 3) ^ n := by
    have hw : (0 : ℚ) < (OuterChallenge.wordSize : ℚ) :=
      Nat.cast_pos.mpr OuterChallenge.word_size_positive
    positivity
  unfold uniformProductProbability
  rw [product_space_card, Nat.cast_pow, Nat.cast_pow, hrw, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hr hpos.le

/-- The tau term: the product mass of the adopted `zeroCheckBadSet`, as a
concrete expression in `n`, `|F| = Fintype.card Element` and the adopted
per-coordinate ratio `fiberCeiling / wordSize`.  Written without `Nat`
subtraction: `|F|^n / |F|` is `|F|^(n-1)` for `n ≥ 1` and `1 / |F|` at `n = 0`. -/
noncomputable def tauTerm (n : Nat) : ℚ :=
  (n : ℚ) * ((Fintype.card Element : ℚ) ^ n / (Fintype.card Element : ℚ))
    * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ (3 * n)

/-- (1) THE TAU PRODUCT BOUND.  The adopted multilinear Schwartz--Zippel count
`ZeroCheckSemantics.zeroCheckBadSet_card_bound` (`card * |F| ≤ n * |F|^n`),
composed with the adopted per-coordinate reduction bound, gives the mass of the
tau zero-check bad event on the explicit space of `n` digest triples. -/
theorem tau_product_mass_bound (n : Nat) (g : Nat → Element) :
    uniformProductProbability n (ZeroCheckSemantics.zeroCheckBadSet n g) ≤ tauTerm n := by
  have hq : (0 : ℚ) < (Fintype.card Element : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := Element)
  have hcard : ((ZeroCheckSemantics.zeroCheckBadSet n g).card : ℚ) * (Fintype.card Element : ℚ)
      ≤ (n : ℚ) * (Fintype.card Element : ℚ) ^ n := by
    exact_mod_cast ZeroCheckSemantics.zeroCheckBadSet_card_bound n g
  have hle : ((ZeroCheckSemantics.zeroCheckBadSet n g).card : ℚ)
      ≤ (n : ℚ) * ((Fintype.card Element : ℚ) ^ n / (Fintype.card Element : ℚ)) := by
    rw [mul_div_assoc', le_div_iff hq]
    exact hcard
  refine (uniform_product_probability_bound n _ _ le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_right hle
    (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)

/-- The adopted per-coordinate modulo-reduction bias, written out. -/
theorem digest_ratio_explicit :
    ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ))
      = (((2 ^ 256 + Arithmetic.modulus - 1) / Arithmetic.modulus : Nat) : ℚ) / (2 : ℚ) ^ 256 := by
  simp only [OuterChallenge.fiberCeiling, WhirChallenge.ceilingQuotient,
    OuterChallenge.word_size_is_256_bits, Nat.cast_pow, Nat.cast_ofNat]

/-- The tau term with every constant written out: `|F| = p^3`, the ratio
`⌈2^256/p⌉ / 2^256`. -/
theorem tau_term_explicit (n : Nat) :
    tauTerm n = (n : ℚ) *
        (((Arithmetic.modulus ^ 3 : Nat) : ℚ) ^ n / ((Arithmetic.modulus ^ 3 : Nat) : ℚ))
      * ((((2 ^ 256 + Arithmetic.modulus - 1) / Arithmetic.modulus : Nat) : ℚ) / (2 : ℚ) ^ 256)
          ^ (3 * n) := by
  rw [tauTerm, cardinality_exact, digest_ratio_explicit]

/-! ## 2. The union of the per-row alpha bad sets over the cube

`AlphaZeroCheck.alphaBadSet` is a `Finset Element` PER ROW: each Boolean row of
the cube has its own slot-coefficient list.  The adopted module takes no union
over the `2^n` rows.  This section takes it. -/

/-- The union of a row-indexed family of challenge sets over the first `rows`
rows.  Kept generic so that no kernel defeq ever has to look inside the
noncomputable `AlphaZeroCheck.alphaBadSet`. -/
def rowUnion (rows : Nat) (f : Nat → Finset Element) : Finset Element :=
  (Finset.range rows).biUnion f

theorem mem_rowUnion (rows : Nat) (f : Nat → Finset Element) (a : Element) :
    a ∈ rowUnion rows f ↔ ∃ i, i < rows ∧ a ∈ f i := by
  constructor
  · intro h
    obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.mp h
    exact ⟨i, Finset.mem_range.mp hi, hm⟩
  · rintro ⟨i, hi, hm⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hm⟩

theorem not_mem_rowUnion (rows : Nat) (f : Nat → Finset Element) (a : Element)
    (h : a ∉ rowUnion rows f) : ∀ i, i < rows → a ∉ f i := by
  intro i hi hm
  exact h (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hm⟩)

theorem rowUnion_card_le (rows : Nat) (f : Nat → Finset Element) (b : Nat)
    (h : ∀ i, i < rows → (f i).card ≤ b) : (rowUnion rows f).card ≤ rows * b := by
  refine (Finset.card_biUnion_le (s := Finset.range rows) (t := f)).trans ?_
  calc ∑ i ∈ Finset.range rows, (f i).card
      ≤ ∑ _i ∈ Finset.range rows, b :=
        Finset.sum_le_sum (fun i hi => h i (Finset.mem_range.mp hi))
    _ = rows * b := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Row `i` of the cube contributes the adopted `AlphaZeroCheck.alphaBadSet` of
its own slot-coefficient list. -/
noncomputable def alphaFamily (coeffsOf : Nat → List Element) (i : Nat) : Finset Element :=
  AlphaZeroCheck.alphaBadSet (coeffsOf i)

theorem alphaFamily_apply (coeffsOf : Nat → List Element) (i : Nat) :
    alphaFamily coeffsOf i = AlphaZeroCheck.alphaBadSet (coeffsOf i) := rfl

theorem alphaFamily_card (coeffsOf : Nat → List Element) (i : Nat) :
    (alphaFamily coeffsOf i).card ≤ (coeffsOf i).length - 1 := by
  rw [alphaFamily_apply]
  exact AlphaZeroCheck.alphaBadSet_card_bound (coeffsOf i)

/-- (2) THE ALPHA UNION.  One `Finset Element` covering every row's alpha bad
set at once.  It lives in the SAME challenge space as an entry of
`ConditionalSoundness.badSets`: a single field challenge, i.e. one
`OuterChallenge.DigestTriple` after reduction. -/
noncomputable def alphaUnionBadSet (rows : Nat) (coeffsOf : Nat → List Element) : Finset Element :=
  rowUnion rows (alphaFamily coeffsOf)

theorem mem_alphaUnionBadSet (rows : Nat) (coeffsOf : Nat → List Element) (a : Element) :
    a ∈ alphaUnionBadSet rows coeffsOf ↔
      ∃ i, i < rows ∧ a ∈ alphaFamily coeffsOf i :=
  mem_rowUnion rows (alphaFamily coeffsOf) a

/-- (2) CARDINALITY.  With every row's slot list of length at most `L`, the
union has at most `rows * (L - 1)` points. -/
theorem alpha_union_card_bound (rows L : Nat) (coeffsOf : Nat → List Element)
    (hlen : ∀ i, i < rows → (coeffsOf i).length ≤ L) :
    (alphaUnionBadSet rows coeffsOf).card ≤ rows * (L - 1) :=
  rowUnion_card_le rows (alphaFamily coeffsOf) (L - 1)
    (fun i hi => (alphaFamily_card coeffsOf i).trans (Nat.sub_le_sub_right (hlen i hi) 1))

/-- (2) CARDINALITY IN CONFIGURATION QUANTITIES.  Every row's slot list is the
source's `vec![ZERO; num_gate_constraints]` buffer, so with `2^n` rows the union
has at most `2^n * (numGateConstraints - 1)` points, and the adopted
`Gates.validateConfiguration` envelope caps that at `122 * 2^n`. -/
theorem alpha_union_configured_card_bound (cfg : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (tbl : GateSuffixPolynomial.Tables) (rows : Nat)
    (coeffsOf : Nat → List Element)
    (hv : Gates.validateConfiguration cfg gates = some ())
    (hw : tbl.wires.length = cfg.numWires) (hc : tbl.constants.length = cfg.numConstants)
    (hcoeffs : ∀ i, i < rows → AlphaZeroCheck.slotCoefficients cfg gates
      (AlphaZeroCheck.rowWires tbl i) (AlphaZeroCheck.rowConstants tbl i) publicHash
        = some (coeffsOf i)) :
    (alphaUnionBadSet rows coeffsOf).card ≤ rows * (cfg.numGateConstraints - 1) ∧
      cfg.numGateConstraints ≤ 123 ∧
      (alphaUnionBadSet rows coeffsOf).card ≤ 122 * rows := by
  have henv := (Gates.validate_configuration_success cfg gates hv).1
  simp only [Gates.envelope] at henv
  have h123 : cfg.numGateConstraints ≤ 123 := henv.2.2.1
  have hrow : ∀ i, i < rows → (coeffsOf i).length = cfg.numGateConstraints := by
    intro i hi
    exact (AlphaZeroCheck.configured_alphaBadSet_card_bound cfg gates
      (AlphaZeroCheck.rowWires tbl i) (AlphaZeroCheck.rowConstants tbl i) publicHash (coeffsOf i)
      hv (by rw [AlphaZeroCheck.rowWires_length]; exact hw)
      (by rw [AlphaZeroCheck.rowConstants_length]; exact hc) (hcoeffs i hi)).1
  have hcard := alpha_union_card_bound rows cfg.numGateConstraints coeffsOf
    (fun i hi => le_of_eq (hrow i hi))
  refine ⟨hcard, h123, hcard.trans ?_⟩
  calc rows * (cfg.numGateConstraints - 1) ≤ rows * 122 :=
        Nat.mul_le_mul (le_refl rows) (by omega)
    _ = 122 * rows := Nat.mul_comm _ _

/-- The alpha term: the mass of the union under the SAME single digest-triple
law as `ConditionalSoundness`'s outer terms. -/
noncomputable def alphaTerm (rows constraints : Nat) : ℚ :=
  ((rows * (constraints - 1) : Nat) : ℚ) *
    ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3

/-- (2) MASS.  Under the adopted uniform digest-triple law of `OuterChallenge`,
the union costs `rows * (L - 1) * (⌈2^256/p⌉ / 2^256)^3`. -/
theorem alpha_union_mass_bound (rows L : Nat) (coeffsOf : Nat → List Element)
    (hlen : ∀ i, i < rows → (coeffsOf i).length ≤ L) :
    OuterChallenge.uniformTupleProbability (alphaUnionBadSet rows coeffsOf)
      ≤ alphaTerm rows L :=
  OuterChallenge.uniform_tuple_probability_bound _ _ (alpha_union_card_bound rows L coeffsOf hlen)

/-- (2) ONE ALPHA, EVERY ROW.  An alpha outside the union is outside every row's
own adopted bad set. -/
theorem alpha_outside_union (rows : Nat) (coeffsOf : Nat → List Element) (alpha : Element)
    (hgood : alpha ∉ alphaUnionBadSet rows coeffsOf) :
    ∀ i, i < rows → alpha ∉ AlphaZeroCheck.alphaBadSet (coeffsOf i) := by
  intro i hi
  rw [← alphaFamily_apply]
  exact not_mem_rowUnion rows (alphaFamily coeffsOf) alpha hgood i hi

/-- (2) THE COMPOSED COROLLARY, ALPHA ONLY.  One alpha outside the union makes
the adopted `AlphaZeroCheck.gate_slots_vanish` conclusion available on EVERY row
simultaneously. -/
theorem all_rows_gate_slots_vanish (cfg : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (tbl : GateSuffixPolynomial.Tables)
    (rows : Nat) (coeffsOf : Nat → List Element)
    (hv : Gates.validateConfiguration cfg gates = some ())
    (hcoeffs : ∀ i, i < rows → AlphaZeroCheck.slotCoefficients cfg gates
      (AlphaZeroCheck.rowWires tbl i) (AlphaZeroCheck.rowConstants tbl i) publicHash
        = some (coeffsOf i))
    (hzero : ∀ i, i < rows → GatesComplete.evalCombined cfg gates
      (AlphaZeroCheck.rowWires tbl i) (AlphaZeroCheck.rowConstants tbl i) publicHash
        alpha.toVerifier = some Verifier.zero)
    (hgood : alpha ∉ alphaUnionBadSet rows coeffsOf) :
    ∀ i, i < rows → (∀ x ∈ coeffsOf i, x = 0) ∧
      ∀ k, k < cfg.numGateConstraints → AlphaZeroCheck.slotValue cfg gates
        (AlphaZeroCheck.rowWires tbl i) (AlphaZeroCheck.rowConstants tbl i) publicHash k = 0 := by
  intro i hi
  exact AlphaZeroCheck.gate_slots_vanish cfg gates (AlphaZeroCheck.rowWires tbl i)
    (AlphaZeroCheck.rowConstants tbl i) publicHash alpha (coeffsOf i) hv (hcoeffs i hi)
    (hzero i hi) (alpha_outside_union rows coeffsOf alpha hgood i hi)

/-- (2) THE COMPOSED COROLLARY, TAU AND ALPHA.  A tau outside the adopted
`ZeroCheckSemantics.zeroCheckBadSet` together with ONE alpha outside the alpha
union forces every constraint slot of EVERY Boolean row to vanish, via the
adopted `AlphaZeroCheck.gate_constraints_vanish_of_tau_and_alpha`.  Read the
conclusion exactly as the adopted module states it: slot `k` is the SUM over the
ordered gate rows of `filter_g * constraint_(g,k)`, and gates whose filter is
zero stay unconstrained. -/
theorem all_rows_constraints_vanish_of_tau_and_alpha_union (cfg : Gates.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base) (alpha : Element)
    (tbl : GateSuffixPolynomial.Tables) (tau : List Element)
    (coeffsOf : Nat → List Element)
    (hv : Gates.validateConfiguration cfg gates = some ())
    (hw : tbl.wires.length = cfg.numWires) (hc : tbl.constants.length = cfg.numConstants)
    (heq : tbl.eq = EqTableProvenance.eqTable tau)
    (hsum : GateDenseRound.cubeSum cfg gates publicHash alpha tbl (2 ^ tau.length) = 0)
    (hgoodTau : ZeroCheckSemantics.tupleOf tau ∉
      ZeroCheckSemantics.zeroCheckBadSet tau.length
        (ZeroCheckSemantics.gateValue cfg gates publicHash alpha tbl))
    (hcoeffs : ∀ i, i < 2 ^ tau.length → AlphaZeroCheck.slotCoefficients cfg gates
      (AlphaZeroCheck.rowWires tbl i) (AlphaZeroCheck.rowConstants tbl i) publicHash
        = some (coeffsOf i))
    (hgoodAlpha : alpha ∉ alphaUnionBadSet (2 ^ tau.length) coeffsOf) :
    ∀ i, i < 2 ^ tau.length → ∀ k, k < cfg.numGateConstraints →
      AlphaZeroCheck.slotValue cfg gates (AlphaZeroCheck.rowWires tbl i)
        (AlphaZeroCheck.rowConstants tbl i) publicHash k = 0 := by
  intro i hi
  exact AlphaZeroCheck.gate_constraints_vanish_of_tau_and_alpha cfg gates publicHash alpha tbl tau
    hv hw hc heq hsum hgoodTau i hi (coeffsOf i) (hcoeffs i hi)
    (alpha_outside_union (2 ^ tau.length) coeffsOf alpha hgoodAlpha i hi)

/-! ## 3. The combined event and its union bound

Three terms, three named challenge spaces.  The sum is over an EXPLICIT ideal
law in each case; nothing here says the three draws are jointly independent of
each other or of the prover's tables. -/

/-- The outer term of `ConditionalSoundness.outer_failure_bound`, verbatim: the
gate-lane degree `quotientDegree + 2` from `GateClaimChain` and the norm-lane
degree `5`, each over `degreeBits` rounds, under the digest-triple law. -/
noncomputable def outerTerm (degreeBits quotientDegree : Nat) : ℚ :=
  ((5 * degreeBits + (quotientDegree + 2) * degreeBits : Nat) : ℚ) *
    ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3

theorem outer_term_is_adopted_bound (degreeBits quotientDegree : Nat) :
    outerTerm degreeBits quotientDegree
      = ((5 * degreeBits + (quotientDegree + 2) * degreeBits : Nat) : ℚ) *
        ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := rfl

/-- THE COMBINED BOUND, as a concrete expression.  Term by term:
`outerTerm` on `OuterChallenge.DigestTriple`; `tauTerm n` on
`TripleTuple n = Fin n → OuterChallenge.DigestTriple`; `alphaTerm (2^n) L` on
`OuterChallenge.DigestTriple`. -/
noncomputable def combinedBound (degreeBits quotientDegree n constraints : Nat) : ℚ :=
  outerTerm degreeBits quotientDegree + tauTerm n + alphaTerm (2 ^ n) constraints

/-- (3) THE UNION BOUND.  The SUM of three SEPARATELY bounded masses is at most
the sum of the three concrete terms.  No disjunction EVENT exists here: the
three masses live on different sample spaces (one digest triple, an n-tuple of
digest triples, one digest triple) and NO JOINT LAW is formalized, so this is
an arithmetic inequality between three independently derived quotients, not
the probability of a union.  `failure` is the free rational of
`ConditionalSoundness`; the other two summands are counted masses. -/
theorem combined_union_bound (failure : ℚ) (degreeBits quotientDegree n constraints : Nat)
    (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hfail : failure ≤ outerTerm degreeBits quotientDegree)
    (hlen : ∀ i, i < 2 ^ n → (coeffsOf i).length ≤ constraints) :
    failure + uniformProductProbability n (ZeroCheckSemantics.zeroCheckBadSet n g)
        + OuterChallenge.uniformTupleProbability (alphaUnionBadSet (2 ^ n) coeffsOf)
      ≤ combinedBound degreeBits quotientDegree n constraints :=
  add_le_add (add_le_add hfail (tau_product_mass_bound n g))
    (alpha_union_mass_bound (2 ^ n) constraints coeffsOf hlen)

section Accepted
open NormDenseRound NormTerminalBinding

variable {e : Verifier.Engine} {decode : Integrated.DecodeGates}
  {cfg : Verifier.Config} {pf : Verifier.Proof}
  {t tLast : NormDenseRound.Tables} {pr : NormDenseRound.Prepared}
  {constants extra : List Verifier.Ext3} {x : Element}
  {logTruths gateCompareRounds : List (List Element)} {gateCompare : Element} {fixedness : Prop}
  {law : Finset Element → ℚ} {failure : ℚ}

/-- (3) THE UNION BOUND ON AN ACCEPTED EXECUTION.  The outer summand is imported
from the adopted `ConditionalSoundness.outer_failure_bound` -- so ASSUMPTIONS
1-3 of that structure are in force for it, and `failure` remains a free rational
bounded only from above -- while the tau and alpha summands are the counted
masses of this module.  IMPORTANT: the parameters `n`, `g` and `coeffsOf` of the
tau and alpha summands are FREE in this theorem.  They are NOT tied to the
accepted execution's gate tables or to `degreeBits`; only the outer summand is
connected to the proof and configuration.  The three summands are added; they are NOT shown to
exhaust the bad events, and no soundness conclusion is drawn from their
complement. -/
theorem accepted_combined_union_bound (pin : Verifier.Pinned) (chain : Nat)
    (A : ConditionalSoundness.Assumptions e decode cfg pf t tLast pr constants extra x logTruths
      gateCompareRounds gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain cfg pf = .ok ())
    (n constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hlen : ∀ i, i < 2 ^ n → (coeffsOf i).length ≤ constraints) :
    failure + uniformProductProbability n (ZeroCheckSemantics.zeroCheckBadSet n g)
        + OuterChallenge.uniformTupleProbability (alphaUnionBadSet (2 ^ n) coeffsOf)
      ≤ combinedBound cfg.degreeBits cfg.quotientDegree n constraints :=
  combined_union_bound failure cfg.degreeBits cfg.quotientDegree n constraints g coeffsOf
    (ConditionalSoundness.outer_failure_bound pin chain A hacc) hlen

end Accepted

/-! ## 4. The envelope extremes -/

theorem digest_ratio_cube_nonneg :
    (0 : ℚ) ≤ ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 :=
  pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) 3

/-- (4) The two DIGEST-TRIPLE-law terms collapse at the envelope: `195` outer
points and at most `122 * 2^13 = 999424` alpha points, i.e. `999619` points of
the field, each of digest mass `(⌈2^256/p⌉ / 2^256)^3`. -/
theorem envelope_digest_terms_bound (cfg : Verifier.Config)
    (henv : Verifier.envelope cfg = true) (constraints : Nat) (hcon : constraints ≤ 123) :
    outerTerm cfg.degreeBits cfg.quotientDegree + alphaTerm (2 ^ cfg.degreeBits) constraints
      ≤ (999619 : ℚ) * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  obtain ⟨hdb, -⟩ := ConditionalSoundness.envelope_parameter_bounds cfg henv
  have houter : 5 * cfg.degreeBits + (cfg.quotientDegree + 2) * cfg.degreeBits ≤ 195 :=
    ConditionalSoundness.envelope_gives_concrete_bound cfg henv
  have hpow : 2 ^ cfg.degreeBits ≤ 8192 := by
    calc 2 ^ cfg.degreeBits ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) hdb
      _ = 8192 := by norm_num
  have halpha : 2 ^ cfg.degreeBits * (constraints - 1) ≤ 999424 := by
    calc 2 ^ cfg.degreeBits * (constraints - 1) ≤ 8192 * 122 :=
          Nat.mul_le_mul hpow (by omega)
      _ = 999424 := by norm_num
  have hsum : (5 * cfg.degreeBits + (cfg.quotientDegree + 2) * cfg.degreeBits) +
      2 ^ cfg.degreeBits * (constraints - 1) ≤ 999619 := by omega
  have hq : ((5 * cfg.degreeBits + (cfg.quotientDegree + 2) * cfg.degreeBits : Nat) : ℚ)
      + ((2 ^ cfg.degreeBits * (constraints - 1) : Nat) : ℚ) ≤ (999619 : ℚ) := by
    have := (Nat.cast_le (α := ℚ)).mpr hsum
    push_cast at this ⊢
    linarith
  unfold outerTerm alphaTerm
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right hq digest_ratio_cube_nonneg

/-- (4) The whole combined bound at the envelope, with the tau term left at the
execution's own `degreeBits`. -/
theorem envelope_combined_bound (cfg : Verifier.Config) (henv : Verifier.envelope cfg = true)
    (constraints : Nat) (hcon : constraints ≤ 123) :
    combinedBound cfg.degreeBits cfg.quotientDegree cfg.degreeBits constraints
      ≤ (999619 : ℚ) * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3
        + tauTerm cfg.degreeBits := by
  have h := envelope_digest_terms_bound cfg henv constraints hcon
  unfold combinedBound
  linarith

/-- (4) THE CLOSED FORM AT THE EXTREMES `degreeBits = 13`, `quotientDegree = 8`,
`numGateConstraints = 123`: exactly `999619 * (⌈2^256/p⌉ / 2^256)^3` on the
digest-triple space plus the tau term on the thirteen-triple space. -/
theorem combined_bound_at_extremes :
    combinedBound 13 8 13 123
      = (999619 : ℚ) * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3
        + tauTerm 13 := by
  unfold combinedBound outerTerm alphaTerm
  norm_num
  ring

/-- (4) EXACT RATIONAL EVALUATION.  Proved by rational arithmetic on ℚ literals
built from `Arithmetic.modulus` and `2 ^ 256` -- no `decide`, no
`native_decide`, no floating point.

`2^-172` IS NOT THE SYSTEM'S SOUNDNESS ERROR.  It omits the WHIR/Merkle term,
which dominates; the deployed design point is around 100 bits. -/
theorem combined_bound_at_extremes_numeric :
    combinedBound 13 8 13 123 ≤ (1 : ℚ) / 2 ^ 172 := by
  rw [combined_bound_at_extremes, digest_ratio_explicit, tau_term_explicit]
  norm_num [Arithmetic.modulus]

/-- (4) The same, reached from an accepted execution's own envelope guard when
its `degreeBits` is at the extreme. -/
theorem envelope_extreme_combined_numeric (cfg : Verifier.Config)
    (henv : Verifier.envelope cfg = true) (hdb : cfg.degreeBits = 13)
    (hqd : cfg.quotientDegree = 8) (constraints : Nat) (hcon : constraints ≤ 123) :
    combinedBound 13 8 13 constraints ≤ (1 : ℚ) / 2 ^ 172 := by
  have h := envelope_combined_bound cfg henv constraints hcon
  rw [hdb, hqd] at h
  refine h.trans ?_
  have h2 := combined_bound_at_extremes_numeric
  rw [combined_bound_at_extremes] at h2
  exact h2

/-! ## 5. Examples at `n = 1`

No tuple `Finset` is ever instantiated at a literal `n ≥ 2`: that would make the
elaborator enumerate `Finset.univ` over `(Element)^n`. -/

/-- At one tau coordinate the product law is exactly the adopted single
digest-triple law's ratio factor. -/
theorem tau_term_one :
    tauTerm 1 = ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  have hq : (Fintype.card Element : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (Fintype.card Element : ℚ) := by
      exact_mod_cast Fintype.card_pos (α := Element)
    exact ne_of_gt this
  rw [tauTerm, Nat.cast_one, pow_one, div_self hq, one_mul, one_mul, Nat.mul_one]

/-- The one-coordinate tau bad event costs one adopted ratio factor. -/
theorem tau_product_mass_bound_one (g : Nat → Element) :
    uniformProductProbability 1 (ZeroCheckSemantics.zeroCheckBadSet 1 g)
      ≤ ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  rw [← tau_term_one]
  exact tau_product_mass_bound 1 g

/-- The empty tau set has empty product event. -/
theorem product_event_empty (n : Nat) : productEvent n (∅ : Finset (ZeroCheckSemantics.Tuple n)) = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro ds hds
  exact absurd ((mem_productEvent n ∅ ds).mp hds) (Finset.not_mem_empty _)

theorem uniform_product_probability_empty (n : Nat) :
    uniformProductProbability n (∅ : Finset (ZeroCheckSemantics.Tuple n)) = 0 := by
  unfold uniformProductProbability
  rw [product_event_empty, Finset.card_empty, Nat.cast_zero, zero_div]

/-- The alpha union over a single row is that row's own adopted bad set bound. -/
theorem alpha_union_one_row (coeffsOf : Nat → List Element) :
    (alphaUnionBadSet 1 coeffsOf).card ≤ (coeffsOf 0).length - 1 := by
  have h := alpha_union_card_bound 1 (coeffsOf 0).length coeffsOf (fun i hi => by
    have : i = 0 := by omega
    subst this
    exact le_rfl)
  simpa using h

/-- A cube every row of which already carries zero slots contributes an EMPTY
alpha union: the adopted `alphaBadSet` is `∅` in its good branch, so there is
nothing for the alpha challenge to detect. -/
theorem alpha_union_all_empty_rows (rows : Nat) :
    (alphaUnionBadSet rows (fun _ => ([] : List Element))).card = 0 := by
  have h := alpha_union_card_bound rows 0 (fun _ => ([] : List Element)) (fun i _ => le_rfl)
  simpa using h

/-- Two cube rows (`n = 1`) is still a union over a `Finset Element`, not over a
tuple space, so it is safe to state at a literal row count. -/
theorem alpha_union_two_rows (coeffsOf : Nat → List Element) (L : Nat)
    (hlen : ∀ i, i < 2 → (coeffsOf i).length ≤ L) :
    (alphaUnionBadSet (2 ^ 1) coeffsOf).card ≤ 2 * (L - 1) := by
  have h := alpha_union_card_bound (2 ^ 1) L coeffsOf (by
    intro i hi
    exact hlen i (by simpa using hi))
  simpa using h

end Audit.Wire3.ChallengeUnionBound
