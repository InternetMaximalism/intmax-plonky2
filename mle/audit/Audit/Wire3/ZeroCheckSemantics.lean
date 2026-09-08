import Audit.Wire3.GateDenseRound
import Audit.Wire3.EqTableProvenance
import Audit.Wire3.TranscriptProvenance
import Audit.Wire3.ConditionalSoundness

/-!
# The multilinear zero check: from "the eq-weighted cube sum is zero" to
"every Boolean row is zero"

The adopted `Audit.Wire3.GateDenseRound` proves that a round's endpoint sum IS
the eq-weighted all-gates aggregate summed over the Boolean cube
(`endpoint_sum_is_cube_sum`, `cubeSum`).  That gives
`sum_i eq(tau,i) * G(i) = 0`, which is NOT `forall i, G(i) = 0`.  This module
supplies exactly that missing semantic step, and nothing else.

What is used, unchanged, from the adopted development:
* the eq function: `Norm.eqFactor` / `Norm.booleanFactor` / `Norm.booleanRowEq`
  (Norm.lean 113-114, 139-143) through `EqTableProvenance.bitFactor` /
  `rowProdFrom` / `eqTable` and `eq_table_getD` /
  `eq_table_entry_is_boolean_row_eq` / `row_prod_even` / `row_prod_odd` /
  `row_prod_shift`.  NO second eq function is defined here; `extensionOf`'s
  weight is literally `EqTableProvenance.rowProdFrom 0 tau i`, and
  `extensionOf_uses_eq_table` / `extension_weight_is_boolean_row_eq` prove it is
  the actual `ext3_eq_evals` table entry and the verifier's `booleanRowEq`;
* the field: the concrete `GoldilocksExt3Field.Element`, with its constructed
  `Field`/`Fintype` instances and `cardinality_exact : Fintype.card = p^3`;
* the sum shape: `GateDenseRound.cubeSum` / `rowTerm` / `rowElement` /
  `interleave_sum` / `endpoint_sum_is_cube_sum`;
* the bad-event style: `zeroCheckBadSet` MIRRORS THE SHAPE of the adopted
  `ConditionalSoundness.roundBadSet` (a bad set that is `∅` in the good branch)
  and of `OuterChallenge`'s explicit uniform law.  It does NOT compose with
  `badSets` / `BadEventFree`: those are `List (Finset Element)` over single
  field challenges, while this is a `Finset (Tuple n)` over n-tuples.  Joining
  them needs an n-fold product event that is not built here;
* the transcript-derived tau: `TranscriptProvenance.gateTauColumn` and
  `derived_column_lengths`, and the eq provenance `GateEqProvenance`.

TWO OBLIGATIONS ON ANY CONSUMER.

1. ADAPTIVITY.  `zeroCheckBadSet` is indexed by `gateValue ... t`, i.e. by the
   PROVER'S OWN TABLES.  Before `hgood` may be read as a probability event, a
   Fiat--Shamir argument must establish that those tables are fixed by transcript
   material PRECEDING the gate-tau block.  Nothing here addresses adaptivity.
2. VACUITY ON FAILING ROWS.  Where `GatesComplete.evalCombined` returns `none`,
   both `gateValue = 0` and the `rowTerm` clause hold TRIVIALLY, so the
   conclusion says nothing on that row.  A consumer must add
   `Gates.validateConfiguration` and `TableShape`, which make `evalCombined`
   total (adopted `GateDenseRound.slice_polynomial_complete`), to obtain real
   content on every row.

WHAT IS PROVED.
1. `extensionOf g tau = sum_{i < 2^|tau|} rowProdFrom 0 tau i * g i` is the
   MULTILINEAR EXTENSION of `g` on the cube: `extensionOf_at_boolean_point`
   shows it returns `g j` at the Boolean point of row `j`, so it interpolates
   the given values, not merely some values.
2. `extensionOf_ne_zero_at_boolean_point`: a nonzero cube value makes the
   extension nonzero, witnessed at that row's own Boolean point.
3. `vanishing_card_bound`: EXACT STATEMENT PROVED —
   `(vanishingSet n g).card * |F| <= n * |F|^n`, i.e. the vanishing set of a
   nonzero multilinear extension in `n` variables has at most `n * |F|^(n-1)`
   points, density at most `n / |F|` (`vanishing_density_bound`).  This is the
   Schwartz--Zippel bound for TOTAL DEGREE <= n (each variable appears with
   degree <= 1, so the total degree is at most `n`).  It is NOT the sharper
   exact multilinear count, and no sharper bound is claimed.  The proof is an
   honest induction on the number of variables through the adopted low-bit
   head split (`extensionOf_cons`), with the per-fibre root count
   `card_root_le_one`; nothing is assumed about the halves.
4. `gate_rows_vanish` / `gate_rows_vanish_of_endpoint_sum` /
   `gate_rows_vanish_of_derived_tau`: with the prover's eq table equal to
   `eqTable tau` and a vanishing `cubeSum`, a `tau` OUTSIDE `zeroCheckBadSet`
   forces every row's gate aggregate, `rowElement` and `rowTerm` to be zero.

BOUNDARIES (nothing below is proved or claimed here).
* NO probability statement about any deterministic hash.  `zeroCheckBadSet` is
  a set; `vanishing_density_bound` is an EXPLICIT uniform law over the tuple
  domain `(Element)^n`, exactly as `OuterChallenge.uniformTupleProbability` is
  an explicit ideal law.  That the drawn `tau` is uniform, or independent of
  the prover's tables, is a Fiat--Shamir obligation NOT discharged here; the
  `hgood` hypothesis of the corollaries is left for a later module.
* NO reduction of the drawn tau's 32-byte-triple mass: this module counts in
  `(Element)^n`, whereas `OuterChallenge` counts in `DigestTriple`.  Composing
  the two (an `n`-fold product version of `OuterChallenge.tupleEvent`) is NOT
  done here.
* NO claim that the cube sum IS zero.  As in `GateDenseRound`, whether the
  circuit's aggregate vanishes is circuit truth and stays outside the model.
* NO soundness, extraction, PCS/WHIR, Merkle, memory-refinement or
  Rust/Solidity-compilation claim.  `gateValue`'s `none` branch is the adopted
  `rowElement` totalisation, not a zero-default read replacing a source bound.
* `tupleOf tau = tau.get` is a total read from a list, with no default.
* Tactic note: `simp`/`ring`/`norm_num` must never see `Fintype.card Element`;
  their `Nat` simprocs try to evaluate the `p^3`-element `Finset.univ`.  Every
  arithmetic step here is therefore routed through the size-generic
  `schwartz_zippel_step` / `density_of_count`.
-/

set_option maxRecDepth 8000

namespace Audit.Wire3.ZeroCheckSemantics
open Audit.Wire3 GoldilocksExt3Field EqTableProvenance

/-! ## 0. List-sum helpers -/

theorem sum_map_mul_left (c : Element) (l : List Nat) (f : Nat → Element) :
    (l.map (fun i => c * f i)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

theorem sum_range_indicator (f : Nat → Element) :
    ∀ (m j : Nat), j < m →
      ((List.range m).map (fun i => if i = j then f i else 0)).sum = f j := by
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
      intro j hj
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rcases Nat.lt_or_ge j m with h | h
      · rw [ih j h, if_neg (by omega), add_zero]
      · have hjm : j = m := by omega
        subst hjm
        rw [if_pos rfl]
        have hz : ((List.range j).map (fun i => if i = j then f i else 0)).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨i, hi, rfl⟩ := hx
          exact if_neg (by omega)
        rw [hz, zero_add]

/-! ## 1. The multilinear extension over the ADOPTED eq product -/

/-- The multilinear extension of a Boolean-cube-indexed family of values.
The weight of row `i` is the ADOPTED per-row eq product
`EqTableProvenance.rowProdFrom 0 tau i`, i.e. entry `i` of the actual
`ext3_eq_evals` table (`eq_table_getD`), i.e. the verifier's
`Norm.booleanRowEq i tau` (`eq_table_entry_is_boolean_row_eq`). No second eq
function is introduced. -/
def extensionOf (g : Nat → Element) (tau : List Element) : Element :=
  ((List.range (2 ^ tau.length)).map (fun i => rowProdFrom 0 tau i * g i)).sum

/-- List-indexed form, for callers holding a value column. -/
def extension (vals : List Element) (tau : List Element) : Element :=
  extensionOf (fun i => vals.getD i 0) tau

theorem extension_eq_extensionOf (vals tau : List Element) :
    extension vals tau = extensionOf (fun i => vals.getD i 0) tau := rfl

/-- The weights ARE the entries of the actual eq table built from `tau`. -/
theorem extensionOf_uses_eq_table (g : Nat → Element) (tau : List Element) :
    extensionOf g tau =
      ((List.range (2 ^ tau.length)).map (fun i => (eqTable tau).getD i 0 * g i)).sum := by
  unfold extensionOf
  refine congrArg List.sum (List.map_congr_left ?_)
  intro i hi
  rw [eq_table_getD tau i (List.mem_range.mp hi)]

/-- The weights ARE the verifier's adopted `Norm.booleanRowEq`. -/
theorem extension_weight_is_boolean_row_eq (tau : List Element) (i : Nat)
    (hi : i < 2 ^ tau.length) :
    (rowProdFrom 0 tau i).toVerifier = Norm.booleanRowEq i (NormDenseRound.values tau) := by
  rw [← eq_table_getD tau i hi]
  exact eq_table_entry_is_boolean_row_eq tau i hi

/-! ### The Boolean points of the cube -/

/-- The Boolean point of row index `j` in `n` variables, in the adopted
coordinate order: the head coordinate is the LOW bit of `j`, exactly the bit
`rowProdFrom`'s coordinate `0` factor selects (`row_prod_even`/`row_prod_odd`). -/
def boolPoint : Nat → Nat → List Element
  | 0, _ => []
  | n + 1, j => (if j % 2 = 0 then 0 else 1) :: boolPoint n (j / 2)

theorem boolPoint_length : ∀ (n j : Nat), (boolPoint n j).length = n
  | 0, _ => rfl
  | n + 1, j => by simp only [boolPoint, List.length_cons, boolPoint_length n (j / 2)]

theorem mod_two_pow_succ_iff (n i j : Nat) :
    i % 2 ^ (n + 1) = j % 2 ^ (n + 1) ↔ i % 2 = j % 2 ∧ i / 2 % 2 ^ n = j / 2 % 2 ^ n := by
  have hp : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hd : (2 : Nat) ∣ 2 * 2 ^ n := ⟨2 ^ n, rfl⟩
  have e1 : i % (2 * 2 ^ n) / 2 = i / 2 % 2 ^ n := Nat.mod_mul_right_div_self i 2 (2 ^ n)
  have e2 : j % (2 * 2 ^ n) / 2 = j / 2 % 2 ^ n := Nat.mod_mul_right_div_self j 2 (2 ^ n)
  have f1 : i % (2 * 2 ^ n) % 2 = i % 2 := Nat.mod_mod_of_dvd i hd
  have f2 : j % (2 * 2 ^ n) % 2 = j % 2 := Nat.mod_mod_of_dvd j hd
  rw [hp]
  constructor
  · intro h
    rw [← e1, ← e2, ← f1, ← f2, h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    omega

/-- The adopted eq weight at a Boolean point is the Kronecker delta of the two
row indices: `1` at the point's own row, `0` at every other Boolean row. -/
theorem row_prod_at_boolean_point :
    ∀ (n i j : Nat),
      rowProdFrom 0 (boolPoint n j) i = if i % 2 ^ n = j % 2 ^ n then 1 else 0
  | 0, i, j => by
      simp only [boolPoint, rowProdFrom, Nat.pow_zero, Nat.mod_one, if_pos rfl, ite_true]
  | n + 1, i, j => by
      have hshift : rowProdFrom 1 (boolPoint n (j / 2)) i
          = rowProdFrom 0 (boolPoint n (j / 2)) (i / 2) := by
        have h := row_prod_shift (i / 2) (i % 2) (Nat.mod_lt _ (by omega)) (boolPoint n (j / 2)) 0
        rw [show 2 * (i / 2) + i % 2 = i by omega] at h
        exact h
      have hfactor : bitFactor (if j % 2 = 0 then (0 : Element) else 1) 0 i
          = if i % 2 = j % 2 then 1 else 0 := by
        have hb : bitFactor (if j % 2 = 0 then (0 : Element) else 1) 0 i
            = if i % 2 = 0 then 1 - (if j % 2 = 0 then (0 : Element) else 1)
              else (if j % 2 = 0 then (0 : Element) else 1) := by
          unfold bitFactor
          simp only [Nat.pow_zero, Nat.div_one]
        rw [hb]
        rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
          rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> rw [hi, hj] <;> norm_num
      rw [boolPoint, rowProdFrom, hshift, hfactor, row_prod_at_boolean_point n (i / 2) (j / 2)]
      by_cases h : i % 2 ^ (n + 1) = j % 2 ^ (n + 1)
      · obtain ⟨h1, h2⟩ := (mod_two_pow_succ_iff n i j).mp h
        rw [if_pos h, if_pos h1, if_pos h2, one_mul]
      · rw [if_neg h]
        by_cases h1 : i % 2 = j % 2
        · by_cases h2 : i / 2 % 2 ^ n = j / 2 % 2 ^ n
          · exact absurd ((mod_two_pow_succ_iff n i j).mpr ⟨h1, h2⟩) h
          · rw [if_pos h1, if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]

/-- (1) THE EXTENSION PROPERTY.  At every Boolean point of the cube the
extension returns exactly the supplied value of that row, i.e. it INTERPOLATES
`g` on the cube.  Affineness is proved for the head coordinate only
(`extensionOf_cons`); multilinearity in every coordinate is evident from
`rowProdFrom` but is not a theorem here, and no uniqueness lemma is proved, so
"the multilinear extension" is used informally.  The bound below does not
depend on either. -/
theorem extensionOf_at_boolean_point (g : Nat → Element) (n j : Nat) (hj : j < 2 ^ n) :
    extensionOf g (boolPoint n j) = g j := by
  have hlen : (boolPoint n j).length = n := boolPoint_length n j
  unfold extensionOf
  rw [hlen]
  have hmap : ((List.range (2 ^ n)).map (fun i => rowProdFrom 0 (boolPoint n j) i * g i))
      = (List.range (2 ^ n)).map (fun i => if i = j then g i else 0) := by
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < 2 ^ n := List.mem_range.mp hi
    rw [row_prod_at_boolean_point n i j, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [hmap, sum_range_indicator g (2 ^ n) j hj]

theorem extension_at_boolean_point (vals : List Element) (n j : Nat) (hj : j < 2 ^ n) :
    extension vals (boolPoint n j) = vals.getD j 0 :=
  extensionOf_at_boolean_point _ n j hj

/-! ## 2. A nonzero value forces a nonvanishing extension -/

/-- (2) If some cube value is nonzero the extension is NOT identically zero:
it is already nonzero at the Boolean point of that very row. -/
theorem extensionOf_ne_zero_at_boolean_point (g : Nat → Element) (n j : Nat)
    (hj : j < 2 ^ n) (hg : g j ≠ 0) : extensionOf g (boolPoint n j) ≠ 0 := by
  rw [extensionOf_at_boolean_point g n j hj]
  exact hg

theorem extensionOf_not_identically_zero (g : Nat → Element) (n : Nat)
    (hg : ∃ j, j < 2 ^ n ∧ g j ≠ 0) :
    ∃ tau : List Element, tau.length = n ∧ extensionOf g tau ≠ 0 := by
  obtain ⟨j, hj, hgj⟩ := hg
  exact ⟨boolPoint n j, boolPoint_length n j, extensionOf_ne_zero_at_boolean_point g n j hj hgj⟩

/-- Contrapositive form: an extension that vanishes at every Boolean point has
every cube value zero. -/
theorem values_zero_of_extension_zero_on_cube (g : Nat → Element) (n : Nat)
    (h : ∀ j, j < 2 ^ n → extensionOf g (boolPoint n j) = 0) :
    ∀ j, j < 2 ^ n → g j = 0 := by
  intro j hj
  rw [← extensionOf_at_boolean_point g n j hj]
  exact h j hj


/-! ## 3. The head-coordinate split -/

/-- The extension is affine in its head coordinate, with the two halves of the
value family as the `0`/`1` endpoints.  This is the adopted low-bit convention
(`row_prod_even`/`row_prod_odd`, `first_binding_uses_head_coordinate`). -/
theorem extensionOf_cons (g : Nat → Element) (t : Element) (tau : List Element) :
    extensionOf g (t :: tau) =
      (1 - t) * extensionOf (fun k => g (2 * k)) tau
        + t * extensionOf (fun k => g (2 * k + 1)) tau := by
  have hlen : (2 : Nat) ^ (t :: tau).length = 2 * 2 ^ tau.length := by
    simp only [List.length_cons, Nat.pow_succ, Nat.mul_comm]
  unfold extensionOf
  rw [hlen, ← GateDenseRound.interleave_sum (fun i => rowProdFrom 0 (t :: tau) i * g i)]
  have he : ((List.range (2 ^ tau.length)).map
        (fun s => rowProdFrom 0 (t :: tau) (2 * s) * g (2 * s)))
      = (List.range (2 ^ tau.length)).map
        (fun s => (1 - t) * (rowProdFrom 0 tau s * g (2 * s))) := by
    refine List.map_congr_left ?_
    intro s _
    rw [row_prod_even, mul_assoc]
  have ho : ((List.range (2 ^ tau.length)).map
        (fun s => rowProdFrom 0 (t :: tau) (2 * s + 1) * g (2 * s + 1)))
      = (List.range (2 ^ tau.length)).map
        (fun s => t * (rowProdFrom 0 tau s * g (2 * s + 1))) := by
    refine List.map_congr_left ?_
    intro s _
    rw [row_prod_odd, mul_assoc]
  rw [he, ho, sum_map_mul_left, sum_map_mul_left]

/-! ## 4. The vanishing set of the extension, and its size -/

/-- The domain of the challenge tuple: `n` independently drawn coordinates. -/
abbrev Tuple (n : Nat) := Fin n → Element

/-- The tuple of an adopted tau list. -/
def tupleOf (tau : List Element) : Tuple tau.length := tau.get

theorem ofFn_tupleOf (tau : List Element) : List.ofFn (tupleOf tau) = tau :=
  List.ofFn_get tau

/-- The vanishing set of the extension in `n` variables. -/
def vanishingSet (n : Nat) (g : Nat → Element) : Finset (Tuple n) :=
  Finset.univ.filter (fun r => extensionOf g (List.ofFn r) = 0)

theorem mem_vanishingSet (n : Nat) (g : Nat → Element) (r : Tuple n) :
    r ∈ vanishingSet n g ↔ extensionOf g (List.ofFn r) = 0 := by
  simp only [vanishingSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Card of the fibre of the head coordinate, written as a sum over the tail. -/
theorem card_filter_pi_succ (n : Nat) (P : Tuple (n + 1) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card
      = ∑ s : Tuple n, (Finset.univ.filter (fun t : Element => P (Fin.cons t s))).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun r : Tuple (n + 1) => Fin.tail r) (t := (Finset.univ : Finset (Tuple n)))
    (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl ?_
  intro s _
  have himg : (Finset.univ.filter P).filter (fun r => Fin.tail r = s)
      = (Finset.univ.filter (fun t : Element => P (Fin.cons t s))).image
        (fun t => Fin.cons t s) := by
    apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hP, ht⟩
      refine ⟨r 0, ?_, ?_⟩
      · rw [← ht, Fin.cons_self_tail]; exact hP
      · rw [← ht, Fin.cons_self_tail]
    · rintro ⟨t, hP, rfl⟩
      exact ⟨hP, by simp⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => by
    have h := congrFun hab 0
    simpa using h)]

/-- The head-coordinate roots of the affine form with endpoints `a` (at `0`)
and `b` (at `1`), inside an arbitrary domain. -/
def rootPoints (a b : Element) (domain : Finset Element) : Finset Element :=
  domain.filter (fun t => (1 - t) * a + t * b = 0)

/-- At most one head coordinate kills an affine form whose two cube endpoints
are not both zero. -/
theorem card_root_le_one (a b : Element) (hab : ¬ (a = 0 ∧ b = 0)) (domain : Finset Element) :
    (rootPoints a b domain).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' : a + x * (b - a) = 0 := by
    have h := (Finset.mem_filter.mp hx).2
    linear_combination h
  have hy' : a + y * (b - a) = 0 := by
    have h := (Finset.mem_filter.mp hy).2
    linear_combination h
  have hsub : (x - y) * (b - a) = 0 := by linear_combination hx' - hy'
  rcases mul_eq_zero.mp hsub with h | h
  · linear_combination h
  · exfalso
    have hba : b = a := by linear_combination h
    have ha : a = 0 := by
      rw [hba] at hx'
      simpa using hx'
    exact hab ⟨ha, hba.trans ha⟩

/-! ### The multilinear Schwartz--Zippel count -/

theorem extensionOf_nil (g : Nat → Element) : extensionOf g [] = g 0 := by
  simp [extensionOf, rowProdFrom, show List.range 1 = [0] from rfl]

theorem ofFn_cons (n : Nat) (t : Element) (s : Tuple n) :
    List.ofFn (Fin.cons t s) = t :: List.ofFn s := by
  rw [List.ofFn_succ]
  simp

theorem extensionOf_ofFn_cons (n : Nat) (g : Nat → Element) (t : Element) (s : Tuple n) :
    extensionOf g (List.ofFn (Fin.cons t s))
      = (1 - t) * extensionOf (fun k => g (2 * k)) (List.ofFn s)
        + t * extensionOf (fun k => g (2 * k + 1)) (List.ofFn s) := by
  rw [ofFn_cons, extensionOf_cons]

theorem card_tuple_univ (n : Nat) :
    (Finset.univ : Finset (Tuple n)).card = Fintype.card Element ^ n := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- The pure-`Nat` arithmetic of one Schwartz--Zippel step, stated over a
variable field size so that no tactic ever tries to evaluate `Fintype.card`. -/
theorem schwartz_zippel_step (n Zc Vc q : Nat) (hcount : Vc ≤ Zc * q + q ^ n)
    (hZcard : Zc * q ≤ n * q ^ n) : Vc * q ≤ (n + 1) * q ^ (n + 1) := by
  calc Vc * q ≤ (Zc * q + q ^ n) * q := Nat.mul_le_mul_right _ hcount
    _ = Zc * q * q + q ^ (n + 1) := by ring
    _ ≤ n * q ^ n * q + q ^ (n + 1) := Nat.add_le_add_right (Nat.mul_le_mul_right _ hZcard) _
    _ = (n + 1) * q ^ (n + 1) := by ring

/-- (3) MULTILINEAR SCHWARTZ--ZIPPEL, EXACT FORM PROVED.  If some value of the
Boolean cube in `n` variables is nonzero, then the number of challenge tuples
in `(Element)^n` at which the extension vanishes, multiplied by the field size
`|F| = p^3`, is at most `n * |F|^n`.  Equivalently the vanishing set has at
most `n * |F|^(n-1)` points, i.e. density at most `n / |F|`.  This is the
Schwartz--Zippel bound at TOTAL DEGREE at most `n`; it is NOT the sharper exact
multilinear vanishing count, and nothing sharper is claimed. -/
theorem vanishing_card_bound : ∀ (n : Nat) (g : Nat → Element),
    (∃ j, j < 2 ^ n ∧ g j ≠ 0) →
    (vanishingSet n g).card * Fintype.card Element ≤ n * Fintype.card Element ^ n := by
  intro n
  induction n with
  | zero =>
      intro g hg
      obtain ⟨j, hj, hgj⟩ := hg
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      have hempty : vanishingSet 0 g = ∅ := by
        apply Finset.eq_empty_of_forall_not_mem
        intro r hr
        rw [mem_vanishingSet] at hr
        have hnil : List.ofFn r = [] := by simp
        rw [hnil, extensionOf_nil] at hr
        exact hgj hr
      -- NOTE: never let `simp`/`ring`/`norm_num` see `Fintype.card Element`;
      -- its Nat simprocs try to evaluate the p^3-element `Finset.univ`.
      have hL : (0 : Nat) * Fintype.card Element = 0 := Nat.zero_mul _
      have hR : (0 : Nat) * Fintype.card Element ^ 0 = 0 := Nat.zero_mul _
      rw [hempty, Finset.card_empty, hL, hR]
  | succ n ih =>
      intro g hg
      -- the two halves of the value family, split on the head coordinate
      have hfilter : ∀ s : Tuple n,
          Finset.univ.filter (fun t : Element => extensionOf g (List.ofFn (Fin.cons t s)) = 0)
            = rootPoints (extensionOf (fun k => g (2 * k)) (List.ofFn s))
                (extensionOf (fun k => g (2 * k + 1)) (List.ofFn s)) Finset.univ := by
        intro s
        apply Finset.ext
        intro t
        simp only [rootPoints, Finset.mem_filter, Finset.mem_univ, true_and,
          extensionOf_ofFn_cons n g t s]
      have hcount : (vanishingSet (n + 1) g).card
          = ∑ s : Tuple n, (rootPoints (extensionOf (fun k => g (2 * k)) (List.ofFn s))
              (extensionOf (fun k => g (2 * k + 1)) (List.ofFn s)) Finset.univ).card := by
        rw [vanishingSet, card_filter_pi_succ n (fun r => extensionOf g (List.ofFn r) = 0)]
        exact Finset.sum_congr rfl (fun s _ => congrArg Finset.card (hfilter s))
      -- the joint vanishing set of the two halves is itself small
      have hZcard : (Finset.univ.filter (fun s : Tuple n =>
            extensionOf (fun k => g (2 * k)) (List.ofFn s) = 0 ∧
            extensionOf (fun k => g (2 * k + 1)) (List.ofFn s) = 0)).card
          * Fintype.card Element ≤ n * Fintype.card Element ^ n := by
        obtain ⟨j, hj, hgj⟩ := hg
        have hj2 : j / 2 < 2 ^ n := by omega
        by_cases hpar : j % 2 = 0
        · have hval : (fun k => g (2 * k)) (j / 2) ≠ 0 := by
            show g (2 * (j / 2)) ≠ 0
            rw [show 2 * (j / 2) = j by omega]
            exact hgj
          refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card ?_))
            (ih (fun k => g (2 * k)) ⟨j / 2, hj2, hval⟩)
          intro x hx
          rw [mem_vanishingSet]
          exact ((Finset.mem_filter.mp hx).2).1
        · have hval : (fun k => g (2 * k + 1)) (j / 2) ≠ 0 := by
            show g (2 * (j / 2) + 1) ≠ 0
            rw [show 2 * (j / 2) + 1 = j by omega]
            exact hgj
          refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card ?_))
            (ih (fun k => g (2 * k + 1)) ⟨j / 2, hj2, hval⟩)
          intro x hx
          rw [mem_vanishingSet]
          exact ((Finset.mem_filter.mp hx).2).2
      -- at most one head root per tail outside the joint vanishing set
      have hfib : ∑ s : Tuple n, (rootPoints (extensionOf (fun k => g (2 * k)) (List.ofFn s))
              (extensionOf (fun k => g (2 * k + 1)) (List.ofFn s)) Finset.univ).card
          ≤ (Finset.univ.filter (fun s : Tuple n =>
              extensionOf (fun k => g (2 * k)) (List.ofFn s) = 0 ∧
              extensionOf (fun k => g (2 * k + 1)) (List.ofFn s) = 0)).card
              * Fintype.card Element + Fintype.card Element ^ n := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Tuple n))
          (fun s : Tuple n => extensionOf (fun k => g (2 * k)) (List.ofFn s) = 0 ∧
            extensionOf (fun k => g (2 * k + 1)) (List.ofFn s) = 0)]
        refine add_le_add ?_ ?_
        · have ha : ∀ s ∈ Finset.univ.filter (fun s : Tuple n =>
              extensionOf (fun k => g (2 * k)) (List.ofFn s) = 0 ∧
              extensionOf (fun k => g (2 * k + 1)) (List.ofFn s) = 0),
              (rootPoints (extensionOf (fun k => g (2 * k)) (List.ofFn s))
                (extensionOf (fun k => g (2 * k + 1)) (List.ofFn s)) Finset.univ).card
                ≤ Fintype.card Element := by
            intro s _
            rw [← Finset.card_univ]
            exact Finset.card_filter_le _ _
          have h1 := Finset.sum_le_card_nsmul _ _ (Fintype.card Element) ha
          rwa [smul_eq_mul] at h1
        · have hb : ∀ s ∈ Finset.univ.filter (fun s : Tuple n =>
              ¬ (extensionOf (fun k => g (2 * k)) (List.ofFn s) = 0 ∧
                 extensionOf (fun k => g (2 * k + 1)) (List.ofFn s) = 0)),
              (rootPoints (extensionOf (fun k => g (2 * k)) (List.ofFn s))
                (extensionOf (fun k => g (2 * k + 1)) (List.ofFn s)) Finset.univ).card ≤ 1 :=
            fun s hs => card_root_le_one _ _ ((Finset.mem_filter.mp hs).2) Finset.univ
          have h1 := Finset.sum_le_card_nsmul _ _ 1 hb
          rw [smul_eq_mul, Nat.mul_one] at h1
          refine h1.trans ?_
          rw [← card_tuple_univ n]
          exact Finset.card_filter_le _ _
      refine schwartz_zippel_step n _ _ (Fintype.card Element) ?_ hZcard
      rw [hcount]
      exact hfib


/-! ### Explicit and density forms of the bound -/

theorem vanishing_card_bound_explicit (n : Nat) (g : Nat → Element)
    (hg : ∃ j, j < 2 ^ n ∧ g j ≠ 0) :
    (vanishingSet n g).card * Arithmetic.modulus ^ 3
      ≤ n * (Arithmetic.modulus ^ 3) ^ n := by
  rw [← cardinality_exact]
  exact vanishing_card_bound n g hg

/-- Pure-`ℚ` density arithmetic, over variable sizes. -/
theorem density_of_count (c nn q m : Nat) (hq : 0 < q) (hm : 0 < m) (h : c * q ≤ nn * m) :
    (c : ℚ) / (m : ℚ) ≤ (nn : ℚ) / (q : ℚ) := by
  rw [div_le_div_iff (by exact_mod_cast hm) (by exact_mod_cast hq)]
  exact_mod_cast h

/-- (3, explicit uniform law) Under the uniform law on `n` independently drawn
field coordinates, the mass of the vanishing set of a nonzero multilinear
extension is at most `n / |F|` with `|F| = p^3`.  This is the same shape as the
adopted `OuterChallenge.uniform_tuple_probability_bound`: an EXPLICIT ideal law
over the tuple domain, NOT an assertion about any deterministic hash. -/
theorem vanishing_density_bound (n : Nat) (g : Nat → Element)
    (hg : ∃ j, j < 2 ^ n ∧ g j ≠ 0) :
    ((vanishingSet n g).card : ℚ) / ((Fintype.card Element : ℚ) ^ n)
      ≤ (n : ℚ) / (Fintype.card Element : ℚ) := by
  have hq : 0 < Fintype.card Element := Fintype.card_pos
  have hm : 0 < Fintype.card Element ^ n := Nat.pos_pow_of_pos n hq
  have h := density_of_count (vanishingSet n g).card n (Fintype.card Element)
    (Fintype.card Element ^ n) hq hm (vanishing_card_bound n g hg)
  rwa [Nat.cast_pow] at h

/-! ## 5. The zero-check bad event -/

/-- Every value of the Boolean cube is zero. -/
def CubeZero (n : Nat) (g : Nat → Element) : Prop := ∀ j, j < 2 ^ n → g j = 0

instance decidableCubeZero (n : Nat) (g : Nat → Element) : Decidable (CubeZero n g) :=
  Nat.decidableBallLT (2 ^ n) (fun j _ => g j = 0)

/-- BAD EVENT (multilinear zero check).  The set of challenge tuples at which
the eq-weighted Boolean-cube sum vanishes although some cube value does NOT.
Empty when every cube value is already zero: there is then nothing to detect.
This MIRRORS THE SHAPE of the adopted `ConditionalSoundness.roundBadSet`, whose
`a = b` branch is likewise `∅`.  It does not compose with `badSets` /
`BadEventFree`, which range over single field challenges rather than n-tuples. -/
def zeroCheckBadSet (n : Nat) (g : Nat → Element) : Finset (Tuple n) :=
  if CubeZero n g then ∅ else vanishingSet n g

theorem zeroCheckBadSet_empty (n : Nat) (g : Nat → Element) (h : CubeZero n g) :
    zeroCheckBadSet n g = ∅ := by rw [zeroCheckBadSet, if_pos h]

theorem zeroCheckBadSet_of_not_cube_zero (n : Nat) (g : Nat → Element) (h : ¬ CubeZero n g) :
    zeroCheckBadSet n g = vanishingSet n g := by rw [zeroCheckBadSet, if_neg h]

/-- (3, consumable) The bad set is small UNCONDITIONALLY: `n * |F|^(n-1)`
points out of `|F|^n`, stated without `Nat` subtraction. -/
theorem zeroCheckBadSet_card_bound (n : Nat) (g : Nat → Element) :
    (zeroCheckBadSet n g).card * Fintype.card Element ≤ n * Fintype.card Element ^ n := by
  by_cases h : CubeZero n g
  · calc (zeroCheckBadSet n g).card * Fintype.card Element = 0 := by
          rw [zeroCheckBadSet_empty n g h, Finset.card_empty, Nat.zero_mul]
      _ ≤ n * Fintype.card Element ^ n := Nat.zero_le _
  · rw [zeroCheckBadSet_of_not_cube_zero n g h]
    refine vanishing_card_bound n g ?_
    unfold CubeZero at h
    push_neg at h
    exact h

theorem zeroCheckBadSet_card_bound_explicit (n : Nat) (g : Nat → Element) :
    (zeroCheckBadSet n g).card * Arithmetic.modulus ^ 3
      ≤ n * (Arithmetic.modulus ^ 3) ^ n := by
  rw [← cardinality_exact]
  exact zeroCheckBadSet_card_bound n g

theorem zeroCheckBadSet_density_bound (n : Nat) (g : Nat → Element) :
    ((zeroCheckBadSet n g).card : ℚ) / ((Fintype.card Element : ℚ) ^ n)
      ≤ (n : ℚ) / (Fintype.card Element : ℚ) := by
  have hq : 0 < Fintype.card Element := Fintype.card_pos
  have hm : 0 < Fintype.card Element ^ n := Nat.pos_pow_of_pos n hq
  have h := density_of_count (zeroCheckBadSet n g).card n (Fintype.card Element)
    (Fintype.card Element ^ n) hq hm (zeroCheckBadSet_card_bound n g)
  rwa [Nat.cast_pow] at h

/-- (4) THE ZERO-CHECK STEP.  A vanishing eq-weighted sum at a challenge tuple
OUTSIDE the bad set forces every Boolean-cube value to be zero. -/
theorem cube_zero_of_extension_zero (n : Nat) (g : Nat → Element) (r : Tuple n)
    (hzero : extensionOf g (List.ofFn r) = 0) (hgood : r ∉ zeroCheckBadSet n g) :
    ∀ j, j < 2 ^ n → g j = 0 := by
  by_cases h : CubeZero n g
  · exact h
  · exact absurd (by
      rw [zeroCheckBadSet_of_not_cube_zero n g h, mem_vanishingSet]
      exact hzero) hgood

/-- The same step against a tau LIST, the shape the audit's transcript columns
have (`TranscriptProvenance.gateTauColumn`). -/
theorem cube_zero_of_extension_zero_at_tau (g : Nat → Element) (tau : List Element)
    (hzero : extensionOf g tau = 0)
    (hgood : tupleOf tau ∉ zeroCheckBadSet tau.length g) :
    ∀ j, j < 2 ^ tau.length → g j = 0 :=
  cube_zero_of_extension_zero tau.length g (tupleOf tau)
    (by rw [ofFn_tupleOf]; exact hzero) hgood

/-! ## 6. The consumable gate-lane corollary -/

open GateSuffixPolynomial GateDenseRound

/-- The all-gates aggregate of one Boolean row WITHOUT the eq weight: exactly
the `evalCombined` call the adopted `GateDenseRound.rowTerm` makes
(gate_ext3_v2.rs:126-132).  The `none` branch is the same totalisation the
adopted `rowElement` uses; it is not a zero-default read standing in for a
source bound (`GateDenseRound.cube_reads_bounded` records the real bounds). -/
def gateValue (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (index : Nat) : Element :=
  match GatesComplete.evalCombined c gates
      (t.wires.map (fun column => (column.getD index 0).toVerifier))
      (t.constants.map (fun column => (column.getD index 0).toVerifier))
      publicHash alpha.toVerifier with
  | some v => NormPolynomial.lift v
  | none => 0

/-- The adopted row value factors as (eq weight) * (gate aggregate). -/
theorem rowElement_is_eq_times_gate (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (index : Nat) :
    rowElement c gates publicHash alpha t index
      = t.eq.getD index 0 * gateValue c gates publicHash alpha t index := by
  unfold rowElement rowTerm gateValue
  cases GatesComplete.evalCombined c gates
      (t.wires.map (fun column => (column.getD index 0).toVerifier))
      (t.constants.map (fun column => (column.getD index 0).toVerifier))
      publicHash alpha.toVerifier with
  | none => exact (mul_zero _).symm
  | some v => rfl

/-- (4) The adopted `cubeSum` over the full cube IS the multilinear extension
of the gate aggregate, evaluated at `tau`, whenever the prover's eq table is
the one `ext3_eq_evals(tau)` builds (the adopted `GateEqProvenance` content). -/
theorem cubeSum_is_extension (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (tau : List Element)
    (heq : t.eq = eqTable tau) :
    cubeSum c gates publicHash alpha t (2 ^ tau.length)
      = extensionOf (gateValue c gates publicHash alpha t) tau := by
  unfold cubeSum extensionOf
  refine congrArg List.sum (List.map_congr_left ?_)
  intro i hi
  rw [rowElement_is_eq_times_gate, heq, eq_table_getD tau i (List.mem_range.mp hi)]

/-- (4) THE CONSUMABLE COROLLARY.  If the eq-weighted Boolean-cube sum of the
gate aggregate vanishes at a `tau` OUTSIDE the zero-check bad set, then EVERY
Boolean row of the cube is zero: the gate aggregate is zero there, the adopted
`rowElement` is zero, and the adopted `rowTerm` returns zero whenever it
returns anything.  HONEST-PROVER SCOPE is unchanged: this is a statement about
the supplied tables, not an extraction claim. -/
theorem gate_rows_vanish (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (tau : List Element)
    (heq : t.eq = eqTable tau)
    (hsum : cubeSum c gates publicHash alpha t (2 ^ tau.length) = 0)
    (hgood : tupleOf tau ∉ zeroCheckBadSet tau.length (gateValue c gates publicHash alpha t)) :
    ∀ i, i < 2 ^ tau.length →
      gateValue c gates publicHash alpha t i = 0 ∧
      rowElement c gates publicHash alpha t i = 0 ∧
      ∀ v, rowTerm c gates publicHash alpha t i = some v → v = Verifier.zero := by
  have hz := cube_zero_of_extension_zero_at_tau (gateValue c gates publicHash alpha t) tau
    (by rw [← cubeSum_is_extension c gates publicHash alpha t tau heq]; exact hsum) hgood
  intro i hi
  have hrow : rowElement c gates publicHash alpha t i = 0 := by
    rw [rowElement_is_eq_times_gate, hz i hi, mul_zero]
  refine ⟨hz i hi, hrow, ?_⟩
  intro v hv
  have h1 : rowElement c gates publicHash alpha t i = NormPolynomial.lift v := by
    unfold rowElement
    rw [hv]
  have h2 : NormPolynomial.lift v = (0 : Element) := by rw [← h1, hrow]
  exact congrArg Element.toVerifier h2

/-- (4) The same conclusion from a ROUND ENDPOINT SUM, via the adopted
`GateDenseRound.endpoint_sum_is_cube_sum`: `f(0)+f(1) = 0` at the first round
is exactly the zero cube sum. -/
theorem gate_rows_vanish_of_endpoint_sum (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (tau : List Element)
    (half : Nat) (hhalf : 2 * half = 2 ^ tau.length)
    (heq : t.eq = eqTable tau)
    (hsum : roundElement c gates publicHash alpha 0 t half
      + roundElement c gates publicHash alpha 1 t half = 0)
    (hgood : tupleOf tau ∉ zeroCheckBadSet tau.length (gateValue c gates publicHash alpha t)) :
    ∀ i, i < 2 ^ tau.length →
      gateValue c gates publicHash alpha t i = 0 ∧
      rowElement c gates publicHash alpha t i = 0 ∧
      ∀ v, rowTerm c gates publicHash alpha t i = some v → v = Verifier.zero := by
  refine gate_rows_vanish c gates publicHash alpha t tau heq ?_ hgood
  rw [← hhalf, ← endpoint_sum_is_cube_sum c gates publicHash alpha t half]
  exact hsum

/-- (4) The transcript-derived form.  `tau` is the ADOPTED transcript-derived
gate tau column (`TranscriptProvenance.gateTauColumn`), the eq table's
provenance is the ADOPTED `EqTableProvenance.GateEqProvenance`, and the bad set
is indexed by the derived width `c.degreeBits`
(`TranscriptProvenance.derived_column_lengths`).  A later module has only to
discharge the `hgood` membership for the actually drawn tau. -/
theorem gate_rows_vanish_of_derived_tau
    (hash : TranscriptProvenance.Hash) (cfg : Verifier.Config) (p : Verifier.Proof)
    (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (s : GateTerminalBinding.ProverState)
    (hprov : EqTableProvenance.GateEqProvenance s (TranscriptProvenance.gateTauColumn hash cfg p))
    (hsum : cubeSum c gates publicHash alpha s.tables (2 ^ cfg.degreeBits) = 0)
    (hgood : tupleOf (TranscriptProvenance.gateTauColumn hash cfg p)
      ∉ zeroCheckBadSet (TranscriptProvenance.gateTauColumn hash cfg p).length
          (gateValue c gates publicHash alpha s.tables)) :
    ∀ i, i < 2 ^ cfg.degreeBits →
      gateValue c gates publicHash alpha s.tables i = 0 ∧
      rowElement c gates publicHash alpha s.tables i = 0 ∧
      ∀ v, rowTerm c gates publicHash alpha s.tables i = some v → v = Verifier.zero := by
  have hlen : (TranscriptProvenance.gateTauColumn hash cfg p).length = cfg.degreeBits :=
    (TranscriptProvenance.derived_column_lengths hash cfg p).2
  have heq : (s.tables).eq = eqTable (TranscriptProvenance.gateTauColumn hash cfg p) := hprov.1
  have h := gate_rows_vanish c gates publicHash alpha s.tables
    (TranscriptProvenance.gateTauColumn hash cfg p) heq (by rw [hlen]; exact hsum) hgood
  rw [hlen] at h
  exact h

/-! ## 7. Concrete examples -/

/-- Values on the two-row cube: `0` at row `0`, `1` at row `1`. -/
def exampleValues : Nat → Element := fun i => if i = 1 then 1 else 0

theorem example_value_nonzero : exampleValues 1 ≠ 0 := by decide

theorem example_bool_point : boolPoint 1 1 = [1] := by decide

theorem example_extension_at_one : extensionOf exampleValues [1] = 1 := by decide

theorem example_extension_at_zero : extensionOf exampleValues [0] = 0 := by decide

/-- (5a) A nonzero cube value forces a NONZERO extension: it is already nonzero
at the Boolean point of that very row. -/
theorem example_extension_nonzero : extensionOf exampleValues (boolPoint 1 1) ≠ 0 :=
  extensionOf_ne_zero_at_boolean_point exampleValues 1 1 (by decide) example_value_nonzero

/-- (5a, two variables) The extension really does reproduce the supplied values
at every Boolean point of the cube, in the adopted low-bit-first order. -/
def exampleValues2 : Nat → Element := fun i => if i = 2 then 1 else 0

theorem example_two_variable_agreement :
    boolPoint 2 2 = [0, 1] ∧
    extensionOf exampleValues2 (boolPoint 2 0) = 0 ∧
    extensionOf exampleValues2 (boolPoint 2 1) = 0 ∧
    extensionOf exampleValues2 (boolPoint 2 2) = 1 ∧
    extensionOf exampleValues2 (boolPoint 2 3) = 0 := by decide

theorem example_not_cube_zero : ¬ CubeZero 1 exampleValues := fun h =>
  example_value_nonzero (h 1 (by decide))

/-- (5b) THE BAD SET IS GENUINELY NONEMPTY, so the `tau` condition of the
corollary is NOT vacuous: at `tau = [0]` the eq-weighted cube sum vanishes even
though the cube value of row `1` does not. -/
theorem example_bad_set_nonempty : (zeroCheckBadSet 1 exampleValues).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [zeroCheckBadSet_of_not_cube_zero 1 exampleValues example_not_cube_zero, mem_vanishingSet]
  have hofn : List.ofFn (fun _ : Fin 1 => (0 : Element)) = [0] := by simp
  rw [hofn]
  exact example_extension_at_zero

theorem example_tau_condition_necessary :
    exampleValues 1 ≠ 0 ∧ extensionOf exampleValues [0] = 0 ∧
      extensionOf exampleValues [1] ≠ 0 :=
  ⟨example_value_nonzero, example_extension_at_zero, by decide⟩

/-- (5b) …and a `tau` OUTSIDE the bad set does exist for the same values. -/
theorem example_good_tau :
    (fun _ => (1 : Element)) ∉ zeroCheckBadSet 1 exampleValues := by
  rw [zeroCheckBadSet_of_not_cube_zero 1 exampleValues example_not_cube_zero, mem_vanishingSet]
  have hofn : List.ofFn (fun _ : Fin 1 => (1 : Element)) = [1] := by simp
  rw [hofn, example_extension_at_one]
  decide

end Audit.Wire3.ZeroCheckSemantics
