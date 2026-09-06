import Audit.Wire3.Arithmetic

/-!
# WHIR authenticated final-row equality slice (becfe98e)

Sources: SpongefishWhirVerify._phaseFinalVectorAndMerkle, _verifyFinalSplit,
_requireFinalOpening, _dotEqWithRow, _dotGroupedRow, _computeEvalPoints;
WhirLinearAlgebra.eqWeightsFrom/tensorProduct; GoldilocksExt3.reduceWithPowers.
Rust wrapper: commitment/whir_pcs.rs::verify_grouped calls native config.verify;
the pinned WHIR verifier's final opening loop evaluates every final-vector
univariate form against its authenticated, folded in-domain row. Its subsequent
final MLE fold is separately preflighted for exact shape/nonzero by the wrapper.

The concrete slice computes eq weights, tensor weights, row dot products,
univariate Horner evaluation, and compares EVERY supplied query position after
all groups authenticate. `Plan` is trusted state derived from validated WHIR
parameters and earlier transcript rounds, NOT additional prover input.
`authenticate` is an explicit root/indices/rows observation; Merkle/hash soundness,
hint decoding, query sampling/deduplication, PoW, OOD, all sumchecks, and final
linear-form equality are not proved. The model does not establish correspondence
from an actual transcript to Plan, nor array/Yul/Arkworks refinement.

One GroupPlan models the standard path (tensor weights in initial multi-vector
mode, ordinary eq weights after intermediate rounds). Several GroupPlans model
the split-initial path: each group's weights use its slice of the same vector
RLC, each tree authenticates separately, then query values add across groups.
The separate helpers below compute the weight formulas, but correspondence of
their arguments to actual transcript slices remains a caller obligation.

`finalSize = 2^finalRounds` is a validated-configuration boundary, not a new
per-query runtime guard. Zero finalRounds allows a singleton final vector.
Empty query lists are NOT rejected here: _challengeIndices(count=0) returns [].
Canonical production-profile sampling properties need a separate proof.
This is not the complete whirTail and not a WHIR soundness theorem.
-/

namespace Audit.Wire3.WhirTerminal
open Audit.Wire3.Arithmetic

abbrev Root := Fin (2 ^ 256)
abbrev Row := List Ext3
abbrev GroupRows := List Row

instance canonicalDecidable (v : Ext3) : Decidable (Canonical v) :=
  inferInstanceAs (Decidable (v.c0 < modulus ∧ v.c1 < modulus ∧ v.c2 < modulus))

def eqWeightStep (weights : List Ext3) (r : Ext3) : List Ext3 :=
  weights.bind (fun w => [emul w (esub one r), emul w r])

def eqWeights (randomness : List Ext3) : List Ext3 := randomness.foldl eqWeightStep [one]

/-- Vector-major tensor layout used by standard initial openings; applying it
    to each group's RLC slice gives _dotGroupedRow's identical block order. -/
def tensorWeights (rlc eqW : List Ext3) : List Ext3 :=
  rlc.bind (fun coefficient => eqW.map (emul coefficient))

def dot (weights row : List Ext3) : Ext3 :=
  (weights.zip row).foldl (fun acc pair => eadd acc (emul pair.1 pair.2)) zero

/-- The explicit final vector is a univariate coefficient vector at this check.
    It is NOT evaluated as an MLE at the queried domain point. -/
def polynomial (finalVector : List Ext3) (x : Ext3) : Ext3 :=
  finalVector.reverse.foldl (fun acc coefficient => eadd (emul acc x) coefficient) zero

structure GroupPlan where
  root : Root
  weights : List Ext3

structure Plan where
  groups : List GroupPlan
  indices : List Nat
  finalRounds : Nat
  finalSize : Nat
  domainGenerator : Nat
  numCosets : Nat
  cosetSize : Nat

def domainPoint (p : Plan) (index : Nat) : Ext3 :=
  fromBase (p.domainGenerator ^ (index / p.cosetSize + (index % p.cosetSize) * p.numCosets))

abbrev Authenticate := Root → List Nat → GroupRows → Bool

def rowsWellFormed (weights : List Ext3) (numQueries : Nat) (rows : GroupRows) : Bool :=
  decide (rows.length = numQueries) &&
    rows.all (fun row => decide (row.length = weights.length) &&
      row.all (fun value => decide (Canonical value)))

def verifyGroups (authenticate : Authenticate) (indices : List Nat) :
    List GroupPlan → List GroupRows → Bool
  | [], [] => true
  | plan :: plans, rows :: groups =>
      rowsWellFormed plan.weights indices.length rows && authenticate plan.root indices rows &&
        verifyGroups authenticate indices plans groups
  | _, _ => false

/-- A proof supplies rows only; the opened value is computed from the fixed
    weights and those SAME authenticated row values, never supplied separately. -/
def openedValue (plans : List GroupPlan) (groups : List GroupRows) (position : Nat) : Ext3 :=
  (plans.zip groups).foldl
    (fun acc pair => eadd acc (dot pair.1.weights (pair.2.getD position []))) zero

def queriesMatch (p : Plan) (finalVector : List Ext3) (groups : List GroupRows) : Bool :=
  p.indices.enum.all (fun query =>
    eq (polynomial finalVector (domainPoint p query.2))
      (openedValue p.groups groups query.1))

def boundaryShape (p : Plan) (finalVector : List Ext3) : Bool := decide (
  p.finalRounds < 256 ∧ p.finalSize = 2 ^ p.finalRounds ∧
  finalVector.length = p.finalSize ∧ 0 < p.groups.length ∧
  0 < p.cosetSize ∧ 0 < p.numCosets) &&
  finalVector.all (fun value => decide (Canonical value))

/-- Combined validated-context and final-row phase. This intentionally omits
    phaseFinalClaim, including its nonzero MLE-fold check. -/
def verifyFinalRows (authenticate : Authenticate) (p : Plan)
    (finalVector : List Ext3) (groups : List GroupRows) : Bool :=
  boundaryShape p finalVector && verifyGroups authenticate p.indices p.groups groups &&
    queriesMatch p finalVector groups

theorem eq_weights_empty : eqWeights [] = [one] := rfl

theorem eq_weights_one_round (r : Ext3) :
    eqWeights [r] = [emul one (esub one r), emul one r] := rfl

theorem tensor_weights_length (rlc eqW : List Ext3) :
    (tensorWeights rlc eqW).length = rlc.length * eqW.length := by
  induction rlc with
  | nil => simp [tensorWeights, List.bind]
  | cons r rs ih =>
      change (eqW.map (emul r) ++ tensorWeights rs eqW).length = (rs.length + 1) * eqW.length
      simp [ih, Nat.add_mul, Nat.add_comm]

theorem rows_well_formed_exact_count_and_columns (weights : List Ext3) (n : Nat) (rows : GroupRows)
    (h : rowsWellFormed weights n rows = true) :
    rows.length = n ∧ ∀ row ∈ rows, row.length = weights.length ∧ ∀ x ∈ row, Canonical x := by
  simpa [rowsWellFormed, List.all_eq_true] using h

theorem verified_groups_exact_count (auth : Authenticate) (indices : List Nat)
    (plans : List GroupPlan) (groups : List GroupRows)
    (h : verifyGroups auth indices plans groups = true) : groups.length = plans.length := by
  induction plans generalizing groups with
  | nil => cases groups <;> simp_all [verifyGroups]
  | cons p ps ih =>
      cases groups with
      | nil => simp [verifyGroups] at h
      | cons rows groups =>
          simp only [verifyGroups, Bool.and_eq_true] at h
          exact congrArg Nat.succ (ih groups h.2)

theorem verified_groups_authenticate_each_pair (auth : Authenticate) (indices : List Nat)
    (plans : List GroupPlan) (groups : List GroupRows)
    (h : verifyGroups auth indices plans groups = true) :
    ∀ pair ∈ plans.zip groups,
      rowsWellFormed pair.1.weights indices.length pair.2 = true ∧
      auth pair.1.root indices pair.2 = true := by
  induction plans generalizing groups with
  | nil => simp
  | cons p ps ih =>
      cases groups with
      | nil => simp [verifyGroups] at h
      | cons rows groups =>
          simp only [verifyGroups, Bool.and_eq_true] at h
          intro pair hp
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact h.1
          · exact ih groups h.2 pair hp

theorem final_rows_success (auth : Authenticate) (p : Plan) (v : List Ext3) (groups : List GroupRows)
    (h : verifyFinalRows auth p v groups = true) :
    boundaryShape p v = true ∧ verifyGroups auth p.indices p.groups groups = true ∧
      queriesMatch p v groups = true := by
  simpa only [verifyFinalRows, Bool.and_eq_true, and_assoc] using h

theorem closed_fold_canonical {α : Type} (f : Ext3 → α → Ext3)
    (hf : ∀ acc x, Canonical (f acc x)) (xs : List α) (acc : Ext3) (ha : Canonical acc) :
    Canonical (xs.foldl f acc) := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x _ ih => exact ih (f acc x) (hf acc x)

theorem polynomial_result_canonical (v : List Ext3) (x : Ext3) : Canonical (polynomial v x) :=
  closed_fold_canonical _ (fun _ _ => eadd_canonical _ _) _ zero zero_canonical

theorem opened_value_canonical (plans : List GroupPlan) (groups : List GroupRows) (position : Nat) :
    Canonical (openedValue plans groups position) :=
  closed_fold_canonical _ (fun _ _ => eadd_canonical _ _) _ zero zero_canonical

theorem successful_final_size_exact (auth : Authenticate) (p : Plan) (v : List Ext3)
    (groups : List GroupRows) (h : verifyFinalRows auth p v groups = true) :
    v.length = 2 ^ p.finalRounds ∧ p.finalRounds < 256 := by
  have hs := (final_rows_success auth p v groups h).1
  simp only [boundaryShape, Bool.and_eq_true, decide_eq_true_eq] at hs
  exact ⟨hs.1.2.2.1.trans hs.1.2.1, hs.1.1⟩

theorem successful_final_vector_nonempty (auth : Authenticate) (p : Plan) (v : List Ext3)
    (groups : List GroupRows) (h : verifyFinalRows auth p v groups = true) : 0 < v.length := by
  rw [(successful_final_size_exact auth p v groups h).1]
  exact Nat.pow_pos (by decide)

theorem successful_each_query_matches (auth : Authenticate) (p : Plan) (v : List Ext3)
    (groups : List GroupRows) (h : verifyFinalRows auth p v groups = true)
    (position index : Nat) (hi : (position, index) ∈ p.indices.enum) :
    normalize (polynomial v (domainPoint p index)) =
      normalize (openedValue p.groups groups position) := by
  have hq := (final_rows_success auth p v groups h).2.2
  simp only [queriesMatch, List.all_eq_true] at hq
  exact (normalized_equality_iff _ _).mp (hq (position, index) hi)

theorem successful_each_query_exact_equality (auth : Authenticate) (p : Plan) (v : List Ext3)
    (groups : List GroupRows) (h : verifyFinalRows auth p v groups = true)
    (position index : Nat) (hi : (position, index) ∈ p.indices.enum) :
    polynomial v (domainPoint p index) = openedValue p.groups groups position := by
  have he := successful_each_query_matches auth p v groups h position index hi
  simpa only [normalize_fixed (polynomial_result_canonical _ _),
    normalize_fixed (opened_value_canonical _ _ _)] using he

theorem any_query_mismatch_rejected (auth : Authenticate) (p : Plan) (v : List Ext3)
    (groups : List GroupRows) (position index : Nat) (hi : (position, index) ∈ p.indices.enum)
    (hm : normalize (polynomial v (domainPoint p index)) ≠
      normalize (openedValue p.groups groups position)) : verifyFinalRows auth p v groups = false := by
  cases h : verifyFinalRows auth p v groups with
  | false => rfl
  | true => exact False.elim (hm (successful_each_query_matches auth p v groups h position index hi))

theorem authentication_failure_rejects (auth : Authenticate) (p : Plan) (v : List Ext3)
    (groups : List GroupRows) (h : verifyGroups auth p.indices p.groups groups = false) :
    verifyFinalRows auth p v groups = false := by simp [verifyFinalRows, h]

theorem empty_queries_have_no_equality_checks (p : Plan) (v : List Ext3) (groups : List GroupRows)
    (h : p.indices = []) : queriesMatch p v groups = true := by simp [queriesMatch, h]

theorem zero_final_rounds_require_singleton (auth : Authenticate) (p : Plan) (v : List Ext3)
    (groups : List GroupRows) (h : verifyFinalRows auth p v groups = true) (hr : p.finalRounds = 0) :
    v.length = 1 := by simpa [hr] using (successful_final_size_exact auth p v groups h).1

theorem polynomial_zero_vector : polynomial [zero] one = zero := by
  simp [polynomial, emul_zero, zero_emul, eadd_zero, normalize_fixed zero_canonical]

def testRoot : Root := ⟨0, by decide⟩
def testPlan : Plan := ⟨[⟨testRoot, [one]⟩], [0], 0, 1, 1, 1, 1⟩

/-- Non-vacuity of the final-row phase alone: a zero polynomial and matching
    authenticated zero row pass this phase. The complete verifier's later
    phaseFinalClaim MUST reject its zero folded value; no full-proof claim. -/
theorem positive_row_phase_is_not_complete_whir :
    verifyFinalRows (fun _ _ _ => true) testPlan [zero] [[[zero]]] = true := by decide

end Audit.Wire3.WhirTerminal
