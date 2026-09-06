import Audit.Wire3.Verifier

/-!
# Concrete formal norm/logUp terminal (runtime snapshot becfe98e)

Correspondence: OuterLogupExt3Verifier._denominatorCoordinates, _formalAdjugate,
_formalNormFromAdjugate, _recomposeFormalAdjugate, _permutationTerminalUnchecked,
_accumulateWireInPlace, _eqEvaluation, _subgroupEvaluation, and Rust
permutation/norm_logup.rs::evaluate_joint_norm_logup_terminal_with_public_inputs.

The PI part uses the ordered direct Rust loop, retaining duplicate map entries
and increasing eta powers. Solidity's row-cache/shared-bit implementation is an
algebraic optimization; PiSharedBits/PiCache prove its complete functional
equality with this direct loop using concrete algebra. Memory refinement is
NOT established. Eq/subgroup use the optimized Solidity formulas.
The downstream Algebra module proves equality with Rust's alternate formulas
inside these Lean models (not source execution refinement). square uses the
specialized Solidity formula; Algebra also proves its equality with the concrete
Ext3 multiplication.

All off-cube coordinates below are themselves Ext3 polynomials. No actual Ext3
inverse, Frobenius, field norm exponent, irreducibility, or PCS soundness is used.
Canonical outputs do not prove helper correctness, the permutation relation,
individual PI equality, or cancellation probability. Statement/PCS/transcript
authentication remain external obligations.

Unchecked helpers are totalized with zero fallback outside their indexed shape;
`checkedEvaluate` excludes those cases. Initial.logChallenges has an explicit
seven-value adapter layout [eta,beta,gamma,xi,lambda,rho,kappa], following the
generated protocol schema; constructing this list from a concrete transcript
is still a separate connection obligation. `tau` is Initial.logTau.
-/
namespace Audit.Wire3.Norm
open Verifier

def embed (n : Nat) : Ext3 := ⟨Arithmetic.fromBase n, Arithmetic.fromBase_canonical n⟩
def one : Ext3 := embed 1
def twice (x : Ext3) : Ext3 := add x x

/-- Specialized square, matching GoldilocksExt3.square's modular formula. -/
def square (x : Ext3) : Ext3 :=
  ⟨⟨Arithmetic.add (Arithmetic.mul x.val.c0 x.val.c0)
        (Arithmetic.mul 4 (Arithmetic.mul x.val.c1 x.val.c2)),
     Arithmetic.add (Arithmetic.mul 2 (Arithmetic.mul x.val.c0 x.val.c1))
        (Arithmetic.mul 2 (Arithmetic.mul x.val.c2 x.val.c2)),
     Arithmetic.add (Arithmetic.mul 2 (Arithmetic.mul x.val.c0 x.val.c2))
        (Arithmetic.mul x.val.c1 x.val.c1)⟩,
    Arithmetic.add_canonical _ _, Arithmetic.add_canonical _ _, Arithmetic.add_canonical _ _⟩

structure Coordinates where
  a : Ext3
  b : Ext3
  c : Ext3

def denominatorCoordinates (wire position beta gamma : Ext3) : Coordinates :=
  ⟨add (add (embed beta.val.c0) wire) (scalar position gamma.val.c0),
   add (embed beta.val.c1) (scalar position gamma.val.c1),
   add (embed beta.val.c2) (scalar position gamma.val.c2)⟩

def formalAdjugate (v : Coordinates) : Coordinates :=
  ⟨sub (square v.a) (twice (mul v.b v.c)),
   sub (twice (square v.c)) (mul v.a v.b),
   sub (square v.b) (mul v.a v.c)⟩

def formalNormFromAdjugate (v s : Coordinates) : Ext3 :=
  add (mul v.a s.a) (twice (add (mul v.c s.b) (mul v.b s.c)))

def formalNorm (v : Coordinates) : Ext3 := formalNormFromAdjugate v (formalAdjugate v)

def timesTheta (v : Ext3) : Ext3 :=
  ⟨⟨Arithmetic.add v.val.c2 v.val.c2, v.val.c0, v.val.c1⟩,
    Arithmetic.add_canonical _ _, v.property.1, v.property.2.1⟩

def timesThetaSquared (v : Ext3) : Ext3 :=
  ⟨⟨Arithmetic.add v.val.c1 v.val.c1, Arithmetic.add v.val.c2 v.val.c2, v.val.c0⟩,
    Arithmetic.add_canonical _ _, Arithmetic.add_canonical _ _, v.property.1⟩

def recomposeFormalAdjugate (s : Coordinates) : Ext3 :=
  add s.a (add (timesTheta s.b) (timesThetaSquared s.c))

def denominatorTerms (wire position beta gamma : Ext3) : Ext3 × Ext3 :=
  let v := denominatorCoordinates wire position beta gamma
  let s := formalAdjugate v
  (formalNormFromAdjugate v s, recomposeFormalAdjugate s)

theorem denominator_terms_share_formal_coordinates (wire position beta gamma : Ext3) :
    (denominatorTerms wire position beta gamma).1 =
      formalNorm (denominatorCoordinates wire position beta gamma) ∧
    (denominatorTerms wire position beta gamma).2 =
      recomposeFormalAdjugate (formalAdjugate (denominatorCoordinates wire position beta gamma)) :=
  ⟨rfl, rfl⟩

theorem formal_norm_canonical (v : Coordinates) : Arithmetic.Canonical (formalNorm v).val :=
  (formalNorm v).property

theorem denominator_terms_canonical (wire position beta gamma : Ext3) :
    Arithmetic.Canonical (denominatorTerms wire position beta gamma).1.val ∧
    Arithmetic.Canonical (denominatorTerms wire position beta gamma).2.val :=
  ⟨(denominatorTerms wire position beta gamma).1.property,
   (denominatorTerms wire position beta gamma).2.property⟩

theorem theta_rotation_exact (v : Ext3) :
    (timesTheta v).val = ⟨Arithmetic.add v.val.c2 v.val.c2, v.val.c0, v.val.c1⟩ := rfl

def eqFactor (tau x : Ext3) : Ext3 := add (sub (sub one tau) x) (twice (mul tau x))
def subgroupFactor (generator : Base) (x : Ext3) : Ext3 :=
  add one (scalar x (Arithmetic.add generator.val (Arithmetic.modulus - 1)))

/-- Left-to-right product loop, in the exact supplied coordinate order. -/
def productLoop {α : Type} (factor : α → Ext3) (values : List α) (acc : Ext3) : Ext3 :=
  values.foldl (fun acc value => mul acc (factor value)) acc

def eqEvaluation (tau point : List Ext3) : Ext3 :=
  productLoop (fun pair => eqFactor pair.1 pair.2) (tau.zip point) one

def subgroupEvaluation (powers : List Base) (point : List Ext3) : Ext3 :=
  productLoop (fun pair => subgroupFactor pair.1 pair.2) (powers.zip point) one

theorem product_loop_append {α : Type} (factor : α → Ext3) (a b : List α) (acc : Ext3) :
    productLoop factor (a ++ b) acc = productLoop factor b (productLoop factor a acc) := by
  simp [productLoop, List.foldl_append]

theorem eq_loop_exact (tau point : List Ext3) :
    eqEvaluation tau point = (tau.zip point).foldl
      (fun acc pair => mul acc (add (sub (sub one pair.1) pair.2) (twice (mul pair.1 pair.2)))) one := rfl

theorem subgroup_loop_exact (powers : List Base) (point : List Ext3) :
    subgroupEvaluation powers point = (powers.zip point).foldl
      (fun acc pair => mul acc (add one
        (scalar pair.2 (Arithmetic.add pair.1.val (Arithmetic.modulus - 1))))) one := rfl

theorem eq_loop_no_truncated_coordinates (tau point : List Ext3) (h : tau.length = point.length) :
    (tau.zip point).length = point.length := by simp [List.length_zip, h]

theorem subgroup_loop_no_truncated_coordinates (powers : List Base) (point : List Ext3)
    (h : powers.length = point.length) : (powers.zip point).length = point.length := by
  simp [List.length_zip, h]

def booleanFactor (row coordinateIndex : Nat) (x : Ext3) : Ext3 :=
  if row / 2 ^ coordinateIndex % 2 = 0 then sub one x else x

def booleanRowEq (row : Nat) (point : List Ext3) : Ext3 :=
  productLoop (fun pair => booleanFactor row pair.1 pair.2) point.enum one

theorem boolean_factor_lsb_zero (row : Nat) (x : Ext3) :
    booleanFactor row 0 x = if row % 2 = 0 then sub one x else x := by simp [booleanFactor]

structure Challenges where
  beta : Ext3
  gamma : Ext3
  lambda : Ext3
  rho : Ext3
  kappa : Ext3
  eta : Ext3
  xi : Ext3
  tau : List Ext3

def challengeList (ch : Challenges) : List Ext3 :=
  [ch.eta, ch.beta, ch.gamma, ch.xi, ch.lambda, ch.rho, ch.kappa]

def challengesFromInitial (i : Initial) : Challenges :=
  ⟨i.logChallenges.getD 1 zero, i.logChallenges.getD 2 zero,
   i.logChallenges.getD 4 zero, i.logChallenges.getD 5 zero,
   i.logChallenges.getD 6 zero, i.logChallenges.getD 0 zero,
   i.logChallenges.getD 3 zero, i.logTau⟩

theorem challenges_roundtrip (ch : Challenges) (bytes : Bytes) (alpha : Ext3) (gateTau : List Ext3) :
    challengesFromInitial ⟨bytes, challengeList ch, ch.tau, alpha, gateTau⟩ = ch := rfl

theorem challenge_layout_length (ch : Challenges) : (challengeList ch).length = 7 := rfl

structure WireState where
  helperChecks : Ext3
  logupSum : Ext3
  lambdaPower : Ext3
  processed : Nat

def wireStart : WireState := ⟨zero, zero, one, 0⟩

def wireStep (c : Config) (ch : Challenges) (t : NormTerminalInput) (subgroup : Ext3)
    (index : Nat) (s : WireState) : WireState :=
  let wire := t.witness.getD index zero
  let identityPosition := scalar subgroup ((c.kIs.getD index (base 0)).val)
  let sigmaPosition := t.preprocessed.getD (c.numConstants + index) zero
  let idTerms := denominatorTerms wire identityPosition ch.beta ch.gamma
  let sigmaTerms := denominatorTerms wire sigmaPosition ch.beta ch.gamma
  let idHelper := t.normInverse.getD index zero
  let sigmaHelper := t.normInverse.getD (c.numRouted + index) zero
  let idZero := sub (mul idHelper idTerms.1) one
  let sigmaZero := sub (mul sigmaHelper sigmaTerms.1) one
  ⟨add s.helperChecks (mul s.lambdaPower (add idZero (mul ch.rho sigmaZero))),
   add s.logupSum (sub (mul idHelper idTerms.2) (mul sigmaHelper sigmaTerms.2)),
   mul s.lambdaPower ch.lambda, s.processed + 1⟩

def runWires (c : Config) (ch : Challenges) (t : NormTerminalInput) (subgroup : Ext3) :
    Nat → Nat → WireState → WireState
  | _, 0, s => s
  | index, count + 1, s => runWires c ch t subgroup (index + 1) count
      (wireStep c ch t subgroup index s)
termination_by _ count _ => count

theorem wire_step_processed (c : Config) (ch : Challenges) (t : NormTerminalInput)
    (subgroup : Ext3) (index : Nat) (s : WireState) :
    (wireStep c ch t subgroup index s).processed = s.processed + 1 := rfl

theorem wire_step_lambda (c : Config) (ch : Challenges) (t : NormTerminalInput)
    (subgroup : Ext3) (index : Nat) (s : WireState) :
    (wireStep c ch t subgroup index s).lambdaPower = mul s.lambdaPower ch.lambda := rfl

theorem run_wires_exact_count (c : Config) (ch : Challenges) (t : NormTerminalInput)
    (subgroup : Ext3) (index count : Nat) (s : WireState) :
    (runWires c ch t subgroup index count s).processed = s.processed + count := by
  induction count generalizing index s with
  | zero => simp [runWires]
  | succ count ih =>
      simpa only [runWires, wire_step_processed, Nat.add_assoc, Nat.add_comm 1 count] using
        (ih (index + 1) (wireStep c ch t subgroup index s))

theorem run_wires_append (c : Config) (ch : Challenges) (t : NormTerminalInput)
    (subgroup : Ext3) (index a b : Nat) (s : WireState) :
    runWires c ch t subgroup index (a + b) s =
      runWires c ch t subgroup (index + a) b (runWires c ch t subgroup index a s) := by
  induction a generalizing index s with
  | zero => simp [runWires]
  | succ a ih =>
      simpa only [runWires, Nat.succ_add, Nat.add_assoc, Nat.add_comm 1 a] using
        (ih (index + 1) (wireStep c ch t subgroup index s))

def multiplyRepeated (x multiplier : Ext3) : Nat → Ext3
  | 0 => x
  | n + 1 => multiplyRepeated (mul x multiplier) multiplier n
termination_by n => n

theorem run_wires_lambda_power (c : Config) (ch : Challenges) (t : NormTerminalInput)
    (subgroup : Ext3) (index count : Nat) (s : WireState) :
    (runWires c ch t subgroup index count s).lambdaPower = multiplyRepeated s.lambdaPower ch.lambda count := by
  induction count generalizing index s with
  | zero => simp [runWires, multiplyRepeated]
  | succ count ih =>
      simpa only [runWires, multiplyRepeated, wire_step_lambda] using
        (ih (index + 1) (wireStep c ch t subgroup index s))

def permutationTerminal (c : Config) (ch : Challenges) (t : NormTerminalInput) (point : List Ext3) : Ext3 :=
  let s := runWires c ch t (subgroupEvaluation c.subgroupPowers point) 0 c.numRouted wireStart
  add (mul (eqEvaluation ch.tau point) s.helperChecks) (mul ch.kappa s.logupSum)

structure Target where
  row : Nat
  column : Nat
  deriving DecidableEq, Repr

def targetAt (wireMap : Bytes) (index : Nat) : Target :=
  ⟨(wireMap.getD (3 * index) 0).toNat + 256 * (wireMap.getD (3 * index + 1) 0).toNat,
   (wireMap.getD (3 * index + 2) 0).toNat⟩

theorem target_bytes_in_bounds (wireMap : Bytes) (count index : Nat)
    (hshape : wireMap.length = 3 * count) (hi : index < count) :
    3 * index < wireMap.length ∧ 3 * index + 1 < wireMap.length ∧ 3 * index + 2 < wireMap.length := by omega

structure PiState where
  binding : Ext3
  etaPower : Ext3
  processed : Nat

def piStart : PiState := ⟨zero, one, 0⟩

def piStep (wireMap : Bytes) (witness point : List Ext3) (eta : Ext3)
    (s : PiState) (pair : Nat × Base) : PiState :=
  let target := targetAt wireMap pair.1
  let term := sub (witness.getD target.column zero) (embed pair.2.val)
  ⟨add s.binding (mul (mul s.etaPower (booleanRowEq target.row point)) term),
   mul s.etaPower eta, s.processed + 1⟩

def publicInputState (c : Config) (t : NormTerminalInput) (point : List Ext3) (eta : Ext3) : PiState :=
  t.publicInputs.enum.foldl (piStep c.publicInputWireMap t.witness point eta) piStart

def publicInputBinding (c : Config) (t : NormTerminalInput) (point : List Ext3) (eta : Ext3) : Ext3 :=
  (publicInputState c t point eta).binding

theorem pi_fold_count (wireMap : Bytes) (witness point : List Ext3) (eta : Ext3)
    (pairs : List (Nat × Base)) (s : PiState) :
    (pairs.foldl (piStep wireMap witness point eta) s).processed = s.processed + pairs.length := by
  induction pairs generalizing s with
  | nil => simp
  | cons pair pairs ih =>
      simpa [List.foldl_cons, piStep, Nat.add_assoc, Nat.add_comm 1 pairs.length] using
        ih (piStep wireMap witness point eta s pair)

theorem public_inputs_all_processed (c : Config) (t : NormTerminalInput) (point : List Ext3) (eta : Ext3) :
    (publicInputState c t point eta).processed = t.publicInputs.length := by
  simpa [publicInputState, piStart] using pi_fold_count c.publicInputWireMap t.witness point eta t.publicInputs.enum piStart

theorem pi_fold_eta_power (wireMap : Bytes) (witness point : List Ext3) (eta : Ext3)
    (pairs : List (Nat × Base)) (s : PiState) :
    (pairs.foldl (piStep wireMap witness point eta) s).etaPower = multiplyRepeated s.etaPower eta pairs.length := by
  induction pairs generalizing s with
  | nil => simp [multiplyRepeated]
  | cons pair pairs ih => simpa [List.foldl_cons, multiplyRepeated, piStep] using ih (piStep wireMap witness point eta s pair)

theorem public_input_power_matches_count (c : Config) (t : NormTerminalInput) (point : List Ext3) (eta : Ext3) :
    (publicInputState c t point eta).etaPower = multiplyRepeated one eta t.publicInputs.length := by
  simpa [publicInputState, piStart] using pi_fold_eta_power c.publicInputWireMap t.witness point eta t.publicInputs.enum piStart

theorem public_input_empty_is_zero (c : Config) (t : NormTerminalInput) (point : List Ext3) (eta : Ext3)
    (h : t.publicInputs = []) : publicInputBinding c t point eta = zero := by
  simp [publicInputBinding, publicInputState, h, piStart]

def evaluate (c : Config) (ch : Challenges) (t : NormTerminalInput) (point : List Ext3) : Ext3 :=
  add (permutationTerminal c ch t point) (mul ch.xi (publicInputBinding c t point ch.eta))

def shapeValid (c : Config) (ch : Challenges) (t : NormTerminalInput) (point : List Ext3) : Bool := decide (
  point.length = c.degreeBits ∧ ch.tau.length = point.length ∧
  c.subgroupPowers.length = point.length ∧ c.kIs.length = c.numRouted ∧
  c.numRouted ≤ c.numWires ∧ t.witness.length = c.numWires ∧
  t.preprocessed.length = c.numConstants + c.numRouted ∧ t.normInverse.length = 2 * c.numRouted ∧
  t.publicInputs.length = c.numPublicInputs ∧ c.publicInputWireMap.length = 3 * t.publicInputs.length ∧
  ∀ i, i < t.publicInputs.length →
    (targetAt c.publicInputWireMap i).column < c.numRouted ∧
    (targetAt c.publicInputWireMap i).row < 2 ^ point.length)

def checkedEvaluate (c : Config) (ch : Challenges) (t : NormTerminalInput) (point : List Ext3) : Option Ext3 :=
  if shapeValid c ch t point then some (evaluate c ch t point) else none

theorem checked_evaluate_success (c : Config) (ch : Challenges) (t : NormTerminalInput) (point : List Ext3)
    (v : Ext3) (h : checkedEvaluate c ch t point = some v) :
    shapeValid c ch t point = true ∧ v = evaluate c ch t point := by
  unfold checkedEvaluate at h
  split at h <;> simp_all

theorem checked_evaluation_index_bounds (c : Config) (ch : Challenges) (t : NormTerminalInput)
    (point : List Ext3) (h : shapeValid c ch t point = true) (index : Nat) (hi : index < c.numRouted) :
    index < t.witness.length ∧ index < c.kIs.length ∧ c.numConstants + index < t.preprocessed.length ∧
    index < t.normInverse.length ∧ c.numRouted + index < t.normInverse.length := by
  simp only [shapeValid, decide_eq_true_eq] at h
  omega

theorem checked_pi_index_bounds (c : Config) (ch : Challenges) (t : NormTerminalInput)
    (point : List Ext3) (h : shapeValid c ch t point = true) (index : Nat) (hi : index < t.publicInputs.length) :
    (targetAt c.publicInputWireMap index).column < t.witness.length ∧
    (targetAt c.publicInputWireMap index).row < 2 ^ point.length := by
  simp only [shapeValid, decide_eq_true_eq] at h
  have ht := h.2.2.2.2.2.2.2.2.2.2 index hi
  exact ⟨by omega, ht.2⟩

def normEvaluation (c : Config) (i : Initial) (t : NormTerminalInput) (point : List Ext3) : Ext3 :=
  evaluate c (challengesFromInitial i) t point

/-- Checked adapter for callers that have not yet established the explicit
    seven-value challenge contract. `withNormEvaluation` below is the unchecked
    Engine hook and does not add this missing check to Verifier.verify. -/
def checkedNormEvaluation (c : Config) (i : Initial) (t : NormTerminalInput)
    (point : List Ext3) : Option Ext3 :=
  if i.logChallenges.length = 7 then checkedEvaluate c (challengesFromInitial i) t point else none

theorem checked_adapter_success (c : Config) (i : Initial) (t : NormTerminalInput)
    (point : List Ext3) (v : Ext3) (h : checkedNormEvaluation c i t point = some v) :
    i.logChallenges.length = 7 ∧ shapeValid c (challengesFromInitial i) t point = true ∧
    v = normEvaluation c i t point := by
  unfold checkedNormEvaluation at h
  split at h
  · have hc := checked_evaluate_success c (challengesFromInitial i) t point v h
    exact ⟨‹i.logChallenges.length = 7›, hc.1, hc.2⟩
  · contradiction

theorem checked_adapter_rejects_wrong_challenge_count (c : Config) (i : Initial)
    (t : NormTerminalInput) (point : List Ext3) (h : i.logChallenges.length ≠ 7) :
    checkedNormEvaluation c i t point = none := by simp [checkedNormEvaluation, h]

def withNormEvaluation (e : Engine) : Engine := {e with normEvaluation := normEvaluation}

theorem engine_uses_complete_terminal (e : Engine) (c : Config) (i : Initial)
    (t : NormTerminalInput) (point : List Ext3) :
    (withNormEvaluation e).normEvaluation c i t point =
      add (permutationTerminal c (challengesFromInitial i) t point)
        (mul (challengesFromInitial i).xi (publicInputBinding c t point (challengesFromInitial i).eta)) := rfl

theorem terminal_result_canonical (c : Config) (ch : Challenges) (t : NormTerminalInput) (point : List Ext3) :
    Arithmetic.Canonical (evaluate c ch t point).val := (evaluate c ch t point).property

theorem engine_uses_same_statement_inputs (e : Engine) (c : Config) (i : Initial) (p : Proof) (point : List Ext3) :
    (withNormEvaluation e).logTerminal c i p point =
      evaluate c (challengesFromInitial i)
        ⟨p.used.logPreprocessed, p.used.logWitness, p.used.logNormInverse, p.publicInputs⟩ point := rfl

/-- Integration theorem: an accepting verifier with this concrete hook must
    check this computed formal terminal, not an arbitrary norm observation.
    The other verifier observations remain explicitly abstract. -/
theorem acceptance_requires_computed_terminal (e : Engine) (pin : Pinned) (chain : Nat)
    (c : Config) (p : Proof) (h : verify (withNormEvaluation e) pin chain c p = .ok ()) :
    evaluate c (challengesFromInitial ((withNormEvaluation e).initialTranscript c p))
      (normTerminalInput p) (derivedRounds (withNormEvaluation e) c p).logPoint =
        (derivedRounds (withNormEvaluation e) c p).logClaim := by
  have hs := verify_success_checks (withNormEvaluation e) pin chain c p h
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, hterminal, _, _⟩
  exact hterminal

end Audit.Wire3.Norm
