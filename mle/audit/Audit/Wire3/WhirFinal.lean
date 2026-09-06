import Audit.Wire3.WhirTerminal
import Audit.Wire3.Spongefish

/-!
# WHIR final sumcheck, final claim, and exhaustion (54400f9f)

Manual executable slice of SpongefishWhirVerify._phaseSumcheck (final use),
_foldEval, _phaseFinalClaim, and _verifyWhirProof's two EOF checks;
WhirLinearAlgebra.mleEvaluateUnivariateFrom/mleEvaluateEq; GoldilocksExt3.inv.
Rust correspondence: fixed WHIR 3db5dec verifier.rs final sumcheck/FinalClaim,
and whir_pcs.rs::verify_grouped's final nonzero preflight, final_claim.verify,
and check_eof. This model uses Solidity's explicit zero rejection and order.

The SAME `finalVector` argument first passes WhirTerminal.verifyFinalRows and
then the concrete final MLE fold. The round decoder, PoW verification and FS
challenge generation are function observations here, with a concrete byte-level
instantiation in WhirFinalSpongefish. The cursor carries the actual modeled
inner sponge digest/counter. These functions cannot set the running
sum or final randomness directly: those are constructed by the executable
quadratic recurrence. No field/PCS/FS soundness is asserted by observations.

Context is post-row trusted state from the unmodeled earlier WHIR phases. Its
prefix randomness, prior sum, round constraints, linear-form coefficients and
points, transcript cursor, and hint cursor must be derived from those phases.
`contextShape` checks internal context invariants; these are NOT claimed to be
new Solidity runtime guards. No proof connects byte parsing/Merkle to Context.

Concrete modular inverse follows norm/adjugate and 64-step binary exponentiation.
Its multiplicative-inverse identity for all nonzero canonical inputs and the
actual-operation finite-field structure are proved later in GoldilocksNorm and
GoldilocksExt3Field, using GoldilocksFoundation's concrete primality proof.
Assembly arithmetic/memory semantics and exception/refinement equivalence remain open.
This module's EOF proves cursor equality under decoder observations;
WhirFinalSpongefish proves the concrete engine's exact byte consumption.
WhirInitial/WhirPrefix model the initial phases but do not derive this final
Context through intermediate rounds and authenticated row reads. Transcript
security, PoW security, query probability and PCS soundness remain open.
-/

namespace Audit.Wire3.WhirFinal
open Audit.Wire3.Arithmetic
open WhirTerminal (canonicalDecidable)

abbrev Bytes := List UInt8

def modPowLoop : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, exponent, result => if exponent = 0 then some result else none
  | fuel + 1, b, exponent, result =>
      if exponent = 0 then some result else
      modPowLoop fuel (mul b b) (exponent / 2)
        (if exponent % 2 = 1 then mul result b else result)

def adjugate (a : Ext3) : Ext3 :=
  ⟨sub (mul a.c0 a.c0) (mul 2 (mul a.c1 a.c2)),
   sub (mul 2 (mul a.c2 a.c2)) (mul a.c0 a.c1),
   sub (mul a.c1 a.c1) (mul a.c0 a.c2)⟩

def norm (a : Ext3) : Nat :=
  let s := adjugate a
  add (mul a.c0 s.c0) (mul 2 (add (mul a.c2 s.c1) (mul a.c1 s.c2)))

def inverse (a : Ext3) : Option Ext3 :=
  if norm a = 0 then none else
  match modPowLoop 64 (norm a) (modulus - 2) 1 with
  | none => none
  | some n => some (scalar (adjugate a) n)

/-- Sum form, exactly _foldEval; do not silently replace by the difference-form
    Packed butterfly without a field-algebra equivalence proof. -/
def sumButterfly (a b r : Ext3) : Ext3 :=
  eadd (emul a (esub one r)) (emul b r)

def sumLayer (r : Ext3) : List Ext3 → List Ext3
  | a :: b :: rest => sumButterfly a b r :: sumLayer r rest
  | _ => []

def foldLayers : List Ext3 → List Ext3 → List Ext3
  | [], v => v
  | r :: rs, v => foldLayers rs (sumLayer r v)

/-- Last randomness first, matching eq-weight and native WHIR bit order. -/
def finalPolynomial (v randomness : List Ext3) : Ext3 :=
  (foldLayers randomness.reverse v).getD 0 zero

def univariateMLE (x : Ext3) (point : List Ext3) : Ext3 :=
  (point.reverse.foldl (fun acc r =>
    (emul acc.1 (eadd (esub one r) (emul r acc.2)), emul acc.2 acc.2)) (one, x)).1

def equalityMLE (point randomness : List Ext3) : Ext3 :=
  (point.zip randomness).foldl (fun acc pair =>
    emul acc (eadd (emul pair.1 pair.2) (emul (esub one pair.1) (esub one pair.2)))) one

structure RoundConstraint where
  numVariables : Nat
  coefficients : List Ext3
  points : List Ext3

structure LinearForm where
  coefficient : Ext3
  point : List Ext3

def subtractEntry (allRandomness : List Ext3) (entry : RoundConstraint) (value : Ext3) : Ext3 :=
  (entry.coefficients.zip entry.points).foldl (fun acc pair =>
    esub acc (emul (univariateMLE pair.2
      (allRandomness.drop (allRandomness.length - entry.numVariables))) pair.1)) value

def subtractConstraints (allRandomness : List Ext3) (entries : List RoundConstraint) (value : Ext3) : Ext3 :=
  entries.foldl (fun acc entry => subtractEntry allRandomness entry acc) value

def expectedLinearForm (forms : List LinearForm) (allRandomness : List Ext3) : Ext3 :=
  forms.foldl (fun acc form => eadd acc (emul form.coefficient (equalityMLE form.point allRandomness))) zero

structure Cursor where
  transcriptPos : Nat
  spongeState : Spongefish.Sponge
  deriving DecidableEq

structure RoundMessage where
  c0 : Ext3
  c2 : Ext3

structure State where
  cursor : Cursor
  sum : Ext3
  finalRandomness : List Ext3
  deriving DecidableEq

structure Context where
  rowPlan : WhirTerminal.Plan
  prefixRandomness : List Ext3
  priorSum : Ext3
  afterRows : Cursor
  hintPos : Nat
  totalVariables : Nat
  powThreshold : Nat
  roundConstraints : List RoundConstraint
  forms : List LinearForm

structure Engine where
  readMessage : Bytes → Cursor → Option (RoundMessage × Cursor)
  checkPow : Nat → Bytes → Cursor → Option Cursor
  challenge : Cursor → Option (Ext3 × Cursor)

def quadratic (claim : Ext3) (message : RoundMessage) (r : Ext3) : Ext3 :=
  let c1 := esub claim (eadd (eadd message.c0 message.c0) message.c2)
  eadd (emul (eadd (emul message.c2 r) c1) r) message.c0

def advance (s : State) (message : RoundMessage) (r : Ext3) (next : Cursor) : State :=
  ⟨next, quadratic s.sum message r, s.finalRandomness ++ [r]⟩

def roundStep (e : Engine) (threshold : Nat) (transcript : Bytes) (s : State) : Option State :=
  match e.readMessage transcript s.cursor with
  | none => none
  | some (message, afterMessage) =>
      if ¬ (Canonical message.c0 ∧ Canonical message.c2) then none else
      match e.checkPow threshold transcript afterMessage with
      | none => none
      | some afterPow => match e.challenge afterPow with
        | none => none
        | some (r, next) => if Canonical r then some (advance s message r next) else none

def runRounds (e : Engine) (threshold : Nat) (transcript : Bytes) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => match roundStep e threshold transcript s with
    | none => none
    | some next => runRounds e threshold transcript n next

def start (c : Context) : State := ⟨c.afterRows, c.priorSum, []⟩

def contextShape (c : Context) : Bool := decide (
  c.totalVariables = c.prefixRandomness.length + c.rowPlan.finalRounds ∧
  0 < c.totalVariables ∧ c.totalVariables < 256 ∧ 0 < c.forms.length) &&
  c.forms.all (fun form => decide (form.point.length = c.totalVariables)) &&
  c.roundConstraints.all (fun entry => decide (
    entry.coefficients.length = entry.points.length ∧ entry.numVariables ≤ c.totalVariables))

def finalClaim (c : Context) (v : List Ext3) (s : State) : Bool :=
  let poly := finalPolynomial v s.finalRandomness
  if isZero poly then false else
  match inverse poly with
  | none => false
  | some inv =>
      let allRandomness := c.prefixRandomness ++ s.finalRandomness
      eq (subtractConstraints allRandomness c.roundConstraints (emul s.sum inv))
        (expectedLinearForm c.forms allRandomness)

def exhausted (c : Context) (transcript hints : Bytes) (s : State) : Bool :=
  decide (s.cursor.transcriptPos = transcript.length ∧ c.hintPos = hints.length)

/-- No second or independently decoded final vector exists in this API. -/
def verifyEnd (auth : WhirTerminal.Authenticate) (e : Engine) (c : Context)
    (transcript hints : Bytes) (finalVector : List Ext3) (rows : List WhirTerminal.GroupRows) : Bool :=
  if contextShape c = false then false else
  if WhirTerminal.verifyFinalRows auth c.rowPlan finalVector rows = false then false else
  match runRounds e c.powThreshold transcript c.rowPlan.finalRounds (start c) with
  | none => false
  | some result => finalClaim c finalVector result && exhausted c transcript hints result

theorem inverse_zero_rejected : inverse zero = none := by rfl
set_option maxRecDepth 4096 in
theorem inverse_one_computes_one : inverse one = some one := by decide

theorem mod_pow_terminates_with_sufficient_bits (fuel b exponent result : Nat)
    (h : exponent < 2 ^ fuel) : ∃ output, modPowLoop fuel b exponent result = some output := by
  induction fuel generalizing b exponent result with
  | zero =>
      have he : exponent = 0 := by simp only [Nat.pow_zero] at h; omega
      exact ⟨result, by simp [modPowLoop, he]⟩
  | succ fuel ih =>
      by_cases he : exponent = 0
      · exact ⟨result, by simp [modPowLoop, he]⟩
      · have hb : exponent / 2 < 2 ^ fuel := by
          simp only [Nat.pow_succ] at h
          omega
        simpa [modPowLoop, he] using ih (mul b b) (exponent / 2)
          (if exponent % 2 = 1 then mul result b else result) hb

theorem inverse_nonzero_norm_does_not_exhaust_fuel (a : Ext3) (h : norm a ≠ 0) :
    ∃ result, inverse a = some result := by
  obtain ⟨n, hn⟩ := mod_pow_terminates_with_sufficient_bits 64 (norm a) (modulus - 2) 1 (by decide)
  exact ⟨scalar (adjugate a) n, by simp [inverse, h, hn]⟩

theorem sum_layer_length (r : Ext3) : ∀ v : List Ext3, (sumLayer r v).length = v.length / 2
  | [] => rfl
  | [_] => by simp [sumLayer]
  | a :: b :: rest => by simp only [sumLayer, List.length_cons, sum_layer_length r rest]; omega

theorem full_final_fold_has_one_value (randomness v : List Ext3)
    (h : v.length = 2 ^ randomness.length) : (foldLayers randomness v).length = 1 := by
  induction randomness generalizing v with
  | nil => simpa [foldLayers] using h
  | cons r rs ih =>
      apply ih
      rw [sum_layer_length, h]
      simp [List.length_cons, Nat.pow_succ, Nat.mul_comm]

theorem final_fold_uses_reverse_order (a b c d r0 r1 : Ext3) :
    finalPolynomial [a,b,c,d] [r0,r1] =
      sumButterfly (sumButterfly a b r1) (sumButterfly c d r1) r0 := rfl

theorem quadratic_reconstructs_linear_coefficient (claim : Ext3) (m : RoundMessage) (r : Ext3) :
    quadratic claim m r = eadd (emul (eadd (emul m.c2 r)
      (esub claim (eadd (eadd m.c0 m.c0) m.c2))) r) m.c0 := rfl

theorem round_step_success (e : Engine) (threshold : Nat) (bytes : Bytes) (s t : State)
    (h : roundStep e threshold bytes s = some t) :
    ∃ message afterMessage afterPow r next,
      e.readMessage bytes s.cursor = some (message, afterMessage) ∧
      Canonical message.c0 ∧ Canonical message.c2 ∧
      e.checkPow threshold bytes afterMessage = some afterPow ∧
      e.challenge afterPow = some (r, next) ∧ Canonical r ∧ t = advance s message r next := by
  unfold roundStep at h
  cases hm : e.readMessage bytes s.cursor with
  | none => simp [hm] at h
  | some pair =>
      rcases pair with ⟨m, am⟩
      simp only [hm] at h
      split at h
      · simp at h
      · rename_i hc
        have hc' : Canonical m.c0 ∧ Canonical m.c2 := by simpa using hc
        cases hp : e.checkPow threshold bytes am with
        | none => simp [hp] at h
        | some ap =>
            simp only [hp] at h
            cases hr : e.challenge ap with
            | none => simp [hr] at h
            | some pair =>
                rcases pair with ⟨r, next⟩
                simp only [hr] at h
                split at h
                · rename_i hrc
                  simp only [Option.some.injEq] at h
                  exact ⟨m, am, ap, r, next, rfl, hc'.1, hc'.2, hp, hr, hrc, h.symm⟩
                · simp at h

theorem round_step_adds_one_challenge (e : Engine) (threshold : Nat) (bytes : Bytes) (s t : State)
    (h : roundStep e threshold bytes s = some t) :
    t.finalRandomness.length = s.finalRandomness.length + 1 := by
  obtain ⟨m, _, _, r, next, _, _, _, _, _, _, ht⟩ := round_step_success e threshold bytes s t h
  simp [ht, advance]

theorem completed_round_count_exact (e : Engine) (threshold : Nat) (bytes : Bytes) (n : Nat) (s t : State)
    (h : runRounds e threshold bytes n s = some t) :
    t.finalRandomness.length = s.finalRandomness.length + n := by
  induction n generalizing s with
  | zero =>
      have ht : s = t := by simpa [runRounds] using h
      simp [← ht]
  | succ n ih =>
      unfold runRounds at h
      cases hs : roundStep e threshold bytes s with
      | none => simp [hs] at h
      | some next =>
          simp only [hs] at h
          have a := ih next h
          have b := round_step_adds_one_challenge e threshold bytes s next hs
          omega

theorem final_claim_requires_nonzero_and_full_equation (c : Context) (v : List Ext3) (s : State)
    (h : finalClaim c v s = true) :
    isZero (finalPolynomial v s.finalRandomness) = false ∧
    ∃ inv, inverse (finalPolynomial v s.finalRandomness) = some inv ∧
      normalize (subtractConstraints (c.prefixRandomness ++ s.finalRandomness)
        c.roundConstraints (emul s.sum inv)) =
      normalize (expectedLinearForm c.forms (c.prefixRandomness ++ s.finalRandomness)) := by
  dsimp only [finalClaim] at h
  split at h
  · simp at h
  · rename_i hz
    cases hi : inverse (finalPolynomial v s.finalRandomness) with
    | none => simp [hi] at h
    | some inv =>
        simp only [hi] at h
        exact ⟨by simpa using hz, inv, rfl, (normalized_equality_iff _ _).mp h⟩

theorem subtract_entry_preserves_canonical (r : List Ext3) (entry : RoundConstraint) (value : Ext3)
    (h : Canonical value) : Canonical (subtractEntry r entry value) :=
  WhirTerminal.closed_fold_canonical _ (fun _ _ => esub_canonical _ _) _ value h

theorem subtract_all_constraints_preserves_canonical (r : List Ext3) (entries : List RoundConstraint)
    (value : Ext3) (h : Canonical value) : Canonical (subtractConstraints r entries value) := by
  induction entries generalizing value with
  | nil => exact h
  | cons entry _ ih => exact ih _ (subtract_entry_preserves_canonical r entry value h)

theorem expected_linear_form_is_canonical (forms : List LinearForm) (r : List Ext3) :
    Canonical (expectedLinearForm forms r) :=
  WhirTerminal.closed_fold_canonical _ (fun _ _ => eadd_canonical _ _) _ zero zero_canonical

theorem final_claim_requires_exact_full_equation (c : Context) (v : List Ext3) (s : State)
    (h : finalClaim c v s = true) :
    ∃ inv, inverse (finalPolynomial v s.finalRandomness) = some inv ∧
      subtractConstraints (c.prefixRandomness ++ s.finalRandomness)
        c.roundConstraints (emul s.sum inv) =
      expectedLinearForm c.forms (c.prefixRandomness ++ s.finalRandomness) := by
  obtain ⟨_, inv, hi, he⟩ := final_claim_requires_nonzero_and_full_equation c v s h
  have hl := subtract_all_constraints_preserves_canonical
    (c.prefixRandomness ++ s.finalRandomness) c.roundConstraints (emul s.sum inv) (emul_canonical _ _)
  have hr := expected_linear_form_is_canonical c.forms (c.prefixRandomness ++ s.finalRandomness)
  exact ⟨inv, hi, by simpa only [normalize_fixed hl, normalize_fixed hr] using he⟩

theorem end_success_same_vector_and_all_checks (auth : WhirTerminal.Authenticate) (e : Engine) (c : Context)
    (bytes hints : Bytes) (v : List Ext3) (rows : List WhirTerminal.GroupRows)
    (h : verifyEnd auth e c bytes hints v rows = true) :
    contextShape c = true ∧ WhirTerminal.verifyFinalRows auth c.rowPlan v rows = true ∧
    ∃ result, runRounds e c.powThreshold bytes c.rowPlan.finalRounds (start c) = some result ∧
      finalClaim c v result = true ∧ exhausted c bytes hints result = true := by
  unfold verifyEnd at h
  split at h
  · simp at h
  · rename_i hc
    split at h
    · simp at h
    · rename_i hr
      cases hs : runRounds e c.powThreshold bytes c.rowPlan.finalRounds (start c) with
      | none => simp [hs] at h
      | some result =>
          simp only [hs, Bool.and_eq_true] at h
          exact ⟨by simpa using hc, by simpa using hr, result, rfl, h.1, h.2⟩

theorem end_success_preserves_every_authenticated_row_equation (auth : WhirTerminal.Authenticate)
    (e : Engine) (c : Context) (bytes hints : Bytes) (v : List Ext3) (rows : List WhirTerminal.GroupRows)
    (h : verifyEnd auth e c bytes hints v rows = true) (position index : Nat)
    (hi : (position, index) ∈ c.rowPlan.indices.enum) :
    WhirTerminal.polynomial v (WhirTerminal.domainPoint c.rowPlan index) =
      WhirTerminal.openedValue c.rowPlan.groups rows position :=
  WhirTerminal.successful_each_query_exact_equality auth c.rowPlan v rows
    (end_success_same_vector_and_all_checks auth e c bytes hints v rows h).2.1 position index hi

theorem end_success_has_nonzero_same_vector_fold_and_exact_eof (auth : WhirTerminal.Authenticate)
    (e : Engine) (c : Context) (bytes hints : Bytes) (v : List Ext3) (rows : List WhirTerminal.GroupRows)
    (h : verifyEnd auth e c bytes hints v rows = true) :
    ∃ result, runRounds e c.powThreshold bytes c.rowPlan.finalRounds (start c) = some result ∧
      result.finalRandomness.length = c.rowPlan.finalRounds ∧
      isZero (finalPolynomial v result.finalRandomness) = false ∧
      result.cursor.transcriptPos = bytes.length ∧ c.hintPos = hints.length := by
  obtain ⟨_, _, result, hs, hf, he⟩ := end_success_same_vector_and_all_checks auth e c bytes hints v rows h
  have hl := completed_round_count_exact e c.powThreshold bytes c.rowPlan.finalRounds (start c) result hs
  have hz := (final_claim_requires_nonzero_and_full_equation c v result hf).1
  simp only [exhausted, decide_eq_true_eq] at he
  exact ⟨result, hs, by simpa [start] using hl, hz, he.1, he.2⟩

theorem end_success_final_fold_is_singleton (auth : WhirTerminal.Authenticate)
    (e : Engine) (c : Context) (bytes hints : Bytes) (v : List Ext3) (rows : List WhirTerminal.GroupRows)
    (h : verifyEnd auth e c bytes hints v rows = true) :
    ∃ result, runRounds e c.powThreshold bytes c.rowPlan.finalRounds (start c) = some result ∧
      (foldLayers result.finalRandomness.reverse v).length = 1 := by
  have hrows := (end_success_same_vector_and_all_checks auth e c bytes hints v rows h).2.1
  have hv := (WhirTerminal.successful_final_size_exact auth c.rowPlan v rows hrows).1
  obtain ⟨result, hr, hl, _⟩ :=
    end_success_has_nonzero_same_vector_fold_and_exact_eof auth e c bytes hints v rows h
  exact ⟨result, hr, full_final_fold_has_one_value _ _ (by simpa [hl] using hv)⟩

theorem end_success_linear_forms_have_exact_dimension (auth : WhirTerminal.Authenticate)
    (e : Engine) (c : Context) (bytes hints : Bytes) (v : List Ext3) (rows : List WhirTerminal.GroupRows)
    (h : verifyEnd auth e c bytes hints v rows = true) :
    ∃ result, runRounds e c.powThreshold bytes c.rowPlan.finalRounds (start c) = some result ∧
      ∀ form ∈ c.forms, form.point.length = (c.prefixRandomness ++ result.finalRandomness).length := by
  have hc := (end_success_same_vector_and_all_checks auth e c bytes hints v rows h).1
  simp only [contextShape, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨result, hr, hl, _⟩ :=
    end_success_has_nonzero_same_vector_fold_and_exact_eof auth e c bytes hints v rows h
  refine ⟨result, hr, ?_⟩
  intro form hm
  rw [List.length_append, hl, ← hc.1.1.1]
  exact hc.1.2 form hm

theorem end_success_constraint_pair_shapes_exact (auth : WhirTerminal.Authenticate)
    (e : Engine) (c : Context) (bytes hints : Bytes) (v : List Ext3) (rows : List WhirTerminal.GroupRows)
    (h : verifyEnd auth e c bytes hints v rows = true) :
    ∀ entry ∈ c.roundConstraints,
      entry.coefficients.length = entry.points.length ∧ entry.numVariables ≤ c.totalVariables := by
  have hc := (end_success_same_vector_and_all_checks auth e c bytes hints v rows h).1
  simp only [contextShape, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  exact hc.2

theorem nonzero_check_rejects_zero_final_fold (c : Context) (v : List Ext3) (s : State)
    (h : isZero (finalPolynomial v s.finalRandomness) = true) : finalClaim c v s = false := by
  simp [finalClaim, h]

theorem eof_rejects_transcript_tail (c : Context) (bytes hints : Bytes) (s : State)
    (h : s.cursor.transcriptPos < bytes.length) : exhausted c bytes hints s = false := by
  simp [exhausted, show s.cursor.transcriptPos ≠ bytes.length by omega]

theorem eof_rejects_hint_tail (c : Context) (bytes hints : Bytes) (s : State)
    (h : c.hintPos < hints.length) : exhausted c bytes hints s = false := by
  simp [exhausted, show c.hintPos ≠ hints.length by omega]

theorem subtract_constraints_preserves_full_list_order (r : List Ext3) (a b : List RoundConstraint) (s : Ext3) :
    subtractConstraints r (a ++ b) s = subtractConstraints r b (subtractConstraints r a s) := by
  simp [subtractConstraints, List.foldl_append]

def testContext : Context :=
  { rowPlan := ⟨[⟨WhirTerminal.testRoot, [one]⟩], [0], 1, 2, 1, 1, 1⟩,
    prefixRandomness := [zero], priorSum := one, afterRows := ⟨0, ⟨Spongefish.zeroDigest, 0⟩⟩, hintPos := 0,
    totalVariables := 2, powThreshold := 0, roundConstraints := [], forms := [⟨one, [zero, zero]⟩] }

def testEngine : Engine :=
  { readMessage := fun _ cursor => some (⟨one, zero⟩, cursor),
    checkPow := fun _ _ cursor => some cursor,
    challenge := fun cursor => some (zero, cursor) }

set_option maxRecDepth 4096 in
/-- A nonempty final round and authenticated row pass this model's complete
    suffix. Observed decoding/authentication are placeholders, NOT a production
    proof fixture or an assertion that the preceding WHIR context exists. -/
theorem positive_suffix_with_one_final_round :
    verifyEnd (fun _ _ _ => true) testEngine testContext [] [] [one, zero] [[[one]]] = true := by decide

end Audit.Wire3.WhirFinal
