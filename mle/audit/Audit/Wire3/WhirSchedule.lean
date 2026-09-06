import Std

/-!
# Folding-schedule projection of WHIR parameter validation

This is ONLY the folding-schedule guards of
SpongefishWhirVerify._validateParameters (source at 4422b4c7): original and
initial variable counts, folding factor, initial/intermediate round counts and
interleaving sizes, declared round-list length, and final rounds/vector size.
checkRounds successively subtracts the accepted sumcheckRounds from remaining
variables; the returned remainder must equal finalSumcheckRounds.

The source also checks each domain/generator/coset and the evaluation points.
Those checks, outer grouped-schema checks, and ABI/config decoding are omitted.
Thus checkFoldingSchedule=true is NOT complete parameter-validation success.
This is a projection of existing source guards, not new proof-time guards, and
it is not yet connected to a model of the full _validateParameters call.

Schedule values MUST come from the stored VK/config caller boundary, not from
untrusted proof fields. Naturals replace uint256; 2^r expresses the source's
1<<r with the same r<256 guards. No EVM arithmetic/bytecode refinement, WHIR
transcript execution, field assumption, or cryptographic soundness is proved.
-/
namespace Audit.Wire3.WhirSchedule

structure Round where
  numVariables : Nat
  sumcheckRounds : Nat
  interleavingDepth : Nat
  deriving DecidableEq

structure Schedule where
  numVariables : Nat
  initialNumVariables : Nat
  foldingFactor : Nat
  initialSumcheckRounds : Nat
  initialInterleavingDepth : Nat
  numRounds : Nat
  rounds : List Round
  finalSumcheckRounds : Nat
  finalSize : Nat
  deriving DecidableEq

def initialChecks (s : Schedule) : Bool := decide (
  0 < s.numVariables ∧ s.numVariables < 256 ∧ s.initialNumVariables = s.numVariables ∧
  0 < s.foldingFactor ∧ 0 < s.initialSumcheckRounds ∧ s.initialSumcheckRounds ≤ s.numVariables ∧
  s.initialSumcheckRounds < 256 ∧ s.initialInterleavingDepth = 2 ^ s.initialSumcheckRounds ∧
  s.rounds.length = s.numRounds)

def roundChecks (foldingFactor remaining : Nat) (r : Round) : Bool := decide (
  r.numVariables = remaining ∧ r.sumcheckRounds = foldingFactor ∧ r.sumcheckRounds ≤ remaining ∧
  r.sumcheckRounds < 256 ∧ r.interleavingDepth = 2 ^ r.sumcheckRounds)

def checkRounds (foldingFactor : Nat) : List Round → Nat → Option Nat
  | [],remaining => some remaining
  | r :: rest,remaining =>
      if roundChecks foldingFactor remaining r then
        checkRounds foldingFactor rest (remaining - r.sumcheckRounds)
      else none

def checkFoldingSchedule (s : Schedule) : Bool :=
  if initialChecks s then
    match checkRounds s.foldingFactor s.rounds (s.numVariables - s.initialSumcheckRounds) with
    | none => false
    | some remaining => decide (
        remaining = s.finalSumcheckRounds ∧ s.finalSumcheckRounds < 256 ∧
        s.finalSize = 2 ^ s.finalSumcheckRounds)
  else false

def roundSum : List Round → Nat
  | [] => 0
  | r :: rest => r.sumcheckRounds + roundSum rest

theorem initial_checks_exact (s : Schedule) : initialChecks s = true ↔
    0 < s.numVariables ∧ s.numVariables < 256 ∧ s.initialNumVariables = s.numVariables ∧
    0 < s.foldingFactor ∧ 0 < s.initialSumcheckRounds ∧ s.initialSumcheckRounds ≤ s.numVariables ∧
    s.initialSumcheckRounds < 256 ∧ s.initialInterleavingDepth = 2 ^ s.initialSumcheckRounds ∧
    s.rounds.length = s.numRounds := by simp [initialChecks]

theorem round_checks_exact (foldingFactor remaining : Nat) (r : Round) :
    roundChecks foldingFactor remaining r = true ↔
      r.numVariables = remaining ∧ r.sumcheckRounds = foldingFactor ∧ r.sumcheckRounds ≤ remaining ∧
      r.sumcheckRounds < 256 ∧ r.interleavingDepth = 2 ^ r.sumcheckRounds := by simp [roundChecks]

theorem empty_rounds_return_remainder (foldingFactor remaining : Nat) :
    checkRounds foldingFactor [] remaining = some remaining := rfl

theorem cons_rounds_success_iff (foldingFactor remaining final : Nat) (r : Round) (rest : List Round) :
    checkRounds foldingFactor (r::rest) remaining = some final ↔
      roundChecks foldingFactor remaining r = true ∧
      checkRounds foldingFactor rest (remaining-r.sumcheckRounds) = some final := by
  cases hg : roundChecks foldingFactor remaining r <;> simp [checkRounds,hg]

theorem schedule_success_exact (s : Schedule) : checkFoldingSchedule s = true ↔
    initialChecks s = true ∧
      checkRounds s.foldingFactor s.rounds (s.numVariables-s.initialSumcheckRounds) = some s.finalSumcheckRounds ∧
      s.finalSumcheckRounds < 256 ∧ s.finalSize = 2 ^ s.finalSumcheckRounds := by
  cases hi : initialChecks s with
  | false => simp [checkFoldingSchedule,hi]
  | true =>
      cases hr : checkRounds s.foldingFactor s.rounds (s.numVariables-s.initialSumcheckRounds) with
      | none => simp [checkFoldingSchedule,hi,hr]
      | some remaining =>
          simp only [checkFoldingSchedule,hi,↓reduceIte,hr,decide_eq_true_eq,Option.some.injEq,true_and]

theorem checked_round_sum_reaches_final (foldingFactor remaining final : Nat) (rounds : List Round)
    (h : checkRounds foldingFactor rounds remaining = some final) : remaining = roundSum rounds + final := by
  induction rounds generalizing remaining with
  | nil => cases h; simp [roundSum]
  | cons r rest ih =>
      obtain ⟨hg,ht⟩ := (cons_rounds_success_iff foldingFactor remaining final r rest).mp h
      have hp := (round_checks_exact foldingFactor remaining r).mp hg
      have hs := ih (remaining-r.sumcheckRounds) ht
      simp only [roundSum]
      omega

theorem checked_rounds_never_increase_remaining (foldingFactor remaining final : Nat) (rounds : List Round)
    (h : checkRounds foldingFactor rounds remaining = some final) : final ≤ remaining := by
  have hs := checked_round_sum_reaches_final foldingFactor remaining final rounds h
  omega

theorem checked_rounds_sum_equals_factor_times_count (foldingFactor remaining final : Nat) (rounds : List Round)
    (h : checkRounds foldingFactor rounds remaining = some final) : roundSum rounds = foldingFactor * rounds.length := by
  induction rounds generalizing remaining with
  | nil => simp [roundSum]
  | cons r rest ih =>
      obtain ⟨hg,ht⟩ := (cons_rounds_success_iff foldingFactor remaining final r rest).mp h
      have hp := (round_checks_exact foldingFactor remaining r).mp hg
      simp only [roundSum,List.length_cons,hp.2.1,ih _ ht,Nat.mul_succ]
      omega

theorem check_rounds_append (foldingFactor remaining : Nat) (first rest : List Round) :
    checkRounds foldingFactor (first++rest) remaining =
      (checkRounds foldingFactor first remaining).bind (checkRounds foldingFactor rest) := by
  induction first generalizing remaining with
  | nil => rfl
  | cons r first ih =>
      cases hg : roundChecks foldingFactor remaining r <;> simp [checkRounds,hg,ih]

/-- Every individual round is annotated with exactly the current round's count
plus all later intermediate counts and the final count. -/
theorem checked_round_at_position (foldingFactor remaining final position : Nat) (rounds : List Round) (r : Round)
    (h : checkRounds foldingFactor rounds remaining = some final) (hi : rounds.get? position = some r) :
    r.numVariables = r.sumcheckRounds + roundSum (rounds.drop (position+1)) + final ∧
      r.sumcheckRounds = foldingFactor ∧ r.sumcheckRounds ≤ r.numVariables ∧
      r.sumcheckRounds < 256 ∧ r.interleavingDepth = 2 ^ r.sumcheckRounds := by
  induction rounds generalizing remaining position with
  | nil => simp at hi
  | cons head tail ih =>
      obtain ⟨hg,ht⟩ := (cons_rounds_success_iff foldingFactor remaining final head tail).mp h
      have hp := (round_checks_exact foldingFactor remaining head).mp hg
      cases position with
      | zero =>
          cases hi
          have hs := checked_round_sum_reaches_final foldingFactor remaining final (r::tail) h
          refine ⟨?_,hp.2.1,?_,hp.2.2.2⟩
          · simpa [roundSum,hp.1,Nat.add_assoc] using hs
          · simpa [hp.1] using hp.2.2.1
      | succ position => exact ih (remaining-head.sumcheckRounds) position ht hi

theorem checked_round_prefix_reaches_annotated_remaining (foldingFactor remaining final : Nat)
    (first rest : List Round) (r : Round)
    (h : checkRounds foldingFactor (first++r::rest) remaining = some final) :
    checkRounds foldingFactor first remaining = some r.numVariables ∧
      checkRounds foldingFactor rest (r.numVariables-r.sumcheckRounds) = some final := by
  rw [check_rounds_append] at h
  cases hp : checkRounds foldingFactor first remaining with
  | none => simp [hp] at h
  | some middle =>
      simp only [hp,Option.bind] at h
      obtain ⟨hg,ht⟩ := (cons_rounds_success_iff foldingFactor middle final r rest).mp h
      have he := ((round_checks_exact foldingFactor middle r).mp hg).1
      exact ⟨by rw [he],by simpa [he] using ht⟩

theorem checked_round_member_guards (foldingFactor remaining final : Nat) (rounds : List Round) (r : Round)
    (h : checkRounds foldingFactor rounds remaining = some final) (hm : r ∈ rounds) :
    r.sumcheckRounds = foldingFactor ∧ r.sumcheckRounds ≤ r.numVariables ∧
      r.sumcheckRounds < 256 ∧ r.interleavingDepth = 2 ^ r.sumcheckRounds ∧ r.numVariables ≤ remaining := by
  induction rounds generalizing remaining with
  | nil => simp at hm
  | cons head tail ih =>
      obtain ⟨hg,ht⟩ := (cons_rounds_success_iff foldingFactor remaining final head tail).mp h
      have hp := (round_checks_exact foldingFactor remaining head).mp hg
      rcases List.mem_cons.mp hm with he | hm
      · subst r
        exact ⟨hp.2.1,by simpa [hp.1] using hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2,by omega⟩
      · have hs := ih (remaining-head.sumcheckRounds) ht hm
        exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,Nat.le_trans hs.2.2.2.2 (Nat.sub_le _ _)⟩

theorem accepted_initial_subtraction_has_no_underflow (s : Schedule) (h : checkFoldingSchedule s = true) :
    s.initialSumcheckRounds ≤ s.numVariables ∧
      s.numVariables-s.initialSumcheckRounds+s.initialSumcheckRounds = s.numVariables := by
  have hp := (initial_checks_exact s).mp ((schedule_success_exact s).mp h).1
  exact ⟨hp.2.2.2.2.2.1,Nat.sub_add_cancel hp.2.2.2.2.2.1⟩

theorem accepted_schedule_partitions_original_variables (s : Schedule) (h : checkFoldingSchedule s = true) :
    s.numVariables = s.initialSumcheckRounds + roundSum s.rounds + s.finalSumcheckRounds := by
  have he := (schedule_success_exact s).mp h
  have hi := (accepted_initial_subtraction_has_no_underflow s h).1
  have hs := checked_round_sum_reaches_final s.foldingFactor _ s.finalSumcheckRounds s.rounds he.2.1
  omega

theorem accepted_schedule_factor_partition (s : Schedule) (h : checkFoldingSchedule s = true) :
    s.numVariables = s.initialSumcheckRounds + s.foldingFactor * s.numRounds + s.finalSumcheckRounds := by
  have he := (schedule_success_exact s).mp h
  have hi := (initial_checks_exact s).mp he.1
  have hs := checked_rounds_sum_equals_factor_times_count s.foldingFactor _ s.finalSumcheckRounds s.rounds he.2.1
  rw [accepted_schedule_partitions_original_variables s h,hs,hi.2.2.2.2.2.2.2.2]

theorem accepted_round_annotations_equal_remaining_suffix (s : Schedule) (position : Nat) (r : Round)
    (h : checkFoldingSchedule s = true) (hi : s.rounds.get? position = some r) :
    r.numVariables = r.sumcheckRounds + roundSum (s.rounds.drop (position+1)) + s.finalSumcheckRounds :=
  (checked_round_at_position s.foldingFactor _ s.finalSumcheckRounds position s.rounds r
    ((schedule_success_exact s).mp h).2.1 hi).1

theorem accepted_prefix_executes_to_round_annotation (s : Schedule) (first rest : List Round) (r : Round)
    (h : checkFoldingSchedule s = true) (hs : s.rounds = first++r::rest) :
    checkRounds s.foldingFactor first (s.numVariables-s.initialSumcheckRounds) = some r.numVariables ∧
      checkRounds s.foldingFactor rest (r.numVariables-r.sumcheckRounds) = some s.finalSumcheckRounds := by
  have he := ((schedule_success_exact s).mp h).2.1
  rw [hs] at he
  exact checked_round_prefix_reaches_annotated_remaining s.foldingFactor _ s.finalSumcheckRounds first rest r he

theorem accepted_final_remainder_exact (s : Schedule) (h : checkFoldingSchedule s = true) :
    roundSum s.rounds ≤ s.numVariables-s.initialSumcheckRounds ∧
      s.numVariables-s.initialSumcheckRounds-roundSum s.rounds = s.finalSumcheckRounds := by
  have hs := checked_round_sum_reaches_final s.foldingFactor _ s.finalSumcheckRounds s.rounds
    ((schedule_success_exact s).mp h).2.1
  omega

theorem accepted_round_subtraction_has_no_underflow (s : Schedule) (r : Round)
    (h : checkFoldingSchedule s = true) (hm : r ∈ s.rounds) :
    r.sumcheckRounds ≤ r.numVariables ∧ r.numVariables-r.sumcheckRounds+r.sumcheckRounds = r.numVariables := by
  have hr := checked_round_member_guards s.foldingFactor _ s.finalSumcheckRounds s.rounds r
    ((schedule_success_exact s).mp h).2.1 hm
  exact ⟨hr.2.1,Nat.sub_add_cancel hr.2.1⟩

theorem accepted_rounds_are_positive_and_bounded (s : Schedule) (r : Round)
    (h : checkFoldingSchedule s = true) (hm : r ∈ s.rounds) :
    0 < r.sumcheckRounds ∧ r.sumcheckRounds < 256 ∧ r.numVariables < 256 ∧
      r.interleavingDepth = 2 ^ r.sumcheckRounds := by
  have he := (schedule_success_exact s).mp h
  have hi := (initial_checks_exact s).mp he.1
  have hr := checked_round_member_guards s.foldingFactor _ s.finalSumcheckRounds s.rounds r he.2.1 hm
  have hn := Nat.le_trans hr.2.2.2.2 (Nat.sub_le s.numVariables s.initialSumcheckRounds)
  exact ⟨by rw [hr.1]; exact hi.2.2.2.1,hr.2.2.1,Nat.lt_of_le_of_lt hn hi.2.1,hr.2.2.2.1⟩

theorem accepted_final_size_exact (s : Schedule) (h : checkFoldingSchedule s = true) :
    s.finalSumcheckRounds < 256 ∧ s.finalSize = 2 ^ s.finalSumcheckRounds :=
  ((schedule_success_exact s).mp h).2.2

theorem accepted_initial_interleaving_exact (s : Schedule) (h : checkFoldingSchedule s = true) :
    0 < s.initialSumcheckRounds ∧ s.initialSumcheckRounds < 256 ∧
      s.initialInterleavingDepth = 2 ^ s.initialSumcheckRounds := by
  have hi := (initial_checks_exact s).mp ((schedule_success_exact s).mp h).1
  exact ⟨hi.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2.1⟩

theorem accepted_declared_round_count_exact (s : Schedule) (h : checkFoldingSchedule s = true) :
    s.rounds.length = s.numRounds :=
  ((initial_checks_exact s).mp ((schedule_success_exact s).mp h).1).2.2.2.2.2.2.2.2

theorem accepted_original_counts_match (s : Schedule) (h : checkFoldingSchedule s = true) :
    0 < s.numVariables ∧ s.numVariables < 256 ∧ s.initialNumVariables = s.numVariables := by
  have hi := (initial_checks_exact s).mp ((schedule_success_exact s).mp h).1
  exact ⟨hi.1,hi.2.1,hi.2.2.1⟩

/-- Mathematical shift correspondence only; no bitvector/EVM semantics are
silently assumed. The exponent guard places the value below 2^256. -/
theorem guarded_power_is_one_shift_and_fits (rounds : Nat) (h : rounds < 256) :
    2 ^ rounds = (1 <<< rounds) ∧ 0 < 2 ^ rounds ∧ 2 ^ rounds < 2 ^ 256 :=
  ⟨(Nat.one_shiftLeft rounds).symm,Nat.pow_pos (by decide),Nat.pow_lt_pow_of_lt (by decide) h⟩

theorem accepted_final_size_positive_and_fits (s : Schedule) (h : checkFoldingSchedule s = true) :
    0 < s.finalSize ∧ s.finalSize < 2 ^ 256 := by
  have hf := accepted_final_size_exact s h
  rw [hf.2]
  exact (guarded_power_is_one_shift_and_fits s.finalSumcheckRounds hf.1).2

theorem accepted_round_interleaving_positive_and_fits (s : Schedule) (r : Round)
    (h : checkFoldingSchedule s = true) (hm : r ∈ s.rounds) :
    0 < r.interleavingDepth ∧ r.interleavingDepth < 2 ^ 256 := by
  have hr := accepted_rounds_are_positive_and_bounded s r h hm
  rw [hr.2.2.2]
  exact (guarded_power_is_one_shift_and_fits r.sumcheckRounds hr.2.1).2

def exampleSchedule : Schedule :=
  ⟨16,16,4,4,16,2,[⟨12,4,16⟩,⟨8,4,16⟩],4,16⟩

/-- Two ordinary intermediate rounds: 16 → 12 → 8 → 4 final variables. -/
theorem nonempty_round_schedule_example : checkFoldingSchedule exampleSchedule = true := by decide

theorem normal_round_sequence_example :
    checkRounds exampleSchedule.foldingFactor exampleSchedule.rounds 12 = some 4 := by decide

theorem normal_second_round_annotation_example :
    exampleSchedule.rounds.get? 1 = some ⟨8,4,16⟩ ∧ 8 = 4 + 0 + exampleSchedule.finalSumcheckRounds := by decide

theorem zero_final_rounds_singleton_size_example :
    checkFoldingSchedule ⟨12,12,4,4,16,2,[⟨8,4,16⟩,⟨4,4,16⟩],0,1⟩ = true := by decide

/-- Source does not bound an unused foldingFactor when there are no
intermediate rounds; the projection must not invent such a guard. -/
theorem empty_rounds_do_not_add_unused_factor_bound :
    checkFoldingSchedule ⟨4,4,1000,4,16,0,[],0,1⟩ = true := by decide

end Audit.Wire3.WhirSchedule
