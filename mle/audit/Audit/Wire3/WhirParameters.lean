import Audit.Wire3.WhirSchedule
import Audit.Wire3.WhirInitial

/-!
# Executable typed WHIR parameter checks, including grouped entry conditions

Manual model of SpongefishWhirVerify.sol:112–239 at becfe98e. The core order is
initial folding guards, initial domain, each round's folding guards then domain,
final remainder/size, first point length/canonical coordinates, then the exact
single- or multi-point branch. `checkBound` separately models the grouped entry
checks; `checkDeployment` checks only positive form count before the core.

Every source scalar is retained, with Domain grouping its five source fields.
Raw points use Arithmetic.Ext3, not a pre-assumed canonical subtype. Successful
coordinate checks construct canonical values without reducing or dropping raw
limbs. The returned forms are a projection of successful validation, not extra
source output or mutation. Source sample counts and PoW thresholds are retained
but the source does not validate them in this slice, so this model does not add
such checks. Generator nonzero/canonical is NOT multiplicative exact order.

Nat models already ABI-decoded unsigned values; uint64/uint256 representation,
overflow, gas, allocation, ABI/config digest decoding, exception payloads, and
instruction/compiler refinement remain unproved. The unreachable public-entry
formCount=0 subtraction branch explicitly fails instead of accepting Nat's
saturating subtraction. It is not a new accepted-input guard. All return failures
here concern parameter admission, not transcript fraud. No bytes are consumed.

No generic success establishes the production 3-commitment/1-vector profile,
caller provenance, domain order, transcript/WHIR/PCS security or full refinement.
-/
namespace Audit.Wire3.WhirParameters
open Spongefish (Bytes Digest Ext3)

instance canonicalDecidable (raw : Arithmetic.Ext3) : Decidable (Arithmetic.Canonical raw) :=
  inferInstanceAs (Decidable (raw.c0 < Arithmetic.modulus ∧ raw.c1 < Arithmetic.modulus ∧
    raw.c2 < Arithmetic.modulus))

structure Domain where
  codewordLength : Nat
  merkleDepth : Nat
  cosetSize : Nat
  numCosets : Nat
  domainGenerator : Nat
  deriving DecidableEq, Repr

structure Round where
  domain : Domain
  inDomainSamples : Nat
  outDomainSamples : Nat
  sumcheckRounds : Nat
  interleavingDepth : Nat
  numVariables : Nat
  powThreshold : Nat
  sumcheckPowThreshold : Nat
  deriving DecidableEq, Repr

def Round.folding (r : Round) : WhirSchedule.Round :=
  ⟨r.numVariables,r.sumcheckRounds,r.interleavingDepth⟩

structure Params where
  numVariables : Nat
  foldingFactor : Nat
  numVectors : Nat
  numCommitments : Nat
  outDomainSamples : Nat
  inDomainSamples : Nat
  initialSumcheckRounds : Nat
  numRounds : Nat
  finalSumcheckRounds : Nat
  finalSize : Nat
  initialDomain : Domain
  initialInterleavingDepth : Nat
  initialNumVariables : Nat
  initialSumcheckPowThreshold : Nat
  finalPowThreshold : Nat
  finalSumcheckPowThreshold : Nat
  evaluationPoint : List Arithmetic.Ext3
  evaluationPoint2 : List Arithmetic.Ext3
  additionalEvaluationPoints : List (List Arithmetic.Ext3)
  rounds : List Round

def schedule (p : Params) : WhirSchedule.Schedule :=
  ⟨p.numVariables,p.initialNumVariables,p.foldingFactor,p.initialSumcheckRounds,
    p.initialInterleavingDepth,p.numRounds,p.rounds.map Round.folding,
    p.finalSumcheckRounds,p.finalSize⟩

def totalVectors (p : Params) : Nat := p.numCommitments*p.numVectors

def checkDomain (d : Domain) : Bool := decide (
  0 < d.codewordLength ∧ d.codewordLength &&& (d.codewordLength-1) = 0 ∧
  d.merkleDepth < 256 ∧ d.codewordLength = 2^d.merkleDepth ∧
  0 < d.cosetSize ∧ 0 < d.numCosets ∧
  d.codewordLength % d.cosetSize = 0 ∧ d.codewordLength / d.cosetSize = d.numCosets ∧
  0 < d.domainGenerator ∧ d.domainGenerator < Arithmetic.modulus)

def checkRounds (foldingFactor : Nat) : List Round → Nat → Option Nat
  | [],remaining => some remaining
  | r::rest,remaining =>
    if WhirSchedule.roundChecks foldingFactor remaining r.folding then
      if checkDomain r.domain then checkRounds foldingFactor rest (remaining-r.sumcheckRounds)
      else none
    else none

def checkCoordinate (raw : Arithmetic.Ext3) : Option Ext3 :=
  if h : Arithmetic.Canonical raw then some ⟨raw,h⟩ else none

def checkPoint : List Arithmetic.Ext3 → Option (List Ext3)
  | [] => some []
  | x::xs => do
    let y ← checkCoordinate x
    let ys ← checkPoint xs
    pure (y::ys)

def checkAdditional (numVariables : Nat) : List (List Arithmetic.Ext3) → Option (List (List Ext3))
  | [] => some []
  | point::points =>
    if point.length = numVariables then do
      let checked ← checkPoint point
      let rest ← checkAdditional numVariables points
      pure (checked::rest)
    else none

def rawForms (p : Params) (numForms : Nat) : List (List Arithmetic.Ext3) :=
  if numForms = 1 then [p.evaluationPoint]
  else p.evaluationPoint::p.evaluationPoint2::p.additionalEvaluationPoints

def checkForms (p : Params) (numForms : Nat) : Option (List (List Ext3)) :=
  if p.evaluationPoint.length = p.numVariables then do
    let first ← checkPoint p.evaluationPoint
    if numForms = 1 then
      if p.evaluationPoint2.length = 0 ∧ p.additionalEvaluationPoints.length = 0 then
        some [first]
      else none
    else
      if p.evaluationPoint2.length = p.numVariables then
        -- Source checked subtraction numForms-2; not Nat saturation.
        if 2 ≤ numForms ∧ p.additionalEvaluationPoints.length = numForms-2 then do
          let second ← checkPoint p.evaluationPoint2
          let additional ← checkAdditional p.numVariables p.additionalEvaluationPoints
          pure (first::second::additional)
        else none
      else none
  else none

def checkCore (p : Params) (numForms : Nat) : Option (List (List Ext3)) :=
  if WhirSchedule.initialChecks (schedule p) then
    if checkDomain p.initialDomain then do
      let remaining ← checkRounds p.foldingFactor p.rounds (p.numVariables-p.initialSumcheckRounds)
      if remaining = p.finalSumcheckRounds ∧ p.finalSumcheckRounds < 256 ∧
          p.finalSize = 2^p.finalSumcheckRounds then checkForms p numForms else none
    else none
  else none

def checkBound (p : Params) (rootCount evaluationCount maskLength : Nat) : Option (List (List Ext3)) :=
  if 0 < p.numCommitments ∧ 0 < p.numVectors then
    if maskLength = (evaluationCount+7)/8 then
      if rootCount = p.numCommitments then
        if 0 < evaluationCount ∧ evaluationCount % totalVectors p = 0 then
          checkCore p (evaluationCount / totalVectors p)
        else none
      else none
    else none
  else none

def checkDeployment (p : Params) (numForms : Nat) : Option (List (List Ext3)) :=
  if 0 < numForms then checkCore p numForms else none

def initialParams (p : Params) (forms : List (List Ext3)) : WhirInitial.Params :=
  ⟨p.numCommitments,p.numVectors,p.outDomainSamples,p.initialNumVariables,forms⟩

theorem domain_success_exact (d : Domain) : checkDomain d = true ↔
    0 < d.codewordLength ∧ d.codewordLength &&& (d.codewordLength-1) = 0 ∧
    d.merkleDepth < 256 ∧ d.codewordLength = 2^d.merkleDepth ∧
    0 < d.cosetSize ∧ 0 < d.numCosets ∧
    d.codewordLength % d.cosetSize = 0 ∧ d.codewordLength / d.cosetSize = d.numCosets ∧
    0 < d.domainGenerator ∧ d.domainGenerator < Arithmetic.modulus := by simp [checkDomain]

theorem domain_success_partition_and_generator (d : Domain) (h : checkDomain d = true) :
    d.codewordLength = d.cosetSize*d.numCosets ∧ 0 < d.domainGenerator ∧
      d.domainGenerator < Arithmetic.modulus := by
  have hd := (domain_success_exact d).mp h
  have he := Nat.mod_add_div d.codewordLength d.cosetSize
  rw [hd.2.2.2.2.2.2.1,hd.2.2.2.2.2.2.2.1,Nat.zero_add] at he
  exact ⟨he.symm,hd.2.2.2.2.2.2.2.2⟩

theorem rounds_success_exact (factor remaining final : Nat) (rounds : List Round) :
    checkRounds factor rounds remaining = some final ↔
      WhirSchedule.checkRounds factor (rounds.map Round.folding) remaining = some final ∧
      ∀ r ∈ rounds, checkDomain r.domain = true := by
  induction rounds generalizing remaining with
  | nil => simp [checkRounds,WhirSchedule.checkRounds]
  | cons r rest ih =>
    cases hf : WhirSchedule.roundChecks factor remaining r.folding <;>
      cases hd : checkDomain r.domain <;>
      simp [checkRounds,WhirSchedule.checkRounds,hf,hd,ih]
    simp [Round.folding]

theorem coordinate_success_keeps_raw (raw : Arithmetic.Ext3) (value : Ext3)
    (h : checkCoordinate raw = some value) : value.val = raw := by
  unfold checkCoordinate at h
  split at h
  · cases h; rfl
  · contradiction

theorem coordinate_success_is_canonical (raw : Arithmetic.Ext3) (value : Ext3)
    (h : checkCoordinate raw = some value) : Arithmetic.Canonical raw := by
  rw [←coordinate_success_keeps_raw raw value h]
  exact value.property

theorem point_success_keeps_all_raw (raw : List Arithmetic.Ext3) (checked : List Ext3)
    (h : checkPoint raw = some checked) : checked.map Subtype.val = raw := by
  induction raw generalizing checked with
  | nil => cases h; rfl
  | cons x xs ih =>
    cases hc : checkCoordinate x with
    | none => simp [checkPoint,hc] at h
    | some y =>
      cases ht : checkPoint xs with
      | none => simp [checkPoint,hc,ht] at h
      | some ys =>
        simp only [checkPoint,hc,ht,bind,Option.bind,pure,Option.some.injEq] at h
        subst checked
        simp [coordinate_success_keeps_raw x y hc,ih ys ht]

theorem point_success_length (raw : List Arithmetic.Ext3) (checked : List Ext3)
    (h : checkPoint raw = some checked) : checked.length = raw.length := by
  have he := congrArg List.length (point_success_keeps_all_raw raw checked h)
  simpa using he

theorem point_success_every_coordinate_canonical (raw : List Arithmetic.Ext3) (checked : List Ext3)
    (h : checkPoint raw = some checked) : ∀ coordinate ∈ raw, Arithmetic.Canonical coordinate := by
  rw [←point_success_keeps_all_raw raw checked h]
  intro coordinate hc
  obtain ⟨value,_,rfl⟩ := List.mem_map.mp hc
  exact value.property

theorem additional_success_exact (numVariables : Nat) (raw : List (List Arithmetic.Ext3))
    (checked : List (List Ext3)) (h : checkAdditional numVariables raw = some checked) :
    checked.map (List.map Subtype.val) = raw ∧ checked.length = raw.length ∧
      ∀ point ∈ checked, point.length = numVariables := by
  induction raw generalizing checked with
  | nil => cases h; simp
  | cons point points ih =>
    unfold checkAdditional at h
    split at h
    · rename_i hl
      cases hp : checkPoint point with
      | none => simp [hp] at h
      | some first =>
        cases ht : checkAdditional numVariables points with
        | none => simp [hp,ht] at h
        | some rest =>
          simp only [hp,ht,bind,Option.bind,pure,Option.some.injEq] at h
          subst checked
          have hh := ih rest ht
          exact ⟨by simp [point_success_keeps_all_raw point first hp,hh.1],by simp [hh.2.1],by
            intro selected hs
            rcases List.mem_cons.mp hs with rfl | hs
            · exact (point_success_length point _ hp).trans hl
            · exact hh.2.2 selected hs⟩
    · contradiction

theorem forms_success_exact (p : Params) (numForms : Nat) (forms : List (List Ext3))
    (h : checkForms p numForms = some forms) :
    0 < numForms ∧ forms.length = numForms ∧ forms.map (List.map Subtype.val) = rawForms p numForms ∧
      ∀ point ∈ forms, point.length = p.numVariables := by
  unfold checkForms at h
  split at h
  · rename_i hfirst
    cases hp : checkPoint p.evaluationPoint with
    | none => simp [hp] at h
    | some first =>
      simp only [hp,bind,Option.bind] at h
      split at h
      · rename_i hone
        split at h
        · cases h
          exact ⟨by omega,by simp [hone],by simp [rawForms,hone,point_success_keeps_all_raw _ _ hp],by
            intro point hm
            simp only [List.mem_singleton] at hm
            subst point
            exact (point_success_length _ _ hp).trans hfirst⟩
        · contradiction
      · rename_i hnotone
        split at h
        · rename_i hsecond
          split at h
          · rename_i hcount
            cases hs : checkPoint p.evaluationPoint2 with
            | none => simp [hs] at h
            | some second =>
              cases ha : checkAdditional p.numVariables p.additionalEvaluationPoints with
              | none => simp [hs,ha] at h
              | some additional =>
                simp only [hs,ha,bind,Option.bind,pure,Option.some.injEq] at h
                subst forms
                have hh := additional_success_exact _ _ _ ha
                exact ⟨by omega,by simp only [List.length_cons]; omega,by
                  simp [rawForms,hnotone,point_success_keeps_all_raw _ _ hp,
                    point_success_keeps_all_raw _ _ hs,hh.1],by
                  intro point hm
                  rcases List.mem_cons.mp hm with rfl | hm
                  · exact (point_success_length _ _ hp).trans hfirst
                  · rcases List.mem_cons.mp hm with rfl | hm
                    · exact (point_success_length _ _ hs).trans hsecond
                    · exact hh.2.2 point hm⟩
          · contradiction
        · contradiction
  · contradiction

theorem forms_single_branch_has_no_ignored_points (p : Params) (forms : List (List Ext3))
    (h : checkForms p 1 = some forms) :
    p.evaluationPoint2 = [] ∧ p.additionalEvaluationPoints = [] := by
  unfold checkForms at h
  split at h
  · cases hp : checkPoint p.evaluationPoint with
    | none => simp [hp] at h
    | some first =>
      simp only [hp,bind,Option.bind,↓reduceIte] at h
      split at h
      · rename_i he
        exact ⟨List.eq_nil_of_length_eq_zero he.1,List.eq_nil_of_length_eq_zero he.2⟩
      · contradiction
  · contradiction

theorem core_success_sequence (p : Params) (numForms : Nat) (forms : List (List Ext3))
    (h : checkCore p numForms = some forms) :
    WhirSchedule.initialChecks (schedule p) = true ∧ checkDomain p.initialDomain = true ∧
      checkRounds p.foldingFactor p.rounds (p.numVariables-p.initialSumcheckRounds) = some p.finalSumcheckRounds ∧
      p.finalSumcheckRounds < 256 ∧ p.finalSize = 2^p.finalSumcheckRounds ∧
      checkForms p numForms = some forms := by
  unfold checkCore at h
  split at h
  · rename_i hi
    split at h
    · rename_i hd
      cases hr : checkRounds p.foldingFactor p.rounds (p.numVariables-p.initialSumcheckRounds) with
      | none => simp [hr] at h
      | some remaining =>
        simp only [hr,bind,Option.bind] at h
        split at h
        · rename_i hf
          rcases hf with ⟨rfl,hlt,hsize⟩
          exact ⟨hi,hd,rfl,hlt,hsize,h⟩
        · contradiction
    · contradiction
  · contradiction

theorem core_success_implies_existing_schedule (p : Params) (numForms : Nat) (forms : List (List Ext3))
    (h : checkCore p numForms = some forms) : WhirSchedule.checkFoldingSchedule (schedule p) = true := by
  have hc := core_success_sequence p numForms forms h
  have hr := (rounds_success_exact p.foldingFactor _ p.finalSumcheckRounds p.rounds).mp hc.2.2.1
  exact (WhirSchedule.schedule_success_exact (schedule p)).mpr ⟨hc.1,hr.1,hc.2.2.2.1,hc.2.2.2.2.1⟩

theorem core_success_checks_all_domains (p : Params) (numForms : Nat) (forms : List (List Ext3))
    (h : checkCore p numForms = some forms) :
    checkDomain p.initialDomain = true ∧ ∀ r ∈ p.rounds, checkDomain r.domain = true := by
  have hc := core_success_sequence p numForms forms h
  exact ⟨hc.2.1,((rounds_success_exact p.foldingFactor _ p.finalSumcheckRounds p.rounds).mp hc.2.2.1).2⟩

theorem core_success_forms_and_raw_coordinates (p : Params) (numForms : Nat) (forms : List (List Ext3))
    (h : checkCore p numForms = some forms) :
    0 < numForms ∧ forms.length = numForms ∧
      forms.map (List.map Subtype.val) = rawForms p numForms ∧
      (∀ point ∈ rawForms p numForms, point.length = p.numVariables ∧
        ∀ coordinate ∈ point, Arithmetic.Canonical coordinate) := by
  have hf := forms_success_exact p numForms forms (core_success_sequence p numForms forms h).2.2.2.2.2
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_⟩
  rw [←hf.2.2.1]
  intro point hp
  obtain ⟨typed,ht,rfl⟩ := List.mem_map.mp hp
  refine ⟨by simpa using hf.2.2.2 typed ht,?_⟩
  intro coordinate hc
  obtain ⟨value,_,rfl⟩ := List.mem_map.mp hc
  exact value.property

theorem bound_success_entry_guards (p : Params) (rootCount evaluationCount maskLength : Nat)
    (forms : List (List Ext3)) (h : checkBound p rootCount evaluationCount maskLength = some forms) :
    0 < p.numCommitments ∧ 0 < p.numVectors ∧ maskLength = (evaluationCount+7)/8 ∧
      rootCount = p.numCommitments ∧ 0 < evaluationCount ∧ evaluationCount % totalVectors p = 0 ∧
      checkCore p (evaluationCount/totalVectors p) = some forms := by
  unfold checkBound at h
  split at h
  · rename_i hv
    split at h
    · rename_i hm
      split at h
      · rename_i hr
        split at h
        · rename_i he
          exact ⟨hv.1,hv.2,hm,hr,he.1,he.2,h⟩
        · contradiction
      · contradiction
    · contradiction
  · contradiction

theorem bound_success_exact_evaluation_count (p : Params) (rootCount evaluationCount maskLength : Nat)
    (forms : List (List Ext3)) (h : checkBound p rootCount evaluationCount maskLength = some forms) :
    0 < forms.length ∧ evaluationCount = forms.length * totalVectors p := by
  have hb := bound_success_entry_guards p rootCount evaluationCount maskLength forms h
  have hf := forms_success_exact p _ forms
    (core_success_sequence p _ forms hb.2.2.2.2.2.2).2.2.2.2.2
  have he := Nat.mod_add_div evaluationCount (totalVectors p)
  rw [hb.2.2.2.2.2.1,Nat.zero_add] at he
  exact ⟨by omega,by rw [hf.2.1,Nat.mul_comm]; exact he.symm⟩

/-- `expected` is already canonical in this typed caller interface. checkBound
checks its LENGTH only; this validator does not prove expected-evaluation
canonicality. The raw-to-canonical checks above concern CONFIGURATION points. -/
theorem bound_success_initial_params_validated (p : Params) (roots : List Digest) (expected : List Ext3)
    (mask : Bytes) (forms : List (List Ext3))
    (h : checkBound p roots.length expected.length mask.length = some forms) :
    WhirInitial.validatedParams (initialParams p forms) roots expected mask := by
  have hb := bound_success_entry_guards p roots.length expected.length mask.length forms h
  have hs := WhirSchedule.accepted_original_counts_match (schedule p)
    (core_success_implies_existing_schedule p _ forms hb.2.2.2.2.2.2)
  have hf := forms_success_exact p _ forms
    (core_success_sequence p _ forms hb.2.2.2.2.2.2).2.2.2.2.2
  have he := bound_success_exact_evaluation_count p roots.length expected.length mask.length forms h
  change 0 < p.numCommitments ∧ 0 < p.numVectors ∧ roots.length = p.numCommitments ∧
    0 < p.initialNumVariables ∧ p.initialNumVariables < 256 ∧ 0 < forms.length ∧
    (∀ form ∈ forms, form.length = p.initialNumVariables) ∧
    expected.length = forms.length*(p.numCommitments*p.numVectors) ∧ mask.length = (expected.length+7)/8
  simp only [schedule] at hs
  exact ⟨hb.1,hb.2.1,hb.2.2.2.1,by omega,by omega,he.1,by
    intro form hm
    exact (hf.2.2.2 form hm).trans hs.2.2.symm,he.2,hb.2.2.1⟩

theorem deployment_success_exact (p : Params) (numForms : Nat) (forms : List (List Ext3)) :
    checkDeployment p numForms = some forms ↔ 0 < numForms ∧ checkCore p numForms = some forms := by
  unfold checkDeployment
  split <;> simp_all

theorem deployment_zero_forms_rejected (p : Params) : checkDeployment p 0 = none := rfl

theorem bound_zero_commitments_rejected (p : Params) (rootCount evaluationCount maskLength : Nat)
    (h : p.numCommitments = 0) : checkBound p rootCount evaluationCount maskLength = none := by
  simp [checkBound,h]

theorem bound_zero_vectors_rejected (p : Params) (rootCount evaluationCount maskLength : Nat)
    (h : p.numVectors = 0) : checkBound p rootCount evaluationCount maskLength = none := by
  simp [checkBound,h]

theorem bound_zero_evaluations_rejected (p : Params) (rootCount maskLength : Nat) :
    checkBound p rootCount 0 maskLength = none := by simp [checkBound]

theorem bound_wrong_mask_length_rejected (p : Params) (rootCount evaluationCount maskLength : Nat)
    (h : maskLength ≠ (evaluationCount+7)/8) : checkBound p rootCount evaluationCount maskLength = none := by
  simp [checkBound,h]

theorem bound_wrong_root_count_rejected (p : Params) (rootCount evaluationCount maskLength : Nat)
    (h : rootCount ≠ p.numCommitments) : checkBound p rootCount evaluationCount maskLength = none := by
  simp [checkBound,h]

theorem bound_nondivisible_evaluation_count_rejected (p : Params) (rootCount evaluationCount maskLength : Nat)
    (h : evaluationCount % totalVectors p ≠ 0) : checkBound p rootCount evaluationCount maskLength = none := by
  simp [checkBound,h]

theorem core_success_partitions_all_variables (p : Params) (numForms : Nat) (forms : List (List Ext3))
    (h : checkCore p numForms = some forms) :
    p.numVariables = p.initialSumcheckRounds+p.foldingFactor*p.numRounds+p.finalSumcheckRounds :=
  WhirSchedule.accepted_schedule_factor_partition (schedule p)
    (core_success_implies_existing_schedule p numForms forms h)

theorem bound_success_quotient_is_positive (p : Params) (rootCount evaluationCount maskLength : Nat)
    (forms : List (List Ext3)) (h : checkBound p rootCount evaluationCount maskLength = some forms) :
    0 < totalVectors p ∧ 0 < evaluationCount/totalVectors p ∧
      forms.length = evaluationCount/totalVectors p := by
  have hb := bound_success_entry_guards p rootCount evaluationCount maskLength forms h
  have hf := forms_success_exact p _ forms
    (core_success_sequence p _ forms hb.2.2.2.2.2.2).2.2.2.2.2
  exact ⟨Nat.mul_pos hb.1 hb.2.1,hf.1,hf.2.1⟩

theorem forms_multi_branch_has_exact_raw_point_count (p : Params) (numForms : Nat)
    (forms : List (List Ext3)) (hne : numForms ≠ 1) (h : checkForms p numForms = some forms) :
    2 ≤ numForms ∧ p.additionalEvaluationPoints.length = numForms-2 ∧
      p.evaluationPoint.length = p.numVariables ∧ p.evaluationPoint2.length = p.numVariables := by
  have hf := forms_success_exact p numForms forms h
  have he := congrArg List.length hf.2.2.1
  have hm1 : p.evaluationPoint ∈ rawForms p numForms := by simp [rawForms,hne]
  have hm2 : p.evaluationPoint2 ∈ rawForms p numForms := by simp [rawForms,hne]
  have hall : ∀ point ∈ rawForms p numForms, point.length = p.numVariables := by
    rw [←hf.2.2.1]
    intro point hm
    obtain ⟨typed,ht,rfl⟩ := List.mem_map.mp hm
    simpa using hf.2.2.2 typed ht
  simp only [List.length_map,rawForms,hne,↓reduceIte,List.length_cons] at he
  exact ⟨by omega,by omega,hall _ hm1,hall _ hm2⟩

/-- The deployment helper intentionally does NOT add the grouped entry's
commitment/vector guards. Those source fields are unused by the core validator. -/
theorem deployment_does_not_validate_group_dimensions (p : Params) (numForms commitments vectors : Nat) :
    checkDeployment {p with numCommitments := commitments, numVectors := vectors} numForms =
      checkDeployment p numForms := rfl

/-- Domain projection retains the five source fields and their explicit guards, not an assumption that
the generator's multiplicative order equals the codeword length. -/
def exampleDomain : Domain := ⟨8,3,4,2,7⟩
def exampleRound : Round := ⟨⟨4,2,2,2,7⟩,3,2,1,2,2,11,13⟩
def exampleCoordinate : Arithmetic.Ext3 := ⟨1,2,3⟩
def examplePoint : List Arithmetic.Ext3 := List.replicate 3 exampleCoordinate
def exampleParams : Params :=
  { numVariables := 3
    foldingFactor := 1
    numVectors := 1
    numCommitments := 3
    outDomainSamples := 2
    inDomainSamples := 3
    initialSumcheckRounds := 1
    numRounds := 1
    finalSumcheckRounds := 1
    finalSize := 2
    initialDomain := exampleDomain
    initialInterleavingDepth := 2
    initialNumVariables := 3
    initialSumcheckPowThreshold := 17
    finalPowThreshold := 19
    finalSumcheckPowThreshold := 23
    evaluationPoint := examplePoint
    evaluationPoint2 := examplePoint
    additionalEvaluationPoints := [examplePoint]
    rounds := [exampleRound] }

/-- An ordinary typed-guard example with non-base Ext3 coordinates and one
intermediate round. It is NOT a proof fixture or a domain-order certificate. -/
theorem nonbase_three_form_success_example :
    (checkBound exampleParams 3 9 2).map (fun forms =>
      (forms.length,forms.map (List.map Subtype.val))) =
      some (3,[examplePoint,examplePoint,examplePoint]) := by decide

theorem single_form_success_example :
    (checkBound {exampleParams with evaluationPoint2 := [], additionalEvaluationPoints := []} 3 3 1).map
      (List.map (List.map Subtype.val)) = some [examplePoint] := by decide

theorem two_form_success_example :
    (checkBound {exampleParams with additionalEvaluationPoints := []} 3 6 1).map
      (List.map (List.map Subtype.val)) = some [examplePoint,examplePoint] := by decide

theorem deployment_and_bound_entry_are_distinct_example :
    (checkDeployment {exampleParams with numCommitments := 0, numVectors := 0} 3).isSome = true ∧
      checkBound {exampleParams with numCommitments := 0, numVectors := 0} 0 9 2 = none := by decide

theorem noncanonical_raw_coordinate_rejected_example :
    checkBound {exampleParams with evaluationPoint :=
      [⟨1,Arithmetic.modulus,3⟩,exampleCoordinate,exampleCoordinate]} 3 9 2 = none := by decide

theorem ignored_single_point_tail_rejected_example :
    checkBound exampleParams 3 3 1 = none := by decide

theorem intermediate_domain_failure_rejected_example :
    checkBound {exampleParams with rounds :=
      [{exampleRound with domain := {exampleRound.domain with codewordLength := 3}}]} 3 9 2 = none := by decide

theorem wrong_final_size_rejected_example :
    checkBound {exampleParams with finalSize := 4} 3 9 2 = none := by decide

theorem zero_internal_form_count_cannot_saturate_subtraction (p : Params) : checkForms p 0 = none := by
  unfold checkForms
  split
  · cases hp : checkPoint p.evaluationPoint with
    | none => simp [hp]
    | some first => simp [hp]
  · rfl

end Audit.Wire3.WhirParameters
