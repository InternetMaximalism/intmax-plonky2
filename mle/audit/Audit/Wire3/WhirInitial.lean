import Audit.Wire3.Spongefish

/-!
# Concrete WHIR initial phase

Manual executable slice of SpongefishWhirVerify.sol at 69516414:
_receiveCommitmentsAndOod, _phaseInitial, _completeOodMatrix, _accumulateTheSum.
Only the deterministic 32-byte Hash is a function parameter. Root/Ext3 reads,
challenge generation, mask checks, cross-answer order and both RLC challenges
consume the SAME Spongefish.State and actual transcript Bytes. No decoder or
evaluator observations supply accepted claims, constraints or the running sum.

`validatedParams` is a PRECONDITION projected from the entry/deployment shape
checks, not an extra guard in _phaseInitial. `forms` lists evaluationPoint,
then the nonempty evaluationPoint2 and additionalEvaluationPoints in that order.
It does not model the unrelated domain/round configuration checks. All Ext3
values have canonical typed limbs. Naturals/lists replace uint256/memory; source
overflow/allocation/Yul refinement, Rust equivalence, parameter decoding, full
WHIR tail, field/PCS/ROM probability and Keccak security are NOT proved here.
The output `forms` is a derived projection for the later final-claim interface,
not an extra stored field in Solidity VerifyState. Its coefficients are exactly
the initialConstraintRlc prefix. `validated_form_count` connects its count to
the source's evaluations.length / totalVectors expression.
-/
namespace Audit.Wire3.WhirInitial
open Spongefish (Hash Bytes Digest State Ext3)
open Verifier (zero add mul)

structure Params where
  numCommitments : Nat
  numVectors : Nat
  outDomainSamples : Nat
  initialNumVariables : Nat
  forms : List (List Ext3)

def totalVectors (p : Params) : Nat := p.numCommitments * p.numVectors
def totalOodPoints (p : Params) : Nat := p.numCommitments * p.outDomainSamples

def validatedParams (p : Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes) : Prop :=
  0 < p.numCommitments ∧ 0 < p.numVectors ∧ roots.length = p.numCommitments ∧
  0 < p.initialNumVariables ∧ p.initialNumVariables < 256 ∧ 0 < p.forms.length ∧
  (∀ form ∈ p.forms, form.length = p.initialNumVariables) ∧
  expected.length = p.forms.length * totalVectors p ∧ mask.length = (expected.length + 7) / 8

structure Commitment where
  root : Digest
  boundRoot : Digest
  points : List Ext3
  answers : List Ext3
  deriving DecidableEq

def receiveOne (hash : Hash) (source : Bytes) (p : Params) (expected : Digest)
    (s : State) : Option (Commitment × State) := do
  let (root, afterRoot) ← Spongefish.proverHash hash s source
  let (points, afterPoints) ← Spongefish.verifierExt3Many hash p.outDomainSamples afterRoot
  let (answers, afterAnswers) ← Spongefish.proverExt3Many hash source
    (p.outDomainSamples * p.numVectors) afterPoints
  let (boundRoot, next) ← Spongefish.proverHash hash afterAnswers source
  if boundRoot = expected ∧ boundRoot = root then
    pure (⟨root,boundRoot,points,answers⟩,next)
  else none

def receiveCommitments (hash : Hash) (source : Bytes) (p : Params) :
    List Digest → State → Option (List Commitment × State)
  | [], s => some ([],s)
  | root :: roots, s => do
      let (entry, next) ← receiveOne hash source p root s
      let (entries, last) ← receiveCommitments hash source p roots next
      pure (entry :: entries,last)

/-- Arithmetic little-endian mask-bit indexing: no ignored checked entry. -/
def isChecked (mask : Bytes) (index : Nat) : Prop :=
  ((mask.getD (index / 8) Spongefish.zeroByte).val / 2 ^ (index % 8)) % 2 = 1

instance (mask : Bytes) (index : Nat) : Decidable (isChecked mask index) := inferInstanceAs (Decidable (_ = _))

def readClaims (hash : Hash) (source mask : Bytes) :
    Nat → List Ext3 → State → Option (List Ext3 × State)
  | _, [], s => some ([],s)
  | i, expected :: rest, s => do
      let (actual, next) ← Spongefish.proverExt3 hash s source
      if isChecked mask i ∧ actual ≠ expected then none else do
        let (values,last) ← readClaims hash source mask (i+1) rest next
        pure (actual :: values,last)

def checkedMatch (mask : Bytes) : Nat → List Ext3 → List Ext3 → Prop
  | _, [], [] => True
  | i, expected :: es, actual :: xs =>
      (isChecked mask i → actual = expected) ∧ checkedMatch mask (i+1) es xs
  | _, _, _ => False

/-- Some is an already read own answer; none is one cross-answer byte read.
The lists are commitment-major, OOD-point-major, then vector-major. -/
def matrixSlot (p : Params) (entries : List Commitment) (c point vector : Nat) : Option Ext3 :=
  if c * p.numVectors ≤ vector ∧ vector < c * p.numVectors + p.numVectors then
    some (((entries.getD c ⟨Spongefish.zeroDigest,Spongefish.zeroDigest,[],[]⟩).answers).getD
      (point * p.numVectors + (vector - c * p.numVectors)) zero)
  else none

def matrixSlots (p : Params) (entries : List Commitment) : List (Option Ext3) :=
  (List.range p.numCommitments).bind fun c =>
    (List.range p.outDomainSamples).bind fun i =>
      (List.range (totalVectors p)).map fun j => matrixSlot p entries c i j

def crossCount : List (Option Ext3) → Nat
  | [] => 0
  | some _ :: rest => crossCount rest
  | none :: rest => 1 + crossCount rest

def completeSlots (hash : Hash) (source : Bytes) :
    List (Option Ext3) → State → Option (List Ext3 × State)
  | [], s => some ([],s)
  | some own :: rest, s => do
      let (values,last) ← completeSlots hash source rest s
      pure (own :: values,last)
  | none :: rest, s => do
      let (cross,next) ← Spongefish.proverExt3 hash s source
      let (values,last) ← completeSlots hash source rest next
      pure (cross :: values,last)

def preservesOwn : List (Option Ext3) → List Ext3 → Prop
  | [], [] => True
  | some own :: rest, actual :: values => own = actual ∧ preservesOwn rest values
  | none :: rest, _ :: values => preservesOwn rest values
  | _, _ => False

def dotRow (matrix vectorRlc : List Ext3) (row width : Nat) : Ext3 :=
  (List.range width).foldl (fun acc j =>
    add acc (mul (matrix.getD (row * width + j) zero) (vectorRlc.getD j zero))) zero

def accumulate (matrix vectorRlc constraintRlc : List Ext3) (offset width : Nat) :
    Nat → Nat → Ext3 → Ext3
  | _, 0, value => value
  | i, count+1, value => accumulate matrix vectorRlc constraintRlc offset width (i+1) count
      (add value (mul (dotRow matrix vectorRlc i width) (constraintRlc.getD (offset+i) zero)))

structure RoundConstraint where
  rlcCoeffs : List Ext3
  univariatePoints : List Ext3
  numVariables : Nat
  deriving DecidableEq

structure LinearForm where
  coefficient : Ext3
  point : List Ext3
  deriving DecidableEq

structure Result where
  commitments : List Commitment
  prevRoot : Digest
  evaluations : List Ext3
  oodMatrix : List Ext3
  vectorRlc : List Ext3
  initialConstraintRlc : List Ext3
  numLinearForms : Nat
  initialRoundConstraint : RoundConstraint
  forms : List LinearForm
  theSum : Ext3
  deriving DecidableEq

def assemble (p : Params) (entries : List Commitment)
    (evaluations oodMatrix vectorRlc constraintRlc : List Ext3) : Result :=
  let numForms := p.forms.length
  { commitments := entries
    prevRoot := (entries.getD 0 ⟨Spongefish.zeroDigest,Spongefish.zeroDigest,[],[]⟩).root
    evaluations := evaluations
    oodMatrix := oodMatrix
    vectorRlc := vectorRlc
    initialConstraintRlc := constraintRlc
    numLinearForms := numForms
    initialRoundConstraint := ⟨(constraintRlc.drop numForms).take (totalOodPoints p),
      entries.bind (·.points), p.initialNumVariables⟩
    forms := (p.forms.zip (constraintRlc.take numForms)).map fun pair => ⟨pair.2,pair.1⟩
    theSum := accumulate oodMatrix vectorRlc constraintRlc numForms (totalVectors p)
      0 (totalOodPoints p)
      (accumulate evaluations vectorRlc constraintRlc 0 (totalVectors p) 0 numForms zero) }

/-- Caller supplies validatedParams; no new internal runtime shape guards. -/
def phaseInitial (hash : Hash) (source : Bytes) (p : Params) (expectedRoots : List Digest)
    (expected : List Ext3) (mask : Bytes) (s : State) : Option (Result × State) := do
  let (entries, afterCommitments) ← receiveCommitments hash source p expectedRoots s
  let (evaluations, afterClaims) ← readClaims hash source mask 0 expected afterCommitments
  let (oodMatrix, afterCross) ← completeSlots hash source (matrixSlots p entries) afterClaims
  let (vectorRlc, afterVectorRlc) ← Spongefish.geometricChallenge hash afterCross (totalVectors p)
  let (constraintRlc, next) ← Spongefish.geometricChallenge hash afterVectorRlc
    (totalOodPoints p + p.forms.length)
  pure (assemble p entries evaluations oodMatrix vectorRlc constraintRlc,next)

theorem prover_hash_exact_read (hash : Hash) (source : Bytes) (s t : State) (root : Digest)
    (h : Spongefish.proverHash hash s source = some (root,t)) :
    t.transcriptPos = s.transcriptPos + 32 ∧ t.transcriptPos ≤ source.length ∧
    t.hintPos = s.hintPos ∧ root.val = (source.drop s.transcriptPos).take 32 := by
  unfold Spongefish.proverHash at h
  cases hp : Spongefish.proverMessage hash s source 32 with
  | none => simp [hp] at h
  | some pair =>
      rcases pair with ⟨data,next⟩
      simp only [hp,bind,Option.bind] at h
      split at h
      · cases h
        have hs := Spongefish.prover_message_reads_then_absorbs hash s t source data 32 hp
        exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.2⟩
      · contradiction

theorem geometric_challenge_shape (hash : Hash) (s t : State) (count : Nat) (xs : List Ext3)
    (h : Spongefish.geometricChallenge hash s count = some (xs,t)) :
    xs.length = count ∧ t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos := by
  cases count with
  | zero => cases h; simp
  | succ n => cases n with
    | zero => cases h; simp
    | succ n =>
        cases hv : Spongefish.verifierExt3 hash s with
        | none => simp [Spongefish.geometricChallenge,hv] at h
        | some pair =>
            rcases pair with ⟨x,next⟩
            simp only [Spongefish.geometricChallenge,hv,bind,Option.bind,pure,
              Option.some.injEq,Prod.mk.injEq] at h
            rcases h with ⟨rfl,rfl⟩
            have hc := Spongefish.verifier_ext3_exact_cursor_and_bytes hash s next x hv
            exact ⟨Spongefish.geometric_powers_length _ _ _,hc.1,hc.2.1⟩

theorem receive_one_success (hash : Hash) (source : Bytes) (p : Params) (expected : Digest)
    (s t : State) (entry : Commitment) (h : receiveOne hash source p expected s = some (entry,t)) :
    entry.root = expected ∧ entry.boundRoot = expected ∧
    entry.points.length = p.outDomainSamples ∧
    entry.answers.length = p.outDomainSamples * p.numVectors ∧
    t.transcriptPos = s.transcriptPos + (64 + 24 * (p.outDomainSamples * p.numVectors)) ∧
    t.transcriptPos ≤ source.length ∧ t.hintPos = s.hintPos := by
  unfold receiveOne at h
  cases hr : Spongefish.proverHash hash s source with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨root,afterRoot⟩
      cases hp : Spongefish.verifierExt3Many hash p.outDomainSamples afterRoot with
      | none => simp [hr,hp] at h
      | some pair =>
          rcases pair with ⟨points,afterPoints⟩
          cases ha : Spongefish.proverExt3Many hash source (p.outDomainSamples*p.numVectors) afterPoints with
          | none => simp [hr,hp,ha] at h
          | some pair =>
              rcases pair with ⟨answers,afterAnswers⟩
              cases hb : Spongefish.proverHash hash afterAnswers source with
              | none => simp [hr,hp,ha,hb] at h
              | some pair =>
                  rcases pair with ⟨boundRoot,next⟩
                  simp only [hr,hp,ha,hb,bind,Option.bind] at h
                  split at h
                  · cases h
                    have hroot := prover_hash_exact_read hash source s afterRoot root hr
                    have hpoints := Spongefish.verifier_many_exact_count_and_counter hash
                      p.outDomainSamples afterRoot afterPoints points hp
                    have hanswers := Spongefish.prover_many_exact_count_and_cursor hash source
                      (p.outDomainSamples*p.numVectors) afterPoints afterAnswers answers ha
                    have hbound := prover_hash_exact_read hash source afterAnswers t boundRoot hb
                    rcases ‹boundRoot = expected ∧ boundRoot = root› with ⟨he,hbnd⟩
                    exact ⟨hbnd.symm.trans he,he,hpoints.1,hanswers.1,by omega,hbound.2.1,
                      hbound.2.2.1.trans (hanswers.2.2.trans (hpoints.2.2.1.trans hroot.2.2.1))⟩
                  · contradiction

theorem receive_commitments_success (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (s t : State) (entries : List Commitment)
    (h : receiveCommitments hash source p roots s = some (entries,t)) :
    entries.map (·.root) = roots ∧ entries.map (·.boundRoot) = roots ∧
    (∀ entry ∈ entries, entry.points.length = p.outDomainSamples ∧
      entry.answers.length = p.outDomainSamples * p.numVectors) ∧
    t.transcriptPos = s.transcriptPos + roots.length * (64 + 24 * (p.outDomainSamples*p.numVectors)) ∧
    t.hintPos = s.hintPos := by
  induction roots generalizing s entries with
  | nil => cases h; simp
  | cons root roots ih =>
      cases ho : receiveOne hash source p root s with
      | none => simp [receiveCommitments,ho] at h
      | some pair =>
          rcases pair with ⟨entry,next⟩
          cases hs : receiveCommitments hash source p roots next with
          | none => simp [receiveCommitments,ho,hs] at h
          | some pair =>
              rcases pair with ⟨rest,last⟩
              simp only [receiveCommitments,ho,hs,bind,Option.bind,pure,
                Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              have he := receive_one_success hash source p root s next entry ho
              have ht := ih next rest hs
              refine ⟨by simp [he.1,ht.1],by simp [he.2.1,ht.2.1],?_,?_,ht.2.2.2.2.trans he.2.2.2.2.2.2⟩
              · intro x hx
                rcases List.mem_cons.mp hx with hx | hx
                · subst x; exact ⟨he.2.2.1,he.2.2.2.1⟩
                · exact ht.2.2.1 x hx
              · rw [List.length_cons,Nat.add_mul,Nat.one_mul]
                omega

theorem read_claims_success (hash : Hash) (source mask : Bytes) (index : Nat)
    (expected actual : List Ext3) (s t : State)
    (h : readClaims hash source mask index expected s = some (actual,t)) :
    actual.length = expected.length ∧ checkedMatch mask index expected actual ∧
    t.transcriptPos = s.transcriptPos + 24 * expected.length ∧ t.hintPos = s.hintPos := by
  induction expected generalizing index s actual with
  | nil => cases h; simp [checkedMatch]
  | cons expected rest ih =>
      cases hp : Spongefish.proverExt3 hash s source with
      | none => simp [readClaims,hp] at h
      | some pair =>
          rcases pair with ⟨value,next⟩
          simp only [readClaims,hp,bind,Option.bind] at h
          split at h
          · contradiction
          · rename_i hcheck
            cases hr : readClaims hash source mask (index+1) rest next with
            | none => simp [hr] at h
            | some pair =>
                rcases pair with ⟨values,last⟩
                simp only [hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
                rcases h with ⟨rfl,rfl⟩
                have hv := Spongefish.prover_ext3_consumes_exact_canonical_bytes hash s next source value hp
                have ht := ih (index+1) values next hr
                refine ⟨by simp [ht.1],⟨?_,ht.2.1⟩,?_,ht.2.2.2.trans hv.2.2.1⟩
                · intro hc
                  by_cases heq : value = expected
                  · exact heq
                  · exact False.elim (hcheck ⟨hc,heq⟩)
                · simp only [List.length_cons]; omega

theorem fixed_flat_map_length {α β : Type} (xs : List α) (f : α → List β) (width : Nat)
    (h : ∀ x ∈ xs, (f x).length = width) : (xs.bind f).length = xs.length * width := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.bind_cons,List.length_append,List.length_cons]
      rw [h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))]
      rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]

theorem range_loop_length (n : Nat) (xs : List Nat) :
    (List.range.loop n xs).length = n + xs.length := by
  induction n generalizing xs with
  | zero => simp [List.range.loop]
  | succ n ih => simp only [List.range.loop,ih,List.length_cons]; omega

theorem range_length (n : Nat) : (List.range n).length = n := by
  simpa only [List.range,List.length_nil,Nat.add_zero] using range_loop_length n []

theorem matrix_slots_length (p : Params) (entries : List Commitment) :
    (matrixSlots p entries).length = totalOodPoints p * totalVectors p := by
  unfold matrixSlots
  rw [fixed_flat_map_length _ _ (p.outDomainSamples * totalVectors p)]
  · simp [range_length,totalOodPoints,Nat.mul_assoc]
  · intro c _
    rw [fixed_flat_map_length _ _ (totalVectors p)]
    · simp [range_length]
    · intro i _; simp [range_length]

theorem complete_slots_success (hash : Hash) (source : Bytes) (slots : List (Option Ext3))
    (values : List Ext3) (s t : State) (h : completeSlots hash source slots s = some (values,t)) :
    values.length = slots.length ∧ preservesOwn slots values ∧
    t.transcriptPos = s.transcriptPos + 24 * crossCount slots ∧ t.hintPos = s.hintPos := by
  induction slots generalizing s values with
  | nil => cases h; simp [preservesOwn,crossCount]
  | cons slot slots ih =>
      cases slot with
      | some own =>
          cases hr : completeSlots hash source slots s with
          | none => simp [completeSlots,hr] at h
          | some pair =>
              rcases pair with ⟨rest,last⟩
              simp only [completeSlots,hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              have ht := ih rest s hr
              exact ⟨by simp [ht.1],⟨rfl,ht.2.1⟩,ht.2.2.1,ht.2.2.2⟩
      | none =>
          cases hp : Spongefish.proverExt3 hash s source with
          | none => simp [completeSlots,hp] at h
          | some pair =>
              rcases pair with ⟨cross,next⟩
              cases hr : completeSlots hash source slots next with
              | none => simp [completeSlots,hp,hr] at h
              | some pair =>
                  rcases pair with ⟨rest,last⟩
                  simp only [completeSlots,hp,hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
                  rcases h with ⟨rfl,rfl⟩
                  have hp' := Spongefish.prover_ext3_consumes_exact_canonical_bytes hash s next source cross hp
                  have ht := ih rest next hr
                  refine ⟨by simp [ht.1],ht.2.1,?_,ht.2.2.2.trans hp'.2.2.1⟩
                  simp only [crossCount]; omega

theorem checked_match_at_index (mask : Bytes) (start : Nat) (expected actual : List Ext3)
    (h : checkedMatch mask start expected actual) (i : Nat) (hi : i < expected.length)
    (hc : isChecked mask (start+i)) : actual.getD i zero = expected.getD i zero := by
  induction expected generalizing actual start i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons e es ih =>
      cases actual with
      | nil => exact False.elim h
      | cons a xs =>
          cases i with
          | zero => simpa only [List.getD_cons_zero,Nat.add_zero] using h.1 hc
          | succ i =>
              simp only [List.getD_cons_succ]
              apply ih (start+1) xs h.2 i (by simp only [List.length_cons] at hi; omega)
              simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hc

theorem mask_byte_in_bounds (expected : List Ext3) (mask : Bytes) (i : Nat)
    (hm : mask.length = (expected.length+7)/8) (hi : i < expected.length) : i/8 < mask.length := by
  omega

theorem preserves_own_at_index (slots : List (Option Ext3)) (values : List Ext3)
    (h : preservesOwn slots values) (i : Nat) (own : Ext3)
    (hs : slots.get? i = some (some own)) : values.get? i = some own := by
  induction slots generalizing values i with
  | nil => simp at hs
  | cons slot slots ih =>
      cases values with
      | nil => cases slot <;> exact False.elim h
      | cons value values =>
          cases i with
          | zero =>
              simp only [List.get?_cons_zero,Option.some.injEq] at hs
              subst slot
              simp only [List.get?_cons_zero]
              exact congrArg some h.1.symm
          | succ i =>
              simp only [List.get?_cons_succ] at hs ⊢
              cases slot with
              | none => exact ih values h i hs
              | some _ => exact ih values h.2 i hs

theorem own_answer_index_bounded (p : Params) (point vector commitment : Nat)
    (hp : point < p.outDomainSamples)
    (hv : commitment*p.numVectors ≤ vector ∧ vector < commitment*p.numVectors+p.numVectors) :
    point*p.numVectors + (vector-commitment*p.numVectors) < p.outDomainSamples*p.numVectors := by
  have ha : point*p.numVectors + p.numVectors ≤ p.outDomainSamples*p.numVectors := by
    have hh := Nat.mul_le_mul_right p.numVectors (show point+1 ≤ p.outDomainSamples by omega)
    simpa only [Nat.add_mul,Nat.one_mul] using hh
  omega

theorem ordered_matrix_row_index_bounded (row rows j width : Nat)
    (hr : row < rows) (hj : j < width) : row*width+j < rows*width := by
  have hm := Nat.mul_le_mul_right width (show row+1 ≤ rows by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  omega

theorem phase_initial_trace (hash : Hash) (source : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (s t : State) (result : Result)
    (h : phaseInitial hash source p roots expected mask s = some (result,t)) :
    ∃ entries evaluations oodMatrix vectorRlc constraintRlc
      afterCommitments afterClaims afterCross afterVectorRlc,
      receiveCommitments hash source p roots s = some (entries,afterCommitments) ∧
      readClaims hash source mask 0 expected afterCommitments = some (evaluations,afterClaims) ∧
      completeSlots hash source (matrixSlots p entries) afterClaims = some (oodMatrix,afterCross) ∧
      Spongefish.geometricChallenge hash afterCross (totalVectors p) = some (vectorRlc,afterVectorRlc) ∧
      Spongefish.geometricChallenge hash afterVectorRlc (totalOodPoints p+p.forms.length) = some (constraintRlc,t) ∧
      result = assemble p entries evaluations oodMatrix vectorRlc constraintRlc := by
  unfold phaseInitial at h
  cases hr : receiveCommitments hash source p roots s with
  | none => simp [hr] at h
  | some pair =>
      rcases pair with ⟨entries,a⟩
      cases he : readClaims hash source mask 0 expected a with
      | none => simp [hr,he] at h
      | some pair =>
          rcases pair with ⟨evaluations,b⟩
          cases hm : completeSlots hash source (matrixSlots p entries) b with
          | none => simp [hr,he,hm] at h
          | some pair =>
              rcases pair with ⟨oodMatrix,c⟩
              cases hv : Spongefish.geometricChallenge hash c (totalVectors p) with
              | none => simp [hr,he,hm,hv] at h
              | some pair =>
                  rcases pair with ⟨vectorRlc,d⟩
                  cases hc : Spongefish.geometricChallenge hash d (totalOodPoints p+p.forms.length) with
                  | none => simp [hr,he,hm,hv,hc] at h
                  | some pair =>
                      rcases pair with ⟨constraintRlc,last⟩
                      simp only [hr,he,hm,hv,hc,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
                      rcases h with ⟨rfl,rfl⟩
                      exact ⟨entries,evaluations,oodMatrix,vectorRlc,constraintRlc,a,b,c,d,
                        rfl,he,hm,hv,hc,rfl⟩

theorem initial_all_roots_and_checked_claims (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (s t : State) (r : Result)
    (h : phaseInitial hash source p roots expected mask s = some (r,t)) :
    r.commitments.map (·.root) = roots ∧ r.commitments.map (·.boundRoot) = roots ∧
    r.evaluations.length = expected.length ∧
    (∀ i, i < expected.length → isChecked mask i → r.evaluations.getD i zero = expected.getD i zero) ∧
    preservesOwn (matrixSlots p r.commitments) r.oodMatrix := by
  rcases phase_initial_trace hash source p roots expected mask s t r h with
    ⟨entries,evaluations,matrix,vr,cr,a,b,c,d,hr,he,hm,_,_,rfl⟩
  have hrs := receive_commitments_success hash source p roots s a entries hr
  have hes := read_claims_success hash source mask 0 expected evaluations a b he
  have hms := complete_slots_success hash source (matrixSlots p entries) matrix b c hm
  refine ⟨hrs.1,hrs.2.1,hes.1,?_,hms.2.1⟩
  intro i hi hc
  exact checked_match_at_index mask 0 expected evaluations hes.2.1 i hi (by simpa using hc)

theorem initial_exact_read_count (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (s t : State) (r : Result)
    (h : phaseInitial hash source p roots expected mask s = some (r,t)) :
    t.transcriptPos = s.transcriptPos +
      roots.length*(64+24*(p.outDomainSamples*p.numVectors)) +
      24*expected.length + 24*crossCount (matrixSlots p r.commitments) ∧ t.hintPos = s.hintPos := by
  rcases phase_initial_trace hash source p roots expected mask s t r h with
    ⟨entries,evaluations,matrix,vr,cr,a,b,c,d,hr,he,hm,hv,hc,rfl⟩
  have hrs := receive_commitments_success hash source p roots s a entries hr
  have hes := read_claims_success hash source mask 0 expected evaluations a b he
  have hms := complete_slots_success hash source (matrixSlots p entries) matrix b c hm
  have hvs := geometric_challenge_shape hash c d (totalVectors p) vr hv
  have hcs := geometric_challenge_shape hash d t (totalOodPoints p+p.forms.length) cr hc
  exact ⟨by dsimp only [assemble]; omega,
    hcs.2.2.trans (hvs.2.2.trans (hms.2.2.2.trans (hes.2.2.2.trans hrs.2.2.2.2)))⟩

theorem validated_form_count (p : Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes)
    (h : validatedParams p roots expected mask) : expected.length / totalVectors p = p.forms.length := by
  have hn : 0 < totalVectors p := Nat.mul_pos h.1 h.2.1
  rw [h.2.2.2.2.2.2.2.1]
  exact Nat.mul_div_cancel _ hn

theorem initial_output_shapes (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (s t : State) (r : Result)
    (hp : validatedParams p roots expected mask)
    (h : phaseInitial hash source p roots expected mask s = some (r,t)) :
    r.commitments.length = p.numCommitments ∧
    (∀ entry ∈ r.commitments, entry.points.length = p.outDomainSamples ∧
      entry.answers.length = p.outDomainSamples*p.numVectors) ∧
    r.evaluations.length = p.forms.length*totalVectors p ∧
    r.oodMatrix.length = totalOodPoints p*totalVectors p ∧
    r.vectorRlc.length = totalVectors p ∧
    r.initialConstraintRlc.length = p.forms.length+totalOodPoints p ∧
    r.initialRoundConstraint.rlcCoeffs.length = totalOodPoints p ∧
    r.initialRoundConstraint.univariatePoints.length = totalOodPoints p ∧
    r.forms.length = p.forms.length := by
  rcases phase_initial_trace hash source p roots expected mask s t r h with
    ⟨entries,evaluations,matrix,vr,cr,a,b,c,d,hr,he,hm,hv,hc,rfl⟩
  have hrs := receive_commitments_success hash source p roots s a entries hr
  have hes := read_claims_success hash source mask 0 expected evaluations a b he
  have hms := complete_slots_success hash source (matrixSlots p entries) matrix b c hm
  have hvs := geometric_challenge_shape hash c d (totalVectors p) vr hv
  have hcs := geometric_challenge_shape hash d t (totalOodPoints p+p.forms.length) cr hc
  have hentries : entries.length = p.numCommitments := by
    have hh := congrArg List.length hrs.1
    simpa only [List.length_map,hp.2.2.1] using hh
  refine ⟨hentries,hrs.2.2.1,hes.1.trans hp.2.2.2.2.2.2.2.1,
    hms.1.trans (matrix_slots_length p entries),hvs.1,?_,?_,?_,?_⟩
  · dsimp only [assemble]; omega
  · dsimp only [assemble]
    simp only [List.length_take,List.length_drop,hcs.1]
    omega
  · dsimp only [assemble]
    rw [fixed_flat_map_length _ _ p.outDomainSamples (by intro x hx; exact (hrs.2.2.1 x hx).1),hentries]
    rfl
  · dsimp only [assemble]
    simp only [List.length_map,List.length_zip,List.length_take,hcs.1]
    omega

theorem initial_sum_and_constraints_same_data (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (s t : State) (r : Result)
    (h : phaseInitial hash source p roots expected mask s = some (r,t)) :
    r.theSum = accumulate r.oodMatrix r.vectorRlc r.initialConstraintRlc p.forms.length (totalVectors p)
      0 (totalOodPoints p)
      (accumulate r.evaluations r.vectorRlc r.initialConstraintRlc 0 (totalVectors p) 0 p.forms.length zero) ∧
    r.initialRoundConstraint.rlcCoeffs = (r.initialConstraintRlc.drop p.forms.length).take (totalOodPoints p) ∧
    r.initialRoundConstraint.univariatePoints = r.commitments.bind (·.points) ∧
    r.initialRoundConstraint.numVariables = p.initialNumVariables ∧
    r.forms = (p.forms.zip (r.initialConstraintRlc.take p.forms.length)).map (fun pair => ⟨pair.2,pair.1⟩) := by
  rcases phase_initial_trace hash source p roots expected mask s t r h with
    ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem get_default_in_list {α : Type} (xs : List α) (fallback : α) (i : Nat)
    (h : i < xs.length) : xs.getD i fallback ∈ xs := by
  induction xs generalizing i with
  | nil => simp only [List.length_nil] at h; omega
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [List.getD_cons_succ,List.mem_cons]
          exact Or.inr (ih i (by simp only [List.length_cons] at h; omega))

theorem initialized_own_read_in_bounds (p : Params) (entries : List Commitment)
    (hc : entries.length = p.numCommitments)
    (ha : ∀ e ∈ entries, e.answers.length = p.outDomainSamples*p.numVectors)
    (c point vector : Nat) (hci : c < p.numCommitments) (hpi : point < p.outDomainSamples)
    (hv : c*p.numVectors ≤ vector ∧ vector < c*p.numVectors+p.numVectors) :
    c < entries.length ∧
    point*p.numVectors+(vector-c*p.numVectors) <
      (entries.getD c ⟨Spongefish.zeroDigest,Spongefish.zeroDigest,[],[]⟩).answers.length := by
  have hi : c < entries.length := by omega
  refine ⟨hi,?_⟩
  rw [ha _ (get_default_in_list entries _ c hi)]
  exact own_answer_index_bounded p point vector c hpi hv

theorem initial_forms_use_supplied_points (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (s t : State) (r : Result)
    (hp : validatedParams p roots expected mask)
    (h : phaseInitial hash source p roots expected mask s = some (r,t)) :
    ∀ form ∈ r.forms, form.point ∈ p.forms ∧ form.point.length = p.initialNumVariables := by
  rcases phase_initial_trace hash source p roots expected mask s t r h with
    ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩
  intro form hm
  rcases List.mem_map.mp hm with ⟨pair,hpair,he⟩
  subst form
  have hm := (List.of_mem_zip hpair).1
  exact ⟨hm,hp.2.2.2.2.2.2.1 pair.1 hm⟩

theorem accumulate_access_bounds (matrix vectorRlc constraintRlc : List Ext3)
    (rows width offset i j : Nat)
    (hm : matrix.length = rows*width) (hv : vectorRlc.length = width)
    (hc : offset+rows ≤ constraintRlc.length) (hi : i < rows) (hj : j < width) :
    i*width+j < matrix.length ∧ j < vectorRlc.length ∧ offset+i < constraintRlc.length := by
  refine ⟨?_,by omega,by omega⟩
  rw [hm]
  exact ordered_matrix_row_index_bounded i rows j width hi hj

theorem receive_commitments_preserves_bound (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (s t : State) (entries : List Commitment)
    (hs : s.transcriptPos ≤ source.length)
    (h : receiveCommitments hash source p roots s = some (entries,t)) : t.transcriptPos ≤ source.length := by
  induction roots generalizing s entries with
  | nil => cases h; exact hs
  | cons root roots ih =>
      cases ho : receiveOne hash source p root s with
      | none => simp [receiveCommitments,ho] at h
      | some pair =>
          rcases pair with ⟨entry,next⟩
          cases hr : receiveCommitments hash source p roots next with
          | none => simp [receiveCommitments,ho,hr] at h
          | some pair =>
              rcases pair with ⟨rest,last⟩
              simp only [receiveCommitments,ho,hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              exact ih next rest (receive_one_success hash source p root s next entry ho).2.2.2.2.2.1 hr

theorem read_claims_preserves_bound (hash : Hash) (source mask : Bytes) (index : Nat)
    (expected actual : List Ext3) (s t : State) (hs : s.transcriptPos ≤ source.length)
    (h : readClaims hash source mask index expected s = some (actual,t)) : t.transcriptPos ≤ source.length := by
  induction expected generalizing index s actual with
  | nil => cases h; exact hs
  | cons expected rest ih =>
      cases hp : Spongefish.proverExt3 hash s source with
      | none => simp [readClaims,hp] at h
      | some pair =>
          rcases pair with ⟨value,next⟩
          simp only [readClaims,hp,bind,Option.bind] at h
          split at h
          · contradiction
          · cases hr : readClaims hash source mask (index+1) rest next with
            | none => simp [hr] at h
            | some pair =>
                rcases pair with ⟨values,last⟩
                simp only [hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
                rcases h with ⟨rfl,rfl⟩
                exact ih (index+1) values next
                  (Spongefish.prover_ext3_consumes_exact_canonical_bytes hash s next source value hp).2.1 hr

theorem complete_slots_preserves_bound (hash : Hash) (source : Bytes) (slots : List (Option Ext3))
    (values : List Ext3) (s t : State) (hs : s.transcriptPos ≤ source.length)
    (h : completeSlots hash source slots s = some (values,t)) : t.transcriptPos ≤ source.length := by
  induction slots generalizing s values with
  | nil => cases h; exact hs
  | cons slot slots ih =>
      cases slot with
      | some own =>
          cases hr : completeSlots hash source slots s with
          | none => simp [completeSlots,hr] at h
          | some pair =>
              rcases pair with ⟨rest,last⟩
              simp only [completeSlots,hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              exact ih rest s hs hr
      | none =>
          cases hp : Spongefish.proverExt3 hash s source with
          | none => simp [completeSlots,hp] at h
          | some pair =>
              rcases pair with ⟨cross,next⟩
              cases hr : completeSlots hash source slots next with
              | none => simp [completeSlots,hp,hr] at h
              | some pair =>
                  rcases pair with ⟨rest,last⟩
                  simp only [completeSlots,hp,hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
                  rcases h with ⟨rfl,rfl⟩
                  exact ih rest next
                    (Spongefish.prover_ext3_consumes_exact_canonical_bytes hash s next source cross hp).2.1 hr

theorem initial_preserves_byte_bound (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (s t : State) (r : Result)
    (hs : s.transcriptPos ≤ source.length)
    (h : phaseInitial hash source p roots expected mask s = some (r,t)) : t.transcriptPos ≤ source.length := by
  rcases phase_initial_trace hash source p roots expected mask s t r h with
    ⟨entries,evaluations,matrix,vr,cr,a,b,c,d,hr,he,hm,hv,hc,_⟩
  have ha := receive_commitments_preserves_bound hash source p roots s a entries hs hr
  have hb := read_claims_preserves_bound hash source mask 0 expected evaluations a b ha he
  have hc' := complete_slots_preserves_bound hash source (matrixSlots p entries) matrix b c hb hm
  have hv' := (geometric_challenge_shape hash c d (totalVectors p) vr hv).2.1
  have he' := (geometric_challenge_shape hash d t (totalOodPoints p+p.forms.length) cr hc).2.1
  omega

/-- Ordinary two-commitment instance: one checked and one unchecked zero claim.
It is a deterministic parser/phase example, not a cryptographic hash model or
a complete WHIR proof. All 272 consumed bytes are canonical zeros. -/
def exampleParams : Params := ⟨2,1,1,1,[[zero]]⟩
def exampleHash : Hash := fun _ => Spongefish.zeroDigest
def exampleSource : Bytes := List.replicate 272 Spongefish.zeroByte
def exampleRoots : List Digest := [Spongefish.zeroDigest,Spongefish.zeroDigest]
def exampleClaims : List Ext3 := [zero,zero]
def exampleMask : Bytes := [⟨1,by decide⟩]
def exampleEntry : Commitment := ⟨Spongefish.zeroDigest,Spongefish.zeroDigest,[zero],[zero]⟩
def exampleStart : State := Spongefish.init exampleHash [] [] []
def exampleResult : Result := assemble exampleParams [exampleEntry,exampleEntry]
  [zero,zero] [zero,zero,zero,zero] [Spongefish.one,zero] [Spongefish.one,zero,zero]

theorem example_params_are_valid : validatedParams exampleParams exampleRoots exampleClaims exampleMask := by
  simp [validatedParams,exampleParams,exampleRoots,exampleClaims,exampleMask,totalVectors]

theorem example_mask_has_checked_and_unchecked : isChecked exampleMask 0 ∧ ¬ isChecked exampleMask 1 := by
  decide

theorem example_cross_order_and_count :
    matrixSlots exampleParams [exampleEntry,exampleEntry] = [some zero,none,none,some zero] ∧
    crossCount (matrixSlots exampleParams [exampleEntry,exampleEntry]) = 2 := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem example_initial_phase_succeeds :
    phaseInitial exampleHash exampleSource exampleParams exampleRoots exampleClaims exampleMask exampleStart =
      some (exampleResult,⟨⟨Spongefish.zeroDigest,8⟩,272,0⟩) := by decide

end Audit.Wire3.WhirInitial
