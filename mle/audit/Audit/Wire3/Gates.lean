import Audit.Wire3.Verifier

/-!
Concrete gate metadata, selector, and a partial gate evaluator at 54400f9f.
Runtime source: Plonky2GateEvaluatorExt3.sol (_validateConfiguration,
_validateGate, _unfilteredDegree, _computeFilter, _evalConstant,
_evalPublicInput, _evalArithmetic, _evalArithmeticExtension, _evalMulExtension),
GoldilocksExt3.reduceWithPowers, and verifier_v2.rs's separate lookup guard.

All 14 configured families have concrete parameter/size/degree checks here.
Evaluation is implemented only for ids 0,1,2,3,6,7. Other valid ACTIVE families
return `none` from this partial evaluator (zero-filter skips remain executable);
this is a MODEL COVERAGE LIMIT, not a claim
that the production implementation rejects them. In particular no Poseidon,
MDS, exponentiation, base-sum, reducing, random-access, or coset evaluation is
delegated to an assumed-sound opaque evaluator.

Metadata naturals represent ABI values with explicit u8/u16 guards. Canonical
Ext3 values reuse Verifier's concrete arithmetic subtype. List reads use a
default only to make helpers total; access-bound theorems justify reads for
the implemented families under configuration and input-size checks. The raw
helpers are not standalone production entry points. Solidity/Yul allocation,
compiler semantics, Rust structural gate classification, configuration hash
binding and degree-as-a-polynomial proofs remain outside this model.
The lookup guard belongs to Rust common-data validation, not the Solidity gate
evaluator API. Zero constraints alone do not prove a circuit witness exists.
-/
namespace Audit.Wire3.Gates
open Verifier

structure GateInfo where
  gateId : Nat
  selectorIndex : Nat
  groupStart : Nat
  groupEnd : Nat
  gateRowIndex : Nat
  numConstraints : Nat
  numOrConsts : Nat
  param2 : Nat
  param3 : Nat
  deriving DecidableEq

structure Config where
  numSelectors : Nat
  numConstants : Nat
  numGateConstraints : Nat
  numWires : Nat
  quotientDegree : Nat

structure Requirements where
  constraints : Nat
  wires : Nat
  localConstants : Nat
  degree : Nat
  deriving DecidableEq

def supportedBase (b : Nat) : Bool := decide
  ((2 ≤ b ∧ b ≤ 8) ∨ b = 16 ∨ b = 32 ∨ b = 64 ∨ b = 128 ∨ b = 256)

def auxZero (g : GateInfo) : Bool := decide (g.param2 = 0 ∧ g.param3 = 0)
def paramsZero (g : GateInfo) : Bool := decide (g.numOrConsts = 0) && auxZero g

/-- Exact requirement formulas; Nat subtraction/division on coset parameters
    occurs only after the same positivity/range checks as production. -/
def requirements (g : GateInfo) : Option Requirements :=
  let n := g.numOrConsts
  match g.gateId with
  | 0 => if paramsZero g then some ⟨0, 0, 0, 0⟩ else none
  | 1 => if auxZero g then some ⟨n, n, n, 1⟩ else none
  | 2 => if paramsZero g then some ⟨4, 4, 0, 1⟩ else none
  | 3 => if auxZero g then some ⟨n, 4 * n, 2, 3⟩ else none
  | 4 => if paramsZero g then some ⟨123, 135, 0, 7⟩ else none
  | 5 => if paramsZero g then some ⟨24, 48, 0, 1⟩ else none
  | 6 => if auxZero g then some ⟨2 * n, 8 * n, 2, 3⟩ else none
  | 7 => if auxZero g then some ⟨2 * n, 6 * n, 1, 3⟩ else none
  | 8 => if auxZero g && decide (0 < n) then some ⟨n + 1, 2 * n + 2, 0, 4⟩ else none
  | 9 => if decide (g.param3 = 0) && supportedBase g.param2 then some ⟨n + 1, n + 1, 0, g.param2⟩ else none
  | 10 => if auxZero g && decide (0 < n) then some ⟨2 * n, 4 + 3 * n, 0, 2⟩ else none
  | 11 => if auxZero g && decide (0 < n) then some ⟨2 * n, 4 + 4 * n, 0, 2⟩ else none
  | 12 => if 0 < n ∧ n ≤ 7 ∧ 0 < g.param2 then
      some ⟨g.param2 * (n + 2) + g.param3,
        (2 + 2 ^ n) * g.param2 + g.param3 + g.param2 * n, g.param3, n + 1⟩ else none
  | 13 => if g.param3 = 0 ∧ 0 < n ∧ n ≤ 5 ∧ 2 ≤ g.param2 ∧ g.param2 ≤ 2 ^ n then
      let k := (2 ^ n - 2) / (g.param2 - 1)
      some ⟨4 + 4 * k, 7 + 2 * 2 ^ n + 4 * k, 0, g.param2⟩ else none
  | _ => none

def abiWidths (g : GateInfo) : Prop :=
  g.gateId < 256 ∧ g.selectorIndex < 256 ∧ g.groupStart < 256 ∧
  g.groupEnd < 256 ∧ g.gateRowIndex < 256 ∧ g.numConstraints < 65536 ∧
  g.numOrConsts < 65536 ∧ g.param2 < 65536 ∧ g.param3 < 65536
instance (g : GateInfo) : Decidable (abiWidths g) := inferInstanceAs (Decidable (_ ∧ _))

def locationValid (c : Config) (row total : Nat) (g : GateInfo) : Prop :=
  g.gateRowIndex = row ∧ g.selectorIndex < c.numSelectors ∧
  g.groupStart < g.groupEnd ∧ g.groupEnd ≤ total ∧
  g.groupStart ≤ row ∧ row < g.groupEnd
instance (c : Config) (row total : Nat) (g : GateInfo) : Decidable (locationValid c row total g) :=
  inferInstanceAs (Decidable (_ ∧ _))

def filterDegree (c : Config) (g : GateInfo) : Nat :=
  g.groupEnd - g.groupStart - 1 + if 1 < c.numSelectors then 1 else 0

def validateGate (c : Config) (row total : Nat) (g : GateInfo) : Option Requirements := do
  if ¬abiWidths g ∨ ¬locationValid c row total g ∨ 14 ≤ g.gateId then none else do
    let r ← requirements g
    if g.numConstraints = r.constraints ∧ r.wires ≤ c.numWires ∧
        r.localConstants ≤ c.numConstants - c.numSelectors ∧
        r.degree + filterDegree c g ≤ c.quotientDegree + 1 then some r else none

theorem validate_gate_success (c : Config) (row total : Nat) (g : GateInfo) (r : Requirements)
    (h : validateGate c row total g = some r) :
    abiWidths g ∧ locationValid c row total g ∧ g.gateId < 14 ∧
      requirements g = some r ∧ g.numConstraints = r.constraints ∧
      r.wires ≤ c.numWires ∧ r.localConstants ≤ c.numConstants - c.numSelectors ∧
      r.degree + filterDegree c g ≤ c.quotientDegree + 1 := by
  unfold validateGate at h
  split at h
  · simp at h
  · rename_i hb
    simp only [not_or, Decidable.not_not] at hb
    cases hr : requirements g with
    | none => simp [hr] at h
    | some req =>
      simp only [Option.bind_eq_bind, hr, Option.bind] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst req
        exact ⟨hb.1, hb.2.1, by omega, rfl, hc⟩
      · simp at h

theorem unknown_gate_rejected_before_filter (c : Config) (row total : Nat) (g : GateInfo)
    (h : 14 ≤ g.gateId) : validateGate c row total g = none := by simp [validateGate, h]

def envelope (c : Config) (total : Nat) : Prop :=
  c.numWires ≤ 160 ∧ c.numConstants ≤ 160 ∧ c.numGateConstraints ≤ 123 ∧
  0 < c.numSelectors ∧ c.numSelectors ≤ c.numConstants ∧ 0 < total ∧ total ≤ 255 ∧
  c.numSelectors ≤ total ∧ 0 < c.quotientDegree ∧ c.quotientDegree ≤ 8
instance (c : Config) (total : Nat) : Decidable (envelope c total) := inferInstanceAs (Decidable (_ ∧ _))

def validateRows (c : Config) (total : Nat) : Nat → List GateInfo → Option Nat
  | _, [] => some 0
  | row, g :: gs => do
    let r ← validateGate c row total g
    let rest ← validateRows c total (row + 1) gs
    pure (max r.constraints rest)

def validateConfiguration (c : Config) (gates : List GateInfo) : Option Unit := do
  if ¬envelope c gates.length then none else do
    let exactMaximum ← validateRows c gates.length 0 gates
    if exactMaximum = c.numGateConstraints then some () else none

theorem validate_configuration_success (c : Config) (gates : List GateInfo)
    (h : validateConfiguration c gates = some ()) :
    envelope c gates.length ∧ validateRows c gates.length 0 gates = some c.numGateConstraints := by
  unfold validateConfiguration at h
  split at h
  · simp at h
  · rename_i he
    cases hr : validateRows c gates.length 0 gates with
    | none => simp [hr] at h
    | some maximum =>
      simp only [Option.bind_eq_bind, hr, Option.bind] at h
      split at h
      · rename_i hm
        exact ⟨Decidable.of_not_not he, by simp [hm]⟩
      · simp at h

theorem validated_rows_have_bounded_requirements (c : Config) (total row maximum : Nat)
    (gs : List GateInfo) (h : validateRows c total row gs = some maximum) :
    ∀ i g, gs.get? i = some g → ∃ r, validateGate c (row + i) total g = some r ∧ r.constraints ≤ maximum := by
  induction gs generalizing row maximum with
  | nil => intro i g hg; simp at hg
  | cons g gs ih =>
    unfold validateRows at h
    cases hr : validateGate c row total g with
    | none => simp [hr] at h
    | some req =>
      cases hs : validateRows c total (row + 1) gs with
      | none => simp [hr, hs] at h
      | some rest =>
        simp [hr, hs] at h
        subst maximum
        intro i other hg
        cases i with
        | zero => simp at hg; subst other; exact ⟨req, by simpa using hr, Nat.le_max_left _ _⟩
        | succ i =>
          simp only [List.get?_cons_succ] at hg
          rcases ih (row + 1) rest hs i other hg with ⟨r, hv, hb⟩
          refine ⟨r, ?_, Nat.le_trans hb (Nat.le_max_right _ _)⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv

theorem every_configured_gate_checked (c : Config) (gs : List GateInfo)
    (h : validateConfiguration c gs = some ()) (i : Nat) (g : GateInfo) (hg : gs.get? i = some g) :
    ∃ r, validateGate c i gs.length g = some r ∧ r.constraints ≤ c.numGateConstraints := by
  have hc := validate_configuration_success c gs h
  simpa using validated_rows_have_bounded_requirements c gs.length 0 c.numGateConstraints gs hc.2 i g hg

theorem validated_rows_exact_maximum (c : Config) (total row maximum : Nat) (gs : List GateInfo)
    (h : validateRows c total row gs = some maximum) :
    maximum = (gs.map GateInfo.numConstraints).foldr max 0 := by
  induction gs generalizing row maximum with
  | nil => simp [validateRows] at h; simpa using h.symm
  | cons g gs ih =>
    unfold validateRows at h
    cases hr : validateGate c row total g with
    | none => simp [hr] at h
    | some req =>
      cases hs : validateRows c total (row + 1) gs with
      | none => simp [hr, hs] at h
      | some rest =>
        simp [hr, hs] at h
        have hv := validate_gate_success c row total g req hr
        have he := ih (row + 1) rest hs
        simp only [List.map_cons, List.foldr_cons]
        rw [← he, hv.2.2.2.2.1]
        exact h.symm

theorem configuration_declares_exact_maximum (c : Config) (gs : List GateInfo)
    (h : validateConfiguration c gs = some ()) :
    c.numGateConstraints = (gs.map GateInfo.numConstraints).foldr max 0 :=
  validated_rows_exact_maximum c gs.length 0 c.numGateConstraints gs
    (validate_configuration_success c gs h).2

/-- Separate Rust common-data admission guard; Solidity has no lookup argument. -/
def rustAdmission (lookupTableCount : Nat) (c : Config) (gates : List GateInfo) : Option Unit :=
  if lookupTableCount = 0 then validateConfiguration c gates else none

theorem lookup_tables_rejected (count : Nat) (c : Config) (gates : List GateInfo) (h : 0 < count) :
    rustAdmission count c gates = none := by simp [rustAdmission, show count ≠ 0 by omega]

def embed (n : Nat) : Ext3 := ⟨Arithmetic.fromBase n, Arithmetic.fromBase_canonical n⟩
def one : Ext3 := embed 1

theorem zero_mul (a : Ext3) : mul zero a = zero := by
  apply Subtype.eq
  exact Arithmetic.zero_emul a.val

theorem mul_zero (a : Ext3) : mul a zero = zero := by
  apply Subtype.eq
  exact Arithmetic.emul_zero a.val

theorem add_zero (a : Ext3) : add a zero = a := by
  apply Subtype.eq
  exact (Arithmetic.eadd_zero a.val).trans (Arithmetic.normalize_fixed a.property)

theorem zero_add (a : Ext3) : add zero a = a := by
  apply Subtype.eq
  rcases a with ⟨⟨a, b, c⟩, ha, hb, hc⟩
  simp [add, zero, Arithmetic.eadd, Arithmetic.zero, Arithmetic.add,
    Arithmetic.reduce, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]

theorem scalar_sub_zero_iff (a b : Nat) (ha : a < Arithmetic.modulus) (hb : b < Arithmetic.modulus) :
    Arithmetic.sub a b = 0 ↔ a = b := by
  unfold Arithmetic.sub Arithmetic.reduce
  rw [Nat.mod_eq_of_lt hb]
  unfold Arithmetic.modulus at *
  omega

theorem sub_zero_iff (a b : Ext3) : sub a b = zero ↔ a = b := by
  constructor
  · intro h
    apply Subtype.eq
    have he := congrArg Subtype.val h
    have h0 := congrArg Arithmetic.Ext3.c0 he
    have h1 := congrArg Arithmetic.Ext3.c1 he
    have h2 := congrArg Arithmetic.Ext3.c2 he
    have e0 := (scalar_sub_zero_iff a.val.c0 b.val.c0 a.property.1 b.property.1).mp h0
    have e1 := (scalar_sub_zero_iff a.val.c1 b.val.c1 a.property.2.1 b.property.2.1).mp h1
    have e2 := (scalar_sub_zero_iff a.val.c2 b.val.c2 a.property.2.2 b.property.2.2).mp h2
    cases ha : a.val; cases hb : b.val
    simp [ha, hb] at e0 e1 e2
    simp_all
  · intro h
    subst b
    apply Subtype.eq
    have h0 := (scalar_sub_zero_iff a.val.c0 a.val.c0 a.property.1 a.property.1).mpr rfl
    have h1 := (scalar_sub_zero_iff a.val.c1 a.val.c1 a.property.2.1 a.property.2.1).mpr rfl
    have h2 := (scalar_sub_zero_iff a.val.c2 a.val.c2 a.property.2.2 a.property.2.2).mpr rfl
    simp only [sub, zero, Arithmetic.esub, Arithmetic.zero, h0, h1, h2]

theorem sub_self (a : Ext3) : sub a a = zero := (sub_zero_iff a a).mpr rfl

def horner (terms : List Ext3) (alpha : Ext3) : Ext3 :=
  terms.reverse.foldl (fun acc term => add (mul acc alpha) term) zero

theorem horner_cons (term : Ext3) (terms : List Ext3) (alpha : Ext3) :
    horner (term :: terms) alpha = add (mul (horner terms alpha) alpha) term := by
  simp [horner, List.reverse_cons, List.foldl_append]

theorem horner_all_zero (terms : List Ext3) (alpha : Ext3)
    (h : ∀ x ∈ terms, x = zero) : horner terms alpha = zero := by
  induction terms with
  | nil => rfl
  | cons x xs ih =>
    rw [horner_cons, ih (by intro y hy; exact h y (by simp [hy]))]
    rw [h x (by simp), zero_mul, add_zero]

def productFactors (factors : List Ext3) (initial : Ext3) : Ext3 := factors.foldl mul initial

theorem zero_product_absorbing (factors : List Ext3) : productFactors factors zero = zero := by
  induction factors with
  | nil => rfl
  | cons x xs ih => simp only [productFactors, List.foldl_cons, zero_mul] at *; exact ih

theorem product_with_zero_factor (factors : List Ext3) (initial : Ext3)
    (h : zero ∈ factors) : productFactors factors initial = zero := by
  induction factors generalizing initial with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst x
      simpa [productFactors, mul_zero] using zero_product_absorbing xs
    · exact ih (mul initial x) h

def selectorFactors (g : GateInfo) (selector : Ext3) (manySelectors : Bool) : List Ext3 :=
  (((List.range (g.groupEnd - g.groupStart)).map (fun i => g.groupStart + i)).filter
    (fun other => decide (other ≠ g.gateRowIndex))).map (fun other => sub (embed other) selector) ++
    if manySelectors then [sub (embed 4294967295) selector] else []

theorem range_loop_append (n : Nat) (xs ys : List Nat) :
    List.range.loop n (xs ++ ys) = List.range.loop n xs ++ ys := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simpa only [List.range.loop, List.cons_append] using ih (n :: xs)

theorem range_successor (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  simpa only [List.range, List.range.loop, List.nil_append] using range_loop_append n [] [n]

theorem range_membership (n i : Nat) : i ∈ List.range n ↔ i < n := by
  induction n with
  | zero => simp
  | succ n ih => simp [range_successor, ih]; omega

def computeFilter (g : GateInfo) (selector : Ext3) (manySelectors : Bool) : Ext3 :=
  productFactors (selectorFactors g selector manySelectors) one

theorem unused_selector_zero_filter (g : GateInfo) : computeFilter g (embed 4294967295) true = zero := by
  apply product_with_zero_factor
  simp [selectorFactors, sub_self]

theorem other_row_zero_filter (g : GateInfo) (other : Nat) (many : Bool)
    (hstart : g.groupStart ≤ other) (hend : other < g.groupEnd) (hrow : other ≠ g.gateRowIndex) :
    computeFilter g (embed other) many = zero := by
  apply product_with_zero_factor
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨other, ?_, sub_self _⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa using hrow⟩
  apply List.mem_map.mpr
  refine ⟨other - g.groupStart, ?_, by omega⟩
  exact (range_membership _ _).mpr (by omega)

def readValue (values : List Ext3) (i : Nat) : Ext3 := values.getD i zero

def evalConstant (wires constants : List Ext3) (offset count : Nat) : List Ext3 :=
  (List.range count).map fun i => sub (readValue constants (offset + i)) (readValue wires i)

def evalPublicInput (wires : List Ext3) (publicHash : Nat → Base) : List Ext3 :=
  (List.range 4).map fun i => sub (readValue wires i) (embed (publicHash i).val)

def arithmeticExpected (c0 c1 a b addend : Ext3) : Ext3 :=
  add (mul c0 (mul a b)) (mul c1 addend)

def arithmeticConstraint (c0 c1 a b addend output : Ext3) : Ext3 :=
  sub output (arithmeticExpected c0 c1 a b addend)

def evalArithmetic (wires constants : List Ext3) (offset count : Nat) : List Ext3 :=
  (List.range count).map fun i =>
    arithmeticConstraint (readValue constants offset) (readValue constants (offset + 1))
      (readValue wires (4 * i)) (readValue wires (4 * i + 1)) (readValue wires (4 * i + 2)) (readValue wires (4 * i + 3))

structure Ext2 where
  c0 : Ext3
  c1 : Ext3
  deriving DecidableEq

def ext2Mul (a b : Ext2) : Ext2 :=
  ⟨add (mul a.c0 b.c0) (scalar (mul a.c1 b.c1) 7),
   add (mul a.c0 b.c1) (mul a.c1 b.c0)⟩

def readExt2 (wires : List Ext3) (offset : Nat) : Ext2 := ⟨readValue wires offset, readValue wires (offset + 1)⟩

def arithmeticExtensionExpected (c0 c1 : Ext3) (a b addend : Ext2) : Ext2 :=
  let product := ext2Mul a b
  ⟨add (mul product.c0 c0) (mul addend.c0 c1),
   add (mul product.c1 c0) (mul addend.c1 c1)⟩

def mulExtensionExpected (c0 : Ext3) (a b : Ext2) : Ext2 :=
  let product := ext2Mul a b
  ⟨mul product.c0 c0, mul product.c1 c0⟩

def ext2Constraints (expected output : Ext2) : List Ext3 :=
  [sub output.c0 expected.c0, sub output.c1 expected.c1]

def evalArithmeticExtension (wires constants : List Ext3) (offset count : Nat) : List Ext3 :=
  (List.range count).bind fun i =>
    ext2Constraints (arithmeticExtensionExpected (readValue constants offset) (readValue constants (offset + 1))
      (readExt2 wires (8 * i)) (readExt2 wires (8 * i + 2)) (readExt2 wires (8 * i + 4)))
      (readExt2 wires (8 * i + 6))

def evalMulExtension (wires constants : List Ext3) (offset count : Nat) : List Ext3 :=
  (List.range count).bind fun i =>
    ext2Constraints (mulExtensionExpected (readValue constants offset)
      (readExt2 wires (6 * i)) (readExt2 wires (6 * i + 2))) (readExt2 wires (6 * i + 4))

theorem range_length (n : Nat) : (List.range n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [range_successor, ih]

theorem constant_constraints_exact (wires constants : List Ext3) (offset count : Nat) :
    (∀ value ∈ evalConstant wires constants offset count, value = zero) ↔
      ∀ i, i < count → readValue constants (offset + i) = readValue wires i := by
  constructor
  · intro h i hi
    apply (sub_zero_iff _ _).mp
    apply h
    exact List.mem_map.mpr ⟨i, (range_membership _ _).mpr hi, rfl⟩
  · intro h value hv
    rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
    exact (sub_zero_iff _ _).mpr (h i ((range_membership _ _).mp hi))

theorem public_input_constraints_exact (wires : List Ext3) (publicHash : Nat → Base) :
    (∀ value ∈ evalPublicInput wires publicHash, value = zero) ↔
      ∀ i, i < 4 → readValue wires i = embed (publicHash i).val := by
  constructor
  · intro h i hi
    apply (sub_zero_iff _ _).mp
    exact h _ (List.mem_map.mpr ⟨i, (range_membership _ _).mpr hi, rfl⟩)
  · intro h value hv
    rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
    exact (sub_zero_iff _ _).mpr (h i ((range_membership _ _).mp hi))

theorem arithmetic_constraint_exact (c0 c1 a b addend output : Ext3) :
    arithmeticConstraint c0 c1 a b addend output = zero ↔
      output = arithmeticExpected c0 c1 a b addend := sub_zero_iff _ _

theorem arithmetic_constraints_exact (wires constants : List Ext3) (offset count : Nat) :
    (∀ value ∈ evalArithmetic wires constants offset count, value = zero) ↔
      ∀ i, i < count → readValue wires (4 * i + 3) =
        arithmeticExpected (readValue constants offset) (readValue constants (offset + 1))
          (readValue wires (4 * i)) (readValue wires (4 * i + 1)) (readValue wires (4 * i + 2)) := by
  constructor
  · intro h i hi
    apply (arithmetic_constraint_exact _ _ _ _ _ _).mp
    exact h _ (List.mem_map.mpr ⟨i, (range_membership _ _).mpr hi, rfl⟩)
  · intro h value hv
    rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
    exact (arithmetic_constraint_exact _ _ _ _ _ _).mpr (h i ((range_membership _ _).mp hi))

theorem ext2_constraints_exact (expected output : Ext2) :
    (∀ value ∈ ext2Constraints expected output, value = zero) ↔ output = expected := by
  simp only [ext2Constraints, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    sub_zero_iff]
  cases output; cases expected
  simp

theorem concrete_constraint_lengths (wires constants : List Ext3) (publicHash : Nat → Base)
    (offset count : Nat) :
    (evalConstant wires constants offset count).length = count ∧
    (evalPublicInput wires publicHash).length = 4 ∧
    (evalArithmetic wires constants offset count).length = count := by
  simp [evalConstant, evalPublicInput, evalArithmetic, range_length]

theorem bind_pairs_length (xs : List Nat) (f : Nat → List Ext3) (h : ∀ i, (f i).length = 2) :
    (xs.bind f).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [List.bind_cons, h, ih, Nat.mul_add, Nat.add_comm]

theorem extension_constraint_lengths (wires constants : List Ext3) (offset count : Nat) :
    (evalArithmeticExtension wires constants offset count).length = 2 * count ∧
    (evalMulExtension wires constants offset count).length = 2 * count := by
  constructor
  · unfold evalArithmeticExtension
    rw [bind_pairs_length _ _ (by intro i; rfl), range_length]
  · unfold evalMulExtension
    rw [bind_pairs_length _ _ (by intro i; rfl), range_length]

theorem arithmetic_accesses_bounded (c : Config) (row total : Nat) (g : GateInfo) (r : Requirements)
    (h : validateGate c row total g = some r) (hg : g.gateId = 3)
    (hc : c.numSelectors ≤ c.numConstants) (i : Nat) (hi : i < g.numOrConsts) :
    4 * i + 3 < c.numWires ∧ c.numSelectors + 1 < c.numConstants := by
  have hv := validate_gate_success c row total g r h
  have hr := hv.2.2.2.1
  simp only [requirements, hg] at hr
  split at hr
  · simp only [Option.some.injEq] at hr
    subst r
    have hw := hv.2.2.2.2.2.1
    have hk := hv.2.2.2.2.2.2.1
    simp only at hw hk
    omega
  · simp at hr

theorem constant_accesses_bounded (c : Config) (row total : Nat) (g : GateInfo) (r : Requirements)
    (h : validateGate c row total g = some r) (hg : g.gateId = 1)
    (hc : c.numSelectors ≤ c.numConstants) (i : Nat) (hi : i < g.numOrConsts) :
    i < c.numWires ∧ c.numSelectors + i < c.numConstants := by
  have hv := validate_gate_success c row total g r h
  have hr := hv.2.2.2.1
  simp only [requirements, hg] at hr
  split at hr
  · simp only [Option.some.injEq] at hr
    subst r
    have hw := hv.2.2.2.2.2.1
    have hk := hv.2.2.2.2.2.2.1
    simp only at hw hk
    omega
  · simp at hr

theorem public_input_accesses_bounded (c : Config) (row total : Nat) (g : GateInfo) (r : Requirements)
    (h : validateGate c row total g = some r) (hg : g.gateId = 2) (i : Nat) (hi : i < 4) :
    i < c.numWires := by
  have hv := validate_gate_success c row total g r h
  have hr := hv.2.2.2.1
  simp only [requirements, hg] at hr
  split at hr
  · simp only [Option.some.injEq] at hr
    subst r
    have hw := hv.2.2.2.2.2.1
    simp only at hw
    omega
  · simp at hr

theorem arithmetic_extension_accesses_bounded (c : Config) (row total : Nat) (g : GateInfo) (r : Requirements)
    (h : validateGate c row total g = some r) (hg : g.gateId = 6)
    (hc : c.numSelectors ≤ c.numConstants) (i : Nat) (hi : i < g.numOrConsts) :
    8 * i + 7 < c.numWires ∧ c.numSelectors + 1 < c.numConstants := by
  have hv := validate_gate_success c row total g r h
  have hr := hv.2.2.2.1
  simp only [requirements, hg] at hr
  split at hr
  · simp only [Option.some.injEq] at hr
    subst r
    have hw := hv.2.2.2.2.2.1
    have hk := hv.2.2.2.2.2.2.1
    simp only at hw hk
    omega
  · simp at hr

theorem mul_extension_accesses_bounded (c : Config) (row total : Nat) (g : GateInfo) (r : Requirements)
    (h : validateGate c row total g = some r) (hg : g.gateId = 7)
    (hc : c.numSelectors ≤ c.numConstants) (i : Nat) (hi : i < g.numOrConsts) :
    6 * i + 5 < c.numWires ∧ c.numSelectors < c.numConstants := by
  have hv := validate_gate_success c row total g r h
  have hr := hv.2.2.2.1
  simp only [requirements, hg] at hr
  split at hr
  · simp only [Option.some.injEq] at hr
    subst r
    have hw := hv.2.2.2.2.2.1
    have hk := hv.2.2.2.2.2.2.1
    simp only at hw hk
    omega
  · simp at hr

def evaluateUnfiltered (g : GateInfo) (wires constants : List Ext3) (publicHash : Nat → Base)
    (numSelectors : Nat) : Option (List Ext3) :=
  match g.gateId with
  | 0 => some []
  | 1 => some (evalConstant wires constants numSelectors g.numOrConsts)
  | 2 => some (evalPublicInput wires publicHash)
  | 3 => some (evalArithmetic wires constants numSelectors g.numOrConsts)
  | 6 => some (evalArithmeticExtension wires constants numSelectors g.numOrConsts)
  | 7 => some (evalMulExtension wires constants numSelectors g.numOrConsts)
  | _ => none

def contribution (c : Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (alpha : Ext3) : Option Ext3 :=
  let filter := computeFilter g (readValue constants g.selectorIndex) (decide (1 < c.numSelectors))
  if filter = zero then some zero else do
    let terms ← evaluateUnfiltered g wires constants publicHash c.numSelectors
    if terms.length = g.numConstraints then some (mul filter (horner terms alpha)) else none

def combineRows (c : Config) (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3) :
    List GateInfo → Ext3 → Option Ext3
  | [], accumulated => some accumulated
  | g :: gs, accumulated => do
    let term ← contribution c g wires constants publicHash alpha
    combineRows c wires constants publicHash alpha gs (add accumulated term)

/-- Partial executable evaluator. Valid but unimplemented ACTIVE gate families
    return none. All configuration rows are checked before any zero-filter skip. -/
def evalCombined (c : Config) (gates : List GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (alpha : Ext3) : Option Ext3 := do
  if wires.length ≠ c.numWires ∨ constants.length ≠ c.numConstants then none else do
    let _ ← validateConfiguration c gates
    combineRows c wires constants publicHash alpha gates zero

theorem inactive_contribution_zero (c : Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (alpha : Ext3)
    (h : computeFilter g (readValue constants g.selectorIndex) (decide (1 < c.numSelectors)) = zero) :
    contribution c g wires constants publicHash alpha = some zero := by simp [contribution, h]

theorem satisfied_contribution_zero (c : Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (alpha : Ext3) (terms : List Ext3)
    (he : evaluateUnfiltered g wires constants publicHash c.numSelectors = some terms)
    (hl : terms.length = g.numConstraints) (hz : ∀ x ∈ terms, x = zero) :
    contribution c g wires constants publicHash alpha = some zero := by
  unfold contribution
  dsimp only
  split
  · rfl
  · simp [he, hl, horner_all_zero terms alpha hz, mul_zero]

theorem all_satisfied_combination_zero (c : Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3)
    (h : ∀ g ∈ gates, contribution c g wires constants publicHash alpha = some zero) :
    combineRows c wires constants publicHash alpha gates zero = some zero := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [combineRows, h g (by simp)]
    simpa [add_zero] using ih (by intro x hx; exact h x (by simp [hx]))

theorem combined_success_requires_all_configuration (c : Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha result : Ext3)
    (h : evalCombined c gates wires constants publicHash alpha = some result) :
    wires.length = c.numWires ∧ constants.length = c.numConstants ∧ validateConfiguration c gates = some () := by
  unfold evalCombined at h
  split at h
  · simp at h
  · rename_i hs
    cases hv : validateConfiguration c gates with
    | none => simp [hv] at h
    | some resultUnit =>
      cases resultUnit
      exact ⟨by omega, by omega, rfl⟩

theorem unknown_gate_rejected_even_when_inactive (c : Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3)
    (i : Nat) (g : GateInfo) (hg : gates.get? i = some g) (hu : 14 ≤ g.gateId) :
    evalCombined c gates wires constants publicHash alpha = none := by
  cases hr : evalCombined c gates wires constants publicHash alpha with
  | none => rfl
  | some result =>
    have hc := (combined_success_requires_all_configuration c gates wires constants publicHash alpha result hr).2.2
    rcases every_configured_gate_checked c gates hc i g hg with ⟨req, hv, _⟩
    have hknown := (validate_gate_success c i gates.length g req hv).2.2.1
    omega

theorem horner_zero_challenge (terms : List Ext3) : horner terms zero = terms.headD zero := by
  cases terms with
  | nil => rfl
  | cons x xs => simp [horner_cons, mul_zero, zero_add]

theorem horner_two_terms (a b alpha : Ext3) : horner [a, b] alpha = add (mul b alpha) a := by
  simp [horner_cons, horner, zero_mul, zero_add]

/-- Ordinary nonvacuity witnesses for every family's CONFIGURATION grammar.
    These do not claim all corresponding evaluators are implemented in Lean. -/
def representativeGates : List GateInfo :=
  [⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 2, 2, 0, 0⟩,
   ⟨2, 0, 0, 1, 0, 4, 0, 0, 0⟩, ⟨3, 0, 0, 1, 0, 1, 1, 0, 0⟩,
   ⟨4, 0, 0, 1, 0, 123, 0, 0, 0⟩, ⟨5, 0, 0, 1, 0, 24, 0, 0, 0⟩,
   ⟨6, 0, 0, 1, 0, 2, 1, 0, 0⟩, ⟨7, 0, 0, 1, 0, 2, 1, 0, 0⟩,
   ⟨8, 0, 0, 1, 0, 2, 1, 0, 0⟩, ⟨9, 0, 0, 1, 0, 3, 2, 2, 0⟩,
   ⟨10, 0, 0, 1, 0, 2, 1, 0, 0⟩, ⟨11, 0, 0, 1, 0, 2, 1, 0, 0⟩,
   ⟨12, 0, 0, 1, 0, 3, 1, 1, 0⟩, ⟨13, 0, 0, 1, 0, 4, 1, 2, 0⟩]

theorem all_fourteen_families_have_valid_configuration_examples :
    representativeGates.map GateInfo.gateId = List.range 14 ∧
    representativeGates.all (fun g => decide
      (validateConfiguration ⟨1, 3, g.numConstraints, 160, 8⟩ [g] = some ())) = true := by decide

def exampleArithmetic : GateInfo := ⟨3, 0, 0, 1, 0, 1, 1, 0, 0⟩

theorem arithmetic_full_path_positive :
    evalCombined ⟨1, 3, 1, 4, 2⟩ [exampleArithmetic]
      [embed 5, embed 7, embed 11, embed 103]
      [embed 0, embed 2, embed 3] (fun _ => base 0) (embed 9) = some zero := by decide

theorem quadratic_extension_nonresidue_seven_positive :
    ext2Mul ⟨embed 2, embed 3⟩ ⟨embed 5, embed 7⟩ = ⟨embed 157, embed 29⟩ := by decide

def extensionGenerator : Ext3 := ⟨⟨0, 1, 0⟩, ⟨by decide, by decide, by decide⟩⟩
def extensionGeneratorSquared : Ext3 := ⟨⟨0, 0, 1⟩, ⟨by decide, by decide, by decide⟩⟩

theorem arithmetic_preserves_nonbase_extension_information :
    arithmeticConstraint one zero extensionGenerator extensionGenerator zero
      extensionGeneratorSquared = zero := by decide

end Audit.Wire3.Gates
