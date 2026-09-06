import Audit.Wire3.GatePolynomial

/-!
# Literal polynomial bridges for the six basic actual gate families

Sources: Gates.lean evalConstant/evalPublicInput/evalArithmetic/
evalArithmeticExtension/evalMulExtension and the matching concrete Rust/Solidity
functions. IDs 0,1,2,3,6,7 only; other polynomial families are not assigned an
empty successful evaluator. All actual checked families' zero-filter branch
erasure is separate in Audit.Wire3.GatePolynomial.

Both wire and local constant columns have degree at most one in the chosen
row-round variable. Public hash, aggregation alpha, metadata and literal 7 are
fixed. Actual affine columns satisfy the degree premises by construction.
The exact evaluation lemmas use the original concrete Ext3/Ext2 operations.
This does not assert gate truth, witness existence, committed-column provenance,
source/compiler refinement, or outer transcript/PCS soundness.
-/
namespace Audit.Wire3.GateBasicPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial
open Polynomial

noncomputable def constantPolys (wires constants : List P) (offset count : Nat) : List P :=
  (List.range count).map fun i : Nat => readPoly constants (offset+i)-readPoly wires i

noncomputable def publicInputPolys (wires : List P) (hash : Nat → Verifier.Base) : List P :=
  (List.range 4).map fun i : Nat => readPoly wires i-C ((hash i).val : Element)

noncomputable def arithmeticPoly (c0 c1 a b addend output : P) : P :=
  output-(c0*(a*b)+c1*addend)

noncomputable def arithmeticPolys (wires constants : List P) (offset count : Nat) : List P :=
  (List.range count).map fun i : Nat =>
    arithmeticPoly (readPoly constants offset) (readPoly constants (offset+1))
      (readPoly wires (4*i)) (readPoly wires (4*i+1)) (readPoly wires (4*i+2)) (readPoly wires (4*i+3))

theorem constant_evaluation_exact (wires constants : List P) (offset count : Nat) (x : Element) :
    columnValues (constantPolys wires constants offset count) x =
      Gates.evalConstant (columnValues wires x) (columnValues constants x) offset count := by
  simp only [columnValues, constantPolys, Gates.evalConstant, List.map_map,
    Function.comp_def, value_sub, read_poly_is_actual_read]

theorem public_input_evaluation_exact (wires : List P) (hash : Nat → Verifier.Base) (x : Element) :
    columnValues (publicInputPolys wires hash) x = Gates.evalPublicInput (columnValues wires x) hash := by
  simp only [columnValues, publicInputPolys, Gates.evalPublicInput, List.map_map,
    Function.comp_def, value_sub, read_poly_is_actual_read, value_nat_constant]

theorem arithmetic_evaluation_exact (c0 c1 a b addend output : P) (x : Element) :
    value (arithmeticPoly c0 c1 a b addend output) x =
      Gates.arithmeticConstraint (value c0 x) (value c1 x) (value a x)
        (value b x) (value addend x) (value output x) := by
  simp only [arithmeticPoly, Gates.arithmeticConstraint, Gates.arithmeticExpected, value_sub, value_add, value_mul]

theorem arithmetic_list_evaluation_exact (wires constants : List P) (offset count : Nat) (x : Element) :
    columnValues (arithmeticPolys wires constants offset count) x =
      Gates.evalArithmetic (columnValues wires x) (columnValues constants x) offset count := by
  simp only [columnValues, arithmeticPolys, Gates.evalArithmetic, List.map_map,
    Function.comp_def, arithmetic_evaluation_exact, read_poly_is_actual_read]

theorem constant_degree (wires constants : List P) (offset count : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ constantPolys wires constants offset count, p.natDegree ≤ 1 := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact sub_degree_bound _ _ 1 1 (read_poly_degree constants 1 _ hc) (read_poly_degree wires 1 _ hw)

theorem public_input_degree (wires : List P) (hash : Nat → Verifier.Base)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ publicInputPolys wires hash, p.natDegree ≤ 1 := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact sub_degree_bound _ _ 1 0 (read_poly_degree wires 1 _ hw) (by simp)

theorem arithmetic_degree (c0 c1 a b addend output : P)
    (hc0 : c0.natDegree ≤ 1) (hc1 : c1.natDegree ≤ 1)
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1)
    (hadd : addend.natDegree ≤ 1) (hout : output.natDegree ≤ 1) :
    (arithmeticPoly c0 c1 a b addend output).natDegree ≤ 3 := by
  have hab := mul_degree_bound a b 1 1 ha hb
  have hm := mul_degree_bound c0 (a*b) 1 2 hc0 hab
  have had := mul_degree_bound c1 addend 1 1 hc1 hadd
  have hs := add_degree_bound _ _ 3 2 hm had
  exact sub_degree_bound _ _ 1 3 hout hs

theorem arithmetic_list_degree (wires constants : List P) (offset count : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ arithmeticPolys wires constants offset count, p.natDegree ≤ 3 := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact arithmetic_degree _ _ _ _ _ _ (read_poly_degree constants 1 _ hc)
    (read_poly_degree constants 1 _ hc) (read_poly_degree wires 1 _ hw)
    (read_poly_degree wires 1 _ hw) (read_poly_degree wires 1 _ hw) (read_poly_degree wires 1 _ hw)

structure PairPoly where
  c0 : P
  c1 : P

def pairValue (pair : PairPoly) (x : Element) : Gates.Ext2 := ⟨value pair.c0 x,value pair.c1 x⟩
noncomputable def pairRead (wires : List P) (offset : Nat) : PairPoly :=
  ⟨readPoly wires offset,readPoly wires (offset+1)⟩
noncomputable def mulSeven (p : P) : P := p*C (7 : Element)
noncomputable def pairMul (a b : PairPoly) : PairPoly :=
  ⟨a.c0*b.c0+mulSeven (a.c1*b.c1),a.c0*b.c1+a.c1*b.c0⟩
noncomputable def arithmeticPair (c0 c1 : P) (a b addend : PairPoly) : PairPoly :=
  let product := pairMul a b
  ⟨product.c0*c0+addend.c0*c1,product.c1*c0+addend.c1*c1⟩
noncomputable def multiplicationPair (c0 : P) (a b : PairPoly) : PairPoly :=
  let product := pairMul a b
  ⟨product.c0*c0,product.c1*c0⟩
noncomputable def pairConstraints (expected output : PairPoly) : List P :=
  [output.c0-expected.c0,output.c1-expected.c1]

theorem pair_read_exact (wires : List P) (offset : Nat) (x : Element) :
    pairValue (pairRead wires offset) x = Gates.readExt2 (columnValues wires x) offset := by
  simp only [pairValue,pairRead,Gates.readExt2,read_poly_is_actual_read]

theorem mul_seven_exact (p : P) (x : Element) : value (mulSeven p) x = Verifier.scalar (value p x) 7 :=
  value_scalar p 7 x

theorem pair_mul_exact (a b : PairPoly) (x : Element) :
    pairValue (pairMul a b) x = Gates.ext2Mul (pairValue a x) (pairValue b x) := by
  simp only [pairValue,pairMul,Gates.ext2Mul,value_add,mul_seven_exact,value_mul]

theorem arithmetic_pair_exact (c0 c1 : P) (a b addend : PairPoly) (x : Element) :
    pairValue (arithmeticPair c0 c1 a b addend) x =
      Gates.arithmeticExtensionExpected (value c0 x) (value c1 x)
        (pairValue a x) (pairValue b x) (pairValue addend x) := by
  have he := pair_mul_exact a b x
  have h0 := congrArg Gates.Ext2.c0 he
  have h1 := congrArg Gates.Ext2.c1 he
  simp only [arithmeticPair,pairValue,value_add,value_mul] at h0 h1 ⊢
  simp only [Gates.arithmeticExtensionExpected,h0,h1]

theorem multiplication_pair_exact (c0 : P) (a b : PairPoly) (x : Element) :
    pairValue (multiplicationPair c0 a b) x =
      Gates.mulExtensionExpected (value c0 x) (pairValue a x) (pairValue b x) := by
  have he := pair_mul_exact a b x
  have h0 := congrArg Gates.Ext2.c0 he
  have h1 := congrArg Gates.Ext2.c1 he
  simp only [multiplicationPair,pairValue,value_mul] at h0 h1 ⊢
  simp only [Gates.mulExtensionExpected,h0,h1]

theorem pair_constraints_exact (expected output : PairPoly) (x : Element) :
    columnValues (pairConstraints expected output) x =
      Gates.ext2Constraints (pairValue expected x) (pairValue output x) := by
  simp only [columnValues,pairConstraints,Gates.ext2Constraints,pairValue,List.map_cons,List.map_nil,value_sub]

noncomputable def arithmeticExtensionPolys (wires constants : List P) (offset count : Nat) : List P :=
  (List.range count).bind fun i : Nat => pairConstraints
    (arithmeticPair (readPoly constants offset) (readPoly constants (offset+1))
      (pairRead wires (8*i)) (pairRead wires (8*i+2)) (pairRead wires (8*i+4))) (pairRead wires (8*i+6))

noncomputable def multiplicationExtensionPolys (wires constants : List P) (offset count : Nat) : List P :=
  (List.range count).bind fun i : Nat => pairConstraints
    (multiplicationPair (readPoly constants offset) (pairRead wires (6*i)) (pairRead wires (6*i+2)))
      (pairRead wires (6*i+4))

theorem arithmetic_extension_evaluation_exact (wires constants : List P) (offset count : Nat) (x : Element) :
    columnValues (arithmeticExtensionPolys wires constants offset count) x =
      Gates.evalArithmeticExtension (columnValues wires x) (columnValues constants x) offset count := by
  simp only [arithmeticExtensionPolys,Gates.evalArithmeticExtension,columnValues,List.map_bind]
  congr 1
  funext i
  exact (pair_constraints_exact _ _ x).trans (by
    rw [arithmetic_pair_exact,pair_read_exact,pair_read_exact,pair_read_exact,pair_read_exact,
      read_poly_is_actual_read,read_poly_is_actual_read]
    rfl)

theorem multiplication_extension_evaluation_exact (wires constants : List P) (offset count : Nat) (x : Element) :
    columnValues (multiplicationExtensionPolys wires constants offset count) x =
      Gates.evalMulExtension (columnValues wires x) (columnValues constants x) offset count := by
  simp only [multiplicationExtensionPolys,Gates.evalMulExtension,columnValues,List.map_bind]
  congr 1
  funext i
  exact (pair_constraints_exact _ _ x).trans (by
    rw [multiplication_pair_exact,pair_read_exact,pair_read_exact,pair_read_exact,read_poly_is_actual_read]
    rfl)

def PairBound (p : PairPoly) (bound : Nat) : Prop := p.c0.natDegree ≤ bound ∧ p.c1.natDegree ≤ bound

theorem pair_read_degree (wires : List P) (offset : Nat) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    PairBound (pairRead wires offset) 1 :=
  ⟨read_poly_degree wires 1 _ hw,read_poly_degree wires 1 _ hw⟩

theorem pair_mul_degree (a b : PairPoly) (ha : PairBound a 1) (hb : PairBound b 1) :
    PairBound (pairMul a b) 2 := by
  have h00 := mul_degree_bound a.c0 b.c0 1 1 ha.1 hb.1
  have h11 := mul_degree_bound a.c1 b.c1 1 1 ha.2 hb.2
  have h7 := mul_degree_bound (a.c1*b.c1) (C (7 : Element)) 2 0 h11 (le_of_eq (natDegree_C _))
  exact ⟨add_degree_bound _ _ 2 2 h00 (by simpa using h7),
    add_degree_bound _ _ 2 2 (mul_degree_bound _ _ 1 1 ha.1 hb.2) (mul_degree_bound _ _ 1 1 ha.2 hb.1)⟩

theorem arithmetic_pair_degree (c0 c1 : P) (a b addend : PairPoly)
    (hc0 : c0.natDegree ≤ 1) (hc1 : c1.natDegree ≤ 1)
    (ha : PairBound a 1) (hb : PairBound b 1) (had : PairBound addend 1) :
    PairBound (arithmeticPair c0 c1 a b addend) 3 := by
  have hm := pair_mul_degree a b ha hb
  exact ⟨add_degree_bound _ _ 3 2 (mul_degree_bound _ _ 2 1 hm.1 hc0) (mul_degree_bound _ _ 1 1 had.1 hc1),
    add_degree_bound _ _ 3 2 (mul_degree_bound _ _ 2 1 hm.2 hc0) (mul_degree_bound _ _ 1 1 had.2 hc1)⟩

theorem multiplication_pair_degree (c0 : P) (a b : PairPoly)
    (hc0 : c0.natDegree ≤ 1) (ha : PairBound a 1) (hb : PairBound b 1) :
    PairBound (multiplicationPair c0 a b) 3 := by
  have hm := pair_mul_degree a b ha hb
  exact ⟨mul_degree_bound _ _ 2 1 hm.1 hc0,mul_degree_bound _ _ 2 1 hm.2 hc0⟩

theorem pair_constraints_degree (expected output : PairPoly)
    (he : PairBound expected 3) (ho : PairBound output 1) :
    ∀ p ∈ pairConstraints expected output, p.natDegree ≤ 3 := by
  intro p hp
  simp only [pairConstraints,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact sub_degree_bound _ _ 1 3 ho.1 he.1
  · exact sub_degree_bound _ _ 1 3 ho.2 he.2

theorem arithmetic_extension_degree (wires constants : List P) (offset count : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ arithmeticExtensionPolys wires constants offset count, p.natDegree ≤ 3 := by
  intro p hp
  obtain ⟨i,_,hi⟩ := List.mem_bind.mp hp
  exact pair_constraints_degree _ _
    (arithmetic_pair_degree _ _ _ _ _ (read_poly_degree constants 1 _ hc) (read_poly_degree constants 1 _ hc)
      (pair_read_degree wires _ hw) (pair_read_degree wires _ hw) (pair_read_degree wires _ hw))
    (pair_read_degree wires _ hw) p hi

theorem multiplication_extension_degree (wires constants : List P) (offset count : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ multiplicationExtensionPolys wires constants offset count, p.natDegree ≤ 3 := by
  intro p hp
  obtain ⟨i,_,hi⟩ := List.mem_bind.mp hp
  exact pair_constraints_degree _ _
    (multiplication_pair_degree _ _ _ (read_poly_degree constants 1 _ hc)
      (pair_read_degree wires _ hw) (pair_read_degree wires _ hw)) (pair_read_degree wires _ hw) p hi

end Audit.Wire3.GateBasicPolynomial
