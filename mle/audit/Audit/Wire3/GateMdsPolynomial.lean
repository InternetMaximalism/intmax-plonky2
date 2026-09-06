import Audit.Wire3.GateBasicPolynomial

/-!
# Standalone Poseidon-MDS gate: actual fixed linear folds

ID 5 only. The actual circulant and diagonal tables, lane/row orientation and
48-wire/24-constraint order are used, not an assumed linear evaluator.
Source: Poseidon.mdsCirculantRow/mdsGeneralRow/evalPoseidonMds;
PoseidonGateExt3.sol:81–139,502–533; gate_ext3.rs:877–894.
This does not prove the nonlinear Poseidon gate degree or hash security.
-/
namespace Audit.Wire3.GateMdsPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial
open Polynomial

noncomputable def weightedSum {A : Type} (indices : List A) (f : A → P) (weight : A → Nat)
    (initial : P) : P := indices.foldl (fun acc i => acc+f i*C (weight i : Element)) initial

theorem weighted_sum_eval {A : Type} (indices : List A) (f : A → P) (weight : A → Nat)
    (initial : P) (x : Element) :
    value (weightedSum indices f weight initial) x = indices.foldl
      (fun acc i => Verifier.add acc (Verifier.scalar (value (f i) x) (weight i))) (value initial x) := by
  induction indices generalizing initial with
  | nil => rfl
  | cons i indices ih =>
      simpa only [weightedSum,List.foldl_cons,value_add,value_scalar] using ih (initial+f i*C (weight i : Element))

theorem weighted_sum_degree {A : Type} (indices : List A) (f : A → P) (weight : A → Nat)
    (initial : P) (hi : initial.natDegree ≤ 1) (hf : ∀ i ∈ indices, (f i).natDegree ≤ 1) :
    (weightedSum indices f weight initial).natDegree ≤ 1 := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
      have hm := mul_degree_bound (f i) (C (weight i : Element)) 1 0
        (hf i (List.mem_cons_self _ _)) (le_of_eq (natDegree_C _))
      have hn := add_degree_bound initial _ 1 1 hi (by simpa only [Nat.add_zero] using hm)
      exact ih _ hn (fun j hj => hf j (List.mem_cons_of_mem _ hj))

noncomputable def mdsCirculantPoly (wires : List P) (lane : Fin 2) (row : Fin 12) : P :=
  weightedSum Poseidon.coordinates
    (fun i => readPoly wires (2*(Poseidon.rotated row i).val+lane.val))
    (fun i => PoseidonConstants.mdsCirc.getD i.val 0) 0

noncomputable def mdsGeneralPoly (wires : List P) (lane : Fin 2) (row : Fin 12) : P :=
  mdsCirculantPoly wires lane row +
    readPoly wires (2*row.val+lane.val)*C ((PoseidonConstants.mdsDiag.getD row.val 0 : Nat) : Element)

theorem mds_circulant_actual_eval (wires : List P) (lane : Fin 2) (row : Fin 12) (x : Element) :
    value (mdsCirculantPoly wires lane row) x =
      Poseidon.mdsCirculantRow (Poseidon.mdsGateInput (columnValues wires x) lane) row := by
  simp only [mdsCirculantPoly,weighted_sum_eval,value_zero,read_poly_is_actual_read,
    Poseidon.mdsCirculantRow,Poseidon.mdsGateInput,Poseidon.at_makeState,Poseidon.wire]

theorem mds_general_actual_eval (wires : List P) (lane : Fin 2) (row : Fin 12) (x : Element) :
    value (mdsGeneralPoly wires lane row) x =
      Poseidon.mdsGeneralRow (Poseidon.mdsGateInput (columnValues wires x) lane) row := by
  simp only [mdsGeneralPoly,value_add,mds_circulant_actual_eval,value_scalar,read_poly_is_actual_read,
    Poseidon.mdsGeneralRow,Poseidon.mdsGateInput,Poseidon.at_makeState,Poseidon.wire]

theorem mds_circulant_degree (wires : List P) (lane : Fin 2) (row : Fin 12)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) : (mdsCirculantPoly wires lane row).natDegree ≤ 1 := by
  apply weighted_sum_degree
  · simp
  · intro i _
    exact read_poly_degree wires 1 _ hw

theorem mds_general_degree (wires : List P) (lane : Fin 2) (row : Fin 12)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) : (mdsGeneralPoly wires lane row).natDegree ≤ 1 := by
  have hm := mul_degree_bound (readPoly wires (2*row.val+lane.val))
    (C ((PoseidonConstants.mdsDiag.getD row.val 0 : Nat) : Element)) 1 0
    (read_poly_degree wires 1 _ hw) (le_of_eq (natDegree_C _))
  exact add_degree_bound _ _ 1 1 (mds_circulant_degree wires lane row hw) (by simpa only [Nat.add_zero] using hm)

noncomputable def mdsPolys (wires : List P) : List P :=
  Poseidon.coordinates.bind fun row =>
    [readPoly wires (2*(12+row.val))-mdsGeneralPoly wires 0 row,
     readPoly wires (2*(12+row.val)+1)-mdsGeneralPoly wires 1 row]

theorem mds_list_actual_eval (wires : List P) (x : Element) :
    columnValues (mdsPolys wires) x = Poseidon.evalPoseidonMds (columnValues wires x) := by
  simp only [mdsPolys,columnValues,List.map_bind,List.map_cons,List.map_nil,value_sub,
    read_poly_is_actual_read,mds_general_actual_eval,Poseidon.evalPoseidonMds,Poseidon.mdsGateExpected,
    Poseidon.wire]

theorem mds_list_degree (wires : List P) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ mdsPolys wires, p.natDegree ≤ 1 := by
  intro p hp
  obtain ⟨row,_,hr⟩ := List.mem_bind.mp hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_degree_bound _ _ 1 1 (read_poly_degree wires 1 _ hw) (mds_general_degree wires 0 row hw)
  · exact sub_degree_bound _ _ 1 1 (read_poly_degree wires 1 _ hw) (mds_general_degree wires 1 row hw)

end Audit.Wire3.GateMdsPolynomial
