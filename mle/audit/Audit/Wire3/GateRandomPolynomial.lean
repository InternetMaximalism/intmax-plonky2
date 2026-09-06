import Audit.Wire3.GateLoopPolynomial

/-!
Gate ID 12: concrete adjacent-difference folding and its actual constraint
order. Unlike reducing gates, the scratch values are REALLY recursively
computed: each bit fold can add one degree. No bit Booleanity or selection
truth is assumed to bound the polynomial. All fixed layout arithmetic and
both wire/local-constant columns are retained.
Source: Plonky2GateEvaluatorExt3.sol:804-921; gate_ext3.rs:989-1030.
The exact bridge is to GatesAdditional, not a source/compiler refinement or
proof that supplied affine endpoints belong to authenticated MLE columns.
-/
namespace Audit.Wire3.GateRandomPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Audit.Wire3.GateBasicPolynomial
open Polynomial

theorem list_pair_induction {A : Type} {motive : List A → Prop}
    (nil : motive []) (singleton : ∀ a, motive [a])
    (cons_cons : ∀ a b rest, motive rest → motive (a::b::rest)) : ∀ xs, motive xs
  | [] => nil
  | [a] => singleton a
  | a::b::rest => cons_cons a b rest (list_pair_induction nil singleton cons_cons rest)

noncomputable def selectionLayerPoly (bit : P) : List P → List P
  | even::odd::rest => (even+bit*(odd-even)) :: selectionLayerPoly bit rest
  | _ => []

noncomputable def selectionLayersPoly : List P → List P → List P
  | [],values => values
  | bit::rest,values => selectionLayersPoly rest (selectionLayerPoly bit values)

noncomputable def selectionPoly (values bits : List P) : P := readPoly (selectionLayersPoly bits values) 0

theorem selection_layer_actual (bit : P) (values : List P) (x : Element) :
    columnValues (selectionLayerPoly bit values) x =
      GatesAdditional.selectionLayer (value bit x) (columnValues values x) := by
  induction values using list_pair_induction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons even odd rest ih =>
      simp only [selectionLayerPoly,columnValues,List.map_cons,value_add,value_mul,value_sub,
        GatesAdditional.selectionLayer] at ih ⊢
      rw [ih]

theorem selection_layers_actual (bits values : List P) (x : Element) :
    columnValues (selectionLayersPoly bits values) x =
      GatesAdditional.selectionLayers (columnValues bits x) (columnValues values x) := by
  induction bits generalizing values with
  | nil => rfl
  | cons bit rest ih =>
      rw [selectionLayersPoly,ih,selection_layer_actual]
      rfl

theorem selection_actual (values bits : List P) (x : Element) :
    value (selectionPoly values bits) x =
      GatesAdditional.selection (columnValues values x) (columnValues bits x) := by
  rw [selectionPoly,read_poly_is_actual_read,selection_layers_actual]
  rfl

theorem selection_layer_degree (bit : P) (values : List P) (bound : Nat)
    (hb : bit.natDegree ≤ 1) (hv : ∀ p ∈ values, p.natDegree ≤ bound) :
    ∀ p ∈ selectionLayerPoly bit values, p.natDegree ≤ bound+1 := by
  induction values using list_pair_induction with
  | nil => simp [selectionLayerPoly]
  | singleton a => simp [selectionLayerPoly]
  | cons_cons even odd rest ih =>
      have he := hv even (by simp)
      have ho := hv odd (by simp)
      have hr := ih (fun p hp => hv p (by simp [hp]))
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        have hm := mul_degree_bound bit (odd-even) 1 bound hb
          (by simpa only [max_self] using sub_degree_bound _ _ bound bound ho he)
        have ha := add_degree_bound even _ bound (1+bound) he hm
        exact ha.trans (by omega)
      · exact hr p hp

theorem selection_layers_degree (bits values : List P) (bound : Nat)
    (hb : ∀ p ∈ bits, p.natDegree ≤ 1) (hv : ∀ p ∈ values, p.natDegree ≤ bound) :
    ∀ p ∈ selectionLayersPoly bits values, p.natDegree ≤ bound+bits.length := by
  induction bits generalizing values bound with
  | nil => simpa only [selectionLayersPoly,List.length_nil,Nat.add_zero] using hv
  | cons bit rest ih =>
      have hl := selection_layer_degree bit values bound (hb bit (by simp)) hv
      have hr := ih (selectionLayerPoly bit values) (bound+1) (fun p hp => hb p (by simp [hp])) hl
      simpa only [selectionLayersPoly,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hr

theorem selection_degree (values bits : List P) (bound : Nat)
    (hb : ∀ p ∈ bits, p.natDegree ≤ 1) (hv : ∀ p ∈ values, p.natDegree ≤ bound) :
    (selectionPoly values bits).natDegree ≤ bound+bits.length :=
  read_poly_degree _ _ 0 (selection_layers_degree bits values bound hb hv)

noncomputable def reconstructedFold (bits : List P) (initial : P) : P :=
  bits.foldl (fun acc bit => (acc+acc)+bit) initial

noncomputable def reconstructedPoly (bits : List P) : P := reconstructedFold bits.reverse 0

theorem reconstructed_fold_actual (bits : List P) (initial : P) (x : Element) :
    value (reconstructedFold bits initial) x =
      (columnValues bits x).foldl (fun acc bit => Verifier.add (Verifier.add acc acc) bit) (value initial x) := by
  induction bits generalizing initial with
  | nil => rfl
  | cons bit rest ih =>
      simpa only [reconstructedFold,columnValues,List.map_cons,List.foldl_cons,value_add] using
        ih ((initial+initial)+bit)

theorem reconstructed_actual (bits : List P) (x : Element) :
    value (reconstructedPoly bits) x = GatesAdditional.randomReconstructedIndex (columnValues bits x) := by
  simp only [reconstructedPoly,reconstructed_fold_actual,value_zero,columnValues,List.map_reverse,
    GatesAdditional.randomReconstructedIndex]

theorem reconstructed_fold_degree (bits : List P) (initial : P)
    (hb : ∀ p ∈ bits, p.natDegree ≤ 1) (hi : initial.natDegree ≤ 1) :
    (reconstructedFold bits initial).natDegree ≤ 1 := by
  induction bits generalizing initial with
  | nil => exact hi
  | cons bit rest ih =>
      have hn := add_degree_bound _ _ 1 1 (add_degree_bound _ _ 1 1 hi hi) (hb bit (by simp))
      exact ih ((initial+initial)+bit) (fun p hp => hb p (by simp [hp])) hn

theorem reconstructed_degree (bits : List P) (hb : ∀ p ∈ bits, p.natDegree ≤ 1) :
    (reconstructedPoly bits).natDegree ≤ 1 :=
  reconstructed_fold_degree bits.reverse 0 (fun p hp => hb p (List.mem_reverse.mp hp)) (by simp)

noncomputable def randomBitsPoly (wires : List P) (bits copies extra copy : Nat) : List P :=
  (List.range bits).map fun b =>
    readPoly wires (GatesAdditional.randomRouted bits copies extra + copy*bits+b)

noncomputable def randomValuesPoly (wires : List P) (bits copy : Nat) : List P :=
  (List.range (GatesAdditional.randomVectorSize bits)).map fun i =>
    readPoly wires (GatesAdditional.randomCopyWidth bits*copy+2+i)

noncomputable def randomCopyPolys (wires : List P) (bits copies extra copy : Nat) : List P :=
  let bs := randomBitsPoly wires bits copies extra copy
  bs.map (fun bit => bit*(bit-1)) ++
    [reconstructedPoly bs-readPoly wires (GatesAdditional.randomCopyWidth bits*copy),
     selectionPoly (randomValuesPoly wires bits copy) bs-readPoly wires (GatesAdditional.randomCopyWidth bits*copy+1)]

noncomputable def randomAccessPolys (wires constants : List P) (offset bits copies extra : Nat) : List P :=
  (List.range copies).bind (fun copy => randomCopyPolys wires bits copies extra copy) ++
    (List.range extra).map (fun i => readPoly constants (offset+i)-
      readPoly wires (GatesAdditional.randomCopyWidth bits*copies+i))

theorem random_bits_actual (wires : List P) (bits copies extra copy : Nat) (x : Element) :
    columnValues (randomBitsPoly wires bits copies extra copy) x =
      GatesAdditional.randomBits (columnValues wires x) bits copies extra copy := by
  simp only [columnValues,randomBitsPoly,GatesAdditional.randomBits,List.map_map,
    Function.comp_def,read_poly_is_actual_read]

theorem random_values_actual (wires : List P) (bits copy : Nat) (x : Element) :
    columnValues (randomValuesPoly wires bits copy) x =
      GatesAdditional.randomValues (columnValues wires x) bits copy := by
  simp only [columnValues,randomValuesPoly,GatesAdditional.randomValues,List.map_map,
    Function.comp_def,read_poly_is_actual_read]

theorem random_copy_actual (wires : List P) (bits copies extra copy : Nat) (x : Element) :
    columnValues (randomCopyPolys wires bits copies extra copy) x =
      GatesAdditional.randomCopyConstraints (columnValues wires x) bits copies extra copy := by
  have map_bits : (randomBitsPoly wires bits copies extra copy).map (fun p => value p x) =
      GatesAdditional.randomBits (columnValues wires x) bits copies extra copy := random_bits_actual _ _ _ _ _ _
  simp only [randomCopyPolys,GatesAdditional.randomCopyConstraints,columnValues,List.map_append,
    List.map_map,List.map_cons,List.map_nil,Function.comp_def,value_mul,value_sub,value_one,
    reconstructed_actual,selection_actual,random_bits_actual,random_values_actual,read_poly_is_actual_read]
  simp only [columnValues] at map_bits
  have map_values := random_values_actual wires bits copy x
  simp only [columnValues] at map_values
  rw [map_bits,map_values,←map_bits,List.map_map]
  rfl

theorem random_access_actual (wires constants : List P) (offset bits copies extra : Nat) (x : Element) :
    columnValues (randomAccessPolys wires constants offset bits copies extra) x =
      GatesAdditional.evalRandomAccess (columnValues wires x) (columnValues constants x) offset bits copies extra := by
  simp only [randomAccessPolys,GatesAdditional.evalRandomAccess,columnValues,List.map_append,List.map_bind,
    List.map_map,Function.comp_def,value_sub,read_poly_is_actual_read]
  have h (copy : Nat) : (randomCopyPolys wires bits copies extra copy).map (fun p => value p x) =
      GatesAdditional.randomCopyConstraints (columnValues wires x) bits copies extra copy := random_copy_actual _ _ _ _ _ _
  simp only [h]
  rfl

theorem random_bits_degree (wires : List P) (bits copies extra copy : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ randomBitsPoly wires bits copies extra copy, p.natDegree ≤ 1 := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact read_poly_degree wires 1 _ hw

theorem random_values_degree (wires : List P) (bits copy : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ randomValuesPoly wires bits copy, p.natDegree ≤ 1 := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact read_poly_degree wires 1 _ hw

theorem random_copy_degree (wires : List P) (bits copies extra copy : Nat)
    (hb : 1 ≤ bits) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ randomCopyPolys wires bits copies extra copy, p.natDegree ≤ bits+1 := by
  have hbits := random_bits_degree wires bits copies extra copy hw
  have hvalues := random_values_degree wires bits copy hw
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp hp
    exact (mul_degree_bound _ _ 1 1 (hbits bit hbit)
      (sub_degree_bound _ _ 1 0 (hbits bit hbit) (by simp))).trans (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact (sub_degree_bound _ _ 1 1 (reconstructed_degree _ hbits)
        (read_poly_degree wires 1 _ hw)).trans (by omega)
    · have hd := selection_degree _ _ 1 hbits hvalues
      simp only [randomBitsPoly,List.length_map,List.length_range] at hd
      exact (sub_degree_bound _ _ (1+bits) 1 hd (read_poly_degree wires 1 _ hw)).trans (by omega)

theorem random_access_degree (wires constants : List P) (offset bits copies extra : Nat)
    (hb : 1 ≤ bits) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ randomAccessPolys wires constants offset bits copies extra, p.natDegree ≤ bits+1 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨copy,_,hcopy⟩ := List.mem_bind.mp hp
    exact random_copy_degree wires bits copies extra copy hb hw p hcopy
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact (sub_degree_bound _ _ 1 1 (read_poly_degree constants 1 _ hc)
      (read_poly_degree wires 1 _ hw)).trans (by omega)

end Audit.Wire3.GateRandomPolynomial
