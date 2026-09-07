import Audit.Wire3.Connections
import Audit.Wire3.DenseMleIndexed
import Audit.Wire3.OuterAdapter

/-!
# Opened-claim folding: the WHIR expected claim is a full-table evaluation

Source correspondence at becfe98e:
* `mle/contracts/src/PackedClaimExt3.sol` 107-125: cells 0-2 are the folds of
  logPreprocessed / logWitness / logNormInverse at `indexPoints[0]`, cells 3-4
  the folds of gatePreprocessed / gateWitness at `indexPoints[1]`, cell 5 stays
  the canonical zero and the mask is the protocol constant.
* `mle/contracts/src/MleVerifierV2.sol` 350-364 and 686-702: the fold is called
  with capacity `1 << indexBits`, and `_packedPoint(row, index)` hands WHIR the
  complete reversal `reverse(index) ++ reverse(row)`.
* `mle/src/verifier_v2.rs` 48-53 (`packed_ext3_point = row ++ index`,
  `bind_expected` slot `point * NUM_PCS_GROUPS_V2 + group`) and 313-375 (five
  `fold_ext3_claim` calls, mask check, two packed points).
* `mle/src/prover_v2.rs` 47-85 (`pack_mles`/`pack_tables`): the committed group
  table is laid out `packed[column * num_rows + row]`, zero-padded to
  `width.next_power_of_two()` columns. This is the join of the constituent
  columns with the ROW variables in the low bits and the INDEX variables in the
  high bits, i.e. the dense-MLE binding order `row ++ index`.

What is proved here is a DETERMINISTIC IDENTITY between existing executable
models: `Packed.foldLayers`/`Packed.fold` (Solidity `_foldFlat`, Rust
`fold_ext3_claim`), `DenseMleIndexed.bindMany`/`evaluate` (Rust
`sumcheck/ext3.rs` binding) and `Verifier.expectedClaims`/`whirContext`.
Folding a full column-joined table at `row ++ index` equals folding the
per-column row folds at `index`; hence each bound cell of the expected-claim
list IS the dense evaluation of the width-padded group table at the packed
point whose complete reversal is the context's native WHIR point, whenever the
opened cells are the per-column row evaluations. That last relation is an
explicit hypothesis (an honest-prover relation); nothing is claimed when it
fails, and the concrete counter-example at the end shows the identity is
contingent on it. Nothing here says the opened values are true PCS openings,
and no WHIR soundness, binding, or Fiat-Shamir property is asserted or used.
-/
namespace Audit.Wire3.OpenedClaimFold
open Audit.Wire3
open Audit.Wire3.GoldilocksExt3Field (Element)
open Audit.Wire3.DenseMleIndexed (State Valid bindMany evaluate raw)

/-! ## 1. Associativity of the packed fold over an appended point -/

/-- `foldLayers` over an appended point is the composition of the two folds:
the layers of `a` are consumed first, then the layers of `b`. -/
theorem foldLayers_append (a b values : List Arithmetic.Ext3) :
    Packed.foldLayers (a ++ b) values = Packed.foldLayers b (Packed.foldLayers a values) := by
  induction a generalizing values with
  | nil => rfl
  | cons r _ ih => exact ih (Packed.layer r values)

theorem fold_append (values a b : List Arithmetic.Ext3) :
    Packed.fold values (a ++ b) = Packed.fold (Packed.foldLayers a values) b := by
  unfold Packed.fold
  rw [foldLayers_append]

/-- One layer distributes over an append whose left part has even length: the
adjacent even/odd pairing never straddles the boundary. -/
theorem layer_append_even (r : Arithmetic.Ext3) : ∀ (xs ys : List Arithmetic.Ext3),
    xs.length % 2 = 0 → Packed.layer r (xs ++ ys) = Packed.layer r xs ++ Packed.layer r ys
  | [], ys, _ => rfl
  | [_], _, h => by simp at h
  | a :: b :: rest, ys, h => by
      have hr : rest.length % 2 = 0 := by simp only [List.length_cons] at h; omega
      show Arithmetic.butterfly a b r :: Packed.layer r (rest ++ ys) =
        (Arithmetic.butterfly a b r :: Packed.layer r rest) ++ Packed.layer r ys
      rw [layer_append_even r rest ys hr, List.cons_append]

theorem layer_join (r : Arithmetic.Ext3) (cols : List (List Arithmetic.Ext3))
    (h : ∀ c ∈ cols, c.length % 2 = 0) :
    Packed.layer r cols.join = (cols.map (Packed.layer r)).join := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.join_cons, List.map_cons]
      rw [layer_append_even r c cs.join (h c (by simp)), ih (fun d hd => h d (by simp [hd]))]

theorem map_foldLayers_nil (cols : List (List Arithmetic.Ext3)) :
    cols.map (Packed.foldLayers []) = cols :=
  List.map_id'' (fun _ => rfl) cols

/-- Folding the joined columns over the row point folds every column
independently; the results stay in column order. Each column must be a full
table for the row point. -/
theorem foldLayers_join (row : List Arithmetic.Ext3) : ∀ (cols : List (List Arithmetic.Ext3)),
    (∀ c ∈ cols, c.length = 2 ^ row.length) →
    Packed.foldLayers row cols.join = (cols.map (Packed.foldLayers row)).join := by
  induction row with
  | nil => intro cols _; rw [map_foldLayers_nil]; rfl
  | cons r rs ih =>
      intro cols h
      have heven : ∀ c ∈ cols, c.length % 2 = 0 := by
        intro c hc
        rw [h c hc, List.length_cons, Nat.pow_succ]
        simp
      have hnext : ∀ c ∈ cols.map (Packed.layer r), c.length = 2 ^ rs.length := by
        intro c hc
        rcases List.mem_map.mp hc with ⟨d, hd, rfl⟩
        apply Packed.layer_even_shape
        rw [h d hd, List.length_cons, Nat.pow_succ, Nat.mul_comm]
      show Packed.foldLayers rs (Packed.layer r cols.join) = _
      rw [layer_join r cols heven, ih _ hnext, List.map_map]
      rfl

theorem foldLayers_full_singleton (row values : List Arithmetic.Ext3)
    (h : values.length = 2 ^ row.length) :
    Packed.foldLayers row values = [Packed.fold values row] := by
  have hl := Packed.full_table_final_shape row values h
  cases hf : Packed.foldLayers row values with
  | nil => simp [hf] at hl
  | cons x rest =>
      have : rest = [] := by simpa [hf] using hl
      subst this
      simp [Packed.fold, hf]

theorem join_singletons {α β : Type} (f : α → β) (xs : List α) :
    (xs.map (fun x => [f x])).join = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.join_cons, List.singleton_append, ih]

/-- The row-folded values of a column-joined table, in column order. -/
theorem foldLayers_join_row_folds (row : List Arithmetic.Ext3) (cols : List (List Arithmetic.Ext3))
    (h : ∀ c ∈ cols, c.length = 2 ^ row.length) :
    Packed.foldLayers row cols.join = cols.map (fun c => Packed.fold c row) := by
  rw [foldLayers_join row cols h, ← join_singletons (fun c => Packed.fold c row) cols]
  congr 1
  exact List.map_congr_left (fun c hc => foldLayers_full_singleton row c (h c hc))

/-- **packed_split_fold.** Folding the joined column table at `row ++ index`
(the Rust `packed_ext3_point` order, LSB-first) equals folding the per-column
row folds at `index`. This is the exact `Packed.fold` used by
`Connections.packedFold`/`Verifier.expectedClaims`. No shape hypothesis on the
number of columns is needed: the sparse fold zero-extends. -/
theorem packed_split_fold (row index : List Arithmetic.Ext3) (cols : List (List Arithmetic.Ext3))
    (h : ∀ c ∈ cols, c.length = 2 ^ row.length) :
    Packed.fold cols.join (row ++ index) = Packed.fold (cols.map (fun c => Packed.fold c row)) index := by
  rw [fold_append, foldLayers_join_row_folds row cols h]

/-- The same split for the verifier's concrete `FoldClaim` on canonical values. -/
theorem packedFold_split (row index : List Verifier.Ext3) (cols : List (List Verifier.Ext3))
    (width : Nat) (h : ∀ c ∈ cols, c.length = 2 ^ row.length) :
    Connections.packedFold cols.join width (row ++ index) =
      Connections.packedFold (cols.map (fun c => Connections.packedFold c width row)) width index := by
  apply Subtype.eq
  rw [Connections.packedFold_exact, Connections.packedFold_exact, List.map_join, List.map_append,
    List.map_map]
  rw [packed_split_fold (row.map Subtype.val) (index.map Subtype.val) (cols.map (List.map Subtype.val))
    (by
      intro c hc
      rcases List.mem_map.mp hc with ⟨d, hd, rfl⟩
      simp only [List.length_map]
      exact h d hd)]
  rw [List.map_map]
  rfl

/-! ## 2. The same split for the indexed dense-MLE binder -/

theorem bindMany_append (a b : List Element) (s : State) :
    bindMany (a ++ b) s = (bindMany a s).bind (bindMany b) := by
  induction a generalizing s with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.cons_append, bindMany, bind, Option.bind]
      cases DenseMleIndexed.bindVariable s r with
      | none => rfl
      | some t => exact ih t

/-- Evaluating a valid full table at `row ++ index` is: bind the row variables
(which always succeeds and leaves a valid table with `index.length` variables),
then evaluate the result at `index`. -/
theorem evaluate_split (s : State) (row index : List Element) (hv : Valid s)
    (hw : row.length + index.length = s.numVars) :
    ∃ t, bindMany row s = some t ∧ Valid t ∧ t.numVars = index.length ∧
      raw t.evaluations = Packed.foldLayers (raw row) (raw s.evaluations) ∧
      evaluate s (row ++ index) = evaluate t index := by
  obtain ⟨t, ht, hvalid, hcount, hraw⟩ :=
    DenseMleIndexed.all_bindings_execute s row hv (by omega)
  refine ⟨t, ht, hvalid, by omega, hraw, ?_⟩
  have h1 : ¬ ((row ++ index).length ≠ s.numVars) := by
    rw [List.length_append, hw]
    exact fun h => h rfl
  have h2 : ¬ (index.length ≠ t.numVars) := fun h => h (by omega)
  simp only [evaluate, if_neg h1, if_neg h2, bindMany_append, ht, bind, Option.bind]

/-! ## 3. The width-padded constituent group as a dense table -/

/-- Canonical verifier values as field elements (`Element` is a wrapper). -/
def lift (xs : List Verifier.Ext3) : List Element := xs.map Element.mk

theorem raw_lift (xs : List Verifier.Ext3) : raw (lift xs) = xs.map Subtype.val := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x.val) ih

theorem raw_length (xs : List Element) : (raw xs).length = xs.length := List.length_map _ _

theorem raw_append (a b : List Element) : raw (a ++ b) = raw a ++ raw b := List.map_append _ _ _

theorem raw_zero_column (n : Nat) : raw (List.replicate n (0 : Element)) = List.replicate n Arithmetic.zero :=
  List.map_replicate.trans rfl

/-- The per-column row folds: what the honest prover sends as the opened
constituent cells for one group at one row point. -/
def rowOpenings (cols : List (List Element)) (row : List Element) : List Arithmetic.Ext3 :=
  cols.map (fun c => Packed.fold (raw c) (raw row))

/-- Each row opening is the dense-MLE evaluation of its own column at the row
point (`DenseMleIndexed.evaluate` on a full column table). -/
theorem row_opening_is_column_evaluation (col row : List Element) (h : col.length = 2 ^ row.length) :
    ∃ v, evaluate ⟨row.length, col⟩ row = some v ∧ v.toVerifier.val = Packed.fold (raw col) (raw row) :=
  DenseMleIndexed.evaluate_full_table_same_packed_fold ⟨row.length, col⟩ row h rfl

/-- The committed group table of `prover_v2::pack_mles`: the constituent
columns joined in column order, zero columns appended up to `2 ^ indexBits`,
with `rowBits + indexBits` variables (row variables in the low bits). -/
def paddedTable (cols : List (List Element)) (rowBits indexBits : Nat) : State :=
  ⟨rowBits + indexBits,
   (cols ++ List.replicate (2 ^ indexBits - cols.length) (List.replicate (2 ^ rowBits) 0)).join⟩

theorem join_uniform_length {α : Type} (cols : List (List α)) (n : Nat)
    (h : ∀ c ∈ cols, c.length = n) : cols.join.length = cols.length * n := by
  induction cols with
  | nil => simp
  | cons c cs ih =>
      have hc : c.length = n := h c (by simp)
      have hcs := ih (fun d hd => h d (by simp [hd]))
      simp only [List.join_cons, List.length_append, List.length_cons, hc, hcs]
      ring

theorem padded_columns_full (cols : List (List Element)) (rowBits indexBits : Nat)
    (hc : ∀ c ∈ cols, c.length = 2 ^ rowBits) :
    ∀ c ∈ cols ++ List.replicate (2 ^ indexBits - cols.length) (List.replicate (2 ^ rowBits) (0 : Element)),
      c.length = 2 ^ rowBits := by
  intro c hc'
  rcases List.mem_append.mp hc' with h | h
  · exact hc c h
  · rw [List.eq_of_mem_replicate h, List.length_replicate]

/-- The padded table is a valid dense MLE exactly when the group fits its
capacity (`values.len() <= width` in Rust, `width ≤ 2 ^ indexBits` in the envelope). -/
theorem padded_table_valid (cols : List (List Element)) (rowBits indexBits : Nat)
    (hc : ∀ c ∈ cols, c.length = 2 ^ rowBits) (hw : cols.length ≤ 2 ^ indexBits) :
    Valid (paddedTable cols rowBits indexBits) := by
  dsimp only [Valid, paddedTable]
  rw [join_uniform_length _ (2 ^ rowBits) (padded_columns_full cols rowBits indexBits hc),
    List.length_append, List.length_replicate, Nat.pow_add, Nat.mul_comm]
  congr 1
  omega

theorem paddedTable_numVars (cols : List (List Element)) (rowBits indexBits : Nat) :
    (paddedTable cols rowBits indexBits).numVars = rowBits + indexBits := rfl

theorem fold_zero_column (n : Nat) (point : List Arithmetic.Ext3) :
    Packed.fold (List.replicate n Arithmetic.zero) point = Arithmetic.zero := by
  have h := Packed.sparse_fold_equals_zero_padded_fold [] point n
  simpa [Packed.empty_fold] using h

/-- **Full-table evaluation equals the packed fold of the row openings.** The
dense evaluation of the padded group table at `row ++ index` succeeds and its
canonical value is `Packed.fold (rowOpenings cols row) (raw index)`, i.e. the
Solidity/Rust fold of the (unpadded) row openings at the index point. -/
theorem full_table_evaluation_is_fold_of_row_openings (cols : List (List Element))
    (row index : List Element) (hc : ∀ c ∈ cols, c.length = 2 ^ row.length)
    (hw : cols.length ≤ 2 ^ index.length) :
    ∃ result, evaluate (paddedTable cols row.length index.length) (row ++ index) = some result ∧
      result.toVerifier.val = Packed.fold (rowOpenings cols row) (raw index) := by
  obtain ⟨result, he, hval⟩ := DenseMleIndexed.evaluate_full_table_same_packed_fold
    (paddedTable cols row.length index.length) (row ++ index)
    (padded_table_valid cols row.length index.length hc hw)
    (by simp [paddedTable])
  refine ⟨result, he, ?_⟩
  rw [hval, raw_append]
  have hjoin : raw (paddedTable cols row.length index.length).evaluations =
      ((cols ++ List.replicate (2 ^ index.length - cols.length)
        (List.replicate (2 ^ row.length) 0)).map raw).join := by
    show raw (List.join _) = _
    rw [raw, List.map_join]
    rfl
  have hfull : ∀ c ∈ (cols ++ List.replicate (2 ^ index.length - cols.length)
      (List.replicate (2 ^ row.length) (0 : Element))).map raw, c.length = 2 ^ (raw row).length := by
    intro c hc'
    rcases List.mem_map.mp hc' with ⟨d, hd, rfl⟩
    rw [raw_length, raw_length]
    exact padded_columns_full cols row.length index.length hc d hd
  have hz : ((fun c => Packed.fold c (raw row)) ∘ raw) (List.replicate (2 ^ row.length) (0 : Element)) =
      Arithmetic.zero := by
    show Packed.fold (raw (List.replicate _ 0)) (raw row) = _
    rw [raw_zero_column]
    exact fold_zero_column _ _
  rw [hjoin, packed_split_fold (raw row) (raw index) _ hfull, List.map_map, List.map_append,
    List.map_replicate, hz, Packed.sparse_fold_equals_zero_padded_fold]
  rfl

/-! ## 4. The verifier's expected claims -/

/-- Rust `bind_expected` slot arithmetic: `point * NUM_PCS_GROUPS_V2 + group`. -/
def numGroups : Nat := 3
def pointLog : Nat := 0
def pointGate : Nat := 1
def groupPreprocessed : Nat := 0
def groupWitness : Nat := 1
def groupNormInverse : Nat := 2
def rustSlot (point group : Nat) : Nat := point * numGroups + group

/-- The five bound cells in the Solidity `_foldV2UsedCellsUnchecked` order:
opened cells and the index point each is folded at. -/
def boundCell (u : Verifier.UsedClaims) (idx : Verifier.IndexPoints) :
    Fin 5 → List Verifier.Ext3 × List Verifier.Ext3
  | 0 => (u.logPreprocessed, idx.log)
  | 1 => (u.logWitness, idx.log)
  | 2 => (u.logNormInverse, idx.log)
  | 3 => (u.gatePreprocessed, idx.gate)
  | 4 => (u.gateWitness, idx.gate)

/-- Which of the two context points (0 = log, 1 = gate) each bound cell uses. -/
def cellPoint : Fin 5 → Nat
  | 0 => pointLog | 1 => pointLog | 2 => pointLog | 3 => pointGate | 4 => pointGate

/-- The row (sumcheck) point paired with each bound cell. -/
def cellRow (s : Verifier.RoundState) : Fin 5 → List Verifier.Ext3
  | 0 => s.logPoint | 1 => s.logPoint | 2 => s.logPoint | 3 => s.gatePoint | 4 => s.gatePoint

def cellGroup : Fin 5 → Nat
  | 0 => groupPreprocessed | 1 => groupWitness | 2 => groupNormInverse
  | 3 => groupPreprocessed | 4 => groupWitness

/-- Solidity cell position and Rust `bind_expected` slot coincide for all five
bound cells. -/
theorem solidity_cell_is_rust_slot (i : Fin 5) : i.val = rustSlot (cellPoint i) (cellGroup i) := by
  fin_cases i <;> rfl

/-- Every bound cell of `Verifier.expectedClaims` is exactly one fold of the
listed opened cells at the listed index point, for any `FoldClaim`. -/
theorem expected_claim_cell_exact (foldClaim : Verifier.FoldClaim) (c : Verifier.Config)
    (p : Verifier.Proof) (idx : Verifier.IndexPoints) (i : Fin 5) :
    (Verifier.expectedClaims foldClaim c p idx)[i.val]? =
      some (some (foldClaim (boundCell p.used idx i).1 (Verifier.width c) (boundCell p.used idx i).2)) := by
  fin_cases i <;> rfl

theorem context_point_exact (foldClaim : Verifier.FoldClaim) (c : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints) (i : Fin 5) :
    (Verifier.whirContext foldClaim c p s idx).points[cellPoint i]? =
      some (Packed.whirPoint ((cellRow s i).map Subtype.val) ((boundCell p.used idx i).2.map Subtype.val)) := by
  fin_cases i <;> rfl

/-- The native WHIR point handed to the context is the complete reversal of the
packed dense-MLE point `row ++ index`; equivalently `reverse(index) ++ reverse(row)`
(`Packed.whir_point_exact_order`, Solidity `_packedPoint`). -/
theorem native_point_is_reversed_dense_point (row index : List Element) :
    (Packed.whirPoint (raw row) (raw index)).reverse = raw (row ++ index) ∧
    Packed.whirPoint (raw row) (raw index) = (raw index).reverse ++ (raw row).reverse :=
  ⟨by rw [Packed.whir_point_roundtrip, raw_append]; rfl, Packed.whir_point_exact_order _ _⟩

/-- Cell `i` of a WHIR context opens the padded table `cols` at the dense point
`row ++ index`: the context's point `pt` is the complete reversal of that dense
point, the dense evaluation succeeds, and its value IS the expected claim. -/
def CellOpensFullTable (ctx : Verifier.WhirContext) (i pt : Nat) (cols : List (List Element))
    (row index : List Element) : Prop :=
  ∃ result,
    ctx.points[pt]? = some (raw (row ++ index)).reverse ∧
    evaluate (paddedTable cols row.length index.length) (row ++ index) = some result ∧
    ctx.expectedClaims[i]? = some (some result.toVerifier)

/-- **expected_claim_cell_is_full_table_evaluation.** For each of the five
bound cells `i`, with `Connections.packedFold` (the executable Solidity/Rust
fold) as the engine's fold: whenever the opened cells of that group are the
per-column row folds of some constituent columns `cols` (hypothesis `hopen`;
this is the HONEST-PROVER relation between the opened cells and a committed
table, and nothing is concluded without it), cell `i` of `Verifier.whirContext`
is the dense evaluation of the width-padded group table at the packed point
`row ++ index`, and the context's native point for that cell is the complete
reversal of that packed point. The log group uses `idx.log` with `s.logPoint`,
the gate group uses `idx.gate` with `s.gatePoint`, exactly as Solidity cells
0-2 / 3-4 and Rust `POINT_LOG_V2` / `POINT_GATE_V2`. -/
theorem expected_claim_cell_is_full_table_evaluation (c : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints) (i : Fin 5) (cols : List (List Element))
    (hc : ∀ col ∈ cols, col.length = 2 ^ (cellRow s i).length)
    (hw : cols.length ≤ 2 ^ (boundCell p.used idx i).2.length)
    (hopen : (boundCell p.used idx i).1.map Subtype.val = rowOpenings cols (lift (cellRow s i))) :
    CellOpensFullTable (Verifier.whirContext Connections.packedFold c p s idx) i.val (cellPoint i) cols
      (lift (cellRow s i)) (lift (boundCell p.used idx i).2) := by
  have hrow : (lift (cellRow s i)).length = (cellRow s i).length := List.length_map _ _
  have hindex : (lift (boundCell p.used idx i).2).length = (boundCell p.used idx i).2.length :=
    List.length_map _ _
  obtain ⟨result, he, hval⟩ := full_table_evaluation_is_fold_of_row_openings cols
    (lift (cellRow s i)) (lift (boundCell p.used idx i).2) (by rw [hrow]; exact hc) (by rw [hindex]; exact hw)
  refine ⟨result, ?_, he, ?_⟩
  · rw [context_point_exact, ← raw_lift, ← raw_lift, ← (native_point_is_reversed_dense_point _ _).1,
      List.reverse_reverse]
  · show (Verifier.expectedClaims Connections.packedFold c p idx)[i.val]? = _
    rw [expected_claim_cell_exact, Option.some.injEq, Option.some.injEq]
    apply Subtype.eq
    rw [Connections.packedFold_exact, hopen, ← raw_lift, hval]

/-- The same statement for a successful checked outer execution
(`OuterAdapter.execute`): its context is `whirContext` at its own rounds and
sampled indices, so every bound cell of `result.context` is the full-table
evaluation whenever `hopen` holds. Under the envelope/shape sizes of
`source_sized_execution_exists` the padded table has exactly
`degreeBits + indexBits = context.numVariables` variables. -/
theorem execute_bound_cell_is_full_table_evaluation (hash : OuterInitial.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (result : OuterAdapter.Execution) (h : OuterAdapter.execute hash c p = some result)
    (i : Fin 5) (cols : List (List Element))
    (hc : ∀ col ∈ cols, col.length = 2 ^ (cellRow result.rounds i).length)
    (hw : cols.length ≤ 2 ^ (boundCell p.used result.indices.points i).2.length)
    (hopen : (boundCell p.used result.indices.points i).1.map Subtype.val =
      rowOpenings cols (lift (cellRow result.rounds i))) :
    CellOpensFullTable result.context i.val (cellPoint i) cols (lift (cellRow result.rounds i))
      (lift (boundCell p.used result.indices.points i).2) ∧
    ((cellRow result.rounds i).length = c.degreeBits →
      (boundCell p.used result.indices.points i).2.length = c.indexBits →
      (paddedTable cols (lift (cellRow result.rounds i)).length
        (lift (boundCell p.used result.indices.points i).2).length).numVars = result.context.numVariables) := by
  obtain ⟨_, _, _, _, _, _, _, hctx⟩ := OuterAdapter.execute_success_uses_same_inputs hash c p result h
  refine ⟨?_, ?_⟩
  · rw [hctx]
    exact expected_claim_cell_is_full_table_evaluation c p result.rounds result.indices.points i cols hc hw hopen
  · intro hd hb
    rw [hctx, paddedTable_numVars, lift, lift, List.length_map, List.length_map, hd, hb]
    rfl

/-! ## 5. The sixth cell -/

/-- **sixth_cell_opens_nothing.** The slot Rust would use for the norm-inverse
group at the gate point (`rustSlot pointGate groupNormInverse = 5`) is `none`
(`Verifier.context_unused_gate_norm_is_unbound`), every cell at the gate point
(positions 3, 4, 5) is unchanged by any replacement of `logNormInverse`, and
every cell at the log point (positions 0, 1, 2) is unchanged by any replacement
of the gate index point. Hence no expected-claim constraint folds
`logNormInverse` at the gate point. -/
theorem sixth_cell_opens_nothing (foldClaim : Verifier.FoldClaim) (c : Verifier.Config)
    (p : Verifier.Proof) (idx : Verifier.IndexPoints) :
    rustSlot pointGate groupNormInverse = 5 ∧
    (Verifier.expectedClaims foldClaim c p idx)[rustSlot pointGate groupNormInverse]? = some none ∧
    (∀ other : List Verifier.Ext3,
      (Verifier.expectedClaims foldClaim c { p with used := { p.used with logNormInverse := other } } idx).drop 3 =
        (Verifier.expectedClaims foldClaim c p idx).drop 3) ∧
    (∀ other : List Verifier.Ext3,
      (Verifier.expectedClaims foldClaim c p { idx with gate := other }).take 3 =
        (Verifier.expectedClaims foldClaim c p idx).take 3) ∧
    (Verifier.expectedClaims foldClaim c p idx).drop 3 =
      [some (foldClaim p.used.gatePreprocessed (Verifier.width c) idx.gate),
       some (foldClaim p.used.gateWitness (Verifier.width c) idx.gate), none] :=
  ⟨rfl, Verifier.context_unused_gate_norm_is_unbound foldClaim c p idx, fun _ => rfl, fun _ => rfl, rfl⟩

theorem sixth_cell_of_execution_opens_nothing (hash : OuterInitial.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (result : OuterAdapter.Execution) (h : OuterAdapter.execute hash c p = some result) :
    result.context.expectedClaims[5]? = some none ∧
    result.context.expectedClaims.map Option.isSome = [true, true, true, true, true, false] := by
  obtain ⟨_, hmask, hclaims⟩ := OuterAdapter.execute_same_roots_and_mask hash c p result h
  exact ⟨by rw [hclaims]; rfl, hmask⟩

/-! ## 6. A concrete, non-vacuous instance -/

/-- Two constituent columns of two rows each: width 2, one row bit, one index bit. -/
def exampleColumns : List (List Element) := [[1, 2], [3, 4]]

def exampleRoot : Verifier.Root := ⟨0, by decide⟩

def exampleConfig : Verifier.Config :=
  { degreeBits := 1, numConstants := 2, numRouted := 0, numWires := 0, numPublicInputs := 0,
    numSelectors := 0, numGateConstraints := 0, quotientDegree := 0, gateRows := 0, indexBits := 1,
    kIs := [], subgroupPowers := [], publicInputWireMap := [], gatesEncoding := [], whirEncoding := [],
    circuitDigest := [], circuitConfigDigest := exampleRoot, whirProtocolId := [], whirSessionId := [] }

/-- Honest openings of `exampleColumns` at row point `[5]`: `1 + 5·(2-1) = 6`
and `3 + 5·(4-3) = 8`. -/
def exampleProof : Verifier.Proof :=
  { protocolVersion := 3, constituentWidth := 2, circuitDigest := [], publicInputs := [],
    preprocessedRoot := exampleRoot, witnessRoot := exampleRoot, normInverseRoot := exampleRoot,
    logRounds := [], gateRounds := [],
    used := ⟨[(6 : Element).toVerifier, (8 : Element).toVerifier], [], [], [], []⟩,
    whirTranscript := [], whirHints := [] }

def exampleRounds : Verifier.RoundState :=
  ⟨[], 1, Verifier.zero, Verifier.zero, [(5 : Element).toVerifier], []⟩

def exampleIndex : Verifier.IndexPoints := ⟨[(7 : Element).toVerifier], []⟩

def exampleContext : Verifier.WhirContext :=
  Verifier.whirContext Connections.packedFold exampleConfig exampleProof exampleRounds exampleIndex

theorem example_width : Verifier.width exampleConfig = 2 := by decide

/-- The full 2-variable table `[1,2,3,4]` at the dense point `[5,7]` is
`6 + 7·(8-6) = 20`. -/
theorem example_full_table_evaluation :
    evaluate (paddedTable exampleColumns 1 1) [5, 7] = some (20 : Element) := by decide

theorem example_openings_are_row_folds :
    exampleProof.used.logPreprocessed.map Subtype.val = rowOpenings exampleColumns [5] := by decide

theorem example_expected_cell :
    exampleContext.expectedClaims[0]? = some (some (20 : Element).toVerifier) := by decide

theorem example_native_point :
    exampleContext.points[0]? = some [(7 : Element).toVerifier.val, (5 : Element).toVerifier.val] := by decide

/-- The general theorem instantiated on the example: cell 0 opens the padded
table `[[1,2],[3,4]]` at the dense point `[5] ++ [7]`, with native point `[7,5]`. -/
theorem example_cell_opens_full_table :
    CellOpensFullTable exampleContext 0 0 exampleColumns (lift [(5 : Element).toVerifier])
      (lift [(7 : Element).toVerifier]) :=
  expected_claim_cell_is_full_table_evaluation exampleConfig exampleProof exampleRounds exampleIndex 0
    exampleColumns (by decide) (by decide) (by decide)

/-- Contingency of the identity: if the opened cells are NOT the row folds
(`[6, 9]` instead of `[6, 8]`), the expected claim is `6 + 7·3 = 27 ≠ 20`.
The verifier computes the fold of whatever cells it is given; equality with the
full-table evaluation is exactly `hopen`, not an unconditional fact. -/
theorem example_dishonest_openings_differ :
    (Verifier.expectedClaims Connections.packedFold exampleConfig
      { exampleProof with used := ⟨[(6 : Element).toVerifier, (9 : Element).toVerifier], [], [], [], []⟩ }
      exampleIndex)[0]? = some (some (27 : Element).toVerifier) ∧
    (27 : Element) ≠ 20 := by
  refine ⟨by decide, by decide⟩

end Audit.Wire3.OpenedClaimFold
