import Audit.Wire3.Gates
import Audit.Wire3.Algebra

/-!
Gate id 13: concrete coset interpolation over Ext3-valued wires (69516414).
The ten tables below are exact eight-byte big-endian entries decoded from
CosetInterpolationConstants.sol; no evaluator or table value is an observation.
The checked wrapper implements _validateAndLayout; raw totalized helpers are
only covered for its valid layouts. Ext3 canonicality is supplied by the input
subtype. The recurrence uses the OLD product for nextEvaluation, exactly as
CosetInterpolationGateExt3._runChunk, and preserves intermediate claim order.

Length/index/recurrence properties below are deterministic model theorems.
They do not establish the barycentric identity, field primality, subgroup
generator order, all gate-degree bounds, or Rust/Yul/compiler refinement.
-/
namespace Audit.Wire3.GatesAdditionalCoset
open Verifier
open Gates (readValue readExt2 embed Ext2)
def subgroup1 : List Nat :=
  [1, 18446744069414584320]

def weights1 : List Nat :=
  [9223372034707292161, 9223372034707292160]

def subgroup2 : List Nat :=
  [1, 281474976710656, 18446744069414584320, 18446462594437873665]

def weights2 : List Nat :=
  [13835058052060938241, 70368744177664, 4611686017353646080, 18446673700670406657]

def subgroup3 : List Nat :=
  [1, 16777216, 281474976710656, 1099511627520, 18446744069414584320, 18446744069397807105, 18446462594437873665, 18446742969902956801]

def weights3 : List Nat :=
  [16140901060737761281, 2097152, 35184372088832, 137438953440, 2305843008676823040, 18446744069412487169, 18446708885042495489, 18446743931975630881]

def subgroup4 : List Nat :=
  [1, 4096, 16777216, 68719476736, 281474976710656, 1152921504606846976, 1099511627520, 4503599626321920, 18446744069414584320, 18446744069414580225, 18446744069397807105, 18446744000695107585, 18446462594437873665, 17293822564807737345, 18446742969902956801, 18442240469788262401]

def weights4 : List Nat :=
  [17293822565076172801, 256, 1048576, 4294967296, 17592186044416, 72057594037927936, 68719476720, 281474976645120, 1152921504338411520, 18446744069414584065, 18446744069413535745, 18446744065119617025, 18446726477228539905, 18374686475376656385, 18446744000695107601, 18446462594437939201]

def subgroup5 : List Nat :=
  [1, 64, 4096, 262144, 16777216, 1073741824, 68719476736, 4398046511104, 281474976710656, 18014398509481984, 1152921504606846976, 17179869180, 1099511627520, 70368744161280, 4503599626321920, 288230376084602880, 18446744069414584320, 18446744069414584257, 18446744069414580225, 18446744069414322177, 18446744069397807105, 18446744068340842497, 18446744000695107585, 18446739671368073217, 18446462594437873665, 18428729670905102337, 17293822564807737345, 18446744052234715141, 18446742969902956801, 18446673700670423041, 18442240469788262401, 18158513693329981441]

def weights5 : List Nat :=
  [17870283317245378561, 2, 128, 8192, 524288, 33554432, 2147483648, 137438953472, 8796093022208, 562949953421312, 36028797018963968, 2305843009213693952, 34359738360, 2199023255040, 140737488322560, 9007199252643840, 576460752169205760, 18446744069414584319, 18446744069414584193, 18446744069414576129, 18446744069414060033, 18446744069381029889, 18446744067267100673, 18446743931975630849, 18446735273321562113, 18446181119461163009, 18410715272395620353, 16140901060200890369, 18446744035054845961, 18446741870391329281, 18446603331926261761, 18437736870161940481]

def subgroupTable : Nat → List Nat
  | 1 => subgroup1 | 2 => subgroup2 | 3 => subgroup3 | 4 => subgroup4 | 5 => subgroup5 | _ => []
def weightTable : Nat → List Nat
  | 1 => weights1 | 2 => weights2 | 3 => weights3 | 4 => weights4 | 5 => weights5 | _ => []

theorem table_lengths (bits : Nat) (h : 1 ≤ bits ∧ bits ≤ 5) :
    (subgroupTable bits).length = 2 ^ bits ∧ (weightTable bits).length = 2 ^ bits := by
  have hs : bits = 1 ∨ bits = 2 ∨ bits = 3 ∨ bits = 4 ∨ bits = 5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem table_values_canonical (bits : Nat) (h : 1 ≤ bits ∧ bits ≤ 5) :
    (subgroupTable bits).all (fun x => decide (x < modulus)) = true ∧
    (weightTable bits).all (fun x => decide (x < modulus)) = true := by
  have hs : bits = 1 ∨ bits = 2 ∨ bits = 3 ∨ bits = 4 ∨ bits = 5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem table_reads_in_bounds (bits index : Nat) (hb : 1 ≤ bits ∧ bits ≤ 5) (hi : index < 2 ^ bits) :
    index < (subgroupTable bits).length ∧ index < (weightTable bits).length := by
  rw [(table_lengths bits hb).1, (table_lengths bits hb).2]
  exact ⟨hi, hi⟩

theorem weight_zero_canonical (bits : Nat) (h : 1 ≤ bits ∧ bits ≤ 5) :
    (weightTable bits).getD 0 0 < modulus := by
  have hs : bits = 1 ∨ bits = 2 ∨ bits = 3 ∨ bits = 4 ∨ bits = 5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

def pairZero : Ext2 := ⟨zero, zero⟩
def pairOne : Ext2 := ⟨Gates.one, zero⟩
def pairAdd (a b : Ext2) : Ext2 := ⟨add a.c0 b.c0, add a.c1 b.c1⟩
def pairSub (a b : Ext2) : Ext2 := ⟨sub a.c0 b.c0, sub a.c1 b.c1⟩
def pairScalar (a : Ext2) (s : Ext3) : Ext2 := ⟨mul a.c0 s, mul a.c1 s⟩
def pairValues (a : Ext2) : List Ext3 := [a.c0, a.c1]

theorem pair_difference_exact (a b : Ext2) :
    (∀ v ∈ pairValues (pairSub a b), v = zero) ↔ a = b := by
  exact Gates.ext2_constraints_exact b a

def points (bits : Nat) : Nat := 2 ^ bits
def intermediates (bits degree : Nat) : Nat := (points bits - 2) / (degree - 1)
def intermediateStart (bits : Nat) : Nat := 2 * points bits + 5
def shiftedPointIndex (bits degree : Nat) : Nat :=
  intermediateStart bits + 4 * intermediates bits degree
def wireCount (bits degree : Nat) : Nat := shiftedPointIndex bits degree + 2
def constraintCount (bits degree : Nat) : Nat := 4 + 4 * intermediates bits degree

structure State where
  evaluation : Ext2
  product : Ext2
  point : Ext2
  deriving DecidableEq

def chunkStep (wires : List Ext3) (bits index : Nat) (s : State) : State :=
  let term := pairSub s.point ⟨embed ((subgroupTable bits).getD index 0), zero⟩
  let weighted := pairScalar (readExt2 wires (1 + 2 * index))
    (embed ((weightTable bits).getD index 0))
  ⟨pairAdd (Gates.ext2Mul s.evaluation term) (Gates.ext2Mul weighted s.product),
    Gates.ext2Mul s.product term, s.point⟩

def runChunk (wires : List Ext3) (bits : Nat) : Nat → Nat → State → State
  | _, 0, s => s
  | index, count + 1, s => runChunk wires bits (index + 1) count (chunkStep wires bits index s)

theorem chunk_step_uses_old_product (wires : List Ext3) (bits index : Nat) (s : State) :
    (chunkStep wires bits index s).evaluation =
      pairAdd (Gates.ext2Mul s.evaluation
        (pairSub s.point ⟨embed ((subgroupTable bits).getD index 0), zero⟩))
        (Gates.ext2Mul
          (pairScalar (readExt2 wires (1 + 2 * index)) (embed ((weightTable bits).getD index 0)))
          s.product) := rfl

theorem run_chunk_retains_point (wires : List Ext3) (bits start count : Nat) (s : State) :
    (runChunk wires bits start count s).point = s.point := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih => simpa [runChunk, chunkStep] using ih (start + 1) (chunkStep wires bits start s)

def nextChunkStart (degree i : Nat) : Nat := 1 + (degree - 1) * (i + 1)
def nextChunkCount (bits degree i : Nat) : Nat :=
  min (nextChunkStart degree i + degree - 1) (points bits) - nextChunkStart degree i

structure Progress where
  state : State
  constraints : List Ext3

def intermediateStep (wires : List Ext3) (bits degree i : Nat) (p : Progress) : Progress :=
  let evaluation := readExt2 wires (intermediateStart bits + 2 * i)
  let product := readExt2 wires (intermediateStart bits + 2 * intermediates bits degree + 2 * i)
  let out := p.constraints ++ pairValues (pairSub evaluation p.state.evaluation) ++
    pairValues (pairSub product p.state.product)
  let installed : State := ⟨evaluation, product, p.state.point⟩
  ⟨runChunk wires bits (nextChunkStart degree i) (nextChunkCount bits degree i) installed, out⟩

def runIntermediates (wires : List Ext3) (bits degree : Nat) : Nat → Nat → Progress → Progress
  | _, 0, p => p
  | i, count + 1, p => runIntermediates wires bits degree (i + 1) count
      (intermediateStep wires bits degree i p)

def evaluateUnchecked (wires : List Ext3) (bits degree : Nat) : List Ext3 :=
  let evaluationPoint := readExt2 wires (1 + 2 * points bits)
  let shifted := readExt2 wires (shiftedPointIndex bits degree)
  let first := pairValues (pairSub evaluationPoint (pairScalar shifted (readValue wires 0)))
  let initial := runChunk wires bits 0 degree ⟨pairZero, pairOne, shifted⟩
  let result := runIntermediates wires bits degree 0 (intermediates bits degree) ⟨initial, first⟩
  result.constraints ++ pairValues
    (pairSub (readExt2 wires (1 + 2 * (points bits + 1))) result.state.evaluation)

def layoutValid (wires : List Ext3) (bits degree : Nat) : Prop :=
  1 ≤ bits ∧ bits ≤ 5 ∧ 2 ≤ degree ∧ degree ≤ points bits ∧
  wires.length = wireCount bits degree ∧ (weightTable bits).getD 0 0 < modulus
instance (wires : List Ext3) (bits degree : Nat) : Decidable (layoutValid wires bits degree) :=
  inferInstanceAs (Decidable (_ ∧ _))

def evaluate (wires : List Ext3) (bits degree : Nat) : Option (List Ext3) :=
  if layoutValid wires bits degree then some (evaluateUnchecked wires bits degree) else none

theorem intermediate_step_adds_four (wires : List Ext3) (bits degree i : Nat) (p : Progress) :
    (intermediateStep wires bits degree i p).constraints.length = p.constraints.length + 4 := by
  simp [intermediateStep, pairValues, Nat.add_assoc]

theorem intermediates_output_length (wires : List Ext3) (bits degree start count : Nat) (p : Progress) :
    (runIntermediates wires bits degree start count p).constraints.length = p.constraints.length + 4 * count := by
  induction count generalizing start p with
  | zero => simp [runIntermediates]
  | succ count ih =>
      rw [runIntermediates, ih, intermediate_step_adds_four]
      omega

theorem output_length (wires : List Ext3) (bits degree : Nat) :
    (evaluateUnchecked wires bits degree).length = constraintCount bits degree := by
  simp only [evaluateUnchecked, List.length_append, intermediates_output_length, pairValues, List.length_cons,
    List.length_nil, constraintCount]
  omega

theorem evaluated_length_and_layout (wires output : List Ext3) (bits degree : Nat)
    (h : evaluate wires bits degree = some output) :
    layoutValid wires bits degree ∧ output.length = constraintCount bits degree := by
  unfold evaluate at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq] at h
    subst output
    exact ⟨hl, output_length wires bits degree⟩
  · simp at h

theorem layout_access_bounds (wires : List Ext3) (bits degree : Nat)
    (h : layoutValid wires bits degree) :
    0 < wires.length ∧ 1 + 2 * points bits + 1 < wires.length ∧
    1 + 2 * (points bits + 1) + 1 < wires.length ∧
    shiftedPointIndex bits degree + 1 < wires.length := by
  simp only [layoutValid, wireCount, shiftedPointIndex, intermediateStart] at h
  simp only [shiftedPointIndex, intermediateStart]
  omega

theorem value_pair_access_bounds (wires : List Ext3) (bits degree index : Nat)
    (h : layoutValid wires bits degree) (hi : index < points bits) :
    1 + 2 * index + 1 < wires.length := by
  simp only [layoutValid, wireCount, shiftedPointIndex, intermediateStart] at h
  omega

theorem intermediate_pair_access_bounds (wires : List Ext3) (bits degree i : Nat)
    (h : layoutValid wires bits degree) (hi : i < intermediates bits degree) :
    intermediateStart bits + 2 * i + 1 < wires.length ∧
    intermediateStart bits + 2 * intermediates bits degree + 2 * i + 1 < wires.length := by
  simp only [layoutValid, wireCount, shiftedPointIndex] at h
  omega

theorem next_chunk_access_bounds (bits degree i j : Nat)
    (hj : j < nextChunkCount bits degree i) :
    nextChunkStart degree i + j < points bits := by
  unfold nextChunkCount at hj
  have hm := Nat.min_le_right (nextChunkStart degree i + degree - 1) (points bits)
  omega

theorem intermediate_checks_preserve_claim_order (wires : List Ext3) (bits degree i : Nat) (p : Progress) :
    (intermediateStep wires bits degree i p).constraints =
      p.constraints ++ pairValues (pairSub (readExt2 wires (intermediateStart bits + 2 * i)) p.state.evaluation) ++
      pairValues (pairSub (readExt2 wires
        (intermediateStart bits + 2 * intermediates bits degree + 2 * i)) p.state.product) := rfl

/-- A degree-one constant polynomial with a genuinely non-base Ext3 value.
    This is a normal gate computation, not a PCS/proof fixture. -/
def nonbaseConstantWires : List Ext3 :=
  [Gates.one, Gates.extensionGenerator, zero, Gates.extensionGenerator, zero,
    zero, zero, Gates.extensionGenerator, zero, zero, zero]

set_option maxRecDepth 8192 in
theorem coset_nonbase_constant_positive :
    evaluate nonbaseConstantWires 1 2 = some [zero, zero, zero, zero] := by decide

end Audit.Wire3.GatesAdditionalCoset
