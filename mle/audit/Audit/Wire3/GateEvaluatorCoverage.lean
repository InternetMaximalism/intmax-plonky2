import Audit.Wire3.GateAllPolynomial
import Audit.Wire3.AlphaZeroCheck

/-!
# Gate-evaluator coverage: the honest baseline, the declared source tables, and a
shape-checked evaluator for all fourteen families

This is gate-evaluation SEMANTICS modelling -- a MIRROR of the source's
per-family constraint lists, declared counts and declared degrees.  It is NOT a
refinement proof of the Rust or the Solidity implementation, and it does NOT
claim circuit truth: that a vanishing constraint list means a satisfied Plonky2
circuit remains outside this model, as everywhere in this development.  No
probability statement is made and nothing here is, or bounds, the system's
soundness error.  The gate-constraint envelope used throughout is `123`
(`Gates.envelope`, mirroring `Plonky2GateEvaluatorExt3.MAX_GATE_CONSTRAINTS`);
the number `125` does not appear in this model and is not the bound.

## The baseline, stated honestly first

The review note this module answers says the adopted gate model "evaluates only
ids 0,1,2,3,6,7".  That is EXACTLY TRUE OF ONE DEFINITION and stale for the
model as a whole, and section 1 proves both halves (`coverage_status`):

* `Gates.evaluateUnfiltered` (Gates.lean:562-571), the PARTIAL evaluator whose
  own header calls itself a model coverage limit, is `some` on exactly ids
  `0,1,2,3,6,7` and `none` on the other eight configured families
  (`partial_evaluator_coverage`);
* `GatesComplete.evaluateUnfiltered` (GatesComplete.lean:16-21) -- the
  dispatcher that `Integrated.evaluateGate`, `GateDenseRound`,
  `GateSlotCommutation` and `AlphaZeroCheck.filteredValue` actually consume --
  evaluates ALL FOURTEEN: ids `0..12` unconditionally and id `13` under the
  coset layout check (`complete_dispatcher_below_coset`,
  `complete_dispatcher_coset_shape_checked`).  `GateAllPolynomial` likewise
  already carries a polynomial bridge and a degree bound for all fourteen.

So the open item is not "eight families are unevaluated".  It is the four things
supplied below.

## What this module adds

1. `declaredConstraints` / `declaredWires` / `declaredLocalConstants` /
   `declaredDegree`: the source tables transcribed directly, and
   `declared_tables_match_adopted_requirements`, a mirror check of the adopted
   `Gates.requirements` against them.  For `declaredDegree` in particular: the
   Rust SHAPE validator `validate_gate_shape` has no degree column, but the Rust
   ADMISSION check `validate_gate_ext3_context` (`gate_ext3.rs:462-479`)
   enforces the same inequality per row,
   `Gate::degree() + filter_degree <= quotient_degree_factor + 1`, taking the
   degree from plonky2's own `Gate::degree()`; and `fixture.rs:1245-1264`
   (`fixture_gate_degree`) is a literal Rust transcription of the same table.
   Solidity's `_unfilteredDegree` agrees with plonky2's `degree()` for all
   fourteen families (`noop.rs:63`, `constant.rs:105`, `public_input.rs:93`,
   `arithmetic_base.rs:158`, `poseidon.rs:410`, `poseidon_mds.rs:214`,
   `arithmetic_extension.rs:163`, `multiplication_extension.rs:150`,
   `exponentiation.rs:198`, `base_sum.rs:140`, `reducing.rs:178`,
   `reducing_extension.rs:178`, `random_access.rs:283`,
   `coset_interpolation.rs:388`).  There is therefore no Rust/Solidity
   divergence on the degree check.
2. A SHAPE-CHECKED evaluator per family.  The adopted dispatcher reads its lists
   through `Gates.readValue`, i.e. `List.getD i zero`, so on a short list it
   returns constraints built from default zeros; the adopted development
   justifies those reads externally, with per-family access-bound theorems that
   hold only under `validateGate`.  `evaluateNoop` ... `evaluateCosetInterpolation`
   make the precondition INTRINSIC, with `<family>_shape` (`some` exactly when
   the parameter grammar holds and both lists are long enough) and
   `<family>_constraint_count` (the emitted length is the SOURCE-declared count,
   proved on the evaluator's own output, not by comparing metadata with itself).
3. `evaluateGateFull`, the dispatcher over those, with
   `extended_agrees_with_complete_dispatcher`,
   `extended_agrees_on_covered_ids` and -- on any validated row at the
   configured widths -- outright equality with the adopted dispatcher
   (`validated_full_evaluator_agrees`).  Every adopted consumer is defined by
   matching on that dispatcher, so substituting the extension changes nothing
   they compute; `validated_contribution_via_full_evaluator` and
   `full_evaluation_length_within_envelope` spell that out for
   `GatesComplete.contribution` and for the `123` bound.
4. The envelope facts that need all fourteen formulas at once:
   `configured_row_constraints_at_most_123` (every configured row, every
   family), the CONCRETE `RandomAccessGate` row that declares `124` constraints,
   passes the per-row `Gates.validateGate` at the widest admissible
   configuration and is nevertheless unconfigurable
   (`overflowing_row_passes_per_row_validation`,
   `overflowing_row_is_unconfigurable`), and
   `base_sum_only_small_bases_are_configurable`: the Rust grammar allows
   `BaseSumGate` bases `16, 32, 64, 128, 256`, but the declared degree of that
   family IS its base and the degree accounting caps it at
   `quotientDegreeFactor + 1 <= 9`, so only bases `2..8` are reachable.

## Alpha-Horner

`AlphaZeroCheck`'s per-row aggregate degree bound is FAMILY-AGNOSTIC: the
coefficient list is the source's `vec![ZERO; num_gate_constraints]` slot buffer
(`gate_ext3.rs:570`), its length is `c.numGateConstraints` alone, and the root
bound `natDegree <= c.numGateConstraints - 1 <= 122` follows from that length.
The families enter only through `AlphaZeroCheck.filteredValue`, which reads the
complete dispatcher; `full_evaluator_keeps_filtered_values` and
`extended_alpha_horner_degree` show the extension reproduces every filtered
value, so every slot coefficient, the aggregate polynomial and its degree and
root bounds are unchanged.

## Sources mirrored (Rust primary; the Solidity mirror is generated from it)

* per-family `(expected_constraints, required_wires, required_local_constants)`
  and the parameter grammars: `mle/src/gate_ext3.rs:177-408`
  (`validate_gate_shape`);
* per-family constraint lists: `mle/src/gate_ext3.rs:649-716`
  (`evaluate_unfiltered`) and the individual `eval_*` at 718-738, 807-894,
  896-1029 and 1031-1101;
* the declared DEGREE table: `mle/contracts/src/Plonky2GateEvaluatorExt3.sol:196-212`
  (`_unfilteredDegree`), consumed at 183-187;
* the configuration envelope: `Plonky2GateEvaluatorExt3.sol:172-189`;
* the slot buffer and forward power reduction: `gate_ext3.rs:570,591-608`.

## What is NOT claimed

No circuit truth, no witness existence, no probability, no Fiat-Shamir, no PCS,
Merkle or WHIR statement, no Rust/Solidity/Yul compilation refinement, and no
claim that the production implementation rejects every input this Lean model
rejects -- the shape guard is a MODEL strengthening, and the adopted
access-bound theorems remain the statement about the production path.  The
per-family formulas are transcribed from the audited Rust with file and line
cited per family; they are not themselves verified against Plonky2's own gate
implementations.  `LookupGate` and `LookupTableGate` have no id here at all --
see section 11.
-/

namespace Audit.Wire3.GateEvaluatorCoverage

open Verifier
open Gates (GateInfo Requirements)

/-- The six ids the PARTIAL evaluator `Gates.evaluateUnfiltered` returns `some`
for.  This is the set the review note names, and section 1 proves it exact. -/
def partialCovered (gateId : Nat) : Bool :=
  decide (gateId = 0 ∨ gateId = 1 ∨ gateId = 2 ∨ gateId = 3 ∨ gateId = 6 ∨ gateId = 7)

theorem partial_evaluator_coverage (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (numSelectors : Nat) (hk : g.gateId < 14) :
    (Gates.evaluateUnfiltered g wires constants publicHash numSelectors).isSome =
      partialCovered g.gateId := by
  have hid : g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨ g.gateId = 4 ∨
      g.gateId = 5 ∨ g.gateId = 6 ∨ g.gateId = 7 ∨ g.gateId = 8 ∨ g.gateId = 9 ∨
      g.gateId = 10 ∨ g.gateId = 11 ∨ g.gateId = 12 ∨ g.gateId = 13 := by omega
  rcases hid with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp [Gates.evaluateUnfiltered, partialCovered, h]

theorem complete_dispatcher_below_coset (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (numSelectors : Nat) (hk : g.gateId < 13) :
    (GatesComplete.evaluateUnfiltered g wires constants publicHash numSelectors).isSome = true := by
  have hid : g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨ g.gateId = 4 ∨
      g.gateId = 5 ∨ g.gateId = 6 ∨ g.gateId = 7 ∨ g.gateId = 8 ∨ g.gateId = 9 ∨
      g.gateId = 10 ∨ g.gateId = 11 ∨ g.gateId = 12 := by omega
  rcases hid with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp [GatesComplete.evaluateUnfiltered, GatesAdditional.dispatchUnchecked,
      Gates.evaluateUnfiltered, h]

theorem complete_dispatcher_coset_shape_checked (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (numSelectors : Nat) (hk : g.gateId = 13) :
    (GatesComplete.evaluateUnfiltered g wires constants publicHash numSelectors).isSome = true ↔
      GatesAdditionalCoset.layoutValid
        (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2))
        g.numOrConsts g.param2 := by
  simp only [GatesComplete.evaluateUnfiltered, GatesAdditional.dispatchUnchecked, hk,
    GatesAdditionalCoset.evaluate]
  by_cases hl : GatesAdditionalCoset.layoutValid
      (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2)) g.numOrConsts g.param2
  · simp [hl]
  · simp [hl]

/-! ## 2. The declared source tables -/

/-- Mirror of the per-family `expected_constraints` of
`mle/src/gate_ext3.rs:177-385` (`validate_gate_shape`).  `POSEIDON_CONSTRAINTS`
is `123` and `2 * SPONGE_WIDTH` is `24`; `INNER_EXTENSION_DEGREE` is `2`. -/
def declaredConstraints (g : GateInfo) : Nat :=
  if g.gateId = 0 then 0
  else if g.gateId = 1 then g.numOrConsts
  else if g.gateId = 2 then 4
  else if g.gateId = 3 then g.numOrConsts
  else if g.gateId = 4 then 123
  else if g.gateId = 5 then 24
  else if g.gateId = 6 then 2 * g.numOrConsts
  else if g.gateId = 7 then 2 * g.numOrConsts
  else if g.gateId = 8 then g.numOrConsts + 1
  else if g.gateId = 9 then g.numOrConsts + 1
  else if g.gateId = 10 then 2 * g.numOrConsts
  else if g.gateId = 11 then 2 * g.numOrConsts
  else if g.gateId = 12 then g.param2 * (g.numOrConsts + 2) + g.param3
  else if g.gateId = 13 then 4 + 4 * ((2 ^ g.numOrConsts - 2) / (g.param2 - 1))
  else 0

/-- Mirror of the per-family `required_wires` of `gate_ext3.rs:177-385`.
`POSEIDON_WIRES` is `135` and `4 * SPONGE_WIDTH` is `48`. -/
def declaredWires (g : GateInfo) : Nat :=
  if g.gateId = 0 then 0
  else if g.gateId = 1 then g.numOrConsts
  else if g.gateId = 2 then 4
  else if g.gateId = 3 then 4 * g.numOrConsts
  else if g.gateId = 4 then 135
  else if g.gateId = 5 then 48
  else if g.gateId = 6 then 8 * g.numOrConsts
  else if g.gateId = 7 then 6 * g.numOrConsts
  else if g.gateId = 8 then 2 * g.numOrConsts + 2
  else if g.gateId = 9 then g.numOrConsts + 1
  else if g.gateId = 10 then 4 + 3 * g.numOrConsts
  else if g.gateId = 11 then 4 + 4 * g.numOrConsts
  else if g.gateId = 12 then
    (2 + 2 ^ g.numOrConsts) * g.param2 + g.param3 + g.param2 * g.numOrConsts
  else if g.gateId = 13 then
    7 + 2 * 2 ^ g.numOrConsts + 4 * ((2 ^ g.numOrConsts - 2) / (g.param2 - 1))
  else 0

/-- Mirror of the per-family `required_local_constants` of
`gate_ext3.rs:177-385`.  These are the constants AFTER the `num_selectors`
selector columns (`gate_ext3.rs:658`, `let local_constants = &constants[num_selectors..]`). -/
def declaredLocalConstants (g : GateInfo) : Nat :=
  if g.gateId = 3 then 2
  else if g.gateId = 6 then 2
  else if g.gateId = 7 then 1
  else if g.gateId = 1 then g.numOrConsts
  else if g.gateId = 12 then g.param3
  else 0

/-- Mirror of `Plonky2GateEvaluatorExt3.sol:196-212` (`_unfilteredDegree`), the
declared per-family degree in the wire columns; the degree accounting at
`Plonky2GateEvaluatorExt3.sol:183-187` consumes it.  The Rust SHAPE validator
`validate_gate_shape` has no degree column, but Rust is not silent on the
degree: the admission check `validate_gate_ext3_context`
(`gate_ext3.rs:462-479`) enforces the same inequality per row,
`Gate::degree() + filter_degree <= quotient_degree_factor + 1`, with the degree
read from plonky2's own `Gate::degree()`, and `fixture.rs:1245-1264`
(`fixture_gate_degree`) transcribes this same table into Rust literally.
Solidity's `_unfilteredDegree` agrees with plonky2's `degree()` family by
family: `noop.rs:63` = 0; `constant.rs:105`, `public_input.rs:93`,
`poseidon_mds.rs:214` = 1; `arithmetic_base.rs:158`,
`arithmetic_extension.rs:163`, `multiplication_extension.rs:150` = 3;
`poseidon.rs:410` = 7; `exponentiation.rs:198` = 4; `base_sum.rs:140` = `B`;
`reducing.rs:178`, `reducing_extension.rs:178` = 2; `random_access.rs:283` =
`bits + 1`; `coset_interpolation.rs:388` = `degree`.  So there is no
Rust/Solidity divergence on the degree check to close. -/
def declaredDegree (g : GateInfo) : Nat :=
  if g.gateId = 0 then 0
  else if g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 5 then 1
  else if g.gateId = 3 ∨ g.gateId = 6 ∨ g.gateId = 7 then 3
  else if g.gateId = 4 then 7
  else if g.gateId = 8 then 4
  else if g.gateId = 9 ∨ g.gateId = 13 then g.param2
  else if g.gateId = 10 ∨ g.gateId = 11 then 2
  else if g.gateId = 12 then g.numOrConsts + 1
  else 0

/-- All four declared columns of the adopted `Gates.requirements` agree with the
tables transcribed directly from `validate_gate_shape` and `_unfilteredDegree`.
This is a mirror check between two independent transcriptions of the same source
tables, not a refinement proof of either source.

One grammar clause is stated more tightly here than in Rust: the adopted
`Gates.requirements` for id `12` (`RandomAccessGate`) carries `n <= 7`,
mirroring `Plonky2GateEvaluatorExt3.sol:322`, whereas Rust's
`validate_gate_shape` (`gate_ext3.rs:288-320`) bounds the bit count only through
`checked_shl`.  The accept-sets still coincide: `n >= 8` forces a vector size of
at least `256`, hence at least `2 + 256 = 258` required wires, which exceeds the
`160` wire cap that both sides enforce, so no row with `n >= 8` is accepted by
either. -/
theorem declared_tables_match_adopted_requirements (g : GateInfo) (r : Requirements)
    (hk : g.gateId < 14) (hr : Gates.requirements g = some r) :
    r.constraints = declaredConstraints g ∧ r.wires = declaredWires g ∧
      r.localConstants = declaredLocalConstants g ∧ r.degree = declaredDegree g := by
  have hid : g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨ g.gateId = 4 ∨
      g.gateId = 5 ∨ g.gateId = 6 ∨ g.gateId = 7 ∨ g.gateId = 8 ∨ g.gateId = 9 ∨
      g.gateId = 10 ∨ g.gateId = 11 ∨ g.gateId = 12 ∨ g.gateId = 13 := by omega
  rcases hid with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · simp only [Gates.requirements, h] at hr
      split at hr
      · simp only [Option.some.injEq] at hr
        subst hr
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp [declaredConstraints, declaredWires, declaredLocalConstants, declaredDegree, h]
      · simp at hr

/-! ## 3. Shape-checked per-family evaluators

The adopted dispatcher reads wires and constants through `Gates.readValue`,
i.e. `List.getD i zero`, so on a list shorter than the family requires it
returns constraints built from default zeros rather than rejecting.  The adopted
development justifies those reads EXTERNALLY, via the per-family access-bound
results `Gates.arithmetic_accesses_bounded` and friends and
`GatesAdditional.random_bit_access_bounds` and friends, which hold under
`validateGate`.  The evaluators below make the precondition INTRINSIC: each
returns `none` unless the family's own parameter grammar holds
(`Gates.requirements`, mirroring `gate_ext3.rs:177-385`) AND the actual wire and
constant lists are long enough for it.  Section 4 proves they agree with the
adopted dispatcher whenever they return `some`, so nothing about the adopted
model changes; what is added is the shape lemma. -/

/-- The source's two size obligations from `gate_ext3.rs:393-407`, applied to the
ACTUAL lists: `required_wires <= num_wires` and
`num_selectors + required_local_constants <= num_constants`.  The adopted
`Gates.validateGate` states the second with truncated subtraction against the
configuration widths (`Gates.lean:108`); this states it as the source's addition
against the list lengths. -/
def shapeValid (numSelectors : Nat) (r : Requirements) (wires constants : List Ext3) : Prop :=
  r.wires ≤ wires.length ∧ numSelectors + r.localConstants ≤ constants.length

instance (numSelectors : Nat) (r : Requirements) (wires constants : List Ext3) :
    Decidable (shapeValid numSelectors r wires constants) := inferInstanceAs (Decidable (_ ∧ _))

/-- Common guard: the family's parameter grammar, then its size obligations. -/
def guarded (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (output : List Ext3) : Option (List Ext3) :=
  match Gates.requirements g with
  | none => none
  | some r => if shapeValid c.numSelectors r wires constants then some output else none

theorem guarded_value (c : Gates.Config) (g : GateInfo) (wires constants output : List Ext3)
    (r : Requirements) (hr : Gates.requirements g = some r)
    (hs : shapeValid c.numSelectors r wires constants) :
    guarded c g wires constants output = some output := by
  simp [guarded, hr, hs]

theorem guarded_is_some (c : Gates.Config) (g : GateInfo) (wires constants output : List Ext3) :
    (guarded c g wires constants output).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants := by
  unfold guarded
  cases Gates.requirements g with
  | none => simp
  | some r =>
    by_cases hs : shapeValid c.numSelectors r wires constants
    · simp [hs]
    · simp [hs]

theorem guarded_output (c : Gates.Config) (g : GateInfo) (wires constants output terms : List Ext3)
    (h : guarded c g wires constants output = some terms) : terms = output := by
  unfold guarded at h
  cases hr : Gates.requirements g with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some r =>
    rw [hr] at h
    by_cases hs : shapeValid c.numSelectors r wires constants
    · simpa [hs, eq_comm] using h
    · simp [hs] at h

/-- Id 0, `NoopGate`: no constraints.  `gate_ext3.rs:179-182` declares
`(0, 0, 0)`; `gate_ext3.rs:660` emits nothing. -/
def evaluateNoop (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) := guarded c g wires constants []

/-- Id 1, `ConstantGate`: `constants[i] - wires[i]` for `i < num_or_consts`.
Source `gate_ext3.rs:718-722` (`eval_constant`), called at 661-666 with the
local constants, i.e. the slice AFTER the selectors (`gate_ext3.rs:658`). -/
def evaluateConstant (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants (Gates.evalConstant wires constants c.numSelectors g.numOrConsts)

/-- Id 2, `PublicInputGate`: `wires[i] - public_hash[i]` for `i < 4`.
Source `gate_ext3.rs:724-728` (`eval_public_input`). -/
def evaluatePublicInput (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) : Option (List Ext3) :=
  guarded c g wires constants (Gates.evalPublicInput wires publicHash)

/-- Id 3, `ArithmeticGate`: `wires[4i+3] - (c0*wires[4i]*wires[4i+1] +
c1*wires[4i+2])`.  Source `gate_ext3.rs:730-738` (`eval_arithmetic`). -/
def evaluateArithmetic (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants (Gates.evalArithmetic wires constants c.numSelectors g.numOrConsts)

/-- Id 4, `PoseidonGate`: the 123-constraint full/partial round schedule over
135 wires.  Source `gate_ext3.rs:807-875` (`eval_poseidon`); the adopted Lean
transcription is `Poseidon.evalPoseidon`. -/
def evaluatePoseidon (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) := guarded c g wires constants (Poseidon.evalPoseidon wires)

/-- Id 5, `PoseidonMdsGate`: 24 linear MDS constraints over 48 wires (two lanes
of the inner quadratic extension, twelve rows each).  Source
`gate_ext3.rs:877-894` (`eval_poseidon_mds`). -/
def evaluatePoseidonMds (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) := guarded c g wires constants (Poseidon.evalPoseidonMds wires)

/-- Id 6, `ArithmeticExtensionGate`: per operation `i`, the inner-Ext2 identity
`out - (a*b*c0 + addend*c1)` split into its two coordinates.  Source
`gate_ext3.rs:896-909` (`eval_arithmetic_extension`); the inner nonresidue is 7. -/
def evaluateArithmeticExtension (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants
    (Gates.evalArithmeticExtension wires constants c.numSelectors g.numOrConsts)

/-- Id 7, `MulExtensionGate`: per operation `i`, `out - a*b*c0` split into its
two inner coordinates.  Source `gate_ext3.rs:911-921` (`eval_mul_extension`). -/
def evaluateMulExtension (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants
    (Gates.evalMulExtension wires constants c.numSelectors g.numOrConsts)

/-- Id 8, `ExponentiationGate`: `bits` square-and-multiply steps
`previous * (bit*base + (1 - bit)) - wires[2+bits+i]`, high bit first, then one
output constraint `wires[1+bits] - wires[2+2*bits-1]`.  Source
`gate_ext3.rs:923-937` (`eval_exponentiation`). -/
def evaluateExponentiation (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants (GatesAdditional.evalExponentiation wires g.numOrConsts)

/-- Id 9, `BaseSumGate`: the recomposition constraint
`sum(limb_i * base^i) - wires[0]` followed by one range product
`prod_{v<base} (limb - v)` per limb.  Source `gate_ext3.rs:939-953`
(`eval_base_sum`).  The base grammar is `gate_ext3.rs:243-256`. -/
def evaluateBaseSum (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants (GatesAdditional.evalBaseSum wires g.numOrConsts g.param2)

/-- Id 10, `ReducingGate`: the Horner recurrence
`accumulator*alpha + coefficient - next` over inner-Ext2 pairs, with base-field
coefficients.  Source `gate_ext3.rs:955-987` (`eval_reducing`, called at 695
with `extension_coefficients = false`). -/
def evaluateReducing (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants (GatesAdditional.evalReducing wires g.numOrConsts false)

/-- Id 11, `ReducingExtensionGate`: the same recurrence with inner-Ext2
coefficients.  Source `gate_ext3.rs:955-987` called at 696 with
`extension_coefficients = true`. -/
def evaluateReducingExtension (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants (GatesAdditional.evalReducing wires g.numOrConsts true)

/-- Id 12, `RandomAccessGate`: per copy, `bits` booleanity constraints
`b*(b-1)`, one index-reconstruction constraint, and one selection constraint
from the adjacent-difference butterfly; then `extra` constant-copy constraints.
Source `gate_ext3.rs:989-1029` (`eval_random_access`). -/
def evaluateRandomAccess (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  guarded c g wires constants
    (GatesAdditional.evalRandomAccess wires constants c.numSelectors g.numOrConsts g.param2 g.param3)

/-- Id 13, `CosetInterpolationGate`: the chunked barycentric interpolation over
the two-adic subgroup of size `2^subgroup_bits`, with `4 + 4*intermediates`
constraints.  Source `gate_ext3.rs:1031-1101` and the shape at 321-383.  The
adopted transcription already carries its own layout guard
(`GatesAdditionalCoset.evaluate`), which is kept here INSIDE the shape guard. -/
def evaluateCosetInterpolation (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    Option (List Ext3) :=
  match Gates.requirements g with
  | none => none
  | some r =>
      if shapeValid c.numSelectors r wires constants then
        GatesAdditionalCoset.evaluate
          (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2))
          g.numOrConsts g.param2
      else none

/-! ## 4. Per-family shape lemmas and constraint counts

For each family: `some` EXACTLY when the family's parameter grammar holds and
both lists are long enough, and then the emitted list has exactly the length the
source declares (`declaredConstraints`, i.e. `expected_constraints` of
`gate_ext3.rs:177-385`).  The count is proved against the EVALUATOR's own output,
so it is not the metadata being compared with itself. -/

theorem noop_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateNoop c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants []

theorem noop_constraint_count (c : Gates.Config) (g : GateInfo) (wires constants out : List Ext3)
    (hid : g.gateId = 0) (h : evaluateNoop c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants [] out h
  subst hv
  simp [declaredConstraints, hid]

theorem constant_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateConstant c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem constant_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 1)
    (h : evaluateConstant c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, Gates.evalConstant, Gates.range_length]

theorem public_input_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) :
    (evaluatePublicInput c g wires constants publicHash).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem public_input_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (publicHash : Nat → Base) (hid : g.gateId = 2)
    (h : evaluatePublicInput c g wires constants publicHash = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, Gates.evalPublicInput, Gates.range_length]

theorem arithmetic_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateArithmetic c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem arithmetic_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 3)
    (h : evaluateArithmetic c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, Gates.evalArithmetic, Gates.range_length]

theorem poseidon_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluatePoseidon c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem poseidon_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 4)
    (h : evaluatePoseidon c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, Poseidon.poseidon_constraint_count]

theorem poseidon_mds_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluatePoseidonMds c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem poseidon_mds_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 5)
    (h : evaluatePoseidonMds c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, Poseidon.mds_constraint_count]

theorem arithmetic_extension_shape (c : Gates.Config) (g : GateInfo)
    (wires constants : List Ext3) :
    (evaluateArithmeticExtension c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem arithmetic_extension_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 6)
    (h : evaluateArithmeticExtension c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid,
    (Gates.extension_constraint_lengths wires constants c.numSelectors g.numOrConsts).1]

theorem mul_extension_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateMulExtension c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem mul_extension_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 7)
    (h : evaluateMulExtension c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid,
    (Gates.extension_constraint_lengths wires constants c.numSelectors g.numOrConsts).2]

theorem exponentiation_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateExponentiation c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem exponentiation_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 8)
    (h : evaluateExponentiation c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, GatesAdditional.exponentiation_output_length]

theorem base_sum_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateBaseSum c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem base_sum_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 9)
    (h : evaluateBaseSum c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, GatesAdditional.base_sum_output_length]

theorem reducing_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateReducing c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem reducing_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 10)
    (h : evaluateReducing c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, GatesAdditional.reducing_output_length]

theorem reducing_extension_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateReducingExtension c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem reducing_extension_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 11)
    (h : evaluateReducingExtension c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, GatesAdditional.reducing_output_length]

theorem random_access_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3) :
    (evaluateRandomAccess c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants :=
  guarded_is_some c g wires constants _

theorem random_access_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 12)
    (h : evaluateRandomAccess c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hv := guarded_output c g wires constants _ out h
  subst hv
  simp [declaredConstraints, hid, GatesAdditional.random_access_output_length]

/-- The coset family's own layout guard is IMPLIED by the shape guard: the
parameter grammar of `gate_ext3.rs:321-340` gives the subgroup-bit and degree
ranges, the size obligation gives the wire prefix length, and the weight table's
canonicity is the adopted `GatesAdditionalCoset.weight_zero_canonical`. -/
theorem coset_layout_of_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (r : Requirements) (hid : g.gateId = 13) (hr : Gates.requirements g = some r)
    (hs : shapeValid c.numSelectors r wires constants) :
    GatesAdditionalCoset.layoutValid
      (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2))
      g.numOrConsts g.param2 := by
  simp only [Gates.requirements, hid] at hr
  split at hr
  · rename_i hp
    simp only [Option.some.injEq] at hr
    subst hr
    have hbits : 1 ≤ g.numOrConsts ∧ g.numOrConsts ≤ 5 := by omega
    have hreq := hs.1
    simp only at hreq
    have hwidth : GatesAdditionalCoset.wireCount g.numOrConsts g.param2 ≤ wires.length := by
      unfold GatesAdditionalCoset.wireCount GatesAdditionalCoset.shiftedPointIndex
        GatesAdditionalCoset.intermediateStart GatesAdditionalCoset.intermediates
        GatesAdditionalCoset.points
      omega
    exact ⟨hbits.1, hbits.2, hp.2.2.2.1, hp.2.2.2.2, List.length_take_of_le hwidth,
      GatesAdditionalCoset.weight_zero_canonical _ hbits⟩
  · simp at hr

theorem coset_interpolation_output (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3)
    (h : evaluateCosetInterpolation c g wires constants = some out) :
    GatesAdditionalCoset.evaluate
      (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2))
      g.numOrConsts g.param2 = some out := by
  unfold evaluateCosetInterpolation at h
  cases hr : Gates.requirements g with
  | none => simp only [hr] at h
  | some r =>
    simp only [hr] at h
    by_cases hs : shapeValid c.numSelectors r wires constants
    · rwa [if_pos hs] at h
    · rw [if_neg hs] at h; exact absurd h (by simp)

theorem coset_rejects_bad_parameters (c : Gates.Config) (g : GateInfo)
    (wires constants : List Ext3) (hr : Gates.requirements g = none) :
    evaluateCosetInterpolation c g wires constants = none := by
  simp [evaluateCosetInterpolation, hr]

theorem coset_rejects_bad_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (r : Requirements) (hr : Gates.requirements g = some r)
    (hs : ¬ shapeValid c.numSelectors r wires constants) :
    evaluateCosetInterpolation c g wires constants = none := by
  simp [evaluateCosetInterpolation, hr, hs]

theorem coset_accepts_valid_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (r : Requirements) (hid : g.gateId = 13) (hr : Gates.requirements g = some r)
    (hs : shapeValid c.numSelectors r wires constants) :
    evaluateCosetInterpolation c g wires constants =
      some (GatesAdditionalCoset.evaluateUnchecked
        (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2))
        g.numOrConsts g.param2) := by
  simp [evaluateCosetInterpolation, hr, hs, GatesAdditionalCoset.evaluate,
    coset_layout_of_shape c g wires constants r hid hr hs]

theorem coset_interpolation_shape (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (hid : g.gateId = 13) :
    (evaluateCosetInterpolation c g wires constants).isSome = true ↔
      ∃ r, Gates.requirements g = some r ∧ shapeValid c.numSelectors r wires constants := by
  constructor
  · intro h
    cases hr : Gates.requirements g with
    | none =>
      rw [coset_rejects_bad_parameters c g wires constants hr] at h
      exact absurd h (by simp)
    | some r =>
      by_cases hs : shapeValid c.numSelectors r wires constants
      · exact ⟨r, rfl, hs⟩
      · rw [coset_rejects_bad_shape c g wires constants r hr hs] at h
        exact absurd h (by simp)
  · rintro ⟨r, hr, hs⟩
    rw [coset_accepts_valid_shape c g wires constants r hid hr hs]
    rfl

theorem coset_interpolation_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (hid : g.gateId = 13)
    (h : evaluateCosetInterpolation c g wires constants = some out) :
    out.length = declaredConstraints g := by
  have hc := (GatesAdditionalCoset.evaluated_length_and_layout _ out g.numOrConsts g.param2
    (coset_interpolation_output c g wires constants out h)).2
  simpa [declaredConstraints, hid, GatesAdditionalCoset.constraintCount,
    GatesAdditionalCoset.intermediates, GatesAdditionalCoset.points] using hc

/-! ## 5. The extended combined evaluator -/

/-- Dispatch on the gate id, exactly as `gate_ext3.rs:659-714` does, but through
the shape-checked family evaluators.  Ids `14` and above return `none`, matching
the source's `unsupported => bail!` at `gate_ext3.rs:713` and `384`. -/
def evaluateGateFull (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) : Option (List Ext3) :=
  match g.gateId with
  | 0 => evaluateNoop c g wires constants
  | 1 => evaluateConstant c g wires constants
  | 2 => evaluatePublicInput c g wires constants publicHash
  | 3 => evaluateArithmetic c g wires constants
  | 4 => evaluatePoseidon c g wires constants
  | 5 => evaluatePoseidonMds c g wires constants
  | 6 => evaluateArithmeticExtension c g wires constants
  | 7 => evaluateMulExtension c g wires constants
  | 8 => evaluateExponentiation c g wires constants
  | 9 => evaluateBaseSum c g wires constants
  | 10 => evaluateReducing c g wires constants
  | 11 => evaluateReducingExtension c g wires constants
  | 12 => evaluateRandomAccess c g wires constants
  | 13 => evaluateCosetInterpolation c g wires constants
  | _ => none

theorem unknown_gate_not_evaluated (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (hk : 14 ≤ g.gateId) :
    evaluateGateFull c g wires constants publicHash = none := by
  obtain ⟨n, hn⟩ : ∃ n, g.gateId = n + 14 := ⟨g.gateId - 14, by omega⟩
  simp [evaluateGateFull, hn]

/-- Whenever the extended evaluator produces a list, the ADOPTED dispatcher
produces the same list.  The extension therefore strengthens the adopted model:
it rejects strictly more inputs and changes no accepted value. -/
theorem extended_agrees_with_complete_dispatcher (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (publicHash : Nat → Base) (hk : g.gateId < 14)
    (h : evaluateGateFull c g wires constants publicHash = some out) :
    GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors = some out := by
  by_cases h13 : g.gateId = 13
  · simp only [evaluateGateFull, h13] at h
    simpa [GatesComplete.evaluateUnfiltered, GatesAdditional.dispatchUnchecked, h13] using
      coset_interpolation_output c g wires constants out h
  · have hid : g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨ g.gateId = 4 ∨
        g.gateId = 5 ∨ g.gateId = 6 ∨ g.gateId = 7 ∨ g.gateId = 8 ∨ g.gateId = 9 ∨
        g.gateId = 10 ∨ g.gateId = 11 ∨ g.gateId = 12 := by omega
    rcases hid with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg <;>
      · simp only [evaluateGateFull, evaluateNoop, evaluateConstant, evaluatePublicInput,
          evaluateArithmetic, evaluatePoseidon, evaluatePoseidonMds,
          evaluateArithmeticExtension, evaluateMulExtension, evaluateExponentiation,
          evaluateBaseSum, evaluateReducing, evaluateReducingExtension, evaluateRandomAccess,
          hg] at h
        have hv := guarded_output c g wires constants _ out h
        subst hv
        simp [GatesComplete.evaluateUnfiltered, GatesAdditional.dispatchUnchecked,
          Gates.evaluateUnfiltered, hg]

/-- On the six ids the PARTIAL adopted evaluator covers, the extension is that
evaluator under the shape guard: same list, or `none` when the shape fails. -/
theorem extended_agrees_on_covered_ids (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (publicHash : Nat → Base)
    (hk : partialCovered g.gateId = true)
    (h : evaluateGateFull c g wires constants publicHash = some out) :
    Gates.evaluateUnfiltered g wires constants publicHash c.numSelectors = some out := by
  have hid : g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨
      g.gateId = 6 ∨ g.gateId = 7 := by
    simpa [partialCovered] using hk
  rcases hid with hg | hg | hg | hg | hg | hg <;>
    · simp only [evaluateGateFull, evaluateNoop, evaluateConstant, evaluatePublicInput,
        evaluateArithmetic, evaluateArithmeticExtension, evaluateMulExtension, hg] at h
      have hv := guarded_output c g wires constants _ out h
      subst hv
      simp [Gates.evaluateUnfiltered, hg]

/-! ## 6. The extended evaluator under the adopted configuration check -/

/-- A row that passes the adopted `Gates.validateGate`, in a configuration whose
selector block fits inside its constant block, satisfies the shape guard on
lists of the configured widths.  The extension therefore never rejects an input
the adopted configured path accepts. -/
theorem validated_shape (c : Gates.Config) (row total : Nat) (g : GateInfo) (r : Requirements)
    (wires constants : List Ext3) (hv : Gates.validateGate c row total g = some r)
    (hsel : c.numSelectors ≤ c.numConstants)
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    shapeValid c.numSelectors r wires constants := by
  have h := Gates.validate_gate_success c row total g r hv
  exact ⟨by have := h.2.2.2.2.2.1; omega, by have := h.2.2.2.2.2.2.1; omega⟩

theorem validated_full_evaluation_exists (c : Gates.Config) (row total : Nat) (g : GateInfo)
    (r : Requirements) (wires constants : List Ext3) (publicHash : Nat → Base)
    (hv : Gates.validateGate c row total g = some r) (hsel : c.numSelectors ≤ c.numConstants)
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    ∃ out, evaluateGateFull c g wires constants publicHash = some out := by
  have hk := (Gates.validate_gate_success c row total g r hv).2.2.1
  have hr := (Gates.validate_gate_success c row total g r hv).2.2.2.1
  have hs := validated_shape c row total g r wires constants hv hsel hw hc
  have hex : ∃ req, Gates.requirements g = some req ∧
      shapeValid c.numSelectors req wires constants := ⟨r, hr, hs⟩
  have hsome : (evaluateGateFull c g wires constants publicHash).isSome = true := by
    have hid : g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨ g.gateId = 4 ∨
        g.gateId = 5 ∨ g.gateId = 6 ∨ g.gateId = 7 ∨ g.gateId = 8 ∨ g.gateId = 9 ∨
        g.gateId = 10 ∨ g.gateId = 11 ∨ g.gateId = 12 ∨ g.gateId = 13 := by omega
    rcases hid with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg <;>
      simp only [evaluateGateFull, hg]
    · exact (noop_shape c g wires constants).mpr hex
    · exact (constant_shape c g wires constants).mpr hex
    · exact (public_input_shape c g wires constants publicHash).mpr hex
    · exact (arithmetic_shape c g wires constants).mpr hex
    · exact (poseidon_shape c g wires constants).mpr hex
    · exact (poseidon_mds_shape c g wires constants).mpr hex
    · exact (arithmetic_extension_shape c g wires constants).mpr hex
    · exact (mul_extension_shape c g wires constants).mpr hex
    · exact (exponentiation_shape c g wires constants).mpr hex
    · exact (base_sum_shape c g wires constants).mpr hex
    · exact (reducing_shape c g wires constants).mpr hex
    · exact (reducing_extension_shape c g wires constants).mpr hex
    · exact (random_access_shape c g wires constants).mpr hex
    · exact (coset_interpolation_shape c g wires constants hg).mpr hex
  exact Option.isSome_iff_exists.mp hsome

/-- The count the EVALUATOR emits is the count the SOURCE declares, for every
one of the fourteen families, without going through the metadata's own
self-consistency check. -/
theorem full_evaluation_constraint_count (c : Gates.Config) (g : GateInfo)
    (wires constants out : List Ext3) (publicHash : Nat → Base) (hk : g.gateId < 14)
    (h : evaluateGateFull c g wires constants publicHash = some out) :
    out.length = declaredConstraints g := by
  have hid : g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨ g.gateId = 4 ∨
      g.gateId = 5 ∨ g.gateId = 6 ∨ g.gateId = 7 ∨ g.gateId = 8 ∨ g.gateId = 9 ∨
      g.gateId = 10 ∨ g.gateId = 11 ∨ g.gateId = 12 ∨ g.gateId = 13 := by omega
  rcases hid with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg <;>
    simp only [evaluateGateFull, hg] at h
  · exact noop_constraint_count c g wires constants out hg h
  · exact constant_constraint_count c g wires constants out hg h
  · exact public_input_constraint_count c g wires constants out publicHash hg h
  · exact arithmetic_constraint_count c g wires constants out hg h
  · exact poseidon_constraint_count c g wires constants out hg h
  · exact poseidon_mds_constraint_count c g wires constants out hg h
  · exact arithmetic_extension_constraint_count c g wires constants out hg h
  · exact mul_extension_constraint_count c g wires constants out hg h
  · exact exponentiation_constraint_count c g wires constants out hg h
  · exact base_sum_constraint_count c g wires constants out hg h
  · exact reducing_constraint_count c g wires constants out hg h
  · exact reducing_extension_constraint_count c g wires constants out hg h
  · exact random_access_constraint_count c g wires constants out hg h
  · exact coset_interpolation_constraint_count c g wires constants out hg h

/-! ## 7. The 123 envelope across all fourteen families -/

/-- Every CONFIGURED row's declared and emitted constraint count is at most
`123`.  The bound comes from `Gates.envelope`'s `numGateConstraints <= 123`
(`Plonky2GateEvaluatorExt3.sol:174`, `MAX_GATE_CONSTRAINTS`) together with
`validateRows`' exact-maximum equality, so it holds for EVERY family without a
per-family argument. -/
theorem configured_row_constraints_at_most_123 (c : Gates.Config) (gates : List GateInfo)
    (i : Nat) (g : GateInfo) (hv : Gates.validateConfiguration c gates = some ())
    (hg : gates.get? i = some g) :
    g.numConstraints ≤ c.numGateConstraints ∧ c.numGateConstraints ≤ 123 ∧
      g.numConstraints ≤ 123 ∧ declaredConstraints g ≤ 123 := by
  obtain ⟨r, hvg, hb⟩ := Gates.every_configured_gate_checked c gates hv i g hg
  have hs := Gates.validate_gate_success c i gates.length g r hvg
  have henv := (Gates.validate_configuration_success c gates hv).1
  simp only [Gates.envelope] at henv
  have := declared_tables_match_adopted_requirements g r hs.2.2.1 hs.2.2.2.1
  have := hs.2.2.2.2.1
  exact ⟨by omega, henv.2.2.1, by omega, by omega⟩

/-- The `123` cap is a CONFIGURATION-level fact, not a per-row one.  This
`RandomAccessGate` row declares `18 * (1 + 2) + 70 = 124` constraints and passes
the per-row `Gates.validateGate` at the widest admissible configuration
(`160` wires, `160` constants, quotient degree `8`). -/
def overflowingRandomAccessRow : GateInfo := ⟨12, 0, 0, 1, 0, 124, 1, 18, 70⟩

/-- The widest configuration the envelope allows. -/
def widestConfig : Gates.Config := ⟨1, 160, 123, 160, 8⟩

theorem overflowing_row_passes_per_row_validation :
    Gates.validateGate widestConfig 0 1 overflowingRandomAccessRow = some ⟨124, 160, 70, 2⟩ ∧
      declaredConstraints overflowingRandomAccessRow = 124 ∧
      declaredWires overflowingRandomAccessRow = 160 := by decide

/-- ... and is nevertheless unconfigurable: no envelope-valid configuration can
contain it, because `validateRows` forces `numGateConstraints` to be the exact
maximum and the envelope caps that at `123`. -/
theorem overflowing_row_is_unconfigurable (c : Gates.Config) (gates : List GateInfo) (i : Nat)
    (hv : Gates.validateConfiguration c gates = some ())
    (hg : gates.get? i = some overflowingRandomAccessRow) : False := by
  have h := configured_row_constraints_at_most_123 c gates i overflowingRandomAccessRow hv hg
  simp only [overflowingRandomAccessRow] at h
  omega

/-- The declared degree of `BaseSumGate` is its BASE
(`Plonky2GateEvaluatorExt3.sol:206-208`), and the degree accounting caps it at
`quotientDegreeFactor + 1 <= 9`.  The Rust grammar at `gate_ext3.rs:246-249`
allows bases `16, 32, 64, 128, 256` as well, but no envelope-valid configuration
can use them: only bases `2..8` survive. -/
theorem base_sum_only_small_bases_are_configurable (c : Gates.Config) (row total : Nat)
    (g : GateInfo) (r : Requirements) (hv : Gates.validateGate c row total g = some r)
    (hid : g.gateId = 9) (hq : c.quotientDegree ≤ 8) :
    g.param3 = 0 ∧ 2 ≤ g.param2 ∧ g.param2 ≤ 8 := by
  have h := Gates.validate_gate_success c row total g r hv
  have hr := h.2.2.2.1
  have hdeg := h.2.2.2.2.2.2.2
  simp only [Gates.requirements, hid] at hr
  split at hr
  · rename_i hp
    simp only [Option.some.injEq] at hr
    subst hr
    simp only at hdeg
    simp only [Bool.and_eq_true, decide_eq_true_eq, Gates.supportedBase] at hp
    omega
  · simp at hr

/-- The declared degree table is inside the envelope's degree accounting for
every configured row, and is therefore at most `9` for every family. -/
theorem configured_declared_degree_bound (c : Gates.Config) (row total : Nat) (g : GateInfo)
    (r : Requirements) (hv : Gates.validateGate c row total g = some r)
    (hq : c.quotientDegree ≤ 8) :
    declaredDegree g + Gates.filterDegree c g ≤ c.quotientDegree + 1 ∧ declaredDegree g ≤ 9 := by
  have h := Gates.validate_gate_success c row total g r hv
  have := declared_tables_match_adopted_requirements g r h.2.2.1 h.2.2.2.1
  have := h.2.2.2.2.2.2.2
  exact ⟨by omega, by omega⟩

/-! ## 8. Degree in the wires, for all fourteen families -/

/-- Every family's constraint polynomials have degree at most the DECLARED
degree of `_unfilteredDegree`, in the affine wire and constant columns.  The
polynomial content is the adopted
`GateAllPolynomial.all_validated_polynomial_degrees` -- which already covers all
fourteen families, the nonlinear Poseidon one through
`GatePoseidonPolynomial.poseidon_degree` and the coset one through
`GateCosetPolynomial.coset_degree`; what is added here is that the bound it
states, `r.degree`, is exactly the Solidity-declared table entry. -/
theorem family_polynomial_degree_is_declared (c : Gates.Config) (row total : Nat)
    (g : GateInfo) (r : Requirements) (wires constants terms : List GatePolynomial.P)
    (publicHash : Nat → Base)
    (hv : Gates.validateGate c row total g = some r)
    (hp : GateAllPolynomial.unfilteredPolys g wires constants publicHash c.numSelectors
      = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ terms, p.natDegree ≤ declaredDegree g := by
  have h := Gates.validate_gate_success c row total g r hv
  have := declared_tables_match_adopted_requirements g r h.2.2.1 h.2.2.2.1
  intro p hpm
  have := GateAllPolynomial.all_validated_polynomial_degrees c row total g r wires constants
    terms publicHash hv hp hw hc p hpm
  omega

/-! ## 9. The alpha-Horner aggregate is family-agnostic

`AlphaZeroCheck`'s per-row aggregate degree bound does NOT depend on any
per-family fact.  Its coefficient list is the source's
`vec![ZERO; num_gate_constraints]` slot buffer (`gate_ext3.rs:570`), its length
is `c.numGateConstraints` alone, and the root bound
`natDegree <= c.numGateConstraints - 1` follows from that length.  The one place
the gate families enter is `AlphaZeroCheck.filteredValue`, which reads the
COMPLETE dispatcher; the theorem below shows the extended evaluator produces the
same filtered value at every configured row, so every slot coefficient, the
aggregate polynomial, and its degree and root bounds are unchanged. -/

def filteredValueFull (c : Gates.Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (k : Nat) : GoldilocksExt3Field.Element :=
  match evaluateGateFull c g wires constants publicHash with
  | some terms =>
      GateSlotCommutation.rowFilter c g constants * (GateSlotAlgebra.wrap terms).getD k 0
  | none => 0

theorem full_evaluator_keeps_filtered_values (c : Gates.Config) (row total : Nat) (g : GateInfo)
    (r : Requirements) (wires constants : List Ext3) (publicHash : Nat → Base) (k : Nat)
    (hv : Gates.validateGate c row total g = some r) (hsel : c.numSelectors ≤ c.numConstants)
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    filteredValueFull c g wires constants publicHash k =
      AlphaZeroCheck.filteredValue c g wires constants publicHash k := by
  obtain ⟨out, hout⟩ := validated_full_evaluation_exists c row total g r wires constants
    publicHash hv hsel hw hc
  have hk := (Gates.validate_gate_success c row total g r hv).2.2.1
  have hagree := extended_agrees_with_complete_dispatcher c g wires constants out publicHash hk hout
  simp only [filteredValueFull, AlphaZeroCheck.filteredValue, hout, hagree]

/-- The slot-coefficient identification and the alpha root bound, restated for
the extended evaluator.  The first four conjuncts are the adopted
`AlphaZeroCheck.aggregate_is_polynomial_in_alpha` and
`configured_alphaBadSet_card_bound` content; the last is the transfer. -/
theorem extended_alpha_horner_degree (c : Gates.Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base)
    (hv : Gates.validateConfiguration c gates = some ())
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    ∃ coeffs, AlphaZeroCheck.slotCoefficients c gates wires constants publicHash = some coeffs ∧
      coeffs.length = c.numGateConstraints ∧
      (WhirPolynomial.ofCoefficients coeffs).natDegree ≤ c.numGateConstraints - 1 ∧
      c.numGateConstraints ≤ 123 ∧
      ∀ i g, gates.get? i = some g → ∀ k,
        filteredValueFull c g wires constants publicHash k =
          AlphaZeroCheck.filteredValue c g wires constants publicHash k := by
  obtain ⟨coeffs, hcoeffs, hlen, -, hdeg, -⟩ :=
    AlphaZeroCheck.aggregate_is_polynomial_in_alpha c gates wires constants publicHash hv hw hc
  have henv := (Gates.validate_configuration_success c gates hv).1
  simp only [Gates.envelope] at henv
  refine ⟨coeffs, hcoeffs, hlen, hdeg, henv.2.2.1, ?_⟩
  intro i g hg k
  obtain ⟨r, hvg, -⟩ := Gates.every_configured_gate_checked c gates hv i g hg
  exact full_evaluator_keeps_filtered_values c i gates.length g r wires constants publicHash k
    hvg henv.2.2.2.2.1 hw hc

/-! ## 9b. Interface compatibility with the adopted consumers -/

/-- On a validated row at the configured widths the extended evaluator is
LITERALLY the adopted dispatcher.  Every adopted consumer -- `GatesComplete`'s
`contribution` / `combineRows` / `evalCombined`, `Integrated.evaluateGate`,
`GateSlotCommutation.slotRows`, `GateDenseRound` and
`AlphaZeroCheck.filteredValue` -- is defined by matching on that dispatcher, so
substituting `evaluateGateFull` for it changes nothing they compute. -/
theorem validated_full_evaluator_agrees (c : Gates.Config) (row total : Nat) (g : GateInfo)
    (r : Requirements) (wires constants : List Ext3) (publicHash : Nat → Base)
    (hv : Gates.validateGate c row total g = some r) (hsel : c.numSelectors ≤ c.numConstants)
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    evaluateGateFull c g wires constants publicHash =
      GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors := by
  obtain ⟨out, hout⟩ := validated_full_evaluation_exists c row total g r wires constants
    publicHash hv hsel hw hc
  have hk := (Gates.validate_gate_success c row total g r hv).2.2.1
  rw [hout, extended_agrees_with_complete_dispatcher c g wires constants out publicHash hk hout]

theorem validated_contribution_via_full_evaluator (c : Gates.Config) (row total : Nat)
    (g : GateInfo) (r : Requirements) (wires constants : List Ext3) (publicHash : Nat → Base)
    (alpha : Ext3) (hv : Gates.validateGate c row total g = some r)
    (hsel : c.numSelectors ≤ c.numConstants)
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    GatesComplete.contribution c g wires constants publicHash alpha =
      (if Gates.computeFilter g (Gates.readValue constants g.selectorIndex)
            (decide (1 < c.numSelectors)) = zero then some zero
        else do
          let terms ← evaluateGateFull c g wires constants publicHash
          if terms.length = g.numConstraints then
            some (mul (Gates.computeFilter g (Gates.readValue constants g.selectorIndex)
              (decide (1 < c.numSelectors))) (Gates.horner terms alpha))
          else none) := by
  rw [validated_full_evaluator_agrees c row total g r wires constants publicHash hv hsel hw hc]
  rfl

/-- The emitted constraint count of every CONFIGURED row is the declared count,
the declared metadata count, and is inside the `123` envelope. -/
theorem full_evaluation_length_within_envelope (c : Gates.Config) (gates : List GateInfo)
    (i : Nat) (g : GateInfo) (wires constants out : List Ext3) (publicHash : Nat → Base)
    (hv : Gates.validateConfiguration c gates = some ()) (hg : gates.get? i = some g)
    (h : evaluateGateFull c g wires constants publicHash = some out) :
    out.length = declaredConstraints g ∧ out.length = g.numConstraints ∧
      out.length ≤ c.numGateConstraints ∧ out.length ≤ 123 := by
  obtain ⟨r, hvg, -⟩ := Gates.every_configured_gate_checked c gates hv i g hg
  have hs := Gates.validate_gate_success c i gates.length g r hvg
  have hcount := full_evaluation_constraint_count c g wires constants out publicHash hs.2.2.1 h
  have := declared_tables_match_adopted_requirements g r hs.2.2.1 hs.2.2.2.1
  have := hs.2.2.2.2.1
  have := configured_row_constraints_at_most_123 c gates i g hv hg
  exact ⟨hcount, by omega, by omega, by omega⟩

/-! ## 10. The coverage table -/

/-- One row of the before/after coverage table.  `partialEvaluator` is
`Gates.evaluateUnfiltered`, `completeDispatcher` is
`GatesComplete.evaluateUnfiltered`, `polynomialBridge` is
`GateAllPolynomial.unfilteredPolys`, `shapeCheckedBefore` records whether the
ADOPTED model rejects a wrongly-sized input for that family, and
`shapeCheckedNow` records the same for `evaluateGateFull`. -/
structure Coverage where
  gateId : Nat
  partialEvaluator : Bool
  completeDispatcher : Bool
  polynomialBridge : Bool
  shapeCheckedBefore : Bool
  shapeCheckedNow : Bool
  deriving DecidableEq

def coverageTable : List Coverage :=
  [⟨0, true, true, true, false, true⟩, ⟨1, true, true, true, false, true⟩,
   ⟨2, true, true, true, false, true⟩, ⟨3, true, true, true, false, true⟩,
   ⟨4, false, true, true, false, true⟩, ⟨5, false, true, true, false, true⟩,
   ⟨6, true, true, true, false, true⟩, ⟨7, true, true, true, false, true⟩,
   ⟨8, false, true, true, false, true⟩, ⟨9, false, true, true, false, true⟩,
   ⟨10, false, true, true, false, true⟩, ⟨11, false, true, true, false, true⟩,
   ⟨12, false, true, true, false, true⟩, ⟨13, false, true, true, true, true⟩]

theorem coverage_table_columns :
    coverageTable.map Coverage.gateId = List.range 14 ∧
    coverageTable.all (fun row => row.partialEvaluator == partialCovered row.gateId) = true ∧
    coverageTable.all (fun row => row.completeDispatcher) = true ∧
    coverageTable.all (fun row => row.polynomialBridge) = true ∧
    coverageTable.all (fun row => row.shapeCheckedBefore == decide (row.gateId = 13)) = true ∧
    coverageTable.all (fun row => row.shapeCheckedNow) = true := by decide

/-- The baseline, in one statement.  The partial evaluator covers exactly the
six ids of the review note; the complete dispatcher covers all fourteen, with
the coset family gated on its layout check and no other family gated at all.
This is the "before" column of the coverage table, PROVED rather than asserted. -/
theorem coverage_status (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (numSelectors : Nat) (hk : g.gateId < 14) :
    (Gates.evaluateUnfiltered g wires constants publicHash numSelectors).isSome =
        partialCovered g.gateId ∧
      (g.gateId ≠ 13 →
        (GatesComplete.evaluateUnfiltered g wires constants publicHash numSelectors).isSome
          = true) ∧
      (g.gateId = 13 →
        ((GatesComplete.evaluateUnfiltered g wires constants publicHash numSelectors).isSome
            = true ↔
          GatesAdditionalCoset.layoutValid
            (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2))
            g.numOrConsts g.param2)) :=
  ⟨partial_evaluator_coverage g wires constants publicHash numSelectors hk,
   fun h13 => complete_dispatcher_below_coset g wires constants publicHash numSelectors
     (by omega),
   fun h13 => complete_dispatcher_coset_shape_checked g wires constants publicHash numSelectors h13⟩

/-! ## 11. Families that are NOT in the fourteen

Plonky2's `LookupGate` and `LookupTableGate` have NO id in this evaluator.
`gate_ext3.rs:384` (`unsupported => bail!`) and Solidity reject every id at or
above `14` outright -- in Solidity at `Plonky2GateEvaluatorExt3.sol:336-337`,
the trailing `else { revert InvalidMleVerifierConfiguration(); }` of
`_validateGate`, and again at `Plonky2GateEvaluatorExt3.sol:211`, the final
`revert` of `_unfilteredDegree` --
and the Rust common-data admission additionally requires zero lookup tables --
the adopted `Gates.rustAdmission` / `Gates.lookup_tables_rejected`.  So the
lookup families are not modelled here because they are not evaluable at all in
this deployment, not because the model stopped short of them; NO lookup table,
challenge or multiset input is invented for them.  The theorem below records
the rejection at this module's own dispatcher. -/
theorem lookup_families_have_no_evaluator (c : Gates.Config) (g : GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (hk : 14 ≤ g.gateId) :
    evaluateGateFull c g wires constants publicHash = none ∧
      Gates.requirements g = none ∧
      ∀ row total : Nat, Gates.validateGate c row total g = none := by
  obtain ⟨n, hn⟩ : ∃ n, g.gateId = n + 14 := ⟨g.gateId - 14, by omega⟩
  exact ⟨unknown_gate_not_evaluated c g wires constants publicHash hk,
    by simp [Gates.requirements, hn],
    fun row total => Gates.unknown_gate_rejected_before_filter c row total g hk⟩

/-! ## 12. Nonvacuity -/

/-- The same concrete arithmetic row the adopted `Gates.arithmetic_full_path_positive`
uses: `c0 * a * b + c1 * addend = 2*5*7 + 3*11 = 103 = out`, so the single
constraint is zero and the shape-checked evaluator returns it. -/
theorem example_full_evaluation_positive :
    evaluateGateFull ⟨1, 3, 1, 4, 2⟩ Gates.exampleArithmetic
        [Gates.embed 5, Gates.embed 7, Gates.embed 11, Gates.embed 103]
        [Gates.embed 0, Gates.embed 2, Gates.embed 3] (fun _ => base 0) = some [zero] := by
  decide

/-- The point of the shape guard: on a wire list too short for the family the
extension returns `none`, where the adopted dispatcher would have returned a
constraint list built from `Gates.readValue`'s default zeros. -/
theorem example_short_wires_rejected :
    evaluateGateFull ⟨1, 3, 1, 4, 2⟩ Gates.exampleArithmetic [Gates.embed 5]
        [Gates.embed 0, Gates.embed 2, Gates.embed 3] (fun _ => base 0) = none ∧
      (GatesComplete.evaluateUnfiltered Gates.exampleArithmetic [Gates.embed 5]
        [Gates.embed 0, Gates.embed 2, Gates.embed 3] (fun _ => base 0) 1).isSome = true := by
  decide

end Audit.Wire3.GateEvaluatorCoverage
