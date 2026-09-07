import Audit.Wire3.Poseidon
import Audit.Wire3.Integrated
import Audit.Wire3.GateTerminalBinding
import Audit.Wire3.IntegratedTerminalChain

/-!
# The concrete public-input hash and the raw canonical preflight

Sources reviewed (snapshot of the reference worktree
`/Users/andropov/repos/intmax-plonky2-lean-wire3`):

* `mle/contracts/src/PoseidonPublicInputsHash.sol` 1-14 -- the external-library
  boundary; `hashNoPad(uint256[] calldata)` forwards to `PoseidonGate.hashNoPad`.
* `mle/contracts/src/PoseidonGate.sol` 29-33 (`P`, `SPONGE_WIDTH = 12`,
  `HALF_N_FULL_ROUNDS = 4`, `N_PARTIAL_ROUNDS = 22`), 53-90 (`hashNoPad`),
  106-126 (`_permuteHashState`), 128-167 (`_partialRoundsHash`).
* `mle/contracts/src/MleVerifierV2.sol` 378-391 -- `publicInputsHash =
  PoseidonPublicInputsHash.hashNoPad(proof.publicInputs)` feeding
  `Plonky2GateEvaluatorExt3.evalCombinedPrevalidated`; 562 (the
  `publicInputs.length != circuit.numPublicInputs` revert); 403 and 634-658
  (`_copyCanonicalBase`, the `count > MAX_PUBLIC_INPUTS_V2` and per-word
  `value < P` reverts).
* `mle/contracts/src/generated/MleWhirV2.sol` 36 -- `MAX_PUBLIC_INPUTS_V2 = 256`.
* `mle/contracts/src/Plonky2GateEvaluatorExt3.sol` 72-95 (`evalCombined`'s own
  four-limb canonical scan) and 97-113 (`evalCombinedPrevalidated`, the entry
  the v2 verifier actually calls).
* `plonky2/src/hash/hashing.rs` 114-145 -- `hash_n_to_m_no_pad` /
  `hash_n_to_hash_no_pad`; `plonky2/src/hash/poseidon.rs` 23-25
  (`SPONGE_RATE = 8`, `SPONGE_CAPACITY = 4`, `SPONGE_WIDTH = 12`), 833-870
  (`PoseidonPermutation`'s `new`/`set_from_slice`/`permute`/`squeeze`),
  878-882 (`PoseidonHash::hash_no_pad`); `plonky2/src/hash/hash_types.rs` 20,
  35-40 (`NUM_HASH_OUT_ELTS = 4`, `HashOut::from_vec`).
* `mle/src/verifier_v2.rs` 232 -- `PoseidonHash::hash_no_pad(&proof.public_inputs)`.

## Solidity / Rust divergences found (stated, not papered over)

1. **Canonical range.** Rust's `proof.public_inputs : Vec<GoldilocksField>` is
   canonical by construction, so `hash_no_pad` performs NO range test.
   Solidity receives `uint256[] calldata` and tests every absorbed word
   (`PoseidonGate.sol` 77-80, `revert InvalidMleProof()`); the v2 verifier
   additionally re-scans the same words in `_copyCanonicalBase`
   (`MleVerifierV2.sol` 634-658, per-word revert 651-654) before absorbing
   them into the transcript. `MleVerifierV2.sol:382` hashes `proof.publicInputs`
   FROM CALLDATA, not that canonical memory copy, so `PoseidonGate.sol:77` is
   what guards the permissionless library entry
   `PoseidonPublicInputsHash.hashNoPad`; inside `verify` it is defence in depth,
   because `_verifyAtomic:305` already ran `_deriveInitialTranscript` ->
   `_copyCanonicalBase` over the same calldata beforehand. The ORDER of the two
   scans is not modelled; `rawPublicInputsHash` conjoins both guards and is
   therefore at least as strict as either site.
   `rawPublicInputsHash` below models the Solidity side as an `Option`.
2. **Public-input count cap.** Solidity caps the vector at
   `MAX_PUBLIC_INPUTS_V2 = 256` inside `_copyCanonicalBase`; Rust has no such
   cap (its bound is the circuit's `num_public_inputs` equality check only).
   Modelled as `rawPublicInputsValid`'s length conjunct.
3. **Trailing zero partial round constant (a MODEL, not a source,
   difference).** `PoseidonGate.sol::_partialRoundsHash` 143-160 and
   `poseidon.rs::partial_rounds` 752-764 BOTH add
   `FAST_PARTIAL_ROUND_CONSTANTS[i]` unconditionally for all 22 rounds; they do
   not diverge. The adopted Lean `Poseidon.partialSboxValue` skips it in round
   21, and the adopted `Poseidon.partial_step_matches_rust_zero_constant`
   reconciles the two because that constant is zero. Reused, not re-proved.
4. **Both sources use the same fast-partial decomposition**
   (`poseidon.rs::poseidon` 767-777 -> `partial_rounds` 752-764;
   `PoseidonGate.sol::_permuteHashState` 106-126), so the adopted permutation
   model applies to both unchanged.
5. **No other divergence.** Padding (there is none in either), absorb order,
   overwrite-mode chunking, the short final chunk that overwrites only its
   occupied rate slots, the number of squeezed elements (4) and the untouched
   4-element capacity are identical; `numChunks 0 = 0` means both paths hash
   the empty vector to the untouched all-zero state's first four elements
   without any permutation. Byte/limb endianness is outside this model: both
   sides are modelled at the field-element level, and the `uint256` word to
   field element decoding of Solidity calldata is the same typed boundary the
   adopted `Verifier` header already declares.

## What is modelled here

The **actual** sponge, on top of the ADOPTED Poseidon permutation model
(`Audit.Wire3.Poseidon`'s witness layers -- `addConstantLayer`, `sboxLayer`,
`mdsLayer`, `partialFirstConstantLayer`, `mdsPartialInit`, `mdsPartialFast`,
`partialSboxValue`, `runWitness`). Poseidon is NOT re-implemented: `permute`
is exactly the composition the adopted `Poseidon.zeroInputWitness` runs, and
`permute_zero_matches_plonky2_test_vector` re-exports the adopted
`Poseidon.zero_input_matches_standard_output` (the hadeshash-derived
`poseidon_goldilocks.rs::tests::test_vectors` fixture) for it.

The adopted permutation model is an `Ext3` model; the hash is a base-field
computation. `permute_preserves_base` proves the whole permutation keeps the
`c1 = c2 = 0` subfield, so reading `c0` back out (`baseOf`) loses nothing --
`digest_limbs_determine_state` states that explicitly. This is a real
obligation, not a coercion.

## Explicit boundaries

* No collision resistance, preimage resistance or any cryptographic property
  of Poseidon is claimed or used. `publicInputsHash` binding the statement is
  a soundness question this module says nothing about.
* No Yul/EVM memory, gas, exception-ordering or bytecode refinement. The
  `revert InvalidMleProof()` sites are modelled as `none`.
* `Arithmetic`'s Nat operations over-approximate uint64/uint256 words, exactly
  as the adopted `Arithmetic` header states.
* The Poseidon round constants are the adopted `PoseidonConstants` literals;
  their correspondence to `plonky2`'s tables is the adopted module's claim.
* Nothing here says the hashed public inputs are the ones the transcript
  absorbed (`MleVerifierV2.sol` 403-406) -- that is a separate binding.
-/

namespace Audit.Wire3.PublicInputHashBinding
open Verifier

/-! ## 1. Sponge parameters (`poseidon.rs` 23-25, `PoseidonGate.sol` 30-33) -/

/-- `SPONGE_RATE` (`poseidon.rs:23`); the Solidity loop's `offset += 8`. -/
def rate : Nat := 8
/-- `SPONGE_CAPACITY` (`poseidon.rs:24`): state slots 8..11 are never written
by an absorb. -/
def capacity : Nat := 4
/-- `SPONGE_WIDTH` (`poseidon.rs:25`, `PoseidonGate.sol:30`). -/
def spongeWidth : Nat := 12
/-- `NUM_HASH_OUT_ELTS` (`hash_types.rs:20`); `digest[i]`, `i < 4`
(`PoseidonGate.sol` 87-89). -/
def hashOutElts : Nat := 4

theorem sponge_rate_capacity_split : rate + capacity = spongeWidth := by decide

/-- `hash_n_to_m_no_pad` squeezes `RATE` elements at a time; four outputs fit
in the first squeeze, so no extra `permute` runs (`hashing.rs` 130-139). -/
theorem outputs_fit_in_first_squeeze : hashOutElts ≤ rate := by decide

/-! ## 2. The permutation, taken from the adopted Poseidon model -/

/-- The Plonky2 Poseidon-12 permutation, EXACTLY the layer composition the
adopted `Poseidon.zeroInputWitness` executes: full rounds with constants 0..3,
`partialFirstConstantLayer`, `mdsPartialInit`, 22 fast partial rounds, full
rounds with constants 26..29 (`PoseidonGate.sol::_permuteHashState` 106-126).
Nothing about Poseidon is re-implemented here. -/
def permuteFirstFullRounds (s : Poseidon.State) : Poseidon.State :=
  (Poseidon.runWitness Poseidon.fullWitnessStep 1 3
    ⟨Poseidon.mdsLayer (Poseidon.sboxLayer (Poseidon.addConstantLayer s 0)), []⟩).state

/-- `_partialFirstConstantLayer`, `_mdsPartialLayerInit`, then
`_partialRoundsHash`'s 22 rounds (`PoseidonGate.sol` 117-119, 133-166). -/
def permutePartialRounds (s : Poseidon.State) : Poseidon.State :=
  (Poseidon.runWitness Poseidon.partialWitnessStep 0 22
    ⟨Poseidon.mdsPartialInit (Poseidon.partialFirstConstantLayer s), []⟩).state

/-- The closing `HALF_N_FULL_ROUNDS` full rounds, round constants 26..29
(`PoseidonGate.sol` 121-125). -/
def permuteSecondFullRounds (s : Poseidon.State) : Poseidon.State :=
  (Poseidon.runWitness (fun round => Poseidon.fullWitnessStep (26 + round)) 0 4 ⟨s, []⟩).state

def permute (s : Poseidon.State) : Poseidon.State :=
  permuteSecondFullRounds (permutePartialRounds (permuteFirstFullRounds s))

/-- `permute` is literally the state the adopted zero-input witness records at
wire offset 12, so the adopted independent test vector applies to it. -/
theorem permute_zero_is_adopted_witness_output :
    Poseidon.stateList (permute Poseidon.zeroState) =
      (Poseidon.zeroInputWitness.drop 12).take 12 := rfl

/-- The adopted `plonky2::hash::poseidon_goldilocks::tests::test_vectors`
zero-input fixture, re-exported for `permute`. -/
theorem permute_zero_matches_plonky2_test_vector :
    Poseidon.stateList (permute Poseidon.zeroState) =
      Poseidon.standardZeroOutput.map Norm.embed :=
  permute_zero_is_adopted_witness_output.trans Poseidon.zero_input_matches_standard_output

/-! ## 3. The base subfield: reading `c0` back out loses nothing -/

/-- A value of the adopted `Ext3` permutation model that is a base-field
element. -/
def IsBase (x : Ext3) : Prop := x.val.c1 = 0 ∧ x.val.c2 = 0

def StateIsBase (s : Poseidon.State) : Prop := ∀ i : Fin 12, IsBase (Poseidon.stateAt s i)

theorem isBase_zero : IsBase zero := ⟨rfl, rfl⟩

theorem isBase_add {x y : Ext3} (hx : IsBase x) (hy : IsBase y) : IsBase (add x y) := by
  refine ⟨?_, ?_⟩ <;>
    simp [add, Arithmetic.eadd, Arithmetic.add, Arithmetic.reduce, hx.1, hx.2, hy.1, hy.2]

theorem isBase_mul {x y : Ext3} (hx : IsBase x) (hy : IsBase y) : IsBase (mul x y) := by
  refine ⟨?_, ?_⟩ <;>
    simp [mul, Arithmetic.emul, Arithmetic.add, Arithmetic.mul, Arithmetic.reduce,
      hx.1, hx.2, hy.1, hy.2]

theorem isBase_scalar {x : Ext3} (hx : IsBase x) (s : Nat) : IsBase (scalar x s) := by
  refine ⟨?_, ?_⟩ <;>
    simp [scalar, Arithmetic.scalar, Arithmetic.mul, Arithmetic.reduce, hx.1, hx.2]

theorem isBase_addBase {x : Ext3} (hx : IsBase x) (n : Nat) : IsBase (Poseidon.addBase x n) :=
  ⟨hx.1, hx.2⟩

theorem isBase_square {x : Ext3} (hx : IsBase x) : IsBase (Norm.square x) := by
  refine ⟨?_, ?_⟩ <;>
    simp [Norm.square, Arithmetic.add, Arithmetic.mul, Arithmetic.reduce, hx.1, hx.2]

theorem isBase_sbox {x : Ext3} (hx : IsBase x) : IsBase (Poseidon.sbox x) :=
  isBase_mul (isBase_mul hx (isBase_square hx)) (isBase_square (isBase_square hx))

theorem isBase_foldl {α : Type} (F : Ext3 → α → Ext3)
    (hF : ∀ x a, IsBase x → IsBase (F x a)) (l : List α) :
    ∀ init : Ext3, IsBase init → IsBase (l.foldl F init) := by
  induction l with
  | nil => intro init h; exact h
  | cons a _l ih => intro init h; exact ih (F init a) (hF init a h)

theorem isBase_addConstantLayer {s : Poseidon.State} (h : StateIsBase s) (round : Nat) :
    StateIsBase (Poseidon.addConstantLayer s round) := by
  intro i
  simp only [Poseidon.addConstantLayer, Poseidon.at_makeState]
  exact isBase_addBase (h i) _

theorem isBase_partialFirstConstantLayer {s : Poseidon.State} (h : StateIsBase s) :
    StateIsBase (Poseidon.partialFirstConstantLayer s) := by
  intro i
  simp only [Poseidon.partialFirstConstantLayer, Poseidon.at_makeState]
  exact isBase_addBase (h i) _

theorem isBase_sboxLayer {s : Poseidon.State} (h : StateIsBase s) :
    StateIsBase (Poseidon.sboxLayer s) := by
  intro i
  simp only [Poseidon.sboxLayer, Poseidon.at_makeState]
  exact isBase_sbox (h i)

theorem isBase_mdsCirculantRow {s : Poseidon.State} (h : StateIsBase s) (row : Fin 12) :
    IsBase (Poseidon.mdsCirculantRow s row) := by
  simp only [Poseidon.mdsCirculantRow]
  exact isBase_foldl _ (fun x _ hx => isBase_add hx (isBase_scalar (h _) _)) _ _ isBase_zero

theorem isBase_mdsLayer {s : Poseidon.State} (h : StateIsBase s) :
    StateIsBase (Poseidon.mdsLayer s) := by
  intro i
  simp only [Poseidon.mdsLayer, Poseidon.at_makeState, Poseidon.mdsRow]
  split
  · exact isBase_add (isBase_mdsCirculantRow h i) (isBase_scalar (h 0) _)
  · exact isBase_mdsCirculantRow h i

theorem isBase_mdsPartialInit {s : Poseidon.State} (h : StateIsBase s) :
    StateIsBase (Poseidon.mdsPartialInit s) := by
  intro i
  simp only [Poseidon.mdsPartialInit, Poseidon.at_makeState]
  split
  · exact h 0
  · exact isBase_foldl _ (fun x _ hx => isBase_add hx (isBase_scalar (h _) _)) _ _ isBase_zero

theorem isBase_mdsPartialFast {s : Poseidon.State} (h : StateIsBase s) (round : Nat) :
    StateIsBase (Poseidon.mdsPartialFast s round) := by
  intro i
  simp only [Poseidon.mdsPartialFast, Poseidon.at_makeState]
  split
  · exact isBase_foldl _ (fun x _ hx => isBase_add hx (isBase_scalar (h _) _)) _ _
      (isBase_scalar (h 0) _)
  · exact isBase_add (isBase_scalar (h 0) _) (h i)

theorem isBase_partialSboxValue {x : Ext3} (hx : IsBase x) (round : Nat) :
    IsBase (Poseidon.partialSboxValue x round) := by
  simp only [Poseidon.partialSboxValue]
  split
  · exact isBase_sbox hx
  · exact isBase_addBase (isBase_sbox hx) _

theorem isBase_fullWitnessStep (round : Nat) (t : Poseidon.WitnessTrace)
    (h : StateIsBase t.state) : StateIsBase (Poseidon.fullWitnessStep round t).state :=
  isBase_mdsLayer (isBase_sboxLayer (isBase_addConstantLayer h round))

theorem isBase_partialWitnessStep (round : Nat) (t : Poseidon.WitnessTrace)
    (h : StateIsBase t.state) : StateIsBase (Poseidon.partialWitnessStep round t).state := by
  refine isBase_mdsPartialFast ?_ round
  intro i
  simp only [Poseidon.at_makeState]
  split
  · exact isBase_partialSboxValue (h 0) round
  · exact h i

theorem isBase_runWitness (step : Nat → Poseidon.WitnessTrace → Poseidon.WitnessTrace)
    (hstep : ∀ round t, StateIsBase t.state → StateIsBase (step round t).state) (count : Nat) :
    ∀ (round : Nat) (t : Poseidon.WitnessTrace), StateIsBase t.state →
      StateIsBase (Poseidon.runWitness step round count t).state := by
  induction count with
  | zero => intro _round t h; exact h
  | succ _count ih =>
      intro round t h
      exact ih (round + 1) (step round t) (hstep round t h)

/-- The full permutation stays inside the base subfield of the adopted `Ext3`
model, so `baseOf` below is a faithful readout and not a truncation. -/
theorem isBase_permuteFirstFullRounds {s : Poseidon.State} (h : StateIsBase s) :
    StateIsBase (permuteFirstFullRounds s) :=
  isBase_runWitness Poseidon.fullWitnessStep isBase_fullWitnessStep 3 1 _
    (isBase_mdsLayer (isBase_sboxLayer (isBase_addConstantLayer h 0)))

theorem isBase_permutePartialRounds {s : Poseidon.State} (h : StateIsBase s) :
    StateIsBase (permutePartialRounds s) :=
  isBase_runWitness Poseidon.partialWitnessStep isBase_partialWitnessStep 22 0 _
    (isBase_mdsPartialInit (isBase_partialFirstConstantLayer h))

theorem isBase_permuteSecondFullRounds {s : Poseidon.State} (h : StateIsBase s) :
    StateIsBase (permuteSecondFullRounds s) :=
  isBase_runWitness _ (fun round t ht => isBase_fullWitnessStep (26 + round) t ht) 4 0 _ h

theorem permute_preserves_base {s : Poseidon.State} (h : StateIsBase s) :
    StateIsBase (permute s) :=
  isBase_permuteSecondFullRounds (isBase_permutePartialRounds (isBase_permuteFirstFullRounds h))

theorem zeroState_isBase : StateIsBase Poseidon.zeroState := by
  intro i
  simp only [Poseidon.zeroState, Poseidon.at_makeState]
  exact isBase_zero

/-! ## 4. Field elements in and out -/

/-- A canonical base-field element as an adopted-model `Ext3`. -/
def embedBase (b : Base) : Ext3 := Norm.embed b.val

/-- The `c0` readout. Faithful exactly under `IsBase`
(`digest_limbs_determine_state`). -/
def baseOf (x : Ext3) : Base := ⟨x.val.c0, x.property.1⟩

theorem isBase_embedBase (b : Base) : IsBase (embedBase b) := ⟨rfl, rfl⟩

theorem baseOf_embedBase (b : Base) : baseOf (embedBase b) = b := by
  apply Fin.ext
  show Arithmetic.reduce b.val = b.val
  exact Arithmetic.reduce_fixed b.isLt

theorem baseOf_embed (n : Nat) : baseOf (Norm.embed n) = base n := rfl

/-- Under `IsBase` the single limb `baseOf x` determines `x` completely. -/
theorem digest_limbs_determine_state {x : Ext3} (h : IsBase x) :
    x.val = ⟨(baseOf x).val, 0, 0⟩ := by
  rcases x with ⟨⟨c0, c1, c2⟩, hc⟩
  obtain ⟨h1, h2⟩ := h
  simp only [] at h1 h2
  subst h1; subst h2; rfl

/-! ## 5. `set_from_slice` (`hashing.rs` 121-122, `poseidon.rs` 850-854,
`PoseidonGate.sol` 73-83) -/

/-- Overwrite mode on the first `chunk.length` slots ONLY. The `none` branch
keeps the previous state element -- this is the source's own semantics
(`self.state[begin..end].copy_from_slice(elts)`, and the Solidity loop bounded
by `chunkLength`), not a default-valued read standing in for a bound.
`set_from_slice_keeps_capacity` below records the rate/capacity consequence. -/
def setFromSlice (s : Poseidon.State) (chunk : List Ext3) : Poseidon.State :=
  Poseidon.makeState fun i =>
    match chunk.get? i.val with
    | some v => v
    | none => Poseidon.stateAt s i

theorem set_from_slice_absorbs {s : Poseidon.State} {chunk : List Ext3} {i : Fin 12} {v : Ext3}
    (h : chunk.get? i.val = some v) : Poseidon.stateAt (setFromSlice s chunk) i = v := by
  simp only [setFromSlice, Poseidon.at_makeState, h]

theorem set_from_slice_keeps {s : Poseidon.State} {chunk : List Ext3} {i : Fin 12}
    (h : chunk.length ≤ i.val) : Poseidon.stateAt (setFromSlice s chunk) i =
      Poseidon.stateAt s i := by
  have hnone : chunk.get? i.val = none := List.get?_eq_none.mpr h
  simp only [setFromSlice, Poseidon.at_makeState, hnone]

/-- The four capacity slots are never touched by an absorb. -/
theorem set_from_slice_keeps_capacity {s : Poseidon.State} {chunk : List Ext3}
    (hc : chunk.length ≤ rate) {i : Fin 12} (hi : rate ≤ i.val) :
    Poseidon.stateAt (setFromSlice s chunk) i = Poseidon.stateAt s i :=
  set_from_slice_keeps (Nat.le_trans hc hi)

theorem isBase_setFromSlice {s : Poseidon.State} (hs : StateIsBase s) {chunk : List Ext3}
    (hc : ∀ x ∈ chunk, IsBase x) : StateIsBase (setFromSlice s chunk) := by
  intro i
  simp only [setFromSlice, Poseidon.at_makeState]
  cases hg : chunk.get? i.val with
  | none => exact hs i
  | some v => exact hc v (List.get?_mem hg)

/-! ## 6. The sponge (`hashing.rs` 114-141, `PoseidonGate.sol` 70-89) -/

/-- The `i`-th absorbed chunk: `inputs[offset .. offset+8]`, i.e. Rust's
`inputs.chunks(RATE)` element and the Solidity loop body's calldata window. -/
def chunkAt (inputs : List Ext3) (offset : Nat) : List Ext3 := (inputs.drop offset).take rate

/-- The Solidity `for (offset = 0; offset < inputs.length; offset += 8)` loop,
counted by its number of iterations. Structural recursion on the count, so the
whole hash reduces in the kernel. -/
def absorbFrom (inputs : List Ext3) : Nat → Nat → Poseidon.State → Poseidon.State
  | _, 0, s => s
  | offset, n + 1, s =>
      absorbFrom inputs (offset + rate) n (permute (setFromSlice s (chunkAt inputs offset)))

/-- `ceil(len / 8)`: the number of loop iterations, equivalently the number of
chunks `inputs.chunks(8)` yields. -/
def numChunks (len : Nat) : Nat := (len + rate - 1) / rate

theorem numChunks_zero : numChunks 0 = 0 := by decide

theorem numChunks_covers (len : Nat) : len ≤ rate * numChunks len := by
  simp only [numChunks, rate]
  omega

/-- The initial state is all zeros (`P::new(core::iter::repeat(F::ZERO))`,
`poseidon.rs` 838-843; `new uint256[](12)`, `PoseidonGate.sol:58`). -/
def absorb (inputs : List Ext3) : Poseidon.State :=
  absorbFrom inputs 0 (numChunks inputs.length) Poseidon.zeroState

theorem absorb_empty : absorb [] = Poseidon.zeroState := rfl

theorem chunk_length_le_rate (inputs : List Ext3) (offset : Nat) :
    (chunkAt inputs offset).length ≤ rate := by
  simp only [chunkAt, List.length_take]
  exact Nat.min_le_left _ _

theorem isBase_absorbFrom (inputs : List Ext3) (hb : ∀ x ∈ inputs, IsBase x) (n : Nat) :
    ∀ (offset : Nat) (s : Poseidon.State), StateIsBase s →
      StateIsBase (absorbFrom inputs offset n s) := by
  induction n with
  | zero => intro _offset s h; exact h
  | succ _n ih =>
      intro offset s h
      refine ih (offset + rate) _ (permute_preserves_base (isBase_setFromSlice h ?_))
      intro x hx
      exact hb x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

theorem isBase_absorb (inputs : List Ext3) (hb : ∀ x ∈ inputs, IsBase x) :
    StateIsBase (absorb inputs) :=
  isBase_absorbFrom inputs hb _ 0 _ zeroState_isBase

/-! ### Absorb order: every input word is absorbed exactly once, in order -/

/-- The concatenation of the chunks the loop visits. -/
def absorbedInputs (inputs : List Ext3) : Nat → Nat → List Ext3
  | _, 0 => []
  | offset, n + 1 => chunkAt inputs offset ++ absorbedInputs inputs (offset + rate) n

theorem absorbedInputs_eq (inputs : List Ext3) (n : Nat) :
    ∀ offset, absorbedInputs inputs offset n = (inputs.drop offset).take (rate * n) := by
  induction n with
  | zero => intro offset; simp [absorbedInputs]
  | succ n ih =>
      intro offset
      simp only [absorbedInputs, ih, chunkAt, Nat.mul_succ, Nat.add_comm (rate * n) rate,
        List.take_add, List.drop_drop, Nat.add_comm offset rate]

/-- The absorbed words are exactly `inputs`, in order, with no padding, no
truncation and no repetition (`hash_no_pad`'s defining property). -/
theorem absorb_consumes_all_inputs (inputs : List Ext3) :
    absorbedInputs inputs 0 (numChunks inputs.length) = inputs := by
  rw [absorbedInputs_eq]
  simp only [List.drop_zero]
  exact List.take_all_of_le (numChunks_covers inputs.length)

/-! ## 7. The digest (`PoseidonGate.sol` 87-89, `hashing.rs` 130-144) -/

/-- The first `NUM_HASH_OUT_ELTS = 4` state elements. Since
`outputs_fit_in_first_squeeze`, this is Rust's whole squeeze loop, and it is
Solidity's `digest[i] = state[i]` loop verbatim. -/
def digestOfState (s : Poseidon.State) : List Base :=
  ((Poseidon.stateList s).take hashOutElts).map baseOf

theorem digest_length (s : Poseidon.State) : (digestOfState s).length = 4 := by
  simp [digestOfState, Poseidon.state_list_length, hashOutElts]

theorem digest_is_first_four_state_elements (s : Poseidon.State) :
    digestOfState s = [baseOf (Poseidon.stateAt s 0), baseOf (Poseidon.stateAt s 1),
      baseOf (Poseidon.stateAt s 2), baseOf (Poseidon.stateAt s 3)] := rfl

/-- `PoseidonPublicInputsHash.hashNoPad` / `PoseidonHash::hash_no_pad`, the
whole computation, on canonical base-field public inputs. -/
def hashNoPad (inputs : List Base) : List Base :=
  digestOfState (absorb (inputs.map embedBase))

/-- The four-limb shape `Integrated.evaluateGate` (Integrated.lean:40) and
`Plonky2GateEvaluatorExt3` (lines 91-93) require, as a theorem. -/
theorem hash_no_pad_length (inputs : List Base) : (hashNoPad inputs).length = 4 :=
  digest_length _

/-- Every output limb is a canonical field element (it is a `Fin modulus`);
this is the property `Plonky2GateEvaluatorExt3.sol` 91-93 re-checks at its
public entry point and `evalCombinedPrevalidated` assumes. -/
theorem hash_no_pad_canonical (inputs : List Base) :
    ∀ x ∈ hashNoPad inputs, x.val < Arithmetic.modulus := fun x _ => x.isLt

/-- `l.map f = l` from a pointwise-on-members identity. -/
theorem map_eq_self_of_mem {α : Type} {f : α → α} :
    ∀ l : List α, (∀ x ∈ l, f x = x) → l.map f = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
      intro h
      rw [List.map_cons, h a (List.mem_cons_self _ _), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem embedBase_baseOf {x : Ext3} (h : IsBase x) : embedBase (baseOf x) = x := by
  apply Subtype.eq
  rcases x with ⟨⟨c0, c1, c2⟩, hc⟩
  obtain ⟨h1, h2⟩ := h
  simp only [] at h1 h2
  subst h1; subst h2
  show Arithmetic.fromBase c0 = _
  simp [Arithmetic.fromBase, Arithmetic.reduce_fixed hc.1]

theorem final_state_isBase (inputs : List Base) :
    StateIsBase (absorb (inputs.map embedBase)) := by
  refine isBase_absorb _ ?_
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  exact isBase_embedBase b

/-- The digest limbs are exactly the first four elements of the final sponge
state, with NOTHING lost in the `Ext3` -> base-field readout: re-embedding the
digest recovers those four state elements on the nose. -/
theorem hash_no_pad_reads_final_state (inputs : List Base) :
    ((Poseidon.stateList (absorb (inputs.map embedBase))).take hashOutElts) =
      (hashNoPad inputs).map embedBase := by
  have hb := final_state_isBase inputs
  have hmem : ∀ x ∈ (Poseidon.stateList (absorb (inputs.map embedBase))).take hashOutElts,
      IsBase x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
    exact hb i
  simp only [hashNoPad, digestOfState, List.map_map]
  exact (map_eq_self_of_mem _ (fun x hx => embedBase_baseOf (hmem x hx))).symm

/-! ## 8. The raw canonical / range preflight (`MleVerifierV2.sol` 562,
634-658; `PoseidonGate.sol` 77-80) -/

/-- `MAX_PUBLIC_INPUTS_V2` (`generated/MleWhirV2.sol:36`). -/
def maxPublicInputs : Nat := 256

/-- The two reverts the Solidity path performs on the RAW `uint256[] calldata`
public inputs before/while hashing them: the length cap
(`MleVerifierV2.sol:639`) and the per-word `value < P` test
(`MleVerifierV2.sol` 651-654 and `PoseidonGate.sol` 77-80). Rust has neither;
its `Vec<GoldilocksField>` is canonical by type. -/
def rawPublicInputsValid (raw : List Nat) : Bool :=
  decide (raw.length ≤ maxPublicInputs) && raw.all (fun v => decide (v < Arithmetic.modulus))

/-- The raw entry point. `none` is exactly the source's `revert
InvalidMleProof()`; a malformed word never reaches the sponge and is never
silently reduced. -/
def rawPublicInputsHash (raw : List Nat) : Option (List Base) :=
  if rawPublicInputsValid raw then some (hashNoPad (raw.map base)) else none

theorem raw_rejects_noncanonical_word {raw : List Nat} {v : Nat} (hv : v ∈ raw)
    (h : Arithmetic.modulus ≤ v) : rawPublicInputsHash raw = none := by
  unfold rawPublicInputsHash
  split
  · rename_i hvalid
    exfalso
    simp only [rawPublicInputsValid, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hvalid
    have hlt := hvalid.2 v hv
    simp only [decide_eq_true_eq] at hlt
    omega
  · rfl

theorem raw_rejects_overlong {raw : List Nat} (h : maxPublicInputs < raw.length) :
    rawPublicInputsHash raw = none := by
  have : rawPublicInputsValid raw = false := by
    simp [rawPublicInputsValid, Nat.not_le.mpr h]
  simp [rawPublicInputsHash, this]

/-- Success carries BOTH source guards and the exact computed value; and on the
accepted range `base` is the identity on every word, so no word was silently
reduced into range. -/
theorem raw_success_exact {raw : List Nat} {h : List Base}
    (hr : rawPublicInputsHash raw = some h) :
    raw.length ≤ maxPublicInputs ∧ (∀ v ∈ raw, v < Arithmetic.modulus) ∧
      (raw.map base).map Fin.val = raw ∧ h = hashNoPad (raw.map base) ∧ h.length = 4 := by
  unfold rawPublicInputsHash at hr
  split at hr
  · rename_i hv
    simp only [rawPublicInputsValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
    have hcanon : ∀ v ∈ raw, v < Arithmetic.modulus := by
      intro v hvm
      have hlt := hv.2 v hvm
      simp only [decide_eq_true_eq] at hlt
      exact hlt
    have hid : (raw.map base).map Fin.val = raw := by
      rw [List.map_map]
      exact map_eq_self_of_mem raw (fun v hvm => Nat.mod_eq_of_lt (hcanon v hvm))
    have heq : h = hashNoPad (raw.map base) := (Option.some.inj hr).symm
    exact ⟨hv.1, hcanon, hid, heq, heq ▸ hash_no_pad_length _⟩
  · contradiction

/-- On canonical, in-range raw public inputs the concrete computation IS
defined (no revert), and every output limb is a canonical field element --
the property `Plonky2GateEvaluatorExt3.sol` 91-93 tests at its permissionless
entry point and `evalCombinedPrevalidated` (line 97-113, the entry
`MleVerifierV2.sol:383` uses) assumes. -/
theorem raw_canonical_is_defined {raw : List Nat} (hlen : raw.length ≤ maxPublicInputs)
    (hcanon : ∀ v ∈ raw, v < Arithmetic.modulus) :
    ∃ h, rawPublicInputsHash raw = some h ∧ h.length = 4 ∧
      ∀ x ∈ h, x.val < Arithmetic.modulus := by
  have hvalid : rawPublicInputsValid raw = true := by
    simp only [rawPublicInputsValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨hlen, hcanon⟩
  refine ⟨hashNoPad (raw.map base), by simp [rawPublicInputsHash, hvalid],
    hash_no_pad_length _, fun x _ => x.isLt⟩

/-- The typed and raw entry points agree on canonical input. -/
theorem raw_hash_of_typed (l : List Base) (h : l.length ≤ maxPublicInputs) :
    rawPublicInputsHash (l.map Fin.val) = some (hashNoPad l) := by
  have hvalid : rawPublicInputsValid (l.map Fin.val) = true := by
    simp only [rawPublicInputsValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.length_map, List.mem_map]
    refine ⟨h, ?_⟩
    rintro v ⟨b, _, rfl⟩
    exact b.isLt
  have hmap : (l.map Fin.val).map base = l := by
    rw [List.map_map]
    exact map_eq_self_of_mem l (fun b _ => Fin.ext (Nat.mod_eq_of_lt b.isLt))
  simp [rawPublicInputsHash, hvalid, hmap]

/-! ## 9. Substituting the concrete computation for the Engine observation
(`Verifier.lean` 373 `Engine.publicInputsHash`, 395-399 `gateTerminal`;
`Integrated.lean` 41-49 `modelEngine`) -/

/-- The adopted `Engine.publicInputsHash` is an OPAQUE parameter
(`Verifier.lean:353`) and `Integrated.modelEngine` (Integrated.lean 41-49)
deliberately leaves it alone -- the Integrated header lists "public-input hash"
among its remaining observations. This installs the concrete computation, in
the same style as the adopted `Norm.withNormEvaluation`. -/
def withPublicInputsHash (e : Engine) : Engine := { e with publicInputsHash := hashNoPad }

theorem engine_hash_is_concrete (e : Engine) (pis : List Base) :
    (withPublicInputsHash e).publicInputsHash pis = hashNoPad pis := rfl

/-- `modelEngine` replaces four other fields and never touches this one, so the
concrete hash survives the adopted wrapper. -/
theorem model_engine_keeps_concrete_hash (e : Engine) (decode : Integrated.DecodeGates)
    (pis : List Base) :
    (Integrated.modelEngine (withPublicInputsHash e) decode).publicInputsHash pis =
      hashNoPad pis := rfl

theorem with_public_inputs_hash_substitution (e : Engine) :
    (withPublicInputsHash e).publicInputsHash = hashNoPad := rfl

/-- The four-limb length that `Integrated.evaluateGate` (Integrated.lean:40)
and `Plonky2GateEvaluatorExt3.sol` 91-93 demand is now a THEOREM, not an
assumption, whenever the engine's hash is this concrete function. -/
theorem hash_length_discharged (e : Engine) (p : Proof)
    (hsub : e.publicInputsHash = hashNoPad) : (e.publicInputsHash p.publicInputs).length = 4 := by
  rw [hsub]
  exact hash_no_pad_length _

/-- The explicit, auditable substitution: IF the engine's `publicInputsHash` is
this concrete `hash_no_pad` computation, THEN the model engine's gate terminal
(`Verifier.lean` 395-399) evaluates the gate table at the actual Poseidon
digest of the proof's public inputs. -/
theorem gate_terminal_uses_concrete_hash (e : Engine) (decode : Integrated.DecodeGates)
    (c : Config) (p : Proof) (hsub : e.publicInputsHash = hashNoPad) :
    Verifier.gateTerminal (Integrated.modelEngine e decode) c p =
      mul (Norm.eqEvaluation (e.initialTranscript c p).gateTau (derivedRounds e c p).gatePoint)
        ((Integrated.evaluateGate decode c p.used.gateWitness
          (p.used.gatePreprocessed.take c.numConstants) (hashNoPad p.publicInputs)
          (e.initialTranscript c p).gateAlpha).getD zero) := by
  rw [GateTerminalBinding.engine_gate_terminal_unfolds]
  show mul _ ((Integrated.evaluateGate decode c p.used.gateWitness
    (p.used.gatePreprocessed.take c.numConstants) (e.publicInputsHash p.publicInputs)
    (e.initialTranscript c p).gateAlpha).getD zero) = _
  rw [hsub]

/-- Same statement for the engine built by `withPublicInputsHash`, with no
hypothesis at all. -/
theorem gate_terminal_of_with_public_inputs_hash (e : Engine) (decode : Integrated.DecodeGates)
    (c : Config) (p : Proof) :
    Verifier.gateTerminal (Integrated.modelEngine (withPublicInputsHash e) decode) c p =
      mul (Norm.eqEvaluation (e.initialTranscript c p).gateTau (derivedRounds e c p).gatePoint)
        ((Integrated.evaluateGate decode c p.used.gateWitness
          (p.used.gatePreprocessed.take c.numConstants) (hashNoPad p.publicInputs)
          (e.initialTranscript c p).gateAlpha).getD zero) :=
  gate_terminal_uses_concrete_hash (withPublicInputsHash e) decode c p rfl

/-! ## 10. The adopted gate-terminal binding, restated on the concrete hash -/

/-- `GateTerminalBinding.bound_terminal_is_engine_gate_terminal` with the
public-input hash observation replaced by this concrete computation. The
adopted `hp : (e.publicInputsHash p.publicInputs).length = 4` hypothesis is
GONE: it is discharged by `hash_no_pad_length`. Everything else (the eq-cell
and cell/claim correspondences) remains an explicit hypothesis exactly as in
the adopted theorem; this changes nothing about them. -/
theorem bound_terminal_is_engine_gate_terminal_concrete_hash
    (e : Engine) (decode : Integrated.DecodeGates) (c : Config) (p : Proof)
    (gates : List Gates.GateInfo) (k : GateTerminalBinding.Cells)
    (alpha : GoldilocksExt3Field.Element)
    (hsub : e.publicInputsHash = hashNoPad)
    (hd : decode c.gatesEncoding = some gates) (hr : gates.length = c.gateRows)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hk : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p))
    (hw : k.wires.length = c.numWires) (hc : k.constants.length = c.numConstants)
    (halpha : alpha.toVerifier = (e.initialTranscript c p).gateAlpha)
    (heq : k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript c p).gateTau (derivedRounds e c p).gatePoint) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      GateTerminalBinding.boundTerminal (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (hashNoPad p.publicInputs)) alpha k =
        some (mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p = mul k.eq.toVerifier gate := by
  have h := GateTerminalBinding.bound_terminal_is_engine_gate_terminal e decode c p gates k alpha
    hd hr (hash_length_discharged e p hsub) hv hk hw hc halpha heq
  rwa [hsub] at h

/-- HONEST-PROVER ONLY (it quantifies over the honest gate prover's own tables,
exactly like the adopted theorem it restates). The adopted
`GateTerminalBinding.honest_last_round_is_engine_gate_terminal` with the
public-input hash observation replaced by the concrete computation and its
length hypothesis discharged. -/
theorem honest_last_round_is_engine_gate_terminal_concrete_hash
    (e : Engine) (decode : Integrated.DecodeGates) (c : Config) (p : Proof)
    (gates : List Gates.GateInfo) (s t : GateTerminalBinding.ProverState)
    (round : List Ext3) (x : GoldilocksExt3Field.Element) (k : GateTerminalBinding.Cells)
    (alpha : GoldilocksExt3Field.Element)
    (hsub : e.publicInputsHash = hashNoPad)
    (hs : GateTerminalBinding.ProverShape (Integrated.gateConfig c) 1 s)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hb : GateTerminalBinding.bindChallenge s round x = some t) (hkt : t.tables = k.tables)
    (hd : decode c.gatesEncoding = some gates) (hr : gates.length = c.gateRows)
    (hk : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p))
    (halpha : alpha.toVerifier = (e.initialTranscript c p).gateAlpha)
    (heq : k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript c p).gateTau (derivedRounds e c p).gatePoint) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (hashNoPad p.publicInputs)) alpha x s.tables 1 =
        some (mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p = mul k.eq.toVerifier gate := by
  have h := GateTerminalBinding.honest_last_round_is_engine_gate_terminal e decode c p gates s t
    round x k alpha hs hv hb hkt hd hr (hash_length_discharged e p hsub) hk halpha heq
  rwa [hsub] at h

/-! ## 11. The honest-prover glue: the hash leaves the hypothesis list -/

/-- `IntegratedTerminalChain.GateChainHypotheses` carries the public-input hash
as its OBSERVATION field `hashLength` (IntegratedTerminalChain.lean:382, and
the module header's item 4: "The four-limb public-input hash length is the
`hashLength` field of `GateChainHypotheses`"). With the concrete engine hash
that field is derivable, so this builder produces the adopted structure from
the remaining TWELVE fields only -- and states the `grid` field directly on
the concrete digest. `IntegratedTerminalChain.honest_prover_passes_deterministic_checks`
consumes the result unchanged, so the public-input hash is no longer one of
the glue's assumptions. Every other field (`grid`, `eqCell`, `claims`,
`alphaMatches`, ...) stays exactly as adopted. -/
theorem gate_chain_hypotheses_of_concrete_hash
    (e : Engine) (decode : Integrated.DecodeGates) (c : Config) (p : Proof)
    (pre : List CoupledMessage) (mLog gLast : List Ext3) (gates : List Gates.GateInfo)
    (s t : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (alpha : GoldilocksExt3Field.Element)
    (hsub : e.publicInputsHash = hashNoPad)
    (split : p.logRounds.zip p.gateRounds = pre ++ [(mLog, gLast)])
    (shape : GateTerminalBinding.ProverShape (Integrated.gateConfig c) 1 s)
    (bind : GateTerminalBinding.bindChallenge s gLast
      (OuterRound.lift (IntegratedTerminalChain.lastGateChallenge e c p pre mLog gLast)) = some t)
    (cells : t.tables = k.tables)
    (hdecode : decode c.gatesEncoding = some gates)
    (rows : gates.length = c.gateRows)
    (valid : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (claims : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p))
    (alphaMatches : alpha.toVerifier = (e.initialTranscript c p).gateAlpha)
    (eqCell : k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript c p).gateTau (derivedRounds e c p).gatePoint)
    (messageLength : gLast.length ≤ c.quotientDegree + 2)
    (grid : ∀ i, i ≤ c.quotientDegree + 2 →
      GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (hashNoPad p.publicInputs)) alpha
        (GateSlotRound.gridPoint i) s.tables 1 =
      some (Verifier.evaluateRound (IntegratedTerminalChain.lastState e c p pre).gateClaim gLast
        (Norm.embed i))) :
    IntegratedTerminalChain.GateChainHypotheses e decode c p pre mLog gLast gates s t k alpha :=
  { split := split, shape := shape, bind := bind, cells := cells, decode := hdecode, rows := rows,
    valid := valid, hashLength := hash_length_discharged e p hsub, claims := claims,
    alphaMatches := alphaMatches, eqCell := eqCell, messageLength := messageLength,
    grid := by rw [hsub]; exact grid }

/-! ## 12. Concrete examples -/

/-- Eight zero public inputs fill exactly one rate chunk, so the sponge runs a
single permutation on the untouched all-zero state. -/
def eightZeroInputs : List Base := List.replicate 8 (base 0)

theorem eight_zero_is_one_chunk : numChunks eightZeroInputs.length = 1 := by decide

theorem eight_zero_absorb :
    absorb (eightZeroInputs.map embedBase) = permute Poseidon.zeroState := rfl

/-- The digest of eight zero public inputs is the first four limbs of the
independent `plonky2::hash::poseidon_goldilocks::tests::test_vectors`
zero-input fixture (adopted as `Poseidon.standardZeroOutput`). This is a
cross-check against a fixture computed by the hadeshash reference
implementation, not a self-consistency check. -/
theorem eight_zero_public_inputs_digest :
    hashNoPad eightZeroInputs = (Poseidon.standardZeroOutput.take hashOutElts).map base := by
  show digestOfState (permute Poseidon.zeroState) = _
  rw [digestOfState, permute_zero_matches_plonky2_test_vector]
  simp [List.map_take, List.map_map, Function.comp, baseOf_embed]

def eightZeroDigest : List Base :=
  [base 0x3c18a9786cb0b359, base 0xc4055e3364a246c3,
   base 0x7953db0ab48808f4, base 0xc71603f33a1144ca]

theorem eight_zero_digest_value : hashNoPad eightZeroInputs = eightZeroDigest := by
  rw [eight_zero_public_inputs_digest]
  rfl

/-- An empty public-input vector runs NO permutation in either implementation
(`inputs.chunks(8)` is empty; the Solidity loop body never executes), so the
digest is the four zero limbs of the untouched initial state. -/
theorem empty_public_inputs_digest :
    hashNoPad [] = [base 0, base 0, base 0, base 0] := rfl

/-- A nine-element vector: two permutations, and the second chunk overwrites
only rate slot 0 -- the short-final-chunk behaviour both implementations have
and neither pads. -/
theorem nine_public_inputs_two_permutations (l : List Base) (h : l.length = 9) :
    absorb (l.map embedBase) =
      permute (setFromSlice
        (permute (setFromSlice Poseidon.zeroState (chunkAt (l.map embedBase) 0)))
        (chunkAt (l.map embedBase) rate)) := by
  simp only [absorb, List.length_map, h]
  rfl

theorem nine_public_inputs_short_final_chunk (l : List Base) (h : l.length = 9) :
    (chunkAt (l.map embedBase) rate).length = 1 ∧
      ∀ (st : Poseidon.State) (i : Fin 12), 1 ≤ i.val →
        Poseidon.stateAt (setFromSlice st (chunkAt (l.map embedBase) rate)) i =
          Poseidon.stateAt st i := by
  have hlen : (chunkAt (l.map embedBase) rate).length = 1 := by
    simp [chunkAt, rate, h]
  exact ⟨hlen, fun st i hi => set_from_slice_keeps (by omega)⟩

/-- Raw-boundary acceptance of the same example. -/
theorem raw_eight_zero_accepted :
    rawPublicInputsHash (List.replicate 8 0) = some eightZeroDigest := by
  have : rawPublicInputsHash (List.replicate 8 0) = some (hashNoPad eightZeroInputs) := rfl
  rw [this, eight_zero_digest_value]

/-- REJECTED, not defaulted: a word at the modulus is out of range and the
computation returns `none` (`PoseidonGate.sol` 77-80 / `MleVerifierV2.sol`
651-654 `revert InvalidMleProof()`). -/
theorem raw_modulus_word_rejected :
    rawPublicInputsHash [1, Arithmetic.modulus, 3] = none :=
  raw_rejects_noncanonical_word (List.mem_cons_of_mem _ (List.mem_cons_self _ _)) (Nat.le_refl _)

/-- REJECTED: `2^64 - 1` is a valid uint64 word but not a canonical Goldilocks
element. -/
theorem raw_u64_max_word_rejected : rawPublicInputsHash [18446744073709551615] = none :=
  raw_rejects_noncanonical_word (List.mem_cons_self _ _) (by decide)

/-- REJECTED: over `MAX_PUBLIC_INPUTS_V2` words (`MleVerifierV2.sol:639`). -/
theorem raw_overlong_rejected : rawPublicInputsHash (List.replicate 257 0) = none :=
  raw_rejects_overlong (by simp [maxPublicInputs])

/-- The circuit-count guard (`MleVerifierV2.sol:562`), kept separate from the
canonical guard because the source performs it at a different site. -/
def checkedPublicInputsHash (c : Config) (raw : List Nat) : Option (List Base) :=
  if raw.length = c.numPublicInputs then rawPublicInputsHash raw else none

theorem checked_rejects_wrong_count (c : Config) (raw : List Nat)
    (h : raw.length ≠ c.numPublicInputs) : checkedPublicInputsHash c raw = none := by
  simp [checkedPublicInputsHash, h]

theorem checked_success_exact {c : Config} {raw : List Nat} {h : List Base}
    (hr : checkedPublicInputsHash c raw = some h) :
    raw.length = c.numPublicInputs ∧ raw.length ≤ maxPublicInputs ∧
      (∀ v ∈ raw, v < Arithmetic.modulus) ∧ h = hashNoPad (raw.map base) ∧ h.length = 4 := by
  unfold checkedPublicInputsHash at hr
  split at hr
  · rename_i hcount
    obtain ⟨hle, hcanon, _, hval, hlen⟩ := raw_success_exact hr
    exact ⟨hcount, hle, hcanon, hval, hlen⟩
  · contradiction

end Audit.Wire3.PublicInputHashBinding
