import Audit.Wire3.ComposedEngine
import Audit.Wire3.InstalledWhirParse

/-!
# The explicit engine: a verifier model with no abstract engine field

## The milestone

`explicitEngine gdec hash thash khash P c₀` is a `Verifier.Engine` with **NO
abstract base engine argument**. Every one of its twelve fields is a concrete
function of the six explicit parameters -- the gate-metadata decoder `gdec`, the
WHIR/Merkle hash `hash`, the outer transcript hash `thash`, the configuration
hash `khash`, the deployment profile table `P` and the deployed configuration
`c₀`. `explicit_has_no_observation` states that as ONE `rfl` equation to a
twelve-field record literal in which no `Verifier.Engine` occurs at all, and
`explicit_is_composed_over_any_base` states that the engine obtained from
`ComposedEngine.composedEngine e …` by installing the last two observations is
the SAME engine for every `e`, so nothing that follows depends on a base.

`ComposedEngine` left exactly two observations, `parseWhir` and
`configurationHash`. `InstalledWhirParse` made the first concrete. This module
makes the second concrete and, in doing so, removes the last place where an
abstract base engine could enter: `PinnedWhirProfile.pinnedDeployment P e c₀`
reads `e.deploymentValid`, so `deploymentValid` is replaced here by the base-free
`explicitDeployment P c₀`. Section 5 below says exactly what that drops and what
it does NOT drop.

The configuration digest is modelled the way `CommitmentOrder` and
`TranscriptProvenance` model transcript hashing: an ARBITRARY DETERMINISTIC
function `khash : Bytes → Root` applied to a CONCRETE ENCODING
`encodeConfig : Verifier.Config → Bytes` that mirrors the source's
`abi.encode(MleVerifierV2.VerificationConfig)` field for field. Configuration
non-malleability then reduces to injectivity of the encoding -- which is PROVED
(`encode_config_injective`) -- plus a `khash` collision, which is never assumed
away and always appears as an explicit disjunct.

## What this does NOT mean

**`hash`, `thash` and `khash` are ARBITRARY DETERMINISTIC FUNCTIONS.** Keccak is
not modelled anywhere in the adopted tree and is not modelled here. No collision
resistance, no preimage resistance, no random-oracle property and no randomness
is assumed of any of the three. Consequently EVERY conclusion of the form "the
accepted configuration is the deployed one" is stated as an explicit disjunction
with `KhashCollision khash`, and a reader who wants the left disjunct must supply
collision resistance from outside this development. `PinnedWhirProfile`'s
`TableIsCanonical` is likewise still an ASSUMPTION, carried visibly by each
statement that needs it, and it is transcribed for `n ∈ {10, 21}` ONLY: the
other nineteen table rows ship as keccak digests and are not modelled.

**The WHIR tail is a MANUAL MODEL.** `InstalledWhirTail`'s caveat stands
unchanged: `installedTail` is a hand-transcribed execution model of the source's
tail, not a refinement proof of it. The R1b family (WHIR proximity and sumcheck
soundness), R2 (extraction / PCS extractability), R3, half (B) of the
Fiat--Shamir reading (that the squeezes are uniform and independent of the
absorbed prefix -- unformalized here and everywhere in the adopted tree, and
whose weaker deterministic shadow is REFUTED for a general deterministic hash by
`CommitmentOrder.separation_fails_for_a_deterministic_hash`), circuit truth, and
Rust/Yul/Solidity refinement all remain OPEN.

**`explicitDeployment` models the SOLIDITY RUNTIME PATH ONLY.** The Rust entry
point `mle_verify_v2` (src/verifier_v2.rs 57-175) re-validates on EVERY call what
the Solidity constructor validated once: the coset shifts `kIs` against the common
data (src/verifier_v2.rs 120-123), the canonical squared subgroup-generator powers
(src/verifier_v2.rs 130-146), the gate metadata against `collect_gate_info_v2`
(src/verifier_v2.rs 148-149), `circuit_config_digest` (src/verifier_v2.rs 156-165),
the WHIR protocol and session identifiers (src/verifier_v2.rs 167-175) and
`proof.circuit_digest` against the verification key (src/verifier_v2.rs 176-179).
NONE of that is modelled by `explicitDeployment`, which drops the abstract
deployment conjunct precisely because the SOLIDITY runtime performs none of it.
Section 5 says exactly which of those Rust checks survive in this model and which
are residue.

**The encoding is a mirror, not a bit-exact ABI transcription.** Section 2 lists
the three departures from `abi.encode` precisely, and `residue_fields_are_not_encoded`
exhibits the six `Verifier.Config` fields the deployed digest does NOT bind.
Nothing here is a gas, exception-order or bytecode claim, `Verifier.verify` is
still a manual success-boundary model, and nothing here is the deployed system's
soundness error. The wire-v3 WHIR profile this tree models is the approximately
100-bit design point. No figure in this module is a security level, and in
particular nothing here says "125".
-/

namespace Audit.Wire3.ExplicitEngine

open Audit.Wire3 GoldilocksExt3Field

abbrev Profile := PinnedWhirProfile.Profile

/-! ## 1. The ABI word and its injectivity

`abi.encode` lays every scalar out as a 32-byte big-endian word
(`ABI_WORD_BYTES = 32`, src/fixture_v2.rs 59; `_writeU64Le`'s big-endian
counterpart in the ABI path is `abi_word_u64` / `abi_word_usize`,
src/fixture_v2.rs 2752-2762). `word n` is that slot, `readBytes` reads it back, and `word_injective`
says the slot determines `n` BELOW `wordBound = 256 ^ 32 = 2 ^ 256`. Lean's `Nat`
is unbounded while Solidity's `uint256` is not, which is why every injectivity
statement below carries a `Bounded` hypothesis; `bounded_of_envelope` discharges
eleven of its thirteen components from `Verifier.envelope` alone. -/

def wordBound : Nat := 256 ^ 32

def wordAux : Nat → Nat → Verifier.Bytes
  | 0, _ => []
  | k + 1, n => wordAux k (n / 256) ++ [UInt8.ofNat (n % 256)]

def word (n : Nat) : Verifier.Bytes := wordAux 32 n

def readBytes (bs : Verifier.Bytes) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem word_aux_length (k n : Nat) : (wordAux k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [wordAux, ih]

theorem word_length (n : Nat) : (word n).length = 32 := word_aux_length 32 n

theorem mod_step (n m : Nat) :
    n / 256 % m * 256 + n % 256 = n % (256 * m) := by
  have h1 : n % (256 * m) / 256 = n / 256 % m := Nat.mod_mul_right_div_self n 256 m
  have h2 : n % (256 * m) % 256 = n % 256 := Nat.mod_mod_of_dvd n ⟨m, rfl⟩
  conv_rhs => rw [← Nat.div_add_mod (n % (256 * m)) 256]
  rw [h1, h2]
  ring

theorem uint8_to_nat_of_nat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := rfl

theorem fold_word_aux (k : Nat) : ∀ a n : Nat,
    List.foldl (fun acc b => acc * 256 + UInt8.toNat b) a (wordAux k n)
      = a * 256 ^ k + n % 256 ^ k := by
  induction k with
  | zero => intro a n; simp [wordAux, Nat.mod_one]
  | succ k ih =>
      intro a n
      rw [wordAux, List.foldl_append, ih]
      have hstep := mod_step n (256 ^ k)
      have hfold : List.foldl (fun acc b => acc * 256 + UInt8.toNat b)
          (a * 256 ^ k + n / 256 % 256 ^ k) [UInt8.ofNat (n % 256)]
          = (a * 256 ^ k + n / 256 % 256 ^ k) * 256 + n % 256 := by
        simp [uint8_to_nat_of_nat, Nat.mod_mod_of_dvd]
      rw [hfold]
      have hre : (a * 256 ^ k + n / 256 % 256 ^ k) * 256 + n % 256
          = a * (256 ^ k * 256) + (n / 256 % 256 ^ k * 256 + n % 256) := by ring
      rw [hre, hstep]
      have hp : (256 : Nat) ^ k * 256 = 256 ^ (k + 1) := by ring
      have hq : (256 : Nat) * 256 ^ k = 256 ^ (k + 1) := by ring
      rw [hp, hq]

theorem read_word (n : Nat) : readBytes (word n) = n % wordBound := by
  have h := fold_word_aux 32 0 n
  simpa [readBytes, word, wordBound] using h

theorem word_injective {n m : Nat} (hn : n < wordBound) (hm : m < wordBound)
    (h : word n = word m) : n = m := by
  have h2 := congrArg readBytes h
  rw [read_word, read_word, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at h2
  exact h2

theorem word_peel {n m : Nat} {r s : Verifier.Bytes} (hn : n < wordBound) (hm : m < wordBound)
    (h : word n ++ r = word m ++ s) : n = m ∧ r = s := by
  have hl : (word n).length = (word m).length := by rw [word_length, word_length]
  exact ⟨word_injective hn hm (List.append_inj_left h hl), List.append_inj_right h hl⟩

theorem base_lt_bound (x : Verifier.Base) : x.val < wordBound := by
  have h : x.val < Verifier.modulus := x.isLt
  have hb : Verifier.modulus < wordBound := by
    norm_num [Verifier.modulus, Arithmetic.modulus, wordBound]
  omega

def encodeBaseWords : List Verifier.Base → Verifier.Bytes
  | [] => []
  | x :: xs => word x.val ++ encodeBaseWords xs

def encodeBaseList (xs : List Verifier.Base) : Verifier.Bytes :=
  word xs.length ++ encodeBaseWords xs

theorem encode_base_words_peel : ∀ {xs ys : List Verifier.Base} {r s : Verifier.Bytes},
    xs.length = ys.length → encodeBaseWords xs ++ r = encodeBaseWords ys ++ s →
    xs = ys ∧ r = s := by
  intro xs
  induction xs with
  | nil =>
      intro ys r s hlen h
      cases ys with
      | nil => exact ⟨rfl, by simpa [encodeBaseWords] using h⟩
      | cons y ys => simp at hlen
  | cons x xs ih =>
      intro ys r s hlen h
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [encodeBaseWords, List.append_assoc] at h
          obtain ⟨hv, h⟩ := word_peel (base_lt_bound x) (base_lt_bound y) h
          have hx : x = y := Fin.val_injective hv
          obtain ⟨hxs, hr⟩ := ih (by simpa using hlen) h
          exact ⟨by rw [hx, hxs], hr⟩

theorem base_list_peel {xs ys : List Verifier.Base} {r s : Verifier.Bytes}
    (hx : xs.length < wordBound) (hy : ys.length < wordBound)
    (h : encodeBaseList xs ++ r = encodeBaseList ys ++ s) : xs = ys ∧ r = s := by
  simp only [encodeBaseList, List.append_assoc] at h
  obtain ⟨hlen, h⟩ := word_peel hx hy h
  exact encode_base_words_peel hlen h

def padLength (n : Nat) : Nat := (32 - n % 32) % 32

def encodeBytes (bs : Verifier.Bytes) : Verifier.Bytes :=
  word bs.length ++ (bs ++ List.replicate (padLength bs.length) 0)

theorem bytes_peel {a b r s : Verifier.Bytes} (ha : a.length < wordBound)
    (hb : b.length < wordBound) (h : encodeBytes a ++ r = encodeBytes b ++ s) :
    a = b ∧ r = s := by
  simp only [encodeBytes, List.append_assoc] at h
  obtain ⟨hlen, h⟩ := word_peel ha hb h
  have hab : a = b := List.append_inj_left h hlen
  refine ⟨hab, ?_⟩
  have h2 : List.replicate (padLength a.length) (0 : UInt8) ++ r
      = List.replicate (padLength b.length) (0 : UInt8) ++ s := List.append_inj_right h hlen
  rw [hlen] at h2
  exact List.append_inj_right h2 rfl

theorem bytes_injective {a b : Verifier.Bytes} (ha : a.length < wordBound)
    (hb : b.length < wordBound) (h : encodeBytes a = encodeBytes b) : a = b := by
  refine (bytes_peel (r := []) (s := []) ha hb ?_).1
  rw [List.append_nil, List.append_nil]
  exact h

/-! ## 2. `encodeConfig`: the deployed configuration digest preimage

**SOURCE.** The digest the deployed verifier compares on EVERY call is
`keccak256(abi.encode(config))` against the constructor-pinned immutable
`verificationConfigDigest`:

* `_requirePinnedConfiguration`, MleVerifierV2.sol 478-488 (the comparison is
  line 485). This is the ONLY configuration check on the runtime path, and it is
  what `Verifier.verify` / `Verifier.verifyCall` model as
  `e.configurationHash c ≠ pin.configDigest → .error .configuration`
  (Verifier.lean 413 and 433).
* The pin: `bytes32 public immutable verificationConfigDigest` (MleVerifierV2.sol
  77), computed as `keccak256(abi.encode(config_))` (MleVerifierV2.sol 149) and
  assigned at MleVerifierV2.sol 180. So `Verifier.Pinned.configDigest` IS
  `verificationConfigDigest`.
* The encoded struct: `MleVerifierV2.VerificationConfig` (MleVerifierV2.sol
  110-118) = `CircuitConfigV2.Parameters circuit` (CircuitConfigV2.sol 18-27,
  eight `uint256`), `bytes publicInputWireMap`, `uint256[] kIs`,
  `uint256[] subgroupGenPowers`, `GateInfoV2[] gates`,
  `SpongefishWhirVerify.WhirParams whir`.
* The byte-exact Rust mirror, which fixes the ORDER used below:
  `solidity_abi_encode_verification_config_v2`, src/fixture_v2.rs 1974-2032 --
  eight scalar words in the order degreeBits, numPublicInputs, numConstants,
  numRoutedWires, numWires, numSelectors, numGateConstraints,
  quotientDegreeFactor, then the five dynamic members in the order
  publicInputWireMap, kIs, subgroupGenPowers, gates, whir. The Rust digest is
  `Keccak256::digest(solidity_abi_encode_verification_config_v2(..))`,
  src/fixture_v2.rs 1102-1104.
* `abi_base_array` (src/fixture_v2.rs 2644-2651) is a length word followed by one
  word per element -- that is `encodeBaseList`. `abi_bytes` (src/fixture_v2.rs
  2739-2750) is a length word followed by the bytes padded up to a multiple of 32
  -- that is `encodeBytes`. (`abi_bytes_encoded_len`, src/fixture_v2.rs 2431-2435,
  is the size predictor for that layout, not the layout itself.)

A DIFFERENT digest, `circuitConfigDigest` (MleVerifierV2.sol 78, computed by
`CircuitConfigV2.digest`, CircuitConfigV2.sol 30-91, `keccak256(preimage)` at
line 91; Rust `circuit_config_digest_v2`, src/vk_v2.rs 334-345 over the preimage
of src/vk_v2.rs 198-292; checked in Rust at src/verifier_v2.rs 156-165), is NOT
the runtime configuration guard: on the Solidity path it is a constructor-pinned
immutable that is only ABSORBED INTO THE TRANSCRIPT (MleVerifierV2.sol 430). The
Lean `Verifier.Config` carries it as the field `circuitConfigDigest`, consumed by
`OuterInitial.derive`, and it is one of the six residue fields below.

**THE THREE DEPARTURES from `abi.encode`.** `encodeConfig` is a MIRROR, not a
bit-exact transcription:

1. The leading top-level offset word and the five head offset words
   (src/fixture_v2.rs 2016-2027) are ELIDED. They are a function of the lengths
   that the encoding already carries, so eliding them neither adds nor removes
   injectivity; it only means `encodeConfig c` is not literally the deployed
   preimage byte string.
2. `gates` and `whir` are encoded by `encodeBytes` from the Lean `Config`'s
   OPAQUE byte fields `gatesEncoding` and `whirEncoding`. The source encodes a
   `GateInfoV2[]` and a `WhirParams` tuple there, and the BYTE LAYOUT DIFFERS at
   both positions, not merely the field names. At `gates` the source writes
   `abi_gate_info_array` (src/fixture_v2.rs 2671-2698): a count word followed by
   NINE words per element -- gateId, selectorIndex, groupStart, groupEnd,
   gateRowIndex, numConstraints, numOrConsts, param2, param3. At `whir` it splices
   in a DYNAMIC TUPLE with its own internal head and tail, obtained by stripping
   the standalone encoding's top-level offset word (src/fixture_v2.rs 1996-2002,
   spliced at 2014), and a tuple carries NO leading length word at all. `encodeBytes`
   wraps each as one length word plus padded bytes, which is neither of those two
   shapes. The adopted `Verifier.Config` carries no structured counterpart for
   either -- `gatesEncoding` is exactly the byte string `Integrated.evaluateGate`
   decodes and `whirEncoding` is exactly the byte string
   `PinnedWhirProfile.decodeParams` decodes -- so no fields are invented here, but
   `encodeConfig c` is correspondingly not the deployed preimage at these two
   positions either.
3. Lean's `Nat` is unbounded, Solidity's `uint256` is not. Injectivity therefore
   carries `Bounded`, whose eleven non-opaque components follow from
   `Verifier.envelope` (`bounded_of_envelope`).

**SOURCE FIELDS WITH NO LEAN COUNTERPART.** None: every member of
`VerificationConfig` has one, with `gates` and `whir` abstracted to byte strings
as in (2).

**LEAN FIELDS THE DEPLOYED DIGEST DOES NOT BIND** -- six, and
`residue_fields_are_not_encoded` proves it by `rfl`: `gateRows`, `indexBits`,
`circuitDigest`, `circuitConfigDigest`, `whirProtocolId`, `whirSessionId`. In the
source each is pinned by a DIFFERENT mechanism: `gates.length` and the derived
index-bit count live inside the encoded `gates` array (capped at MleVerifierV2.sol
501) and `_constituentIndexBits` (MleVerifierV2.sol 718) respectively;
`circuitDigest` is four constructor immutables `circuitDigest0..3`
(MleVerifierV2.sol 83-86) checked against the PROOF at `_requireCanonicalProof`
(MleVerifierV2.sol 557-560); `circuitConfigDigest`, `whirProtocolId` and
`whirSessionId` are constructor immutables (MleVerifierV2.sol 78, 80-82) rather
than call-time configuration.

FOUR of the six are nonetheless pinned inside this model.
`envelope_and_core_determine_index_bits` shows `Verifier.envelope` pins `indexBits`
uniquely from the encoded width; `PinnedWhirProfile.profileOk` -- kept as conjunct
(ii) of `explicitDeployment` -- pins `whirProtocolId` and `whirSessionId` against
the table. And `gateRows`, while genuinely UNENCODED, is pinned by ACCEPTANCE
rather than by the digest: `Integrated.verify` requires `gateResult = some _`, and
`Integrated.evaluateGate` returns `none` unless `gates.length = c.gateRows` for
`gates = gdec c.gatesEncoding` -- and `gatesEncoding` IS inside the encoding. So
`accepted_gate_rows_are_the_decoded_length` recovers `c.gateRows` as the decoded
length on every accepted call, and `accepted_gate_rows_match_deployed_gates` then
identifies it with the length decoded from the DEPLOYED `c₀.gatesEncoding`, modulo
a `khash` collision. `gateRows` is therefore not free: an adversary who changes it
without changing `gatesEncoding` is rejected by the gate preflight, not by the
configuration guard.

**THE GENUINE RESIDUE IS `circuitDigest` AND `circuitConfigDigest` ONLY.** Neither
is encoded, neither is recovered, and in the MODEL both are ATTACKER-CHOSEN
TRANSCRIPT INPUTS: `circuitDigest` reaches `OuterInitial.derive` through
`Verifier.statement` (OuterInitial.lean 71; `Verifier.shape`, Verifier.lean 135,
only forces the proof's copy to agree with the configuration's) and
`circuitConfigDigest` is absorbed directly (OuterInitial.lean 76). In Solidity both
are fixed by constructor immutables -- `circuitDigest0..3` compared against the
proof at MleVerifierV2.sol 557-560, and `circuitConfigDigest` absorbed from the
immutable at MleVerifierV2.sol 430 -- so neither is call-time data there. What this
gap is, precisely: nothing in the model CONSUMES either field semantically (circuit
truth is open, and `Verifier.verify` never relates `circuitDigest` to any circuit),
so the freedom is a TRANSCRIPT DEGREE OF FREEDOM. Its consequences belong to the
unformalized half (B) of the Fiat--Shamir reading -- whether a chosen absorbed
prefix helps an adversary steer the squeezes -- and not to a model-internal break:
no theorem below is weakened by it, and no theorem below rules it out.

`example_residue_variant_has_the_same_encoding` witnesses the ENCODING half of this
only. It says the digest guard does not separate a residue variant; it is NOT a
statement that such a variant is accepted, and it cannot be, because `gateRows := 9`
there would have to survive the gate preflight as well.
-/

structure Core where
  degreeBits : Nat
  numPublicInputs : Nat
  numConstants : Nat
  numRouted : Nat
  numWires : Nat
  numSelectors : Nat
  numGateConstraints : Nat
  quotientDegree : Nat
  publicInputWireMap : Verifier.Bytes
  kIs : List Verifier.Base
  subgroupPowers : List Verifier.Base
  gatesEncoding : Verifier.Bytes
  whirEncoding : Verifier.Bytes
  deriving DecidableEq

def core (c : Verifier.Config) : Core :=
  { degreeBits := c.degreeBits, numPublicInputs := c.numPublicInputs,
    numConstants := c.numConstants, numRouted := c.numRouted, numWires := c.numWires,
    numSelectors := c.numSelectors, numGateConstraints := c.numGateConstraints,
    quotientDegree := c.quotientDegree, publicInputWireMap := c.publicInputWireMap,
    kIs := c.kIs, subgroupPowers := c.subgroupPowers, gatesEncoding := c.gatesEncoding,
    whirEncoding := c.whirEncoding }

def encodeConfig (c : Verifier.Config) : Verifier.Bytes :=
  word c.degreeBits ++ (word c.numPublicInputs ++ (word c.numConstants ++
    (word c.numRouted ++ (word c.numWires ++ (word c.numSelectors ++
      (word c.numGateConstraints ++ (word c.quotientDegree ++
        (encodeBytes c.publicInputWireMap ++ (encodeBaseList c.kIs ++
          (encodeBaseList c.subgroupPowers ++ (encodeBytes c.gatesEncoding ++
            encodeBytes c.whirEncoding)))))))))))

structure Bounded (c : Verifier.Config) : Prop where
  degreeBits : c.degreeBits < wordBound
  numPublicInputs : c.numPublicInputs < wordBound
  numConstants : c.numConstants < wordBound
  numRouted : c.numRouted < wordBound
  numWires : c.numWires < wordBound
  numSelectors : c.numSelectors < wordBound
  numGateConstraints : c.numGateConstraints < wordBound
  quotientDegree : c.quotientDegree < wordBound
  publicInputWireMap : c.publicInputWireMap.length < wordBound
  kIs : c.kIs.length < wordBound
  subgroupPowers : c.subgroupPowers.length < wordBound
  gatesEncoding : c.gatesEncoding.length < wordBound
  whirEncoding : c.whirEncoding.length < wordBound

/-- **THE ENCODING IS INJECTIVE ON WHAT IT ENCODES.** Two bounded configurations
with the same encoding agree on all thirteen members of the source's
`VerificationConfig`. They need NOT be equal as `Verifier.Config` values: the six
residue fields of section 2 are not encoded, and `residue_fields_are_not_encoded`
exhibits that directly. This is the honest form of "`encodeConfig` is injective"
for an abstraction whose `Config` carries more than the deployed struct. -/
theorem encode_config_injective {c c' : Verifier.Config} (hc : Bounded c) (hc' : Bounded c')
    (h : encodeConfig c = encodeConfig c') : core c = core c' := by
  simp only [encodeConfig] at h
  obtain ⟨e1, h⟩ := word_peel hc.degreeBits hc'.degreeBits h
  obtain ⟨e2, h⟩ := word_peel hc.numPublicInputs hc'.numPublicInputs h
  obtain ⟨e3, h⟩ := word_peel hc.numConstants hc'.numConstants h
  obtain ⟨e4, h⟩ := word_peel hc.numRouted hc'.numRouted h
  obtain ⟨e5, h⟩ := word_peel hc.numWires hc'.numWires h
  obtain ⟨e6, h⟩ := word_peel hc.numSelectors hc'.numSelectors h
  obtain ⟨e7, h⟩ := word_peel hc.numGateConstraints hc'.numGateConstraints h
  obtain ⟨e8, h⟩ := word_peel hc.quotientDegree hc'.quotientDegree h
  obtain ⟨e9, h⟩ := bytes_peel hc.publicInputWireMap hc'.publicInputWireMap h
  obtain ⟨e10, h⟩ := base_list_peel hc.kIs hc'.kIs h
  obtain ⟨e11, h⟩ := base_list_peel hc.subgroupPowers hc'.subgroupPowers h
  obtain ⟨e12, h⟩ := bytes_peel hc.gatesEncoding hc'.gatesEncoding h
  have e13 := bytes_injective hc.whirEncoding hc'.whirEncoding h
  simp only [core, Core.mk.injEq]
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩

theorem bounded_of_envelope {c : Verifier.Config} (h : Verifier.envelope c = true)
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound) :
    Bounded c := by
  have hbig : (1000 : Nat) < wordBound := by norm_num [wordBound]
  simp only [Verifier.envelope, decide_eq_true_eq] at h
  obtain ⟨hd0, hd13, -, hw160, hr80, hrw, hpi, hs0, hsc, hgc, hq0, hq10, hgr0, hgr255,
    hkl, hsl, hpl, hcl, hib, hib2, hib3⟩ := h
  have hwd : Verifier.width c
      = max (c.numConstants + c.numRouted) (max c.numWires (2 * c.numRouted)) := rfl
  rw [hwd] at hw160
  have hnc : c.numConstants + c.numRouted ≤ 160 := le_trans (le_max_left _ _) hw160
  have hnw : c.numWires ≤ 160 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hw160
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, hg, hw⟩

theorem index_bits_unique {w k k' : Nat} (h1 : w ≤ 2 ^ k)
    (h2 : k = 0 ∨ 2 ^ (k - 1) < w) (h3 : w ≤ 2 ^ k') (h4 : k' = 0 ∨ 2 ^ (k' - 1) < w) :
    k = k' := by
  have aux : ∀ a b : Nat, a < b → w ≤ 2 ^ a → (b = 0 ∨ 2 ^ (b - 1) < w) → False := by
    intro a b hab hle hb
    rcases hb with hb | hb
    · omega
    · have : (2 : Nat) ^ a ≤ 2 ^ (b - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd (aux k k' hlt h1 h4) (by simp)
  · exact heq
  · exact absurd (aux k' k hgt h3 h2) (by simp)

/-! ## 3. The explicit engine

The field table, with the "function of" column that is the point of this module.
Every entry is a function of the six explicit parameters ONLY; no row reads a
`Verifier.Engine`.

| field | value | function of |
|---|---|---|
| `configurationHash` | `concreteConfigurationHash khash` | `khash` |
| `deploymentValid` | `explicitDeployment P c₀` | `P`, `c₀` |
| `initialObservation` | `InstalledInitialTranscript.concreteInitialObservation thash` | `thash` |
| `commitRound` | `InstalledRoundCommit.concreteCommitRound thash` | `thash` |
| `sampleIndices` | `InstalledIndexSampler.concreteSampleIndices thash` | `thash` |
| `foldClaim` | `Connections.packedFold` | nothing |
| `normEvaluation` | `Norm.normEvaluation` | nothing |
| `publicInputsHash` | `PublicInputHashBinding.hashNoPad` | nothing |
| `gateEvaluation` | `Integrated.evaluateGate gdec …` | `gdec` |
| `eqEvaluation` | `Norm.eqEvaluation` | nothing |
| `parseWhir` | `InstalledWhirParse.concreteParseWhir hash (pinnedParams P c₀)` | `hash`, `P`, `c₀` |
| `whirTail` | `InstalledWhirTail.installedTail hash (pinnedParams P c₀)` | `hash`, `P`, `c₀` |

`explicitBase` exists ONLY to name a witness for the transfer identities of
section 4; it is `Verifier.testEngine` with the two former observations replaced,
its `deploymentValid` is `Verifier.testEngine`'s constant `fun _ => true`
(Verifier.lean 603), and all eight of the fields it inherits from `testEngine`
are overwritten downstream. `explicit_has_no_observation` is the statement that
the resulting engine mentions none of it. -/

/-- The configuration hash as an arbitrary deterministic `khash` over the
concrete encoding of section 2. NOTHING is assumed of `khash`: it is exactly as
unconstrained as `thash` in `CommitmentOrder` and `hash` in `InstalledWhirTail`,
so no conclusion below is a collision-resistance claim. -/
def concreteConfigurationHash (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.Config → Verifier.Root := fun c => khash (encodeConfig c)

/-- `PinnedWhirProfile.pinnedDeployment P e c₀` with its FIRST conjunct -- the
abstract `e.deploymentValid c` -- removed, which is what makes the engine
base-free. What that conjunct stood for, and why removing it is defensible, is
the subject of section 5. -/
def explicitDeployment (P : Profile) (c₀ : Verifier.Config) : Verifier.Config → Bool :=
  fun c => decide (c.whirEncoding = c₀.whirEncoding) && PinnedWhirProfile.profileOk P c

theorem explicit_deployment_exact (P : Profile) (c₀ c : Verifier.Config) :
    explicitDeployment P c₀ c = true ↔
      c.whirEncoding = c₀.whirEncoding ∧ PinnedWhirProfile.profileOk P c = true := by
  simp [explicitDeployment]

def explicitBase (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : Profile) (c₀ : Verifier.Config) : Verifier.Engine :=
  { Verifier.testEngine with
      configurationHash := concreteConfigurationHash khash,
      parseWhir := InstalledWhirParse.concreteParseWhir hash
        (PinnedWhirProfile.pinnedParams P c₀) }

def explicitEngine (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : Profile) (c₀ : Verifier.Config) : Verifier.Engine where
  configurationHash := concreteConfigurationHash khash
  deploymentValid := explicitDeployment P c₀
  initialObservation := InstalledInitialTranscript.concreteInitialObservation thash
  commitRound := InstalledRoundCommit.concreteCommitRound thash
  sampleIndices := InstalledIndexSampler.concreteSampleIndices thash
  foldClaim := Connections.packedFold
  normEvaluation := Norm.normEvaluation
  publicInputsHash := InstalledInitialTranscript.concretePublicInputsHash
  gateEvaluation := fun c wires constants publicHash alpha =>
    (Integrated.evaluateGate gdec c wires constants publicHash alpha).getD Verifier.zero
  eqEvaluation := Norm.eqEvaluation
  parseWhir := InstalledWhirParse.concreteParseWhir hash (PinnedWhirProfile.pinnedParams P c₀)
  whirTail := InstalledWhirTail.installedTail hash (PinnedWhirProfile.pinnedParams P c₀)

/-- **(b) NO FIELD MENTIONS A `Verifier.Engine`.** The engine is definitionally
a twelve-field record literal every one of whose entries is written out in terms
of `gdec`, `hash`, `thash`, `khash`, `P` and `c₀`. There is no base to
instantiate, no observation left to install, and no hook an adversary or a
later module could choose. -/
theorem explicit_has_no_observation (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) :
    explicitEngine gdec hash thash khash P c₀ =
      { configurationHash := fun c => khash (encodeConfig c),
        deploymentValid := fun c =>
          decide (c.whirEncoding = c₀.whirEncoding) && PinnedWhirProfile.profileOk P c,
        initialObservation := fun c s =>
          OuterInitial.toInitial (OuterInitial.derive thash c s),
        commitRound := InstalledRoundCommit.concreteCommitRound thash,
        sampleIndices := InstalledIndexSampler.concreteSampleIndices thash,
        foldClaim := Connections.packedFold,
        normEvaluation := Norm.normEvaluation,
        publicInputsHash := PublicInputHashBinding.hashNoPad,
        gateEvaluation := fun c wires constants publicHash alpha =>
          (Integrated.evaluateGate gdec c wires constants publicHash alpha).getD Verifier.zero,
        eqEvaluation := Norm.eqEvaluation,
        parseWhir := InstalledWhirParse.concreteParseWhir hash
          (PinnedWhirProfile.pinnedParams P c₀),
        whirTail := InstalledWhirTail.installedTail hash
          (PinnedWhirProfile.pinnedParams P c₀) } := rfl

/-- **(a) THE EXPLICIT ENGINE IS THE COMPOSED ENGINE OVER *EVERY* BASE.** For an
ARBITRARY `e`, installing the concrete parse, the concrete configuration hash and
the base-free deployment predicate on `ComposedEngine.composedEngine e …` yields
this engine. Two consequences: the engine is base-independent
(`explicit_is_base_independent`), and every `ComposedEngine` theorem transfers by
instantiating its base at `explicitBase` (section 4). -/
theorem explicit_is_composed_over_any_base (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    explicitEngine gdec hash thash khash P c₀ =
      { ComposedEngine.composedEngine e gdec hash thash P c₀ with
          parseWhir := InstalledWhirParse.concreteParseWhir hash
            (PinnedWhirProfile.pinnedParams P c₀),
          configurationHash := concreteConfigurationHash khash,
          deploymentValid := explicitDeployment P c₀ } := rfl

theorem explicit_is_base_independent (e e' : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    ({ ComposedEngine.composedEngine e gdec hash thash P c₀ with
        parseWhir := InstalledWhirParse.concreteParseWhir hash
          (PinnedWhirProfile.pinnedParams P c₀),
        configurationHash := concreteConfigurationHash khash,
        deploymentValid := explicitDeployment P c₀ } : Verifier.Engine) =
      { ComposedEngine.composedEngine e' gdec hash thash P c₀ with
          parseWhir := InstalledWhirParse.concreteParseWhir hash
            (PinnedWhirProfile.pinnedParams P c₀),
          configurationHash := concreteConfigurationHash khash,
          deploymentValid := explicitDeployment P c₀ } := rfl

theorem explicit_is_composed_over_the_explicit_base (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    explicitEngine gdec hash thash khash P c₀ =
      ComposedEngine.composedEngine (explicitBase hash khash P c₀) gdec hash thash P c₀ := rfl

theorem explicit_is_the_installed_parse_engine (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    explicitEngine gdec hash thash khash P c₀ =
      InstalledWhirParse.installedParseEngine
        (ComposedEngine.roundBase (explicitBase hash khash P c₀) thash P c₀) gdec hash
        (PinnedWhirProfile.pinnedParams P c₀) thash := rfl

theorem explicit_is_its_own_model_engine (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    Integrated.modelEngine (explicitEngine gdec hash thash khash P c₀) gdec =
      explicitEngine gdec hash thash khash P c₀ := rfl

theorem explicit_twelve_fields (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) :
    (explicitEngine gdec hash thash khash P c₀).configurationHash =
      concreteConfigurationHash khash ∧
    (explicitEngine gdec hash thash khash P c₀).deploymentValid = explicitDeployment P c₀ ∧
    (explicitEngine gdec hash thash khash P c₀).initialObservation =
      InstalledInitialTranscript.concreteInitialObservation thash ∧
    (explicitEngine gdec hash thash khash P c₀).commitRound =
      InstalledRoundCommit.concreteCommitRound thash ∧
    (explicitEngine gdec hash thash khash P c₀).sampleIndices =
      InstalledIndexSampler.concreteSampleIndices thash ∧
    (explicitEngine gdec hash thash khash P c₀).foldClaim = Connections.packedFold ∧
    (explicitEngine gdec hash thash khash P c₀).normEvaluation = Norm.normEvaluation ∧
    (explicitEngine gdec hash thash khash P c₀).publicInputsHash =
      PublicInputHashBinding.hashNoPad ∧
    (explicitEngine gdec hash thash khash P c₀).gateEvaluation =
      (fun c wires constants publicHash alpha =>
        (Integrated.evaluateGate gdec c wires constants publicHash alpha).getD Verifier.zero) ∧
    (explicitEngine gdec hash thash khash P c₀).eqEvaluation = Norm.eqEvaluation ∧
    (explicitEngine gdec hash thash khash P c₀).parseWhir =
      InstalledWhirParse.concreteParseWhir hash (PinnedWhirProfile.pinnedParams P c₀) ∧
    (explicitEngine gdec hash thash khash P c₀).whirTail =
      InstalledWhirTail.installedTail hash (PinnedWhirProfile.pinnedParams P c₀) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. Transfer: every adopted result, at the explicit engine

**NO NEW PROOF CONTENT IN THIS SECTION.** Because
`explicit_is_composed_over_the_explicit_base` and
`explicit_is_the_installed_parse_engine` are `rfl`, each `ComposedEngine`
result applies with its base instantiated at `explicitBase hash khash P c₀`,
and each `InstalledWhirParse` result applies with its base instantiated at
`ComposedEngine.roundBase (explicitBase hash khash P c₀) thash P c₀` and its
parameter record at `PinnedWhirProfile.pinnedParams P c₀`. Acceptance under the
explicit engine is still a DIFFERENT predicate from acceptance under
`composedEngine e …` for a general `e` -- the configuration guard, the parse and
the deployment predicate all differ -- which is why nothing is transported; the
identities are used instead. -/

abbrev VkParams := InstalledWhirTail.VkParams

/-- `ComposedEngine.composed_acceptance_summary` at the explicit engine: the
sixteen-conjunct headline now holds for an engine with no observation left.
Its caveats are unchanged, including the three conjuncts that are CONSTANTS
rather than consequences of acceptance (the two `OuterInitial.derive` digest
facts and the frame-list lengths). -/
theorem explicit_acceptance_summary (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (hT : PinnedWhirProfile.TableIsCanonical P) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : VkParams)
    (hrow : PinnedWhirProfile.canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    c.degreeBits ≤ 13 ∧
    PinnedWhirProfile.paramsOfConfig P c = some wq ∧
    PinnedWhirProfile.pinnedParams P c₀ = wq ∧
    0 < wq.inDomainSamples ∧
    (∀ (position : Nat) (root : Verifier.Root),
      [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root →
      ∃ (r : WhirTail.Result) (opening : WhirIntermediate.Opening) (rows : List WhirRows.RawRow)
        (offset next : Nat),
        InstalledWhirTail.tailRun hash wq
          (Verifier.derivedContext (explicitEngine gdec hash thash khash P c₀) c p)
          p.whirTranscript p.whirHints = some r ∧
        InstalledWhirTail.RoundOneOpening hash wq (InstalledWhirTail.outerBytes p.whirHints)
          r opening ∧
        opening.indices ≠ [] ∧
        opening.groups.get? position = some rows ∧
        Merkle.verify hash (InstalledWhirTail.rootDigest root)
          (WhirConfigured.initialOpen wq).merkleDepth opening.indices
          (WhirRows.rowHashes hash rows) (InstalledWhirTail.outerBytes p.whirHints) offset
          = some next) ∧
    (∀ result : OuterAdapter.Execution, OuterAdapter.execute thash c p = some result →
      result.rounds = Verifier.derivedRounds (explicitEngine gdec hash thash khash P c₀) c p ∧
      result.initial = (explicitEngine gdec hash thash khash P c₀).initialTranscript c p ∧
      result.indices.points =
        Verifier.derivedIndices (explicitEngine gdec hash thash khash P c₀) c p ∧
      result.context = Verifier.derivedContext (explicitEngine gdec hash thash khash P c₀) c p) ∧
    (Verifier.derivedRounds (explicitEngine gdec hash thash khash P c₀) c p).logPoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.logChallengeOf thash) ∧
    (Verifier.derivedRounds (explicitEngine gdec hash thash khash P c₀) c p).gatePoint =
      (InstalledRoundCommit.actualChain thash c p).map
        (InstalledRoundCommit.gateChallengeOf thash) ∧
    (∃ st, OuterAdapter.decode
        (Verifier.derivedRounds (explicitEngine gdec hash thash khash P c₀) c p).transcript =
          some st ∧
      OuterAdapter.claimsCommitted thash st p.used =
        OuterInitial.absorbMessages thash st (InstalledIndexSampler.claimFrames p.used) ∧
      (InstalledIndexSampler.claimFrames p.used).length = 8) ∧
    (Verifier.derivedIndices (explicitEngine gdec hash thash khash P c₀) c p).log.length =
      c.indexBits ∧
    (Verifier.derivedIndices (explicitEngine gdec hash thash khash P c₀) c p).gate.length =
      c.indexBits ∧
    TranscriptProvenance.DerivedInitial thash (explicitEngine gdec hash thash khash P c₀) c p ∧
    (OuterInitial.derive thash c (Verifier.statement p)).state.digest =
      (OuterInitial.absorbMessages thash OuterInitial.startState
        (CommitmentOrder.gateChallengeFrames c (Verifier.statement p))).digest ∧
    (CommitmentOrder.gateChallengeFrames c (Verifier.statement p)).length = 22 ∧
    p.publicInputs.length ≤ PublicInputHashBinding.maxPublicInputs ∧
    PublicInputHashBinding.rawPublicInputsHash (p.publicInputs.map Fin.val) =
      some ((explicitEngine gdec hash thash khash P c₀).publicInputsHash p.publicInputs) :=
  ComposedEngine.composed_acceptance_summary (explicitBase hash khash P c₀) gdec hash thash P
    hT c₀ pin chain c p wq hrow hacc

theorem explicit_accepted_profile_is_canonical (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ wp, PinnedWhirProfile.paramsOfConfig P c = some wp ∧
      PinnedWhirProfile.canonicalProfileCheck P c wp = true ∧
      PinnedWhirProfile.paramsOfConfig P c₀ = some wp ∧
      PinnedWhirProfile.pinnedParams P c₀ = wp ∧
      PinnedWhirProfile.minProfileVariables ≤ wp.numVariables ∧
      wp.numVariables ≤ PinnedWhirProfile.maxProfileVariables ∧
      wp.numVariables = c.degreeBits + c.indexBits :=
  ComposedEngine.composed_accepted_profile_is_canonical (explicitBase hash khash P c₀) gdec hash
    thash P c₀ pin chain c p hacc

theorem explicit_verify_whir_concrete_iff (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (ctx : Verifier.WhirContext) (p : Verifier.Proof) :
    Verifier.verifyWhir (explicitEngine gdec hash thash khash P c₀) ctx p = true ↔
      ∃ s, InstalledWhirParse.prefixRun hash (PinnedWhirProfile.pinnedParams P c₀) ctx
            p.whirTranscript p.whirHints = some s ∧
        (InstalledWhirParse.parsedOf s).actualRoots = ctx.roots ∧
        (InstalledWhirParse.parsedOf s).boundRoots = ctx.roots ∧
        Verifier.claimsMatch ctx.expectedClaims (InstalledWhirParse.parsedOf s).claims = true ∧
        InstalledWhirTail.installedTail hash (PinnedWhirProfile.pinnedParams P c₀) ctx
          p.whirTranscript p.whirHints (InstalledWhirParse.parsedOf s) = true :=
  InstalledWhirParse.verify_whir_concrete_iff
    (ComposedEngine.roundBase (explicitBase hash khash P c₀) thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash ctx p

theorem explicit_accepted_verify_first_root_is_pinned (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Verifier.verify (explicitEngine gdec hash thash khash P c₀) pin chain c p = .ok ()) :
    (InstalledWhirTail.outerBytes p.whirTranscript).take 32 =
      (Transcript.le 32 pin.preprocessedRoot.val).reverse :=
  InstalledWhirParse.accepted_verify_first_root_is_pinned
    (ComposedEngine.roundBase (explicitBase hash khash P c₀) thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash pin chain c p h

theorem explicit_wrong_root_in_transcript_is_rejected (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (ctx : Verifier.WhirContext) (p : Verifier.Proof) (pre : Verifier.Root)
    (rest : List Verifier.Root) (hroots : ctx.roots = pre :: rest)
    (hbytes : (InstalledWhirTail.outerBytes p.whirTranscript).take 32 ≠
      (Transcript.le 32 pre.val).reverse) :
    (explicitEngine gdec hash thash khash P c₀).parseWhir ctx p.whirTranscript p.whirHints
        = none ∧
    Verifier.verifyWhir (explicitEngine gdec hash thash khash P c₀) ctx p = false :=
  InstalledWhirParse.wrong_root_in_transcript_is_rejected
    (ComposedEngine.roundBase (explicitBase hash khash P c₀) thash P c₀) gdec hash
    (PinnedWhirProfile.pinnedParams P c₀) thash ctx p pre rest hroots hbytes

/-! ## 5. The configuration digest binds the configuration

**WHAT `explicitDeployment` DROPPED.** `PinnedWhirProfile.pinnedDeployment P e c₀`
is `e.deploymentValid c && decide (c.whirEncoding = c₀.whirEncoding) && profileOk P c`.
The first conjunct is the adopted ABSTRACT deployment observation; it stands for
whatever the deployment checks beyond the configuration digest and the canonical
profile. From the source, that is the CONSTRUCTOR-ONLY validation:
`_validateConfiguration` (MleVerifierV2.sol 490-549: the numeric caps
(492-502), the wire-map row/column bounds (505-512), `whir.numCommitments`,
`whir.numVectors`, the three empty evaluation-point lists and `rounds.length`
(517-522), `whir.numVariables = degreeBits + _constituentIndexBits(width)`
(523-526), the `kIs[i] = g^i` coset-shift chain (527-532) and the canonical
squared subgroup-generator chain ending at `p - 1` (534-548)),
`Plonky2GateEvaluatorExt3.validateConfiguration` (MleVerifierV2.sol 154-161),
`CanonicalWhirProfileV2.validateCanonical` (MleVerifierV2.sol 151-153) and
`SpongefishWhirVerify.validateParameters` (MleVerifierV2.sol 166).

**NONE of those runs on the runtime path.** The runtime configuration check is
`_requirePinnedConfiguration` alone -- one digest comparison, MleVerifierV2.sol
478-488 -- and its own comment says re-running the nested validation "only burns
gas and cannot strengthen that equality check". So for the SOLIDITY boundary the
deployment check IS exactly config digest plus (constructor-time) canonical
profile, and dropping the abstract conjunct drops nothing the runtime performs.
`Verifier.verifyCall`, the model of that boundary, already omits `deploymentValid`
entirely.

For the RUST boundary (`verifier_v2.rs`, which re-derives and re-checks the
configuration on every call -- `mle_verify_v2`, src/verifier_v2.rs 57-175) the
conjunct did have content. What of it SURVIVES concretely in this model:

* `Verifier.envelope` (the numeric caps and the length equations, checked by
  `Verifier.verify`);
* `PinnedWhirProfile.profileOk` (`validateCanonical`, kept as conjunct (ii));
* `explicit_accepted_profile_is_canonical`'s
  `wp.numVariables = c.degreeBits + c.indexBits` (recovered from acceptance, not
  assumed);
* `Plonky2GateEvaluatorExt3.validateConfiguration` (MleVerifierV2.sol 154-161).
  `Gates.validateConfiguration` (Gates.lean, whose header names that exact source
  at line 5) is a transcription of it, and it is not an assumption here but a
  CONSEQUENCE of every accepted call:
  `Integrated.successful_gate_evaluation_checks_all_metadata` extracts
  `Gates.validateConfiguration (Integrated.gateConfig c) gates = some ()` from the
  gate preflight, and `accepted_gate_rows_are_the_decoded_length` restates that at
  this engine. What survives here is the configuration validation, not full
  evaluation. (Coverage note: `Gates.lean`'s own partial evaluator handles ids
  0,1,2,3,6,7 only, but the integrated entry uses `GatesComplete.evaluateUnfiltered`,
  which evaluates all 14 configured families — `GateEvaluatorCoverage.coverage_status`.)

What does NOT survive, and is the residue of this module:

* the canonical `kIs` and `subgroupGenPowers` VALUE chains (MleVerifierV2.sol
  527-532 and 534-548; src/verifier_v2.rs 120-123 and 130-146). The Lean `Config`
  carries both as `List Base`, so their canonicity is expressible and simply not
  proved here;
* the WIRE-MAP ROW/COLUMN BOUNDS (MleVerifierV2.sol 505-512: each three-byte entry
  must decode to `row < 2 ^ degreeBits` and `column < numRoutedWires`; Rust
  `decode_public_input_wire_map_v2`, src/verifier_v2.rs 150-155). `Verifier.envelope`
  checks only `publicInputWireMap.length = 3 * numPublicInputs`; the CONTENT of the
  map is unconstrained in this model, and `publicInputWireMap` is an encoded field,
  so the digest pins it to the deployment but nothing here says the deployed value
  is in range;
* `SpongefishWhirVerify.validateParameters` (MleVerifierV2.sol 166), which concerns
  a structured `WhirParams` record the Lean `Config` does not carry.

**WHAT IS GAINED.** Conjunct (i) of `pinnedDeployment` -- the WHIR-bytes pin
`c.whirEncoding = c₀.whirEncoding`, which `PinnedWhirProfile`'s header calls an
explicit keccak idealisation -- becomes a THEOREM modulo an explicit `khash`
collision, because `whirEncoding` is inside the encoded struct:
`accepted_whir_bytes_are_the_deployed_ones`. And
`weak_acceptance_recovers_the_deployment_predicate` shows the conjunct is
REDUNDANT: an engine whose `deploymentValid` is `profileOk P` alone still forces
the full `explicitDeployment P c₀ c = true` on any accepted call, modulo the same
collision, so `weak_acceptance_gives_full_acceptance` turns acceptance under the
weaker predicate into acceptance under this module's. -/

/-- The explicit collision disjunct. It is a `Prop` about an arbitrary function,
NOT a bound, a probability, or an assumption discharged anywhere. -/
def KhashCollision (khash : Verifier.Bytes → Verifier.Root) : Prop :=
  ∃ a b, a ≠ b ∧ khash a = khash b

/-- **(c) THE DIGEST BINDS THE PREIMAGE OR `khash` COLLIDES.** The bare
disjunction, with the collision written out. It is only useful together with
`encode_config_injective`, which turns the left disjunct into equality of all
thirteen encoded configuration fields -- see `config_digest_binds_the_core`. -/
theorem config_digest_binds_the_configuration (khash : Verifier.Bytes → Verifier.Root)
    (c c' : Verifier.Config)
    (h : concreteConfigurationHash khash c = concreteConfigurationHash khash c') :
    encodeConfig c = encodeConfig c' ∨ ∃ a b, a ≠ b ∧ khash a = khash b := by
  by_cases he : encodeConfig c = encodeConfig c'
  · exact Or.inl he
  · exact Or.inr ⟨encodeConfig c, encodeConfig c', he, h⟩

theorem config_digest_binds_the_core (khash : Verifier.Bytes → Verifier.Root)
    (c c' : Verifier.Config) (hc : Bounded c) (hc' : Bounded c')
    (h : concreteConfigurationHash khash c = concreteConfigurationHash khash c') :
    core c = core c' ∨ KhashCollision khash := by
  rcases config_digest_binds_the_configuration khash c c' h with he | hcol
  · exact Or.inl (encode_config_injective hc hc' he)
  · exact Or.inr hcol

/-! **`Bounded c` IS NOT AN EXTRA ASSUMPTION ON THE ADVERSARY.** Eleven of its
thirteen components follow from `Verifier.envelope`, which `Verifier.verify`
CHECKS, so on any accepted call only the two opaque byte-length bounds remain --
and those are a statement that the call's own calldata fits a `uint256` length,
not a restriction on which configuration the adversary submits. The theorems
below therefore have variants taking `hg` and `hw` in place of `hc`. -/
theorem bounded_of_integrated_acceptance (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hacc : Integrated.verify e gdec pin chain c p = .ok ()) : Bounded c := by
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    e gdec pin chain c p hacc
  exact bounded_of_envelope (Verifier.verify_success_checks _ pin chain c p hv).2.2.1 hg hw

theorem bounded_of_acceptance (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) : Bounded c :=
  bounded_of_integrated_acceptance _ gdec pin chain c p hg hw hacc

/-- **(d) AN ACCEPTED CALL HASHED THE DEPLOYED DIGEST.** The configuration guard
is no longer an opaque observation: acceptance says literally that `khash` of
`encodeConfig c` -- the MIRROR of the accepted configuration's ABI encoding, with
the three departures of section 2 -- is the constructor-pinned digest. -/
theorem accepted_configuration_is_the_pinned_one (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    khash (encodeConfig c) = pin.configDigest := by
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  exact (Verifier.verify_success_checks _ pin chain c p hv).2.1

/-- **(d) WITH THE DEPLOYMENT HYPOTHESIS: THE ACCEPTED CONFIGURATION *IS* THE
DEPLOYED ONE, OR `khash` COLLIDES.** `hdep` is the deployment fact that the
pinned digest was computed from `c₀` -- the Lean counterpart of
`verificationConfigDigest = keccak256(abi.encode(config_))` in the constructor
(MleVerifierV2.sol 149, 180). It is a HYPOTHESIS, not a consequence: nothing in
the model establishes what a deployer pinned. -/
theorem accepted_configuration_is_the_deployed_one (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hdep : pin.configDigest = khash (encodeConfig c₀)) (hc : Bounded c) (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    core c = core c₀ ∨ KhashCollision khash := by
  have h := accepted_configuration_is_the_pinned_one gdec hash thash khash P c₀ pin chain c p hacc
  rw [hdep] at h
  exact config_digest_binds_the_core khash c c₀ hc hc₀ h

/-- The same conclusion with `Bounded c` DISCHARGED from the accepted call. Only
the two opaque byte-length bounds are hypotheses; every numeric bound comes from
the envelope the verifier itself checks. -/
theorem accepted_configuration_is_the_deployed_one_from_lengths
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hdep : pin.configDigest = khash (encodeConfig c₀))
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    core c = core c₀ ∨ KhashCollision khash :=
  accepted_configuration_is_the_deployed_one gdec hash thash khash P c₀ pin chain c p hdep
    (bounded_of_acceptance gdec hash thash khash P c₀ pin chain c p hg hw hacc) hc₀ hacc

/-- **`gateRows` IS PINNED BY ACCEPTANCE, NOT BY THE DIGEST.** It is one of the
six fields `encodeConfig` does not encode, but `Integrated.verify` runs the gate
preflight, and `Integrated.evaluateGate` returns `none` unless the decoded
`gatesEncoding` has exactly `c.gateRows` entries. Since `gatesEncoding` IS encoded,
an accepted call determines `gateRows` as the decoded length -- so `gateRows` is
NOT part of the genuine residue of section 2. The same extraction also yields
`Gates.validateConfiguration`, the transcription of
`Plonky2GateEvaluatorExt3.validateConfiguration`. -/
theorem accepted_gate_rows_are_the_decoded_length (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ gates, gdec c.gatesEncoding = some gates ∧ gates.length = c.gateRows ∧
      Gates.validateConfiguration (Integrated.gateConfig c) gates = some () := by
  obtain ⟨_, gate, _, hg, _⟩ := Integrated.accepted_preflights_and_original_verifier
    (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  obtain ⟨gates, hd, hr, -, -, -, hv⟩ :=
    Integrated.successful_gate_evaluation_checks_all_metadata gdec c _ _ _ _ gate hg
  exact ⟨gates, hd, hr, hv⟩

/-- With the deployment hypothesis: the accepted `gateRows` is the length of the
gate list decoded from the DEPLOYED configuration's `gatesEncoding`, modulo a
`khash` collision. -/
theorem accepted_gate_rows_match_deployed_gates (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hdep : pin.configDigest = khash (encodeConfig c₀)) (hc : Bounded c) (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    (∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c.gateRows) ∨
      KhashCollision khash := by
  rcases accepted_configuration_is_the_deployed_one gdec hash thash khash P c₀ pin chain c p
    hdep hc hc₀ hacc with hcore | hcol
  · obtain ⟨gates, hd, hr, -⟩ := accepted_gate_rows_are_the_decoded_length gdec hash thash khash
      P c₀ pin chain c p hacc
    have he : c.gatesEncoding = c₀.gatesEncoding := congrArg Core.gatesEncoding hcore
    exact Or.inl ⟨gates, he ▸ hd, hr⟩
  · exact Or.inr hcol

theorem accepted_gate_rows_match_deployed_gates_from_lengths (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hdep : pin.configDigest = khash (encodeConfig c₀))
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    (∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c.gateRows) ∨
      KhashCollision khash :=
  accepted_gate_rows_match_deployed_gates gdec hash thash khash P c₀ pin chain c p hdep
    (bounded_of_acceptance gdec hash thash khash P c₀ pin chain c p hg hw hacc) hc₀ hacc

theorem accepted_whir_bytes_are_the_deployed_ones (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hdep : pin.configDigest = khash (encodeConfig c₀)) (hc : Bounded c) (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    c.whirEncoding = c₀.whirEncoding ∨ KhashCollision khash := by
  rcases accepted_configuration_is_the_deployed_one gdec hash thash khash P c₀ pin chain c p
    hdep hc hc₀ hacc with hcore | hcol
  · exact Or.inl (congrArg Core.whirEncoding hcore)
  · exact Or.inr hcol

theorem accepted_whir_bytes_are_the_deployed_ones_from_lengths (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hdep : pin.configDigest = khash (encodeConfig c₀))
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    c.whirEncoding = c₀.whirEncoding ∨ KhashCollision khash :=
  accepted_whir_bytes_are_the_deployed_ones gdec hash thash khash P c₀ pin chain c p hdep
    (bounded_of_acceptance gdec hash thash khash P c₀ pin chain c p hg hw hacc) hc₀ hacc

/-! The deployment predicate with conjunct (i) removed. -/
def weakExplicitEngine (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) : Verifier.Engine :=
  { explicitEngine gdec hash thash khash P c₀ with
      deploymentValid := PinnedWhirProfile.profileOk P }

theorem weak_engine_configuration_hash (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    (weakExplicitEngine gdec hash thash khash P c₀).configurationHash =
      concreteConfigurationHash khash ∧
    (weakExplicitEngine gdec hash thash khash P c₀).deploymentValid =
      PinnedWhirProfile.profileOk P :=
  ⟨rfl, rfl⟩

theorem weak_acceptance_recovers_the_deployment_predicate (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hdep : pin.configDigest = khash (encodeConfig c₀)) (hc : Bounded c) (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (weakExplicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    explicitDeployment P c₀ c = true ∨ KhashCollision khash := by
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (weakExplicitEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  have hs := Verifier.verify_success_checks _ pin chain c p hv
  have hdigest : khash (encodeConfig c) = pin.configDigest := hs.2.1
  have hprofile : PinnedWhirProfile.profileOk P c = true := hs.2.2.2.1
  rw [hdep] at hdigest
  rcases config_digest_binds_the_core khash c c₀ hc hc₀ hdigest with hcore | hcol
  · exact Or.inl ((explicit_deployment_exact P c₀ c).mpr
      ⟨congrArg Core.whirEncoding hcore, hprofile⟩)
  · exact Or.inr hcol

theorem weak_bounded_of_acceptance (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hacc : Integrated.verify (weakExplicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) : Bounded c :=
  bounded_of_integrated_acceptance _ gdec pin chain c p hg hw hacc

theorem weak_acceptance_recovers_the_deployment_predicate_from_lengths
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hdep : pin.configDigest = khash (encodeConfig c₀))
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (weakExplicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    explicitDeployment P c₀ c = true ∨ KhashCollision khash :=
  weak_acceptance_recovers_the_deployment_predicate gdec hash thash khash P c₀ pin chain c p hdep
    (weak_bounded_of_acceptance gdec hash thash khash P c₀ pin chain c p hg hw hacc) hc₀ hacc

theorem weak_acceptance_gives_full_acceptance (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hd : explicitDeployment P c₀ c = true)
    (hacc : Integrated.verify (weakExplicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p = .ok () := by
  obtain ⟨norm, gate, hn, hg, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (weakExplicitEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  have hs := Verifier.verify_success_checks _ pin chain c p hv
  have henv : Verifier.envelope c = true := hs.2.2.1
  have hdw := hs.2.2.2.1
  have hcall := (Verifier.checked_boundary_agrees_with_call
    (Integrated.modelEngine (weakExplicitEngine gdec hash thash khash P c₀) gdec) pin chain c p
    henv hdw) ▸ hv
  have hcall2 : Verifier.verifyCall
      (Integrated.modelEngine (explicitEngine gdec hash thash khash P c₀) gdec) pin chain c p
        = .ok () := hcall
  have hfull : Verifier.verify
      (Integrated.modelEngine (explicitEngine gdec hash thash khash P c₀) gdec) pin chain c p
        = .ok () :=
    Verifier.call_acceptance_yields_checked_acceptance _ pin chain c p henv hd hcall2
  have hn' : Integrated.normResult
      (Integrated.modelEngine (explicitEngine gdec hash thash khash P c₀) gdec) c p = some norm :=
    hn
  have hg' : Integrated.gateResult
      (Integrated.modelEngine (explicitEngine gdec hash thash khash P c₀) gdec) gdec c p
        = some gate := hg
  simp only [Integrated.verify, hn', hg']
  exact hfull

theorem explicit_deployment_is_the_pinned_one_without_the_abstract_conjunct
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) :
    explicitDeployment P c₀ =
      PinnedWhirProfile.pinnedDeployment P (explicitBase hash khash P c₀) c₀ := rfl

theorem pinned_deployment_adds_exactly_the_abstract_conjunct (P : Profile)
    (e : Verifier.Engine) (c₀ c : Verifier.Config) :
    PinnedWhirProfile.pinnedDeployment P e c₀ c = true ↔
      e.deploymentValid c = true ∧ explicitDeployment P c₀ c = true := by
  rw [PinnedWhirProfile.pinned_deployment_exact, explicit_deployment_exact]

def residueVariant (c : Verifier.Config) (gr ib : Nat) (cd : List Verifier.Base)
    (ccd : Verifier.Root) (pid sid : Verifier.Bytes) : Verifier.Config :=
  { c with
      gateRows := gr, indexBits := ib, circuitDigest := cd, circuitConfigDigest := ccd,
      whirProtocolId := pid, whirSessionId := sid }

theorem residue_fields_are_not_encoded (c : Verifier.Config) (gr ib : Nat)
    (cd : List Verifier.Base) (ccd : Verifier.Root) (pid sid : Verifier.Bytes) :
    encodeConfig (residueVariant c gr ib cd ccd pid sid) = encodeConfig c := rfl

theorem core_determines_width {c c' : Verifier.Config} (h : core c = core c') :
    Verifier.width c = Verifier.width c' := by
  have h1 := congrArg Core.numConstants h
  have h2 := congrArg Core.numRouted h
  have h3 := congrArg Core.numWires h
  simp only [core] at h1 h2 h3
  simp only [Verifier.width, h1, h2, h3]

theorem envelope_and_core_determine_index_bits {c c' : Verifier.Config}
    (hc : Verifier.envelope c = true) (hc' : Verifier.envelope c' = true)
    (h : core c = core c') : c.indexBits = c'.indexBits := by
  have hw := core_determines_width h
  simp only [Verifier.envelope, decide_eq_true_eq] at hc hc'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hA, hB⟩ := hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hA', hB'⟩ := hc'
  rw [hw] at hA hB
  exact index_bits_unique hA hB hA' hB'

theorem accepted_configuration_matches_the_deployment_up_to_the_residue
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (henv₀ : Verifier.envelope c₀ = true) (hdep : pin.configDigest = khash (encodeConfig c₀))
    (hc : Bounded c) (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    (core c = core c₀ ∧ c.indexBits = c₀.indexBits) ∨ KhashCollision khash := by
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  have henv : Verifier.envelope c = true := (Verifier.verify_success_checks _ pin chain c p hv).2.2.1
  rcases accepted_configuration_is_the_deployed_one gdec hash thash khash P c₀ pin chain c p
    hdep hc hc₀ hacc with hcore | hcol
  · exact Or.inl ⟨hcore, envelope_and_core_determine_index_bits henv henv₀ hcore⟩
  · exact Or.inr hcol

theorem accepted_configuration_matches_the_deployment_up_to_the_residue_from_lengths
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (henv₀ : Verifier.envelope c₀ = true) (hdep : pin.configDigest = khash (encodeConfig c₀))
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    (core c = core c₀ ∧ c.indexBits = c₀.indexBits) ∨ KhashCollision khash :=
  accepted_configuration_matches_the_deployment_up_to_the_residue gdec hash thash khash P c₀
    pin chain c p henv₀ hdep
    (bounded_of_acceptance gdec hash thash khash P c₀ pin chain c p hg hw hacc) hc₀ hacc

/-- **THE FULL PICTURE AT ONE ACCEPTED CALL.** Everything the digest and the gate
preflight together pin, with `Bounded c` discharged: the thirteen encoded fields,
`indexBits` (from the envelope), and `gateRows` (as the decoded gate-list length).
What is left free is exactly `circuitDigest` and `circuitConfigDigest` -- the two
genuine residue fields of section 2, both pure transcript inputs in this model. -/
theorem accepted_call_pins_everything_but_the_two_digests (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (henv₀ : Verifier.envelope c₀ = true) (hdep : pin.configDigest = khash (encodeConfig c₀))
    (hg : c.gatesEncoding.length < wordBound) (hw : c.whirEncoding.length < wordBound)
    (hc₀ : Bounded c₀)
    (hacc : Integrated.verify (explicitEngine gdec hash thash khash P c₀) gdec pin chain c p
      = .ok ()) :
    (core c = core c₀ ∧ c.indexBits = c₀.indexBits ∧
      ∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c.gateRows) ∨
      KhashCollision khash := by
  rcases accepted_configuration_matches_the_deployment_up_to_the_residue_from_lengths gdec hash
    thash khash P c₀ pin chain c p henv₀ hdep hg hw hc₀ hacc with ⟨hcore, hib⟩ | hcol
  · rcases accepted_gate_rows_match_deployed_gates_from_lengths gdec hash thash khash P c₀ pin
      chain c p hdep hg hw hc₀ hacc with hgates | hcol
    · exact Or.inl ⟨hcore, hib, hgates⟩
    · exact Or.inr hcol
  · exact Or.inr hcol

/-! ## 6. Examples

The adopted `OuterAdapter` fixture under the explicit engine (shapes and `rfl`
only -- no digest space is enumerated and nothing below is a fixture of the
deployed profile), and three small configurations that witness what the
configuration digest does and does not separate. -/

theorem example_fixture_initial_is_derived (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) :
    TranscriptProvenance.DerivedInitial InstalledRoundCommit.toyHash
      (explicitEngine gdec hash InstalledRoundCommit.toyHash khash P c₀)
      OuterAdapter.fixtureConfig OuterAdapter.fixtureProof := rfl

theorem example_fixture_index_lanes (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    (Verifier.derivedIndices (explicitEngine gdec hash InstalledRoundCommit.toyHash khash P c₀)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).log.length = 1 ∧
    (Verifier.derivedIndices (explicitEngine gdec hash InstalledRoundCommit.toyHash khash P c₀)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).gate.length = 1 :=
  ComposedEngine.example_fixture_index_lanes (explicitBase hash khash P c₀) gdec hash P c₀

theorem example_fixture_snapshot_decodes (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) :
    ∃ st, OuterAdapter.decode
      (Verifier.derivedRounds (explicitEngine gdec hash InstalledRoundCommit.toyHash khash P c₀)
        OuterAdapter.fixtureConfig OuterAdapter.fixtureProof).transcript = some st :=
  ComposedEngine.example_fixture_snapshot_decodes (explicitBase hash khash P c₀) gdec hash P c₀

theorem example_fixture_public_input_hash (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    (explicitEngine gdec hash thash khash P c₀).publicInputsHash
        OuterAdapter.fixtureProof.publicInputs =
      PublicInputHashBinding.hashNoPad OuterAdapter.fixtureProof.publicInputs ∧
    ((explicitEngine gdec hash thash khash P c₀).publicInputsHash
      OuterAdapter.fixtureProof.publicInputs).length = 4 :=
  ComposedEngine.example_fixture_public_input_hash (explicitBase hash khash P c₀) gdec hash
    thash P c₀

theorem zero_lt_word_bound : 0 < wordBound := by norm_num [wordBound]

theorem one_lt_word_bound : 1 < wordBound := by norm_num [wordBound]

def exampleWhirVariant : Verifier.Config := { Verifier.testConfig with whirEncoding := [7] }

def exampleGateVariant : Verifier.Config :=
  { Verifier.testConfig with numGateConstraints := 2 }

theorem example_test_config_is_bounded : Bounded Verifier.testConfig :=
  bounded_of_envelope (by decide) zero_lt_word_bound zero_lt_word_bound

theorem example_whir_variant_is_bounded : Bounded exampleWhirVariant :=
  bounded_of_envelope (by decide) zero_lt_word_bound one_lt_word_bound

theorem example_gate_variant_is_bounded : Bounded exampleGateVariant :=
  bounded_of_envelope (by decide) zero_lt_word_bound zero_lt_word_bound

theorem example_whir_variant_has_a_different_encoding :
    encodeConfig exampleWhirVariant ≠ encodeConfig Verifier.testConfig := by
  intro h
  exact absurd (congrArg Core.whirEncoding
    (encode_config_injective example_whir_variant_is_bounded example_test_config_is_bounded h))
    (by decide)

theorem example_gate_variant_has_a_different_encoding :
    encodeConfig exampleGateVariant ≠ encodeConfig Verifier.testConfig := by
  intro h
  exact absurd (congrArg Core.numGateConstraints
    (encode_config_injective example_gate_variant_is_bounded example_test_config_is_bounded h))
    (by decide)

def exampleResidueVariant : Verifier.Config :=
  residueVariant Verifier.testConfig 9 0 (List.replicate 4 (Verifier.base 1))
    ⟨1, by norm_num⟩ [3] [4]

/-- **THIS IS A STATEMENT ABOUT THE DIGEST GUARD, NOT ABOUT ACCEPTANCE.** The
variant has the same encoding, so `_requirePinnedConfiguration`'s Lean counterpart
cannot separate it from `Verifier.testConfig`. It does NOT follow that the variant
would be ACCEPTED: `gateRows := 9` here, and
`accepted_gate_rows_are_the_decoded_length` says any accepted call has `gateRows`
equal to the length decoded from `gatesEncoding`, which the gate preflight checks
independently of the digest. Of the six fields changed below, only `circuitDigest`
and `circuitConfigDigest` are free under acceptance as well. -/
theorem example_residue_variant_has_the_same_encoding :
    encodeConfig exampleResidueVariant = encodeConfig Verifier.testConfig := rfl

end Audit.Wire3.ExplicitEngine
