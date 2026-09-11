import Audit.Wire3.CanonicalProofCheck
import Audit.Wire3.VkSubgroupProvenance

/-!
# The Rust call boundary: a second deployment predicate, and its exact relation
to the Solidity one

## The two boundaries

`ExplicitEngine` and `CanonicalProofCheck` model the SOLIDITY RUNTIME PATH. There
the per-call configuration guard is `_requirePinnedConfiguration` alone -- ONE
digest comparison, MleVerifierV2.sol 478-488 -- so the adopted deployment
predicate is
`canonicalDeployment P c₀ c = (c.whirEncoding = c₀.whirEncoding) && profileOk P c
&& (the two digests equal the deployed ones)`, and `ExplicitEngine`'s section 5
records explicitly that everything else `_validateConfiguration` checks
(MleVerifierV2.sol 490-549) is CONSTRUCTOR-ONLY and therefore absent from the
runtime path.

The RUST entry point `mle_verify_v2` (src/verifier_v2.rs 57-193) is a different
trust boundary with a different shape. It takes THREE inputs -- `common_data`,
`vk` and `proof` -- and it re-derives and re-checks, on EVERY call, what the
Solidity constructor checked once: the digest lengths (79-83), the resource
envelope and width profile (85-95 including `num_gate_constraints` at 97 and the
quotient degree at 98-99), the lookup admission (67-70), the coset shifts
(120-123), the canonical squared subgroup-generator powers (130-147), the
gate metadata against `collect_gate_info_v2` (148-149), the wire map (150-155),
the `circuit_config_digest` recomputation (156-166), the WHIR protocol and session
identifiers (167-175) and `proof.circuit_digest` against the key (176-179).

This module gives that boundary its own explicit deployment predicate,
`rustDeployment`, installs it as `rustEngine` (the adopted `explicitEngine` with
ONE field replaced, exactly as `CanonicalProofCheck.pinnedProofEngine` replaces
it), and proves the two boundaries' relationship in four directions.

## The model difference, stated once

**SOLIDITY PINS BY DIGEST; RUST VALIDATES STRUCTURE.** On the Solidity path the
deployed configuration is fixed at construction and the caller's configuration is
accepted only by matching an immutable digest; `deploymentValid` is therefore a
predicate that mentions `c₀`. In Rust the verification key IS the deployment: it
arrives as a call argument, it is compared against NO pinned constant, and the
per-call checks establish that the key is INTERNALLY CONSISTENT (its shifts,
powers, gate metadata, configuration digest and identifiers are the canonical
functions of its own dimensions). Accordingly `rustDeployment` takes no `c₀`
argument at all, and `rust_deployment_reads_no_deployed_constant` states that as
one `rfl`. The security of a Rust call therefore rests on the PROVENANCE of the
`(common_data, vk)` pair, which is outside this model entirely;
`solidity_pins_are_not_implied_by_rust_checks` and the two example theorems
exhibit configurations that pass every Rust check and differ in exactly the fields
the Solidity pin fixes.

**THAT IS A STATEMENT ABOUT THE PREDICATE, NOT ABOUT `rustEngine` ACCEPTANCE.**
`rustEngine` installs `rustDeployment` into the ADOPTED `Verifier.verify`
skeleton, which still runs the Solidity deployment pin on every call: `chain =
pin.chainId` and `configurationHash c = pin.configDigest` (the adopted
`Verifier.verify_success_checks`), and `Verifier.shape` still forces
`p.preprocessedRoot = pin.preprocessedRoot`, the model's stand-in for Rust's
`vk.preprocessed_commitment_root` comparison at src/verifier_v2.rs 184-187. So
acceptance under `rustEngine` is Rust's per-call checks ON TOP OF those guards --
`rust_engine_acceptance_still_reads_the_solidity_pin` states the two of them --
which makes (c) a fortiori, leaves (b) a statement about the PREDICATE
`rustDeployment` alone, and leaves (d) unaffected.

`rustEngine` keeps ELEVEN of `explicitEngine`'s twelve fields, including
`parseWhir` and `whirTail`, which remain keyed to `PinnedWhirProfile.pinnedParams
P c₀` (`rust_engine_whir_tail_is_still_keyed_to_the_deployment`). The Rust WHIR
parameter derivation (`WhirPCS::for_constituents`, src/verifier_v2.rs 168-170) is
NOT re-modelled here; only the deployment predicate changes.

## `vk.k_is == common_data.k_is`: a named modelling decision

src/verifier_v2.rs 120-123 compares the key's coset shifts to the COMMON DATA's.
`CommonCircuitData` has no counterpart in the adopted Lean tree -- `Verifier.Config`
carries one `kIs` list, the key's -- so the comparison is not literally
expressible. `kIsCanonical` instead checks the shifts against plonky2's own
derivation, `get_unique_coset_shifts` (field/src/cosets.rs 9-24), which is
`MULTIPLICATIVE_GROUP_GENERATOR.powers().take(num_shifts)`, i.e. `g^0, .., g^(n-1)`
for `g = 14293326489335486720` (field/src/goldilocks_field.rs 80). That is exactly
the chain the Solidity constructor writes at MleVerifierV2.sol 527-532 with
`BASE_FIELD_MULTIPLICATIVE_GENERATOR_V2` (MleWhirV2.sol 19).

**THE DIRECTION OF THE SUBSTITUTION.** Because the model carries ONE `kIs` list,
the source's comparison `vk.k_is == common_data.k_is` is a TAUTOLOGY here: it
relates two copies the model has identified. `kIsCanonical` is therefore an EXTRA
check, one the source does not make per call, and the model is STRICTER than the
source at this line -- an UNDER-APPROXIMATION of its accept set, `model accept-set
⊊ source accept-set`, not an over-approximation. Rust checks only `vk.k_is ==
common_data.k_is`; that the shifts are the canonical chain is a BUILDER-PROVENANCE
fact (field/src/cosets.rs 20-23, and the assignments at circuit_builder.rs 1216 and
1501), not a per-call Rust guard. The Solidity constructor, by contrast, checks
exactly `kIs[i] = g^i` (MleVerifierV2.sol 527-532). So a Rust caller who supplies a
non-canonical `k_is` in BOTH `vk` and `common_data` is accepted by the source and
rejected by this model, and every theorem below that concludes from
`rustDeployment c = true` concludes from a hypothesis the source need not
establish. It is recorded here rather than silently assumed.

The subgroup-power check needs no such decision: src/verifier_v2.rs 130-147
recomputes from `F::two_adic_subgroup(degree_bits)` (130-147) and the adopted
`VkSubgroupProvenance.checkSubgroupGenPowers` is a transcription of both
`ensure!`s, already proved equivalent to
`EqTableProvenance.SubgroupPowersProvenance`.

## `circuit_config_digest_v2` IS modelled

Section 2 models the preimage. `encodeCircuitConfig` mirrors
`circuit_config_digest_preimage_from_parts_v2` (src/vk_v2.rs 198-293, reached from
`circuit_config_digest_preimage_v2` at 148-190 and hashed by
`circuit_config_digest_v2` at 334-349) field for field, in the source's order: the
domain string `plonky2-mle-circuit-config-v3` (mle_whir_v2.rs 12), the protocol
version `3` (mle_whir_v2.rs 5) and inner extension degree `2` (mle_whir_v2.rs 20)
as `u64` little-endian words, then the eight scalars `degree_bits`,
`num_public_inputs`, `num_constants`, `num_routed_wires`, `num_wires`,
`num_selectors`, `num_gate_constraints`, `quotient_degree_factor`, then the three
length-prefixed field-element vectors `circuit_digest`, `k_is`,
`subgroup_gen_powers` as canonical `u64` little-endian limbs, then the gate count
and the gate blob, then the length-prefixed `public_input_wire_map`. The hash is
an ARBITRARY DETERMINISTIC `khash2 : Bytes → Root`, exactly as `khash` is in
`ExplicitEngine`: keccak is not modelled anywhere in this tree, no collision
resistance is assumed, and `recomputed_digest_binds_the_recomputed_core` carries
an explicit `Khash2Collision khash2` disjunct.

**THE THREE DEPARTURES.** `encodeCircuitConfig` is a MIRROR, not a byte-exact
transcription:

1. The source writes exactly `13 * gates.len()` bytes for the gate array -- five
   `u8` fields (`gate_id`, `selector_index`, `group_start`, `group_end`,
   `gate_row_index`) and four `u16` little-endian fields (`num_constraints`,
   `num_or_consts`, `param2`, `param3`), src/vk_v2.rs 274-286 -- with NO byte-length
   word, because the length is a function of the count. `Verifier.Config` carries
   the gate metadata only as the opaque `gatesEncoding` byte string that
   `Integrated.evaluateGate` decodes, so the mirror writes the faithful gate-count
   word `u64 c.gateRows` followed by `byteVec c.gatesEncoding`, i.e. ONE EXTRA
   length word and a byte string that is not the source's. No field is invented,
   but `encodeCircuitConfig c` is not the deployed preimage at this position.
2. Lean's `Nat` is unbounded and the source's widths are not. Injectivity
   therefore carries `Bounded2`, whose thirteen non-opaque components follow from
   `Verifier.envelope` alone (`bounded2_of_envelope`).
3. `push_u64`'s `u64::try_from` failure path (src/vk_v2.rs 67-71) and
   `decode_public_input_wire_map_v2`'s row/column bounds (src/vk_v2.rs 121-144,
   called at src/verifier_v2.rs 150-155) are not modelled; the wire map enters the
   preimage as opaque bytes, exactly as it does in `ExplicitEngine.encodeConfig`.

`encode_circuit_config_injective` proves the mirror injective on the fourteen
members it encodes, and `residue_fields_are_not_recomputed` exhibits the five
`Verifier.Config` fields it does NOT bind: `indexBits`, `whirEncoding`,
`whirProtocolId`, `whirSessionId` and `circuitConfigDigest` itself.

## What this does NOT mean

**NO REFINEMENT OF THE RUST CODE.** `rustDeployment` is a MANUAL MIRROR of
`mle_verify_v2`'s per-call checks, transcribed by reading the source, in the same
sense that `InstalledWhirTail.installedTail` is a manual model of the tail. There
is no extraction, no Rust semantics, no `anyhow` error-ordering claim, no
allocation or panic model, and no statement about `MleVerificationKeyV2`'s
deserialisation. The checks at src/verifier_v2.rs 180-... (claim lengths, the
sumcheck rounds and the WHIR call) are outside `rustDeployment` by construction:
they are proof-side, and the adopted `Verifier.shape` and `Verifier.verify` model
them.

**KECCAK IS NOT MODELLED.** `khash` and `khash2` are arbitrary deterministic
functions; every conclusion of the form "the accepted configuration is the
deployed one" keeps its `ExplicitEngine.KhashCollision khash` disjunct, and the
digest-binding statement of section 7 keeps a `Khash2Collision khash2` disjunct.

**THE VK IS A TRUSTED INPUT IN RUST.** Nothing here says the key a Rust caller
supplies is the key the prover's circuit produced. That is the whole content of
section 7's counterexamples.

**THE ADOPTED OPEN OBLIGATIONS ARE UNCHANGED.** R1b (WHIR proximity and sumcheck
soundness), R2 (extraction / PCS extractability), half (B) of the Fiat--Shamir
reading, circuit truth, and Rust/Yul/Solidity refinement all remain OPEN.
`Gates`'s evaluator COVERAGE limit stands: the fourteen configured families'
metadata are validated, only ids 0,1,2,3,6,7 are evaluated. The wire-v3 WHIR
profile this tree models is the approximately 100-bit design point. No figure in
this module is a security level, nothing here is the deployed system's soundness
error, and in particular nothing here says "125".
-/

namespace Audit.Wire3.RustCallBoundary

open Audit.Wire3

/-! ## 1. The little-endian digest preimage word -/

def u64Bound : Nat := 256 ^ 8

theorem u64_bound_value : u64Bound = 18446744073709551616 := by norm_num [u64Bound]

def leAux : Nat → Nat → Verifier.Bytes
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: leAux k (n / 256)

def u64 (n : Nat) : Verifier.Bytes := leAux 8 n

def readLe : Verifier.Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * readLe bs

theorem le_aux_length (k n : Nat) : (leAux k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leAux, ih]

theorem u64_length (n : Nat) : (u64 n).length = 8 := le_aux_length 8 n

theorem read_le_aux (k : Nat) : ∀ n : Nat, readLe (leAux k n) = n % 256 ^ k := by
  induction k with
  | zero => intro n; simp [leAux, readLe, Nat.mod_one]
  | succ k ih =>
      intro n
      have hstep := ExplicitEngine.mod_step n (256 ^ k)
      have hpow : (256 : Nat) ^ (k + 1) = 256 * 256 ^ k := by
        rw [Nat.pow_succ]; ring
      simp only [leAux, readLe, ih, ExplicitEngine.uint8_to_nat_of_nat, hpow]
      rw [← hstep, Nat.mod_mod_of_dvd n dvd_rfl]
      ring

theorem read_u64 (n : Nat) : readLe (u64 n) = n % u64Bound := read_le_aux 8 n

theorem u64_injective {n m : Nat} (hn : n < u64Bound) (hm : m < u64Bound)
    (h : u64 n = u64 m) : n = m := by
  have hr := congrArg readLe h
  rw [read_u64, read_u64, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at hr
  exact hr

theorem u64_peel {n m : Nat} {r s : Verifier.Bytes} (hn : n < u64Bound) (hm : m < u64Bound)
    (h : u64 n ++ r = u64 m ++ s) : n = m ∧ r = s := by
  have hlen : (u64 n).length = (u64 m).length := by rw [u64_length, u64_length]
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  exact ⟨u64_injective hn hm h1, h2⟩

theorem base_lt_u64_bound (x : Verifier.Base) : x.val < u64Bound := by
  have h : (x.val : Nat) < 18446744069414584321 := x.isLt
  rw [u64_bound_value]
  omega

def baseWords : List Verifier.Base → Verifier.Bytes
  | [] => []
  | x :: xs => u64 x.val ++ baseWords xs

def baseVec (xs : List Verifier.Base) : Verifier.Bytes := u64 xs.length ++ baseWords xs

def byteVec (bs : Verifier.Bytes) : Verifier.Bytes := u64 bs.length ++ bs

theorem base_words_length (xs : List Verifier.Base) : (baseWords xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [baseWords, List.length_append, u64_length, ih, List.length_cons]
      ring

theorem base_words_peel : ∀ {xs ys : List Verifier.Base} {r s : Verifier.Bytes},
    xs.length = ys.length → baseWords xs ++ r = baseWords ys ++ s → xs = ys ∧ r = s := by
  intro xs
  induction xs with
  | nil =>
      intro ys r s hl h
      have hy : ys = [] := List.eq_nil_of_length_eq_zero hl.symm
      subst hy
      exact ⟨rfl, by simpa [baseWords] using h⟩
  | cons x xs ih =>
      intro ys r s hl h
      cases ys with
      | nil => simp at hl
      | cons y ys =>
          simp only [baseWords, List.append_assoc] at h
          obtain ⟨hv, h⟩ := u64_peel (base_lt_u64_bound x) (base_lt_u64_bound y) h
          have hl' : xs.length = ys.length := by simpa using hl
          obtain ⟨hxs, hrs⟩ := ih hl' h
          exact ⟨by rw [Fin.eq_of_val_eq hv, hxs], hrs⟩

theorem base_vec_peel {xs ys : List Verifier.Base} {r s : Verifier.Bytes}
    (hx : xs.length < u64Bound) (hy : ys.length < u64Bound)
    (h : baseVec xs ++ r = baseVec ys ++ s) : xs = ys ∧ r = s := by
  simp only [baseVec, List.append_assoc] at h
  obtain ⟨hl, h⟩ := u64_peel hx hy h
  exact base_words_peel hl h

theorem byte_vec_peel {a b r s : Verifier.Bytes} (ha : a.length < u64Bound)
    (hb : b.length < u64Bound) (h : byteVec a ++ r = byteVec b ++ s) : a = b ∧ r = s := by
  simp only [byteVec, List.append_assoc] at h
  obtain ⟨hl, h⟩ := u64_peel ha hb h
  exact List.append_inj h hl

theorem byte_vec_injective {a b : Verifier.Bytes} (ha : a.length < u64Bound)
    (hb : b.length < u64Bound) (h : byteVec a = byteVec b) : a = b := by
  have h' : byteVec a ++ [] = byteVec b ++ [] := by rw [List.append_nil, List.append_nil, h]
  exact (byte_vec_peel ha hb h').1

/-! ## 2. `circuit_config_digest_v2`: the preimage, modelled -/

def circuitConfigDomain : Verifier.Bytes := "plonky2-mle-circuit-config-v3".toUTF8.data.toList

def protocolVersionCurrent : Nat := 3

def innerExtensionDegree : Nat := 2

def encodeCircuitConfig (c : Verifier.Config) : Verifier.Bytes :=
  circuitConfigDomain ++ (u64 protocolVersionCurrent ++ (u64 innerExtensionDegree ++
    (u64 c.degreeBits ++ (u64 c.numPublicInputs ++ (u64 c.numConstants ++
      (u64 c.numRouted ++ (u64 c.numWires ++ (u64 c.numSelectors ++
        (u64 c.numGateConstraints ++ (u64 c.quotientDegree ++
          (baseVec c.circuitDigest ++ (baseVec c.kIs ++ (baseVec c.subgroupPowers ++
            (u64 c.gateRows ++
              (byteVec c.gatesEncoding ++ byteVec c.publicInputWireMap)))))))))))))))

structure Core2 where
  degreeBits : Nat
  numPublicInputs : Nat
  numConstants : Nat
  numRouted : Nat
  numWires : Nat
  numSelectors : Nat
  numGateConstraints : Nat
  quotientDegree : Nat
  circuitDigest : List Verifier.Base
  kIs : List Verifier.Base
  subgroupPowers : List Verifier.Base
  gateRows : Nat
  gatesEncoding : Verifier.Bytes
  publicInputWireMap : Verifier.Bytes
  deriving DecidableEq

def core2 (c : Verifier.Config) : Core2 :=
  { degreeBits := c.degreeBits, numPublicInputs := c.numPublicInputs,
    numConstants := c.numConstants, numRouted := c.numRouted, numWires := c.numWires,
    numSelectors := c.numSelectors, numGateConstraints := c.numGateConstraints,
    quotientDegree := c.quotientDegree, circuitDigest := c.circuitDigest, kIs := c.kIs,
    subgroupPowers := c.subgroupPowers, gateRows := c.gateRows,
    gatesEncoding := c.gatesEncoding, publicInputWireMap := c.publicInputWireMap }

structure Bounded2 (c : Verifier.Config) : Prop where
  degreeBits : c.degreeBits < u64Bound
  numPublicInputs : c.numPublicInputs < u64Bound
  numConstants : c.numConstants < u64Bound
  numRouted : c.numRouted < u64Bound
  numWires : c.numWires < u64Bound
  numSelectors : c.numSelectors < u64Bound
  numGateConstraints : c.numGateConstraints < u64Bound
  quotientDegree : c.quotientDegree < u64Bound
  circuitDigest : c.circuitDigest.length < u64Bound
  kIs : c.kIs.length < u64Bound
  subgroupPowers : c.subgroupPowers.length < u64Bound
  gateRows : c.gateRows < u64Bound
  gatesEncoding : c.gatesEncoding.length < u64Bound
  publicInputWireMap : c.publicInputWireMap.length < u64Bound

theorem bounded2_of_envelope {c : Verifier.Config} (h : Verifier.envelope c = true)
    (hg : c.gatesEncoding.length < u64Bound) : Bounded2 c := by
  have hbig : (1000 : Nat) < u64Bound := by rw [u64_bound_value]; norm_num
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
    by omega, by omega, by omega, by omega, hg, by omega⟩

/-- **THE RECOMPUTED PREIMAGE IS INJECTIVE ON WHAT IT ENCODES.** Two `Bounded2`
configurations with the same `circuit_config_digest` preimage agree on all
fourteen members the source hashes. They need NOT be equal as `Verifier.Config`
values: `residue_fields_are_not_recomputed` exhibits the five fields the preimage
does not bind. This is the Rust-side counterpart of
`ExplicitEngine.encode_config_injective`. -/
theorem encode_circuit_config_injective {c c' : Verifier.Config} (hc : Bounded2 c)
    (hc' : Bounded2 c') (h : encodeCircuitConfig c = encodeCircuitConfig c') :
    core2 c = core2 c' := by
  simp only [encodeCircuitConfig] at h
  replace h := List.append_cancel_left h
  replace h := List.append_cancel_left h
  replace h := List.append_cancel_left h
  obtain ⟨e1, h⟩ := u64_peel hc.degreeBits hc'.degreeBits h
  obtain ⟨e2, h⟩ := u64_peel hc.numPublicInputs hc'.numPublicInputs h
  obtain ⟨e3, h⟩ := u64_peel hc.numConstants hc'.numConstants h
  obtain ⟨e4, h⟩ := u64_peel hc.numRouted hc'.numRouted h
  obtain ⟨e5, h⟩ := u64_peel hc.numWires hc'.numWires h
  obtain ⟨e6, h⟩ := u64_peel hc.numSelectors hc'.numSelectors h
  obtain ⟨e7, h⟩ := u64_peel hc.numGateConstraints hc'.numGateConstraints h
  obtain ⟨e8, h⟩ := u64_peel hc.quotientDegree hc'.quotientDegree h
  obtain ⟨e9, h⟩ := base_vec_peel hc.circuitDigest hc'.circuitDigest h
  obtain ⟨e10, h⟩ := base_vec_peel hc.kIs hc'.kIs h
  obtain ⟨e11, h⟩ := base_vec_peel hc.subgroupPowers hc'.subgroupPowers h
  obtain ⟨e12, h⟩ := u64_peel hc.gateRows hc'.gateRows h
  obtain ⟨e13, h⟩ := byte_vec_peel hc.gatesEncoding hc'.gatesEncoding h
  have e14 := byte_vec_injective hc.publicInputWireMap hc'.publicInputWireMap h
  simp only [core2, Core2.mk.injEq]
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩

def residueVariant2 (c : Verifier.Config) (ib : Nat) (we pid sid : Verifier.Bytes)
    (ccd : Verifier.Root) : Verifier.Config :=
  { c with
    indexBits := ib
    whirEncoding := we
    whirProtocolId := pid
    whirSessionId := sid
    circuitConfigDigest := ccd }

/-- **THE RUST DIGEST'S RESIDUE.** `indexBits`, `whirEncoding`, `whirProtocolId`,
`whirSessionId` and `circuitConfigDigest` itself may all be changed without
changing the recomputed preimage. Two of the five -- `indexBits` and the two
identifiers -- are nevertheless pinned by the OTHER Rust conjuncts (`envelope` and
`rustIds`); `whirEncoding` is pinned by nothing at all, which is the content of
section 7. -/
theorem residue_fields_are_not_recomputed (c : Verifier.Config) (ib : Nat)
    (we pid sid : Verifier.Bytes) (ccd : Verifier.Root) :
    encodeCircuitConfig (residueVariant2 c ib we pid sid ccd) = encodeCircuitConfig c := rfl

/-! ## 3. The per-call checks -/

def multiplicativeGenerator : Nat := 14293326489335486720

def cosetShifts (v : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => v :: cosetShifts (Arithmetic.mul v multiplicativeGenerator) k

/-- plonky2's `get_unique_coset_shifts` (field/src/cosets.rs 9-24), which is
`MULTIPLICATIVE_GROUP_GENERATOR.powers().take(num_shifts)`, and the chain the
Solidity constructor writes at MleVerifierV2.sol 527-532. See the header for why
this stands in for src/verifier_v2.rs 120-123's `vk.k_is == common_data.k_is`, and
why standing in makes the model STRICTER than the source at that line. -/
def canonicalKIs (numRouted : Nat) : List Nat := cosetShifts 1 numRouted

theorem coset_shifts_length : ∀ (k v : Nat), (cosetShifts v k).length = k
  | 0, _ => rfl
  | k + 1, v => by
      rw [cosetShifts, List.length_cons, coset_shifts_length k]

theorem canonical_kis_length (n : Nat) : (canonicalKIs n).length = n :=
  coset_shifts_length n 1

theorem coset_shifts_canonical : ∀ (k v : Nat), v < Arithmetic.modulus →
    ∀ x ∈ cosetShifts v k, x < Arithmetic.modulus
  | 0, _, _ => by simp [cosetShifts]
  | k + 1, v, hv => by
      intro x hx
      rw [cosetShifts, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hv
      · exact coset_shifts_canonical k _ (Nat.mod_lt _ (by decide)) x hx

def kIsCanonical (c : Verifier.Config) : Bool :=
  decide (c.kIs.map Fin.val = canonicalKIs c.numRouted)

def subgroupPowersCanonical (c : Verifier.Config) : Bool :=
  decide (c.subgroupPowers.map Fin.val =
    VkSubgroupProvenance.expectedSubgroupGenPowers c.degreeBits)

theorem rust_admission_without_lookups (cfg : Gates.Config) (gates : List Gates.GateInfo) :
    Gates.rustAdmission 0 cfg gates = Gates.validateConfiguration cfg gates := by
  simp [Gates.rustAdmission]

def gatesAdmissible (gdec : Integrated.DecodeGates) (c : Verifier.Config) : Bool :=
  match gdec c.gatesEncoding with
  | none => false
  | some gates => decide (gates.length = c.gateRows ∧
      Gates.rustAdmission 0 (Integrated.gateConfig c) gates = some ())

abbrev Profile := PinnedWhirProfile.Profile

def rustIds (P : Profile) (c : Verifier.Config) : Bool :=
  decide (c.whirSessionId = P.sessionId ∧
    c.whirProtocolId = P.tableProtocolId (c.degreeBits + c.indexBits))

def configDigestRecomputed (khash2 : Verifier.Bytes → Verifier.Root)
    (c : Verifier.Config) : Bool :=
  decide (c.circuitConfigDigest = khash2 (encodeCircuitConfig c))

/-- **THE RUST CALL BOUNDARY'S DEPLOYMENT PREDICATE.** The conjunction of the
per-call checks of `mle_verify_v2` that are functions of the configuration alone:
the resource/width envelope and the digest-length, constraint-count and
quotient-degree caps (src/verifier_v2.rs 79-99) as `Verifier.envelope`; the coset
shifts (120-123) as `kIsCanonical`; the canonical squared subgroup-generator
powers (130-147) as `subgroupPowersCanonical`; the lookup admission (67-70) and the
per-call gate-metadata validation as `gatesAdmissible`; the
`circuit_config_digest` recomputation (156-166) as `configDigestRecomputed`; and
the WHIR protocol/session identifiers (167-175) as `rustIds`.

`gatesAdmissible`'s citation is worth stating precisely. Line 149's `vk.gates ==
collect_gate_info_v2(common_data)` is a DERIVATION from the unmodelled
`CommonCircuitData` and is residue. What `Gates.validateConfiguration` mirrors is
the STRUCTURAL validation (gate_ext3.rs 437-479), and that does run per call, by a
different route: src/verifier_v2.rs 422 calls `evaluate_gate_aggregation_ext3`,
which reaches gate_ext3.rs 619 and thence 539's `validate_gate_ext3_context`. So
the conjunct is a faithful per-call check with its own line numbers, not a
transcription of 148-149. NOTE THE ABSENT
ARGUMENT: there is no `c₀`. The Rust verifier compares the key against no pinned
constant, so this predicate is a function of the submitted configuration alone.

The proof-side per-call checks -- `proof.circuit_digest == vk.circuit_digest`
(176-179), the public-input length (180-183), the roots (184-193) and the WHIR byte
caps (74-78) -- are NOT here: they are modelled by the adopted `Verifier.shape`
and `Verifier.verify`, which `Integrated.verify` runs on every call. -/
def rustDeployment (gdec : Integrated.DecodeGates) (khash2 : Verifier.Bytes → Verifier.Root)
    (P : Profile) : Verifier.Config → Bool := fun c =>
  Verifier.envelope c && kIsCanonical c && subgroupPowersCanonical c && gatesAdmissible gdec c &&
    configDigestRecomputed khash2 c && rustIds P c

theorem gates_admissible_exact (gdec : Integrated.DecodeGates) (c : Verifier.Config) :
    gatesAdmissible gdec c = true ↔
      ∃ gates, gdec c.gatesEncoding = some gates ∧ gates.length = c.gateRows ∧
        Gates.validateConfiguration (Integrated.gateConfig c) gates = some () := by
  cases h : gdec c.gatesEncoding with
  | none => simp [gatesAdmissible, h]
  | some gates => simp [gatesAdmissible, h, rust_admission_without_lookups]

theorem subgroup_powers_canonical_is_the_source_check (c : Verifier.Config) :
    subgroupPowersCanonical c = true ↔
      VkSubgroupProvenance.checkSubgroupGenPowers c.degreeBits c.subgroupPowers = .ok () := by
  rw [VkSubgroupProvenance.check_accepts_iff]
  simp [subgroupPowersCanonical]

theorem rust_deployment_exact (gdec : Integrated.DecodeGates)
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c : Verifier.Config) :
    rustDeployment gdec khash2 P c = true ↔
      Verifier.envelope c = true ∧ kIsCanonical c = true ∧ subgroupPowersCanonical c = true ∧
      gatesAdmissible gdec c = true ∧ configDigestRecomputed khash2 c = true ∧
      rustIds P c = true := by
  simp only [rustDeployment, Bool.and_eq_true]
  tauto

/-- Everything one accepted Rust deployment predicate yields, written out. The
fourth conjunct is the adopted `EqTableProvenance.SubgroupPowersProvenance`,
obtained from `VkSubgroupProvenance.check_accepts_iff_provenance`; nothing is
re-proved here. -/
theorem rust_deployment_structural (gdec : Integrated.DecodeGates)
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c : Verifier.Config)
    (h : rustDeployment gdec khash2 P c = true) :
    Verifier.envelope c = true ∧
    c.kIs.map Fin.val = canonicalKIs c.numRouted ∧
    VkSubgroupProvenance.checkSubgroupGenPowers c.degreeBits c.subgroupPowers = .ok () ∧
    EqTableProvenance.SubgroupPowersProvenance c.subgroupPowers
      (VkSubgroupProvenance.subgroupGenerator c.degreeBits) c.degreeBits ∧
    (∃ gates, gdec c.gatesEncoding = some gates ∧ gates.length = c.gateRows ∧
      Gates.validateConfiguration (Integrated.gateConfig c) gates = some ()) ∧
    c.circuitConfigDigest = khash2 (encodeCircuitConfig c) ∧
    c.whirSessionId = P.sessionId ∧
    c.whirProtocolId = P.tableProtocolId (c.degreeBits + c.indexBits) := by
  obtain ⟨henv, hk, hs, hg, hd, hi⟩ := (rust_deployment_exact gdec khash2 P c).mp h
  have hs' := (subgroup_powers_canonical_is_the_source_check c).mp hs
  have hi' : c.whirSessionId = P.sessionId ∧
      c.whirProtocolId = P.tableProtocolId (c.degreeBits + c.indexBits) := by
    simpa [rustIds] using hi
  exact ⟨henv, by simpa [kIsCanonical] using hk, hs',
    VkSubgroupProvenance.accepted_vk_has_subgroup_powers_provenance _ _ hs',
    (gates_admissible_exact gdec c).mp hg, by simpa [configDigestRecomputed] using hd,
    hi'.1, hi'.2⟩

/-! ## 4. The Rust engine -/

def rustEngine (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    Verifier.Engine :=
  { ExplicitEngine.explicitEngine gdec hash thash khash P c₀ with
      deploymentValid := rustDeployment gdec khash2 P }

/-- **THE ENGINE IS `explicitEngine` WITH ONE FIELD REPLACED**, as one `rfl`, in
exactly the shape of `CanonicalProofCheck.pinned_proof_is_explicit_with_stronger_deployment`.
No new observation and no new parameter beyond `khash2`. -/
theorem rust_engine_is_explicit_with_the_rust_deployment (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    rustEngine gdec hash thash khash khash2 P c₀ =
      { ExplicitEngine.explicitEngine gdec hash thash khash P c₀ with
          deploymentValid := rustDeployment gdec khash2 P } := rfl

theorem rust_engine_twelve_fields (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (thash : Transcript.Hash) (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile)
    (c₀ : Verifier.Config) :
    (rustEngine gdec hash thash khash khash2 P c₀).configurationHash =
      ExplicitEngine.concreteConfigurationHash khash ∧
    (rustEngine gdec hash thash khash khash2 P c₀).deploymentValid = rustDeployment gdec khash2 P ∧
    (rustEngine gdec hash thash khash khash2 P c₀).initialObservation =
      InstalledInitialTranscript.concreteInitialObservation thash ∧
    (rustEngine gdec hash thash khash khash2 P c₀).commitRound =
      InstalledRoundCommit.concreteCommitRound thash ∧
    (rustEngine gdec hash thash khash khash2 P c₀).sampleIndices =
      InstalledIndexSampler.concreteSampleIndices thash ∧
    (rustEngine gdec hash thash khash khash2 P c₀).foldClaim = Connections.packedFold ∧
    (rustEngine gdec hash thash khash khash2 P c₀).normEvaluation = Norm.normEvaluation ∧
    (rustEngine gdec hash thash khash khash2 P c₀).publicInputsHash =
      PublicInputHashBinding.hashNoPad ∧
    (rustEngine gdec hash thash khash khash2 P c₀).gateEvaluation =
      (fun c wires constants publicHash alpha =>
        (Integrated.evaluateGate gdec c wires constants publicHash alpha).getD Verifier.zero) ∧
    (rustEngine gdec hash thash khash khash2 P c₀).eqEvaluation = Norm.eqEvaluation ∧
    (rustEngine gdec hash thash khash khash2 P c₀).parseWhir =
      InstalledWhirParse.concreteParseWhir hash (PinnedWhirProfile.pinnedParams P c₀) ∧
    (rustEngine gdec hash thash khash khash2 P c₀).whirTail =
      InstalledWhirTail.installedTail hash (PinnedWhirProfile.pinnedParams P c₀) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rust_engine_is_its_own_model_engine (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    Integrated.modelEngine (rustEngine gdec hash thash khash khash2 P c₀) gdec =
      rustEngine gdec hash thash khash khash2 P c₀ := rfl

/-- **THE RUST DEPLOYMENT PREDICATE HAS NO DEPLOYMENT PIN.** The installed
predicate is the same function whatever the deployed configuration is. In Solidity
the deployed configuration enters `deploymentValid` twice (the WHIR-bytes pin and
the two digest pins); in Rust it does not enter at all, because the verification
key IS the deployment. The scope is exactly `deploymentValid`: the next theorem
records that `rustEngine` ACCEPTANCE still carries the Solidity pin, because the
predicate is installed into the adopted `Verifier.verify` skeleton. -/
theorem rust_deployment_reads_no_deployed_constant (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ c₁ : Verifier.Config) :
    (rustEngine gdec hash thash khash khash2 P c₀).deploymentValid =
      (rustEngine gdec hash thash khash khash2 P c₁).deploymentValid := rfl

/-- **`rustEngine` ACCEPTANCE STILL READS THE SOLIDITY PIN.** Replacing
`deploymentValid` does not remove the deployment pin from the CALL: `rustEngine`
keeps `configurationHash = ExplicitEngine.concreteConfigurationHash khash`, and the
adopted `Verifier.verify` skeleton compares that hash with `pin.configDigest` and
`chain` with `pin.chainId` before anything else. `Verifier.shape` likewise still
forces `p.preprocessedRoot = pin.preprocessedRoot`, the model's stand-in for
src/verifier_v2.rs 184-187's `proof.preprocessed_root ==
vk.preprocessed_commitment_root`. So acceptance under `rustEngine` is the Rust
per-call checks ON TOP OF the Solidity skeleton's guards, which is why section 8's
(c) is a fortiori and why section 7's (b) is a statement about `rustDeployment`
alone. -/
theorem rust_engine_acceptance_still_reads_the_solidity_pin (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (rustEngine gdec hash thash khash khash2 P c₀) gdec pin chain c p
      = .ok ()) :
    chain = pin.chainId ∧
    ExplicitEngine.concreteConfigurationHash khash c = pin.configDigest := by
  obtain ⟨-, -, -, -, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (rustEngine gdec hash thash khash khash2 P c₀) gdec pin chain c p hacc
  have hs := Verifier.verify_success_checks _ pin chain c p hv
  exact ⟨hs.1, hs.2.1⟩

/-- The honest qualification to the previous statement: only `deploymentValid`
changed. The two WHIR fields still read `PinnedWhirProfile.pinnedParams P c₀`, so
`rustEngine` is a hybrid -- Rust's deployment predicate over the adopted
installed WHIR tail -- and not a model of the Rust WHIR parameter derivation. -/
theorem rust_engine_whir_tail_is_still_keyed_to_the_deployment (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) :
    (rustEngine gdec hash thash khash khash2 P c₀).whirTail =
      InstalledWhirTail.installedTail hash (PinnedWhirProfile.pinnedParams P c₀) ∧
    (rustEngine gdec hash thash khash khash2 P c₀).parseWhir =
      InstalledWhirParse.concreteParseWhir hash (PinnedWhirProfile.pinnedParams P c₀) :=
  ⟨rfl, rfl⟩

/-- The deployment-side facts about the configuration a deployer pinned: what the
Solidity CONSTRUCTOR establishes once and the Rust verifier re-runs per call. FOUR
of the seven are `_validateConfiguration` groups (MleVerifierV2.sol 490-549) -- the
numeric caps (492-502), the coset-shift chain (527-532), the canonical subgroup
chain (534-548) and the gate validation
(`Plonky2GateEvaluatorExt3.validateConfiguration`, MleVerifierV2.sol 154-161). THE
OTHER THREE COME FROM ELSEWHERE IN THE CONSTRUCTOR, and saying otherwise would
misplace them: `configDigest` is the constructor's `CircuitConfigV2.digest`
(MleVerifierV2.sol 168-176, stored at 181), whose preimage is byte-identical to
src/vk_v2.rs 198-293 by way of CircuitConfigV2.sol 52-89; `sessionId` and
`protocolId` are `CanonicalWhirProfileV2.validateCanonical` (MleVerifierV2.sol
151-153). Like `CanonicalProofCheck.DeployedFacts` these are statements about what
was deployed, never about what a caller submits;
`example_rust_deployed_facts_inhabited` shows they are satisfiable. -/
structure RustDeployedFacts (gdec : Integrated.DecodeGates)
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config) : Prop where
  envelope : Verifier.envelope c₀ = true
  cosetShifts : c₀.kIs.map Fin.val = canonicalKIs c₀.numRouted
  subgroupPowers :
    VkSubgroupProvenance.checkSubgroupGenPowers c₀.degreeBits c₀.subgroupPowers = .ok ()
  gates : ∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c₀.gateRows ∧
    Gates.validateConfiguration (Integrated.gateConfig c₀) gates = some ()
  configDigest : c₀.circuitConfigDigest = khash2 (encodeCircuitConfig c₀)
  sessionId : c₀.whirSessionId = P.sessionId
  protocolId : c₀.whirProtocolId = P.tableProtocolId (c₀.degreeBits + c₀.indexBits)

theorem rust_deployment_of_deployed_facts (gdec : Integrated.DecodeGates)
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (h : RustDeployedFacts gdec khash2 P c₀) : rustDeployment gdec khash2 P c₀ = true := by
  refine (rust_deployment_exact gdec khash2 P c₀).mpr
    ⟨h.envelope, by simpa [kIsCanonical] using h.cosetShifts,
      (subgroup_powers_canonical_is_the_source_check c₀).mpr h.subgroupPowers,
      (gates_admissible_exact gdec c₀).mpr h.gates,
      by simpa [configDigestRecomputed] using h.configDigest,
      by simpa [rustIds] using And.intro h.sessionId h.protocolId⟩

/-! ## 5. The three conjuncts that need no deployment hypothesis -/

/-- First of the three Rust conjuncts that need NO deployment hypothesis at all:
`Verifier.envelope` is checked by `Verifier.verify` on the Solidity path too (the
adopted model's own caveat: it is a call-time Rust check placed in the combined
boundary). -/
theorem rust_envelope_follows_from_acceptance (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) : Verifier.envelope c = true := by
  obtain ⟨-, -, -, -, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  exact (Verifier.verify_success_checks _ pin chain c p hv).2.2.1

/-- Second: the gate conjunct is a CONSEQUENCE of the gate preflight, not an extra
assumption. `Integrated.evaluateGate` returns `none` unless `gatesEncoding` decodes
to exactly `gateRows` entries that pass `Gates.validateConfiguration`, so any
accepted Solidity call already establishes `gatesAdmissible`. -/
theorem rust_gates_conjunct_follows_from_acceptance (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) : gatesAdmissible gdec c = true :=
  (gates_admissible_exact gdec c).mpr
    (ExplicitEngine.accepted_gate_rows_are_the_decoded_length gdec hash thash khash P c₀ pin chain
      c p (CanonicalProofCheck.pinned_acceptance_is_explicit_acceptance gdec hash thash khash P c₀
        pin chain c p hacc))

/-- Third: the identifiers. `PinnedWhirProfile.canonicalProfileCheck` reads the
session id against `P.sessionId` and the protocol id against the table row
`wp.numVariables`, and acceptance forces `wp.numVariables = degreeBits + indexBits`
-- which is the Lean counterpart of Rust's `packed_group_num_vars_v2`. So the
Solidity and Rust identifier checks coincide on any accepted call, even though
Solidity reads the row index out of the decoded VK WHIR bytes and Rust derives it
from the circuit dimensions. -/
theorem rust_ids_conjunct_follows_from_acceptance (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) : rustIds P c = true := by
  obtain ⟨wp, -, hcheck, -, -, -, -, hnv⟩ := CanonicalProofCheck.pinned_accepted_profile_is_canonical
    gdec hash thash khash P c₀ pin chain c p hacc
  obtain ⟨-, -, hsid, -, hpid⟩ := (PinnedWhirProfile.canonical_check_exact P c wp).mp hcheck
  exact by simpa [rustIds] using And.intro hsid (hnv ▸ hpid)

/-! ## 6. (a) the Rust checks under Solidity acceptance -/

/-- **3(a) EVERY RUST PER-CALL CHECK HOLDS FOR AN ACCEPTED SOLIDITY CALL, MODULO A
`khash` COLLISION.** `CanonicalProofCheck.accepted_configuration_is_the_deployment`
gives `c = c₀` or a collision, and the deployed configuration satisfies the
constructor validations by hypothesis. So the Solidity boundary loses nothing the
Rust boundary checks -- the pin plus the constructor does the work the Rust
verifier redoes per call. Three of the six conjuncts -- the envelope, the gates and
the identifiers -- hold with no `RustDeployedFacts` hypothesis at all, as section 5
proves; so only the coset shifts, the subgroup powers and the configuration digest
are genuinely carried by `hr`. -/
theorem rust_checks_are_consequences_of_solidity_acceptance_up_to (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hr : RustDeployedFacts gdec khash2 P c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    rustDeployment gdec khash2 P c = true ∨ ExplicitEngine.KhashCollision khash := by
  rcases CanonicalProofCheck.accepted_configuration_is_the_deployment gdec hash thash khash P c₀
    pin chain c p hd hg hw hacc with heq | hcol
  · exact Or.inl (heq ▸ rust_deployment_of_deployed_facts gdec khash2 P c₀ hr)
  · exact Or.inr hcol

/-! ## 7. (b) the Rust checks do not pin a deployment -/

def Khash2Collision (khash2 : Verifier.Bytes → Verifier.Root) : Prop :=
  ∃ a b, a ≠ b ∧ khash2 a = khash2 b

theorem encode_ignores_the_config_digest (c : Verifier.Config) (r : Verifier.Root) :
    encodeCircuitConfig { c with circuitConfigDigest := r } = encodeCircuitConfig c := rfl

theorem rust_deployment_ignores_the_whir_encoding (gdec : Integrated.DecodeGates)
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c : Verifier.Config)
    (we : Verifier.Bytes) :
    rustDeployment gdec khash2 P { c with whirEncoding := we } =
      rustDeployment gdec khash2 P c := rfl

/-- **3(b) THE CONVERSE FAILS: THE RUST CHECKS PIN NO DEPLOYMENT.** From ONE
configuration passing every Rust check, two configurations passing every Rust check
with DIFFERENT `whirEncoding`, one of which the Solidity deployment predicate
rejects outright. `rustDeployment` never reads `whirEncoding`
(`rust_deployment_ignores_the_whir_encoding`, one `rfl`), and the statement is
stronger than "ignores": the Rust boundary HAS NO SUCH INPUT. `mle_verify_v2`
derives the WHIR parameters from the circuit dimensions
(`WhirPCS::for_constituents`, src/verifier_v2.rs 168) instead of reading them from a
key field, and the `circuit_config_digest` preimage has no position for them
either, so `whirEncoding` is a `Verifier.Config` field with no Rust counterpart at
all. The pin that is missing is the VK's PROVENANCE, and that is outside this
model. -/
theorem solidity_pins_are_not_implied_by_rust_checks (gdec : Integrated.DecodeGates)
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ c : Verifier.Config)
    (we : Verifier.Bytes) (hne : we ≠ c₀.whirEncoding)
    (h : rustDeployment gdec khash2 P c = true) :
    rustDeployment gdec khash2 P { c with whirEncoding := we } = true ∧
    rustDeployment gdec khash2 P { c with whirEncoding := c₀.whirEncoding } = true ∧
    ({ c with whirEncoding := we } : Verifier.Config).whirEncoding ≠
      ({ c with whirEncoding := c₀.whirEncoding } : Verifier.Config).whirEncoding ∧
    ExplicitEngine.explicitDeployment P c₀ { c with whirEncoding := we } = false := by
  refine ⟨h, h, hne, ?_⟩
  simp [ExplicitEngine.explicitDeployment, hne]

theorem envelope_circuit_digest_congr (c : Verifier.Config) (cd : List Verifier.Base)
    (h : cd.length = 4) (henv : Verifier.envelope c = true) :
    Verifier.envelope { c with circuitDigest := cd } = true := by
  simp only [Verifier.envelope, decide_eq_true_eq] at henv ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, -,
    a19, a20, a21⟩ := henv
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, h,
    a19, a20, a21⟩

def digestVariant (khash2 : Verifier.Bytes → Verifier.Root) (c : Verifier.Config)
    (cd : List Verifier.Base) : Verifier.Config :=
  { c with
    circuitDigest := cd
    circuitConfigDigest := khash2 (encodeCircuitConfig { c with circuitDigest := cd }) }

/-- The same separation at the other pinned immutable. Changing `circuitDigest`
DOES change the recomputed preimage, so the variant must carry the recomputed
digest -- and once it does, every Rust check passes again. A Rust caller who
supplies a matching `(circuit_digest, circuit_config_digest)` pair PASSES EVERY
CONFIGURATION CHECK for any circuit whatsoever; the proof still has to verify. -/
theorem rust_deployment_does_not_pin_the_circuit_digest (gdec : Integrated.DecodeGates)
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c : Verifier.Config)
    (cd : List Verifier.Base) (hlen : cd.length = 4)
    (h : rustDeployment gdec khash2 P c = true) :
    rustDeployment gdec khash2 P (digestVariant khash2 c cd) = true ∧
      (digestVariant khash2 c cd).circuitDigest = cd := by
  obtain ⟨henv, hk, hs, hga, -, hi⟩ := (rust_deployment_exact gdec khash2 P c).mp h
  refine ⟨(rust_deployment_exact gdec khash2 P _).mpr
    ⟨envelope_circuit_digest_congr c cd hlen henv, hk, hs, hga, ?_, hi⟩, rfl⟩
  simp only [configDigestRecomputed, decide_eq_true_eq]
  rfl

/-- The Rust digest's binding power, with the collision written out: two accepted
configurations with the same `circuit_config_digest` agree on the fourteen encoded
members, or `khash2` collides. This is what the recomputation buys INSIDE one call;
it says nothing across calls, because nothing pins the digest itself. -/
theorem recomputed_digest_binds_the_recomputed_core (khash2 : Verifier.Bytes → Verifier.Root)
    (c c' : Verifier.Config) (hb : Bounded2 c) (hb' : Bounded2 c')
    (h : configDigestRecomputed khash2 c = true) (h' : configDigestRecomputed khash2 c' = true)
    (heq : c.circuitConfigDigest = c'.circuitConfigDigest) :
    core2 c = core2 c' ∨ Khash2Collision khash2 := by
  have h1 : c.circuitConfigDigest = khash2 (encodeCircuitConfig c) := by
    simpa [configDigestRecomputed] using h
  have h2 : c'.circuitConfigDigest = khash2 (encodeCircuitConfig c') := by
    simpa [configDigestRecomputed] using h'
  by_cases he : encodeCircuitConfig c = encodeCircuitConfig c'
  · exact Or.inl (encode_circuit_config_injective hb hb' he)
  · exact Or.inr ⟨_, _, he, by rw [← h1, ← h2, heq]⟩

/-! ## 8. (c) what acceptance under the Rust engine gives -/

/-- **3(c) THE RUST-SIDE ANALOGUE OF `explicit_acceptance_summary`.** One accepted
call under `rustEngine` yields each structural fact the model's per-call checks
establish: the envelope, the coset-shift chain, the source's own subgroup
recomputation check together with the adopted `SubgroupPowersProvenance` it is
equivalent to, the decoded and validated gate metadata, the recomputed
configuration digest, and the two identifiers.

**HOW MUCH OF THIS TRANSFERS TO A SOURCE-ACCEPTED RUN.** Every conjunct but the
second transfers unconditionally: each is the model of a check `mle_verify_v2`
actually makes per call. CONJUNCT 2, `c.kIs.map Fin.val = canonicalKIs c.numRouted`,
is the exception, for the reason the header records: Rust compares `vk.k_is` with
`common_data.k_is` and never with the canonical chain, so for a source-accepted run
this conjunct holds only under BUILDER PROVENANCE of `common_data`
(field/src/cosets.rs 20-23 via circuit_builder.rs 1216, 1501). On the Solidity path
it needs no such qualification -- the constructor checks `kIs[i] = g^i` outright
(MleVerifierV2.sol 527-532). -/
theorem rust_engine_acceptance_implies_structural_validity (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (rustEngine gdec hash thash khash khash2 P c₀) gdec pin chain c p
      = .ok ()) :
    Verifier.envelope c = true ∧
    c.kIs.map Fin.val = canonicalKIs c.numRouted ∧
    VkSubgroupProvenance.checkSubgroupGenPowers c.degreeBits c.subgroupPowers = .ok () ∧
    EqTableProvenance.SubgroupPowersProvenance c.subgroupPowers
      (VkSubgroupProvenance.subgroupGenerator c.degreeBits) c.degreeBits ∧
    (∃ gates, gdec c.gatesEncoding = some gates ∧ gates.length = c.gateRows ∧
      Gates.validateConfiguration (Integrated.gateConfig c) gates = some ()) ∧
    c.circuitConfigDigest = khash2 (encodeCircuitConfig c) ∧
    c.whirSessionId = P.sessionId ∧
    c.whirProtocolId = P.tableProtocolId (c.degreeBits + c.indexBits) := by
  obtain ⟨-, -, -, -, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (rustEngine gdec hash thash khash khash2 P c₀) gdec pin chain c p hacc
  have hs := Verifier.verify_success_checks _ pin chain c p hv
  exact rust_deployment_structural gdec khash2 P c hs.2.2.2.1

/-! ## 9. (d) the two boundaries on the deployed configuration -/

theorem canonical_deployment_at_the_deployment (P : Profile) (c₀ : Verifier.Config)
    (h : PinnedWhirProfile.profileOk P c₀ = true) :
    CanonicalProofCheck.canonicalDeployment P c₀ c₀ = true :=
  (CanonicalProofCheck.canonical_deployment_exact P c₀ c₀).mpr ⟨⟨rfl, h⟩, rfl, rfl⟩

/-- The bridge for 3(d). `Integrated.verify` reads `deploymentValid` in exactly one
place, `Verifier.verify`'s configuration guard, and
`Verifier.checked_boundary_agrees_with_call` erases that guard whenever the
predicate holds. The preflights and `Verifier.verifyCall` never read the field at
all (`CanonicalProofCheck.call_boundary_ignores_the_deployment_predicate`). -/
theorem integrated_verify_ignores_the_deployment_predicate (e : Verifier.Engine)
    (d : Verifier.Config → Bool) (gdec : Integrated.DecodeGates) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (henv : Verifier.envelope c = true) (h1 : e.deploymentValid c = true) (h2 : d c = true) :
    Integrated.verify { e with deploymentValid := d } gdec pin chain c p =
      Integrated.verify e gdec pin chain c p := by
  have hv : Verifier.verify
      (Integrated.modelEngine { e with deploymentValid := d } gdec) pin chain c p =
      Verifier.verify (Integrated.modelEngine e gdec) pin chain c p := by
    rw [Verifier.checked_boundary_agrees_with_call
        (Integrated.modelEngine { e with deploymentValid := d } gdec) pin chain c p henv h2,
      Verifier.checked_boundary_agrees_with_call
        (Integrated.modelEngine e gdec) pin chain c p henv h1]
    rfl
  simp only [Integrated.verify,
    show Integrated.normResult (Integrated.modelEngine { e with deploymentValid := d } gdec) c p
      = Integrated.normResult (Integrated.modelEngine e gdec) c p from rfl,
    show Integrated.gateResult (Integrated.modelEngine { e with deploymentValid := d } gdec) gdec c p
      = Integrated.gateResult (Integrated.modelEngine e gdec) gdec c p from rfl, hv]

/-- **3(d) ON THE DEPLOYED CONFIGURATION THE TWO BOUNDARIES ARE THE SAME FUNCTION.**
Not merely the same accept set: the same `Except` value, for every proof. The
boundaries can differ only on a configuration that is not the deployment, and there
they differ only in WHICH configurations are rejected -- both reject with the same
coarse `.configuration` error, for different reasons. Combined with 3(a) and 3(b):
running the Rust checks per call buys nothing on the deployed configuration, and
omitting the deployment pin costs everything off it. -/
theorem both_boundaries_agree_on_the_deployed_config (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (p : Verifier.Proof)
    (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hr : RustDeployedFacts gdec khash2 P c₀) :
    Integrated.verify (rustEngine gdec hash thash khash khash2 P c₀) gdec pin chain c₀ p =
      Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀) gdec
        pin chain c₀ p :=
  integrated_verify_ignores_the_deployment_predicate
    (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
    (rustDeployment gdec khash2 P) gdec pin chain c₀ p hd.envelope
    (canonical_deployment_at_the_deployment P c₀ hd.canonicalProfile)
    (rust_deployment_of_deployed_facts gdec khash2 P c₀ hr)

/-! ## 10. The gate conjunct is redundant -/

/-- The gate conjunct of `rustDeployment` is implied by acceptance under
`rustEngine` itself, by the same preflight argument as section 5. It is kept in the
predicate because the source checks it, not because the model needs it. -/
theorem rust_gates_conjunct_is_redundant (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify (rustEngine gdec hash thash khash khash2 P c₀) gdec pin chain c p
      = .ok ()) :
    ∃ gates, gdec c.gatesEncoding = some gates ∧ gates.length = c.gateRows ∧
      Gates.validateConfiguration (Integrated.gateConfig c) gates = some () := by
  obtain ⟨-, gate, -, hg, -⟩ := Integrated.accepted_preflights_and_original_verifier
    (rustEngine gdec hash thash khash khash2 P c₀) gdec pin chain c p hacc
  obtain ⟨gates, hdec, hrow, -, -, -, hval⟩ :=
    Integrated.successful_gate_evaluation_checks_all_metadata gdec c _ _ _ _ gate hg
  exact ⟨gates, hdec, hrow, hval⟩

/-! ## 11. Non-vacuity -/

/-- The witness decoder is CONSTANT, so `gatesAdmissible exampleDecodeGates` is
insensitive to `gatesEncoding`; the examples below therefore witness the
configuration-level separations and say nothing about gate decoding. -/
def exampleDecodeGates : Integrated.DecodeGates := fun _ => some [Gates.exampleArithmetic]

def exampleBaseConfig (P : Profile) : Verifier.Config :=
  { degreeBits := 1, numConstants := 3, numRouted := 1, numWires := 160,
    numPublicInputs := 0, numSelectors := 1, numGateConstraints := 1,
    quotientDegree := 8, gateRows := 1, indexBits := 8,
    kIs := [⟨1, by decide⟩], subgroupPowers := VkSubgroupProvenance.exampleVk1,
    publicInputWireMap := [], gatesEncoding := [], whirEncoding := [],
    circuitDigest := List.replicate 4 (Verifier.base 0),
    circuitConfigDigest := Verifier.testRoot,
    whirProtocolId := P.tableProtocolId 9, whirSessionId := P.sessionId }

def exampleRustConfig (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) :
    Verifier.Config :=
  { exampleBaseConfig P with
      circuitConfigDigest := khash2 (encodeCircuitConfig (exampleBaseConfig P)) }

theorem example_base_envelope (P : Profile) : Verifier.envelope (exampleBaseConfig P) = true := rfl

theorem example_canonical_kis : canonicalKIs 1 = [1] := rfl

theorem example_rust_deployment_holds (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) :
    rustDeployment exampleDecodeGates khash2 P (exampleRustConfig khash2 P) = true := by
  refine (rust_deployment_exact exampleDecodeGates khash2 P (exampleRustConfig khash2 P)).mpr
    ⟨example_base_envelope P, rfl,
      (subgroup_powers_canonical_is_the_source_check (exampleRustConfig khash2 P)).mpr
        VkSubgroupProvenance.example_vk1_accepted,
      (gates_admissible_exact exampleDecodeGates (exampleRustConfig khash2 P)).mpr
        ⟨[Gates.exampleArithmetic], rfl, rfl, rfl⟩, ?_, ?_⟩
  · simp only [configDigestRecomputed, decide_eq_true_eq]
    rfl
  · simp only [rustIds, decide_eq_true_eq]
    exact ⟨rfl, rfl⟩

/-- **THE DEPLOYMENT HYPOTHESES ARE INHABITED.** All seven fields of
`RustDeployedFacts`, at a one-row arithmetic-gate configuration with `degreeBits =
1`, `numRouted = 1`, canonical shifts `[1]` and the adopted
`VkSubgroupProvenance.exampleVk1` subgroup powers, for an ARBITRARY `khash2` and an
arbitrary profile table. Nothing in this module is vacuous. -/
theorem example_rust_deployed_facts_inhabited (khash2 : Verifier.Bytes → Verifier.Root)
    (P : Profile) :
    RustDeployedFacts exampleDecodeGates khash2 P (exampleRustConfig khash2 P) :=
  ⟨example_base_envelope P, rfl, VkSubgroupProvenance.example_vk1_accepted,
    ⟨[Gates.exampleArithmetic], rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem example_bounded2 (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) :
    Bounded2 (exampleRustConfig khash2 P) := by
  refine bounded2_of_envelope (example_base_envelope P) ?_
  have hlen : (exampleRustConfig khash2 P).gatesEncoding.length = 0 := rfl
  rw [hlen, u64_bound_value]
  norm_num

/-- 3(b) at the witness: the example configuration with foreign WHIR bytes still
passes every Rust check, and the Solidity deployment predicate rejects it. -/
theorem example_rust_deployment_does_not_pin_the_whir_bytes
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) :
    rustDeployment exampleDecodeGates khash2 P
        { exampleRustConfig khash2 P with whirEncoding := [7] } = true ∧
      ExplicitEngine.explicitDeployment P (exampleRustConfig khash2 P)
        { exampleRustConfig khash2 P with whirEncoding := [7] } = false := by
  refine ⟨example_rust_deployment_holds khash2 P, ?_⟩
  have hwe : (exampleRustConfig khash2 P).whirEncoding = [] := rfl
  simp [ExplicitEngine.explicitDeployment, hwe]

theorem example_rust_deployment_does_not_pin_the_circuit_digest
    (khash2 : Verifier.Bytes → Verifier.Root) (P : Profile) :
    rustDeployment exampleDecodeGates khash2 P
        (digestVariant khash2 (exampleRustConfig khash2 P)
          (List.replicate 4 (Verifier.base 1))) = true ∧
      CanonicalProofCheck.canonicalDigestPin (exampleRustConfig khash2 P)
        (digestVariant khash2 (exampleRustConfig khash2 P)
          (List.replicate 4 (Verifier.base 1))) = false := by
  refine ⟨(rust_deployment_does_not_pin_the_circuit_digest exampleDecodeGates khash2 P
    (exampleRustConfig khash2 P) (List.replicate 4 (Verifier.base 1)) (by simp)
    (example_rust_deployment_holds khash2 P)).1, ?_⟩
  have hne : ¬ ((digestVariant khash2 (exampleRustConfig khash2 P)
      (List.replicate 4 (Verifier.base 1))).circuitDigest
      = (exampleRustConfig khash2 P).circuitDigest) := by
    show ¬ (List.replicate 4 (Verifier.base 1) = List.replicate 4 (Verifier.base 0))
    decide
  simp [CanonicalProofCheck.canonicalDigestPin, hne]

end Audit.Wire3.RustCallBoundary
