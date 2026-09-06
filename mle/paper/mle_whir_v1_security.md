# MLE/WHIR packed constituent PCS v1

## 2026-09-03 wire-v3 superseding addendum

This addendum is the current protocol/security statement. The remainder of
this file is retained as the frozen v1/v2 design and audit history; wherever
it calls v2 “current” or “production,” assigns WHIR 130 bits, treats the
Poseidon public-input hash as the load-bearing statement binding, or uses the
old `Q_H = 4` conclusion, this addendum supersedes it. Historical Rust API,
Solidity class, and filename suffixes remain `V2`, while the accepted wire
identity is exclusively schema/protocol version 3 with compact magic
`MLEWHIR3`.

### Current statement and transcript

Wire v3 retains the three committed packed groups and two terminal points of
the final v2 design:

```text
groups = [preprocessed(constants || sigmas), witness(wires), norm_inverse]
points = [r_log, r_gate]
point-major/group-major bound mask = 0x1f
```

All six packed evaluations are authenticated by one grouped WHIR proof; the
first five feed an outer terminal equation. Row bits are low/LSB-first,
constituent bits are high/LSB-first, and the bridge reverses the complete
packed point once.

The new verification-key field `public_input_wire_map` contains exactly one
`row_u16_le || routed_column_u8` record per raw PI, preserving PI order and
duplicates. `canonical_public_input_wires` scans the compressed Plonky2
copy-equivalence classes in row-major/routed-column order and selects the
first routed witness cell for each PI target. For `m` raw inputs, define

```text
D_PI(x) = sum_(i=0..m-1) eta^i * eq(row_i, x)
                               * (W_column_i(x) - PI_i).
```

The degree-five norm/logUp sumcheck includes `xi * D_PI(x)`. Its Boolean-cube
sum is zero only when the randomized aggregate of the mapped committed
witness cells equals the raw statement. This binding is independently
load-bearing: the Plonky2 Poseidon public-input digest remains evaluated as a
circuit gate but is no longer the only PI-to-witness link.

The exact outer dependency order is:

1. absorb the circuit digest, raw PI vector, schema metadata, circuit-config
   digest, WHIR protocol/session IDs, preprocessed root, and witness root;
2. sample uniform full-`Fp3` `eta`, then full-`Fp3` `beta` and `gamma`;
3. construct and commit the challenge-dependent norm-inverse group, then
   absorb its root;
4. sample full-`Fp3` `xi`, `lambda`, `rho`, `kappa`, `tau_log`,
   `gate_alpha`, and `gate_tau`;
5. for every row variable, absorb the five nonconstant norm/logUp
   coefficients and all gate coefficients before sampling distinct full-`Fp3`
   log and gate challenges;
6. absorb all six ordered constituent vectors (including the explicit empty
   gate/norm vector), then sample the two independent full-`Fp3` constituent
   index points and invoke WHIR.

Zero values of `eta` and `xi` are not resampled: they are ordinary bad events
included in the PI soundness term. The current domains are
`plonky2-mle-outer-v3`, `mle-whir-packed-schema-v3`,
`plonky2-mle-whir-split-v3`, and the dedicated `*-v3` domains generated from
`protocol/mle_whir_v2.json`.

### Current soundness accounting

Let `p = 0xffffffff00000001` and `q = p^3`. At the maximum admitted shape,
the conservative outer terms are

```text
epsilon_log        = 2,621,599/q  ~= 2^-170.678
epsilon_PI         =       256/q  ~= 2^-184
epsilon_gate       =         265/q ~= 2^-183.95
epsilon_projection =          48/q ~= 2^-186.4
epsilon_outer      = 2,622,168/q  ~= 2^-170.678.
```

The pinned upstream `Config::security_level()` returns the minimum of its
round-by-round displayed bounds; it is not an aggregate failure probability.
The production machine-check therefore reconstructs every native event and
sums the inverse-work quantities `multiplicity * 2^-event_bits`. For the maximum packed dimension
`n + ell = 21`, its 35 charged events are one vector RLC, one linear-form RLC,
three initial OOD commitments, four initial binary folds, four repetitions of
`(one OOD + one query + four binary folds)`, one final query, and one final
binary fold. Twenty-five of those events attain the configured target. With
`securityLevel = 133`, `powBits = 22`, starting inverse-rate exponent 4, and
folding factor 4, the aggregate native inverse-work measure is

```text
omega_WHIR,work(21) = sum_j multiplicity_j * 2^-event_bits_j
                    ~= 2^-128.356142910.
```

The same reconstruction is checked for every admitted packed dimension 1
through 21. A negative regression fixes the former target 132 result at only
about `2^-127.356143360`, which does not meet 128 bits. The target-133 profile
does not change samples (`[58,33,23,18,14]` at dimension 21), proof-size
bounds, Solidity verifier structure, or gas structure. It raises the maximum
internal PoW difficulty from about 21.2535 to 22.2535 bits and the modeled
aggregate prover work from about 23.9563 to 24.9563 bits (approximately two
times the PoW work), preserving practical proof and transaction limits.

The 128.356-bit aggregate includes WHIR's internal PoW difficulties and is a
generic-work exponent. It is not a conditional failure probability for one
completed proof. A malicious prover can abort after an unfavorable
intermediate challenge and grind at that stage without completing a proof.
Let `A_j`, `B_k`, and `C_l` count raw-oracle work trials allocated respectively
to native WHIR event `j`, outer event `k`, and extraction event `l`; a
candidate protected by `d` PoW bits consumes about `2^d` such trials. Let `H`
count all raw Keccak oracle calls. A literal ROM accounting has the form

```text
Adv_wire3({A_j},{B_k},{C_l},H)
 <= sum_j A_j*2^-b_j
    + sum_k B_k*epsilon_outer,k
    + sum_l C_l*delta_extract,l
    + H*(H-1)/2^257,
```

where `b_j` includes the exact PoW acceptance work for that stage. The coarse
but safe substitution `A_j,B_k,C_l <= H` gives

```text
Adv_wire3(H)
 <= H * (omega_WHIR,work
         + 2,622,168/q
         + 228*p/2^256
         + 102*p/2^320)
    + H*(H-1)/2^257.
```

The outer transcript reduces 256 bits per base limb modulo `p`, whose
statistical distance is below `p/2^256 < 2^-192`. Pinned spongefish WHIR
squeezes 40 bytes per base limb (120 per `Fp3`) before reduction, giving below
`p/2^320 < 2^-256`; power-of-two query-index reduction is exactly uniform.
The production trace machine-check fixes 228 outer and 102 WHIR base limbs at
dimension 21; the latter is also counted from the actual pinned native trace,
where every `Fp3` squeeze is 120 bytes. The coarse bound loses approximately
`log2(H)` from the 128.356-bit work figure. At `H = 2^32` it is only about
96.356 bits, even though the Keccak collision term alone is about 193 bits.
Thus target 133 clears the aggregate generic-work criterion but does not prove
a literal, unqualified `2^-128` advantage. That stronger statement requires a
protocol-specific, externally reviewed Fiat--Shamir/grinding theorem and an
operational raw-oracle budget; completed-proof counts are insufficient.

Generic Keccak-256 collision resistance at 128 bits is a computational work-
factor convention, not a fixed additive `2^-128` failure event. It is kept
separate from the literal `H*(H-1)/2^257` advantage term. Under the former
convention, the local complete MLE/WHIR statement has a 128-bit work-factor
target. The direct PI relation removes the old approximately-95-bit Poseidon
PI-binding cap from this local statement.

The map is trusted setup data. It must be produced from the full `CircuitData`
by `mle_setup_v2`/the canonical exporter and admitted with
`validate_against_circuit`; a common-data or on-chain verifier cannot
rediscover the original PI copy classes. Proof-free parsing nevertheless
checks exact VK/config map equality and bounds, recomputes the circuit-config
digest, WHIR profile, compact shape/size bound, and Solidity ABI bytes and
digests. Hand-authored maps are forbidden.

Parent Plonky2 recursion still uses the default Goldilocks Poseidon
configuration with the repository's approximately-95-bit estimate, so this
local repair does not make the whole application a 128-bit system. Fixture
migration, the full cross-language/resource matrix, external cryptographic
review, and every separate parent audit blocker remain release gates.

## Frozen historical v1/v2 record

## Status and scope

This note begins with the frozen packed-v1 audit record and then specifies the
production-v2 redesign in “v2 two-Ext3 implementation security
specification.” Statements before that subsection describe historical V1, not
the production V2 proof shape. The current disposition is recorded at the end.
Both parts address the PCS constituent-binding failure described in
`doc/audit/mle-whir-pcs-repair-handoff.md`.

The result is deliberately scoped:

- the packed V1 constituent PCS has a conventional 128-bit binding budget;
- the complete V1 MLE proof does **not** have a 128-bit soundness bound because
  its outer algebraic checks use individual Goldilocks challenges;
- V2 replaces those checks with the Ext3 construction specified below, but its
  complete-statement binding is capped by the concrete Poseidon public-input
  hash (about 95-bit work by this repository's cited estimate), and its literal
  random-oracle claim remains conditional on explicit `Q_H` and Poseidon attack
  budgets. The unconditional production disposition therefore remains
  **NO-GO**, and the chain restriction remains containment only.

Nothing in the 130-bit WHIR configuration should be cited as amplifying an
outer Goldilocks gate, permutation, or sumcheck challenge.

## Versioned statement

The version and domain identifiers are:

| Item | Value |
|---|---|
| Outer proof version | `1` |
| Outer transcript protocol domain | `plonky2-mle-v1` |
| Outer packed schema domain | `pcs-schema-packed-v1` |
| WHIR session | `plonky2-mle-whir-packed-constituents-v1` |
| Claim-list domain | `pcs-constituent-claims-v1` |
| Index-challenge domain | `pcs-constituent-index-v1` |

The WHIR protocol ID is derived from the exported WHIR configuration. The
Solidity caller supplies the expected protocol and session IDs from the VK;
Rust uses the constants above. The WHIR instance payload is empty. Old session,
schema, proof-layout, or parameter bytes are not aliases for this statement.

The canonical machine-readable source for the packed-protocol metadata is
`protocol/mle_whir_v1.json`. `tests/protocol_schema_codegen.rs` validates that
artifact and generates `src/generated/mle_whir_v1.rs` and
`contracts/src/generated/MleWhirV1.sol`. Those outputs drive the Rust prover,
verifier, transcript and fixture exporter and the Solidity verifier and trace
tests for protocol labels, group and terminal-point order/counts, Ext3 limb
count, the 16-cell claim matrix, and its nine-cell terminal mask. The artifact
also contains the ordered 48-field `MleProof` ABI manifest: Solidity source
field names, fixture JSON keys, source and canonical ABI types, its tuple
signature, and a semantic layout hash. The drift test parses the handwritten
Solidity struct and Rust fixture fields against that manifest, while
`ProtocolSchemaLayoutTest` compares a generated selector with the compiler's
fully expanded tuple selector, including nested structs. The ordinary test is
an exact read-only drift check; regeneration requires
`MLE_WRITE_PROTOCOL_SCHEMA=1`.

This generated surface is deliberately narrower than the handoff's complete
proof-schema requirement. The artifact now specifies and drift-checks the
public Solidity proof tuple, but it does not generate the Rust proof/fixture
types, the Solidity struct or parsers, parent Rust ABI encoder,
`FixtureLib`/script parsing, or VK types/generation. Those consumers still
contain handwritten layouts and mappings, so this must not be described as a
single generated cross-language proof/VK/layout implementation.

There are exactly four commitment groups, in this order:

1. `preprocessed = constants || sigmas`;
2. `witness = wires`;
3. `inverse = A_0..A_{R-1} || B_0..B_{R-1}`;
4. `auxiliary = C_tilde || h_tilde`.

Let `C` be the number of constant columns, `R` the number of routed wires,
`N_wires` the number of wire columns, and

```text
W = max(C + R, N_wires, 2R, 2)
ell = ceil_log2(W)
L = 2^ell.
```

The exact real counts of the four groups are `C + R`, `N_wires`, `2R`, and
`2`. Their order and counts are determined by the schema above; there are no
optional or trailing constituents. Every group is represented to WHIR by
exactly **one** packed vector, so the production WHIR shape is:

```text
numCommitments = 4
numVectors     = 1
numVariables   = n + ell
numPoints      = 4
```

where `n = degree_bits`. Unused constituent-index slots through `L - 1` are
zero in the honest packed table. Expected terminal folds likewise extend every
real claim array with extension-field zero through length `L`.

## Packed-bivariate table and coordinate order

For group `g`, define one multilinear polynomial

```text
F_g(row, index)
```

over `n + ell` Boolean variables. The dense evaluation table is laid out as

```text
table[row + (index << n)] = f_{g,index}(row),  index < real_count(g)
table[row + (index << n)] = 0,                 index >= real_count(g).
```

Thus row bits are the low table bits and constituent-index bits are the high
table bits. Both axes use least-significant-bit-first numbering. The dense-MLE
coordinate sequence is exactly

```text
[r_0, ..., r_{n-1}, u_0, ..., u_{ell-1}],
```

where each row coordinate is embedded as `Ext3(r_i, 0, 0)` and each `u_i` is a
general Ext3 element.

WHIR's multilinear evaluator consumes its first coordinate as the highest
table bit. The bridge therefore reverses the **complete** packed point, not the
row and index portions independently:

```text
whir_point = [u_{ell-1}, ..., u_0,
              Ext3(r_{n-1},0,0), ..., Ext3(r_0,0,0)].
```

Rust and Solidity implement this same full reversal. Every Ext3 value is
encoded and compared as three canonical Goldilocks limbs `(c0,c1,c2)`; a
`c0`-only comparison is not part of this protocol.

## Claims, index challenges, and packed openings

The four row points, in point-major order, are:

1. `r_combined`, the combined-sumcheck terminal point;
2. `r_inv`, the inverse zero-check terminal point;
3. `r_h`, the unweighted `H`-sumcheck terminal point;
4. `r_gate_v2`, the gate zero-check terminal point.

After those row points and all constituent claim arrays have been fixed, the
outer transcript absorbs exactly 16 field vectors in point-major then
group-major order:

| Point | preprocessed | witness | inverse | auxiliary |
|---|---|---|---|---|
| `r_combined` | full claims | full claims | empty | `[C_tilde(r), h_tilde(r)]` |
| `r_inv` | full claims | full claims | full `A || B` claims | empty |
| `r_h` | empty | empty | full `A || B` claims | empty |
| `r_gate_v2` | full claims | full claims | empty | empty |

An empty entry is still absorbed as an explicit zero-length field vector. It
is not an omitted transcript item.

Only after all 16 vectors have been absorbed does the transcript sample four
independent index points

```text
u^(0), u^(1), u^(2), u^(3) in Ext3^ell,
```

one for each row point above. Sampling is point-major, then bit-major. Each
coordinate consumes three consecutive outer transcript squeezes in the exact
limb order `c0`, `c1`, `c2`.

For a real claim vector `y = (y_0,...,y_{m-1})`, extend it with zeros to length
`L` and compute its constituent-index MLE value

```text
Y(u) = sum_{j=0}^{L-1} y_j * chi_j(u),

chi_j(u) = product over b=0..ell-1 of
           (u_b if bit_b(j)=1 else (1-u_b)).
```

The implementation obtains the same value by repeatedly folding adjacent
even/odd entries with `even + u_b * (odd - even)`, starting at bit zero.

WHIR opens every one of the four packed commitments at every one of the four
full points `(r_point, u^(point))`, producing a 4-by-4 matrix of Ext3 scalar
evaluations. The outer verifier equality-fixes the nine cells used by terminal
equations to the corresponding `Y(u)` values. The other seven cells remain
authenticated evaluations of the same four commitments, but are not inputs to
an outer terminal equation.

Before WHIR samples any of its native batching challenges, all 16 packed
evaluation scalars are written into the WHIR transcript. Consequently neither
the constituent claims nor their packed evaluations can be selected after a
WHIR batching challenge.

## Commitment and challenge order

The required dependency order is:

1. Construct and commit `preprocessed`, then `witness`.
2. Absorb the preprocessed root into its dedicated mini-transcript before
   `rho_preprocessed`; absorb both base roots into the outer transcript before
   `rho_witness`, `beta`, and `gamma`.
3. Construct `A_j/B_j` from `beta/gamma`, commit the packed inverse group, and
   absorb its root.
4. Derive `rho_inverse`, `alpha`, and `extension_challenge`.
5. Construct `C_tilde/h_tilde`, commit the packed auxiliary group, and absorb
   its root.
6. Only then derive `rho_auxiliary`, all zero-check points, all sumcheck
   messages/challenges, and the four terminal row points.
7. Absorb the 16 claim vectors, sample the four Ext3 index points, and prove the
   four-point packed WHIR opening statement.

The root order is always

```text
preprocessed, witness, inverse_helpers, auxiliary.
```

For each group, the WHIR transcript contains the actual Merkle root consumed
by the commitment verifier, its OOD response cycle, and then an explicit
duplicate root statement. Rust and Solidity require both root slots to equal
the corresponding outer root. The preprocessed outer root is additionally
equal to the VK root. This prevents a proof from using one root for WHIR while
placing a different root in the outer Fiat-Shamir transcript.

## Byte-exact outer transcript

A domain label is encoded as
`u64_le(byte_length) || UTF-8 bytes`. A base-field vector is encoded as
`u64_le(count) || count * u64_le(canonical_field)`. Raw bytes are encoded as
`u64_le(byte_length) || bytes`. Each schema integer is passed through the raw
byte encoding with an eight-byte little-endian payload.

An outer squeeze hashes `state || u64_le(squeeze_counter)` with Keccak-256 and
reduces the complete little-endian 256-bit value modulo the Goldilocks prime by
radix-`2^64` Horner reduction. Consecutive squeezes increment the counter;
every absorb resets it.

The normative outer order is:

| Order | Domain/message | Exact payload or output |
|---:|---|---|
| 1 | `plonky2-mle-v1` | protocol domain |
| 2 | `circuit` | absorb `circuit_digest`, then `public_inputs` |
| 3 | `pcs-schema-packed-v1` | ten raw u64 values: `version, 4, C, R, N_wires, W, ell, 1, 3, 0` |
| 4 | `pcs-group-preprocessed` | absorb 32-byte preprocessed root |
| 5 | `pcs-group-witness` | absorb 32-byte witness root |
| 6 | `batch-commit-witness` | squeeze `rho_witness` |
| 7 | `challenges` | squeeze `beta`, then `gamma` |
| 8 | `pcs-group-inverse-helpers` | absorb 32-byte inverse root |
| 9 | `inverse-helpers-batch-r` | squeeze `rho_inverse`, then `alpha` |
| 10 | `extension-combine` | squeeze `extension_challenge` |
| 11 | `pcs-group-auxiliary` | absorb 32-byte auxiliary root |
| 12 | `aux-batch-r` | squeeze `rho_auxiliary` |
| 13 | `post-auxiliary-challenges-v1` | squeeze `tau[n]`, then `tau_perm[n]` |
| 14 | `v2-logup-challenges` | squeeze `lambda_inv`, `mu_inv`, then `tau_inv[n]` |
| 15 | `combined-sumcheck` | squeeze `mu` |
| 16 | each combined round | `sumcheck-round`; absorb exactly 3 fields, squeeze one coordinate of `r_combined` |
| 17 | `v2-inv-zerocheck` and its rounds | each round absorbs exactly 4 fields and squeezes one coordinate of `r_inv` |
| 18 | `v2-h-linear` and its rounds | each round absorbs exactly 2 fields and squeezes one coordinate of `r_h` |
| 19 | `v2-gate-challenges` | squeeze `tau_gate[n]` |
| 20 | `v2-gate-zerocheck` and its rounds | each round absorbs exactly `quotient_degree_factor + 3` fields and squeezes one coordinate of `r_gate_v2` |
| 21 | `pcs-eval` | domain handoff to the packed opening layer |
| 22 | `pcs-constituent-claims-v1` | absorb the 16 field vectors in the table above |
| 23 | `pcs-constituent-index-v1` | squeeze `4 * ell * 3` base fields as four Ext3 index points |

`H(b)` is the unweighted polynomial

```text
H(b) = sum_j (A_j(b) - B_j(b)).
```

There is no `lambda_h` challenge, proof field, or transcript entry. In
particular, the `v2-logup-challenges` sequence proceeds directly from
`lambda_inv` and `mu_inv` to `tau_inv`. The still-present `tau_perm` squeeze is
part of the current byte transcript even though the implemented combined
terminal uses the unweighted `h_tilde` term; it cannot be silently omitted
without another version change.

The shared golden file `contracts/test/fixtures/transcript_v1_trace.json`
contains all 192 checkpoints in this sequence, including every claim-vector
absorb and every Ext3 limb squeeze. Each entry pins the operation label, exact
newly absorbed bytes, cumulative state length, squeeze counter, and Keccak
state digest. The outer table separately pins all 122 squeezed Goldilocks
values and their checkpoint indices. A second five-checkpoint table in the
same artifact pins the dedicated `preprocessedBatchR` mini-transcript: protocol
initialization, its domain, circuit digest, packed preprocessed root, and the
single squeeze. Rust replays both tables in
`tests/transcript_e2e_trace.rs`; Solidity replays the same JSON in
`contracts/test/TranscriptE2ETrace.t.sol`. A final digest alone is not treated
as sufficient transcript parity evidence.

The artifact also contains a 307-checkpoint native-WHIR table generated by the
production Rust `GroupedWhirPreflight` schedule for `small_mul.json`. It records
all native Keccak absorbs and squeezes, root copies, sixteen bound claims,
query entropy and deduplicated indices, hint-range digests, both stream cursors,
state/counter, and exact EOF. `contracts/test/WhirNativeTrace.t.sol` binds those
events to the fixture NARG/hints and replays them through Solidity's production
`Keccak256Chain`; the ordinary Solidity E2E test independently accepts the same
proof through `SpongefishWhirVerify`.

No trace branch was added to the near-EIP-170 deployed verifier. Consequently
this is production-Rust-schedule/production-Solidity-primitive differential
coverage, not literal instrumentation of every upstream prover or production
Solidity WHIR call site.

## Canonical decoding and grouped-verifier totality

The pinned Rust NARG decoder reduces field bytes modulo the Goldilocks prime.
Without an explicit boundary check, the eight-byte encoding of `p` would
therefore alias the canonical encoding of zero and disagree with Solidity.
Before invoking that decoder, the production grouped verifier transcript-replays
the proof and checks every prover-supplied Ext3 message limb is strictly less
than `p`. This covers initial and round OOD evaluations, transcript-bound
evaluations, cross-group OOD values, all sumcheck coefficients, and the final
folded polynomial. Truncated and trailing NARG bytes are rejected.

Arkworks' canonical hint-field decoder rejects non-canonical limbs, but its
serialized `Vec` length prefix would otherwise be consumed before the verifier
checks the WHIR shape. The grouped preflight instead derives the exact initial
and per-round row counts from the trusted WHIR configuration and
transcript-derived query indices, compares every eight-byte length prefix
before upstream allocation, and then checks every initial base-field or round
Ext3 limb. Merkle authentication paths are raw hashes rather than field
elements; the preflight consumes their exact derived sibling count without
interpreting them as fields. Oversized prefixes, truncation, and tails are all
rejected before the upstream verifier runs, which still performs the actual
Merkle and polynomial checks.

The same replay also rejects a zero final-fold divisor before the pinned
upstream division. The dedicated `panic = "abort"` executable covers that path
and oversized, non-canonical, truncated, and tailed hint streams, including
complete traversal of a proof with a nonempty folding-round configuration.
These checks
make the production grouped MLE path total for the preflighted grammar and
identified divisor path; they are parser and availability protections, not
additional cryptographic soundness bits. Legacy split, auxiliary, and
single-vector wrapper entry points retain only unwind-mode panic containment
and do not carry this grouped-path guarantee.

## Packed PCS binding reduction

Fix a group and a terminal row point after its commitment root has been fixed.
Let `v_j` be the committed constituent value at that row and `y_j` the claimed
value, including zero expected padding. If the vectors differ, then

```text
D(u) = sum_j (y_j - v_j) * chi_j(u)
```

is a nonzero multilinear polynomial because its values on the Boolean index
cube recover the nonzero difference vector. Its total degree is at most `ell`.
The claim vector is absorbed before `u` is sampled, so Schwartz-Zippel over
`Field64_3` gives

```text
Pr[D(u) = 0] <= ell / p^3.
```

At the maximum current width `W = 160`, `ell = 8`. Conservatively union-bound
all four groups at all four points:

```text
Pr[any packed projection collision] <= 4 * 4 * 8 / p^3
                                    = 128 / p^3
                                    < 2^-184.99.
```

This bound also covers a nonzero padding contribution whenever it changes a
terminal-point packed evaluation. Only nine group/point cells are actually
equality-fixed, so the 16-cell calculation is intentionally conservative.

The production configuration requests 130-bit WHIR security with zero explicit
initial PoW bits. WHIR still derives the per-round sumcheck PoW needed by its
security calculation (up to about 19.25 bits at the largest current packed
dimension). It accounts for four commitments, one vector per commitment, and
four linear forms. The regression
`test_constituent_security_budget_exceeds_128_bits` uses the actual packed
variable count `n + ell` and reports:

| Row degree bits `n` | Packed variables | WHIR estimate | Projection estimate |
|---:|---:|---:|---:|
| 2 | 10 | 130.325 bits | 185.000 bits |
| 3 | 11 | 130.325 bits | 185.000 bits |
| 4 | 12 | 130.325 bits | 185.000 bits |
| 11 | 19 | 130.000 bits | 185.000 bits |
| 12 | 20 | 130.000 bits | 185.000 bits |
| 13 | 21 | 130.000 bits | 185.000 bits |

WHIR transcript bytes and hints are both consumed exactly. Merkle commitments
use Keccak-256, whose conventional generic collision-resistance level is 128
bits. Subject to the WHIR analysis and random-oracle model, the local packed
constituent-opening statement is therefore limited by the conventional
128-bit Merkle-binding level, not by the Ext3 projection.

Here, “conventional 128-bit” means the generic collision **work factor**. It is
not a literal additive advantage bound of at most `2^-128`: adding a Merkle
term stated only as `2^-128` to any positive WHIR or algebraic error is already
larger than `2^-128`. If the handoff's “at least 128 bits” requirement is read
as that strict additive bound, a reviewed release needs explicit hash margin
(for example a wider binding construction) and a quantified random-oracle
query budget; rounding the sum back up to 128 is not valid.

## Measured proof, calldata, and gas envelope

The canonical fixture set was regenerated with the configuration above and
verified by both the Rust verifier and the Solidity `MleE2ETest` harness. The
WHIR column below is the exact combined byte length of `whirTranscript` and
`whirHints`; ABI bytes are `abi.encode(MleProof).length`, which is the proof
stream currently committed through the parent proof-DA path.

| Fixture | `n` | WHIR bytes | ABI bytes | Solidity verify gas | Two-blob DA (`253,921`) |
|---|---:|---:|---:|---:|---|
| `small_mul` | 2 | 79,616 | 116,608 | 18,132,443 | pass |
| `poseidon_hash` | 2 | 79,008 | 115,712 | 18,225,967 | pass |
| `medium_mul` | 3 | 87,920 | 126,240 | 19,123,180 | pass |
| `large_mul` | 4 | 116,632 | 155,968 | 21,434,970 | pass |
| `recursive_verify` | 11 | 208,592 | 257,184 | 30,525,774 | **fail by 3,263 bytes** |
| `coset_recursive_verify` | 12 | 232,696 | 282,592 | 32,604,009 | **fail by 28,671 bytes** |
| `huge_mul` | 13 | 240,832 | 289,344 | 33,302,958 | **fail by 35,423 bytes** |

Consequently, local proof verification passing does not close the deployment
gate: three statement families exceed the parent protocol's exact two-blob
capacity, and the same three require more than the repository's documented
30-million-gas verification envelope. They require a reviewed
proof-encoding/PCS-parameter change or a versioned proof-DA/gas migration;
silently allowing a third blob or assuming a larger block budget is not part
of this protocol version.

A guarded current-root-order parent integration regeneration produced the
degree-13 validity fixture and passed `MleE2ETest` 6/6 and
`MleFinalizeE2ETest` 7/7, including `postBlock -> finalize`. One measured proof
was 292,672 ABI bytes, exceeding the 253,921-byte two-blob payload ceiling by
38,751 bytes; its direct `MleVerifier.verify` call used 33,196,433 gas and its
full `finalize` path used 35,105,368 gas. An immediately preceding honest
regeneration used 33,298,168 and 35,217,967 gas respectively, reflecting the
query-deduplication variability described below. The pre-existing tracked
parent fixtures were restored byte-for-byte to their pre-run working-tree
state afterward; that state already contained unrelated pending fixture edits
and is not asserted to match `HEAD`. This is current one-family integration
evidence, but it is not the required atomic all-family migration and it
confirms both resource gates still fail.

The fresh full tracked-parent `forge test --offline --summary` gate reports 470
passing and 38 failing tests. Thirty-six failures are caused by the sixteen
parent MLE fixtures that still use legacy or transitional schemas. The other
two are test setup OOG while copying roughly 2.45 MB of JSON into storage. The
parent `cargo check --all-targets --locked --offline` gate passes. An earlier
`E0061` call-arity error came from an untracked, partially edited
`public_validity_publisher.rs`; it is absent from the current file, which
matches `HEAD`, and was unrelated to this PCS repair.

Plonky2 intentionally randomizes unused public-input wires. Roots, Fiat-Shamir
queries, and the number of duplicate WHIR query rows therefore vary between
honest regenerations; the table records the checked-in golden fixture snapshot,
not a universal maximum. A second full regeneration produced ABI sizes
255,360, 281,792, and 292,768 bytes for the same three failing families, so the
DA failure is not a single-sample boundary accident.

With Solidity 0.8.29, `via_ir`, optimizer enabled, and 200 optimizer runs, the
largest production runtimes in the submodule build are:

| Contract/library | Runtime bytes | EIP-170 margin |
|---|---:|---:|
| `MleVerifier` | 24,104 | 472 |
| `SpongefishWhirVerify` | 24,201 | 375 |
| `Plonky2GateEvaluator` | 22,484 | 2,092 |
| `PoseidonPublicInputsHash` | 5,007 | 19,569 |
| `PackedClaimLib` | 1,582 | 22,994 |

The margins on the first two components are small and must be remeasured after
any protocol or compiler change.

## Why the complete construction remains NO-GO

The local reduction above starts after the outer proof has selected its
terminal claims and proves that those claims are openings of the committed
packed groups. It does not increase the entropy of the outer algebraic tests.

The outer transcript reduces each Keccak squeeze to one element of the
Goldilocks base field. Thus each individual `alpha`, `extension_challenge`,
`beta/gamma`, `lambda_inv/mu_inv`, `tau`, `tau_inv`, `tau_gate`, `mu`, and
sumcheck-round coordinate ranges over roughly 64 bits before polynomial degree,
multiple tests, union bounds, or Fiat-Shamir grinding are charged.

For scale, at the current maximum `N = 8192` rows and `R = 80` routed wires, a
coarse logUp rational-identity degree/bad-event term is

```text
2 * N * R / p approximately 2^-43.7.
```

Other false statements can be localized to one gate aggregation, extension
flattening, inverse aggregation, or sumcheck challenge family, so unrelated
base-field challenges cannot simply be multiplied into a 128-bit claim.

Meeting the handoff literally requires a separate reviewed outer-protocol
change, such as extension-field outer challenges and extension-valued
sumchecks, or enough independently enforced repetitions of every relevant
base-field challenge family. Repeating only the packed index challenge,
increasing WHIR's target, or adding WHIR queries does not amplify the outer
arguments. Such a change affects helper commitments, terminal openings, proof
schema, Solidity ABI, fixtures, proof-size/gas measurements, and deployment
migration.

### Quantitative redesign floor

At `N = 8192, R = 80`, the exact coarse coefficient is
`2*N*R = 1,310,720`, giving 43.67807 bits for one base-field check. Three
independent complete repetitions give about 131.03 bits if that term already
covers all pole events. If bad denominators are charged as a separate term,
three repetitions leave only about 128.03 outer bits; adding the configured
WHIR error drops the combined estimate below 128 bits and leaves no margin for
Fiat--Shamir grinding or omitted constants. More importantly, multiplying the
one-shot interactive errors of parallel base-field repetitions is not a valid
Fiat--Shamir work-factor argument. Even if all messages in each row round are
absorbed before that round's challenges, a malicious prover can bridge one
false repetition to an honest suffix in round 0, retain it, then use later
round messages as nonces to bridge the remaining repetitions sequentially.
The three-gate construction considered below therefore costs only on the
order of `3*p/266` generic queries, not `(p/266)^3`, and is rejected.

A single-pass challenge field needs extension degree three: `Fp2` supplies
only about 107.68 bits against this degree term, while `Fp3` supplies about
171.68 bits. This is not a parameter flip. Ext3 `beta/gamma` make the current
`A/B` helper tables extension-valued unless the relation itself is replaced,
all extension-valued outer sumcheck messages and terminal claims gain three
base-field limbs, and recursive degree-two gate evaluation would need a
reviewed higher-extension construction. The Rust proof schema, Solidity ABI,
WHIR statement, fixtures, and deployments would all change.

Even the optimistic compact three-repetition design is estimated at roughly
182--411 kB and 29--59 million gas across the current fixture range; the more
conservative four-permutation/three-gate design is roughly 220--493 kB and
33--67 million gas. These are architecture estimates, not acceptance
measurements, but they show why raising the WHIR target or query count cannot
simultaneously satisfy the existing two-blob and 30-million-gas gates.

`tests/outer_soundness_budget.rs` now pins the selected v2 budget below:
double-charged Ext3 pole events, one exact Ext3 gate sumcheck, the complete
three-group/two-point projection matrix, the 130-bit WHIR target, an explicit
random-oracle query variable `Q_H`, and a regression rejecting the sequential
bridge attack on the superseded three-base-gate design. It also keeps the
Poseidon public-input binding advantage as an explicit input and separates the
128-bit local PCS/transcript work target from the approximately 95-bit complete-
statement estimate. Passing this arithmetic test alone does not establish an
implemented proof system or release approval.

### v2 two-Ext3 implementation security specification (external review pending)

The selected and implemented v2 construction uses exactly two
cubic-extension sumchecks: one joint norm/logUp check and one exact
gate-formula check. Rust proof objects, prover/verifier, compact codec,
constant-state transcript, and exact gate evaluator are implemented. The
byte-matched Solidity transcript, all-14-family Ext3 evaluator, complete atomic
verifier, cross-language fixtures, and compact/gas/runtime-size resource gates
are also implemented and pass the local evidence recorded below. Parent
integration is outside this submodule review, and its use of the approximately
95-bit default Goldilocks Poseidon configuration still requires a separate
whole-system security decision. The concrete
Poseidon public-input binding is estimated at only about 95-bit work by the root
Plonky2 README. Its reviewed advantage bound, the literal `Q_H` bound, and
external cryptographic review all remain open, so the unconditional release
disposition remains **NO-GO**.

V2 is a versioned replacement for both of these v1 mechanisms:

- the `A_0..A_{R-1} || B_0..B_{R-1}` inverse-helper group and its inverse and
  `H` sumchecks; and
- the committed `C_tilde || h_tilde` auxiliary group and combined sumcheck.

It is not an extra check that can be appended to v1. The redundant batch
scalar/evaluation proof fields, `tauPerm`, `C_tilde`, `h_tilde`, and the three
replaced sumchecks should be removed from the v2 statement rather than kept as
parallel acceptance paths. New proof, transcript, packed-schema, WHIR-session,
VK, ABI, fixture, and deployment version identifiers are mandatory.

#### Three commitment groups and two terminal points

Let `K = Fp[theta] / (theta^3 - 2)` and `q = |K| = p^3`. The proposed packed
groups, in canonical order, are:

1. `preprocessed = constants || sigmas`;
2. `witness = wires`;
3. `norm_inverse = T_id,0..T_id,R-1 || T_sigma,0..T_sigma,R-1`.

The canonical width is

```text
W_v2 = max(C + R, N_wires, 2R).
```

At the current maxima this remains `W_v2 = 160`, so `ell = 8` and the packed
WHIR variable count remains `n + 8`. There is no fourth auxiliary commitment.

There are two row points in `K^n`: `r_log` for the joint norm/logUp sumcheck
and `r_gate` for the exact Ext3 gate sumcheck. WHIR opens the Cartesian
three-group by two-point matrix, or six cells. The terminal equations
equality-fix exactly five cells:

| Row point | Preprocessed | Witness | Norm inverse |
|---|---:|---:|---:|
| `r_log` | used | used | used |
| `r_gate` | used | used | unused |

Thus the v2 shape is **3 groups, 2 points, and 5 terminal-used cells**, with
the point-major mask `0x1f`. The remaining gate/norm cell is an authenticated
opening but is not an input to an outer equation. As in v1, all claim arrays
must be absorbed before fresh, per-point Ext3 constituent-index points are
sampled. A WHIR query index or native WHIR batching challenge is not an outer
field challenge and must not be reused as `beta`, `gamma`, a gate challenge,
or a sumcheck coordinate.

#### Base-valued norm helpers for Ext3 denominators

Sample `beta = beta_0 + beta_1*theta + beta_2*theta^2` and
`gamma = gamma_0 + gamma_1*theta + gamma_2*theta^2` from `K` only after the
preprocessed and witness roots are fixed. For Boolean row `b`, set

```text
I_j(b) = k_j * g_sub(b)

D_id,j(b)    = beta + W_j(b) + gamma * I_j(b)
D_sigma,j(b) = beta + W_j(b) + gamma * sigma_j(b).
```

For `d = a + b*theta + c*theta^2`, define the adjugate coordinates and norm

```text
s_0(d) = a^2 - 2*b*c
s_1(d) = 2*c^2 - a*b
s_2(d) = b^2 - a*c

N(d) = a*s_0(d) + 2*(c*s_1(d) + b*s_2(d))
     = a^3 + 2*b^3 + 4*c^3 - 6*a*b*c.
```

These are the formulas already used by `GoldilocksExt3.inv`. On a Boolean row,
all three coordinates are in `Fp`, `N(d)` is in `Fp`, and

```text
d^-1 = N(d)^-1 * (s_0(d) + s_1(d)*theta + s_2(d)*theta^2).
```

The prover therefore commits only the two base-field tables per routed wire

```text
T_id,j(b)    = N(D_id,j(b))^-1
T_sigma,j(b) = N(D_sigma,j(b))^-1.
```

This is `2R = 160` base columns at `R = 80`, rather than the `6R = 480`
base-coordinate columns needed to commit the two Ext3 `A/B` helper families
directly.
Also, `N(d) = 0` if and only if `d = 0`; when a denominator is zero no value
of `T` can satisfy `T*N(d) - 1 = 0`.

The off-cube definition is security-critical. Write the three formal
coordinate polynomials separately. For example,

```text
a_id,j(X) = beta_0 + W_j(X) + gamma_0 * I_j(X)
b_id,j(X) = beta_1          + gamma_1 * I_j(X)
c_id,j(X) = beta_2          + gamma_2 * I_j(X),
```

and replace `I_j` by `sigma_j` for the sigma denominator. At a point in
`K^n`, each of `a`, `b`, and `c` is itself a `K` value; the verifier evaluates
the displayed low-degree formulas formally over `K`.

It is incorrect to form one off-cube value `D(r)` and call a field-norm,
Frobenius, exponentiation by `1 + p + p^2`, or `GoldilocksExt3.inv(D(r))`.
Those operations do not compute the multilinear extensions of the Boolean-row
coordinate formulas; the exponent form also has degree `p^2 + p + 1`, which
invalidates the degree-five sumcheck bound. An implementation should use an
unambiguous name such as `formalNormFromCoords`.

#### Exact joint norm/logUp target

For `x in K^n`, define

```text
Z_id,j(x)    = T_id,j(x)    * N(D_id,j(x))    - 1
Z_sigma,j(x) = T_sigma,j(x) * N(D_sigma,j(x)) - 1

Z_lambda,rho(x)
  = sum_{j=0}^{R-1} lambda^j
      * (Z_id,j(x) + rho * Z_sigma,j(x))

A_id,j(x)
  = T_id,j(x)
      * (s_0(D_id,j(x))
         + s_1(D_id,j(x))*theta
         + s_2(D_id,j(x))*theta^2)

A_sigma,j(x)
  = T_sigma,j(x)
      * (s_0(D_sigma,j(x))
         + s_1(D_sigma,j(x))*theta
         + s_2(D_sigma,j(x))*theta^2)

H(x) = sum_{j=0}^{R-1} (A_id,j(x) - A_sigma,j(x)).
```

After the norm-inverse root is fixed, sample fresh and domain-separated
`lambda, rho, kappa, tau_log` in that exact order in `K`, where
`tau_log in K^n`. The single
sumcheck has claimed sum zero and exact target polynomial

```text
Phi_log(x)
  = eq(tau_log, x) * Z_lambda,rho(x) + kappa * H(x).

sum_{x in {0,1}^n} Phi_log(x) = 0.
```

The fresh `kappa` prevents a false aggregated inverse relation from cancelling
a false global `H` sum. The per-variable degrees are:

| Expression | Degree in each row variable |
|---|---:|
| `W`, `I`, `sigma`, or `T` | 1 |
| `s_k(D)` | 2 |
| `N(D)` | 3 |
| `T*N(D) - 1` | 4 |
| `eq(tau_log,x) * Z_lambda,rho(x)` | 5 |
| `T*s_k(D)` and `H` | 3 |
| `Phi_log` | **5** |

Consequently the prover evaluates the univariate round polynomial at six
points and converts it to degree-five monomial form. The proof carries only
the five non-constant `K` coefficients; the verifier reconstructs the constant
coefficient from the incoming-claim relation before evaluating at the round
challenge. In the master schedule below, that coefficient vector is absorbed
before any round challenge. At `r_log`, the verifier reconstructs every formal
`D`, `s_k`, `N`, `Z`, and `H` from the three packed groups and checks

```text
log_final
  == eq(tau_log, r_log) * Z_lambda,rho(r_log)
       + kappa * H(r_log).
```

In Solidity this terminal calculation must retain all three limbs. The
preprocessed, witness, and `T` tables contain base-field values, but their MLE
evaluations at `r_log in K^n` are general `K` values. Comparing only `c0` or
forming an actual off-cube Ext3 inverse is unsound.

Under correct helper relations, the Boolean-cube `H` sum is the usual
log-derivative permutation fingerprint. Writing `M = N*R` and `q = p^3`, the
v2 release budget SHALL use the following conservative bound:

```text
epsilon_log
  <= (2*M                 rational fingerprint, rounded up
      + 2*M               all denominator/pole events, charged separately
      + R                 lambda/rho helper aggregation
      + n                 tau_log zero test
      + 1                 kappa joint combination
      + 5*n) / q          degree-five sumcheck
   = (4*N*R + R + 6*n + 1) / p^3.
```

This deliberately charges the pole event even if a tighter proof conditions
on all denominators being nonzero. A release may replace it only with an
independently reviewed reduction that proves the tighter conditioning; it may
not alternate conventions between components. At `N = 8192`, `R = 80`, and
`n = 13`, the fixed numerator is `2,621,599`, or about 170.677984 bits.

#### Exact Ext3 gate sumcheck and rejected base repetitions

Every supported Plonky2 gate is evaluated directly over `K`. A Plonky2
quadratic-extension value is represented as a pair of `K` coordinates in
`K[t]/(t^2-7)`; it is not flattened to `Fp` and is not treated as `Fp6`.
Protocol v2 fails closed unless `D = 2`, the ordered gate metadata matches the
canonical `CommonCircuitData` classification, and the metadata/configuration
digest recomputes exactly.

With fresh `alpha in K` and `tau_gate in K^n`, define

```text
C_gate(x)   = sum_{m=0}^{G-1} alpha^m * c_m(x)
Phi_gate(x) = eq(tau_gate, x) * C_gate(x)

sum_{x in {0,1}^n} Phi_gate(x) = 0.
```

The exact round-degree bound is
`d_gate = quotient_degree_factor + 2 <= 10`: Plonky2's selector-grouping
construction bounds each filtered constraint by
`quotient_degree_factor + 1`, and the equality polynomial contributes one
further linear factor. The production
prover samples the polynomial at `0..d_gate`, interpolates monomial
coefficients, and sends exactly the `d_gate` non-constant `K` coefficients.
The verifier reconstructs the constant coefficient from the incoming sumcheck
claim. All 14 supported gate families use the same exact evaluator at round
nodes and at the PCS-bound terminal point.

The conservative gate bound is

```text
epsilon_gate
  <= ((G - 1)             alpha aggregation
      + n                 tau_gate Boolean-cube zero test
      + n*d_gate) / p^3   degree-d sumcheck
   = 265 / p^3
   approximately 2^-183.95.
```

The superseded design ran three base-field gate sumchecks and claimed a cubed
`(266/p)^3` error from per-round lockstep absorption. That claim is invalid in
Fiat--Shamir. A malicious prover can bridge the first false repetition to an
honest suffix in round 0, keep it fixed, use later round messages as nonces to
bridge the second in round 1, and similarly bridge the third in round 2.
Previously repaired repetitions can answer honestly while unrepaired messages
supply grinding freedom. Expected generic work is therefore on the order of
`3*p/266`, about 57.5 bits, rather than `(p/266)^3`. Same-round
commit-before-challenge, independent counter outputs, and domain labels do not
prevent this sequential attack. Base-field gate repetitions are forbidden in
the production v2 proof type and transcript API.

The two Ext3 sumchecks share one master schedule. After all relation
challenges are derived, round `i` absorbs the log coefficient vector followed
by the gate coefficient vector, then squeezes one independent `K` challenge
for each in canonical order. This consumes six base-field counter outputs.
Lockstep ordering provides unambiguous cross-language binding, while the
security of each transition comes from its own full `K` challenge; lockstep is
not counted as an amplification mechanism.

#### Complete security composition and random-oracle budget

For the implementation maxima, the normative design terms are:

```text
q                  = p^3
epsilon_log        = 2,621,599 / q                  ~= 2^-170.677984
epsilon_gate       = 265 / q                        ~= 2^-183.95
epsilon_outer      = epsilon_log + epsilon_gate     ~= 2^-170.678
epsilon_projection = (3 * 2 * 8) / q                ~= 2^-186.4
epsilon_WHIR       <= 2^-130

epsilon_stat
  = epsilon_outer + epsilon_projection + epsilon_WHIR.
```

The projection term conservatively includes all six cells of the
three-group/two-point matrix, including the one authenticated gate/norm cell
not consumed by a terminal equation. The production WHIR estimator, evaluated
at 21 packed variables, three groups, and two points, returns the 130-bit
target within floating-point tolerance. Generated fixtures SHALL repeat that
check for their exact implemented parameters.

These terms do not yet account for binding the raw public-input vector to the
committed witness trace. Both verifiers compute
`PoseidonHash::hash_no_pad(public_inputs)` and the `PublicInputGate` constrains
only the resulting four Goldilocks digest wires. Raw public inputs are also
absorbed into the Keccak outer transcript, but that only forces a fresh proof;
it does not strengthen trace-to-input binding beyond Poseidon. A collision for
equal-length `x != x'` therefore lets an adversary commit a satisfying trace for
`x'` while producing a fresh outer proof whose application-visible public input
is `x`. If `x` is fixed independently this is a second-preimage game; if the
adversary can arrange both statements it is a chosen-collision game.

The concrete hash is Goldilocks Poseidon-12, rate 8, capacity 4, 8 full rounds,
22 partial rounds, with the `x^7` S-box and four field outputs. The root Plonky2
README, citing BBLP22, says this configuration may have around 95 bits of
security. That is a computational work estimate, not a fixed `2^-95` failure
probability.

There are two distinct security conventions and they MUST NOT be mixed:

1. Under the conventional computational-work-factor convention, the generic
   work estimates
   compose by their minimum:

   ```text
   local PCS/transcript:
     min(170.678 logUp, 183.95 gates, 186.4 projection,
         130 WHIR, 128 Keccak-collision work) = 128 bits

   complete statement:
     min(128 local PCS/transcript,
         approximately 95 Poseidon public-input binding) <= approximately 95 bits.
   ```

   The first line says that a generic Keccak collision attack is the cheapest
   listed local PCS/transcript attack. The second includes the load-bearing
   public-input hash. Neither line assigns a fixed failure probability from a
   work estimate.
2. For a literal random-oracle advantage bound, let `Q_H >= 1` be the total
   number of adversarial random-oracle queries and conservatively allow each
   query one candidate Fiat--Shamir/grinding attempt. A coarse release bound is

   ```text
   Adv_v2(Q_H, Q_P; L_PI)
     <= Q_H * epsilon_stat
        + Q_H * (Q_H - 1) / 2^257
        + Adv_bind_Poseidon12-Goldilocks-8F22P-x7-no-pad,L_PI(Q_P).
   ```

   The second term is `choose(Q_H,2)/2^256` for Keccak-256 collisions. At the
   current 130-bit WHIR target this coarse bound is above 128 bits for
   `Q_H <= 3`, but falls just below 128 bits already at `Q_H = 4`. Thus the
   two-bit WHIR gap is not a usable unquantified grinding margin. A reviewed
   Fiat--Shamir theorem may derive a tighter protocol-specific loss, but it
   must expose its query/work budget and account for both Ext3 sumchecks and
   WHIR proof of work. The final symbolic term is Poseidon second-preimage
   advantage for an independently fixed public input, or chosen-collision
   advantage when both statements can be arranged. Under an ideal `p^4` output
   model alone those generic terms would be `Q_P/p^4` and
   `Q_P*(Q_P-1)/(2*p^4)`, respectively. A release needs a reviewed bound for the
   actual reduced-round instance; the approximately 95-bit work estimate must
   not be substituted as an additive `2^-95` probability.

The old three-base-repetition construction is excluded from this bound. Its
sequential round-bridging attack reaches constant success after roughly
`3*p/266` work even when its messages share a per-round master transcript.
The regression suite preserves this as a mandatory negative design test.

Likewise, replacing the query-dependent collision term with a literal
`2^-128` hash term gives

```text
-log2(2^-128 + epsilon_stat) ~= 127.678072 bits,
```

not 128 bits. A release using the literal-probability convention therefore
needs both a reviewed hash-binding margin and enough WHIR/Fiat--Shamir margin
for its declared `Q_H`; merely raising the WHIR target cannot make an already
fixed `2^-128` hash term plus a positive error at most `2^-128`. A wider
binding construction must strengthen every Merkle leaf/node binding; hashing
an already computed 256-bit root twice does not remove a collision in that
root.

#### V2 resource envelope

The following counts are architectural estimates, not acceptance
measurements. Using the current degree-13 `huge_mul` arithmetic dimensions
`preprocessed = 84`, `witness = 135`, `norm_inverse = 160`, `n = 13`, and
`d_gate = 10`, the directly exposed terminal and round payload is:

| Payload | Base-field limbs | Compact bytes at 8 bytes/limb |
|---|---:|---:|
| `r_log` claims: `(84 + 135 + 160)` Ext3 values | 1,137 | 9,096 |
| One gate terminal: `(84 + 135)` Ext3 values | 657 | 5,256 |
| Degree-five Ext3 log rounds: `13*5` Ext3 coefficients | 195 | 1,560 |
| One degree-ten Ext3 gate proof: `13*10` Ext3 coefficients | 390 | 3,120 |
| **Subtotal** | **2,379** | **19,032** |

This excludes roots, array lengths, transcript/hint streams, WHIR openings,
and ABI metadata. A direct `uint256`/three-word-Ext3 ABI representation would
consume at least `2,379 * 32 = 76,128` bytes for the same limbs before dynamic
array overhead; a packed canonical proof encoding is therefore part of any
plausible v2 DA design.

The WHIR shape uses two linear-form points and `n + 8` variables with three
commitments. The conservative constituent-projection term over all six cells
is

```text
6 * ell / p^3 = 48 / p^3, approximately 2^-186.4.
```

The versioned v2 configuration now regenerates and pins the exact profile for
this shape. This sampled resource proof reaches the degree, packed-width, wire,
and 123-constraint dimensions, but it has one public input and five configured
gate rows; it is not a simultaneous instantiation of the generic 256-PI and
255-gate-row decoder ceilings. The checked-in degree-13 proof measures 194,244 compact bytes; its
grammar-theoretic maximum is 201,636 bytes, below the strict 253,921-byte
two-SimpleCoder-blob cap. The same proof contains 2,032 NARG bytes and 173,016
hint bytes against caps of 2,032 and 180,408 bytes. Its direct Solidity proof
ABI is 254,816 bytes (262,208-byte grammar maximum), but that ABI expansion is
not the compact DA representation.

The sampled resource proof's atomic paths are measured on the local Forge EVM as follows.
Each upper bound is measured execution plus intrinsic calldata gas:

| Entry point | Execution gas | Intrinsic calldata gas | Transaction upper bound |
|---|---:|---:|---:|
| `MleVerifierV2.verify` | 19,317,468 | 3,269,668 | 22,587,136 |
| `PinnedMleVerifierV2.verifyCompact` | 20,564,468 | 2,985,924 | 23,550,392 |
| compact public-input return | 20,564,815 | 2,985,924 | 23,550,739 |
| compact fraud classifier | 20,674,425 | 2,986,180 | 23,660,605 |

All are below the repository's 30-million-gas gate. Production runtime sizes
are 20,257 bytes for `MleVerifierV2`, 12,101 for
`PinnedMleVerifierV2`, and 23,771 for `SpongefishWhirVerify`, all below
EIP-170. These are reproducible repository acceptance measurements, not a
prediction of any particular public chain's block policy.

As specified above, the 130-bit WHIR target still has no unquantified
Fiat--Shamir/grinding margin, and the conventional Keccak/Merkle collision
work factor is not interchangeable with a literal additive advantage. That is
a security-definition release condition, not a missing implementation or
resource measurement.

For comparison, putting four base-field permutation repetitions behind one
physical inverse root is not a free one-root optimization. Four independent
`2R = 160` blocks require 640 real columns and a canonical width of 1024. Four
points must fix the top two constituent selector bits to select the intended
block; one unconstrained ten-bit fold would mix repetitions and would not bind
the four terminal arrays independently. Because the current grouped WHIR uses
one variable count for all groups, this changes every group from `n + 8` to
`n + 10` variables and increases the committed codeword domain by a factor of
four. The norm implementation is therefore decisively smaller in helper width
and WHIR prover work than that rejected construction, and its complete v2
sampled resource envelope is measured above. The parent separately admits its
six exact pinned production profiles; a new profile needs a real integrated
proof/gas gate rather than relying on the wider parser ceilings. There is no production
four-base-repetition implementation to support a like-for-like gas claim, and
its Fiat--Shamir sequential-bridging problem remains independently
disqualifying.

#### Required implementation and review work

The Rust and Solidity implementations now include the byte-matched
constant-state transcript, base-valued norm helpers, both exact Ext3
coefficient sumchecks, all 14 gate families, the three-commitment/two-point
WHIR statement, strict ABI and compact decoding, configuration/profile
binding, atomic verification, and proof-dependent fraud classification. The
cross-language fixture and native-WHIR traces bind roots, challenges,
coefficient limbs, terminal constituents, point/index order, query indices,
leaf bytes, protocol/session IDs, and exact stream EOF. V0/V1 bytes are
rejected at the V2 boundary. The sampled degree-13/max-width fixture closes its
own compact DA, gas, and runtime-size gates above; it is not evidence for every
simultaneous combination of the wider generic parser caps. The parent release
separately pins and admits its six exact production profiles, whose largest
current value path is the 103-public-input, 13-gate close statement.

The remaining release work is review and whole-system policy rather than a
missing V2 verifier phase:

- obtain a reviewed concrete advantage bound for the load-bearing Poseidon
  public-input binding, or replace it with a binding construction meeting the
  selected complete-statement target;
- approve a protocol-specific Fiat--Shamir/random-oracle theorem and declare
  its `Q_H`/grinding budget; the coarse literal bound drops below 128 bits at
  `Q_H = 4`;
- independently review the formal-coordinate/off-cube norm reduction, its
  conservative pole accounting, exact WHIR composition, and the Solidity
  arithmetic/transcript realization;
- quantify parent recursion and application composition. Parent recursion also
  uses the approximately 95-bit default Goldilocks Poseidon configuration and caps the whole-system claim below
  this local PCS target;
- retain the chain and pinned-configuration containment until those approvals
  and the parent migration gates are complete.

The trace suite is strong byte-exact differential evidence, but it does not
constitute literal instrumentation of every upstream prover and Solidity call
site. The independent red-team pass recorded here is internal, not an external
cryptographic audit.

Until that complete bound and migration exist, the correct disposition is:

```text
packed constituent PCS repair: implemented and mutation-tested
v2 atomic implementation/resource gates: pass locally
v2 local PCS/transcript work-factor target: 128 bits
v2 complete-statement work estimate: at most approximately 95 bits (Poseidon PI binding)
v2 literal advantage bound: conditional on explicit Q_H, Q_P, and reviewed Poseidon bound
external cryptographic approval: absent
unconditional production release: NO-GO
```

## Acceptance disposition

### Historical V1 evidence

The packed-PCS implementation and its local Rust/Solidity differential tests
pass. The generalized adversarial matrix covers all nine terminal-used
group/point cells in both Rust and Solidity. It keeps the four roots, WHIR
transcript and hints, all four sumchecks, derived terminal points and public
inputs fixed, preserves the applicable legacy batch and terminal equations,
and reaches packed-PCS rejection on the allowed chain. For the two-column
auxiliary cell, fixing both `auxEvalValue` and the combined terminal has only
the zero solution when `mu - eq(tau,r) * rho_aux` is nonzero (as it is in the
fixture); that case instead preserves the auxiliary decomposition and combined
terminal while updating the redundant aggregate claim. Separate low-level
tests also mutate every constituent and every Ext3 limb of each used cell.

The exact historical triples now also have proof-dependent PCS regressions.
The Rust-generated `contracts/test/fixtures/historical_pcs_triples.json`
contains, for each `small_mul` and parent-validity triple, a production-shape
packed-v1 WHIR proof that commits the exact audit-recorded `BEFORE`
constituents. It freezes the protocol/session IDs, four ordered roots, complete
NARG transcript, hints, four full Ext3 query points, all 16 honest packed
evaluations, and the 160-element `BEFORE`/`AFTER` witness and inverse vectors.
Rust and `SpongefishWhirVerify.verifyWhirProofBound` first accept the honest
baseline. The tests then change only `w0`, `w80`, and `A1` in the constituent
vectors, recompute only point-`inverse` slots 5 and 6 with the production fold,
and keep every proof byte, root, point, and other packed cell fixed. Rust's
first failure is `WHIR bound evaluation mismatch at 5`; Solidity returns the
proof-dependent `InvalidMleProof` from its initial bound-evaluation comparison.
The fixture is regenerated only with
`MLE_WRITE_HISTORICAL_PCS_FIXTURE=1`; the ordinary Rust test checks exact drift.

That result closes the exact-frozen gate at the packed PCS boundary, but it is
not a full current-v1 outer proof that recreates the retired v0 challenge
sequence. The historical witness cancellation holds only for its recorded
`rho`, and the inverse terminal cancellation additionally fixes the old
`beta/gamma`, `lambda_inv`, and `mu_inv`. In v1 the roots are committed before
those Fiat-Shamir values, so matching even one exact historical 64-bit
challenge is a random-oracle preimage search, while the old v0
version/session/layout intentionally cannot decode as v1. No current fixture
generation API can force these challenges without replacing the production
verifier. A literal full-outer historical transcript/sumcheck baseline therefore
remains unmet and is separate from the passing PCS-layer regression.

Protocol separation at the byte-decoding boundary is tested independently:
`BoundaryCheckTest` defines the exact retired 63-field v0 Solidity tuple,
round-trips a canonical old-ABI encoding, and then proves that both the v1 raw
decoder and authenticated fraud-verdict path reject those bytes. This closes
the old-proof/new-decoder byte-shape sub-gate; it does not recreate the old
Fiat--Shamir challenges discussed above.

Those paragraphs are frozen V1 regression evidence, not a description of the
production V2 proof shape.

### Current V2 disposition

The submodule's implementation acceptance gates now pass: the former
post-challenge batching kernel is removed, both complete Ext3 relations are
atomically verified against one grouped WHIR proof, canonical/resource checks
fail closed, and the V2/V1 boundary is explicit. The synthetic
resource fixture samples the maximum admitted row/wire/constraint dimensions
with 1 public input and 5 gate rows; the six exact parent-production
configuration digests (at most 103 public inputs and 13 gate rows) are pinned
separately and their real proofs are covered by the on-chain gas suites. The
local Forge gate on 2026-09-03 reports 337 passing tests in 27 suites with no
failure or skip.

The handoff's unconditional production criterion is nevertheless **not
accepted**:

- **High:** the literal random-oracle bound remains
  `Adv_v2(Q_H,Q_P) <= Q_H*epsilon_stat + Q_H*(Q_H-1)/2^257
  + Adv_bind_Poseidon(Q_P)`; even before the Poseidon term it is below the
  requested 128-bit level at `Q_H = 4`, and no reviewed concrete Poseidon
  advantage bound is supplied;
- **High:** the complete statement is load-bearing on the concrete Goldilocks
  Poseidon public-input hash, for which the repository records only an
  approximately 95-bit work estimate. The 128-bit figure applies only to the
  local PCS/transcript component;
- **High, whole-system:** parent recursion/application composition is not
  established here and uses the approximately 95-bit default Goldilocks
  Poseidon configuration, capping the system even though the local conventional
  PCS work factor is 128 bits;
- **High:** no external cryptographic review has approved the new transcript,
  norm/logUp and gate reductions, exact WHIR statement, malicious-prover
  model, or cross-language implementation.

The immutable allowed-chain and pinned-configuration restrictions remain
containment. This internal independent review does not authorize a production
deployment or relaxation of those restrictions.
