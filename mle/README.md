# `plonky2_mle` — MLE/WHIR PCS wire v3 (`V2` API generation)

> **Release status: local PCS engineering candidate, not an unconditional
> production approval.** Wire v3 repairs the historical constituent-batching
> forgery and directly binds every raw public input to a canonical routed
> witness cell. Every constituent table is committed before its challenges and
> every terminal value is authenticated by one three-group, two-point WHIR
> statement. The round-by-round WHIR failure events are unioned explicitly;
> target 105 at inverse rate `2^-6` gives about 101.535 bits of aggregate
> generic work, a deliberate approximately-100-bit design point chosen so the
> parent's cold close transaction fits a 20,000,000-gas envelope. This is not a
> literal probability for one completed proof: an attacker can abort and grind
> at intermediate Fiat--Shamir stages. The conservative raw-oracle bound loses
> `log2(H)` bits and is only about 69.535 bits at `H = 2^32`. Parent recursion
> separately retains the default
> Goldilocks Poseidon configuration whose repository estimate is about 95 bits,
> so the whole application is not a 128-bit system. The current worktree must
> also complete fixture migration and the full acceptance matrix. Keep release
> containment in place until those gates and an external cryptographic audit
> are complete.

This crate reuses Plonky2 circuit and witness generation while replacing its
univariate proof engine with dense multilinear extensions, two Ext3
sumchecks, a norm/logUp permutation argument, and a grouped WHIR polynomial
commitment statement.

The machine-readable protocol source is
[`protocol/mle_whir_v2.json`](protocol/mle_whir_v2.json). Generated Rust and
Solidity constants are drift-checked against it. The current security derivation is
in the wire-v3 addendum of
[`paper/mle_whir_v1_security.md`](paper/mle_whir_v1_security.md); that filename
is retained for history and its earlier v0/v1 sections are not the production
protocol. Historical `V2` suffixes on code symbols and filenames identify the
implementation generation; they do not authorize wire-v2 bytes.

## Production statement

Wire v3 has three ordered packed commitment groups:

1. `preprocessed = constants || sigmas`;
2. `witness = wires`;
3. `norm_inverse = norm(A_0)^-1 || ... || norm(B_{R-1})^-1`.

Each group is one packed bivariate table `F(row, constituent_index)`. Row bits
are the low dense-table bits and constituent-index bits are the high bits; both
are LSB-first. Unused constituent slots are committed zeros. The native WHIR
boundary reverses the complete packed point, so Solidity supplies
`reverse(index) || reverse(row)` and Rust applies the equivalent full-point
reversal exactly once.

There are two terminal row points, `log` and `gate`, and six point-major,
group-major claim cells. The bound-cell mask is `0x1f`:

| Point | Preprocessed | Witness | Norm inverse |
|---|---:|---:|---:|
| `log` | terminal-used and bound | terminal-used and bound | terminal-used and bound |
| `gate` | terminal-used and bound | terminal-used and bound | WHIR-authenticated, not terminal-used |

The sixth cell is deliberately included in the WHIR statement and projection
accounting even though no outer terminal equation consumes it.

The verification key also contains exactly one three-byte
`row_u16_le || routed_column_u8` record for each public input, in public-input
order with duplicates retained. The location is the first row-major routed
wire in that target's Plonky2 copy-equivalence class. For raw inputs `PI_i`,
mapped witness columns `W_{c_i}`, and the row equality polynomial, the joint
degree-five sumcheck contains the direct relation

```text
D_PI(x) = sum_i eta^i * eq(row_i, x) * (W_{c_i}(x) - PI_i),
joint(x) = norm/logUp(x) + xi * D_PI(x).
```

Thus `sum_x D_PI(x) = 0` binds the raw statement directly to committed witness
cells. Plonky2's public-input Poseidon digest remains part of the evaluated
circuit, but it is no longer the sole or load-bearing raw-PI binding.

The production protocol identifiers are:

```text
outer transcript: plonky2-mle-outer-v3
packed schema:    mle-whir-packed-schema-v3
WHIR session:     plonky2-mle-whir-split-v3
PI eta domain:    public-input-aggregation-challenge-v3
PI xi domain:     public-input-mix-challenge-v3
claim domain:     pcs-constituent-claims-v3
index domain:     pcs-constituent-index-v3
compact magic:    MLEWHIR3
```

## Commit-before-challenge and transcript order

The outer transcript is one typed, framed Keccak transcript shared by Rust and
Solidity. Its security-critical order is:

1. absorb the exact circuit statement, configuration digest, WHIR protocol and
   session IDs, then the preprocessed and witness roots;
2. sample the full-`Fp3` public-input aggregation challenge `eta` from the
   already committed witness root;
3. sample the denominator challenges `beta` and `gamma`;
4. construct the challenge-dependent norm-inverse table, commit it, and absorb
   its root;
5. sample the full-`Fp3` public-input mix challenge `xi`, then `lambda`, `rho`,
   `kappa`, `tau_log`, `gate_alpha`, and `gate_tau`;
6. in each row round, absorb all five non-constant log coefficients followed
   by all gate coefficients, then sample independent full `Fp3` log and gate
   challenges;
7. absorb all six ordered constituent-claim slots (the unused gate/norm slot is
   an explicit empty vector), sample the two independent `Fp3` index points,
   and only then hand the derived claims and points to WHIR.

Thus no root, round polynomial, or claim vector is chosen after the challenge
that binds it. Independent counter outputs and explicit domains prevent
cross-role transcript reuse. `eta = 0` or `xi = 0` is retained as a uniformly
sampled bad event and charged in the direct-PI soundness term; rejection
sampling that would bias the transcript is not used. Lockstep ordering itself
is not counted as security amplification.

## Field, degree, and circuit profile

All outer challenges and arithmetic live in
`Fp3 = Fp[theta]/(theta^3 - 2)` over the Goldilocks prime
`p = 0xffffffff00000001`. Plonky2 quadratic-extension values remain pairs of
`Fp3` coordinates with inner non-residue 7. The verifier rejects any other
base field or inner extension degree.

The norm/logUp round polynomial has exact degree five. The gate sumcheck uses
the exact bound
`quotient_degree_factor + 2 <= 10`. The same Ext3 evaluator covers all 14
supported Plonky2 gate families at round nodes and at the terminal point.
Lookup tables are not supported and fail closed.

The decoder/reviewed maxima are:

| Parameter | Maximum |
|---|---:|
| row variables | 13 |
| routed wires | 80 |
| constituent width | 160 |
| constituent-index bits | 8 |
| gate constraints | 123 |
| gate round degree | 10 |
| gate rows | 255 |
| public inputs | 256 |
| circuit-digest limbs | exactly 4 |

These are fail-closed generic decoder ceilings, not a promise that every axis
can be combined in one 30-million-gas transaction. The parent release admits
six exact pinned configurations separately; its largest current profile has
103 public inputs and 13 configured gate rows. Any new configuration requires
its own real-proof DA and gas admission before deployment.

The verification key binds the exact circuit digest and configuration digest,
ordered gate metadata, canonical PI wire map, dimensions, coset shifts,
subgroup powers, packed schema, and WHIR protocol/session IDs. The map is a
trusted-setup output: generate it only from complete `CircuitData` through
`mle_setup_v2`/the config exporter, and require `validate_against_circuit`
before admitting a deployment artifact. A verifier that has only common data
cannot rediscover the original PI target copy classes, so a hand-written map
is forbidden. Proof-free consumers additionally recompute its circuit-config
digest and require exact VK/config/ABI/pinned-view agreement. Both direct Rust
verification and the Solidity/compact paths enforce the reviewed byte and
shape limits before expensive parsing or allocation.

The generated parent close configuration has 103 map entries in exactly 13
unique rows: rows 0 through 11 each use columns 0 through 7, and row 12 uses
columns 0 through 6. A Rust release test independently rederives that exact
layout from `CircuitData`. The matching Solidity terminal microbenchmark
measures 508,524 gas for the direct-PI increment, leaving 163,476 gas inside
its dedicated 672,000-gas allowance. This is a component margin only; the
complete close entry point remains subject to its separate real-proof
20,000,000-gas release gate.

## Canonical decoding and resource limits

Base-field and every Ext3 limb must be canonical (`< p`). Commitment roots are
exactly 32 bytes and the circuit digest is exactly four limbs. The wire-v3
compact stream (implemented by the historical `CompactV2` API) uses
little-endian scalar limbs, exact schema-derived vector lengths, exact EOF,
and rejects truncation, tails, non-canonical aliases, overflowed length
prefixes, wrong magic/version, and zero WHIR final-fold divisors.

The schema-fixed input caps are:

| Input | Cap |
|---|---:|
| WHIR NARG/transcript | 1,904 bytes |
| WHIR hints | 112,408 bytes |
| compact proof | 253,921 bytes |

For the checked-in degree-13 resource fixture (maximum row, wire and gate-
constraint dimensions; one public input and five configured gate families):

| Measurement | Bytes |
|---|---:|
| compact proof, actual | 129,284 |
| compact proof, grammar-theoretic maximum | 133,508 |
| Solidity proof ABI, actual | 189,856 |
| Solidity proof ABI, grammar-theoretic maximum | 194,080 |
| Solidity verification config ABI | 5,664 |
| WHIR NARG/transcript, actual | 1,904 |
| WHIR hints, actual | 108,184 |

The compact grammar maximum is below the strict two-SimpleCoder-blob cap. The
larger Solidity ABI number is an execution/calldata representation, not the
parent's compact DA payload.

On the checked-in fixture and local Forge EVM, the enforced transaction-gas
upper bounds (measured execution plus intrinsic calldata gas) are:

| Production entry point | Execution | Intrinsic calldata | Upper bound |
|---|---:|---:|---:|
| `MleVerifierV2.verify` | 11,689,441 | 2,299,260 | 13,988,701 |
| `PinnedMleVerifierV2.verifyCompact` | 12,666,921 | 2,014,964 | 14,681,885 |
| compact public-input return | 12,667,290 | 2,014,964 | 14,682,254 |
| compact fraud classifier | 12,724,559 | 2,015,092 | 14,739,651 |

These are reproducible local acceptance measurements, not a prediction of a
particular public chain's block policy. They are warm-path Forge numbers: the
adapter's configuration is read once per test process. `PinnedMleVerifierV2`
keeps its 5,664-byte configuration in an immutable code-resident store (a
`STOP`-prefixed data contract created by its constructor) and materializes it
with one `EXTCODECOPY` plus `abi.decode`. Compared with the earlier
constructor-written storage copy, that costs about 5,000 gas more on a warm
path but about 366,000 gas less on a production-shaped cold transaction, where
the roughly 170 storage slots were each a 2,100-gas cold `SLOAD`. The parent
repository's cold 103-public-input Manager close path measured 16,901,877
execution gas plus 2,017,528 intrinsic calldata gas against that store
(18,919,405 in total; 18,919,366 on a real Anvil transaction). All four
sampled upper bounds and the parent cold path are below the repository's
20,000,000-gas gate; the parent cold path retains 1,080,595 gas of headroom.

`forge build --sizes --offline` reports the production runtime sizes:

| Contract | Runtime bytes | EIP-170 margin |
|---|---:|---:|
| `MleVerifierV2` | 20,053 | 4,523 |
| `PinnedMleVerifierV2` | 12,570 | 12,006 |
| `SpongefishWhirVerify` | 23,656 | 920 |

## Build and verification

The repository pins `nightly-2025-03-23`; do not replace it with mutable
`nightly`.

From the `polygon-plonky2` workspace root:

```bash
cargo build -p plonky2_mle --locked --offline
cargo test -p plonky2_mle --all-targets --locked --offline
```

For Solidity:

```bash
cd mle/contracts
forge test --offline
forge build --sizes --offline
```

The 2026-09-04 local gate ran 347 Forge tests in 27 suites with zero failures
or skips, including the four sampled max-row resource assertions above. Rust includes
cross-language transcript/WHIR traces, exact schema/codegen drift checks,
compact decoder mutations, malformed-proof and panic-totality regressions,
all-six-cell claim mutations, circuit/VK binding tests, and the machine-checked
soundness budget. Expensive randomized maximum-fixture regeneration remains an
explicitly ignored opt-in test; the ordinary suite verifies the checked-in
canonical fixture without rewriting it.

Regeneration is always explicit:

```bash
MLE_WRITE_PROTOCOL_SCHEMA_V2=1 \
  cargo test -p plonky2_mle --test protocol_schema_v2_codegen --locked

MLE_WRITE_V2_FIXTURE=1 \
  cargo test -p plonky2_mle --test v2_cross_language_fixture --locked \
  regenerate_v2_cross_language_fixture -- --ignored --exact --nocapture

MLE_WRITE_V2_RESOURCE_FIXTURE=1 \
  cargo test -p plonky2_mle --test v2_resource_envelope \
  generate_real_max_row_profile_fixture --locked -- --ignored --nocapture
```

Check each test's environment guard before regeneration; normal test runs are
read-only drift checks.

## Security accounting and remaining release gates

For `q = p^3`, the conservative maximum-profile terms are:

```text
epsilon_log        = 2,621,599 / q  ~= 2^-170.677984
epsilon_PI         =       256 / q  ~= 2^-184
epsilon_gate       = 265 / q        ~= 2^-183.95
epsilon_projection = 48 / q         ~= 2^-186.4
epsilon_outer      = 2,622,168 / q  ~= 2^-170.678
```

The pinned WHIR `Config::security_level()` is only the minimum displayed
round-by-round term, not the union of the complete protocol's failure events.
`outer_soundness_budget.rs` reconstructs and sums every native inverse-work
term with its multiplicity for each admitted packed dimension 1 through 21. At the maximum
dimension there are 35 charged events. Nine attain the configured 105-bit
target (the four intermediate-round queries, the four binary folds of the last
intermediate round, and the final query), while the initial folds, RLC, OOD,
and final-fold terms contribute at their own higher bit levels. The resulting
native aggregate work measure is

```text
omega_WHIR,work(21) ~= 2^-101.534561723.
```

Target 104 is retained as a negative regression: its aggregate is only about
`2^-100.674765149`. The selected target-105/PoW-22/inverse-rate-6/fold-4
profile uses the dimension-21 sample schedule `[29,19,14,12,10]`; the retired
target-133/inverse-rate-4 profile needed `[58,33,23,18,14]`. Its maximum
internal PoW is about 21.9855 bits and its modeled total PoW work about
22.7830 bits. Halving the sample schedule is what moves the maximum-resource
WHIR hint payload from 173,784 to 108,184 bytes and removes roughly one third
of the verifier's Merkle and constraint work; the prover pays for the lower
rate with a four-times larger initial codeword, which is acceptable because
these proofs are only ever produced server-side.

Under the conventional generic-work-factor convention, the local minimum is
now the WHIR union itself, about 101.5 bits, below the 128-bit generic
Keccak-256 collision work. That is the intended approximately-100-bit design
point of this profile, not an accident: the retired target-133 profile cost
about 4,700,000 more gas on the parent close path. The convention is not a
literal fixed failure probability and is not a whole-parent-system claim. The direct PI relation removes the former approximately-95-bit Poseidon
bottleneck from this local statement boundary.

The 101.535-bit WHIR number includes internal PoW difficulties and is therefore
a generic-work exponent. It is not the conditional failure probability of one
valid completed proof: a malicious prover can abandon a candidate after an
unfavorable intermediate challenge and grind at that stage without ever
submitting a complete proof. Let `A_j`, `B_k`, and `C_l` be raw-oracle work
trials allocated respectively to WHIR stage `j`, outer event `k`, and
extraction event `l`; a candidate behind `d` bits of PoW consumes about `2^d`
such trials. Let `H` be the total raw Keccak oracle calls. A literal ROM
accounting has the form

```text
Adv_wire3({A_j}, {B_k}, {C_l}, H)
  <= sum_j A_j * 2^-b_j
     + sum_k B_k * epsilon_outer,k
     + sum_l C_l * delta_extract,l
     + H * (H - 1) / 2^257.
```

Here `b_j` includes the exact PoW acceptance work at stage `j`. Bounding every
stage trial count conservatively by `H` gives

```text
Adv_wire3(H)
  <= H * (omega_WHIR,work
          + 2,622,168 / q
          + 228 * p / 2^256
          + 102 * p / 2^320)
     + H * (H - 1) / 2^257.
```

Each outer base limb reduces 256 Keccak bits modulo `p`, giving statistical
distance below `p/2^256 < 2^-192`; native WHIR deliberately squeezes 40 bytes
per base limb, giving below `p/2^320 < 2^-256`. WHIR query indices reduce
uniform bytes modulo a power-of-two codeword size and are exactly uniform.
The maximum-dimension counts are 228 outer and 102 WHIR base limbs; the WHIR
count is cross-checked against the actual pinned native trace and its 120-byte
`Fp3` codec squeezes. The coarse bound loses about `log2(H)` from the
101.535-bit union-work figure: at `H = 2^32` it is only about 69.535 bits,
although the Keccak collision term alone is about 193 bits. Counting completed
proofs instead of raw intermediate candidates is unsound. Therefore target 105
meets the approximately-100-bit aggregate generic-work design point but does
not establish a literal unqualified `2^-100` advantage bound; that requires a protocol-specific,
externally reviewed Fiat--Shamir/grinding analysis and operational oracle
budget.

Generic 128-bit Keccak collision work is a separate computational convention,
not an additive `2^-128` failure term. It must not be mixed into the literal
formula above.

Remaining release gates are:

- **High:** obtain a protocol-specific Fiat--Shamir/grinding theorem and set an
  operational raw-oracle budget; target 105 establishes about 101.5 bits of
  aggregate generic work, not a literal `2^-100` advantage for arbitrary
  intermediate retries;
- **High, whole-system:** quantify parent composition. Parent recursion also uses
  the approximately 95-bit default Goldilocks Poseidon configuration, which caps the whole system below the
  local PCS claim even if this submodule is otherwise sound;
- **High:** obtain an external cryptographic review of the wire-v3 transcript,
  norm/logUp reduction, gate reduction, packed projection, and WHIR binding;
- **High:** finish the wire-v3 config/full-fixture migration and rerun the
  complete Rust/Solidity/Node/WASM/DA/gas/size acceptance matrix;
- keep the immutable chain/deployment containment and pinned verification
  configuration until those approvals are complete.

This README records an internal independent adversarial review. It must not be
cited as external audit approval.

## Frozen V1 legacy

`prover.rs`, `verifier.rs`, `proof.rs`, `transcript.rs`,
`protocol/mle_whir_v1.json`, `MleVerifier.sol`, and V1 trace/history fixtures
are frozen compatibility and negative-regression material. They preserve the
old proof shapes and the exact historical constituent-cancellation exploit so
V2 cannot regress.

V1 is not a production fallback. New integrations must use `*_v2` Rust APIs,
`MleVerifierV2`/`PinnedMleVerifierV2`, current generated constants, and compact
magic `MLEWHIR3`. V1, retired wire v2, and current wire v3 domains, layouts,
sessions, decoders, and verification keys are intentionally isolated;
accepting an old proof in the current entry point is a security failure.

## Repository map

```text
mle/
├── protocol/mle_whir_v2.json       canonical wire-v3 schema (historical filename)
├── src/
│   ├── prover_v2.rs                staged commitments and coupled Ext3 prover
│   ├── verifier_v2.rs              native V2 verifier and resource boundary
│   ├── proof_v2.rs                 V2 proof/VK types and dimension helpers
│   ├── compact_v2.rs               strict compact codec
│   ├── transcript_v2.rs            typed framed Keccak transcript
│   ├── gate_ext3.rs                exact Plonky2 gate evaluation over Fp3
│   ├── permutation/norm_logup.rs   norm/logUp relation
│   ├── commitment/whir_pcs.rs      grouped packed WHIR adapter and preflight
│   └── generated/mle_whir_v2.rs    generated Rust constants
├── contracts/
│   ├── src/MleVerifierV2.sol       atomic Solidity verifier
│   ├── src/PinnedMleVerifierV2.sol compact production adapter
│   ├── src/CompactMleProofV2.sol   strict compact decoder
│   ├── src/OuterLogupExt3Verifier.sol
│   ├── src/Plonky2GateEvaluatorExt3.sol
│   ├── src/PackedClaimExt3.sol
│   ├── src/TranscriptV2.sol
│   ├── src/spongefish/SpongefishWhirVerify.sol
│   └── src/generated/              generated Solidity constants/profiles
├── tests/                           Rust parity, mutation, and budget gates
├── contracts/test/                 Foundry parity, mutation, and resource gates
└── paper/mle_whir_v1_security.md   historical record plus V2 derivation
```
