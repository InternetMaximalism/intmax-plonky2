# Per-phase gas profiler for the V2 verifier

Reproducible per-phase execution-gas profile of `PinnedMleVerifierV2.verifyCompact`
(and `verifyCompactPublicInputs`, `MleVerifierV2.verify`) over the checked-in
fixtures. It is the procedure that produced `mle/tasks/gas_profile_2026-11-07/`
and the "Gas baseline and profiling" section of `mle/README.md`.

Nothing in this directory is compiled by the tracked project: `foundry.toml`
only collects `src`, `test` and `script`, so `forge build` / `forge test` never
see `gasprof/*.sol` (`forge test --list | grep GasProfile` is empty). The
procedure instruments a **scratch copy** of `mle/contracts`; it must never be
applied to the tracked sources, and `patch.py` refuses to write to them.

## What it measures

`GasProfile.t.sol` deploys the core and the pinned adapter exactly like
`V2ResourceEnvelope.t.sol` / `GasBaselineV2.t.sol`, pre-encodes the calldata,
and measures one raw `staticcall` with a `gasleft()` delta, so the harness-side
argument copy is excluded and the uninstrumented totals equal the tracked
baseline (`GasBaselineV2.t.sol`) to within a few gas of memory-expansion
offset. It also prints the calldata byte statistics, the legacy intrinsic cost
(21,000 + 4/zero byte + 16/non-zero byte) and the EIP-7623 floor
(21,000 + 10 x (zero bytes + 4 x non-zero bytes)).

`GasProbe.sol` is a library with `mark(id)`: it records `gasleft()` and ships
it to the forge console as a `log(uint256)` word written into free memory
without bumping the free pointer, so a mark has a near-constant cost. The word
packs `kind(8) | id(24) | freePtr(64) | gasleft(160)`. With `COUNTING = true`
(flipped by `run.sh` on the `PROBE_COUNTING_FLAG` anchor) additional counter
probes are compiled in that count keccak invocations/bytes, Ext3 multiplications
and base-field `mulmod`s per site; those are attributed to the spans of the
timing run by event position.

`patch.py` holds 103 exact-match replacements that insert marks (and counters)
into 15 files of the scratch `src/`. Every anchor must match exactly once or
the script aborts without writing. Mark id ranges: 10-13/110-127/9001-9005
pinned adapter and compact decoder (`P`), 20-55 core (`C`), 60-77/1000-1199
outer coupled sumcheck and terminal (`O`), 200-599 WHIR (`W`; 300+20r per
folding round, 450+10c per round-0 commitment, 420-424 constraint values,
500-524 final round), 600-699 gate evaluator (`G`), 700-708 Poseidon gate
(`PS`), 800-802 gate terminal (`GT`), 850-851 public-input Poseidon (`PH`).

### Mark correction

A mark costs **207 gas** (measured by the calibration marks 9001/9002/9003 and
9004/9005 placed back to back at the entry and exit of `verifyCompact`; `parse.py`
takes the median of the three calibration gaps). Every span `a -> b` is
reported as `raw - (marks strictly inside + 1) x 207`, and every frame total
(entry mark to exit mark) as `raw - (marks in between) x 207`. The corrected
callee total therefore equals what the uninstrumented bytecode costs up to the
residual that the marks' own code-size/jump effects introduce: with the 103
patches the corrected max total is **12,688,189** against the uninstrumented
raw-staticcall **12,654,251** (+0.27%); the small fixture is 7,863,277 against
7,850,402 (+0.16%). The counters (counting run) are not gas-corrected; only
their event positions are used.

Boundary spans (`BOUNDARY` rows in the summary) are caller spans around an
external/delegate call minus the callee's own corrected frame total, i.e. the
ABI encode/decode, copy and call overhead of crossing that boundary.

## Running it

The whole procedure, into a scratch directory outside the tree:

```sh
cd mle/contracts
./gasprof/run.sh /path/to/scratch
```

This performs, in order (each `forge test` compiles the scratch copy with the
tracked `foundry.toml`, i.e. via-IR, 200 runs, prague):

1. `rm -rf scratch/contracts`, copy `src/`, `lib/`, `foundry.toml`, `foundry.lock`
   and `test/fixtures/v2_*.json` there, plus `gasprof/GasProfile.t.sol` as the
   only test.
2. `forge test --offline -vv --match-contract GasProfileTest` on the
   uninstrumented copy -> `scratch/base_harness_run.log` (raw totals, calldata
   statistics, runtime code sizes).
3. Copy `gasprof/GasProbe.sol` to `scratch/contracts/src/` and run
   `python3 gasprof/patch.py scratch/contracts/src` (aborts if any anchor does
   not match exactly once).
4. Same forge command -> `scratch/timing_run.log` (marks only).
5. Flip `COUNTING = false; // PROBE_COUNTING_FLAG` to `true` in the scratch
   `GasProbe.sol`, same forge command -> `scratch/counting_run.log`.
6. `python3 gasprof/parse.py timing_run.log counting_run.log > profile_full.txt`
   (every span, corrected gas, operation counts per span) and
   `python3 gasprof/summarize.py timing_run.log > summary_tables.txt` (the
   phase table for the max and small `verifyCompact` runs).

It takes about two minutes. The reference outputs for the current sources are
in `mle/tasks/gas_profile_2026-11-07/`; a rerun must reproduce
`summary_tables.txt` exactly (max corrected total 12,688,189) as long as
`src/` is unchanged.

Manual steps, if you need only part of it:

```sh
# verify the anchors still match the tracked sources without writing anything
python3 gasprof/patch.py --check src

# instrument an existing scratch copy
cp gasprof/GasProbe.sol /path/to/scratch/contracts/src/
python3 gasprof/patch.py /path/to/scratch/contracts/src
(cd /path/to/scratch/contracts && forge test --offline -vv --match-contract GasProfileTest) > timing_run.log
python3 gasprof/summarize.py timing_run.log
```

## Maintaining the patches

When a tracked source changes, `patch.py --check src` says which anchor no
longer matches. Update that anchor (old text) and its replacement so the marks
stay in the same logical positions; keep the mark ids, because `parse.py`
(`LABELS`, `ENTRIES`/`EXITS`, `frame_of`) and `summarize.py` (`group_of`) name
and group the spans by id. New marks need a label in `parse.py` and a group in
`summarize.py`, otherwise they appear under `99 unclassified`.

The uninstrumented totals that the baseline test enforces are in
`test/GasBaselineV2.t.sol`; the profile explains them, it does not gate them.
