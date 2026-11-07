#!/usr/bin/env bash
# Per-phase gas profile of the V2 verifier, end to end, into a scratch directory.
#
#   usage: gasprof/run.sh <scratch-dir>
#
# The tracked sources are never modified: a copy of mle/contracts is made under
# <scratch-dir>/contracts, instrumented with gasprof/patch.py, built and run there.
# Outputs left in <scratch-dir>:
#   base_harness_run.log   uninstrumented harness run (raw staticcall totals, calldata stats)
#   timing_run.log         instrumented run, marks only (gasleft at every mark)
#   counting_run.log       instrumented run with the operation counters compiled in
#   profile_full.txt       every span with mark-corrected gas and operation counts
#   summary_tables.txt     the phase table (corrected callee totals per fixture)
set -euo pipefail

if [ $# -ne 1 ]; then
    echo "usage: $0 <scratch-dir>" >&2
    exit 2
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONTRACTS="$(dirname "$HERE")"
SCRATCH="$(mkdir -p "$1" && cd "$1" && pwd)"
case "$SCRATCH" in
    "$CONTRACTS"|"$CONTRACTS"/*)
        echo "scratch dir must be outside the tracked contracts tree: $SCRATCH" >&2
        exit 2
        ;;
esac
WORK="$SCRATCH/contracts"
FORGE_ARGS=(test --offline -vv --match-contract GasProfileTest)

echo "== scratch copy -> $WORK"
rm -rf "$WORK"
mkdir -p "$WORK/test/fixtures"
cp -R "$CONTRACTS/src" "$WORK/src"
cp -R "$CONTRACTS/lib" "$WORK/lib"
cp "$CONTRACTS/foundry.toml" "$WORK/foundry.toml"
[ -f "$CONTRACTS/foundry.lock" ] && cp "$CONTRACTS/foundry.lock" "$WORK/foundry.lock"
cp "$CONTRACTS"/test/fixtures/v2_*.json "$WORK/test/fixtures/"
cp "$HERE/GasProfile.t.sol" "$WORK/test/GasProfile.t.sol"

echo "== baseline (uninstrumented) harness run"
(cd "$WORK" && forge "${FORGE_ARGS[@]}") | tee "$SCRATCH/base_harness_run.log" | grep -E "^\[|TOTAL|CALLDATA|INTRINSIC|CODESIZE"

echo "== instrumenting the scratch copy"
cp "$HERE/GasProbe.sol" "$WORK/src/GasProbe.sol"
python3 "$HERE/patch.py" "$WORK/src"

echo "== timing run (marks only)"
(cd "$WORK" && forge "${FORGE_ARGS[@]}") > "$SCRATCH/timing_run.log"
grep -E "^\[|TOTAL" "$SCRATCH/timing_run.log"

echo "== counting run (operation counters compiled in)"
python3 - "$WORK/src/GasProbe.sol" <<'EOF'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
t = p.read_text()
flag = "bool internal constant COUNTING = false; // PROBE_COUNTING_FLAG"
assert t.count(flag) == 1, "PROBE_COUNTING_FLAG anchor not found exactly once"
p.write_text(t.replace(flag, flag.replace("false", "true")))
EOF
(cd "$WORK" && forge "${FORGE_ARGS[@]}") > "$SCRATCH/counting_run.log"
grep -E "^\[|TOTAL" "$SCRATCH/counting_run.log"

echo "== parsing"
python3 "$HERE/parse.py" "$SCRATCH/timing_run.log" "$SCRATCH/counting_run.log" > "$SCRATCH/profile_full.txt"
python3 "$HERE/summarize.py" "$SCRATCH/timing_run.log" > "$SCRATCH/summary_tables.txt"

echo "== done: $SCRATCH/summary_tables.txt"
grep -E "^====|sum of groups" "$SCRATCH/summary_tables.txt"
