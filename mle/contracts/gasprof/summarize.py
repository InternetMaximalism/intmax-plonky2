#!/usr/bin/env python3
"""Group the parsed spans into the phase table requested for the gas-halving plan."""
import sys
from collections import OrderedDict
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from parse import parse, Profile, fmt

def group_of(fr, a, b):
    """Return (group, subgroup) for a span; boundary spans handled separately."""
    if fr == "P":
        if a in (10, 9001, 9002, 9004, 13) or (a == 9003): return ("00 Pinned adapter: entry/chainid/config load", "glue/chainid")
        if a == 110: return ("00 Pinned adapter: entry/chainid/config load", "EXTCODECOPY config store")
        if a in (111, 11): return ("00 Pinned adapter: entry/chainid/config load", "glue")
        if a == 12: return ("02 BOUNDARY Pinned->core.verifyCompactWithConfig (compact+config calldata copy, STATICCALL, return)", None)
    if fr == "C":
        if a == 20: return ("03 Core: config digest (keccak of encoded config)", "")
        if a in (21, 127): return ("01 Compact parse", "glue")
        if 120 <= a <= 126:
            return ("01 Compact parse", {120: "header/digest/PIs/roots", 121: "whirTranscript copy", 122: "whirHints bounds (calldata slice)",
                                         123: "PIs + logProof rounds -> flat limbs", 124: "gateProof rounds -> flat limbs",
                                         125: "log terminal vectors -> flat limbs", 126: "blob seal + gate terminal vectors -> flat limbs"}[a])
        if a in (22, 30, 36): return ("05 Core: initial transcript", "statement absorption (16 frames)" if a == 30 else "glue")
        if a in (31, 32, 33, 34, 35):
            return ("05 Core: initial transcript", {31: "eta/beta/gamma/xi squeezes + normInverse root", 32: "lambda/rho/kappa squeezes",
                                                  33: "tau vector squeezes", 34: "gate alpha squeeze", 35: "gate tau vector squeezes"}[a])
        if a == 23: return ("06 Core: outer VK + views", "outer VK struct")
        if a == 24: return ("06 Core: outer VK + views", "pointer tables / sumcheck views")
        if a == 25: return ("07 BOUNDARY core->OuterLogupExt3Verifier (DELEGATECALL ABI encode/decode)", None)
        if a in (26, 40): return ("10 Core: constituent-claim absorption", "5 Ext3 vec frames (calldatacopy of wire records)")
        if a in (41, 42): return ("11 Core: index-point squeezes", "2 x indexBits Ext3 squeezes")
        if a == 27: return ("12 Core: packed-claim folds (5 cells)", "")
        if a == 28: return ("13 Core: WHIR param prep", "")
        if a == 29: return ("14 BOUNDARY core->SpongefishWhirVerify (DELEGATECALL ABI encode/decode incl. hints copy)", None)
        if a == 50: return ("20 Core: WHIR accept check", "")
        if a == 51: return ("21 BOUNDARY core->PoseidonPublicInputsHash", None)
        if a == 52: return ("23 BOUNDARY core->Plonky2GateEvaluatorExt3 (wires+constants ABI copy)", None)
        if a == 53: return ("27 Core: gate terminal equality (eq(tau,point)*gateEval, inline)", "")
        if a == 54: return ("29 tails", "")
    if fr == "O":
        if 1000 <= a < 1200:
            s = (a - 1000) % 10
            if s == 0: return ("08 Outer coupled sumcheck rounds", "transcript commit per round (11 keccaks)")
            if s == 1: return ("08 Outer coupled sumcheck rounds", "round-poly evaluation (log deg5 + gate deg10, library Ext3 ops)")
            return ("08 Outer coupled sumcheck rounds", "glue")
        if a in (60, 63): return ("08 Outer coupled sumcheck rounds", "glue")
        if a == 70: return ("09 Norm/logUp terminal", "eq(tau, point)")
        if a == 71: return ("09 Norm/logUp terminal", "subgroup evaluation")
        if a == 72: return ("09 Norm/logUp terminal", "per-routed-wire denominators/norms/adjugates/accumulate (80 wires)")
        if a in (73, 77): return ("09 Norm/logUp terminal", "combine + xi*PI + eq check")
        if a in (74, 75, 76): return ("09 Norm/logUp terminal", "PI aggregation (binding loop + eq rows)")
    if fr == "W":
        if a == 200: return ("15 WHIR: parameter validation + transcript init", "validateParameters")
        if a in (201, 202): return ("15 WHIR: parameter validation + transcript init", "initTranscript + state alloc")
        if a == 210: return ("16 WHIR: initial roots/OOD", "3 roots + OOD squeezes/answers")
        if a == 211: return ("16 WHIR: initial claims + RLC", "6 evaluation claims absorb + mask check")
        if a == 212: return ("16 WHIR: initial claims + RLC", "cross-commitment OOD matrix")
        if a == 213: return ("16 WHIR: initial claims + RLC", "vector/constraint RLC geometric challenges")
        if a in (214, 215): return ("16 WHIR: initial claims + RLC", "theSum accumulation")
        if a in (203, 204): return ("17 WHIR: initial sumcheck (4 rounds)", "")
        if 300 <= a < 400:
            r = (a - 300) // 20; s = (a - 300) % 20
            g = f"18 WHIR: folding round {r}"
            if s in (0, 1, 2): return (g, "root read + OOD squeeze/answers")
            if s == 3: return (g, "PoW check")
            if s == 4: return (g, "challenge indices (1 keccak per index byte + sort)")
            if s == 5: return (g, "vec prefix + leaf row hashing")
            if s == 6: return (g, "in-domain eval points (glPow per query)")
            if s == 7: return (g, "Merkle authentication")
            if s == 8: return (g, "glue")
            if s == 9: return (g, "sumcheck (4 rounds)")
            if s == 10: return (g, "glue")
        if 450 <= a < 480:
            s = a % 10
            if s == 0: return ("18 WHIR: folding round 0", "Merkle authentication")
            if s == 1: return ("18 WHIR: folding round 0", "vec prefix + leaf row hashing" if b != 306 else "glue")
        if 420 <= a <= 424:
            # which round? decided by caller via context; use the 'ctx' trick below
            return ("18 WHIR: folding round ?", {420: "constraint values: eq weights", 421: "constraint values: RLC challenge",
                                                422: "constraint values: in-domain dot products (+OOD) into theSum",
                                                423: "constraint values: store round constraints", 424: "glue"}[a])
        if a == 500: return ("19 WHIR: final round", "read final polynomial")
        if a == 501: return ("19 WHIR: final round", "PoW check")
        if a == 502: return ("19 WHIR: final round", "challenge indices")
        if a == 503: return ("19 WHIR: final round", "eq weights")
        if a == 504: return ("19 WHIR: final round", "in-domain eval points (glPow)")
        if a == 505: return ("19 WHIR: final round", "vec prefix + leaf row hashing")
        if a == 506: return ("19 WHIR: final round", "Merkle authentication")
        if a in (507, 508): return ("19 WHIR: final round", "final-vector openings per query (reduceWithPowers + Ext3 row dot)")
        if a == 205: return ("19 WHIR: final sumcheck", "")
        if a in (206, 520): return ("19 WHIR: final claim", "foldEval")
        if a == 521: return ("19 WHIR: final claim", "Ext3 inverse + mul")
        if a == 522: return ("19 WHIR: final claim", "subtract round constraints (mleEvaluateUnivariate per OOD/in-domain point)")
        if a == 523: return ("19 WHIR: final claim", "eq(evalPoint_i, r) x2 + expectedRlc")
        if a == 524: return ("19 WHIR: final claim", "eq check")
        if a == 207: return ("19 WHIR: EOF checks", "")
    if fr == "PH": return ("22 Public-input Poseidon hash (hash_no_pad)", "")
    if fr == "G":
        if a == 600 or (a >= 2000 and (a - 2010) % 10 == 4): return ("24 Gate terminal: non-Poseidon gates + filters", "glue")
        s = (a - 2010) % 10; r = (a - 2010) // 10
        if s == 0: return ("24 Gate terminal: non-Poseidon gates + filters", "selector filters")
        if s == 1 and b == a + 2: return ("25 BOUNDARY gate evaluator->PoseidonGateExt3 (wires ABI copy)", None)
        if s in (1, 2): return ("24 Gate terminal: non-Poseidon gates + filters", f"row {r}: unfiltered eval + alpha reduce")
        if s == 3: return ("24 Gate terminal: non-Poseidon gates + filters", "filter*reduced accumulate")
    if fr == "PS":
        return ("26 Gate terminal: Poseidon gate (123 constraints)", {700: "constants load + allocs", 701: "swap/delta", 702: "first 4 full rounds",
                                                                     703: "partial constant layer + MDS partial init", 704: "22 partial rounds",
                                                                     705: "second 4 full rounds", 706: "output constraints", 707: "alpha-reduce 123"}[a])
    if fr == "GT": return ("28 Gate terminal equality (eq(tau,point)*gateEval)", "canonical checks" if a == 800 else "eq + mul + compare")
    return ("99 unclassified", f"{fr} {a}->{b}")

CALLEE = {12: "C", 25: "O", 29: "W", 51: "PH", 52: "G"}

def summarize(prof):
    groups = OrderedDict()
    totals = {fr: lst[0]["gas"] for fr, lst in prof.frame_totals.items()}
    total = totals["P"] if "P" in totals else totals["C"]
    cur_round = None
    # map callee frame entry/exit positions for boundary computation
    for s in prof.spans:
        fr, a, b, gas = s["frame"], s["a"], s["b"], s["gas"]
        if fr == "W" and 300 <= a < 400: cur_round = (a - 300) // 20
        g, sub = group_of(fr, a, b)
        if g.startswith("18 WHIR: folding round ?"): g = f"18 WHIR: folding round {cur_round}"
        if sub is None:  # boundary span: subtract the callee frame total
            callee = CALLEE.get(a) if fr in ("C", "P") else "PS"
            gas = gas - totals[callee]
            sub = ""
        groups.setdefault(g, OrderedDict())
        groups[g][sub] = groups[g].get(sub, 0) + gas
    return total, groups

def main():
    timing = parse(sys.argv[1])
    for name in ("test_production_verifyCompact", "test_max_verifyCompact", "test_small_verifyCompact"):
        if name not in timing: continue
        prof = Profile(timing[name]["events"])
        total, groups = summarize(prof)
        print(f"==== {name}: corrected callee total {fmt(total)} gas ====")
        acc = 0
        for g in sorted(groups):
            gsum = sum(groups[g].values()); acc += gsum
            print(f"{gsum:>12,}  {100*gsum/total:5.2f}%  {g}")
            if len(groups[g]) > 1 or list(groups[g].keys())[0]:
                for sub, v in groups[g].items():
                    if sub: print(f"{v:>12,}  {100*v/total:5.2f}%      - {sub}")
        print(f"{acc:>12,}  sum of groups (check)")
        print()

if __name__ == "__main__":
    main()
