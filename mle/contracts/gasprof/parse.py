#!/usr/bin/env python3
"""Parse forge -vv output of the instrumented GasProfile tests into per-phase gas tables.

usage: parse.py timing.log [counting.log]
"""
import re, sys, statistics
from collections import OrderedDict, defaultdict

MASK160 = (1 << 160) - 1
ENTRIES = {"P": 10, "C": 20, "O": 60, "W": 200, "G": 600, "PS": 700, "GT": 800, "PH": 850}
EXITS = {"P": 9005, "C": 55, "O": 64, "W": 208, "G": 601, "PS": 708, "GT": 802, "PH": 851}

def frame_of(i):
    if i in (10, 11, 12, 13) or 110 <= i <= 127 or 9000 <= i <= 9010: return "P"
    if 20 <= i <= 55: return "C"
    if 60 <= i <= 77 or 1000 <= i <= 1199: return "O"
    if 200 <= i <= 599: return "W"
    if 600 <= i <= 699 or 2000 <= i <= 2999: return "G"
    if 700 <= i <= 708: return "PS"
    if 800 <= i <= 802: return "GT"
    if 850 <= i <= 851: return "PH"
    raise ValueError(i)

def parse(path):
    tests = OrderedDict()
    cur = None
    for line in open(path):
        m = re.match(r"\[(PASS|FAIL)[^\]]*\] (\w+)\(\)", line)
        if m:
            cur = m.group(2); tests[cur] = {"events": [], "info": []}
            continue
        if cur is None: continue
        s = line.strip()
        if re.fullmatch(r"\d+", s):
            w = int(s)
            kind = w >> 248
            idv = (w >> 224) & 0xFFFFFF
            if kind == 1:
                tests[cur]["events"].append(("M", idv, (w >> 160) & 0xFFFFFFFFFFFFFFFF, w & MASK160))
            else:
                tests[cur]["events"].append(("K", kind, idv, (w >> 96) & ((1 << 128) - 1), w & ((1 << 96) - 1)))
        elif s and not s.startswith("Logs:") and not s.startswith("Suite") and not s.startswith("Ran"):
            tests[cur]["info"].append(s)
    return tests

def fmt(n):
    return f"{int(round(n)):,}"

LABELS = {
    ("P", 10, 9001): "P: entry -> calibration",
    ("P", 9003, 110): "P: chainid check",
    ("P", 110, 111): "P: _loadConfiguration: EXTCODECOPY config store",
    ("P", 111, 112): "P: _loadConfiguration: abi.decode(VerificationConfig)",
    ("P", 112, 11): "P: tail of _loadConfiguration",
    ("P", 11, 120): "P: call into compact decoder",
    ("P", 120, 121): "P: decode: magic/version/width/digest/PIs/roots",
    ("P", 121, 122): "P: decode: whirTranscript blob copy",
    ("P", 122, 123): "P: decode: whirHints blob copy (calldatacopy)",
    ("P", 123, 124): "P: decode: logProof rounds (Ext3 vectors)",
    ("P", 124, 125): "P: decode: logPreprocessed/logWitness/logNormInverse",
    ("P", 125, 126): "P: decode: gateProof rounds",
    ("P", 126, 127): "P: decode: gatePreprocessed/gateWitness + EOF check",
    ("P", 127, 12): "P: decoder return",
    ("P", 12, 13): "P: core.verify external call (ABI-encode proof+config, STATICCALL, callee, return)",
    ("P", 13, 9004): "P: after core.verify",
    ("C", 20, 21): "C: _requirePinnedConfiguration (abi.encode(config) + keccak)",
    ("C", 21, 22): "C: _requireCanonicalProof (shape checks)",
    ("C", 22, 30): "C: indexBits + call derive",
    ("C", 30, 31): "C: transcript: statement absorption (digest, PIs, metadata, config digest, WHIR ids, 2 roots)",
    ("C", 31, 32): "C: transcript: eta/beta/gamma squeeze + normInverse root + xi squeeze",
    ("C", 32, 33): "C: transcript: lambda/rho/kappa squeeze",
    ("C", 33, 34): "C: transcript: tau vector squeeze (degreeBits Ext3)",
    ("C", 34, 35): "C: transcript: gate alpha squeeze",
    ("C", 35, 36): "C: transcript: gate tau vector squeeze (degreeBits Ext3)",
    ("C", 36, 23): "C: derive return",
    ("C", 23, 24): "C: canonical limb copy of 5 terminal vectors (calldata->memory)",
    ("C", 24, 25): "C: VK/terminal structs + canonical copy of 2 sumcheck proofs",
    ("C", 25, 26): "C: OuterLogupExt3Verifier.verifyPrevalidated DELEGATECALL (incl. ABI encode/decode)",
    ("C", 26, 40): "C: -> absorb claims",
    ("C", 40, 41): "C: absorb 5 constituent claim vectors (+empty vec, 2 domains)",
    ("C", 41, 42): "C: squeeze 2 index points (2*indexBits Ext3)",
    ("C", 42, 27): "C: absorb return",
    ("C", 27, 28): "C: PackedClaimExt3 fold of 5 used cells (internal)",
    ("C", 28, 29): "C: WHIR param prep (config.whir copy, packed points, roots)",
    ("C", 29, 50): "C: SpongefishWhirVerify.verifyWhirProofBound DELEGATECALL (incl. ABI encode/decode)",
    ("C", 50, 51): "C: constants prefix copy",
    ("C", 51, 52): "C: PoseidonPublicInputsHash.hashNoPad DELEGATECALL",
    ("C", 52, 53): "C: Plonky2GateEvaluatorExt3.evalCombinedPrevalidated DELEGATECALL",
    ("C", 53, 54): "C: OuterLogupExt3Verifier.verifyGateTerminal DELEGATECALL",
    ("C", 54, 55): "C: tail",
    ("O", 60, 1000): "O: prologue (alloc points)",
    ("O", 63, 70): "O: -> terminal",
    ("O", 70, 71): "O: terminal: eq(tau, point)",
    ("O", 71, 72): "O: terminal: subgroup evaluation",
    ("O", 72, 73): "O: terminal: per-routed-wire denominators/norms/adjugates/logUp accumulate (80 wires)",
    ("O", 73, 74): "O: terminal: final combine",
    ("O", 74, 75): "O: -> PI binding",
    ("O", 75, 76): "O: terminal: PI binding loop",
    ("O", 76, 77): "O: terminal: PI eq-row evaluation",
    ("O", 77, 64): "O: terminal: xi*binding add + eq check + return",
    ("W", 200, 201): "W: _validateParameters",
    ("W", 201, 202): "W: initTranscript (3 absorbs) + VerifyState alloc",
    ("W", 202, 210): "W: -> phaseInitial",
    ("W", 210, 211): "W: initial: 3 roots + OOD point squeezes + OOD answers (absorbs)",
    ("W", 211, 212): "W: initial: 6 evaluation claims read/absorb + mask check",
    ("W", 212, 213): "W: initial: cross-commitment OOD matrix read",
    ("W", 213, 214): "W: initial: vector RLC + constraint RLC geometric challenges",
    ("W", 214, 215): "W: initial: theSum accumulation",
    ("W", 215, 203): "W: initial: return",
    ("W", 203, 204): "W: initial sumcheck (initialSumcheckRounds rounds)",
    ("W", 204, 300): "W: -> rounds",
    ("W", 500, 501): "W: final: read final vector",
    ("W", 501, 502): "W: final: PoW",
    ("W", 502, 503): "W: final: challenge indices (sort/dedup)",
    ("W", 503, 504): "W: final: eq weights",
    ("W", 504, 505): "W: final: eval points (glPow)",
    ("W", 505, 506): "W: final: vec prefix + leaf row hashing",
    ("W", 506, 507): "W: final: Merkle authentication",
    ("W", 507, 508): "W: final: per-query final-vector openings (reduceWithPowers + dotEqWithRow)",
    ("W", 508, 205): "W: final: return",
    ("W", 205, 206): "W: final sumcheck",
    ("W", 206, 520): "W: -> final claim",
    ("W", 520, 521): "W: finalClaim: foldEval of final vector",
    ("W", 521, 522): "W: finalClaim: Ext3 inverse + mul",
    ("W", 522, 523): "W: finalClaim: subtract round constraints (mleEvaluateUnivariate per OOD/in-domain point)",
    ("W", 523, 524): "W: finalClaim: eq(evalPoint, r) for 2 points + expectedRlc",
    ("W", 524, 207): "W: finalClaim: eq check + return",
    ("W", 207, 208): "W: EOF checks",
    ("W", 305, 450): "W: round 0 split: commitment 0: vec prefix + leaf row hashing",
    ("W", 450, 451): "W: round 0 split: commitment 0: Merkle authentication",
    ("W", 451, 460): "W: round 0 split: commitment 1: vec prefix + leaf row hashing",
    ("W", 460, 461): "W: round 0 split: commitment 1: Merkle authentication",
    ("W", 461, 470): "W: round 0 split: commitment 2: vec prefix + leaf row hashing",
    ("W", 470, 471): "W: round 0 split: commitment 2: Merkle authentication",
    ("W", 471, 306): "W: round 0 split: commitments done",
    ("W", 420, 421): "W: constraint values: eq weights (2^foldingFactor)",
    ("W", 421, 422): "W: constraint values: constraint RLC geometric challenge",
    ("W", 422, 423): "W: constraint values: OOD + in-domain dot products into theSum",
    ("W", 423, 424): "W: constraint values: store round constraints",
    ("G", 600, 610): "G: prologue",
    ("PS", 700, 701): "PS: Poseidon: load constants + allocate state/scratch/constraints",
    ("PS", 701, 702): "PS: Poseidon: swap/delta constraints",
    ("PS", 702, 703): "PS: Poseidon: first 4 full rounds (S-box + MDS)",
    ("PS", 703, 704): "PS: Poseidon: partial first constant layer + MDS partial init",
    ("PS", 704, 705): "PS: Poseidon: 22 partial rounds",
    ("PS", 705, 706): "PS: Poseidon: second 4 full rounds",
    ("PS", 706, 707): "PS: Poseidon: output constraints",
    ("PS", 707, 708): "PS: Poseidon: alpha-reduce 123 constraints",
    ("GT", 800, 801): "GT: canonical checks",
    ("GT", 801, 802): "GT: eq(tau, point) * gateEval + compare",
    ("PH", 850, 851): "PH: Poseidon hash_no_pad of public inputs",
}

def label(fr, a, b):
    key = (fr, a, b)
    if key in LABELS: return LABELS[key]
    if fr == "O" and 1000 <= a < 1200:
        r = (a - 1000) // 10; s = (a - 1000) % 10
        if s == 0 and b == a + 1: return f"O: round {r}: transcript commit (2 domains, idx, 2 Ext3 vecs, 6 squeezes)"
        if s == 1 and b == a + 1: return f"O: round {r}: evaluate log (deg 5) + gate (deg 10) round polys"
        if s == 2 and b == a + 8: return f"O: round {r}: loop tail"
        if s == 2 and b == 63: return f"O: round {r}: loop exit"
    if fr == "W" and 300 <= a < 400:
        r = (a - 300) // 20; s = (a - 300) % 20
        names = {0: "root read", 1: "OOD point squeeze", 2: "OOD answers absorb", 3: "PoW", 4: "challenge indices (squeeze+sort)",
                 5: "vec prefix + leaf row hashing", 6: "eval points (glPow)", 7: "Merkle authentication", 8: "-> constraint values", 9: "sumcheck (4 rounds)", 10: "loop tail"}
        if b == a + 1 or (s == 8 and b == 420) or (s == 10 and b == a + 10) or (s == 10 and b == 500):
            return f"W: round {r}: {names[s]}"
        if s == 6 and b == 420: return f"W: round {r}: -> constraint values (split)"
    if fr == "W" and a == 424:
        return "W: constraint values: return"
    if fr == "G" and 610 <= a < 700:
        r = (a - 610) // 10; s = (a - 610) % 10
        if s == 0 and b == a + 1: return f"G: gate row {r}: selector filter"
        if s == 1 and b == a + 9: return f"G: gate row {r}: filter zero -> skipped"
        if s == 1 and b == a + 1: return f"G: gate row {r}: evaluate unfiltered constraints"
        if s == 1 and b == a + 2: return f"G: gate row {r}: Poseidon DELEGATECALL (evalPoseidonReduced)"
        if s == 2 and b == a + 1: return f"G: gate row {r}: alpha reduce"
        if s == 3 and b == a + 1: return f"G: gate row {r}: filter*reduced accumulate"
        if s == 4 and b == a + 6: return f"G: gate row {r}: loop tail"
        if s == 4 and b == 601: return f"G: last row exit"
        if s == 1 and b == 601: return f"G: last row skipped exit"
    return f"{fr}: {a}->{b}"

class Profile:
    def __init__(self, events):
        self.events = events
        self.marks = [(k, e) for k, e in enumerate(events) if e[0] == "M"]
        self.counts = [(k, e) for k, e in enumerate(events) if e[0] == "K"]
        gas = {}
        for k, (_, i, fp, g) in self.marks:
            gas.setdefault(i, []).append((k, g))
        cal = []
        for a, b in ((9001, 9002), (9002, 9003), (9004, 9005)):
            if a in gas and b in gas:
                cal.append(gas[a][0][1] - gas[b][0][1])
        self.ovh = statistics.median(cal) if cal else 0
        self.cal = cal
        # positions of marks in mark-order (for overhead counting) and event-order (for count attribution)
        frames = defaultdict(list)
        for mi, (k, e) in enumerate(self.marks):
            frames[frame_of(e[1])].append(mi)
        self.spans = []  # dict entries
        for fr, mis in frames.items():
            for a, b in zip(mis, mis[1:]):
                ka, ea = self.marks[a]; kb, eb = self.marks[b]
                raw = ea[3] - eb[3]
                inside = b - a - 1
                self.spans.append(dict(frame=fr, a=ea[1], b=eb[1], raw=raw, gas=raw - (inside + 1) * self.ovh,
                                       ka=ka, kb=kb, mi=a, label=label(fr, ea[1], eb[1])))
        self.spans.sort(key=lambda s: s["ka"])
        self.frame_totals = {}
        for fr, mis in frames.items():
            starts = [mi for mi in mis if self.marks[mi][1][1] == ENTRIES[fr]]
            ends = [mi for mi in mis if self.marks[mi][1][1] == EXITS[fr]]
            for a, b in zip(starts, ends):
                ka, ea = self.marks[a]; kb, eb = self.marks[b]
                raw = ea[3] - eb[3]
                self.frame_totals.setdefault(fr, []).append(dict(raw=raw, gas=raw - (b - a) * self.ovh, ka=ka, kb=kb))

    def counts_between(self, ka, kb):
        """Aggregate counter events with event index in (ka, kb)."""
        agg = defaultdict(int)
        for k, e in self.counts:
            if ka < k < kb:
                _, kind, idv, a, b = e
                if kind == 2:
                    agg["keccak_n"] += a; agg["keccak_bytes"] += a * b
                    agg[f"keccak_site_{idv}_n"] += a; agg[f"keccak_site_{idv}_bytes"] += a * b
                elif kind == 3:
                    agg["ext3_full"] += a; agg[f"ext3_site_{idv}"] += a
                    if idv == 1: agg["lib_mul"] += a
                    if idv == 2: agg["lib_square"] += a
                    if idv == 3: agg["lib_inv"] += a
                elif kind == 4:
                    agg["ext3_scalar"] += a; agg[f"scalar_site_{idv}"] += a
                    if idv == 4: agg["lib_mulScalar"] += a
                elif kind == 5:
                    agg["base_mulmod"] += a
        return agg

def main():
    timing = parse(sys.argv[1])
    counting = parse(sys.argv[2]) if len(sys.argv) > 2 else {}
    for name, data in timing.items():
        if not any(e[0] == "M" for e in data["events"]): continue
        prof = Profile(data["events"])
        cprof = Profile(counting[name]["events"]) if name in counting else None
        print(f"=== {name} ===")
        for s in data["info"]: print("  " + s)
        print(f"  marks {len(prof.marks)}; probe overhead/mark {prof.ovh} (cal {prof.cal})")
        if cprof:
            # sanity: same mark sequence
            seqa = [e[1] for _, e in prof.marks]; seqb = [e[1] for _, e in cprof.marks]
            print(f"  counting run mark sequence identical: {seqa == seqb}")
            tot = cprof.counts_between(-1, len(cprof.events))
            print(f"  TOTAL keccak256 invocations {tot['keccak_n']:,} hashing {tot['keccak_bytes']:,} bytes; "
                  f"Ext3 full mul-equivalents {tot['ext3_full']:,} (library mul {tot['lib_mul']:,}, square {tot['lib_square']:,}, inv {tot['lib_inv']:,}); "
                  f"Ext3*scalar {tot['ext3_scalar']:,} (library mulScalar {tot['lib_mulScalar']:,}); base mulmod (glPow/inv/univariate) {tot['base_mulmod']:,}")
            for site, nm in ((1, "config digest"), (10, "TranscriptV2 absorbFrame"), (11, "TranscriptV2 vec frame"), (12, "TranscriptV2 squeeze"),
                             (30, "WHIR challenge-index bytes"), (31, "WHIR leaf row hash"), (32, "WHIR PoW"), (33, "Merkle node"),
                             (34, "Keccak256Chain absorb"), (35, "Keccak256Chain squeeze block"), (36, "Keccak256Chain squeezeByte"), (37, "ratchet")):
                n = tot.get(f"keccak_site_{site}_n", 0)
                if n: print(f"    keccak site {site:2d} {nm:28s}: {n:7,} invocations, {tot[f'keccak_site_{site}_bytes']:9,} bytes")
        print("  -- frame totals (corrected) --")
        for fr, lst in prof.frame_totals.items():
            for t in lst:
                extra = ""
                if cprof:
                    ct = [x for x in cprof.frame_totals.get(fr, [])]
                    if ct:
                        c = cprof.counts_between(ct[lst.index(t)]["ka"], ct[lst.index(t)]["kb"])
                        extra = f"  keccak {c['keccak_n']:,}/{c['keccak_bytes']:,}B ext3 {c['ext3_full']:,} scalar {c['ext3_scalar']:,}"
                print(f"  {fr:3s} raw {fmt(t['raw']):>12s} corrected {fmt(t['gas']):>12s}{extra}")
        print("  -- spans --")
        for i, s in enumerate(prof.spans):
            extra = ""
            if cprof:
                cs = cprof.spans[i]
                assert (cs["frame"], cs["a"], cs["b"]) == (s["frame"], s["a"], s["b"]), (cs, s)
                c = cprof.counts_between(cs["ka"], cs["kb"])
                if c["keccak_n"] or c["ext3_full"] or c["ext3_scalar"]:
                    extra = f"   [keccak {c['keccak_n']:,}/{c['keccak_bytes']:,}B ext3 {c['ext3_full']:,} sc {c['ext3_scalar']:,}]"
            print(f"  {s['frame']:3s} {s['a']:>5d}->{s['b']:<5d} {fmt(s['gas']):>12s}  {s['label']}{extra}")
        print()

if __name__ == "__main__":
    main()
