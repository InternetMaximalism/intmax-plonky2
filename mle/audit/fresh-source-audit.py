#!/usr/bin/env python3
"""Fresh Lean source regeneration audit for the wire-v3 Lean models.

Rewrite of the lost `/private/tmp/wire3-fresh-source-runner.iXATos/fresh_audit.py`
(documented in mle/audit/REPORT.md). It recompiles EVERY non-toolchain Lean module
reachable from Audit.lean (the audit root plus the pinned packages under
.lake/packages) from source into a fresh, empty output directory, with a search
path that contains only the Lean toolchain core library and that fresh output, and
then re-checks every named theorem of wire3-manifest.json using only that output.

Claim: "Lean source regenerated with fixed JS data; not implementation/refinement/PCS
soundness". Trust boundary: Lean toolchain/core artifacts, Python/Git, the existing
ProofWidgets JS bytes (hashed, not regenerated), fixed metaprograms, and a
non-adversarial filesystem. No network, no Lake, no release download, and no write
into existing build artifacts. See README.md / DESIGN.md next to this file.
"""
import concurrent.futures
import hashlib
import heapq
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import threading
import time

# The audit root is the directory holding this script (mle/audit), never a hard-coded path.
AUDIT_DIR = Path(__file__).resolve().parent
TOOLCHAIN = Path("/Users/andropov/.elan/toolchains/leanprover--lean4---v4.10.0")
TOOLCHAIN_NAME = "leanprover/lean4:v4.10.0"
LEAN_GITHASH = "c375e19f6b656fcd594cdca3a38b8578634df8cd"
OUTPUT_BASE = Path.home() / ".local" / "share" / "wire3-fresh-source"
OUTPUT_PREFIX = "wire3-fresh-source-build."
FORBIDDEN_OUTPUT_PREFIXES = ("/private/tmp", "/tmp", "/private/var/folders", "/var/folders")
MAX_WORKERS = 4
ENTRY_MODULE = "Audit"
CLAIM = "Lean source regenerated with fixed JS data; not implementation/refinement/PCS soundness"
JAVASCRIPT_PROVENANCE = "existing bytes, not source-generated here; fixed by pre/post SHA256"
# Modules shipped inside the toolchain core library are trusted, never recompiled.
TOOLCHAIN_ROOTS = ("Init", "Std", "Lean", "Lake")
# Source roots: the audit root and the seven pinned packages. Every package's
# `lean_lib` uses the package directory as its source root.
PACKAGE_DIRS = {
    "audit": Path("."),
    "mathlib": Path(".lake/packages/mathlib"),
    "batteries": Path(".lake/packages/batteries"),
    "aesop": Path(".lake/packages/aesop"),
    "Qq": Path(".lake/packages/Qq"),
    "proofwidgets": Path(".lake/packages/proofwidgets"),
    "importGraph": Path(".lake/packages/importGraph"),
    "Cli": Path(".lake/packages/Cli"),
}
# Reviewed `leanOptions` of each pinned lakefile (source-integrity checked by
# check-proof-dependencies.py). Lake passes exactly these -D flags to `lean`.
PACKAGE_OPTIONS = {
    "audit": [],
    "mathlib": ["-Dpp.unicode.fun=true", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"],
    "batteries": ["-Dlinter.missingDocs=true"],
    "aesop": [],
    "Qq": [],
    "proofwidgets": [],
    "importGraph": [],
    "Cli": [],
}
REPORTED_PACKAGES = ("audit", "mathlib", "batteries", "aesop", "Qq", "proofwidgets", "importGraph")
RECEIPT_KEYS = (
    "claim", "status", "script_sha256", "audit_manifest_sha256", "lean_commit",
    "trusted_toolchain", "lean_binary_sha256", "max_concurrent_lean_processes",
    "package_options", "pre_source_guard", "post_source_guard", "javascript_provenance",
    "output_directory", "module_counts", "js_references", "compiled_modules",
    "theorem_axioms", "direct_toolchain_imports", "elapsed_seconds", "errors",
)
KERNEL_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
COMPILE_TIMEOUT = 3600
PROBE_TIMEOUT = 1800
ERROR_LINE = re.compile(r"^(?:[^\n:]*:\d+:\d+: )?error(?::| )", re.MULTILINE)
INCLUDE_STR = re.compile(r"\binclude_str\s+((?:\"[^\"\n]*\"\s*/\s*)*\"[^\"\n]*\")")


class AuditFailure(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditFailure(message)


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    path = Path(path)
    require(not path.is_symlink() and path.is_file(), f"missing/non-regular or symlink file: {path}")
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        while True:
            chunk = stream.read(1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
    return digest.hexdigest()


def load_source_module(path, name):
    """Compile the reviewed source bytes explicitly; never read a cached .pyc."""
    path = Path(path)
    require(not path.is_symlink() and path.is_file(), f"missing helper source: {path}")
    spec = importlib.util.spec_from_file_location(name, str(path))
    module = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    return module


def unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def module_relative_path(module, suffix):
    parts = module.split(".")
    require(all(parts) and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", p) for p in parts),
            f"invalid module name: {module}")
    return Path(*parts).with_suffix(suffix)


def is_toolchain_module(module):
    return module.split(".", 1)[0] in TOOLCHAIN_ROOTS


def without_lean_comments(source):
    """Blank out `--` line comments and nested `/- -/` block comments, preserving
    newlines and the contents of double-quoted string literals (which include_str
    paths are). Conservative scanner, not a Lean parser; the guard's own
    `without_comments_and_strings` cannot be used here because it also blanks strings."""
    output, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                output.append("  ")
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                output.append("  ")
                index += 2
                continue
            output.append("\n" if char == "\n" else " ")
        elif quoted:
            output.append(char)
            if char == "\\" and index + 1 < len(source):
                output.append(source[index + 1])
                index += 2
                continue
            if char == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            output.append("  ")
            index += 2
            continue
        elif pair == "--":
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            output.append(" " * (end - index))
            index = end
            continue
        else:
            quoted = char == '"'
            output.append(char)
        index += 1
    require(depth == 0 and not quoted, "unterminated Lean comment/string while scanning include_str")
    return "".join(output)


def parse_include_str_paths(source_text):
    """Literal `include_str "a" / "b"` components; resolved relative to the source directory."""
    references = []
    for literal in INCLUDE_STR.findall(source_text):
        parts = re.findall(r'"([^"\n]*)"', literal)
        require(parts and all(parts), "empty include_str path component")
        references.append(parts)
    return references


def create_output_directory(base=OUTPUT_BASE):
    base = Path(base)
    resolved_base = base.resolve()
    require(not str(resolved_base).startswith(FORBIDDEN_OUTPUT_PREFIXES),
            f"output base must not live in a temporary directory: {resolved_base}")
    base.mkdir(parents=True, exist_ok=True)
    require(not base.is_symlink() and base.is_dir(), f"output base is not a directory: {base}")
    out = Path(tempfile.mkdtemp(prefix=OUTPUT_PREFIX, dir=str(base)))
    require(out.is_dir() and not any(out.iterdir()), f"fresh output directory is not empty: {out}")
    return out


def check_search_path(toolchain_lib, out_lib, non_toolchain_roots, protected_dirs=()):
    """Refuse any configuration whose search path could resolve an existing olean."""
    toolchain_lib = Path(toolchain_lib)
    out_lib = Path(out_lib)
    require(not toolchain_lib.is_symlink() and toolchain_lib.is_dir(), f"toolchain lib missing: {toolchain_lib}")
    for root in ("Init", "Std", "Lean"):
        require((toolchain_lib / root).is_dir() and (toolchain_lib / (root + ".olean")).is_file(),
                f"toolchain core root missing: {root}")
    for entry in toolchain_lib.iterdir():
        stem = entry.name.split(".", 1)[0]
        if entry.is_dir() or entry.suffix in (".olean", ".ilean"):
            require(stem in TOOLCHAIN_ROOTS, f"non-toolchain module material inside toolchain lib: {entry}")
        require(stem not in non_toolchain_roots, f"non-toolchain root inside toolchain lib: {entry}")
    require(not out_lib.is_symlink() and out_lib.is_dir(), f"fresh output lib missing: {out_lib}")
    require(not any(out_lib.iterdir()), f"fresh output lib is not empty: {out_lib}")
    resolved_out = out_lib.resolve()
    require(not str(resolved_out).startswith(FORBIDDEN_OUTPUT_PREFIXES),
            f"fresh output must not live in a temporary directory: {resolved_out}")
    for protected in (toolchain_lib, *protected_dirs):
        protected = Path(protected).resolve()
        require(resolved_out != protected and protected not in resolved_out.parents,
                f"fresh output must not live inside {protected}")
    require(".lake" not in resolved_out.parts, f"fresh output must not be a Lake build directory: {resolved_out}")


def lean_environment(toolchain_lib, out_lib, toolchain_bin):
    """Minimal child environment: LEAN_PATH is exactly toolchain lib + fresh output."""
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LAKE_PKG_URL_MAP"):
        require(not os.environ.get(name), f"external dependency override is forbidden: {name}")
    entries = [str(Path(toolchain_lib)), str(Path(out_lib))]
    require(all(os.pathsep not in e for e in entries), "search path entry contains a separator")
    # LEAN_ABORT_ON_PANIC makes a Lean-level panic during elaboration a hard failure.
    return {"PATH": str(toolchain_bin), "HOME": os.environ.get("HOME", "/"),
            "LEAN_PATH": os.pathsep.join(entries), "LEAN_ABORT_ON_PANIC": "1"}


def run_process(args, env, cwd, timeout):
    try:
        result = subprocess.run(list(map(str, args)), cwd=str(cwd), env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=timeout)
    except (OSError, subprocess.SubprocessError) as error:
        raise AuditFailure(f"process failed: {args!r}: {error}") from error
    return result.returncode, result.stdout.decode("utf-8", errors="replace")


def discover_graph(roots, imports_of, entry=ENTRY_MODULE):
    """Import closure of `entry` over the non-toolchain source roots.

    roots: {package: source root directory}. Returns (graph, direct_toolchain_imports).
    Every module must resolve to exactly one regular file under exactly one root.
    """
    graph = {}
    direct_toolchain = set()
    pending = [entry]
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        relative = module_relative_path(module, ".lean")
        found = []
        for package, root in roots.items():
            candidate = Path(root) / relative
            if candidate.exists() or candidate.is_symlink():
                require(not candidate.is_symlink() and candidate.is_file(), f"module source is not a regular file: {candidate}")
                found.append((package, candidate))
        require(len(found) == 1, f"module resolves to {len(found)} source roots (need exactly 1): {module} {found}")
        package, path = found[0]
        data = path.read_bytes()
        try:
            text = data.decode("utf-8")
        except UnicodeError as error:
            raise AuditFailure(f"non-UTF-8 Lean source: {path}") from error
        clean = imports_of(text)
        toolchain_imports = sorted(i for i in clean if is_toolchain_module(i))
        other = sorted(i for i in clean if not is_toolchain_module(i))
        direct_toolchain.update(toolchain_imports)
        prelude = re.search(r"^\s*prelude\s*$", text, flags=re.MULTILINE) is not None
        graph[module] = {"package": package, "source": str(path), "source_sha256": sha256_bytes(data),
                         "imports": other, "toolchain_imports": toolchain_imports, "prelude": prelude}
        pending.extend(other)
    return graph, sorted(direct_toolchain)


def topological_order(graph):
    """Deterministic dependency-first order; fails on cycles."""
    indegree = {m: len(info["imports"]) for m, info in graph.items()}
    dependents = {m: [] for m in graph}
    for module, info in graph.items():
        for dep in info["imports"]:
            require(dep in graph, f"import outside the discovered graph: {module} -> {dep}")
            dependents[dep].append(module)
    ready = sorted(m for m, d in indegree.items() if d == 0)
    order = []
    while ready:
        module = ready.pop(0)
        order.append(module)
        for dep in sorted(dependents[module]):
            indegree[dep] -= 1
            if indegree[dep] == 0:
                ready.append(dep)
        ready.sort()
    require(len(order) == len(graph), "import cycle among non-toolchain modules")
    return order


def critical_priority(graph, order):
    """Number of transitive dependents per module (bitset), used to pick ready work."""
    index = {m: i for i, m in enumerate(order)}
    dependents = {m: [] for m in graph}
    for module, info in graph.items():
        for dep in info["imports"]:
            dependents[dep].append(module)
    mask = {}
    for module in reversed(order):
        bits = 0
        for dep in dependents[module]:
            bits |= (1 << index[dep]) | mask[dep]
        mask[module] = bits
    return {m: bin(bits).count("1") for m, bits in mask.items()}


def schedule(graph, order, work, workers=MAX_WORKERS):
    """Run `work(module)` for every module, dependencies first, at most `workers` at once.

    Stops submitting on the first failure, waits for in-flight work, and returns
    (results, errors). Results are keyed by module; errors are strings.
    """
    priority = critical_priority(graph, order)
    position = {m: i for i, m in enumerate(order)}
    remaining = {m: len(graph[m]["imports"]) for m in graph}
    dependents = {m: [] for m in graph}
    for module, info in graph.items():
        for dep in info["imports"]:
            dependents[dep].append(module)
    ready = [(-priority[m], position[m], m) for m in graph if remaining[m] == 0]
    heapq.heapify(ready)
    results, errors, in_flight = {}, [], {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        while (ready or in_flight) and not errors:
            while ready and len(in_flight) < workers:
                _, _, module = heapq.heappop(ready)
                in_flight[pool.submit(work, module)] = module
            done, _ = concurrent.futures.wait(list(in_flight), return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                module = in_flight.pop(future)
                try:
                    results[module] = future.result()
                except Exception as error:  # noqa: BLE001 - every failure must be recorded
                    errors.append(f"{module}: {error}")
                    continue
                for dep in dependents[module]:
                    remaining[dep] -= 1
                    if remaining[dep] == 0:
                        heapq.heappush(ready, (-priority[dep], position[dep], dep))
        for future in list(in_flight):
            module = in_flight.pop(future)
            try:
                results[module] = future.result()
            except Exception as error:  # noqa: BLE001
                errors.append(f"{module}: {error}")
    if not errors:
        missing = sorted(set(graph) - set(results))
        require(not missing, f"scheduler left modules uncompiled: {missing[:5]}")
    return results, errors


def check_compile_output(module, returncode, output):
    require(returncode == 0, f"lean exited {returncode} compiling {module}:\n{output[-4000:]}")
    require(ERROR_LINE.search(output) is None, f"lean reported an error compiling {module}:\n{output[-4000:]}")
    require("declaration uses 'sorry'" not in output and "sorryAx" not in output,
            f"admitted declaration while compiling {module}")
    require("PANIC" not in output, f"lean panicked while compiling {module}:\n{output[-4000:]}")
    return len(re.findall(r": warning:", output))


def expected_dependency_paths(info, toolchain_lib, out_lib):
    expected = set()
    if not info.get("prelude"):
        expected.add((Path(toolchain_lib) / "Init.olean").resolve())
    for dep in info["toolchain_imports"]:
        expected.add((Path(toolchain_lib) / module_relative_path(dep, ".olean")).resolve())
    for dep in info["imports"]:
        expected.add((Path(out_lib) / module_relative_path(dep, ".olean")).resolve())
    return expected


def check_dependency_output(module, info, output, toolchain_lib, out_lib):
    """`lean --deps` must resolve exactly the graph's imports, and only to the two search roots."""
    printed = {Path(line.strip()).resolve() for line in output.splitlines() if line.strip()}
    expected = expected_dependency_paths(info, toolchain_lib, out_lib)
    require(printed == expected,
            f"import resolution differs from source graph for {module}: "
            f"unexpected={sorted(map(str, printed - expected))} missing={sorted(map(str, expected - printed))}")
    allowed = (Path(toolchain_lib).resolve(), Path(out_lib).resolve())
    for path in printed:
        require(any(root == path or root in path.parents for root in allowed),
                f"import resolved outside the fresh search path: {module} -> {path}")


def parse_probe_output(output, theorems, parse_axioms):
    require("sorryAx" not in output and "declaration uses 'sorry'" not in output, "admitted dependency")
    require(ERROR_LINE.search(output) is None, f"probe reported an error:\n{output[-4000:]}")
    axioms = {}
    for name in theorems:
        # `#check` prints `name : type` or `name (binders) : type`; the name is the whole first token.
        require(re.search(r"^" + re.escape(name) + r"(?=\s)", output, flags=re.MULTILINE) is not None,
                f"missing #check result: {name}")
        try:
            axioms[name] = sorted(parse_axioms(output, name))
        except Exception as error:  # noqa: BLE001 - the guard's own failure type is not ours
            raise AuditFailure(f"axiom result rejected for {name}: {error}") from error
        require(set(axioms[name]) <= KERNEL_AXIOMS, f"unapproved axioms in {name}: {axioms[name]}")
    return axioms


def probe_source(module, theorems):
    lines = ["import Lean", "import " + module]
    for name in theorems:
        lines.extend([
            "run_cmd do",
            "  let info ← Lean.getConstInfo `" + name,
            "  match info with",
            "  | .thmInfo _ => pure ()",
            '  | _ => throwError "audit target is not a theorem"',
            "#check " + name, "#print axioms " + name,
        ])
    return "\n".join(lines) + "\n"


def write_json(path, document):
    path = Path(path)
    temp = path.with_name(path.name + ".tmp")
    temp.write_text(json.dumps(document, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temp, path)


class FreshSourceAudit:
    """One audit run. Methods that touch Lean/Git are overridable for Lean-free self-checks."""

    def __init__(self, audit_dir=AUDIT_DIR, toolchain=TOOLCHAIN, output_base=OUTPUT_BASE,
                 workers=MAX_WORKERS, script_path=None, log=print):
        self.audit_dir = Path(audit_dir)
        self.toolchain = Path(toolchain)
        self.lean = self.toolchain / "bin" / "lean"
        self.toolchain_lib = self.toolchain / "lib" / "lean"
        self.output_base = Path(output_base)
        self.workers = workers
        self.script_path = Path(script_path or __file__)
        self.log = log
        self.guard = None
        self.deps = None
        self.records = None
        self.out = None
        self.out_lib = None
        self.env = None
        self.deps_supported = False
        self.lock = threading.Lock()
        self.receipt = {key: None for key in RECEIPT_KEYS}
        self.receipt.update(claim=CLAIM, status="RUNNING", max_concurrent_lean_processes=workers,
                            package_options=dict(PACKAGE_OPTIONS), javascript_provenance=JAVASCRIPT_PROVENANCE,
                            trusted_toolchain=str(self.toolchain), errors=[], compiled_modules={},
                            theorem_axioms={}, js_references=[], module_counts={}, direct_toolchain_imports=[])

    # ---- guards ---------------------------------------------------------------------------
    def manifest_path(self):
        return self.audit_dir / "wire3-manifest.json"

    def load_guards(self):
        self.guard = load_source_module(self.audit_dir / "check-wire3.py", "wire3_guard")
        self.deps = load_source_module(self.audit_dir / "check-proof-dependencies.py", "wire3_proof_dependencies")
        require(Path(self.guard.ROOT / self.guard.PROJECT).resolve() == self.audit_dir.resolve(),
                "check-wire3.py does not describe the configured audit directory")

    def source_guard(self, label):
        """validate_manifest + constant tables + pinned dependency integrity."""
        manifest = json.loads(self.manifest_path().read_text(encoding="utf-8"), object_pairs_hook=unique_json_object)
        failures = (self.guard.GuardFailure, self.deps.GuardFailure)
        try:
            records = self.guard.validate_manifest(self.guard.ROOT, manifest)
            self.guard.check_constant_tables(self.guard.ROOT)
            result = self.deps.check_project(self.audit_dir)
        except failures as error:
            raise AuditFailure(f"{label} source guard failed: {error}") from error
        summary = {"packages": result["packages"], "tracked_files": result["tracked_files"],
                   "tracked_bytes": result["tracked_bytes"]}
        self.log(f"[fresh-source] {label} source guard PASS: {summary}")
        return records, summary

    # ---- toolchain -----------------------------------------------------------------------
    def check_toolchain(self):
        require(not self.lean.is_symlink() and self.lean.is_file(), f"lean binary missing: {self.lean}")
        require((self.audit_dir / "lean-toolchain").read_text(encoding="utf-8").strip() == TOOLCHAIN_NAME,
                "unexpected lean-toolchain")
        self.receipt["lean_binary_sha256"] = sha256_file(self.lean)
        env = {"PATH": str(self.toolchain / "bin"), "HOME": os.environ.get("HOME", "/")}
        code, githash = run_process([self.lean, "--githash"], env, self.audit_dir, 60)
        require(code == 0 and githash.strip() == LEAN_GITHASH, f"unexpected lean --githash: {githash.strip()!r}")
        self.receipt["lean_commit"] = githash.strip()
        code, libdir = run_process([self.lean, "--print-libdir"], env, self.audit_dir, 60)
        require(code == 0 and Path(libdir.strip()).resolve() == self.toolchain_lib.resolve(),
                f"lean --print-libdir is not the trusted toolchain core lib: {libdir.strip()!r}")
        code, usage = run_process([self.lean, "--help"], env, self.audit_dir, 60)
        self.deps_supported = "--deps" in usage
        # A PASS must always mean `lean --deps` confirmed every module's import resolution;
        # the pinned Lean 4.10 binary provides the flag, so its absence is a failure.
        require(self.deps_supported, "pinned lean must support --deps for import-resolution confirmation")
        self.log(f"[fresh-source] lean {LEAN_GITHASH} at {self.lean}; --deps available")

    # ---- graph ---------------------------------------------------------------------------
    def roots(self):
        result = {}
        for package, relative in PACKAGE_DIRS.items():
            root = (self.audit_dir / relative).resolve()
            require(not root.is_symlink() and root.is_dir(), f"package source root missing: {package} {root}")
            result[package] = root
        return result

    def build_graph(self):
        graph, direct = discover_graph(self.roots(), self.guard.imports_of)
        order = topological_order(graph)
        counts = {package: 0 for package in REPORTED_PACKAGES}
        for info in graph.values():
            counts[info["package"]] = counts.get(info["package"], 0) + 1
        self.receipt["module_counts"] = counts
        self.receipt["direct_toolchain_imports"] = direct
        write_json(self.out / "graph.json", {"entry": ENTRY_MODULE, "order": order, "modules": graph})
        self.log(f"[fresh-source] {len(graph)} non-toolchain modules: {counts}; "
                 f"{len(direct)} direct toolchain imports")
        return graph, order

    # ---- JS assets -----------------------------------------------------------------------
    def js_assets(self, graph):
        assets = {}
        for module in sorted(graph):
            info = graph[module]
            source = Path(info["source"])
            # Strip comments first (keeping string literals) so a commented-out
            # include_str is not treated as an asset.
            for parts in parse_include_str_paths(without_lean_comments(source.read_text(encoding="utf-8"))):
                target = source.parent.joinpath(*parts).resolve()
                package_root = self.roots()[info["package"]]
                require(package_root == target or package_root in target.parents,
                        f"include_str escapes its package: {module} -> {target}")
                assets.setdefault(str(target), []).append(module)
        references = []
        for path in sorted(assets):
            references.append({"path": path, "sha256": sha256_file(path), "size": Path(path).stat().st_size,
                               "modules": sorted(assets[path])})
        return references

    # ---- compilation ---------------------------------------------------------------------
    def compile_module(self, module, info):
        package = info["package"]
        root = self.roots()[package]
        source = Path(info["source"])
        olean = self.out_lib / module_relative_path(module, ".olean")
        ilean = self.out_lib / module_relative_path(module, ".ilean")
        require(not olean.exists() and not ilean.exists(), f"fresh output already contains {module}")
        olean.parent.mkdir(parents=True, exist_ok=True)
        require(sha256_file(source) == info["source_sha256"], f"source changed before compile: {module}")
        started = time.monotonic()
        deps_check = "parser-only"
        if self.deps_supported:
            code, output = run_process([self.lean, "--deps", source], self.env, root, 300)
            require(code == 0, f"lean --deps failed for {module}:\n{output[-2000:]}")
            check_dependency_output(module, info, output, self.toolchain_lib, self.out_lib)
            deps_check = "lean --deps"
        for dep in info["imports"]:
            require((self.out_lib / module_relative_path(dep, ".olean")).is_file(),
                    f"dependency olean missing in fresh output: {module} -> {dep}")
        command = [self.lean, *PACKAGE_OPTIONS[package], "-o", olean, "-i", ilean, f"--root={root}", source]
        code, output = run_process(command, self.env, root, COMPILE_TIMEOUT)
        warnings = check_compile_output(module, code, output)
        require(olean.is_file() and ilean.is_file(), f"lean produced no fresh artifacts for {module}")
        result = {"package": package, "source": str(source), "source_sha256": info["source_sha256"],
                  "olean_sha256": sha256_file(olean), "ilean_sha256": sha256_file(ilean),
                  "imports": info["imports"], "toolchain_imports": info["toolchain_imports"],
                  "options": PACKAGE_OPTIONS[package], "deps_check": deps_check,
                  "warnings": warnings, "seconds": round(time.monotonic() - started, 3)}
        with self.lock:
            self.receipt["compiled_modules"][module] = result
            count = len(self.receipt["compiled_modules"])
        if count % 50 == 0 or count == 1:
            self.log(f"[fresh-source] compiled {count} modules (latest {module}, {result['seconds']}s)")
        return result

    def compile_all(self, graph, order):
        results, errors = schedule(graph, order, lambda m: self.compile_module(m, graph[m]), self.workers)
        require(not errors, "compilation failed: " + " | ".join(errors))
        return results

    def recheck_artifacts(self, graph):
        compiled = self.receipt["compiled_modules"]
        require(set(compiled) == set(graph), "compiled module set differs from graph")
        for module, result in compiled.items():
            require(sha256_file(result["source"]) == result["source_sha256"], f"source changed after compile: {module}")
            require(sha256_file(self.out_lib / module_relative_path(module, ".olean")) == result["olean_sha256"],
                    f"fresh olean changed after compile: {module}")
        stray = [p for p in self.out_lib.rglob("*") if p.is_file() and p.suffix not in (".olean", ".ilean")]
        require(not stray, f"unexpected files in fresh output lib: {stray[:5]}")
        oleans = sorted(str(p.relative_to(self.out_lib)) for p in self.out_lib.rglob("*.olean"))
        expected = sorted(str(module_relative_path(m, ".olean")) for m in graph)
        require(oleans == expected, "fresh olean inventory differs from graph")

    # ---- theorem probes ------------------------------------------------------------------
    def probe_record(self, index, record):
        probe_dir = self.out / "probes"
        probe = probe_dir / f"Axioms{index}.lean"
        probe.write_text(probe_source(record["module"], record["theorems"]), encoding="utf-8")
        code, output = run_process([self.lean, probe], self.env, probe_dir, PROBE_TIMEOUT)
        require(code == 0, f"probe {record['module']} exited {code}:\n{output[-4000:]}")
        axioms = parse_probe_output(output, record["theorems"], self.guard.parse_axioms)
        with self.lock:
            self.receipt["theorem_axioms"].update(axioms)
        return axioms

    def probe_all(self, records, graph):
        (self.out / "probes").mkdir()
        for record in records:
            require(record["module"] in graph, f"manifest model not in compiled graph: {record['module']}")
        errors = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=self.workers) as pool:
            futures = {pool.submit(self.probe_record, i, r): r["module"] for i, r in enumerate(records)}
            for future in concurrent.futures.as_completed(futures):
                try:
                    future.result()
                except Exception as error:  # noqa: BLE001
                    errors.append(f"{futures[future]}: {error}")
        require(not errors, "theorem probes failed: " + " | ".join(sorted(errors)))
        total = sum(len(r["theorems"]) for r in records)
        require(len(self.receipt["theorem_axioms"]) == total, "theorem result count differs from manifest")
        return total

    # ---- driver --------------------------------------------------------------------------
    def write_receipt(self):
        if self.out is not None:
            write_json(self.out / "receipt.json", self.receipt)

    def run(self):
        started = time.monotonic()
        receipt = self.receipt
        receipt["script_sha256"] = sha256_file(self.script_path)
        receipt["audit_manifest_sha256"] = sha256_file(self.manifest_path())
        self.out = create_output_directory(self.output_base)
        receipt["output_directory"] = str(self.out)
        self.log(f"[fresh-source] output directory: {self.out}")
        self.write_receipt()
        module_total = theorem_total = 0
        try:
            self.load_guards()
            self.records, receipt["pre_source_guard"] = self.source_guard("pre")
            self.check_toolchain()
            self.out_lib = self.out / "lib"
            self.out_lib.mkdir()
            check_search_path(self.toolchain_lib, self.out_lib, set(PACKAGE_DIRS) | {"Audit", "Mathlib", "Batteries",
                              "Aesop", "ProofWidgets", "ImportGraph"}, protected_dirs=[self.audit_dir])
            self.env = lean_environment(self.toolchain_lib, self.out_lib, self.toolchain / "bin")
            graph, order = self.build_graph()
            receipt["js_references"] = self.js_assets(graph)
            self.log(f"[fresh-source] {len(receipt['js_references'])} include_str assets fixed by SHA256")
            self.write_receipt()
            self.compile_all(graph, order)
            after = self.js_assets(graph)
            require(after == receipt["js_references"], "include_str asset bytes changed during compilation")
            self.recheck_artifacts(graph)
            module_total = len(graph)
            self.write_receipt()
            theorem_total = self.probe_all(self.records, graph)
            receipt["status"] = "PASS"
        except Exception as error:  # noqa: BLE001 - every failure must land in the receipt
            receipt["errors"].append(f"{type(error).__name__}: {error}")
            receipt["status"] = "FAIL"
        finally:
            try:
                if self.guard is not None and self.deps is not None:
                    _, receipt["post_source_guard"] = self.source_guard("post")
                    require(receipt["post_source_guard"] == receipt["pre_source_guard"], "source guard summary drifted")
                else:
                    raise AuditFailure("post source guard skipped: guards never loaded")
                require(sha256_file(self.manifest_path()) == receipt["audit_manifest_sha256"], "manifest changed during run")
                require(sha256_file(self.script_path) == receipt["script_sha256"], "runner script changed during run")
            except Exception as error:  # noqa: BLE001
                receipt["errors"].append(f"{type(error).__name__}: {error}")
                receipt["status"] = "FAIL"
            if receipt["status"] != "PASS" or receipt["errors"]:
                receipt["status"] = "FAIL"
            receipt["elapsed_seconds"] = round(time.monotonic() - started, 3)
            require_keys = set(receipt) == set(RECEIPT_KEYS)
            self.write_receipt()
        if not require_keys:
            receipt["status"] = "FAIL"
            receipt["errors"].append("receipt key set drifted")
            self.write_receipt()
        if receipt["status"] == "PASS":
            self.log(f"[fresh-source] PASS: {module_total} fresh source modules; "
                     f"{theorem_total} current named theorem checks")
            self.log(f"[fresh-source] NOT PROVED: implementation refinement, PCS/FS soundness; "
                     f"JS assets are fixed existing bytes; toolchain/core is trusted")
        else:
            self.log(f"[fresh-source] FAIL: {receipt['errors']}")
        self.log(f"[fresh-source] receipt: {self.out / 'receipt.json'}")
        return receipt["status"] == "PASS"


def main(argv):
    require(argv == ["--run"], "usage: fresh-source-audit.py --run (no other arguments are accepted)")
    return 0 if FreshSourceAudit().run() else 1


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except AuditFailure as error:
        print(f"[fresh-source] FAIL: {error}", file=sys.stderr)
        sys.exit(2)
