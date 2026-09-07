#!/usr/bin/env python3
"""Lean-free self-checks for fresh-source-audit.py.

Every test runs without a Lean toolchain: Lean/Git-touching methods are replaced by
subclass overrides, and synthetic toolchain/package trees are built under a
directory next to this file (never /private/tmp, which the runner refuses).
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import unittest

HERE = Path(__file__).resolve().parent
RUNNER = HERE / "fresh-source-audit.py"
sys.dont_write_bytecode = True
import importlib.util  # noqa: E402

spec = importlib.util.spec_from_file_location("fresh_source_audit", str(RUNNER))
fsa = importlib.util.module_from_spec(spec)
exec(compile(RUNNER.read_bytes(), str(RUNNER), "exec"), fsa.__dict__)

REAL_GUARD = fsa.AUDIT_DIR / "check-wire3.py"
if REAL_GUARD.is_file():
    guard = fsa.load_source_module(REAL_GUARD, "wire3_guard_for_tests")
    imports_of, parse_axioms = guard.imports_of, guard.parse_axioms
else:  # minimal stand-ins so the suite still runs on a host without the audit checkout
    import re

    def imports_of(source):
        return set(sum((line.split()[1:] for line in source.splitlines() if line.startswith("import ")), []))

    def parse_axioms(output, theorem):
        pattern = re.escape("'" + theorem + "'") + r" (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
        matches = list(re.finditer(pattern, output))
        fsa.require(len(matches) == 1, f"missing/ambiguous Lean axiom result: {theorem}")
        content = matches[0].group(1)
        return set() if not content or not content.strip() else {x.strip() for x in content.split(",")}


def make_toolchain(base):
    lib = base / "toolchain" / "lib" / "lean"
    for root in ("Init", "Std", "Lean", "Lake"):
        (lib / root).mkdir(parents=True)
        (lib / (root + ".olean")).write_bytes(b"olean")
        (lib / root / "Prelude.olean").write_bytes(b"olean")
    (lib / "libleanshared.dylib").write_bytes(b"")
    (base / "toolchain" / "bin").mkdir()
    (base / "toolchain" / "bin" / "lean").write_bytes(b"#!/bin/sh\nexit 1\n")
    return base / "toolchain"


def make_roots(base, layout):
    """layout: {package: {module: source text}} -> {package: root}"""
    roots = {}
    for package, modules in layout.items():
        root = base / "roots" / package
        root.mkdir(parents=True, exist_ok=True)
        for module, text in modules.items():
            path = root / fsa.module_relative_path(module, ".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        roots[package] = root
    return roots


class Base(unittest.TestCase):
    def setUp(self):
        (HERE / ".selftest").mkdir(exist_ok=True)
        self.base = Path(tempfile.mkdtemp(prefix="case.", dir=str(HERE / ".selftest")))
        self.addCleanup(shutil.rmtree, self.base, True)


class ArgumentTests(Base):
    def test_main_rejects_everything_but_run(self):
        for argv in ([], ["--help"], ["--run", "--run"], ["run"], ["--run", "extra"], ["--RUN"]):
            with self.assertRaises(fsa.AuditFailure):
                fsa.main(argv)

    def test_command_line_rejection_exits_2_without_output(self):
        before = set(fsa.OUTPUT_BASE.iterdir()) if fsa.OUTPUT_BASE.is_dir() else set()
        result = subprocess.run([sys.executable, "-B", str(RUNNER), "--dry-run"], stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("[fresh-source] FAIL: usage", result.stderr)
        after = set(fsa.OUTPUT_BASE.iterdir()) if fsa.OUTPUT_BASE.is_dir() else set()
        self.assertEqual(before, after)


class OutputDirectoryTests(Base):
    def test_output_directory_is_fresh_and_outside_tmp(self):
        out = fsa.create_output_directory(self.base / "share")
        self.assertTrue(out.name.startswith(fsa.OUTPUT_PREFIX) and len(out.name) > len(fsa.OUTPUT_PREFIX))
        self.assertEqual(list(out.iterdir()), [])
        self.assertNotIn("/private/tmp", str(out.resolve()))

    def test_refuses_temporary_bases(self):
        for base in ("/private/tmp/wire3-x", "/tmp/wire3-x", "/var/folders/xx/wire3-x"):
            with self.assertRaises(fsa.AuditFailure):
                fsa.create_output_directory(base)


class SearchPathTests(Base):
    def setUp(self):
        super().setUp()
        self.toolchain = make_toolchain(self.base)
        self.lib = self.toolchain / "lib" / "lean"
        self.out_lib = self.base / "out" / "lib"
        self.out_lib.mkdir(parents=True)
        self.roots = {"Audit", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "ImportGraph", "Cli"}

    def check(self):
        fsa.check_search_path(self.lib, self.out_lib, self.roots, protected_dirs=[self.base / "audit"])

    def test_clean_configuration_is_accepted(self):
        self.check()

    def test_refuses_existing_oleans_in_fresh_output(self):
        (self.out_lib / "Mathlib").mkdir()
        (self.out_lib / "Mathlib" / "Foo.olean").write_bytes(b"olean")
        with self.assertRaises(fsa.AuditFailure):
            self.check()

    def test_refuses_any_preexisting_entry_in_fresh_output(self):
        (self.out_lib / "note.txt").write_text("x")
        with self.assertRaises(fsa.AuditFailure):
            self.check()

    def test_refuses_non_toolchain_oleans_planted_in_toolchain_lib(self):
        (self.lib / "Mathlib").mkdir()
        with self.assertRaises(fsa.AuditFailure):
            self.check()
        shutil.rmtree(self.lib / "Mathlib")
        (self.lib / "Audit.olean").write_bytes(b"olean")
        with self.assertRaises(fsa.AuditFailure):
            self.check()

    def test_refuses_output_inside_audit_or_lake_directories(self):
        inside = self.base / "audit" / "fresh" / "lib"
        inside.mkdir(parents=True)
        with self.assertRaises(fsa.AuditFailure):
            fsa.check_search_path(self.lib, inside, self.roots, protected_dirs=[self.base / "audit"])
        lake = self.base / "elsewhere" / ".lake" / "build" / "lib"
        lake.mkdir(parents=True)
        with self.assertRaises(fsa.AuditFailure):
            fsa.check_search_path(self.lib, lake, self.roots)

    def test_environment_contains_only_toolchain_and_fresh_output(self):
        saved = {k: os.environ.pop(k, None) for k in ("LEAN_PATH", "LEAN_SRC_PATH", "LAKE_PKG_URL_MAP")}
        try:
            os.environ["LEAN_SRC_PATH"] = "/somewhere"
            with self.assertRaises(fsa.AuditFailure):
                fsa.lean_environment(self.lib, self.out_lib, self.toolchain / "bin")
            del os.environ["LEAN_SRC_PATH"]
            os.environ["LEAN_PATH"] = str(self.base / "existing" / ".lake" / "build" / "lib")
            with self.assertRaises(fsa.AuditFailure):
                fsa.lean_environment(self.lib, self.out_lib, self.toolchain / "bin")
            del os.environ["LEAN_PATH"]
            env = fsa.lean_environment(self.lib, self.out_lib, self.toolchain / "bin")
        finally:
            for key, value in saved.items():
                if value is not None:
                    os.environ[key] = value
        self.assertEqual(set(env), {"PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"})
        self.assertEqual(env["LEAN_ABORT_ON_PANIC"], "1")
        self.assertEqual(env["LEAN_PATH"].split(os.pathsep), [str(self.lib), str(self.out_lib)])
        self.assertNotIn(".lake", env["LEAN_PATH"])


class GraphTests(Base):
    LAYOUT = {
        "audit": {"Audit": "import Audit.Wire3.A\nimport Audit.Wire3.B\n",
                  "Audit.Wire3.A": "import Lean\nimport Mathlib.X\n-- import Audit.Wire3.Ghost\n",
                  "Audit.Wire3.B": "/- import Audit.Wire3.Ghost -/\nimport Audit.Wire3.A\nimport Std\n"},
        "mathlib": {"Mathlib.X": "import Batteries.Y\nimport Init.Core\n", "Mathlib.Unused": "import Lean\n"},
        "batteries": {"Batteries.Y": "prelude\nimport Init.Prelude\n"},
        "Cli": {},
    }

    def test_closure_packages_and_toolchain_split(self):
        roots = make_roots(self.base, self.LAYOUT)
        graph, direct = fsa.discover_graph(roots, imports_of)
        self.assertEqual(set(graph), {"Audit", "Audit.Wire3.A", "Audit.Wire3.B", "Mathlib.X", "Batteries.Y"})
        self.assertEqual({m: i["package"] for m, i in graph.items()},
                         {"Audit": "audit", "Audit.Wire3.A": "audit", "Audit.Wire3.B": "audit",
                          "Mathlib.X": "mathlib", "Batteries.Y": "batteries"})
        self.assertEqual(graph["Audit.Wire3.A"]["imports"], ["Mathlib.X"])
        self.assertEqual(graph["Audit.Wire3.A"]["toolchain_imports"], ["Lean"])
        self.assertEqual(direct, ["Init.Core", "Init.Prelude", "Lean", "Std"])
        self.assertTrue(graph["Batteries.Y"]["prelude"] and not graph["Mathlib.X"]["prelude"])
        order = fsa.topological_order(graph)
        self.assertLess(order.index("Mathlib.X"), order.index("Audit.Wire3.A"))
        self.assertLess(order.index("Audit.Wire3.A"), order.index("Audit.Wire3.B"))
        self.assertEqual(order[-1], "Audit")

    def test_ambiguous_missing_and_symlinked_sources_fail(self):
        roots = make_roots(self.base, self.LAYOUT)
        (roots["batteries"] / "Mathlib").mkdir()
        (roots["batteries"] / "Mathlib" / "X.lean").write_text("import Lean\n")
        with self.assertRaisesRegex(fsa.AuditFailure, "resolves to 2"):
            fsa.discover_graph(roots, imports_of)
        (roots["batteries"] / "Mathlib" / "X.lean").unlink()
        (roots["mathlib"] / "Mathlib" / "X.lean").unlink()
        with self.assertRaisesRegex(fsa.AuditFailure, "resolves to 0"):
            fsa.discover_graph(roots, imports_of)
        os.symlink(roots["mathlib"] / "Mathlib" / "Unused.lean", roots["mathlib"] / "Mathlib" / "X.lean")
        with self.assertRaisesRegex(fsa.AuditFailure, "regular file"):
            fsa.discover_graph(roots, imports_of)

    def test_cycle_is_rejected(self):
        graph = {"A": {"imports": ["B"]}, "B": {"imports": ["A"]}}
        with self.assertRaisesRegex(fsa.AuditFailure, "cycle"):
            fsa.topological_order(graph)

    def test_invalid_module_names(self):
        for name in ("", "A..B", "A.", ".A", "A/B", "A-B"):
            with self.assertRaises(fsa.AuditFailure):
                fsa.module_relative_path(name, ".lean")

    def test_include_str_components(self):
        text = ('javascript := include_str ".." / ".." / ".lake" / "build" / "js" / "x.js"\n'
                'def t := include_str "a.txt"\n')
        self.assertEqual(fsa.parse_include_str_paths(text),
                         [["..", "..", ".lake", "build", "js", "x.js"], ["a.txt"]])


class SchedulerTests(Base):
    GRAPH = {"A": {"imports": []}, "B": {"imports": ["A"]}, "C": {"imports": ["A"]},
             "D": {"imports": ["B", "C"]}, "E": {"imports": []}, "F": {"imports": ["E", "D"]}}

    def test_dependency_order_and_concurrency_bound(self):
        order = fsa.topological_order(self.GRAPH)
        lock, active, peak, done, starts = threading.Lock(), [0], [0], set(), {}

        def work(module):
            with lock:
                for dep in self.GRAPH[module]["imports"]:
                    self.assertIn(dep, done)
                active[0] += 1
                peak[0] = max(peak[0], active[0])
                starts[module] = time.monotonic()
            time.sleep(0.02)
            with lock:
                active[0] -= 1
                done.add(module)
            return module.lower()

        results, errors = fsa.schedule(self.GRAPH, order, work, workers=2)
        self.assertEqual(errors, [])
        self.assertEqual(results, {m: m.lower() for m in self.GRAPH})
        self.assertLessEqual(peak[0], 2)
        self.assertGreaterEqual(peak[0], 2)

    def test_failure_stops_dependents_and_is_reported(self):
        order = fsa.topological_order(self.GRAPH)
        ran = []

        def work(module):
            ran.append(module)
            if module == "B":
                raise fsa.AuditFailure("boom")
            return True

        results, errors = fsa.schedule(self.GRAPH, order, work, workers=1)
        self.assertEqual(errors, ["B: boom"])
        self.assertNotIn("D", ran)
        self.assertNotIn("F", ran)
        self.assertNotIn("B", results)


class OutputParsingTests(Base):
    def test_compile_output_checks(self):
        self.assertEqual(fsa.check_compile_output("M", 0, ""), 0)
        self.assertEqual(fsa.check_compile_output("M", 0, "x.lean:3:1: warning: unused variable\n"), 1)
        with self.assertRaisesRegex(fsa.AuditFailure, "exited 1"):
            fsa.check_compile_output("M", 1, "")
        with self.assertRaisesRegex(fsa.AuditFailure, "error"):
            fsa.check_compile_output("M", 0, "x.lean:3:1: error: unknown identifier\n")
        with self.assertRaisesRegex(fsa.AuditFailure, "admitted"):
            fsa.check_compile_output("M", 0, "x.lean:3:1: warning: declaration uses 'sorry'\n")

    def test_dependency_output_must_match_graph_and_search_path(self):
        toolchain = self.base / "tc"
        out = self.base / "out"
        (toolchain / "Lean").mkdir(parents=True)
        (out / "Mathlib").mkdir(parents=True)
        info = {"imports": ["Mathlib.X"], "toolchain_imports": ["Lean"], "prelude": False}
        good = f"{toolchain}/Init.olean\n{toolchain}/Lean.olean\n{out}/Mathlib/X.olean\n"
        fsa.check_dependency_output("M", info, good, toolchain, out)
        stale = good.replace(f"{out}/Mathlib/X.olean", f"{self.base}/.lake/build/lib/Mathlib/X.olean")
        with self.assertRaisesRegex(fsa.AuditFailure, "differs from source graph"):
            fsa.check_dependency_output("M", info, stale, toolchain, out)
        with self.assertRaisesRegex(fsa.AuditFailure, "differs from source graph"):
            fsa.check_dependency_output("M", info, good + f"{out}/Mathlib/Y.olean\n", toolchain, out)
        with self.assertRaisesRegex(fsa.AuditFailure, "differs from source graph"):
            fsa.check_dependency_output("M", info, f"{toolchain}/Lean.olean\n", toolchain, out)

    def test_probe_output_parsing(self):
        names = ["Audit.Wire3.T.a", "Audit.Wire3.T.b"]
        good = ("Audit.Wire3.T.a : 0 < 1\n'Audit.Wire3.T.a' does not depend on any axioms\n"
                "Audit.Wire3.T.b (n : Nat) : n = n\n'Audit.Wire3.T.b' depends on axioms: [propext, Quot.sound]\n")
        self.assertEqual(fsa.parse_probe_output(good, names, parse_axioms),
                         {"Audit.Wire3.T.a": [], "Audit.Wire3.T.b": ["Quot.sound", "propext"]})
        with self.assertRaisesRegex(fsa.AuditFailure, "unapproved"):
            fsa.parse_probe_output(good.replace("propext", "myAxiom"), names, parse_axioms)
        with self.assertRaisesRegex(fsa.AuditFailure, "admitted"):
            fsa.parse_probe_output(good.replace("propext", "sorryAx"), names, parse_axioms)
        with self.assertRaisesRegex(fsa.AuditFailure, "missing #check"):
            fsa.parse_probe_output(good.replace("Audit.Wire3.T.b (n : Nat) : n = n\n", ""), names, parse_axioms)
        with self.assertRaises(Exception):
            fsa.parse_probe_output(good.replace("'Audit.Wire3.T.b' depends", "'Audit.Wire3.T.bb' depends"),
                                   names, parse_axioms)
        with self.assertRaisesRegex(fsa.AuditFailure, "error"):
            fsa.parse_probe_output(good + "P.lean:4:2: error: audit target is not a theorem\n", names, parse_axioms)


class FakeGuards:
    class GuardFailure(Exception):
        pass


class Scripted(fsa.FreshSourceAudit):
    """Driver with every Lean/Git-touching step replaced; each hook can be told to fail."""

    def __init__(self, base, **kwargs):
        audit = base / "audit"
        (audit / ".lake" / "packages").mkdir(parents=True)
        for package, relative in fsa.PACKAGE_DIRS.items():
            (audit / relative).mkdir(parents=True, exist_ok=True)
        (audit / "wire3-manifest.json").write_text('{"models": []}\n')
        (audit / "lean-toolchain").write_text("leanprover/lean4:v4.10.0\n")
        toolchain = make_toolchain(base)
        super().__init__(audit_dir=audit, toolchain=toolchain, output_base=base / "share",
                         workers=2, script_path=RUNNER, log=self.lines.append)
        self.fail_at = kwargs.get("fail_at")
        self.guard_calls = []
        self.records_value = [{"module": "Audit.Wire3.A", "theorems": ["Audit.Wire3.A.t1", "Audit.Wire3.A.t2"]}]

    lines = None

    def maybe_fail(self, step):
        if self.fail_at == step:
            raise fsa.AuditFailure(f"{step} rejected")

    def load_guards(self):
        self.maybe_fail("load_guards")
        self.guard = self.deps = FakeGuards()

    def source_guard(self, label):
        self.guard_calls.append(label)
        self.maybe_fail(label + "_guard")
        return self.records_value, {"packages": 7, "tracked_files": 5601, "tracked_bytes": 64398270}

    def check_toolchain(self):
        self.maybe_fail("toolchain")
        self.receipt["lean_commit"] = fsa.LEAN_GITHASH
        self.receipt["lean_binary_sha256"] = "0" * 64
        self.deps_supported = True

    def build_graph(self):
        self.maybe_fail("graph")
        graph = {"Audit": {"package": "audit", "imports": ["Audit.Wire3.A"], "toolchain_imports": [],
                           "source": str(self.audit_dir / "Audit.lean"), "source_sha256": "1" * 64},
                 "Audit.Wire3.A": {"package": "audit", "imports": [], "toolchain_imports": ["Lean"],
                                   "source": str(self.audit_dir / "Audit" / "Wire3" / "A.lean"), "source_sha256": "2" * 64}}
        self.receipt["module_counts"] = {p: 0 for p in fsa.REPORTED_PACKAGES}
        self.receipt["module_counts"]["audit"] = 2
        self.receipt["direct_toolchain_imports"] = ["Lean"]
        fsa.write_json(self.out / "graph.json", {"modules": graph})
        return graph, ["Audit.Wire3.A", "Audit"]

    def js_assets(self, graph):
        self.maybe_fail("js")
        return [{"path": "x.js", "sha256": "3" * 64, "size": 1, "modules": ["Audit.Wire3.A"]}]

    def compile_all(self, graph, order):
        self.maybe_fail("compile")
        for module in order:
            self.receipt["compiled_modules"][module] = {"package": "audit", "deps_check": "lean --deps"}
        return dict(self.receipt["compiled_modules"])

    def recheck_artifacts(self, graph):
        self.maybe_fail("recheck")

    def probe_all(self, records, graph):
        self.maybe_fail("probe")
        if self.fail_at == "manifest-drift":
            (self.audit_dir / "wire3-manifest.json").write_text('{"models": [], "drift": 1}\n')
        for record in records:
            for name in record["theorems"]:
                self.receipt["theorem_axioms"][name] = ["propext"]
        return sum(len(r["theorems"]) for r in records)


def scripted(base, **kwargs):
    Scripted.lines = []
    driver = Scripted(base, **kwargs)
    driver.lines = Scripted.lines
    driver.log = driver.lines.append
    return driver


class DriverTests(Base):
    def receipt(self, driver):
        path = Path(driver.receipt["output_directory"]) / "receipt.json"
        self.assertTrue(path.is_file())
        document = json.loads(path.read_text())
        self.assertEqual(list(document), sorted(fsa.RECEIPT_KEYS))
        self.assertEqual(document["claim"], fsa.CLAIM)
        self.assertEqual(document["max_concurrent_lean_processes"], 2)
        self.assertIsInstance(document["elapsed_seconds"], float)
        return document

    def test_pass_path_prints_documented_summary(self):
        driver = scripted(self.base)
        self.assertTrue(driver.run())
        document = self.receipt(driver)
        self.assertEqual(document["status"], "PASS")
        self.assertEqual(document["errors"], [])
        self.assertEqual(document["pre_source_guard"], document["post_source_guard"])
        self.assertEqual(driver.guard_calls, ["pre", "post"])
        self.assertEqual(sorted(document["theorem_axioms"]), ["Audit.Wire3.A.t1", "Audit.Wire3.A.t2"])
        self.assertEqual(document["script_sha256"], fsa.sha256_file(RUNNER))
        self.assertIn("[fresh-source] PASS: 2 fresh source modules; 2 current named theorem checks", driver.lines)
        self.assertTrue(Path(document["output_directory"]).name.startswith(fsa.OUTPUT_PREFIX))
        self.assertTrue((Path(document["output_directory"]) / "graph.json").is_file())

    def test_receipt_written_on_toolchain_failure_and_post_guard_still_runs(self):
        driver = scripted(self.base, fail_at="toolchain")
        self.assertFalse(driver.run())
        document = self.receipt(driver)
        self.assertEqual(document["status"], "FAIL")
        self.assertEqual(document["errors"], ["AuditFailure: toolchain rejected"])
        self.assertEqual(driver.guard_calls, ["pre", "post"])
        self.assertIsNotNone(document["post_source_guard"])
        self.assertEqual(document["theorem_axioms"], {})

    def test_pre_guard_failure_propagates(self):
        driver = scripted(self.base, fail_at="pre_guard")
        self.assertFalse(driver.run())
        document = self.receipt(driver)
        self.assertEqual(document["status"], "FAIL")
        self.assertIn("AuditFailure: pre_guard rejected", document["errors"])
        self.assertIsNone(document["pre_source_guard"])
        self.assertEqual(driver.guard_calls, ["pre", "post"])
        self.assertEqual(document["compiled_modules"], {})

    def test_post_guard_failure_fails_an_otherwise_passing_run(self):
        driver = scripted(self.base, fail_at="post_guard")
        self.assertFalse(driver.run())
        document = self.receipt(driver)
        self.assertEqual(document["status"], "FAIL")
        self.assertEqual(document["errors"], ["AuditFailure: post_guard rejected"])
        self.assertEqual(len(document["theorem_axioms"]), 2)

    def test_manifest_change_during_run_is_detected(self):
        driver = scripted(self.base, fail_at="manifest-drift")
        self.assertFalse(driver.run())
        document = self.receipt(driver)
        self.assertEqual(document["status"], "FAIL")
        self.assertEqual(document["errors"], ["AuditFailure: manifest changed during run"])

    def test_compile_and_probe_failures_are_recorded(self):
        for step in ("graph", "js", "compile", "recheck", "probe"):
            driver = scripted(self.base / step, fail_at=step)
            self.assertFalse(driver.run(), step)
            document = self.receipt(driver)
            self.assertEqual(document["status"], "FAIL")
            self.assertEqual(document["errors"], [f"AuditFailure: {step} rejected"])
            self.assertEqual(driver.guard_calls, ["pre", "post"], step)

    def test_search_path_guard_runs_inside_driver(self):
        driver = scripted(self.base)
        (driver.toolchain_lib / "Mathlib").mkdir()
        self.assertFalse(driver.run())
        document = self.receipt(driver)
        self.assertEqual(document["status"], "FAIL")
        self.assertIn("non-toolchain module material inside toolchain lib", document["errors"][0])
        self.assertEqual(document["compiled_modules"], {})

    def test_default_configuration_matches_documented_constants(self):
        driver = fsa.FreshSourceAudit(script_path=RUNNER, log=lambda *_: None)
        self.assertEqual(driver.lean, fsa.TOOLCHAIN / "bin" / "lean")
        self.assertEqual(driver.toolchain_lib, fsa.TOOLCHAIN / "lib" / "lean")
        self.assertEqual(driver.workers, 4)
        self.assertEqual(str(fsa.OUTPUT_BASE), str(Path.home() / ".local" / "share" / "wire3-fresh-source"))
        self.assertEqual(set(fsa.PACKAGE_OPTIONS), set(fsa.PACKAGE_DIRS))
        self.assertEqual(fsa.PACKAGE_OPTIONS["mathlib"],
                         ["-Dpp.unicode.fun=true", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"])
        self.assertEqual(fsa.KERNEL_AXIOMS, frozenset({"propext", "Classical.choice", "Quot.sound"}))

    def test_probe_source_shape(self):
        text = fsa.probe_source("Audit.Wire3.A", ["Audit.Wire3.A.t"])
        self.assertTrue(text.startswith("import Lean\nimport Audit.Wire3.A\nrun_cmd do\n"))
        self.assertIn("| .thmInfo _ => pure ()", text)
        self.assertIn("#check Audit.Wire3.A.t\n#print axioms Audit.Wire3.A.t\n", text)


if __name__ == "__main__":
    unittest.main(verbosity=1)
