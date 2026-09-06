#!/usr/bin/env python3
"""Isolated guard unit tests; never mutate implementation or construct proofs."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location("wire3guard", Path(__file__).with_name("check-wire3.py"))
G = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(G)
REAL_COMMAND = G.command


class GuardTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="wire3-guard-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.paths = set()
        self.manifest = {"schema_version": 1, "audit_base_commit": "a" * 40,
                         "claim": G.CLAIM, "files": [], "models": []}
        for path in sorted(G.REQUIRED):
            self.add_file(path, "tooling", "tooling\n")
        self.replace_file(G.PROJECT + "/lakefile.lean", "@[default_target]\nlean_lib Audit\n")
        self.replace_file(G.PROJECT + "/lean-toolchain", "leanprover/lean4:v4.10.0\n")
        self.replace_file(G.PROJECT + "/Audit.lean", "import Audit.Wire3.Example\n")
        self.model = "Audit.Wire3.Example"
        self.modules_patch = patch.object(G, "REQUIRED_MODULES", {self.model})
        self.modules_patch.start()
        self.addCleanup(self.modules_patch.stop)
        self.model_path = G.MODEL_PREFIX + "Example.lean"
        self.add_file(self.model_path, "current-model",
                      "import Std\nnamespace Audit.Wire3.Example\ntheorem checked : True := True.intro\nend Audit.Wire3.Example\n")
        self.add_file("mle/src/example.rs", "implementation", "// source\n")
        self.add_file("plonky2/src/other.rs", "implementation", "// explicitly not modeled\n")
        self.manifest["models"].append({"module": self.model,
            "theorems": [self.model + ".checked"], "sources": ["mle/src/example.rs"],
            "scope": "partial control-flow model, no refinement theorem"})
        self.command_patch = patch.object(G, "command", side_effect=self.command)
        self.command_patch.start()
        self.addCleanup(self.command_patch.stop)

    def add_file(self, path, kind, content):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(content)
        self.paths.add(path)
        self.manifest["files"].append({"path": path, "kind": kind,
                                      "sha256": hashlib.sha256(file.read_bytes()).hexdigest()})

    def replace_file(self, path, content):
        (self.root / path).write_text(content)
        for record in self.manifest["files"]:
            if record["path"] == path:
                record["sha256"] = hashlib.sha256(content.encode()).hexdigest()

    def command(self, args, cwd=None, capture=True):
        if args[:3] == ["git", "merge-base", "--is-ancestor"]:
            return ""
        if args == ["git", "ls-files", "--cached", "--others", "--exclude-standard"]:
            return "\n".join(sorted(self.paths)) + "\n"
        raise AssertionError(args)

    def validate(self, manifest=None):
        return G.validate_manifest(self.root, self.manifest if manifest is None else manifest)

    def test_complete_inventory_and_partial_claim(self):
        self.assertEqual(len(self.validate()), 1)

    def test_unmodeled_source_cannot_disappear(self):
        self.manifest["files"] = [f for f in self.manifest["files"] if f["path"] != "plonky2/src/other.rs"]
        with self.assertRaisesRegex(G.GuardFailure, "source inventory incomplete"):
            self.validate()

    def test_new_source_requires_inventory(self):
        self.paths.add("mle/src/new.rs")
        with self.assertRaisesRegex(G.GuardFailure, "source inventory incomplete"):
            self.validate()

    def test_claim_cannot_be_relabeled_complete(self):
        self.manifest["claim"] = "everything-proved"
        with self.assertRaisesRegex(G.GuardFailure, "must not claim full"):
            self.validate()

    def test_source_drift_fails(self):
        (self.root / "mle/src/example.rs").write_text("// changed\n")
        with self.assertRaisesRegex(G.GuardFailure, "reviewed file changed"):
            self.validate()

    def test_empty_and_omitted_theorems_fail(self):
        for names in ([], [self.model + ".wrong"]):
            m = copy.deepcopy(self.manifest)
            m["models"][0]["theorems"] = names
            with self.assertRaises(G.GuardFailure):
                self.validate(m)

    def test_missing_model_fails(self):
        self.manifest["models"] = []
        with self.assertRaisesRegex(G.GuardFailure, "missing/extra"):
            self.validate()

    def test_baseline_module_cannot_be_removed(self):
        with patch.object(G, "REQUIRED_MODULES", {self.model, "Audit.Wire3.Required"}):
            with self.assertRaisesRegex(G.GuardFailure, "baseline current model missing"):
                self.validate()

    def test_root_cannot_hide_unaudited_declarations(self):
        self.replace_file(G.PROJECT + "/Audit.lean", "import Audit.Wire3.Example\ntheorem hidden : True := True.intro\n")
        with self.assertRaisesRegex(G.GuardFailure, "root must contain only imports"):
            self.validate()

    def test_missing_import_fails(self):
        self.replace_file(G.PROJECT + "/Audit.lean", "import Std\n")
        with self.assertRaisesRegex(G.GuardFailure, "unbuilt current"):
            self.validate()

    def test_historical_import_fails(self):
        self.replace_file(self.model_path, "import Audit.Poly\n")
        with self.assertRaisesRegex(G.GuardFailure, "historical/unreviewed import"):
            self.validate()

    def test_admission_and_non_kernel_evaluation_fail(self):
        for keyword in ("sorry", "admit", "axiom", "native_decide"):
            self.replace_file(self.model_path, "import Std\n" + keyword + "\n")
            with self.assertRaisesRegex(G.GuardFailure, "admission/non-kernel"):
                self.validate()

    def test_missing_guard_hash_fails(self):
        self.manifest["files"] = [f for f in self.manifest["files"] if f["path"] != G.PROJECT + "/check-wire3.py"]
        with self.assertRaisesRegex(G.GuardFailure, "unhashed required"):
            self.validate()

    def test_missing_mapping_or_scope_fails(self):
        for field, value in (("sources", []), ("sources", ["unreviewed.sol"]), ("scope", "")):
            m = copy.deepcopy(self.manifest)
            m["models"][0][field] = value
            with self.assertRaises(G.GuardFailure):
                self.validate(m)

    def test_wrong_default_root_fails(self):
        self.replace_file(G.PROJECT + "/lakefile.lean", "@[default_target]\nlean_lib HistoricalAudit\n")
        with self.assertRaisesRegex(G.GuardFailure, "sole default"):
            self.validate()

    def test_bad_paths_and_duplicate_entries_fail(self):
        for path in ("../secret", "/tmp/secret", "mle//source.rs", "mle/../source.rs"):
            with self.assertRaises(G.GuardFailure):
                G.checked_path(self.root, path)
        self.manifest["files"].append(copy.deepcopy(self.manifest["files"][0]))
        with self.assertRaisesRegex(G.GuardFailure, "duplicate/self"):
            self.validate()

    def test_duplicate_json_keys_fail(self):
        with self.assertRaisesRegex(G.GuardFailure, "duplicate JSON"):
            json.loads('{"claim":1,"claim":2}', object_pairs_hook=G.unique_json_object)

    def test_axiom_allowlist(self):
        name = self.model + ".checked"
        self.assertEqual(G.parse_axioms(f"'{name}' does not depend on any axioms", name), set())
        self.assertEqual(G.parse_axioms(f"'{name}' depends on axioms: [propext,\nClassical.choice, Quot.sound]", name), G.KERNEL_AXIOMS)
        for axiom in ("sorryAx", "Poly.roots_le_degree", "CryptoSoundness", "Lean.ofReduceBool"):
            with self.assertRaisesRegex(G.GuardFailure, "unapproved transitive"):
                G.parse_axioms(f"'{name}' depends on axioms: [{axiom}]", name)

    def test_empty_duplicate_or_malformed_axiom_output_fails(self):
        name = self.model + ".checked"
        good = f"'{name}' does not depend on any axioms\n"
        for output in ("", "Build succeeded", good + good, f"'{name}' depends on axioms: ["):
            with self.assertRaisesRegex(G.GuardFailure, "missing/ambiguous"):
                G.parse_axioms(output, name)

    def test_comments_and_strings_not_admissions(self):
        source = '/- sorry /- axiom -/ -/\n-- admit\nimport Std\n#check "sorry"\n'
        self.assertEqual(G.imports_of(source), {"Std"})
        self.assertNotIn("sorry", G.without_comments_and_strings(source))

    def test_subprocess_failure_propagates(self):
        failure = subprocess.CalledProcessError(1, ["lean"], output="type mismatch")
        with patch.object(G.subprocess, "run", side_effect=failure):
            with self.assertRaisesRegex(G.GuardFailure, "command failed"):
                REAL_COMMAND(["lean"], cwd=self.root)


if __name__ == "__main__":
    unittest.main()
