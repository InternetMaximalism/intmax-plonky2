#!/usr/bin/env python3
"""Isolated source-dependency guard tests; no downloads, Lake or real-tree edits."""
import contextlib
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location("proofdependencies", Path(__file__).with_name("check-proof-dependencies.py"))
G = importlib.util.module_from_spec(SPEC)
exec(compile(Path(SPEC.origin).read_bytes(), SPEC.origin, "exec"), G.__dict__)
OFFICIAL_PACKAGES = copy.deepcopy(G.PACKAGES)


def git(directory, *args):
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_AUTHOR_DATE="2000-01-01T00:00:00+0000", GIT_COMMITTER_DATE="2000-01-01T00:00:00+0000")
    return subprocess.run(["git", "-c", "user.name=Dependency guard fixture",
                           "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgSign=false",
                           "-C", str(directory), *args], check=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, env=env, timeout=30).stdout.decode().strip()


def manifest(root):
    return {"version": "1.1.0", "packagesDir": ".lake/packages", "lakeDir": ".lake",
            "name": "audit" if root else "mathlib", "packages": list(G.expected_entries(root).values())}


def write_json(path, value):
    path.write_text(json.dumps(value), encoding="utf-8")


class DependencyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture_temp = tempfile.TemporaryDirectory(prefix="proof-dep-fixture-")
        cls.fixture = Path(cls.fixture_temp.name) / "audit"
        cls.fixture.mkdir()
        (cls.fixture / "lean-toolchain").write_text(G.TOOLCHAIN)
        cls.policy = copy.deepcopy(OFFICIAL_PACKAGES)
        with patch.object(G, "PACKAGES", cls.policy):
            # The six leaves are committed before Mathlib's own pinned lock.
            for name in [n for n in cls.policy if n != "mathlib"] + ["mathlib"]:
                directory = cls.fixture / ".lake" / "packages" / name
                directory.mkdir(parents=True)
                git(directory, "init", "--quiet")
                git(directory, "remote", "add", "origin", cls.policy[name]["url"])
                (directory / cls.policy[name]["configFile"]).write_text("# inert fixture; never executed\n")
                (directory / "Example.lean").write_text("-- UTF-8 fixture: 証明\ntheorem sample : True := True.intro\n")
                (directory / ".gitignore").write_text("/.lake/\n/ignored/\n/widget/node_modules/\n")
                (directory / "README.md").write_bytes(b"binary-safe content\x00\xff\n")
                if name == "mathlib":
                    write_json(directory / "lake-manifest.json", manifest(False))
                git(directory, "add", "--all")
                git(directory, "commit", "--quiet", "-m", "fixture")
                cls.policy[name]["rev"] = git(directory, "rev-parse", "HEAD")
                if tag := cls.policy[name].get("releaseTag"):
                    git(directory, "tag", tag)
            write_json(cls.fixture / "lake-manifest.json", manifest(True))

    @classmethod
    def tearDownClass(cls):
        cls.fixture_temp.cleanup()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="proof-dep-test-")
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name) / "audit"
        shutil.copytree(self.fixture, self.project)
        self.policy_patch = patch.object(G, "PACKAGES", copy.deepcopy(self.policy))
        self.policy_patch.start()
        self.addCleanup(self.policy_patch.stop)
        self.environment_patch = patch.dict(os.environ, {key: "" for key in G.OVERRIDE_ENV})
        self.environment_patch.start()
        self.addCleanup(self.environment_patch.stop)

    def repo(self, name="batteries"):
        return self.project / ".lake" / "packages" / name

    def validate(self):
        return G.check_project(self.project)

    def expect_failure(self, text=None):
        return self.assertRaisesRegex(G.GuardFailure, text) if text else self.assertRaises(G.GuardFailure)

    def root_manifest(self):
        return G.read_manifest(self.project / "lake-manifest.json")

    def set_root_manifest(self, value):
        write_json(self.project / "lake-manifest.json", value)

    def test_clean_seven_pinned_repositories(self):
        result = self.validate()
        self.assertEqual(result["packages"], 7)
        self.assertEqual(result["tracked_files"], 29)
        self.assertGreater(result["tracked_bytes"], 0)

    def test_policy_is_exact_official_revision_set(self):
        expected = {
            "mathlib": "a719ba5c3115d47b68bf0497a9dd1bcbb21ea663",
            "batteries": "0f3e143dffdc3a591662f3401ce1d7a3405227c0",
            "Qq": "01ad33937acd996ee99eb74eefb39845e4e4b9f5",
            "aesop": "209712c78b16c795453b6da7f7adbda4589a8f21",
            "proofwidgets": "c87908619cccadda23f71262e6898b9893bffa36",
            "Cli": "2cf1030dc2ae6b3632c84a09350b675ef3e347d0",
            "importGraph": "543725b3bfed792097fc134adca628406f6145f5",
        }
        self.assertEqual({name: p["rev"] for name, p in OFFICIAL_PACKAGES.items()}, expected)
        self.assertTrue(all(G.HEX40.fullmatch(rev) for rev in expected.values()))

    def test_official_input_branches_and_inherited_flags(self):
        official = manifest(False)
        G.validate_manifest(official, root=False)
        self.assertTrue(next(x for x in official["packages"] if x["name"] == "Cli")["inherited"])
        self.assertTrue(all(x["inherited"] == (x["name"] == "Cli") for x in official["packages"]))
        self.assertIn("master", [x["inputRev"] for x in official["packages"]])

    def test_root_shape_and_version_are_fixed(self):
        original = self.root_manifest()
        for key, value in (("version", "1.2.0"), ("packagesDir", "../deps"),
                           ("lakeDir", "other"), ("name", "mathlib"), ("packages", {})):
            with self.subTest(key=key):
                altered = copy.deepcopy(original)
                altered[key] = value
                self.set_root_manifest(altered)
                with self.expect_failure():
                    self.validate()
        altered = copy.deepcopy(original)
        altered["extra"] = True
        self.set_root_manifest(altered)
        with self.expect_failure("shape"):
            self.validate()

    def test_empty_missing_extra_and_duplicate_packages(self):
        original = self.root_manifest()
        for entries in ([], original["packages"][:-1], original["packages"] + [original["packages"][0]],
                        original["packages"] + [dict(original["packages"][0], name="other")]):
            self.set_root_manifest(dict(original, packages=entries))
            with self.expect_failure():
                self.validate()

    def test_entry_fields_cannot_be_rebound(self):
        original = self.root_manifest()
        for key, value in (("type", "path"), ("url", "file:///elsewhere"), ("rev", "f" * 40),
                           ("subDir", "../elsewhere"), ("configFile", "other.lean"),
                           ("manifestFile", None), ("scope", "different"),
                           ("inputRev", "main"), ("inherited", True), ("inherited", 0)):
            with self.subTest(key=key, value=value):
                altered = copy.deepcopy(original)
                entry = next(x for x in altered["packages"] if x["name"] == "mathlib")
                entry[key] = value
                self.set_root_manifest(altered)
                with self.expect_failure():
                    self.validate()

    def test_duplicate_json_keys_and_non_json_constants(self):
        path = self.project / "lake-manifest.json"
        for text in ('{"name":"audit","name":"mathlib"}', '{"packages":NaN}'):
            path.write_text(text)
            with self.expect_failure():
                G.read_manifest(path)

    def test_toolchain_changes_rejected(self):
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.11.0\n")
        with self.expect_failure("toolchain"):
            self.validate()

    def test_missing_and_extra_package_directories(self):
        extra = self.repo("extra")
        extra.mkdir()
        with self.expect_failure("inventory"):
            self.validate()
        extra.rmdir()
        self.repo().rename(self.repo("other"))
        with self.expect_failure("inventory"):
            self.validate()

    def test_package_symlink_rejected_even_inside_audit(self):
        original = self.repo()
        moved = self.project / "moved"
        original.rename(moved)
        original.symlink_to(moved, target_is_directory=True)
        with self.expect_failure("symlink"):
            self.validate()

    def test_packages_container_symlink_rejected(self):
        original = self.project / ".lake" / "packages"
        moved = self.project / "moved"
        original.rename(moved)
        original.symlink_to(moved, target_is_directory=True)
        with self.expect_failure("symlink"):
            self.validate()

    def test_head_mismatch_rejected(self):
        (self.repo() / "README.md").write_text("changed")
        git(self.repo(), "add", "README.md")
        git(self.repo(), "commit", "--quiet", "-m", "different head")
        with self.expect_failure("HEAD mismatch"):
            self.validate()

    def test_release_tag_inventory_is_exact(self):
        directory = self.repo("proofwidgets")
        git(directory, "tag", "other-release")
        with self.expect_failure("release tag inventory"):
            self.validate()
        git(directory, "tag", "--delete", "other-release", "v0.0.40")
        with self.expect_failure("release tag inventory"):
            self.validate()

    def test_release_tag_target_is_pinned(self):
        directory = self.repo("proofwidgets")
        git(directory, "commit", "--allow-empty", "--quiet", "-m", "other revision")
        git(directory, "tag", "--force", "v0.0.40")
        git(directory, "checkout", "--quiet", "--detach", G.PACKAGES["proofwidgets"]["rev"])
        with self.expect_failure("release tag target"):
            self.validate()

    def test_wrong_and_duplicate_origin_rejected(self):
        git(self.repo(), "remote", "set-url", "origin", "https://example.invalid/elsewhere")
        with self.expect_failure("origin"):
            self.validate()
        git(self.repo(), "remote", "set-url", "origin", G.PACKAGES["batteries"]["url"])
        git(self.repo(), "config", "--add", "remote.origin.url", G.PACKAGES["batteries"]["url"])
        with self.expect_failure("origin"):
            self.validate()

    def test_all_tracked_files_not_only_lean_are_hashed(self):
        (self.repo() / "README.md").write_text("non-Lean drift")
        with self.expect_failure("pinned blob"):
            self.validate()

    def test_assume_unchanged_does_not_hide_content_drift(self):
        git(self.repo(), "update-index", "--assume-unchanged", "Example.lean")
        (self.repo() / "Example.lean").write_text("-- drift\n")
        self.assertEqual(git(self.repo(), "status", "--porcelain"), "")
        with self.expect_failure("pinned blob"):
            self.validate()

    def test_skip_worktree_does_not_hide_content_drift(self):
        git(self.repo(), "update-index", "--skip-worktree", "Example.lean")
        (self.repo() / "Example.lean").write_text("-- drift\n")
        with self.expect_failure("pinned blob"):
            self.validate()

    def test_staged_only_change_is_dirty(self):
        path = self.repo() / "Example.lean"
        original = path.read_bytes()
        path.write_text("-- staged\n")
        git(self.repo(), "add", "Example.lean")
        path.write_bytes(original)
        with self.expect_failure("Git inspection failed"):
            self.validate()

    def test_deleted_tracked_file_and_mode_change_rejected(self):
        path = self.repo() / "Example.lean"
        original = path.read_bytes()
        path.unlink()
        with self.expect_failure("missing"):
            self.validate()
        path.write_bytes(original)
        path.chmod(0o755)
        with self.expect_failure("mode"):
            self.validate()

    def test_ignored_extra_lean_and_config_are_rejected(self):
        directory = self.repo() / "ignored"
        directory.mkdir()
        for name in ("Injected.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"):
            path = directory / name
            path.write_text("additional source")
            with self.expect_failure("untracked Lean/config"):
                self.validate()
            path.unlink()

    def test_extra_source_below_lake_but_not_build_is_rejected(self):
        path = self.repo() / ".lake" / "unexpected" / "Injected.lean"
        path.parent.mkdir(parents=True)
        path.write_text("-- source")
        with self.expect_failure("untracked Lean/config"):
            self.validate()

    def test_extra_lean_source_inside_build_is_also_rejected(self):
        path = self.repo() / ".lake" / "build" / "lib" / "Injected.lean"
        path.parent.mkdir(parents=True)
        path.write_text("-- additional source, not a binary build artifact")
        with self.expect_failure("untracked Lean/config"):
            self.validate()

    def test_untracked_file_and_directory_symlinks_are_rejected(self):
        path = self.repo() / "alias"
        path.symlink_to(self.project / "lean-toolchain")
        with self.expect_failure("symlink"):
            self.validate()
        path.unlink()
        path.symlink_to(self.project, target_is_directory=True)
        with self.expect_failure("symlink"):
            self.validate()

    def test_tracked_file_replaced_by_symlink_rejected(self):
        path = self.repo() / "Example.lean"
        moved = self.project / "outside.lean"
        path.rename(moved)
        path.symlink_to(moved)
        with self.expect_failure("symlink"):
            self.validate()

    def test_build_artifacts_are_not_certified(self):
        path = self.repo() / ".lake" / "build" / "lib" / "Example.olean"
        path.parent.mkdir(parents=True)
        path.write_bytes(b"explicitly outside source-provenance claim")
        (self.repo() / "extra-not-a-source.txt").write_text("not importable source")
        self.assertEqual(self.validate()["packages"], 7)

    def test_mathlib_official_manifest_is_separately_checked(self):
        # Re-pin a synthetic Mathlib tree containing a changed official lock.
        # Root agreement with that synthetic HEAD alone must not waive the policy.
        altered = manifest(False)
        altered["packages"][0]["inputRev"] = "different"
        directory = self.repo("mathlib")
        write_json(directory / "lake-manifest.json", altered)
        git(directory, "add", "lake-manifest.json")
        git(directory, "commit", "--quiet", "-m", "wrong official lock")
        G.PACKAGES["mathlib"]["rev"] = git(directory, "rev-parse", "HEAD")
        self.set_root_manifest(manifest(True))
        with self.expect_failure("policy mismatch"):
            self.validate()

    def test_external_lean_and_url_map_overrides_rejected(self):
        for key in G.OVERRIDE_ENV:
            with self.subTest(key=key), patch.dict(os.environ, {key: "/outside"}):
                with self.expect_failure("override"):
                    self.validate()

    def test_git_environment_and_hooks_are_not_inherited(self):
        with patch.dict(os.environ, {"GIT_DIR": "/outside", "GIT_CONFIG_COUNT": "1"}), \
             patch.object(G.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, b"ok")) as run:
            self.assertEqual(G.run_git(self.repo(), "rev-parse", "HEAD"), b"ok")
        args, kwargs = run.call_args
        self.assertNotIn("GIT_DIR", kwargs["env"])
        self.assertNotIn("GIT_CONFIG_COUNT", kwargs["env"])
        self.assertEqual(kwargs["env"]["GIT_NO_REPLACE_OBJECTS"], "1")
        self.assertIn("core.fsmonitor=false", args[0])
        self.assertIn(f"core.hooksPath={os.devnull}", args[0])

    def test_git_failure_is_not_success(self):
        with patch.object(G.subprocess, "run", side_effect=subprocess.CalledProcessError(7, ["git"])):
            with self.expect_failure("Git inspection failed"):
                G.run_git(self.repo(), "rev-parse", "HEAD")

    def test_tree_parser_rejects_empty_unsafe_and_non_blob_records(self):
        oid = b"a" * 40
        cases = [b"", b"100644 blob " + oid + b"\tx.lean", b"broken\0",
                 b"100644 blob " + oid + b"\t../x.lean\0",
                 b"100644 blob " + oid + b"\t.\0",
                 b"100644 blob " + oid + b"\t/absolute\0",
                 b"100644 blob " + oid + b"\tx//y\0",
                 b"120000 blob " + oid + b"\tlink\0",
                 b"160000 commit " + oid + b"\tmodule\0"]
        for data in cases:
            with self.subTest(data=data), self.expect_failure():
                G.parse_tree(data)
        record = b"100644 blob " + oid + b"\tx.lean\0"
        with self.expect_failure("duplicate"):
            G.parse_tree(record + record)

    def test_tree_parser_preserves_tabs_and_newlines_in_filenames(self):
        name = "dir/name\twith\nspace.lean"
        parsed = G.parse_tree(b"100644 blob " + b"a" * 40 + b"\t" + name.encode() + b"\0")
        self.assertEqual(set(parsed), {name})

    def test_directory_enumeration_failure_is_fatal(self):
        def failing_walk(*args, **kwargs):
            kwargs["onerror"](PermissionError("unreadable source directory"))
            return iter(())
        with patch.object(G.os, "walk", side_effect=failing_walk):
            with self.expect_failure("cannot enumerate"):
                G.check_extra_sources(self.repo(), {}, "batteries")

    def test_main_exit_codes_and_no_skip_options(self):
        with patch.object(sys, "argv", ["check-proof-dependencies.py"]), \
             patch.object(G, "check_project", return_value={"packages": 7, "tracked_files": 29, "tracked_bytes": 1}), \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(G.main(), 0)
        for args in (["check-proof-dependencies.py", "--skip"], ["check-proof-dependencies.py"]):
            with patch.object(sys, "argv", args), \
                 patch.object(G, "check_project", side_effect=G.GuardFailure("failure")), \
                 contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(G.main(), 1)


if __name__ == "__main__":
    unittest.main()
