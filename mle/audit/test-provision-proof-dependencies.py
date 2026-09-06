#!/usr/bin/env python3
"""Provisioner tests using isolated local repositories, never network transport."""
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
SPEC = importlib.util.spec_from_file_location(
    "proofprovision", Path(__file__).with_name("provision-proof-dependencies.py"))
P = importlib.util.module_from_spec(SPEC)
exec(compile(Path(SPEC.origin).read_bytes(), SPEC.origin, "exec"), P.__dict__)
G = P.G
REAL_PROVISION_GIT = P.run_git


def git(directory, *args):
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_AUTHOR_DATE="2000-01-01T00:00:00+0000", GIT_COMMITTER_DATE="2000-01-01T00:00:00+0000")
    return subprocess.run(["git", "-c", "user.name=Provision fixture",
                           "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgSign=false",
                           "-C", str(directory), *args], check=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, env=env, timeout=30).stdout.decode().strip()


def manifest(root):
    return {"version": "1.1.0", "packagesDir": ".lake/packages", "lakeDir": ".lake",
            "name": "audit" if root else "mathlib", "packages": list(G.expected_entries(root).values())}


def write_json(path, data):
    path.write_text(json.dumps(data), encoding="utf-8")


class ProvisionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture_temp = tempfile.TemporaryDirectory(prefix="proof-provision-fixture-")
        cls.fixtures = Path(cls.fixture_temp.name)
        cls.policy = copy.deepcopy(G.PACKAGES)
        with patch.object(G, "PACKAGES", cls.policy):
            for name in [n for n in cls.policy if n != "mathlib"] + ["mathlib"]:
                directory = cls.fixtures / name
                directory.mkdir()
                git(directory, "init", "--quiet")
                git(directory, "remote", "add", "origin", cls.policy[name]["url"])
                (directory / cls.policy[name]["configFile"]).write_text("-- inert fixture; not executed\n")
                (directory / "Example.lean").write_text("theorem example : True := True.intro\n")
                (directory / ".gitignore").write_text("/.lake/\n")
                if name == "mathlib":
                    write_json(directory / "lake-manifest.json", manifest(False))
                git(directory, "add", "--all")
                git(directory, "commit", "--quiet", "-m", "fixture")
                cls.policy[name]["rev"] = git(directory, "rev-parse", "HEAD")
                if tag := cls.policy[name].get("releaseTag"):
                    git(directory, "tag", tag)

    @classmethod
    def tearDownClass(cls):
        cls.fixture_temp.cleanup()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="proof-provision-test-")
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name) / "audit"
        self.project.mkdir()
        (self.project / "lean-toolchain").write_text(G.TOOLCHAIN)
        self.policy_patch = patch.object(G, "PACKAGES", copy.deepcopy(self.policy))
        self.policy_patch.start()
        self.addCleanup(self.policy_patch.stop)
        self.environment_patch = patch.dict(os.environ, {key: "" for key in G.OVERRIDE_ENV})
        self.environment_patch.start()
        self.addCleanup(self.environment_patch.stop)
        write_json(self.project / "lake-manifest.json", manifest(True))
        self.commands = []
        self.transport_patch = patch.object(P, "run_git", side_effect=self.local_transport)
        self.transport_patch.start()
        self.addCleanup(self.transport_patch.stop)

    def repo(self, name):
        return self.project / ".lake" / "packages" / name

    def copy_existing(self, *names):
        for name in names:
            self.repo(name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(self.fixtures / name, self.repo(name))

    def local_transport(self, directory, *args):
        self.commands.append((directory.name, args))
        if args[0] == "fetch":
            # Assert the real program would fetch only the hardcoded origin/SHA.
            expected_targets = [G.PACKAGES[directory.name]["rev"]]
            if tag := G.PACKAGES[directory.name].get("releaseTag"):
                expected_targets.append(f"refs/tags/{tag}:refs/tags/{tag}")
            self.assertEqual(args[:5], ("fetch", "--no-tags", "--no-recurse-submodules", "--depth=1", "origin"))
            self.assertIn(args[5], expected_targets)
            self.assertEqual(len(args), 6)
            # This is the only fetch actually executed by these tests: a local path.
            args = (*args[:4], str(self.fixtures / directory.name), args[5])
        self.assertIn(args[0], {"init", "remote", "fetch", "checkout"})
        return REAL_PROVISION_GIT(directory, *args)

    def validate_failure_before_mutation(self, message=None):
        context = self.assertRaisesRegex(G.GuardFailure, message) if message else self.assertRaises(G.GuardFailure)
        with context:
            P.provision(self.project)
        self.assertEqual(self.commands, [])

    def test_missing_repositories_are_fetched_at_exact_commits(self):
        result = P.provision(self.project)
        self.assertEqual(result["packages"], 7)
        self.assertEqual(len(self.commands), 29)
        for name in sorted(G.PACKAGES):
            commands = [args for package, args in self.commands if package == name]
            expected_kinds = ["init", "remote", "fetch", "checkout"]
            if G.PACKAGES[name].get("releaseTag"):
                expected_kinds.append("fetch")
            self.assertEqual([args[0] for args in commands], expected_kinds)
            self.assertEqual(commands[0], ("init", "--quiet", "--object-format=sha1"))
            self.assertEqual(commands[1], ("remote", "add", "origin", G.PACKAGES[name]["url"]))
            self.assertEqual(commands[3], ("checkout", "--quiet", "--detach", G.PACKAGES[name]["rev"]))
            self.assertEqual(git(self.repo(name), "rev-parse", "HEAD"), G.PACKAGES[name]["rev"])
            self.assertEqual((self.repo(name) / ".git" / "HEAD").read_text(), G.PACKAGES[name]["rev"] + "\n")

    def test_existing_valid_repositories_are_retained_without_git_writes(self):
        self.copy_existing(*G.PACKAGES)
        before = (self.repo("mathlib") / ".git" / "HEAD").read_bytes()
        self.assertEqual(P.provision(self.project)["packages"], 7)
        self.assertEqual(self.commands, [])
        self.assertEqual((self.repo("mathlib") / ".git" / "HEAD").read_bytes(), before)

    def test_only_missing_subset_is_provisioned(self):
        self.copy_existing("mathlib", "batteries")
        self.assertEqual(P.provision(self.project)["packages"], 7)
        self.assertEqual({name for name, args in self.commands}, set(G.PACKAGES) - {"mathlib", "batteries"})

    def test_invalid_root_manifest_fails_before_directory_creation(self):
        altered = manifest(True)
        altered["packages"][0]["rev"] = "f" * 40
        write_json(self.project / "lake-manifest.json", altered)
        self.validate_failure_before_mutation("policy mismatch")
        self.assertFalse((self.project / ".lake").exists())

    def test_missing_and_extra_root_packages_cannot_trigger_fetch(self):
        for packages in ([], manifest(True)["packages"][:-1],
                         manifest(True)["packages"] + [dict(manifest(True)["packages"][0], name="extra")]):
            altered = manifest(True)
            altered["packages"] = packages
            write_json(self.project / "lake-manifest.json", altered)
            self.validate_failure_before_mutation()

    def test_duplicate_json_key_fails_before_creation(self):
        (self.project / "lake-manifest.json").write_text('{"name":"audit","name":"other"}')
        self.validate_failure_before_mutation("duplicate")
        self.assertFalse((self.project / ".lake").exists())

    def test_toolchain_and_external_overrides_prevent_fetch(self):
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.11.0\n")
        self.validate_failure_before_mutation("toolchain")
        (self.project / "lean-toolchain").write_text(G.TOOLCHAIN)
        for key in G.OVERRIDE_ENV:
            with self.subTest(key=key), patch.dict(os.environ, {key: "/outside"}):
                self.validate_failure_before_mutation("override")

    def test_unknown_existing_entry_prevents_all_mutation(self):
        self.repo("unknown").mkdir(parents=True)
        marker = self.repo("unknown") / "keep.txt"
        marker.write_text("must remain")
        self.validate_failure_before_mutation("unexpected")
        self.assertEqual(marker.read_text(), "must remain")

    def test_incomplete_existing_directory_is_not_repaired(self):
        self.repo("mathlib").mkdir(parents=True)
        marker = self.repo("mathlib") / "keep.txt"
        marker.write_text("incomplete; do not delete")
        self.validate_failure_before_mutation("missing directory")
        self.assertEqual(marker.read_text(), "incomplete; do not delete")

    def test_missing_existing_release_tag_is_not_repaired(self):
        self.copy_existing("proofwidgets")
        git(self.repo("proofwidgets"), "tag", "--delete", "v0.0.40")
        self.validate_failure_before_mutation("release tag inventory")
        self.assertEqual(git(self.repo("proofwidgets"), "tag", "--list"), "")

    def test_existing_dirty_repository_blocks_other_missing_fetches(self):
        self.copy_existing("mathlib")
        changed = self.repo("mathlib") / "Example.lean"
        changed.write_text("-- retain this change\n")
        self.validate_failure_before_mutation("pinned blob")
        self.assertEqual(changed.read_text(), "-- retain this change\n")
        self.assertFalse(self.repo("Cli").exists())

    def test_wrong_existing_head_is_not_checked_out_or_reset(self):
        self.copy_existing("mathlib")
        (self.repo("mathlib") / "Example.lean").write_text("-- other commit\n")
        git(self.repo("mathlib"), "add", "Example.lean")
        git(self.repo("mathlib"), "commit", "--quiet", "-m", "other")
        before = git(self.repo("mathlib"), "rev-parse", "HEAD")
        self.validate_failure_before_mutation("HEAD mismatch")
        self.assertEqual(git(self.repo("mathlib"), "rev-parse", "HEAD"), before)

    def test_container_and_package_symlinks_are_not_followed(self):
        outside = self.project / "outside"
        outside.mkdir()
        lake = self.project / ".lake"
        lake.symlink_to(outside, target_is_directory=True)
        self.validate_failure_before_mutation("symlink")
        lake.unlink()
        self.repo("mathlib").parent.mkdir(parents=True)
        self.repo("mathlib").symlink_to(outside, target_is_directory=True)
        self.validate_failure_before_mutation("symlink")
        self.assertEqual(list(outside.iterdir()), [])

    def test_dangling_symlink_and_regular_file_package_are_rejected(self):
        self.repo("mathlib").parent.mkdir(parents=True)
        self.repo("mathlib").symlink_to(self.project / "missing")
        self.validate_failure_before_mutation("symlink")
        self.repo("mathlib").unlink()
        self.repo("mathlib").write_text("must not replace")
        self.validate_failure_before_mutation("directory")
        self.assertEqual(self.repo("mathlib").read_text(), "must not replace")

    def test_failed_fetch_retains_partial_and_previous_repositories(self):
        failed_name = sorted(G.PACKAGES)[1]
        def failing(directory, *args):
            if directory.name == failed_name and args[0] == "fetch":
                raise P.ProvisionFailure("simulated unavailable transport")
            return self.local_transport(directory, *args)
        with patch.object(P, "run_git", side_effect=failing):
            with self.assertRaisesRegex(P.ProvisionFailure, "unavailable"):
                P.provision(self.project)
        first = sorted(G.PACKAGES)[0]
        G.check_repository(self.repo(first), first)
        self.assertTrue((self.repo(failed_name) / ".git").is_dir())
        self.commands.clear()
        self.validate_failure_before_mutation("Git inspection failed")
        self.assertTrue((self.repo(failed_name) / ".git").is_dir())

    def test_final_full_guard_detects_root_manifest_drift(self):
        real_check = G.check_project
        def changed_root(project):
            altered = manifest(True)
            altered["packagesDir"] = "other"
            write_json(project / "lake-manifest.json", altered)
            return real_check(project)
        with patch.object(G, "check_project", side_effect=changed_root) as final_check:
            with self.assertRaisesRegex(G.GuardFailure, "packagesDir"):
                P.provision(self.project)
            final_check.assert_called_once_with(self.project.resolve())
        self.assertTrue(self.repo("mathlib").is_dir())

    def test_existing_official_mathlib_lock_checked_before_fetch(self):
        self.copy_existing("mathlib")
        altered = manifest(False)
        altered["packages"][0]["inputRev"] = "wrong"
        write_json(self.repo("mathlib") / "lake-manifest.json", altered)
        git(self.repo("mathlib"), "add", "lake-manifest.json")
        git(self.repo("mathlib"), "commit", "--quiet", "-m", "wrong lock")
        G.PACKAGES["mathlib"]["rev"] = git(self.repo("mathlib"), "rev-parse", "HEAD")
        write_json(self.project / "lake-manifest.json", manifest(True))
        self.validate_failure_before_mutation("policy mismatch")

    def test_mutating_git_runner_sanitizes_hooks_and_environment(self):
        with patch.dict(os.environ, {"GIT_DIR": "/outside", "GIT_TEMPLATE_DIR": "/outside"}), \
             patch.object(P.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, b"ok")) as run:
            self.assertEqual(REAL_PROVISION_GIT(self.project, "init", "--quiet"), b"ok")
        args, kwargs = run.call_args
        self.assertNotIn("GIT_DIR", kwargs["env"])
        self.assertNotIn("GIT_TEMPLATE_DIR", kwargs["env"])
        self.assertEqual(kwargs["env"]["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertIn("core.fsmonitor=false", args[0])
        self.assertIn(f"core.hooksPath={os.devnull}", args[0])
        self.assertIn("maintenance.auto=false", args[0])

    def test_git_failure_is_nonzero_without_cleanup(self):
        with patch.object(P.subprocess, "run", side_effect=subprocess.CalledProcessError(8, ["git"])):
            with self.assertRaisesRegex(P.ProvisionFailure, "retained"):
                REAL_PROVISION_GIT(self.project, "init")
        self.assertTrue(self.project.is_dir())

    def test_main_status_and_arguments(self):
        with patch.object(sys, "argv", ["provision-proof-dependencies.py"]), \
             patch.object(P, "provision", return_value={"packages": 7, "tracked_files": 22}), \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(P.main(), 0)
        for args in (["provision-proof-dependencies.py", "--force"], ["provision-proof-dependencies.py"]):
            with patch.object(sys, "argv", args), \
                 patch.object(P, "provision", side_effect=P.ProvisionFailure("failure")), \
                 contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(P.main(), 1)


if __name__ == "__main__":
    unittest.main()
