#!/usr/bin/env python3
"""Explicitly provision only the seven source checkouts accepted by the guard.

Unlike check-proof-dependencies.py, executing this script authorizes network Git
fetches from its seven fixed public origins. It never executes Lake, package
configuration, dependency hooks, cache downloads, submodule updates or builds.
Existing repositories must already pass inspection and are never repaired or
updated. An incomplete repository, including one left by a failed fetch, causes
failure without deletion; recovery requires a separate deliberate user action.

The final source-integrity check is not a source-only-build attestation and does
not certify existing .olean/release artifacts or proof soundness. The installed
Python/Git binaries and absence of concurrent filesystem changes are assumptions.
"""
import importlib.util
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location(
    "proof_dependency_guard", Path(__file__).with_name("check-proof-dependencies.py"))
G = importlib.util.module_from_spec(SPEC)
exec(compile(Path(SPEC.origin).read_bytes(), SPEC.origin, "exec"), G.__dict__)
PROJECT = Path(__file__).resolve().parent


class ProvisionFailure(Exception):
    pass


def run_git(directory, *args):
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_NO_REPLACE_OBJECTS="1", GIT_OPTIONAL_LOCKS="0",
               GIT_TERMINAL_PROMPT="0")
    command = ["git", "--no-replace-objects", "-c", "core.fsmonitor=false",
               "-c", f"core.hooksPath={os.devnull}", "-c", "gc.auto=0",
               "-c", "maintenance.auto=false", "-C", str(directory), *args]
    try:
        return subprocess.run(command, check=True, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, env=env, timeout=300).stdout
    except (OSError, subprocess.SubprocessError) as error:
        raise ProvisionFailure(
            f"Git provisioning failed in {directory}; existing contents were retained: {error}") from error


def exists_or_symlink(path):
    return path.exists() or path.is_symlink()


def preflight(project):
    """Finish every available read-only check before creating/fetching anything."""
    G.check_environment()
    G.safe_directory(project)
    G.regular_file(project / "lean-toolchain")
    G.require((project / "lean-toolchain").read_text(encoding="utf-8") == G.TOOLCHAIN,
              "root toolchain mismatch")
    G.validate_manifest(G.read_manifest(project / "lake-manifest.json"), root=True)
    lake_dir = project / ".lake"
    packages_dir = lake_dir / "packages"
    for directory in (lake_dir, packages_dir):
        if exists_or_symlink(directory):
            G.safe_directory(directory)
    existing = set()
    if packages_dir.exists():
        actual = {entry.name for entry in packages_dir.iterdir()}
        G.require(actual <= set(G.PACKAGES), "unexpected package directory entries")
        for name in sorted(actual):
            G.check_repository(packages_dir / name, name)
            existing.add(name)
        if "mathlib" in existing:
            G.validate_manifest(G.read_manifest(packages_dir / "mathlib" / "lake-manifest.json"), root=False)
    return existing


def provision(project=PROJECT):
    project = Path(project).resolve()
    existing = preflight(project)
    lake_dir = project / ".lake"
    packages_dir = lake_dir / "packages"
    # No exist_ok: an unexpected intervening creation is not silently accepted.
    for directory in (lake_dir, packages_dir):
        if not exists_or_symlink(directory):
            directory.mkdir()
        G.safe_directory(directory)
    for name in sorted(G.PACKAGES):
        if name in existing:
            continue
        policy = G.PACKAGES[name]
        directory = packages_dir / name
        directory.mkdir()
        run_git(directory, "init", "--quiet", "--object-format=sha1")
        run_git(directory, "remote", "add", "origin", policy["url"])
        run_git(directory, "fetch", "--no-tags", "--no-recurse-submodules", "--depth=1",
                "origin", policy["rev"])
        run_git(directory, "checkout", "--quiet", "--detach", policy["rev"])
        if tag := policy.get("releaseTag"):
            # Fetch only this fixed name, never all tags or a moving branch.
            # The following source guard checks the exact tag set and target.
            run_git(directory, "fetch", "--no-tags", "--no-recurse-submodules", "--depth=1",
                    "origin", f"refs/tags/{tag}:refs/tags/{tag}")
        G.check_repository(directory, name)
    return G.check_project(project)


def main():
    try:
        G.require(len(sys.argv) == 1, "no alternative revisions, directories or skip options are supported")
        result = provision()
        print(f"[proof-dependencies] Provisioned or retained {result['packages']} exact pinned source checkouts; "
              f"verified {result['tracked_files']} tracked files.")
        print("[proof-dependencies] No Lake/hooks/builds executed; build provenance and proof soundness are not certified.")
        return 0
    except (ProvisionFailure, G.GuardFailure, OSError, UnicodeError) as error:
        print(f"[proof-dependencies] FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
