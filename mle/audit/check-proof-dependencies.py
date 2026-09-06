#!/usr/bin/env python3
"""Read-only source-integrity guard for the pinned Mathlib 4.10 audit dependency.

This standalone checker complements, but never replaces, check-wire3.py. It executes
only read-only Git commands, never Lake, dependency hooks, provisioning or network
operations. All seven source trees are checked against their pinned Git blobs,
including files hidden from ordinary status by assume-unchanged/skip-worktree.

It does NOT establish the provenance of ignored build outputs or release archives,
recheck existing .olean files, prove source/model refinement, or enlarge production
proof coverage. A caller integrating it must run it both before and after builds,
retain all named-theorem axiom checks, and separately control build provenance.
Concurrent filesystem mutation and the installed Python/Git/toolchain are outside
this point-in-time source-integrity check's trust boundary.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys


PROJECT = Path(__file__).resolve().parent
TOOLCHAIN = "leanprover/lean4:v4.10.0\n"
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
OVERRIDE_ENV = ("LEAN_PATH", "LEAN_SRC_PATH", "LAKE_PKG_URL_MAP")
MANIFEST_KEYS = {"version", "packagesDir", "packages", "name", "lakeDir"}
ENTRY_KEYS = {"url", "type", "subDir", "scope", "rev", "name",
              "manifestFile", "inputRev", "inherited", "configFile"}
PACKAGES = {
    "mathlib": {
        "url": "https://github.com/leanprover-community/mathlib4",
        "rev": "a719ba5c3115d47b68bf0497a9dd1bcbb21ea663",
        "scope": "", "inputRev": None, "configFile": "lakefile.lean"},
    "batteries": {
        "url": "https://github.com/leanprover-community/batteries",
        "rev": "0f3e143dffdc3a591662f3401ce1d7a3405227c0",
        "scope": "leanprover-community", "inputRev": "main", "configFile": "lakefile.lean"},
    "Qq": {
        "url": "https://github.com/leanprover-community/quote4",
        "rev": "01ad33937acd996ee99eb74eefb39845e4e4b9f5",
        "scope": "leanprover-community", "inputRev": "master", "configFile": "lakefile.lean"},
    "aesop": {
        "url": "https://github.com/leanprover-community/aesop",
        "rev": "209712c78b16c795453b6da7f7adbda4589a8f21",
        "scope": "leanprover-community", "inputRev": "master", "configFile": "lakefile.toml"},
    "proofwidgets": {
        "url": "https://github.com/leanprover-community/ProofWidgets4",
        "rev": "c87908619cccadda23f71262e6898b9893bffa36",
        "releaseTag": "v0.0.40",
        "scope": "leanprover-community", "inputRev": "v0.0.40", "configFile": "lakefile.lean"},
    "Cli": {
        "url": "https://github.com/leanprover/lean4-cli",
        "rev": "2cf1030dc2ae6b3632c84a09350b675ef3e347d0",
        "scope": "", "inputRev": "main", "configFile": "lakefile.toml"},
    "importGraph": {
        "url": "https://github.com/leanprover-community/import-graph",
        "rev": "543725b3bfed792097fc134adca628406f6145f5",
        "scope": "leanprover-community", "inputRev": "main", "configFile": "lakefile.toml"},
}


class GuardFailure(Exception):
    pass


def require(condition, message):
    if not condition:
        raise GuardFailure(message)


def check_environment():
    for name in OVERRIDE_ENV:
        require(not os.environ.get(name), f"external dependency override is forbidden: {name}")


def run_git(directory, *args):
    # Git environment indirection and executable hooks must not affect inspection.
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_NO_REPLACE_OBJECTS="1", GIT_OPTIONAL_LOCKS="0",
               GIT_TERMINAL_PROMPT="0")
    command = ["git", "--no-replace-objects", "-c", "core.fsmonitor=false",
               "-c", f"core.hooksPath={os.devnull}", "-C", str(directory), *args]
    try:
        return subprocess.run(command, check=True, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, env=env, timeout=60).stdout
    except (OSError, subprocess.SubprocessError) as error:
        raise GuardFailure(f"read-only Git inspection failed in {directory}: {error}") from error


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def regular_file(path):
    require(not path.is_symlink() and path.is_file(), f"missing/non-regular or symlink file: {path}")


def read_manifest(path):
    regular_file(path)
    try:
        return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=no_duplicate_keys,
                          parse_constant=lambda value: (_ for _ in ()).throw(
                              GuardFailure(f"non-JSON constant: {value}")))
    except (OSError, UnicodeError, ValueError) as error:
        raise GuardFailure(f"invalid manifest {path}: {error}") from error


def expected_entries(root):
    result = {}
    for name, policy in PACKAGES.items():
        if not root and name == "mathlib":
            continue
        result[name] = {
            "name": name, "type": "git", "url": policy["url"],
            "rev": policy["rev"], "subDir": None, "scope": policy["scope"],
            "manifestFile": "lake-manifest.json", "configFile": policy["configFile"],
            "inputRev": policy["rev"] if name == "mathlib" else policy["inputRev"],
            "inherited": name != "mathlib" if root else name == "Cli",
        }
    return result


def validate_manifest(document, root):
    require(type(document) is dict and set(document) == MANIFEST_KEYS, "manifest shape mismatch")
    for key, expected in (("version", "1.1.0"), ("packagesDir", ".lake/packages"),
                          ("lakeDir", ".lake"), ("name", "audit" if root else "mathlib")):
        require(document[key] == expected, f"manifest {key} mismatch")
    entries = document["packages"]
    require(type(entries) is list, "manifest packages must be an array")
    expected = expected_entries(root)
    seen = set()
    for entry in entries:
        require(type(entry) is dict and set(entry) == ENTRY_KEYS, "package entry shape mismatch")
        name = entry["name"]
        require(type(name) is str and name in expected, f"unexpected dependency: {name!r}")
        require(name not in seen, f"duplicate dependency: {name}")
        seen.add(name)
        require(type(entry["inherited"]) is bool, f"non-Boolean inherited flag: {name}")
        require(entry == expected[name], f"dependency policy mismatch: {name}")
    require(seen == set(expected), f"missing dependencies: {sorted(set(expected) - seen)}")


def safe_directory(path):
    require(not path.is_symlink() and path.is_dir(), f"missing directory or symlink: {path}")


def parse_tree(data):
    require(bool(data) and data.endswith(b"\0"), "empty or malformed Git tree")
    result = {}
    for record in data[:-1].split(b"\0"):
        try:
            header, raw_path = record.split(b"\t", 1)
            mode, kind, oid = header.split(b" ")
            name = os.fsdecode(raw_path)
            digest = oid.decode("ascii")
        except (ValueError, UnicodeError) as error:
            raise GuardFailure("malformed Git tree record") from error
        path = PurePosixPath(name)
        require(name and path.parts and not path.is_absolute() and path.as_posix() == name
                and all(part not in (".", "..", ".git") for part in path.parts),
                f"unsafe Git tree path: {name!r}")
        require(name not in result, f"duplicate Git tree path: {name!r}")
        require(mode in (b"100644", b"100755") and kind == b"blob",
                f"unsupported tree entry (including symlink/gitlink): {name!r}")
        require(HEX40.fullmatch(digest), f"invalid Git blob ID: {name!r}")
        result[name] = (mode == b"100755", digest)
    return result


def blob_digest(path):
    regular_file(path)
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        with os.fdopen(os.open(path, flags), "rb") as stream:
            before = os.fstat(stream.fileno())
            require(stat.S_ISREG(before.st_mode), f"not a regular file: {path}")
            digest = hashlib.sha1(b"blob " + str(before.st_size).encode("ascii") + b"\0")
            total = 0
            while chunk := stream.read(1024 * 1024):
                total += len(chunk)
                digest.update(chunk)
            require(total == before.st_size, f"file changed during inspection: {path}")
            return digest.hexdigest(), bool(before.st_mode & stat.S_IXUSR), total
    except OSError as error:
        raise GuardFailure(f"cannot hash {path}: {error}") from error


def check_extra_sources(directory, tracked, package):
    # Git metadata and installed NPM packages are not Lean source trees. Ignored
    # .olean/archive/JS content is not certified; build policy controls provenance.
    # Unlike binary outputs, added Lean/config files in .lake/build are rejected.
    skipped = {".git"}
    if package == "proofwidgets":
        skipped.add("widget/node_modules")
    config_names = {"lakefile.toml", "lean-toolchain", "lake-manifest.json", ".gitmodules"}
    def traversal_error(error):
        raise GuardFailure(f"cannot enumerate dependency sources: {error}") from error

    for current, directories, files in os.walk(directory, followlinks=False, onerror=traversal_error):
        relative = Path(current).relative_to(directory)
        keep = []
        for name in directories:
            path = Path(current) / name
            rel = (relative / name).as_posix()
            require(not path.is_symlink(), f"source directory symlink: {path}")
            if rel not in skipped:
                keep.append(name)
        directories[:] = keep
        for name in files:
            path = Path(current) / name
            require(not path.is_symlink(), f"source file symlink: {path}")
            rel = (relative / name).as_posix()
            if path.suffix == ".lean" or name in config_names:
                require(rel in tracked, f"untracked Lean/config source: {path}")


def check_repository(directory, package):
    policy = PACKAGES[package]
    safe_directory(directory)
    safe_directory(directory / ".git")
    top = os.fsdecode(run_git(directory, "rev-parse", "--show-toplevel").rstrip(b"\n"))
    require(Path(top).resolve() == directory.resolve(), f"dependency is not its own Git root: {directory}")
    head = run_git(directory, "rev-parse", "--verify", "HEAD^{commit}").decode("ascii").strip()
    require(head == policy["rev"], f"dependency HEAD mismatch: {package}")
    if tag := policy.get("releaseTag"):
        # Lake 4.10 discovers ProofWidgets releases through a local tag. Accept
        # exactly the reviewed tag, not another name selecting a different asset.
        tags = run_git(directory, "tag", "--list").decode("utf-8").splitlines()
        require(tags == [tag], f"dependency release tag inventory mismatch: {package}")
        target = run_git(directory, "rev-parse", "--verify", f"refs/tags/{tag}^{{commit}}").decode("ascii").strip()
        require(target == policy["rev"], f"dependency release tag target mismatch: {package}")
    origin = run_git(directory, "config", "--get-all", "remote.origin.url").decode("utf-8").splitlines()
    require(origin == [policy["url"]], f"dependency origin mismatch: {package}")
    # Index-only changes are also dirty, even when working files match HEAD.
    run_git(directory, "diff-index", "--cached", "--quiet", "--no-ext-diff", "--no-textconv", head, "--")
    tracked = parse_tree(run_git(directory, "ls-tree", "-r", "-z", "--full-tree", head))
    checked_directories = {directory}
    byte_count = 0
    for name, (executable, expected_digest) in tracked.items():
        path = directory / name
        for parent in reversed(path.parents):
            if parent == directory or directory in parent.parents:
                if parent not in checked_directories:
                    safe_directory(parent)
                    checked_directories.add(parent)
        actual_digest, actual_executable, size = blob_digest(path)
        require(actual_digest == expected_digest, f"tracked content differs from pinned blob: {package}/{name}")
        require(actual_executable == executable, f"tracked executable mode differs: {package}/{name}")
        byte_count += size
    require(policy["configFile"] in tracked, f"pinned package config is missing: {package}")
    check_extra_sources(directory, tracked, package)
    return len(tracked), byte_count


def check_project(project=PROJECT):
    check_environment()
    project = Path(project).resolve()
    regular_file(project / "lean-toolchain")
    require((project / "lean-toolchain").read_text(encoding="utf-8") == TOOLCHAIN, "root toolchain mismatch")
    validate_manifest(read_manifest(project / "lake-manifest.json"), root=True)
    safe_directory(project / ".lake")
    packages = project / ".lake" / "packages"
    safe_directory(packages)
    require({entry.name for entry in packages.iterdir()} == set(PACKAGES), "package directory inventory mismatch")
    files, size = 0, 0
    for package in sorted(PACKAGES):
        count, byte_count = check_repository(packages / package, package)
        files += count
        size += byte_count
    validate_manifest(read_manifest(packages / "mathlib" / "lake-manifest.json"), root=False)
    return {"packages": len(PACKAGES), "tracked_files": files, "tracked_bytes": size}


def main():
    try:
        require(len(sys.argv) == 1, "no arguments or skip options are supported")
        result = check_project()
        print(f"[proof-dependencies] PASS: {result['packages']} pinned source checkouts, "
              f"{result['tracked_files']} tracked files, {result['tracked_bytes']} bytes")
        print("[proof-dependencies] Source integrity only; build provenance and proof soundness are not certified.")
        return 0
    except (GuardFailure, OSError, UnicodeError) as error:
        print(f"[proof-dependencies] FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
