#!/usr/bin/env python3
"""Check current Lean proofs and a complete, explicitly partial source inventory.

Checksums detect review drift, NOT source-to-model semantic equivalence.
The allowlist checks global axioms, NOT explicit theorem/Engine hypotheses.
"""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
PROJECT = "mle/audit"
MANIFEST = PROJECT + "/wire3-manifest.json"
MODEL_PREFIX = PROJECT + "/Audit/Wire3/"
CLAIM = "partial-models-not-full-implementation-proof"
IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
QUALIFIED = re.compile(rf"{IDENT}(?:\.{IDENT})*\Z")
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
KERNEL_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REQUIRED_MODULES = {"Audit.Wire3." + name for name in (
    "Arithmetic", "Packed", "Transcript", "Compact", "Sumcheck", "Verifier",
    "Connections", "WhirTerminal",
)}
REQUIRED = {
    PROJECT + "/check-wire3.py", PROJECT + "/test-check-wire3.py",
    PROJECT + "/lakefile.lean", PROJECT + "/lean-toolchain",
    PROJECT + "/Audit.lean", PROJECT + "/README.md", PROJECT + "/SCOPE.md",
    PROJECT + "/REPORT.md", "mle/protocol/mle_whir_v2.json",
    "mle/Cargo.toml", "Cargo.toml", "Cargo.lock", "rust-toolchain",
    ".github/workflows/continuous-integration-workflow.yml",
}

class GuardFailure(Exception):
    pass


def require(condition, message):
    if not condition:
        raise GuardFailure(message)


def command(args, cwd=ROOT, capture=True):
    try:
        result = subprocess.run(args, cwd=cwd, check=True, text=True,
                                stdout=subprocess.PIPE if capture else None,
                                stderr=subprocess.STDOUT, timeout=600)
    except (OSError, subprocess.SubprocessError) as error:
        output = getattr(error, "stdout", "") or ""
        raise GuardFailure(f"command failed: {args!r}\n{output}\n{error}") from error
    return result.stdout or ""


def exact_keys(value, keys, label):
    require(isinstance(value, dict) and set(value) == set(keys),
            f"{label}: expected exactly keys {sorted(keys)}")


def checked_path(root, value):
    require(isinstance(value, str) and value != "", "empty/non-string source path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and path.as_posix() == value
            and not any(part in {"", ".", ".."} for part in path.parts),
            f"noncanonical source path: {value!r}")
    resolved = (root / value).resolve()
    require(resolved.is_relative_to(root.resolve()), f"source escapes checkout: {value}")
    require(resolved.is_file(), f"missing source: {value}")
    return resolved


def without_comments_and_strings(source):
    """Preserve newlines, including through nested Lean block comments.

    This is a conservative admission/import inventory, not a Lean parser. Actual
    parsing and the trusted dependency check are always performed by Lean too.
    """
    output = []
    depth = 0
    quoted = False
    index = 0
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                output.extend("  ")
                index += 2
                continue
            output.append("\n" if char == "\n" else " ")
        elif quoted:
            if char == "\\":
                output.extend("  ")
                index += 2
                continue
            if char == '"':
                quoted = False
            output.append("\n" if char == "\n" else " ")
        elif pair == "/-":
            depth = 1
            output.extend("  ")
            index += 2
            continue
        elif pair == "--":
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            output.extend(" " * (end - index))
            index = end
            continue
        elif char == '"':
            quoted = True
            output.append(" ")
        else:
            output.append(char)
        index += 1
    require(depth == 0 and not quoted, "unterminated Lean comment/string")
    return "".join(output)


def imports_of(source):
    clean = without_comments_and_strings(source)
    imports = set()
    for group in re.findall(r"^\s*import\s+([^\n]+)", clean, flags=re.MULTILINE):
        for name in group.split():
            require(QUALIFIED.fullmatch(name), f"unrecognized import: {name}")
            imports.add(name)
    return imports



def tracked_files(root):
    paths = command(["git", "ls-files", "--cached", "--others", "--exclude-standard"], cwd=root).splitlines()
    require(len(paths) == len(set(paths)), "duplicate tracked/untracked path")
    return set(paths)


def implementation_inventory(paths):
    # Every Rust/Solidity file owned by this checkout, including tests/examples.
    # External submodule/git dependency contents are not silently called proved.
    return {p for p in paths if p.endswith((".rs", ".sol"))}


def current_modules(root, paths):
    result = {}
    for path in sorted(paths):
        if path.startswith(MODEL_PREFIX) and path.endswith(".lean"):
            module = path[len(PROJECT) + 1:-5].replace("/", ".")
            require(QUALIFIED.fullmatch(module), f"invalid current module: {path}")
            result[module] = path
    require(result, "no current Lean modules")
    require(REQUIRED_MODULES <= set(result), "baseline current model missing")
    return result


def check_current_imports(root, modules):
    sources = {module: checked_path(root, path).read_text() for module, path in modules.items()}
    sources["Audit"] = checked_path(root, PROJECT + "/Audit.lean").read_text()
    root_body = without_comments_and_strings(sources["Audit"])
    require(not re.sub(r"^\s*import\s+[^\n]+", "", root_body, flags=re.MULTILINE).strip(),
            "Audit root must contain only imports; put all declarations in inventoried current modules")
    for module, source in sources.items():
        clean = without_comments_and_strings(source)
        require(not re.search(r"\b(sorry|admit|sorryAx|axiom|native_decide)\b", clean),
                f"admission/non-kernel proof/axiom in current module: {module}")
        for imported in imports_of(source):
            standard = imported in {"Init", "Std", "Lean"} or imported.startswith(("Init.", "Std.", "Lean."))
            require(standard or imported in modules, f"historical/unreviewed import: {module} -> {imported}")
    reached = set()
    pending = ["Audit"]
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        reached.add(name)
        pending.extend(i for i in imports_of(sources[name]) if i in sources)
    require(reached == set(sources), f"unbuilt current modules: {sorted(set(sources) - reached)}")
    config = without_comments_and_strings(checked_path(root, PROJECT + "/lakefile.lean").read_text())
    require(re.findall(rf"@\[default_target\]\s*lean_lib\s+({IDENT})", config) == ["Audit"],
            "current Audit root must be the sole default build target")
    require(checked_path(root, PROJECT + "/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.10.0",
            "unexpected Lean toolchain")
    return sources


def validate_manifest(root, manifest):
    exact_keys(manifest, {"schema_version", "audit_base_commit", "claim", "files", "models"}, "manifest")
    require(type(manifest["schema_version"]) is int and manifest["schema_version"] == 1, "invalid schema")
    require(manifest["claim"] == CLAIM, "this audit must not claim full implementation soundness")
    base = manifest["audit_base_commit"]
    require(isinstance(base, str) and HEX40.fullmatch(base), "invalid base commit")
    command(["git", "merge-base", "--is-ancestor", base, "HEAD"], cwd=root)
    paths = tracked_files(root)
    modules = current_modules(root, paths)
    entries = manifest["files"]
    require(isinstance(entries, list) and entries, "empty file inventory")
    files = {}
    for entry in entries:
        exact_keys(entry, {"path", "sha256", "kind"}, "file")
        path = entry["path"]
        file = checked_path(root, path)
        require(path != MANIFEST and path not in files, f"duplicate/self-hashed path: {path}")
        require(entry["kind"] in {"implementation", "current-model", "historical", "spec", "tooling"}, "invalid file kind")
        digest = entry["sha256"]
        require(isinstance(digest, str) and HEX64.fullmatch(digest), "invalid hash")
        require(hashlib.sha256(file.read_bytes()).hexdigest() == digest,
                f"reviewed file changed: {path}; review correspondence before updating hashes")
        files[path] = entry
    require(REQUIRED <= set(files), f"unhashed required inputs: {sorted(REQUIRED - set(files))}")
    actual_sources = implementation_inventory(paths)
    listed_sources = {p for p, f in files.items() if f["kind"] == "implementation"}
    require(actual_sources == listed_sources,
            f"source inventory incomplete: missing={sorted(actual_sources - listed_sources)}, extra={sorted(listed_sources - actual_sources)}")
    all_lean = {p for p in paths if p.startswith(PROJECT + "/") and p.endswith(".lean")}
    require(all_lean <= set(files), f"unhashed current/historical Lean files: {sorted(all_lean - set(files))}")
    sources = check_current_imports(root, modules)
    records = manifest["models"]
    require(isinstance(records, list) and len(records) == len(modules), "missing/extra current model records")
    seen, represented = set(), set()
    for record in records:
        exact_keys(record, {"module", "theorems", "sources", "scope"}, "model")
        module = record["module"]
        require(isinstance(module, str) and module in modules and module not in seen, "duplicate/unknown model")
        require(files[modules[module]]["kind"] == "current-model", "current model mislabeled")
        require(isinstance(record["scope"], str) and record["scope"].strip(), "missing scope qualification")
        names = record["theorems"]
        require(isinstance(names, list) and names and all(isinstance(n, str) for n in names), "empty/invalid theorem list")
        require(len(set(names)) == len(names) and all(QUALIFIED.fullmatch(n) and n.startswith(module + ".") for n in names),
                "duplicate/unqualified theorem")
        declared = re.findall(rf"\btheorem\s+({IDENT})\b", without_comments_and_strings(sources[module]))
        require(declared and len(declared) == len(names) and set(declared) == {n.rsplit(".", 1)[-1] for n in names},
                f"must audit every named theorem: {module}")
        mapped = record["sources"]
        require(isinstance(mapped, list) and mapped and all(isinstance(p, str) for p in mapped), "empty/invalid source mapping")
        require(len(set(mapped)) == len(mapped) and set(mapped) <= listed_sources, "mapping must name inventoried implementation")
        represented.update(mapped)
        seen.add(module)
    require(seen == set(modules), "current model omitted")
    print(f"[wire3-audit] {len(listed_sources)} source files inventoried: {len(represented)} partially modeled, "
          f"{len(listed_sources - represented)} not modeled; NONE certified as whole implementation", flush=True)
    print(f"[wire3-audit] {len(files)} reviewed hashes, {len(modules)} current modules", flush=True)
    return records


def parse_axioms(output, theorem):
    # Require exactly one compiler-generated result per requested theorem; empty,
    # malformed, repeated, or unexpected output must never look like success.
    start = re.escape("'" + theorem + "'")
    pattern = start + r" (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    matches = list(re.finditer(pattern, output))
    require(len(matches) == 1, f"missing/ambiguous Lean axiom result: {theorem}")
    content = matches[0].group(1)
    axioms = set() if content is None or not content.strip() else {x.strip() for x in content.split(",")}
    require(axioms <= KERNEL_AXIOMS, f"unapproved transitive axioms in {theorem}: {sorted(axioms - KERNEL_AXIOMS)}")
    return axioms



def audit_theorems(root, records):
    lake = shutil.which("lake")
    require(lake is not None, "lake not on PATH")
    command([lake, "build"], cwd=root / PROJECT, capture=False)
    with tempfile.TemporaryDirectory(prefix="wire3-axioms-") as temp:
        for index, record in enumerate(records):
            lines = ["import Lean", "import " + record["module"]]
            for name in record["theorems"]:
                lines.extend([
                    "run_cmd do",
                    "  let info ← Lean.getConstInfo `" + name,
                    "  match info with",
                    "  | .thmInfo _ => pure ()",
                    '  | _ => throwError "audit target is not a theorem"',
                    "#check " + name, "#print axioms " + name,
                ])
            probe = Path(temp) / f"Axioms{index}.lean"
            probe.write_text("\n".join(lines) + "\n")
            output = command([lake, "env", "lean", str(probe)], cwd=root / PROJECT)
            require("sorryAx" not in output and "declaration uses 'sorry'" not in output, "admitted dependency")
            for name in record["theorems"]:
                print(f"[wire3-audit] {name}: {sorted(parse_axioms(output, name))}", flush=True)


def unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def main():
    require(len(sys.argv) == 1, "no skip/refresh options")
    manifest = json.loads(checked_path(ROOT, MANIFEST).read_text(), object_pairs_hook=unique_json_object)
    records = validate_manifest(ROOT, manifest)
    audit_theorems(ROOT, records)
    validate_manifest(ROOT, manifest)
    print("[wire3-audit] PASS: current model build, complete inventory, reviewed hashes, all named theorem dependencies")
    print("[wire3-audit] NOT PROVED: complete implementation/refinement, field/PCS/FS soundness, witness existence")


if __name__ == "__main__":
    try:
        main()
    except (GuardFailure, OSError, TypeError, ValueError, KeyError) as error:
        print(f"[wire3-audit] FAIL: {error}", file=sys.stderr)
        sys.exit(1)
