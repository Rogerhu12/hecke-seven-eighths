#!/usr/bin/env python3
"""Build MOM_BASE with Lake and check every public theorem's recursive axioms.

Run after the pinned Mathlib cache and, optionally, restore-lake-cache. Lake
validates source, options, dependency and output hashes for cached libraries.
Task outputs are removed before building; the audit is always re-elaborated.
All evidence stays in mom-base-verification/ for the Actions artifact.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
TASK_DIR = ROOT / "HeckeSkeleton/Moments/MOM_BASE"
AUDIT = TASK_DIR / "Audit.lean"
LOGS = ROOT / "mom-base-verification"
EXPECTED_LEAN = "4.35.0-rc3"
EXPECTED_LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
EXPECTED_MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def checked(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def lean_code(source: str) -> str:
    """Blank nested comments and strings, retaining lines for the source gate."""
    output, index, depth = [], 0, 0
    while index < len(source):
        pair = source[index:index + 2]
        if pair == "/-":
            depth += 1
            output.extend("  ")
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            output.extend("  ")
            index += 2
        elif depth:
            output.append("\n" if source[index] == "\n" else " ")
            index += 1
        elif pair == "--":
            newline = source.find("\n", index)
            if newline < 0:
                break
            output.append("\n")
            index = newline + 1
        elif source[index] == '"':
            output.append(" ")
            index += 1
            while index < len(source):
                char = source[index]
                output.append("\n" if char == "\n" else " ")
                index += 1
                if char == "\\":
                    index += 1
                    output.append(" ")
                elif char == '"':
                    break
        else:
            output.append(source[index])
            index += 1
    if depth:
        raise RuntimeError("Unclosed Lean block comment")
    return "".join(output)


def public_theorems(source: str) -> set[str]:
    """Inventory this task's ordinary namespace/section theorem declarations."""
    namespace, scopes, result = [], [], set()
    for line in source.splitlines():
        line = line.strip()
        match = re.fullmatch(r"namespace\s+([\w.]+)", line)
        if match:
            scopes.append(len(namespace))
            namespace.extend(match[1].split("."))
            continue
        if re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+[\w.]+)?", line):
            scopes.append(len(namespace))
            continue
        if re.fullmatch(r"end(?:\s+[\w.]+)?", line):
            if not scopes:
                raise RuntimeError("Unmatched namespace/section end")
            namespace = namespace[:scopes.pop()]
            continue
        match = re.match(r"(?:@\[[^]]*\]\s*)*((?:(?:private|protected|public)\s+)*)"
                         r"(?:theorem|lemma)\s+([\w'.]+)", line)
        if match and "private" not in match[1].split():
            result.add(".".join(namespace + [match[2]]))
    return result


def option_flags(options: dict, prefix: str = "") -> list[str]:
    result = []
    for key, value in options.items():
        name = f"{prefix}.{key}" if prefix else key
        if isinstance(value, dict):
            result.extend(option_flags(value, name))
        else:
            text = str(value).lower() if isinstance(value, bool) else str(value)
            result.append(f"-D{name}={text}")
    return result


def logged_run(command: list[str], log: Path) -> dict:
    print("COMMAND: " + " ".join(command), flush=True)
    started = time.monotonic()
    with log.open("w") as evidence:
        with subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, bufsize=1) as process:
            assert process.stdout is not None
            for line in process.stdout:
                evidence.write(line)
                evidence.flush()
                print(line, end="", flush=True)
            code = process.wait()
    return {"command": command, "exit_code": code,
            "seconds": round(time.monotonic() - started, 3)}


def main() -> None:
    LOGS.mkdir(exist_ok=True)
    sources = sorted(TASK_DIR.glob("*.lean"))
    if not sources or not AUDIT.is_file():
        raise SystemExit("Missing MOM_BASE source modules or mandatory Audit.lean")
    hashes, declarations = {}, set()
    for path in sources:
        raw = path.read_bytes()
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(raw).hexdigest()
        code = lean_code(raw.decode())
        forbidden = re.findall(r"\b(?:sorry|axiom|native_decide)\b", code)
        if forbidden:
            raise SystemExit(f"Forbidden proof token in {path.relative_to(ROOT)}: {forbidden}")
        if path != AUDIT:
            declarations.update(public_theorems(code))
    expected = re.findall(r"^\s*#print\s+axioms\s+(\S+)\s*$", lean_code(AUDIT.read_text()), re.M)
    if not expected or len(expected) != len(set(expected)):
        raise SystemExit("The axiom audit must list distinct, fully qualified declarations")
    if set(expected) != declarations:
        raise SystemExit(f"Audit inventory mismatch: missing={sorted(declarations - set(expected))}; "
                         f"extra={sorted(set(expected) - declarations)}")

    version = checked("lake", "env", "lean", "--version")
    if EXPECTED_LEAN not in version or EXPECTED_LEAN_COMMIT not in version:
        raise SystemExit(f"Unexpected Lean version: {version}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    actual_mathlib = checked("git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
    if mathlib["rev"] != EXPECTED_MATHLIB or actual_mathlib != EXPECTED_MATHLIB:
        raise SystemExit(f"Unexpected Mathlib revision: manifest={mathlib['rev']}, actual={actual_mathlib}")
    targets = [".".join(p.relative_to(ROOT).with_suffix("").parts)
               for p in sources if p != AUDIT]
    write_json(LOGS / "environment.json", {
        "lean": version, "mathlib": actual_mathlib,
        "git_head": checked("git", "rev-parse", "HEAD"), "targets": targets,
        "source_sha256": hashes, "public_theorems": sorted(declarations),
        "restored_lake_cache": os.environ.get("RESTORED_LAKE_CACHE", ""),
    })

    # Never reuse task outputs, including when the verifier is invoked locally.
    # Dependency caches are left intact and validated by ordinary Lake traces.
    for subdir in ("lib/lean", "ir"):
        output = ROOT / ".lake/build" / subdir / "HeckeSkeleton/Moments/MOM_BASE"
        if output.is_symlink():
            output.unlink()
        elif output.exists():
            shutil.rmtree(output)
    build = logged_run(["lake", "build", *targets], LOGS / "lake-build.log")
    write_json(LOGS / "build-result.json", build)
    if build["exit_code"]:
        raise SystemExit(f"Lake compilation failed: {build['exit_code']}")

    options = tomllib.loads((ROOT / "lakefile.toml").read_text()).get("leanOptions", {})
    audit = logged_run(["lake", "env", "lean", "-j1", *option_flags(options), str(AUDIT)],
                       LOGS / "axioms.log")
    if audit["exit_code"]:
        raise SystemExit(f"Axiom audit compilation failed: {audit['exit_code']}")
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    rows = re.findall(pattern, (LOGS / "axioms.log").read_text(), re.S)
    records = {}
    for name, names in rows:
        if name in records:
            raise SystemExit(f"Duplicate axiom output: {name}")
        records[name] = {item.strip() for item in names.split(",") if item.strip()}
    if set(expected) != records.keys():
        raise SystemExit(f"Axiom output mismatch: missing={sorted(set(expected) - records.keys())}; "
                         f"extra={sorted(records.keys() - set(expected))}")
    violations = {name: sorted(records[name] - ALLOWED) for name in expected
                  if records[name] - ALLOWED}
    unchanged = all(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest
                    for path, digest in hashes.items())
    write_json(LOGS / "axioms.json", {
        "expected": expected, "allowed": sorted(ALLOWED),
        "records": {name: sorted(records[name]) for name in expected},
        "violations": violations, "source_unchanged": unchanged,
        "audit": audit, "complete": not violations and unchanged,
    })
    if violations or not unchanged:
        raise SystemExit(f"Axiom violations={violations}; source_unchanged={unchanged}")
    print(f"PASS: {len(sources)} task modules compiled; "
          f"{len(expected)} public theorems use only the three standard axioms", flush=True)


if __name__ == "__main__":
    main()
