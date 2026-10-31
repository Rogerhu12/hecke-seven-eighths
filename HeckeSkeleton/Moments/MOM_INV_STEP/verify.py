#!/usr/bin/env python3
"""Compile the canonical inverse single step and preserve kernel-audit evidence.

Run after `lake exe cache get` in the pinned repository. The compiler, import
search path, and package options come from this checkout's Lake environment.
Project objects are built from their real sources. A previous successful
object may be reused only when its source, options, complete project import
closure, pinned external environment and object hashes still match. The
recursive axiom audit itself is always recompiled.
"""
from __future__ import annotations

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
LOGS = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "mom-inv-step-verification"
OUT = ROOT / ".lake/build/lib/lean"
STATE = ROOT / ".lake/build/mom-inv-step-state.json"
TARGETS = sys.argv[1:] or ["HeckeSkeleton.Moments.MOM_INV_STEP.CoreAudit",
                         "HeckeSkeleton.Moments.MOM_INV_STEP.Audit"]
EXPECTED_LEAN = "4.35.0-rc3"
EXPECTED_LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
EXPECTED_MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
LOGS.mkdir(exist_ok=True)
OUT.mkdir(parents=True, exist_ok=True)


def checked(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


lean = checked("lake", "env", "which", "lean")
version = checked(lean, "--version")
if EXPECTED_LEAN not in version or EXPECTED_LEAN_COMMIT not in version:
    raise SystemExit(f"Unexpected Lean version: {version}")
manifest_bytes = (ROOT / "lake-manifest.json").read_bytes()
manifest = json.loads(manifest_bytes)
mathlib_entry = next(p for p in manifest["packages"] if p["name"] == "mathlib")
if mathlib_entry["rev"] != EXPECTED_MATHLIB:
    raise SystemExit("Unexpected Mathlib revision")
actual_mathlib = checked("git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
if actual_mathlib != EXPECTED_MATHLIB:
    raise SystemExit(f"Unexpected checked-out Mathlib revision: {actual_mathlib}")
env = os.environ.copy()
env["LEAN_PATH"] = checked("lake", "env", "printenv", "LEAN_PATH")
paths = [(ROOT / p).resolve() for p in env["LEAN_PATH"].split(os.pathsep)]
env["LEAN_PATH"] = os.pathsep.join(map(str, [OUT] + [p for p in paths if p != OUT]))
sysroot = Path(lean).resolve().parent.parent
paths.append(sysroot / "lib/lean")
external_paths = [path for path in paths if path != OUT]
config = tomllib.loads((ROOT / "lakefile.toml").read_text())
source_roots = [(ROOT, config.get("leanOptions", {}))]
for lib in config.get("lean_lib", []):
    directory = ROOT / lib.get("srcDir", ".")
    entry = (directory, config.get("leanOptions", {}))
    if entry not in source_roots:
        source_roots.append(entry)
vendor = ROOT / "vendor/class-field-theory"
vendor_config = tomllib.loads((vendor / "lakefile.toml").read_text())
for lib in vendor_config.get("lean_lib", []):
    directory = vendor / lib.get("srcDir", vendor_config.get("srcDir", "."))
    entry = (directory, vendor_config.get("leanOptions", {}))
    if entry not in source_roots:
        source_roots.append(entry)


def module_path(module: str, suffix: str) -> Path:
    return Path(*module.split(".")).with_suffix(suffix)


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


def imports(text: str) -> list[str]:
    """Read the Lean import header, excluding nested documentation comments."""
    output, index, depth = [], 0, 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == "/-":
            depth += 1
            output.extend("  ")
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            output.extend("  ")
            index += 2
        elif depth:
            output.append("\n" if text[index] == "\n" else " ")
            index += 1
        elif pair == "--":
            newline = text.find("\n", index)
            if newline < 0:
                break
            output.append("\n")
            index = newline + 1
        else:
            output.append(text[index])
            index += 1
    result = []
    for line in "".join(output).splitlines():
        line = line.strip()
        if not line or line in {"module", "prelude"}:
            continue
        match = re.fullmatch(
            r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+(?:\s+[\w.]+)*)", line)
        if not match:
            break
        result.extend(match.group(1).split())
    return result


nodes, order, seen, active = {}, [], set(), set()
external_environment = hashlib.sha256(version.encode() + manifest_bytes).hexdigest()
fingerprints = {}


def discover(module: str) -> None:
    if module in seen:
        return
    if module in active:
        raise RuntimeError(f"Import cycle: {module}")
    source = next(((root / module_path(module, ".lean"), root, options)
                   for root, options in source_roots
                   if (root / module_path(module, ".lean")).is_file()), None)
    if source is None:
        if not any((root / module_path(module, ".olean")).is_file() for root in external_paths):
            raise RuntimeError(f"Missing cached external module: {module}; run lake exe cache get")
        fingerprints[module] = hashlib.sha256(
            f"{external_environment}:{module}".encode()).hexdigest()
        seen.add(module)
        return
    path, root, options = source
    raw = path.read_bytes()
    deps = imports(raw.decode())
    active.add(module)
    for dep in deps:
        discover(dep)
    active.remove(module)
    seen.add(module)
    nodes[module] = {
        "path": path, "root": root, "options": options, "deps": deps,
        "source_sha256": hashlib.sha256(raw).hexdigest(),
    }
    fingerprints[module] = hashlib.sha256(json.dumps({
        "environment": external_environment,
        "source": nodes[module]["source_sha256"],
        "options": option_flags(options),
        "imports": [(dep, fingerprints[dep]) for dep in deps],
    }, sort_keys=True).encode()).hexdigest()
    order.append(module)


for target in TARGETS:
    discover(target)
(LOGS / "environment.json").write_text(json.dumps({
    "lean": version, "mathlib": actual_mathlib,
    "git_head": checked("git", "rev-parse", "HEAD"), "targets": TARGETS,
    "dependency_order": order,
}, indent=2) + "\n")
try:
    state = json.loads(STATE.read_text())
except (FileNotFoundError, json.JSONDecodeError):
    old_state = ROOT / ".lake/build/wire-low-hybrid-state.json"
    state = json.loads(old_state.read_text()) if old_state.is_file() else {}


def artifact_hashes(output: Path) -> dict[str, str]:
    # Include every emitted companion, especially .olean.private and .ir.sig.
    artifacts = list(output.parent.glob(output.stem + ".*"))
    return {str(path.relative_to(OUT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in artifacts if path.is_file()}


def reusable(module: str, output: Path) -> bool:
    old = state.get(module, {})
    if module.endswith("Audit") or old.get("fingerprint") != fingerprints[module]:
        return False
    return (old.get("exit_code") == 0 and output.is_file()
            and bool(old.get("artifacts"))
            and artifact_hashes(output) == old["artifacts"])


print(f"Verifying {len(order)} actual project modules", flush=True)
results = []
failed = set()
errors = []
finished = set()
workers = max(1, min(2, int(os.environ.get("WIRE_BUILD_WORKERS", "1"))))
positions = {module: index for index, module in enumerate(order, 1)}


def compile_module(module: str) -> tuple[dict, str, Path]:
    node = nodes[module]
    output = OUT / module_path(module, ".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    flags = option_flags(node["options"])
    command = [lean, "-j1", *flags, "-R", str(node["root"]), "-o", str(output), str(node["path"])]
    started = time.monotonic()
    result = subprocess.run(command, cwd=node["root"], env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    unchanged = hashlib.sha256(node["path"].read_bytes()).hexdigest() == node["source_sha256"]
    record = {
        "module": module, "source": str(node["path"].relative_to(ROOT)),
        "source_sha256": node["source_sha256"], "source_unchanged": unchanged,
        "exit_code": result.returncode, "seconds": round(time.monotonic() - started, 3),
        "command": command,
        "fingerprint": fingerprints[module], "reused": False,
    }
    return record, result.stdout, output


def write_json_atomic(path: Path, value: object) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def save_results() -> None:
    write_json_atomic(LOGS / "results.json", results)


print(f"At most {workers} single-threaded Lean processes", flush=True)
pending = list(order)
running = {}
with ThreadPoolExecutor(max_workers=workers) as executor:
    while pending or running:
        for module in list(pending):
            deps = nodes[module]["deps"]
            if any(dep in nodes and dep not in finished for dep in deps):
                continue
            index = positions[module]
            blocked = [dep for dep in deps if dep in failed]
            output = OUT / module_path(module, ".olean")
            if blocked:
                failed.add(module)
                finished.add(module)
                pending.remove(module)
                print(f"[{index}/{len(order)}] BLOCKED {module}: {', '.join(blocked)}", flush=True)
                results.append({"module": module, "blocked_by": blocked})
                save_results()
            elif reusable(module, output):
                finished.add(module)
                pending.remove(module)
                print(f"[{index}/{len(order)}] REUSED {module} (verified source/import/object hashes)", flush=True)
                results.append({**state[module], "module": module, "reused": True})
                save_results()
            elif len(running) < workers:
                pending.remove(module)
                print(f"[{index}/{len(order)}] BUILD {module}", flush=True)
                running[executor.submit(compile_module, module)] = module
        if not running:
            if pending:
                raise RuntimeError(f"Unresolved project dependencies: {pending}")
            break
        completed, _ = wait(running, return_when=FIRST_COMPLETED)
        for future in completed:
            module = running.pop(future)
            record, stdout, output = future.result()
            finished.add(module)
            if record["exit_code"] or not record["source_unchanged"]:
                state.pop(module, None)
                failed.add(module)
                errors.append(module)
            else:
                record["artifacts"] = artifact_hashes(output)
                state[module] = record
            write_json_atomic(STATE, state)
            results.append(record)
            (LOGS / (module + ".log")).write_text(json.dumps(record, indent=2) + "\n\n" + stdout)
            save_results()
            print(f"[{positions[module]}/{len(order)}] EXIT {record['exit_code']} "
                  f"{record['seconds']}s {module}", flush=True)
            if stdout:
                print(stdout, flush=True)
# Every requested declaration is audited recursively by the kernel command.
# Record each successful audit even when another target failed. Compilation
# failures below still make the complete workflow fail.
allowed = {"propext", "Classical.choice", "Quot.sound"}
all_axioms = {}
for target in TARGETS:
    if not target.endswith("Audit") or target in failed:
        continue
    source = nodes[target]["path"].read_text()
    expected = set(re.findall(r"^#print axioms (\S+)", source, re.M))
    if not expected:
        raise SystemExit("Empty axiom audit")
    output = (LOGS / (target + ".log")).read_text()
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    records = dict(re.findall(pattern, output, re.S))
    missing = expected - records.keys()
    if missing:
        raise SystemExit(f"Missing kernel axiom records: {sorted(missing)}")
    audit = {}
    for name in sorted(expected):
        axioms = {x.strip() for x in records[name].split(",") if x.strip()}
        if axioms - allowed:
            raise SystemExit(f"{name}: unexpected axioms {sorted(axioms - allowed)}")
        audit[name] = sorted(axioms)
    all_axioms.update(audit)
    (LOGS / "axioms.json").write_text(json.dumps(all_axioms, indent=2) + "\n")
    print(f"PASS: {len(expected)} declarations; recursive axioms within {sorted(allowed)}")
if failed:
    print(f"FAIL: {len(errors)} compilation failures; {len(failed) - len(errors)} blocked modules", flush=True)
    print("\n".join(errors), flush=True)
    raise SystemExit(1)
print(f"PASS: verified actual project import closure for {', '.join(TARGETS)}", flush=True)
