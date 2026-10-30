#!/usr/bin/env python3
"""Compile the actual exterior wiring in dependency order and preserve evidence.

Run after `lake exe cache get` in the pinned repository. The compiler, import
search path, and package options come from this checkout's Lake environment.
Every project module is compiled from its real source; external cached
dependencies are the versions selected by lake-manifest.json.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / "wire-low-hybrid-verification"
OUT = ROOT / ".lake/build/lib/lean"
TARGETS = sys.argv[1:] or ["HeckeSkeleton.LowHybridExteriorAudit"]
EXPECTED_LEAN = "4.35.0-rc3"
EXPECTED_MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
LOGS.mkdir(exist_ok=True)
OUT.mkdir(parents=True, exist_ok=True)


def checked(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


lean = checked("lake", "env", "which", "lean")
version = checked(lean, "--version")
if EXPECTED_LEAN not in version:
    raise SystemExit(f"Unexpected Lean version: {version}")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
mathlib_entry = next(p for p in manifest["packages"] if p["name"] == "mathlib")
if mathlib_entry["rev"] != EXPECTED_MATHLIB:
    raise SystemExit("Unexpected Mathlib revision")
env = os.environ.copy()
env["LEAN_PATH"] = checked("lake", "env", "printenv", "LEAN_PATH")
paths = [Path(p) for p in env["LEAN_PATH"].split(os.pathsep)]
env["LEAN_PATH"] = os.pathsep.join(map(str, [OUT] + [p for p in paths if p != OUT]))
sysroot = Path(lean).resolve().parent.parent
paths.append(sysroot / "lib/lean")
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


def discover(module: str) -> None:
    if module in seen:
        return
    if module in active:
        raise RuntimeError(f"Import cycle: {module}")
    source = next(((root / module_path(module, ".lean"), root, options)
                   for root, options in source_roots
                   if (root / module_path(module, ".lean")).is_file()), None)
    if source is None:
        if not any((root / module_path(module, ".olean")).is_file() for root in paths):
            raise RuntimeError(f"Missing cached external module: {module}; run lake exe cache get")
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
    order.append(module)


for target in TARGETS:
    discover(target)
(LOGS / "environment.json").write_text(json.dumps({
    "lean": version, "mathlib": EXPECTED_MATHLIB,
    "git_head": checked("git", "rev-parse", "HEAD"), "targets": TARGETS,
    "dependency_order": order,
}, indent=2) + "\n")
print(f"Compiling {len(order)} actual project modules", flush=True)
results = []
for index, module in enumerate(order, 1):
    node = nodes[module]
    output = OUT / module_path(module, ".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    flags = option_flags(node["options"])
    command = [lean, "-j1", *flags, "-R", str(node["root"]), "-o", str(output), str(node["path"])]
    print(f"[{index}/{len(order)}] {module}", flush=True)
    started = time.monotonic()
    result = subprocess.run(command, cwd=node["root"], env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    unchanged = hashlib.sha256(node["path"].read_bytes()).hexdigest() == node["source_sha256"]
    record = {
        "module": module, "source": str(node["path"].relative_to(ROOT)),
        "source_sha256": node["source_sha256"], "source_unchanged": unchanged,
        "exit_code": result.returncode, "seconds": round(time.monotonic() - started, 3),
        "command": command,
    }
    results.append(record)
    (LOGS / (module + ".log")).write_text(json.dumps(record, indent=2) + "\n\n" + result.stdout)
    (LOGS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(result.stdout, flush=True)
    if result.returncode or not unchanged:
        raise SystemExit(result.returncode or 2)
print("PASS: actual exterior wiring and recursive axiom guard", flush=True)
