#!/usr/bin/env python3
"""Build S3/S5 and strictly audit their entire loaded V2 environment.

This is an additional diagnostic gate. It does not replace the complete
V2 build or the repository build. Command logging (including any shared
watchdog) and Lean-source token handling come from the existing V2 driver.
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

import build as v2_build

ROOT = Path.cwd()
TASK = ROOT / "HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2"
EVIDENCE = ROOT / "v2-s3-s5-build"
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
NAMESPACE = "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
TARGETS = ("TasksAmplification", "TasksNominalGeometry")
THEOREMS = {
    "TasksAmplification": "amplification",
    "TasksNominalGeometry": "nominalGeometry",
}
OWNED_MODULES = (
    "S3Assembly",
    "S3Energy",
    "S3ExpansionData",
    "S3FrozenDivisor",
    "S3OriginalColumnBound",
    "S3PoolData",
    "S3RowExponent",
    "S3RowTransport",
    "S3UniformDensity",
    "S3Windows",
    "S5ClassIdeals",
    "S5GeometryConstruction",
    "S5NominalLedger",
    "S5RowWindow",
    "S5SupportWindow",
    *TARGETS,
)
FORBIDDEN = re.compile(r"\b(?:sorry|axiom|admit|native_decide|sorryAx)\b")

# These are the shared implementations, not independent subprocess monitors.
code_only = v2_build.code_only
logged = v2_build.logged


def preflight() -> tuple[list[str], dict[str, str]]:
    errors = []
    discovered = {path.stem for pattern in ("S3*.lean", "S5*.lean")
                  for path in TASK.glob(pattern)} | set(TARGETS)
    if discovered != set(OWNED_MODULES):
        errors.append("Owned S3/S5 module inventory changed: "
                      + repr(sorted(discovered.symmetric_difference(OWNED_MODULES))))
    for module in OWNED_MODULES:
        path = TASK / (module + ".lean")
        if not path.is_file():
            errors.append("Missing owned source: " + str(path.relative_to(ROOT)))
            continue
        source = code_only(path.read_text(encoding="utf-8"))
        for match in FORBIDDEN.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: forbidden {match.group()}")
        if module in THEOREMS:
            theorem = THEOREMS[module]
            if not re.search(r"\btheorem\s+" + re.escape(theorem) + r"\b", source):
                errors.append("Missing public theorem declaration: " + NAMESPACE + "." + theorem)
            if not re.search(r"\bnamespace\s+" + re.escape(NAMESPACE) + r"\b", source):
                errors.append("Missing public task namespace in " + module)
    # Hash every V2 source, a superset of the loaded V2 import closure.
    # The exact Git head and Lake manifest identify the remaining dependencies.
    snapshots = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in sorted(TASK.glob("*.lean"))}
    if not snapshots:
        errors.append("No V2 source files found")
    return errors, snapshots


def audit_source() -> str:
    imports = "\n".join("import " + PREFIX + "." + module for module in TARGETS)
    checks = "\n".join("#check " + NAMESPACE + "." + THEOREMS[module]
                       for module in TARGETS)
    return imports + "\nimport Lean.Elab.Command\nimport Lean.Util.CollectAxioms\n\n" + checks + """

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let names := (env.constants.toList.filterMap fun (name, _) =>
    if nsPrefix.isPrefixOf (privateToUserName name) then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No V2 declarations found"
  let required : Array Name := #[
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.amplification,
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.nominalGeometry]
  for name in required do
    unless names.contains name do
      throwError "Missing public S3/S5 theorem in audit environment: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"S3_S5_AXIOMS_PASSED: {names.size} declarations"
"""


def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    # logged resolves its module globals at call time. This preserves the
    # upstream implementation and automatically inherits its watchdog updates.
    v2_build.EVIDENCE = EVIDENCE
    start = time.monotonic()
    errors, snapshots = preflight()
    config_paths = (
        "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json",
        ".github/v2/build.py", ".github/v2/s3_s5.py",
        ".github/v2/manifest.json", ".github/workflows/mom-v2-s3-s5.yml",
    )
    config_snapshots = {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        for name in config_paths if (ROOT / name).is_file()
    }
    environment = {
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "targets": [PREFIX + "." + module for module in TARGETS],
        "public_theorems": [NAMESPACE + "." + THEOREMS[module] for module in TARGETS],
        "owned_modules": list(OWNED_MODULES),
        "source_sha256": snapshots,
        "verification_sha256": config_snapshots,
        "allowed_axioms": ALLOWED,
        "module_timeout_seconds": v2_build.MODULE_TIMEOUT_SECONDS,
        "watch_interval_seconds": v2_build.WATCH_INTERVAL_SECONDS,
        "audit_scope": "Every loaded V2 declaration, including private and generated names, recursively",
    }
    (EVIDENCE / "environment.json").write_text(
        json.dumps(environment, indent=2) + "\n", encoding="utf-8")
    preflight_text = ("\n".join(errors) + "\n" if errors else
                      f"PASS: {len(OWNED_MODULES)} owned modules; both public theorem declarations present.\n")
    (EVIDENCE / "preflight.log").write_text(preflight_text, encoding="utf-8")
    print(preflight_text, end="", flush=True)
    results = {
        "preflight_passed": not errors,
        "owned_module_count": len(OWNED_MODULES),
        "build_exit": None,
        "audit_exit": None,
        "audit_success_marker": False,
        "watchdogs": v2_build.WATCHDOG_RESULTS,
        "module_timeout_seconds": v2_build.MODULE_TIMEOUT_SECONDS,
        "watch_interval_seconds": v2_build.WATCH_INTERVAL_SECONDS,
        "errors": errors,
    }
    if not errors:
        try:
            results["build_exit"] = logged(
                ["lake", "build", *("+" + PREFIX + "." + module + ":olean"
                                     for module in TARGETS)], "build.log")
            if results["build_exit"] == 0:
                audit_path = EVIDENCE / "S3S5_AxiomAudit.lean"
                audit_path.write_text(audit_source(), encoding="utf-8")
                results["audit_exit"] = logged(
                    ["lake", "env", "lean", str(audit_path)], "axioms.log")
                output = (EVIDENCE / "axioms.log").read_text(encoding="utf-8")
                marker = re.search(r"S3_S5_AXIOMS_PASSED: (\d+) declarations", output)
                results["audit_success_marker"] = marker is not None
                if marker:
                    results["audited_declaration_count"] = int(marker.group(1))
        except Exception as exception:
            message = f"{type(exception).__name__}: {exception}"
            errors.append(message)
            (EVIDENCE / "driver-error.log").write_text(message + "\n", encoding="utf-8")
            print(message, file=sys.stderr, flush=True)
    for name, digest in {**snapshots, **config_snapshots}.items():
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            errors.append("Source or verification input changed during verification: " + name)
    results["elapsed_seconds"] = time.monotonic() - start
    success = (not errors and results["build_exit"] == 0
               and results["audit_exit"] == 0 and results["audit_success_marker"])
    results["success"] = success
    (EVIDENCE / "result.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    summary = ("# MOM Engine Step V2 — S3/S5\n\n"
               + f"- Exact head: `{environment['head']}`\n"
               + "- Build targets: `TasksAmplification`, `TasksNominalGeometry` and their dependencies\n"
               + f"- Owned sources checked: {len(OWNED_MODULES)}\n"
               + f"- Lake exit: {results['build_exit']}\n"
               + f"- Fresh Lean audit exit: {results['audit_exit']}\n"
               + f"- Loaded V2 declarations audited: {results.get('audited_declaration_count', 0)}\n"
               + f"- Result: {'PASS' if success else 'FAIL'}\n"
               + "- The complete V2 and repository gates remain required.\n")
    if errors:
        summary += "\nVerification errors:\n\n" + "\n".join("- " + error for error in errors) + "\n"
    (EVIDENCE / "summary.md").write_text(summary, encoding="utf-8")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
            stream.write(summary)
    print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
