#!/usr/bin/env python3
"""Build all completed T1/T2 modules and audit their loaded V2 environment.

This is an additional diagnostic gate. It does not replace the complete
V2 build, the repository build, or the agreed full-V2 batch boundary.
Its model is the published S3/S5 driver at commit
29eecadbb7b4ca6f3dfcc2fbe73ff357a37de881. Source-token handling, command
logging, and the 600-second / 15-second Watcher are shared with build.py.
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
EVIDENCE = ROOT / "v2-t1-t2-build"
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
NAMESPACE = "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks"
GROUP_ID = "t1_t2"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
OWNED_MODULES = (
    "FirstPhysicalMaskBounds",
    "FirstSourceCarrierBounds",
    "FirstZeroCentral",
    "FirstZeroColumnWindows",
    "FirstZeroFactorization",
    "FirstZeroInputBounds",
    "FirstZeroMaskBounds",
    "FirstZeroNormalization",
    "FirstZeroProfileBounds",
    "FirstZeroSignedBound",
    "FirstZeroUniformEstimate",
    "SecondZeroCoefficients",
    "SecondZeroDivisor",
    "SecondZeroFactors",
    "SecondZeroFirstMass",
    "SecondZeroFrozenBounds",
    "SecondZeroLocal",
    "SecondZeroLocalEstimate",
    "SecondZeroNormalization",
    "SecondZeroOrbitMultiplicity",
    "SecondZeroPoolMass",
    "SecondZeroRowSizeBounds",
    "SecondZeroStage",
    "SecondZeroTransport",
    "SecondZeroUniformEstimate",
    "SourceEqualityTransport",
    "TasksFirstZero",
    "TasksSecondZero",
)
THEOREMS = {
    "TasksFirstZero": "firstZero",
    "TasksSecondZero": "secondZero",
}
FORBIDDEN = re.compile(r"\b(?:sorry|axiom|admit|native_decide|sorryAx)\b")
CONFIG_PATHS = (
    "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json",
    ".github/v2/build.py", ".github/v2/t1_t2.py", ".github/v2/manifest.json",
    ".github/workflows/mom-v2-t1-t2.yml",
)
REQUIRED_CONFIG_PATHS = (
    "lean-toolchain", "lake-manifest.json", ".github/v2/build.py",
    ".github/v2/t1_t2.py", ".github/v2/manifest.json",
    ".github/workflows/mom-v2-t1-t2.yml",
)

# These aliases preserve the shared implementations and their Watcher.
code_only = v2_build.code_only
logged = v2_build.logged


def source_snapshots() -> dict[str, str]:
    # A superset of the loaded V2 closure. The exact Git head/tree and Lake
    # manifest identify non-V2 source dependencies resolved by Lake.
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(TASK.glob("*.lean"))
    }


def preflight() -> tuple[list[str], dict[str, str]]:
    errors = []
    manifest_path = ROOT / ".github/v2/manifest.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        groups = manifest["groups"]
        selected = [group for group in groups if group.get("id") == GROUP_ID]
        if len(selected) != 1:
            errors.append("The manifest must contain exactly one t1_t2 group")
        else:
            group = selected[0]
            if group.get("proved") is not True:
                errors.append("The t1_t2 manifest group must be marked proved")
            if group.get("modules") != list(OWNED_MODULES):
                errors.append("The t1_t2 manifest must match the fixed 28-module list exactly")
        for module in OWNED_MODULES:
            owners = [group.get("id") for group in groups
                      if module in group.get("modules", [])]
            if owners != [GROUP_ID]:
                errors.append(f"Unexpected manifest ownership for {module}: {owners!r}")
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as exception:
        errors.append(f"Cannot validate the manifest: {type(exception).__name__}: {exception}")
    if len(OWNED_MODULES) != 28 or len(set(OWNED_MODULES)) != 28:
        errors.append("The diagnostic driver must list exactly 28 distinct T1/T2 modules")
    if (v2_build.MODULE_TIMEOUT_SECONDS, v2_build.WATCH_INTERVAL_SECONDS) != (300, 15):
        errors.append("The shared Watcher must use a 300-second limit and 15-second polling")
    for name in REQUIRED_CONFIG_PATHS:
        if not (ROOT / name).is_file():
            errors.append("Missing verification input: " + name)
    if not any((ROOT / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
        errors.append("Missing Lake project configuration")
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
    snapshots = source_snapshots()
    if not snapshots:
        errors.append("No V2 source files found")
    return errors, snapshots


def audit_source() -> str:
    # Import every completed module, including any helper not reachable from
    # the two public Tasks. The fresh environment is exactly this import closure.
    imports = "\n".join("import " + PREFIX + "." + module for module in OWNED_MODULES)
    checks = "\n".join("#check " + NAMESPACE + "." + theorem
                       for theorem in THEOREMS.values())
    return imports + "\nimport Lean.Elab.Command\nimport Lean.Util.CollectAxioms\n\n" + checks + """

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let modulePrefix : Name := `HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let moduleNames := env.header.moduleNames
  let names := (env.constants.toList.filterMap fun (name, _) =>
    let fromV2Module := match env.getModuleIdxFor? name with
      | some idx => modulePrefix.isPrefixOf (moduleNames[idx.toNat]!)
      | none => false
    if nsPrefix.isPrefixOf (privateToUserName name) || fromV2Module then
      some name
    else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No V2 declarations found"
  let required : Array Name := #[
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.firstZero,
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.secondZero]
  for name in required do
    unless names.contains name do
      throwError "Missing public T1/T2 theorem in audit environment: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"T1_T2_AXIOMS_PASSED: {names.size} declarations"
"""


def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    # logged resolves its globals in build.py. Redirect only evidence output;
    # its code_only, logged, Watcher and timeout policy remain unchanged.
    v2_build.EVIDENCE = EVIDENCE
    v2_build.WATCHDOG_RESULTS.clear()
    start = time.monotonic()
    errors, snapshots = preflight()
    config_snapshots = {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        for name in CONFIG_PATHS if (ROOT / name).is_file()
    }
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    tree = subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], text=True).strip()
    expected_head = os.environ.get("EXPECTED_HEAD_SHA", "")
    if not re.fullmatch(r"[0-9a-f]{40}", expected_head):
        errors.append("EXPECTED_HEAD_SHA must identify the exact PR head commit")
    elif head != expected_head:
        errors.append(f"Checkout head {head} does not match expected PR head {expected_head}")
    audit_path = EVIDENCE / "T1T2_AxiomAudit.lean"
    audit_path.write_text(audit_source(), encoding="utf-8")
    audit_sha256 = hashlib.sha256(audit_path.read_bytes()).hexdigest()
    environment = {
        "diagnostic_only": True,
        "head": head,
        "expected_head": expected_head,
        "tree": tree,
        "toolchain": ((ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
                      if (ROOT / "lean-toolchain").is_file() else None),
        "manifest_group": GROUP_ID,
        "targets": [PREFIX + "." + module for module in OWNED_MODULES],
        "public_theorems": [NAMESPACE + "." + theorem for theorem in THEOREMS.values()],
        "owned_modules": list(OWNED_MODULES),
        "source_sha256": snapshots,
        "verification_sha256": config_snapshots,
        "audit_source_sha256": audit_sha256,
        "allowed_axioms": ALLOWED,
        "module_timeout_seconds": v2_build.MODULE_TIMEOUT_SECONDS,
        "watch_interval_seconds": v2_build.WATCH_INTERVAL_SECONDS,
        "audit_scope": "Every loaded V2 declaration, including private and generated names, recursively",
        "reference_commit": "29eecadbb7b4ca6f3dfcc2fbe73ff357a37de881",
    }
    (EVIDENCE / "environment.json").write_text(
        json.dumps(environment, indent=2) + "\n", encoding="utf-8")
    preflight_text = ("\n".join(errors) + "\n" if errors else
                      "PASS: all 28 completed T1/T2 modules match the manifest; "
                      "both public Tasks declarations and exact PR head are present.\n")
    (EVIDENCE / "preflight.log").write_text(preflight_text, encoding="utf-8")
    print(preflight_text, end="", flush=True)
    results = {
        "diagnostic_only": True,
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
                                     for module in OWNED_MODULES)], "build.log")
            if results["build_exit"] == 0:
                results["audit_exit"] = logged(
                    ["lake", "env", "lean", str(audit_path)], "axioms.log")
                output = (EVIDENCE / "axioms.log").read_text(encoding="utf-8")
                markers = re.findall(r"T1_T2_AXIOMS_PASSED: (\d+) declarations", output)
                results["audit_success_marker"] = len(markers) == 1 and int(markers[0]) >= 2
                if len(markers) == 1:
                    results["audited_declaration_count"] = int(markers[0])
        except Exception as exception:
            message = f"{type(exception).__name__}: {exception}"
            errors.append(message)
            (EVIDENCE / "driver-error.log").write_text(message + "\n", encoding="utf-8")
            print(message, file=sys.stderr, flush=True)
    for name, digest in {**snapshots, **config_snapshots}.items():
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            errors.append("Source or verification input changed during verification: " + name)
    if set(source_snapshots()) != set(snapshots):
        errors.append("The V2 source inventory changed during verification")
    if not audit_path.is_file() or hashlib.sha256(audit_path.read_bytes()).hexdigest() != audit_sha256:
        errors.append("The generated fresh Lean audit changed during verification")
    final_head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    if final_head != head:
        errors.append("Git HEAD changed during verification: " + final_head)
    results["elapsed_seconds"] = time.monotonic() - start
    success = (not errors and results["build_exit"] == 0
               and results["audit_exit"] == 0 and results["audit_success_marker"])
    results["success"] = success
    (EVIDENCE / "result.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    summary = ("# MOM Engine Step V2 — T1/T2 diagnostic\n\n"
               + f"- Exact head: `{head}`\n"
               + "- Build targets: all 28 completed T1/T2 modules and their actual dependencies\n"
               + "- Required Tasks: `firstZero`, `secondZero`\n"
               + f"- Lake exit: {results['build_exit']}\n"
               + f"- Fresh Lean audit exit: {results['audit_exit']}\n"
               + f"- Loaded V2 declarations audited: {results.get('audited_declaration_count', 0)}\n"
               + f"- Per-module Watcher: {v2_build.MODULE_TIMEOUT_SECONDS}s, "
                 f"{v2_build.WATCH_INTERVAL_SECONDS}s polling\n"
               + f"- Result: {'PASS' if success else 'FAIL'}\n"
               + "- Diagnostic only: the complete V2 and repository gates remain required.\n"
               + "- The full-V2 batch boundary is unchanged.\n")
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
