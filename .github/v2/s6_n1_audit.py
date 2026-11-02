#!/usr/bin/env python3
"""Supplement the full V2 and whole-project gates with exact S6/N1 evidence.

Build and import only the two task entries. Scan the fixed 31-module owned
inventory, require every owned module to be loaded, and freshly audit every
loaded V2 declaration by source module or namespace. No old audit is reused.
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

# Do not create configuration-directory bytecode while checking source identity.
sys.dont_write_bytecode = True
import build as shared

ROOT = Path(__file__).resolve().parents[2]
TASK = ROOT / "HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2"
EVIDENCE = ROOT / "v2-s6-n1-build"
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
BRANCH = "cloud/mom-v2-s6-n1"
ENTRY_MODULES = ("TasksFiniteLeaves", "TasksOriginalAtoms")
WARMUP_MODULES = ("RawContracts", "OrdinaryData")
EXPECTED_GROUPS = {
    "s6_n1_helpers": [
        "FiniteLeavesCover",
        "FiniteLeavesOriginalSupport",
        "FiniteLeavesTraceCover",
        "FiniteLeavesSupport",
        "FiniteLeavesIntegral",
        "FiniteLeavesAssembly",
        "OrdinaryLeafBinding",
        "OrdinarySourceFacts",
        "OrdinaryRectangleFactors",
        "OrdinarySourceTransport",
        "OrdinaryAtomModel",
        "OrdinaryOccurrenceFacts",
        "OrdinaryPhaseFacts",
        "OrdinaryPointTransport",
        "OrdinaryLeafLocations",
        "OrdinaryDivisorGate",
        "OrdinaryCharacterFacts",
        "OrdinaryAtomExtraction",
        "OrdinaryNormPower",
        "OrdinaryScaleFacts",
        "OrdinaryOriginalTerms",
        "OrdinaryNormProfile",
        "OrdinaryOriginalCoordinates",
        "OrdinaryMultiplierTransport",
        "OrdinaryPhaseCoefficients",
        "OrdinaryRawAtomData",
        "OrdinaryFromAtoms",
        "OrdinaryFirstAtomFormula",
        "OrdinaryRawAtomFormula"
    ],
    "s6": [
        "TasksFiniteLeaves"
    ],
    "n1": [
        "TasksOriginalAtoms"
    ]
}
OWN_MODULES = tuple(module for modules in EXPECTED_GROUPS.values() for module in modules)
REQUIRED = (
    "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.finiteLeaves",
    "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.originalAtoms",
)
ALLOWED = ("propext", "Classical.choice", "Quot.sound")
SUCCESS_MARKER = "V2_S6_N1_AXIOMS_PASSED:"
REQUIRED_MARKER = "REQUIRED_V2_DECLARATION_PRESENT: "
MODULE_MARKER = "REQUIRED_S6_N1_MODULE_PRESENT: "
FORBIDDEN = re.compile(r"\b(?:axiom|native_decide|admit|sorryAx|sorry)\b")
CONFIG_DIRS = (
    ".github/v2",
    ".github/workflows",
    ".github/actions/restore-lake-cache",
)
ROOT_CONFIG = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
REQUIRED_CONFIG = (
    ".github/v2/manifest.json",
    ".github/v2/build.py",
    ".github/v2/s6_n1_audit.py",
    ".github/workflows/mom-v2-s6-n1-proofs.yml",
    ".github/workflows/mom-engine-step-v2.yml",
    ".github/workflows/integration-build.yml",
    ".github/actions/restore-lake-cache/action.yml",
    *ROOT_CONFIG,
)

AUDIT_BODY = r"""
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modulePrefix : Name := `HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let declarationPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let moduleNames := env.header.moduleNames
  let requiredModules : Array Name := #[__MODULES__]
  for moduleName in requiredModules do
    unless moduleNames.contains moduleName do
      throwError "Required S6/N1 module missing: {moduleName}"
    logInfo m!"REQUIRED_S6_N1_MODULE_PRESENT: {moduleName}"
  let names := (env.constants.toList.filterMap fun (name, _) =>
    let fromV2Module := match env.getModuleIdxFor? name with
      | some idx => modulePrefix.isPrefixOf (moduleNames[idx.toNat]!)
      | none => false
    if fromV2Module || declarationPrefix.isPrefixOf (privateToUserName name)
      then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No loaded V2 declarations found"
  let required : Array Name := #[__REQUIRED__]
  for requiredName in required do
    unless names.contains requiredName do
      throwError "Required S6/N1 declaration missing: {requiredName}"
    logInfo m!"REQUIRED_V2_DECLARATION_PRESENT: {requiredName}"
  let permitted : Array Name := #[__ALLOWED__]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"V2_S6_N1_AXIOMS_PASSED: {names.size} declarations"
"""


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_snapshot() -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): digest(path)
        for path in sorted(TASK.rglob("*.lean"))
    }


def configuration_snapshot() -> dict[str, str]:
    paths = {ROOT / name for name in ROOT_CONFIG if (ROOT / name).is_file()}
    for directory in CONFIG_DIRS:
        for path in (ROOT / directory).rglob("*"):
            if (path.is_file() and "__pycache__" not in path.parts
                    and path.suffix not in (".pyc", ".pyo")):
                paths.add(path)
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(paths)}


def git_output(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def tracked_input_status() -> str:
    return git_output(
        "status", "--porcelain=v1", "--untracked-files=all", "--",
        str(TASK.relative_to(ROOT)), *CONFIG_DIRS, *ROOT_CONFIG,
    )


def validate_inputs() -> list[str]:
    errors = []
    if len(OWN_MODULES) != 31 or len(set(OWN_MODULES)) != 31:
        errors.append("The fixed S6/N1 inventory must contain 31 distinct modules")
    for name in REQUIRED_CONFIG:
        if not (ROOT / name).is_file():
            errors.append("Required configuration missing: " + name)
    try:
        manifest = json.loads((ROOT / ".github/v2/manifest.json").read_text(encoding="utf-8"))
        groups = manifest.get("groups") if isinstance(manifest, dict) else None
        if not isinstance(groups, list) or any(not isinstance(group, dict) for group in groups):
            raise ValueError("manifest.groups must be an array of objects")
        for group_id, expected in EXPECTED_GROUPS.items():
            matches = [group for group in groups if group.get("id") == group_id]
            if len(matches) != 1:
                errors.append("Expected exactly one manifest group: " + group_id)
                continue
            group = matches[0]
            modules = group.get("modules")
            if group.get("proved") is not True:
                errors.append("Owned group is not proved:true: " + group_id)
            if (not isinstance(modules, list)
                    or any(not isinstance(module, str) for module in modules)
                    or sorted(modules) != sorted(expected)):
                errors.append("Fixed module inventory mismatch: " + group_id)
        for group in groups:
            modules = group.get("modules", [])
            if group.get("id") not in EXPECTED_GROUPS and isinstance(modules, list):
                duplicates = sorted(set(OWN_MODULES).intersection(
                    module for module in modules if isinstance(module, str)))
                if duplicates:
                    errors.append("Owned modules duplicated outside owned groups: " + ", ".join(duplicates))
    except (OSError, ValueError) as error:
        errors.append("Cannot validate manifest: " + str(error))
    for module in OWN_MODULES:
        path = TASK / (module + ".lean")
        if not path.is_file():
            errors.append("Required module missing: " + str(path.relative_to(ROOT)))
            continue
        try:
            if FORBIDDEN.search(shared.code_only(path.read_text(encoding="utf-8"))):
                errors.append("Forbidden proof token: " + str(path.relative_to(ROOT)))
        except OSError as error:
            errors.append("Cannot read owned module: " + str(error))
    if tuple(shared.ALLOWED) != ALLOWED:
        errors.append("Shared driver permitted axioms differ from the three standard axioms")
    return errors


def audit_source() -> str:
    imports = "\n".join("import " + PREFIX + "." + name for name in ENTRY_MODULES)
    body = AUDIT_BODY.replace(
        "__REQUIRED__", ", ".join(chr(96) + name for name in REQUIRED)
    ).replace(
        "__ALLOWED__", ", ".join(chr(96) + name for name in ALLOWED)
    ).replace(
        "__MODULES__", ", ".join(chr(96) + PREFIX + "." + name for name in OWN_MODULES)
    )
    return imports + "\n" + body


def snapshot_safely(function, label: str, errors: list[str]) -> dict[str, str]:
    try:
        return function()
    except OSError as error:
        errors.append("Cannot snapshot " + label + ": " + str(error))
        return {}


def git_safely(args: tuple[str, ...], errors: list[str]) -> str:
    try:
        return git_output(*args)
    except (OSError, subprocess.SubprocessError) as error:
        errors.append("Cannot inspect Git " + " ".join(args) + ": " + str(error))
        return ""


def status_safely(errors: list[str]) -> str:
    try:
        return tracked_input_status()
    except (OSError, subprocess.SubprocessError) as error:
        errors.append("Cannot inspect input status: " + str(error))
        return ""


def main() -> int:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    os.chdir(ROOT)
    shared.ROOT = ROOT
    shared.EVIDENCE = EVIDENCE
    shared.WATCHDOG_RESULTS.clear()
    start = time.monotonic()
    errors = validate_inputs()
    head = git_safely(("rev-parse", "HEAD"), errors)
    expected_head = os.environ.get("S6_N1_EXPECTED_HEAD", "")
    source_branch = os.environ.get("S6_N1_SOURCE_BRANCH", "")
    if expected_head and head != expected_head:
        errors.append("Checkout HEAD differs from the requested exact head")
    if source_branch and source_branch != BRANCH:
        errors.append("This supplementary job is restricted to " + BRANCH)
    status_before = status_safely(errors)
    if status_before:
        errors.append("V2 source or verification configuration differs from the checkout HEAD")
    before_sources = snapshot_safely(source_snapshot, "V2 sources", errors)
    before_configuration = snapshot_safely(configuration_snapshot, "configuration", errors)
    if not before_sources:
        errors.append("No V2 source files found")
    targets = ["+" + PREFIX + "." + name + ":olean" for name in ENTRY_MODULES]
    audit_path = EVIDENCE / "S6N1_AxiomAudit.lean"
    audit_path.write_text(audit_source(), encoding="utf-8")
    audit_hash = digest(audit_path)
    environment = {
        "head": head,
        "expected_head": expected_head,
        "source_branch": source_branch,
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
            if (ROOT / "lean-toolchain").is_file() else None,
        "scope": "s6_n1_proofs",
        "supplementary_check": True,
        "entry_modules": ENTRY_MODULES,
        "owned_groups": EXPECTED_GROUPS,
        "owned_module_count": len(OWN_MODULES),
        "targets": targets,
        "warmup_order": WARMUP_MODULES,
        "warmup_targets": {name: "+" + PREFIX + "." + name + ":olean" for name in WARMUP_MODULES},
        "required_declarations": REQUIRED,
        "allowed_axioms": ALLOWED,
        "source_sha256": before_sources,
        "configuration_sha256": before_configuration,
        "audit_sha256": audit_hash,
        "audit_selection": "all loaded V2 module declarations or V2 namespace declarations",
        "module_timeout_seconds": shared.MODULE_TIMEOUT_SECONDS,
        "watch_interval_seconds": shared.WATCH_INTERVAL_SECONDS,
        "input_status_before": status_before,
    }
    (EVIDENCE / "environment.json").write_text(
        json.dumps(environment, indent=2) + "\n", encoding="utf-8"
    )
    warmup_exits = {name: None for name in WARMUP_MODULES}
    build_exit = None
    audit_exit = None
    audit_output = ""
    # A fresh run must not leave an old successful audit beside a failed build.
    (EVIDENCE / "axioms.log").unlink(missing_ok=True)
    if not errors:
        # Keep the same environment and child compiler thread configuration.
        # Each synchronous logged call finishes before the other large target starts.
        for module in WARMUP_MODULES:
            try:
                warmup_exits[module] = shared.logged(
                    ["lake", "build", "+" + PREFIX + "." + module + ":olean"],
                    "warmup_" + module + ".log",
                )
            except (OSError, subprocess.SubprocessError) as error:
                errors.append("Could not run warmup " + module + ": " + str(error))
        # Obtain both independent warmup results, then avoid rebuilding a failed target.
        if not errors and all(code == 0 for code in warmup_exits.values()):
            try:
                build_exit = shared.logged(["lake", "build", *targets], "build.log")
                if build_exit == 0:
                    audit_exit = shared.logged(
                        ["lake", "env", "lean", str(audit_path)], "axioms.log"
                    )
                    audit_output = (EVIDENCE / "axioms.log").read_text(encoding="utf-8")
            except (OSError, subprocess.SubprocessError) as error:
                errors.append("Could not run verification: " + str(error))

    after_sources = snapshot_safely(source_snapshot, "V2 sources after verification", errors)
    after_configuration = snapshot_safely(
        configuration_snapshot, "configuration after verification", errors
    )
    changed_sources = sorted(
        path for path in set(before_sources) | set(after_sources)
        if before_sources.get(path) != after_sources.get(path)
    )
    changed_configuration = sorted(
        path for path in set(before_configuration) | set(after_configuration)
        if before_configuration.get(path) != after_configuration.get(path)
    )
    if changed_sources:
        errors.append("V2 sources changed during verification: " + ", ".join(changed_sources))
    if changed_configuration:
        errors.append("Configuration changed during verification: " + ", ".join(changed_configuration))
    head_after = git_safely(("rev-parse", "HEAD"), errors)
    if head_after != head:
        errors.append("Git HEAD changed during verification")
    status_after = status_safely(errors)
    if status_after:
        errors.append("V2 source or configuration is dirty after verification")
    try:
        audit_hash_after = digest(audit_path)
    except OSError as error:
        audit_hash_after = None
        errors.append("Cannot hash the generated fresh audit: " + str(error))
    if audit_hash_after != audit_hash:
        errors.append("Generated audit changed during verification")

    marker = SUCCESS_MARKER in audit_output
    required_present = {name: REQUIRED_MARKER + name in audit_output for name in REQUIRED}
    modules_present = {
        name: MODULE_MARKER + PREFIX + "." + name in audit_output for name in OWN_MODULES
    }
    watchdogs = dict(shared.WATCHDOG_RESULTS)
    expected_watchdogs = {"build.log", "axioms.log"} | {
        "warmup_" + module + ".log" for module in WARMUP_MODULES
    }
    watchdogs_complete = set(watchdogs) == expected_watchdogs
    watchdog_killed = sum(len(report["killed"]) for report in watchdogs.values())
    watchdog_errors = sum(len(report["monitor_errors"]) for report in watchdogs.values())
    watchdog_ok = watchdogs_complete and watchdog_killed == 0 and watchdog_errors == 0
    success = (
        not errors and all(code == 0 for code in warmup_exits.values())
        and build_exit == 0 and audit_exit == 0 and marker
        and all(required_present.values()) and all(modules_present.values()) and watchdog_ok
    )
    result = {
        "head": head,
        "head_after": head_after,
        "scope": "s6_n1_proofs",
        "supplementary_check": True,
        "targets": targets,
        "owned_groups": EXPECTED_GROUPS,
        "warmup_exits": warmup_exits,
        "build_exit": build_exit,
        "audit_exit": audit_exit,
        "success_marker": marker,
        "required_declarations_present": required_present,
        "required_owned_modules_loaded": modules_present,
        "allowed_axioms": ALLOWED,
        "source_sha256_after": after_sources,
        "configuration_sha256_after": after_configuration,
        "audit_sha256_after": audit_hash_after,
        "changed_sources": changed_sources,
        "changed_configuration": changed_configuration,
        "input_status_after": status_after,
        "elapsed_seconds": time.monotonic() - start,
        "watchdogs": watchdogs,
        "watchdogs_complete": watchdogs_complete,
        "watchdog_killed": watchdog_killed,
        "watchdog_monitor_errors": watchdog_errors,
        "watchdog_ok": watchdog_ok,
        "errors": errors,
        "success": success,
    }
    (EVIDENCE / "result.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    summary = (
        "# MOM_ENGINE_STEP_V2 — S6/N1 proofs\n\n"
        + f"- Exact head: {head}\n"
        + "- Build/import entries: TasksFiniteLeaves and TasksOriginalAtoms.\n"
        + f"- Fixed owned inventory scanned: {len(OWN_MODULES)} modules.\n"
        + f"- All owned modules loaded: {all(modules_present.values())}\n"
        + f"- Both required task declarations present: {all(required_present.values())}\n"
        + f"- Sequential warmup exits: {warmup_exits}.\n"
        + f"- Lake exit: {build_exit}; fresh Lean audit exit: {audit_exit}.\n"
        + f"- Shared per-module Lean timeout: {shared.MODULE_TIMEOUT_SECONDS}s.\n"
        + f"- All four watchdog reports complete: {watchdogs_complete}.\n"
        + f"- Watchdog terminations: {watchdog_killed}; monitor errors: {watchdog_errors}.\n"
        + f"- V2 source files hashed: {len(before_sources)}; changed: {len(changed_sources)}.\n"
        + f"- Configuration files hashed: {len(before_configuration)}; changed: {len(changed_configuration)}.\n"
        + "- Axiom scope: every loaded V2 declaration, including private and generated declarations.\n"
        + "- Permitted axioms: propext, Classical.choice, Quot.sound.\n"
        + f"- Result: {'PASS' if success else 'FAIL'}.\n"
        + "- This supplementary result does not replace the full V2 or whole-project gates.\n"
    )
    if errors:
        summary += "\n" + "\n".join("- " + error for error in errors) + "\n"
    (EVIDENCE / "summary.md").write_text(summary, encoding="utf-8")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
            stream.write(summary)
    print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())

