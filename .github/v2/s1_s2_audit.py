#!/usr/bin/env python3
"""Build the S1/S2 proof entries and freshly audit their loaded V2 declarations.

This branch-specific check supplements the unchanged full V2 and whole-project
jobs. It never reads a previous audit result and does not alter the manifest,
the permitted axioms, or the mathematical sources.
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

import build as shared

ROOT = Path(__file__).resolve().parents[2]
TASK = ROOT / "HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2"
EVIDENCE = ROOT / "v2-s1-s2-build"
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
MODULES = (
    "S1ExactBound",
    "S1SourceConstruction",
    "S2FirstFamilyData",
    "S2FirstFamilyCost",
    "S2FirstRowWindow",
    "S2FirstPhysicalCutoff",
    "S2OriginalColumnWindow",
    "S2FirstColumnWindows",
    "S2FirstRetainedWindow",
    "TasksFirstTransform",
    "TasksFirstAllowance",
)
REQUIRED = (
    "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.firstTransform",
    "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.firstAllowance",
)
ALLOWED = ("propext", "Classical.choice", "Quot.sound")
SUCCESS_MARKER = "V2_S1_S2_AXIOMS_PASSED:"
REQUIRED_MARKER = "REQUIRED_V2_DECLARATION_PRESENT: "
FORBIDDEN = re.compile(r"\b(?:axiom|native_decide|admit|sorryAx|sorry)\b")

AUDIT_BODY = r"""
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modulePrefix : Name := `HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let declarationPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let moduleNames := env.header.moduleNames
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
      throwError "Required S1/S2 declaration missing: {requiredName}"
    logInfo m!"REQUIRED_V2_DECLARATION_PRESENT: {requiredName}"
  let permitted : Array Name := #[__ALLOWED__]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"V2_S1_S2_AXIOMS_PASSED: {names.size} declarations"
"""


def source_snapshot() -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(TASK.glob("*.lean"))
    }


def audit_source() -> str:
    imports = "\n".join("import " + PREFIX + "." + name for name in MODULES)
    body = AUDIT_BODY.replace(
        "__REQUIRED__", ", ".join("`" + name for name in REQUIRED)
    ).replace("__ALLOWED__", ", ".join("`" + name for name in ALLOWED))
    return imports + "\n" + body


def main() -> int:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    # The shared runner and Watcher use module globals. Each CI job has its own
    # Python process, so this preserves the independent S1/S2 evidence directory.
    os.chdir(ROOT)
    shared.ROOT = ROOT
    shared.EVIDENCE = EVIDENCE
    shared.WATCHDOG_RESULTS.clear()
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    snapshots = source_snapshot()
    targets = ["+" + PREFIX + "." + name + ":olean" for name in MODULES]
    errors = []
    for module in MODULES:
        path = TASK / (module + ".lean")
        if not path.is_file():
            errors.append("Required module missing: " + str(path.relative_to(ROOT)))
        elif FORBIDDEN.search(shared.code_only(path.read_text(encoding="utf-8"))):
            errors.append("Forbidden proof token: " + str(path.relative_to(ROOT)))

    audit_path = EVIDENCE / "S1S2_AxiomAudit.lean"
    audit_path.write_text(audit_source(), encoding="utf-8")
    environment = {
        "head": head,
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "scope": "s1_s2_proofs",
        "supplementary_check": True,
        "targets": targets,
        "required_declarations": REQUIRED,
        "allowed_axioms": ALLOWED,
        "source_sha256": snapshots,
        "audit_sha256": hashlib.sha256(audit_path.read_bytes()).hexdigest(),
        "audit_selection": "all loaded V2 module declarations or V2 namespace declarations",
        "module_timeout_seconds": shared.MODULE_TIMEOUT_SECONDS,
        "watch_interval_seconds": shared.WATCH_INTERVAL_SECONDS,
    }
    (EVIDENCE / "environment.json").write_text(
        json.dumps(environment, indent=2) + "\n", encoding="utf-8"
    )

    start = time.monotonic()
    build_exit = None
    audit_exit = None
    audit_output = ""
    if not errors:
        try:
            build_exit = shared.logged(["lake", "build", *targets], "build.log")
            if build_exit == 0:
                audit_exit = shared.logged(
                    ["lake", "env", "lean", str(audit_path)], "axioms.log"
                )
                audit_output = (EVIDENCE / "axioms.log").read_text(encoding="utf-8")
        except OSError as error:
            errors.append("Could not run verification: " + str(error))

    after = source_snapshot()
    changed = [
        path for path in sorted(set(snapshots) | set(after))
        if snapshots.get(path) != after.get(path)
    ]
    if changed:
        errors.append("V2 sources changed during verification: " + ", ".join(changed))
    head_after = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    if head_after != head:
        errors.append("Git HEAD changed during verification")

    marker = SUCCESS_MARKER in audit_output
    required_present = {
        name: REQUIRED_MARKER + name in audit_output for name in REQUIRED
    }
    watchdogs = dict(shared.WATCHDOG_RESULTS)
    watchdogs_complete = set(watchdogs) == {"build.log", "axioms.log"}
    watchdog_killed = sum(len(report["killed"]) for report in watchdogs.values())
    watchdog_errors = sum(len(report["monitor_errors"]) for report in watchdogs.values())
    watchdog_ok = watchdogs_complete and watchdog_killed == 0 and watchdog_errors == 0
    success = (
        not errors
        and build_exit == 0
        and audit_exit == 0
        and marker
        and all(required_present.values())
        and watchdog_ok
    )
    result = {
        "head": head,
        "scope": "s1_s2_proofs",
        "targets": targets,
        "build_exit": build_exit,
        "audit_exit": audit_exit,
        "success_marker": marker,
        "required_declarations_present": required_present,
        "allowed_axioms": ALLOWED,
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
        "# MOM_ENGINE_STEP_V2 — S1/S2 proofs\n\n"
        + f"- Exact head: `{head}`\n"
        + f"- Target modules: {len(MODULES)} (two task entries and nine helpers)\n"
        + f"- Lake exit: {build_exit}\n"
        + f"- Fresh Lean audit exit: {audit_exit}\n"
        + f"- Shared per-module Lean timeout: {shared.MODULE_TIMEOUT_SECONDS}s\n"
        + f"- Watchdog reports complete: {watchdogs_complete}\n"
        + f"- Modules terminated by watchdog: {watchdog_killed}\n"
        + f"- Watchdog monitor errors: {watchdog_errors}\n"
        + f"- Both required declarations present: {all(required_present.values())}\n"
        + "- Axiom scope: every loaded V2 declaration, including private and generated declarations.\n"
        + "- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.\n"
        + f"- Result: {'PASS' if success else 'FAIL'}\n"
        + "- This supplementary result does not replace the full V2 or whole-project checks.\n"
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
