#!/usr/bin/env python3
"""Build and recursively audit the manifest's S4/T4 proof groups only.

This independent job supplements the unchanged all-module V2 gate. It
shares that gate's forbidden-token scanner and per-process watchdog.
No source is generated or rewritten; only the fresh audit and evidence
are written outside the source tree.
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

import build

ROOT = build.ROOT
TASK = build.TASK
EVIDENCE = ROOT / "v2-s4-t4-build"
GROUP_IDS = ("s4", "t4")
TARGETS = (
    "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.secondTransform",
    "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.tails",
)


def audit_source(modules: list[str]) -> str:
    imports = "\n".join("import " + build.PREFIX + "." + name for name in modules)
    return imports + """
import Lean.Elab.Command
import Lean.Util.CollectAxioms

-- The shared watchdog bounds this complete metadata walk in wall time.
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let moduleNames := env.allImportedModuleNames
  let modulePrefix : Name := `HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let targets : Array Name := #[
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.secondTransform,
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.tails]
  for target in targets do
    unless env.contains target do
      throwError "Missing required S4/T4 declaration: {target}"
    logInfo m!"S4_T4_TARGET_EXISTS {target}"
    let dependencies ← collectAxioms target
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected target axiom dependency in {target}: {extra}"
    logInfo m!"S4_T4_TARGET_AXIOMS {target}: {dependencies}"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let fromModule ← match env.getModuleIdxFor? name with
      | none => pure false
      | some idx =>
        match moduleNames[idx]? with
        | none => throwError "Invalid imported-module index {idx} for {name}"
        | some moduleName => pure (modulePrefix.isPrefixOf moduleName)
    if fromModule || nsPrefix.isPrefixOf (privateToUserName name) then
      names := names.push name
  unless !names.isEmpty do
    throwError "No loaded V2 declarations found"
  for name in names.qsort Name.lt do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"S4_T4_LOADED_V2_AXIOMS_PASSED: {names.size} declarations"

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.secondTransform
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.tails
"""


def write_json(name: str, value: dict) -> None:
    (EVIDENCE / name).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    build.EVIDENCE = EVIDENCE
    build.WATCHDOG_RESULTS.clear()
    start = time.monotonic()
    snapshots: dict[str, str] = {}
    environment: dict = {"allowed_axioms": build.ALLOWED,
                         "required_targets": TARGETS,
                         "module_timeout_seconds": build.MODULE_TIMEOUT_SECONDS,
                         "watch_interval_seconds": build.WATCH_INTERVAL_SECONDS}
    result: dict = {"status": "preflight", "build_exit": None, "audit_exit": None,
                    "module_count": 0, "group_modules": {}, "targets": {},
                    "success_marker": False, "source_unchanged": False,
                    "errors": [], "watchdogs": build.WATCHDOG_RESULTS}
    write_json("result.json", result)
    try:
        manifest_path = ROOT / ".github/v2/manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        groups = manifest["groups"]
        files = sorted(TASK.glob("*.lean"))
        listed = [name for group in groups for name in group["modules"]]
        if sorted(listed) != [path.stem for path in files] or len(listed) != len(set(listed)):
            raise ValueError("The manifest must cover every V2 module exactly once")
        if any(len(group["modules"]) > 100 for group in groups):
            raise ValueError("Each manifest group must have at most 100 modules")
        chosen = []
        for group_id in GROUP_IDS:
            matches = [group for group in groups if group["id"] == group_id]
            if len(matches) != 1 or matches[0].get("proved") is not True:
                raise ValueError("Expected one proved manifest group: " + group_id)
            if not matches[0]["modules"]:
                raise ValueError("Empty proof group: " + group_id)
            chosen.append(matches[0])
        modules = [name for group in chosen for name in group["modules"]]
        if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) for name in modules):
            raise ValueError("Invalid S4/T4 module identifier")
        if not {"TasksSecondTransform", "TasksTails"}.issubset(modules):
            raise ValueError("Both task entry modules must be selected by the manifest")
        result["module_count"] = len(modules)
        result["group_modules"] = {group["id"]: group["modules"] for group in chosen}
        snapshot_files = [*files, manifest_path, ROOT / ".github/v2/build.py",
                          Path(__file__).resolve(), ROOT / "lean-toolchain",
                          ROOT / "lake-manifest.json"]
        snapshots = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                     for path in snapshot_files}
        environment.update({
            "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
            "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "manifest": manifest, "selected_groups": GROUP_IDS,
            "selected_modules": modules, "source_sha256": snapshots,
        })
        write_json("environment.json", environment)
        # Preserve the full gate's source preflight; only the build/audit roots differ.
        forbidden = []
        for group in groups:
            pattern = r"\b(?:axiom|native_decide|admit|sorryAx)\b"
            if group["proved"]:
                pattern = r"\b(?:axiom|native_decide|admit|sorryAx|sorry)\b"
            for module in group["modules"]:
                path = TASK / (module + ".lean")
                if re.search(pattern, build.code_only(path.read_text(encoding="utf-8"))):
                    forbidden.append(str(path.relative_to(ROOT)))
        result["forbidden_sources"] = forbidden
        if forbidden:
            raise ValueError("Forbidden proof tokens: " + ", ".join(forbidden))
        result["status"] = "building"
        write_json("result.json", result)
        result["build_exit"] = build.logged(
            ["lake", "build", *("+" + build.PREFIX + "." + name + ":olean"
                               for name in modules)], "build.log")
        write_json("result.json", result)
        if result["build_exit"] == 0:
            audit_path = EVIDENCE / "S4T4_AxiomAudit.lean"
            audit_path.write_text(audit_source(modules), encoding="utf-8")
            result["status"] = "auditing"
            write_json("result.json", result)
            result["audit_exit"] = build.logged(
                ["lake", "env", "lean", str(audit_path)], "axioms.log")
            output = (EVIDENCE / "axioms.log").read_text(encoding="utf-8")
            result["success_marker"] = "S4_T4_LOADED_V2_AXIOMS_PASSED:" in output
            result["targets"] = {
                name: {"present": "S4_T4_TARGET_EXISTS " + name in output,
                       "axioms_logged": "S4_T4_TARGET_AXIOMS " + name + ":" in output}
                for name in TARGETS}
    except Exception as error:
        result["errors"].append(f"{type(error).__name__}: {error}")
    finally:
        changed = [path for path, digest in snapshots.items()
                   if not (ROOT / path).is_file() or
                   hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest]
        result["changed_sources"] = changed
        result["source_unchanged"] = bool(snapshots) and not changed
        result["elapsed_seconds"] = time.monotonic() - start
        success = (not result["errors"] and result["build_exit"] == 0 and
                   result["audit_exit"] == 0 and result["success_marker"] and
                   result["source_unchanged"] and len(result["targets"]) == len(TARGETS) and
                   all(item["present"] and item["axioms_logged"]
                       for item in result["targets"].values()))
        result["status"] = "passed" if success else "failed"
        write_json("environment.json", environment)
        write_json("result.json", result)
        summary = ("# MOM_ENGINE_STEP_V2: S4 and T4\n\n"
                   + f"- Exact head: `{environment.get('head', 'unavailable')}`\n"
                   + f"- Selected proof modules: {result['module_count']}\n"
                   + f"- Lake exit: {result['build_exit']}\n"
                   + f"- Loaded V2 recursive axiom audit exit: {result['audit_exit']}\n"
                   + f"- Required entry declarations: {', '.join(TARGETS)}\n"
                   + f"- Sources unchanged: {result['source_unchanged']}\n"
                   + f"- Per-module Lean timeout: {build.MODULE_TIMEOUT_SECONDS}s\n"
                   + f"- Result: {'PASS' if success else 'FAIL'}\n")
        if result["errors"]:
            summary += "\n" + "\n".join("- " + error for error in result["errors"]) + "\n"
        (EVIDENCE / "summary.md").write_text(summary, encoding="utf-8")
        if os.environ.get("GITHUB_STEP_SUMMARY"):
            with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
                stream.write(summary)
        print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
