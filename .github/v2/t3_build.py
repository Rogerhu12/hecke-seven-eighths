#!/usr/bin/env python3
"""Build T3 and audit declarations originating in every loaded V2 module.

This additional diagnostic gate does not replace the all-module gate or
the whole-project build. It uses the unchanged B-line process watchdog.
Module provenance includes private, generated and external-namespace
declarations, independently of their user-facing names.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path.cwd()
spec = importlib.util.spec_from_file_location("v2_gate", ROOT / ".github/v2/build.py")
assert spec and spec.loader
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.EVIDENCE = ROOT / "t3-build"

CONFIG_PATHS = (
    ".github/v2/t3_build.py",
    ".github/v2/build.py",
    ".github/v2/manifest.json",
    ".github/workflows/mom-v2-t3-proofs.yml",
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "vendor/class-field-theory/lean-toolchain",
    "vendor/class-field-theory/lake-manifest.json",
    "vendor/class-field-theory/lakefile.toml",
)
TASK_DECLARATIONS = {
    "TasksExceptionalRecovery":
        "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.exceptional_recovery",
    "TasksExceptionalSummation":
        "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.exceptional_summation",
}


def audit_source(modules: list[str], required: list[str]) -> str:
    # The pinned Lean module-index API is also used by expansion_verify.py.
    # Keep raw constant names: private/generated declarations have the same
    # originating module as the public declarations from their source file.
    return "\n".join([
        *("import " + gate.PREFIX + "." + name for name in modules),
        "import Lean.Elab.Command",
        "import Lean.Util.CollectAxioms",
        "",
        "open Lean Elab Command in",
        "run_cmd do",
        "  let env ← getEnv",
        "  let modulePrefix : Name := `" + gate.PREFIX,
        "  let names := (env.constants.toList.filterMap fun (name, _) =>",
        "    match env.getModuleIdxFor? name with",
        "    | some idx =>",
        "      if modulePrefix.isPrefixOf env.header.moduleNames[idx.toNat]! then some name else none",
        "    | none => none).toArray.qsort Name.lt",
        "  unless !names.isEmpty do",
        '    throwError "No declarations originating in V2 modules found"',
        "  let required : Array Name := #[" + ", ".join("`" + name for name in required) + "]",
        "  for name in required do",
        "    let _ ← getConstInfo name",
        "    unless names.contains name do",
        '      throwError "Required T3 task is outside the V2 origin audit: {name}"',
        '    logInfo m!"T3_REQUIRED_TASK {name}"',
        "  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]",
        "  for name in names do",
        "    let dependencies ← collectAxioms name",
        "    let extra := dependencies.filter fun ax => !permitted.contains ax",
        "    unless extra.isEmpty do",
        '      throwError "Unexpected axiom dependency in {name}: {extra}"',
        '    logInfo m!"AXIOMS {name}: {dependencies}"',
        '  logInfo m!"T3_AXIOMS_PASSED: {names.size} declarations"',
        "",
    ])


def main() -> int:
    evidence = gate.EVIDENCE
    evidence.mkdir(exist_ok=True)
    manifest = json.loads((ROOT / ".github/v2/manifest.json").read_text())
    groups = [g for g in manifest["groups"] if g["id"].startswith("t3_")]
    if not groups or any(not g["proved"] for g in groups):
        raise SystemExit("T3 closure must have nonempty proved groups")
    names = sorted({name for g in groups for name in g["modules"]})
    if len(names) != sum(len(g["modules"]) for g in groups):
        raise SystemExit("Duplicate T3 module")
    required_tasks = TASK_DECLARATIONS if set(TASK_DECLARATIONS).issubset(names) else {}
    snapshots = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in sorted(gate.TASK.glob("*.lean"))}
    config_snapshots = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                        for path in CONFIG_PATHS}
    for name in names:
        path = gate.TASK / (name + ".lean")
        if re.search(r"\b(?:axiom|native_decide|admit|sorryAx|sorry)\b",
                     gate.code_only(path.read_text())):
            raise SystemExit("Forbidden proof token in " + str(path))
    environment = {
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "groups": groups,
        "source_sha256": snapshots,
        "config_sha256": config_snapshots,
        "audit_origin_module_prefix": gate.PREFIX,
        "required_task_declarations": required_tasks,
        "allowed_axioms": gate.ALLOWED,
        "module_timeout_seconds": gate.MODULE_TIMEOUT_SECONDS,
    }
    (evidence / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    start = time.monotonic()
    build = gate.logged(["lake", "build", *(
        "+" + gate.PREFIX + "." + name + ":olean" for name in names)], "build.log")
    results = {"build_exit": build, "audits": {}, "watchdogs": gate.WATCHDOG_RESULTS}
    if build == 0:
        for group in groups:
            required = [declaration for module, declaration in required_tasks.items()
                        if module in group["modules"]]
            source = audit_source(group["modules"], required)
            path = evidence / (group["id"] + "_AxiomAudit.lean")
            path.write_text(source)
            log = group["id"] + "_axioms.log"
            code = gate.logged(["lake", "env", "lean", str(path)], log)
            output = (evidence / log).read_text()
            results["audits"][group["id"]] = {
                "exit_code": code,
                "success_marker": "T3_AXIOMS_PASSED:" in output,
                "required_tasks": required,
                "required_tasks_found": all("T3_REQUIRED_TASK " + name in output
                                            for name in required),
            }
    for category, hashes in (("Source", snapshots), ("Configuration", config_snapshots)):
        for path, digest in hashes.items():
            if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
                raise SystemExit(category + " changed during verification: " + path)
    results["elapsed_seconds"] = time.monotonic() - start
    success = build == 0 and len(results["audits"]) == len(groups) and all(
        a["exit_code"] == 0 and a["success_marker"] and a["required_tasks_found"]
        for a in results["audits"].values())
    results["success"] = success
    (evidence / "result.json").write_text(json.dumps(results, indent=2) + "\n")
    summary = (f"# T3 proof closure\n\n- Exact head: `{environment['head']}`\n"
               f"- Explicit proof modules: {len(names)}\n- Lake exit: {build}\n"
               f"- Recursive audit groups: {len(results['audits'])}/{len(groups)}\n"
               f"- Audit scope: declarations originating in any loaded `{gate.PREFIX}` module\n"
               f"- Required task declarations: {len(required_tasks)}\n"
               f"- Hashed build configurations: {len(config_snapshots)}\n"
               f"- Per-module watchdog: {gate.MODULE_TIMEOUT_SECONDS}s\n"
               f"- Result: {'PASS' if success else 'FAIL'}\n")
    (evidence / "summary.md").write_text(summary)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as out:
            out.write(summary)
    print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
