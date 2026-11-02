#!/usr/bin/env python3
"""Build the T3 proof closure and audit all loaded V2 declarations in CI.

This additional diagnostic gate does not replace the all-module gate or
the whole-project build. It uses the unchanged B-line process watchdog.
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
    snapshots = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in sorted(gate.TASK.glob("*.lean"))}
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
            source = "\n".join("import " + gate.PREFIX + "." + n for n in group["modules"])
            source += """
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let names := (env.constants.toList.filterMap fun (name, _) =>
    if nsPrefix.isPrefixOf (privateToUserName name) then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No V2 declarations found"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"T3_AXIOMS_PASSED: {names.size} declarations"
"""
            path = evidence / (group["id"] + "_AxiomAudit.lean")
            path.write_text(source)
            log = group["id"] + "_axioms.log"
            code = gate.logged(["lake", "env", "lean", str(path)], log)
            results["audits"][group["id"]] = {
                "exit_code": code,
                "success_marker": "T3_AXIOMS_PASSED:" in (evidence / log).read_text(),
            }
    for path, digest in snapshots.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise SystemExit("Source changed during verification: " + path)
    results["elapsed_seconds"] = time.monotonic() - start
    success = build == 0 and len(results["audits"]) == len(groups) and all(
        a["exit_code"] == 0 and a["success_marker"] for a in results["audits"].values())
    results["success"] = success
    (evidence / "result.json").write_text(json.dumps(results, indent=2) + "\n")
    summary = (f"# T3 proof closure\n\n- Exact head: `{environment['head']}`\n"
               f"- Explicit proof modules: {len(names)}\n- Lake exit: {build}\n"
               f"- Recursive audit groups: {len(results['audits'])}/{len(groups)}\n"
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
