#!/usr/bin/env python3
"""Compile V2 modules and audit each selected group whose proofs are complete.

The skeleton permits proof placeholders only in groups marked unproved.
Lake is the build authority; the fresh Lean audit checks every loaded V2
declaration, including private and generated declarations, recursively.
Without --group this remains the full build. Selected proved groups use
separate evidence and do not replace the full-build gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path.cwd()
TASK = ROOT / "HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2"
DEFAULT_EVIDENCE = ROOT / "v2-build"
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
NAMESPACE = "HeckeSkeleton.Moments.EngineStepV2"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]


def code_only(text: str) -> str:
    result = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        char, pair = text[i], text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.append("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.append("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            if char == "\\" and i + 1 < len(text):
                result.append("  ")
                i += 2
            else:
                if char == '"':
                    quoted = False
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            result.append("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            result.append(" " * (end - i))
            i = end
        else:
            quoted = char == '"'
            result.append(" " if quoted else char)
            i += 1
    return "".join(result)


def logged(command: list[str], name: str, evidence: Path) -> int:
    print("$ " + " ".join(command), flush=True)
    with (evidence / name).open("w", encoding="utf-8") as log:
        with subprocess.Popen(command, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True,
                              encoding="utf-8", errors="replace") as process:
            assert process.stdout is not None
            show_block = False
            for line in process.stdout:
                log.write(line)
                log.flush()
                if line.startswith(("⚠", "✔", "✖", "ℹ")):
                    show_block = "MOM_ENGINE_STEP_V2" in line or line.startswith("✖")
                if (name != "build.log" or show_block or "MOM_ENGINE_STEP_V2" in line or
                        line.startswith(("error:", "✖", "Build completed", "Some required"))):
                    print(line, end="", flush=True)
            return process.wait()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", action="append", default=[], metavar="ID",
                        help="Build and audit a proved manifest group; may be repeated")
    parser.add_argument("--evidence-dir", type=Path,
                        help="Evidence directory (default: v2-build, or v2-selected-build)")
    args = parser.parse_args()
    selected_ids = list(dict.fromkeys(args.group))
    scope = "selected_groups" if selected_ids else "full"
    evidence = args.evidence_dir or (ROOT / "v2-selected-build" if selected_ids
                                     else DEFAULT_EVIDENCE)
    if selected_ids and evidence.resolve() == DEFAULT_EVIDENCE.resolve():
        raise SystemExit("Selected-group evidence must not overwrite v2-build")
    evidence.mkdir(parents=True, exist_ok=True)
    manifest_path = ROOT / ".github/v2/manifest.json"
    files = sorted(TASK.glob("*.lean"))
    names = [path.stem for path in files]
    manifest = (json.loads(manifest_path.read_text()) if manifest_path.exists()
                else {"groups": [{"id": "skeleton", "proved": False, "modules": names}]})
    groups = manifest["groups"]
    listed = [name for group in groups for name in group["modules"]]
    if sorted(listed) != names or len(listed) != len(set(listed)):
        raise SystemExit("The group manifest must cover every V2 module exactly once")
    if any(len(group["modules"]) > 100 for group in groups):
        raise SystemExit("Each group must have at most 100 modules")
    group_ids = [group["id"] for group in groups]
    if (len(group_ids) != len(set(group_ids)) or
            any(not re.fullmatch(r"[a-z0-9_]+", group_id) for group_id in group_ids)):
        raise SystemExit("Group identifiers must be unique lowercase names")
    for group in groups:
        if not isinstance(group.get("proved"), bool):
            raise SystemExit("The proved flag must be boolean for group " + group["id"])
        required = group.get("required_declarations", [])
        if (not isinstance(required, list) or
                any(not isinstance(name, str) or
                    not re.fullmatch(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*", name)
                    for name in required)):
            raise SystemExit("Invalid required_declarations for group " + group["id"])
    by_id = {group["id"]: group for group in groups}
    if selected_ids:
        invalid = [group_id for group_id in selected_ids
                   if group_id not in by_id or not by_id[group_id]["proved"]]
        if invalid:
            raise SystemExit("Selected groups must exist and be proved: " + ", ".join(invalid))
        build_groups = [by_id[group_id] for group_id in selected_ids]
    else:
        build_groups = groups
    build_names = sorted(name for group in build_groups for name in group["modules"])
    if not build_names or any(not group["modules"] for group in build_groups):
        raise SystemExit("Every selected group must contain at least one module")
    audit_groups = [group for group in build_groups if group["proved"]]
    expected_audits = [group["id"] for group in audit_groups]
    targets = ["+" + PREFIX + "." + name + ":olean" for name in build_names]
    snapshots = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in files}
    bad = []
    for group in groups:
        pattern = r"\b(?:axiom|native_decide|admit|sorryAx)\b"
        if group["proved"]:
            pattern = r"\b(?:axiom|native_decide|admit|sorryAx|sorry)\b"
        for module in group["modules"]:
            path = TASK / (module + ".lean")
            if re.search(pattern, code_only(path.read_text())):
                bad.append(str(path.relative_to(ROOT)))
    if bad:
        raise SystemExit("Forbidden proof tokens: " + ", ".join(bad))
    environment = {
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "manifest": manifest,
        "source_sha256": snapshots,
        "allowed_axioms": ALLOWED,
        "scope": scope,
        "selected_groups": selected_ids,
        "targets": targets,
        "expected_audits": expected_audits,
    }
    (evidence / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    start = time.monotonic()
    build_exit = logged(["lake", "build", *targets], "build.log", evidence)
    results = {"scope": scope, "selected_groups": selected_ids, "targets": targets,
               "build_exit": build_exit, "module_count": len(build_names),
               "total_module_count": len(names), "expected_audits": expected_audits,
               "elapsed_seconds": time.monotonic() - start, "group_audits": {}}
    if build_exit == 0:
        for group in audit_groups:
            group_id = group["id"]
            required = group.get("required_declarations", [])
            audit = "\n".join("import " + PREFIX + "." + name for name in group["modules"])
            audit += """
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
"""
            audit += "  let required : Array Name := #[" + ", ".join(
                "`" + name for name in required) + "]\n"
            audit += """
  for requiredName in required do
    unless names.contains requiredName do
      throwError "Required V2 declaration missing: {requiredName}"
    logInfo m!"REQUIRED_V2_DECLARATION_PRESENT: {requiredName}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"V2_GROUP_AXIOMS_PASSED: {names.size} declarations"
"""
            audit_path = evidence / (group_id + "_AxiomAudit.lean")
            audit_path.write_text(audit)
            code = logged(["lake", "env", "lean", str(audit_path)],
                          group_id + "_axioms.log", evidence)
            output = (evidence / (group_id + "_axioms.log")).read_text()
            results["group_audits"][group_id] = {
                "exit_code": code,
                "success_marker": "V2_GROUP_AXIOMS_PASSED:" in output,
                "required_declarations": required,
            }
    for path, digest in snapshots.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise SystemExit("Source changed during verification: " + path)
    success = build_exit == 0 and set(results["group_audits"]) == set(expected_audits) and all(
        result["exit_code"] == 0 and result["success_marker"]
        for result in results["group_audits"].values())
    results["success"] = success
    (evidence / "result.json").write_text(json.dumps(results, indent=2) + "\n")
    audited = (", ".join(results["group_audits"]) or
               ("not run (build failed)" if expected_audits else "none (no proved groups)"))
    summary = ("# MOM_ENGINE_STEP_V2\n\n"
               + f"- Exact head: `{environment['head']}`\n"
               + f"- Scope: `{scope}`\n"
               + f"- Selected groups: {', '.join(selected_ids) or 'all'}\n"
               + f"- Target modules: {len(build_names)} of {len(names)} V2 modules\n"
               + f"- Lake exit: {build_exit}\n"
               + f"- Proved groups audited: {audited}\n"
               + f"- Result: {'PASS' if success else 'FAIL'}\n")
    if selected_ids:
        summary += "- This selected-group result does not replace the full-build gate.\n"
    (evidence / "summary.md").write_text(summary)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as stream:
            stream.write(summary)
    print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
