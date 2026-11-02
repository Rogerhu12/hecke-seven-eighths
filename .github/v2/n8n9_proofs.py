#!/usr/bin/env python3
"""Build N8/N9 proofs and audit their entire loaded V2 environment.

The analysis stage builds two N9 analytic roots and three N8 helpers
independently of the RawContracts and OrdinaryData assembly dependencies.
The complete stage checks every module in the three proved task groups.
The complete task statements remain candidates until this stage succeeds
at the exact selected head.  These additional jobs do not replace the
registered task V2 gate.
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

import build as shared

ROOT = Path.cwd()
TASK = ROOT / "HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2"
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
NAMESPACE = "HeckeSkeleton.Moments.EngineStepV2"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
GROUPS = ("n8a_proved", "n8b_proved", "n9_proved")
ANALYSIS_MODULES = (
    "N9FixedRadiusMass", "N9UniformCost", "SecondZeroFirstMass",
    "SecondZeroRowSizeBounds", "N8NormalizedLeafWeights",
)
COMPLETE_WARMUP_MODULES = ("RawContracts", "OrdinaryData")
ANALYSIS_THEOREMS = (
    NAMESPACE + ".Blueprint.fixed_radius_kernel_mass",
    NAMESPACE + ".Blueprint.kernelMass_le_uniformCost",
    NAMESPACE + ".Blueprint.Tasks.SecondZeroProof.first_family_mass_uniform",
    NAMESPACE + ".Blueprint.Tasks.SecondZeroProof.pool_rowExponent_le",
    NAMESPACE + ".Blueprint.RawLeafPacket.leaf_weight_eq",
)
COMPLETE_MODULES = (
    "N8SourceIndexProof", "TasksSourceIndex", "N8NormalizedMassProof",
    "TasksNormalizedMass", "N8NormalizedArithmeticAssembly", "N9OriginalWindowMass",
)
COMPLETE_THEOREMS = (
    NAMESPACE + ".Blueprint.N8Source.sourceIndexTask",
    NAMESPACE + ".Blueprint.Tasks.sourceIndex",
    NAMESPACE + ".Blueprint.Tasks.normalizedMass",
    NAMESPACE + ".Assembly.canonicalArithmeticMass",
    NAMESPACE + ".Blueprint.Tasks.originalWindowKernelMass",
)
FORBIDDEN = re.compile(r"\b(?:sorry|axiom|admit|native_decide|sorryAx)\b")
MODULE_NAME = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_snapshot() -> dict[str, str]:
    return {str(path.relative_to(ROOT)): digest(path)
            for path in sorted(TASK.glob("*.lean"))}


def config_snapshot() -> dict[str, str]:
    paths = {ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json")}
    for pattern in ("*.py", "*.json", "*.yml", "*.yaml"):
        paths.update((ROOT / ".github").rglob(pattern))
    return {str(path.relative_to(ROOT)): digest(path)
            for path in sorted(paths) if path.is_file()}


def selected_modules(stage: str, manifest: dict) -> tuple[list[str], list[str]]:
    if stage == "analysis":
        return list(ANALYSIS_MODULES), list(ANALYSIS_THEOREMS)
    groups = manifest["groups"]
    selected = []
    for group_id in GROUPS:
        matches = [group for group in groups if group["id"] == group_id]
        if len(matches) != 1 or matches[0].get("proved") is not True:
            raise ValueError(f"Expected exactly one proved manifest group: {group_id}")
        selected.extend(matches[0]["modules"])
    if len(selected) != len(set(selected)):
        raise ValueError("A selected task module occurs more than once in the manifest")
    owned = {path.stem for pattern in ("N8*.lean", "N9*.lean")
             for path in TASK.glob(pattern)} | {"KernelMassContracts", "TasksKernelMass"}
    missing = owned.difference(selected)
    if missing:
        raise ValueError("Owned N8/N9 sources outside the proved groups: " + ", ".join(sorted(missing)))
    missing = set(COMPLETE_MODULES).difference(selected)
    if missing:
        raise ValueError("Final N8a/N8b/exact-N9 proof modules missing from groups: " + ", ".join(sorted(missing)))
    return sorted(selected), list(COMPLETE_THEOREMS)


def preflight(modules: list[str]) -> list[str]:
    errors = []
    for module in modules:
        if not MODULE_NAME.fullmatch(module):
            errors.append("Invalid task module name: " + repr(module))
            continue
        path = TASK / (module + ".lean")
        if not path.is_file():
            errors.append("Missing selected source: " + str(path.relative_to(ROOT)))
            continue
        source = shared.code_only(path.read_text(encoding="utf-8"))
        for match in FORBIDDEN.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: forbidden {match.group()}")
    return errors


def audit_source(stage: str, modules: list[str], required: list[str]) -> str:
    imports = "\n".join("import " + PREFIX + "." + module for module in modules)
    checks = "\n".join("#check " + name for name in required)
    names = ",\n    ".join("`" + name for name in required)
    marker = "N8_N9_" + stage.upper() + "_AXIOMS_PASSED"
    return imports + "\nimport Lean.Elab.Command\nimport Lean.Util.CollectAxioms\n\n" + checks + "\n" + f"""
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames : Array Name := env.header.moduleNames
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let modulePrefix : Name := `HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let sourceModule? (name : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? name
    moduleNames[idx.toNat]?
  let names := (env.constants.toList.filterMap fun (name, _) =>
    let fromModule := (sourceModule? name).any (modulePrefix.isPrefixOf ·)
    if fromModule || nsPrefix.isPrefixOf (privateToUserName name)
    then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No loaded V2 declarations found"
  let required : Array Name := #[
    {names}]
  for name in required do
    unless names.contains name do
      throwError "Missing required N8/N9 theorem in the audit environment: {{name}}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {{name}}: {{extra}}"
    logInfo m!"AXIOMS {{name}}: {{dependencies}}"
  let modules := moduleNames.filter (modulePrefix.isPrefixOf ·)
  for moduleName in modules do
    let count : Nat := names.foldl (fun (n : Nat) name =>
      if sourceModule? name == some moduleName then n + 1 else n) 0
    logInfo m!"V2_SOURCE_MODULE {{moduleName}}: {{count}} declarations"
  logInfo m!"{marker}: {{names.size}} declarations"
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", required=True, choices=("analysis", "complete"))
    parser.add_argument(
        "--warmup-shared-roots", action="store_true",
        help="For complete only: diagnose the two shared roots sequentially before the mandatory full build")
    args = parser.parse_args()
    if args.warmup_shared_roots and args.stage != "complete":
        parser.error("--warmup-shared-roots is only valid with --stage complete")
    stage = args.stage
    warmup_shared_roots = stage == "complete" and args.warmup_shared_roots
    evidence = ROOT / ("v2-n8n9-" + stage + "-build")
    evidence.mkdir(exist_ok=True)
    # Reuse the B driver's actual logger and Watcher, including future fixes.
    shared.EVIDENCE = evidence
    shared.WATCHDOG_RESULTS.clear()
    start = time.monotonic()
    errors = []
    modules, required = [], []
    snapshots = source_snapshot()
    configurations = config_snapshot()
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    expected = os.environ.get("N8N9_EXPECTED_HEAD", "")
    if not re.fullmatch(r"[0-9a-f]{40}", expected) or head != expected:
        errors.append(f"Exact head mismatch or missing expected head: expected={expected!r}, actual={head}")
    initial_diff = subprocess.check_output(["git", "diff", "--name-only", "HEAD", "--"], text=True)
    if initial_diff.strip():
        errors.append("Tracked files differ from the exact selected head: " + initial_diff.strip())
    manifest = None
    try:
        manifest = json.loads((ROOT / ".github/v2/manifest.json").read_text(encoding="utf-8"))
        modules, required = selected_modules(stage, manifest)
        errors.extend(preflight(modules))
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors.append(f"Preflight {type(error).__name__}: {error}")
    if not snapshots:
        errors.append("No V2 sources found")
    task_scope = (
        "Helper analysis: N9FixedRadiusMass, N9UniformCost, SecondZeroFirstMass, "
        "SecondZeroRowSizeBounds, and N8NormalizedLeafWeights, with all five "
        "helper endpoints required; "
        "this stage does not certify the N8a, N8b, or exact N9 main task statements"
        if stage == "analysis" else
        "All modules in n8a_proved, n8b_proved, and n9_proved, with the "
        "Tasks.sourceIndex, Tasks.normalizedMass, and Tasks.originalWindowKernelMass "
        "main statements and Assembly.canonicalArithmeticMass required"
    )
    n8b_status = (
        "Main N8b task not certified by helper analysis"
        if stage == "analysis" else
        "Candidate: the complete N8b task must build and pass the recursive axiom audit at this exact head"
    )
    environment = {
        "head": head,
        "expected_head": expected,
        "stage": stage,
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "targets": [PREFIX + "." + module for module in modules],
        "warmup_shared_roots_requested": warmup_shared_roots,
        "sequential_warmup_targets": (
            [PREFIX + "." + module for module in COMPLETE_WARMUP_MODULES]
            if warmup_shared_roots else []
        ),
        "required_theorems": required,
        "manifest": manifest,
        "source_sha256": snapshots,
        "verification_sha256": configurations,
        "allowed_axioms": ALLOWED,
        "module_timeout_seconds": shared.MODULE_TIMEOUT_SECONDS,
        "watch_interval_seconds": shared.WATCH_INTERVAL_SECONDS,
        "audit_scope": "Every loaded declaration in a V2 source module OR V2 namespace, including private/generated names; recursive collectAxioms",
        "task_scope": task_scope,
        "n8b_status": n8b_status,
    }
    (evidence / "environment.json").write_text(json.dumps(environment, indent=2) + "\n", encoding="utf-8")
    preflight_text = "\n".join(errors) + "\n" if errors else f"PASS: {len(modules)} selected modules; stage={stage}.\n"
    (evidence / "preflight.log").write_text(preflight_text, encoding="utf-8")
    print(preflight_text, end="", flush=True)
    results = {
        "stage": stage,
        "preflight_passed": not errors,
        "warmup_shared_roots_requested": warmup_shared_roots,
        "warmup_exits": {},
        "build_exit": None,
        "build_skipped_reason": None,
        "audit_exit": None,
        "audit_skipped_reason": None,
        "audit_success_marker": False,
        "watchdogs": shared.WATCHDOG_RESULTS,
        "errors": errors,
        "n8b_status": environment["n8b_status"],
    }
    if not errors:
        if warmup_shared_roots:
            # Optional diagnostic: isolate the shared roots before the full build. A
            # failed warmup is a hard gate failure.  Both warmups still
            # run, but their failed dependencies are not rebuilt a third
            # time by the full task command.
            for module in COMPLETE_WARMUP_MODULES:
                log_name = "warmup-" + module + ".log"
                try:
                    code = shared.logged(
                        ["lake", "build", "+" + PREFIX + "." + module + ":olean"],
                        log_name)
                    results["warmup_exits"][module] = code
                    if code != 0:
                        errors.append(f"Sequential warmup {module} failed with exit {code}")
                except Exception as error:
                    results["warmup_exits"][module] = None
                    message = f"Sequential warmup {module}: {type(error).__name__}: {error}"
                    errors.append(message)
                    with (evidence / log_name).open("a", encoding="utf-8") as stream:
                        stream.write(message + "\n")
                    print(message, file=sys.stderr, flush=True)
        warmup_failed = warmup_shared_roots and any(
            results["warmup_exits"].get(module) != 0 for module in COMPLETE_WARMUP_MODULES)
        if warmup_failed:
            reason = "A sequential shared-root warmup failed; the full task build and fresh axiom audit were not run"
            results["build_skipped_reason"] = reason
            results["audit_skipped_reason"] = reason
            (evidence / "skipped-verification.log").write_text(reason + "\n", encoding="utf-8")
            print("SKIPPED (gate remains FAIL): " + reason, flush=True)
        else:
            try:
                results["build_exit"] = shared.logged(
                    ["lake", "build", *("+" + PREFIX + "." + module + ":olean" for module in modules)], "build.log")
                if results["build_exit"] == 0:
                    audit = evidence / "N8N9_AxiomAudit.lean"
                    audit.write_text(audit_source(stage, modules, required), encoding="utf-8")
                    results["audit_exit"] = shared.logged(["lake", "env", "lean", str(audit)], "axioms.log")
                    output = (evidence / "axioms.log").read_text(encoding="utf-8")
                    marker = re.search(r"N8_N9_" + stage.upper() + r"_AXIOMS_PASSED: (\d+) declarations", output)
                    results["audit_success_marker"] = marker is not None
                    if marker:
                        results["audited_declaration_count"] = int(marker.group(1))
            except Exception as error:
                message = f"{type(error).__name__}: {error}"
                errors.append(message)
                (evidence / "driver-error.log").write_text(message + "\n", encoding="utf-8")
                print(message, file=sys.stderr, flush=True)
    if source_snapshot() != snapshots:
        errors.append("V2 source inventory or contents changed during verification")
    if config_snapshot() != configurations:
        errors.append("Verification configuration inventory or contents changed during verification")
    final_head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    final_diff = subprocess.check_output(["git", "diff", "--name-only", "HEAD", "--"], text=True)
    if final_head != head or final_diff.strip():
        errors.append("Exact head or tracked source state changed during verification")
    success = (not errors and results["build_exit"] == 0 and results["audit_exit"] == 0
               and results["audit_success_marker"])
    results["success"] = success
    if stage == "complete":
        results["n8b_status"] = (
            "Complete N8b task built and recursively audited at the exact selected head"
            if success else
            "Candidate: complete N8b task certification has not succeeded at this exact head"
        )
    results["elapsed_seconds"] = time.monotonic() - start
    (evidence / "result.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    summary = (f"# MOM Engine Step V2 — N8/N9 {stage}\n\n"
               + f"- Exact head: `{head}`\n"
               + f"- Selected modules: {len(modules)}\n"
               + f"- Task scope: {task_scope}.\n"
               + (f"- Optional shared-root warmup requested: {warmup_shared_roots}; exits: {results['warmup_exits']}.\n"
                  if stage == "complete" else "")
               + f"- Lake exit: {results['build_exit']}\n"
               + f"- Fresh Lean audit exit: {results['audit_exit']}\n"
               + f"- Loaded V2 declarations recursively audited: {results.get('audited_declaration_count', 0)}\n"
               + f"- Result: {'PASS' if success else 'FAIL'}\n"
               + f"- N8b status: {results['n8b_status']}.\n"
               + "- The registered task V2 gate remains required.\n")
    if results["build_skipped_reason"]:
        summary += "\nSkipped verification (not passed): " + results["build_skipped_reason"] + ".\n"
    if errors:
        summary += "\nVerification errors:\n\n" + "\n".join("- " + error for error in errors) + "\n"
    (evidence / "summary.md").write_text(summary, encoding="utf-8")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
            stream.write(summary)
    print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
