#!/usr/bin/env python3
"""Build every owned N4/N6 module and audit the entire loaded V2 environment.

This additional diagnostic gate follows the reviewed S3/S5 driver at
29eecadbb7b4ca6f3dfcc2fbe73ff357a37de881. It does not replace the complete
V2 or repository gates. Logging, token handling and the 600-second Lean
watchdog come from the shared V2 build driver.
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
EVIDENCE = ROOT / "v2-n4-n6-build"
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
OWNED_GROUPS = {
    "n4": (
        "N4CalibrationBinding",
        "N4CalibrationContracts",
        "N4ComputedLengths",
        "N4FrozenIdeals",
        "N4InnerScale",
        "N4NominalScale",
        "N4OriginalCapacity",
        "N4OriginalPrimeWindows",
        "N4PacketGeometry",
        "N4PaidSupport",
        "N4RecipeBridge",
        "N4ScaleProduct",
        "N4ScaleWindows",
        "N4SixthPattern",
        "N4SourceConditions",
        "N4UniformCapacity",
        "N4UniformThreshold",
        "OriginalCapacityContracts",
        "TasksOriginalCapacity",
    ),
    "n6": (
        "FullKappaContracts",
        "N6AnalyticChoices",
        "N6FullKappaConstruction",
        "N6OriginalAnalytic",
        "N6SourceBounds",
        "TasksFullKappa",
    ),
}
OWNED_MODULES = tuple(module for modules in OWNED_GROUPS.values() for module in modules)
# Both the build and the fresh audit import every owned module explicitly.
TARGETS = OWNED_MODULES
THEOREMS = {
    "TasksOriginalCapacity": (
        "HeckeSkeleton.Moments.EngineStepV2.Blueprint.originalCapacityTask",
        "HeckeSkeleton.Moments.EngineStepV2.Blueprint.originalCapacityTask_uniform",
    ),
    "TasksFullKappa": (
        "HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.fullKappaNormalization",
    ),
}
PUBLIC_THEOREMS = tuple(name for names in THEOREMS.values() for name in names)
FORBIDDEN = re.compile(r"\b(?:sorry|axiom|admit|native_decide|sorryAx)\b")
CONFIG_PATHS = (
    "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json",
    ".github/v2/build.py", ".github/v2/n4_n6.py", ".github/v2/manifest.json",
    ".github/workflows/mom-v2-n4-n6.yml",
    ".github/workflows/mom-engine-step-v2.yml", ".github/workflows/integration-build.yml",
)

# Reuse the shared implementations, including its process ownership checks.
code_only = v2_build.code_only
logged = v2_build.logged


def source_hashes() -> dict[str, str]:
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(TASK.glob("*.lean")) if path.is_file()}


def config_hashes() -> dict[str, str]:
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in CONFIG_PATHS if (ROOT / name).is_file()}


def preflight() -> tuple[list[str], dict[str, str]]:
    """Read-only checks; no Lean, Lake, process monitor or evidence writes."""
    errors = []
    discovered = {path.stem for pattern in ("N4*.lean", "N6*.lean")
                  for path in TASK.glob(pattern)} | {
                      "OriginalCapacityContracts", "FullKappaContracts", *THEOREMS}
    if discovered != set(OWNED_MODULES):
        errors.append("Owned N4/N6 module inventory changed: "
                      + repr(sorted(discovered.symmetric_difference(OWNED_MODULES))))
    if len(OWNED_MODULES) != 25 or len(set(OWNED_MODULES)) != len(OWNED_MODULES):
        errors.append("The fixed N4/N6 inventory must contain 25 distinct modules")
    try:
        manifest = json.loads((ROOT / ".github/v2/manifest.json").read_text(encoding="utf-8"))
        groups = manifest.get("groups") if isinstance(manifest, dict) else None
        if not isinstance(groups, list):
            raise ValueError("manifest.groups must be a list")
    except (OSError, ValueError) as error:
        errors.append("Cannot validate V2 manifest: " + str(error))
        groups = []
    for group_id, expected in OWNED_GROUPS.items():
        matches = [group for group in groups
                   if isinstance(group, dict) and group.get("id") == group_id]
        if len(matches) != 1:
            errors.append(f"Expected exactly one manifest group {group_id}; found {len(matches)}")
            continue
        group = matches[0]
        if group.get("proved") is not True:
            errors.append(f"Manifest group {group_id} must have proved=true")
        modules = group.get("modules")
        if not isinstance(modules, list) or not all(isinstance(name, str) for name in modules):
            errors.append(f"Manifest group {group_id} has an invalid module list")
        elif len(modules) != len(set(modules)) or set(modules) != set(expected):
            errors.append(f"Manifest group {group_id} differs from its fixed owned inventory: "
                          + repr(modules))
    for module in OWNED_MODULES:
        locations = [group.get("id") for group in groups if isinstance(group, dict)
                     and isinstance(group.get("modules"), list)
                     for name in group["modules"] if name == module]
        expected_group = next(group for group, modules in OWNED_GROUPS.items() if module in modules)
        if locations != [expected_group]:
            errors.append(f"Owned module {module} has unexpected manifest ownership: {locations}")
        path = TASK / (module + ".lean")
        if not path.is_file():
            errors.append("Missing owned source: " + str(path.relative_to(ROOT)))
            continue
        source = code_only(path.read_text(encoding="utf-8"))
        for match in FORBIDDEN.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: forbidden {match.group()}")
        for full_name in THEOREMS.get(module, ()):
            namespace, theorem = full_name.rsplit(".", 1)
            if not re.search(r"\btheorem\s+" + re.escape(theorem) + r"\b", source):
                errors.append("Missing public theorem declaration: " + full_name)
            if not re.search(r"\bnamespace\s+" + re.escape(namespace) + r"\b", source):
                errors.append("Missing public task namespace in " + module)
    if v2_build.MODULE_TIMEOUT_SECONDS != 600:
        errors.append("The shared per-module Lean watchdog must remain 600 seconds")
    snapshots = source_hashes()
    if not snapshots:
        errors.append("No V2 source files found")
    return errors, snapshots


def audit_source() -> str:
    imports = "\n".join("import " + PREFIX + "." + module for module in TARGETS)
    checks = "\n".join("#check " + name for name in PUBLIC_THEOREMS)
    required = ",\n".join("    `" + name for name in PUBLIC_THEOREMS)
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
""" + required + """ ]
  for name in required do
    unless names.contains name do
      throwError "Missing public N4/N6 theorem in audit environment: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"N4_N6_AXIOMS_PASSED: {names.size} declarations"
"""


def git_identity() -> dict[str, str]:
    return {
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "tree": subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], text=True).strip(),
        "parents": subprocess.check_output(["git", "show", "-s", "--format=%P", "HEAD"],
                                           text=True).strip(),
    }


def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    # logged resolves the shared module globals when invoked. In particular,
    # both commands use the unchanged shared Watcher and its failure handling.
    v2_build.EVIDENCE = EVIDENCE
    v2_build.WATCHDOG_RESULTS.clear()
    start = time.monotonic()
    errors, snapshots = preflight()
    config_snapshots = config_hashes()
    identity = git_identity()
    expected_head = os.environ.get("N4_N6_EXPECTED_HEAD")
    if expected_head and identity["head"] != expected_head:
        errors.append(f"Checkout head {identity['head']} differs from requested head {expected_head}")
    environment = {
        **identity,
        "expected_head": expected_head,
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "targets": [PREFIX + "." + module for module in TARGETS],
        "public_theorems": list(PUBLIC_THEOREMS),
        "owned_groups": OWNED_GROUPS,
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
                      f"PASS: {len(OWNED_MODULES)} owned modules match proved manifest groups; "
                      f"all {len(PUBLIC_THEOREMS)} public theorem declarations present.\n")
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
                audit_path = EVIDENCE / "N4N6_AxiomAudit.lean"
                audit_path.write_text(audit_source(), encoding="utf-8")
                results["audit_exit"] = logged(
                    ["lake", "env", "lean", str(audit_path)], "axioms.log")
                output = (EVIDENCE / "axioms.log").read_text(encoding="utf-8")
                marker = re.search(r"N4_N6_AXIOMS_PASSED: (\d+) declarations", output)
                results["audit_success_marker"] = marker is not None
                if marker:
                    results["audited_declaration_count"] = int(marker.group(1))
        except Exception as exception:
            message = f"{type(exception).__name__}: {exception}"
            errors.append(message)
            (EVIDENCE / "driver-error.log").write_text(message + "\n", encoding="utf-8")
            print(message, file=sys.stderr, flush=True)
    after_identity = git_identity()
    after_sources = source_hashes()
    after_configs = config_hashes()
    results["head_unchanged"] = after_identity == identity
    results["sources_unchanged"] = after_sources == snapshots
    results["verification_inputs_unchanged"] = after_configs == config_snapshots
    if not results["head_unchanged"]:
        errors.append("Git head, tree or parents changed during verification")
    for kind, before, after in (("Source", snapshots, after_sources),
                                ("Verification input", config_snapshots, after_configs)):
        for name in sorted(before.keys() | after.keys()):
            if before.get(name) != after.get(name):
                errors.append(kind + " changed during verification: " + name)
    (EVIDENCE / "postflight.json").write_text(json.dumps({
        **after_identity, "source_sha256": after_sources,
        "verification_sha256": after_configs,
    }, indent=2) + "\n", encoding="utf-8")
    results["elapsed_seconds"] = time.monotonic() - start
    success = (not errors and results["build_exit"] == 0
               and results["audit_exit"] == 0 and results["audit_success_marker"])
    results["success"] = success
    (EVIDENCE / "result.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    summary = ("# MOM Engine Step V2 — N4/N6\n\n"
               + f"- Exact head: `{environment['head']}`\n"
               + f"- Exact tree: `{environment['tree']}`\n"
               + f"- Build and fresh audit targets: all {len(TARGETS)} owned N4/N6 modules\n"
               + f"- Required public theorems: {len(PUBLIC_THEOREMS)}\n"
               + f"- Lake exit: {results['build_exit']}\n"
               + f"- Fresh Lean audit exit: {results['audit_exit']}\n"
               + f"- Loaded V2 declarations audited: {results.get('audited_declaration_count', 0)}\n"
               + f"- Per-module Lean timeout: {v2_build.MODULE_TIMEOUT_SECONDS}s\n"
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
