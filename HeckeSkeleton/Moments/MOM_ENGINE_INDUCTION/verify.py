#!/usr/bin/env python3
"""Validate the exact-head native build and recursive axiom audit for this task.

The workflow runs Lake and Lean explicitly with pipefail before invoking `check`.
All generated records live in the caller's output directory (RUNNER_TEMP in CI).
The existing skeleton adapter is a separate integration boundary: it imports
admitted upstream definitions and is not included in the clean proof target.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import resource
import shutil
import subprocess
from pathlib import Path

TASK = Path(__file__).resolve().parent
ROOT = TASK.parents[2]
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION"
MODULES = (
    "Order", "Recursion", "IntegralRecursion", "Reduction", "Family", "Terminal", "ExceptionalCounting",
    "TerminalCertificate", "Interface", "Centering", "Induction", "ChildStepCompatibility",
    "RootNormalization", "KernelReduction", "LogNormProfiles",
)
EXCLUDED = {"SkeletonFamily.lean"}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
COMPILER_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
UPSTREAM_PROBES = (
    "HeckeSkeleton.paired_zero_slot_models",
    "HeckeSkeleton.paired_positive_below_one",
    "HeckeSkeleton.paired_positive_endpoint",
    "HeckeSkeleton.targetData",
    "HeckeSkeleton.momentModels",
)
REQUIRED_SKELETON_TARGETS = {
    "HeckeSkeleton.Moments.EngineInduction.paired_zero_slot_models_of_parent_reduction",
    "HeckeSkeleton.Moments.EngineInduction.paired_positive_below_one_of_parent_reduction",
    "HeckeSkeleton.Moments.EngineInduction.paired_positive_endpoint_of_parent_reduction",
}
REQUIRED_TARGETS = {
    "HeckeSkeleton.Moments.EngineInduction.paired_zero_slot_models",
    "HeckeSkeleton.Moments.EngineInduction.paired_positive_below_one",
    "HeckeSkeleton.Moments.EngineInduction.paired_positive_endpoint",
    "HeckeSkeleton.Moments.EngineInduction.ClosedParentReduction.energy_bound",
    "HeckeSkeleton.Moments.EngineInduction.ParentReductionInput.sectorBound",
    "HeckeSkeleton.Moments.EngineInduction.RawParentReduction.closeTerminals",
    "HeckeSkeleton.Moments.EngineInduction.LocalStep.bound",
    "HeckeSkeleton.Moments.EngineInduction.LocalStep.uniform_rank_bound",
    "HeckeSkeleton.Moments.EngineInduction.IntegralStep.bound",
    "HeckeSkeleton.Moments.EngineInduction.IntegralStep.uniform_rank_bound",
    "HeckeSkeleton.Moments.EngineInduction.Reduction.power_bound",
    "HeckeSkeleton.Moments.EngineInduction.normalized_child_transfer",
    "HeckeSkeleton.Moments.EngineInduction.repaired_child_for_recursion",
    "HeckeSkeleton.Moments.EngineInduction.SourceFamily.uniformBound_of_dyadic_rowWidth",
    "HeckeSkeleton.Moments.EngineInduction.CommonKernelReduction.toIntegralStep",
    "HeckeSkeleton.Moments.EngineInduction.CommonKernelReduction.toIntegralStep_mass",
    "HeckeSkeleton.Moments.EngineInduction.CommonKernelReduction.toRawParentReduction",
    "HeckeSkeleton.Moments.EngineInduction.logNormSeparatedProfiles_plainPolynomial₁",
    "HeckeSkeleton.Moments.EngineInduction.logNormSeparatedProfiles_plainPolynomial₂",
    "HeckeSkeleton.Moments.EngineInduction.logNormSeparatedProfiles_primePolynomial",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def runner_resources() -> dict:
    disk = shutil.disk_usage(ROOT)
    result = dict(system=platform.system(), kernel=platform.release(), cpu_count=os.cpu_count(),
                  lean_num_threads=os.environ.get("LEAN_NUM_THREADS"),
                  disk_total_bytes=disk.total, disk_free_bytes=disk.free,
                  address_space_limit=list(resource.getrlimit(resource.RLIMIT_AS)),
                  open_file_limit=list(resource.getrlimit(resource.RLIMIT_NOFILE)))
    mapping_limit = Path("/proc/sys/vm/max_map_count")
    if mapping_limit.is_file():
        result["vm_max_map_count"] = int(mapping_limit.read_text())
    memory = Path("/proc/meminfo")
    if memory.is_file():
        for line in memory.read_text().splitlines():
            name, _, value = line.partition(":")
            if name in {"MemTotal", "MemAvailable", "SwapTotal"}:
                result[name + "_kB"] = int(value.split()[0])
    return result


def command(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def lean_code(text: str) -> str:
    """Remove nested Lean comments, retaining lines and quoted strings."""
    result: list[str] = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        char = text[i]
        pair = text[i:i + 2]
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
            result.append(char)
            i += 1
            if char == "\\" and i < len(text):
                result.append(text[i])
                i += 1
            elif char == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            result.append("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end == -1:
                end = len(text)
            result.append(" " * (end - i))
            i = end
        else:
            result.append(char)
            quoted = char == '"'
            i += 1
    require(depth == 0, "Unclosed Lean comment in audited source")
    return "".join(result)


def declarations(path: Path) -> set[str]:
    """Inventory explicit public declarations in these conventionally laid-out files."""
    scopes: list[tuple[str, str]] = []
    names: set[str] = set()
    declaration = re.compile(
        r"^(?:@\[[^\]]*\]\s*)*"
        r"(?P<modifiers>(?:(?:noncomputable|protected|private)\s+)*)"
        r"(?:def|abbrev|theorem|lemma|structure|inductive)\s+(?P<name>[^\s({:]+)"
    )
    for raw_line in lean_code(path.read_text()).splitlines():
        line = raw_line.lstrip()
        namespace = re.match(r"^namespace\s+(\S+)", line)
        section = re.match(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$", line)
        end = re.match(r"^end(?:\s+(\S+))?\s*$", line)
        if namespace:
            scopes.append(("namespace", namespace[1]))
        elif section:
            scopes.append(("section", section[1] or ""))
        elif end:
            require(bool(scopes), f"Unmatched end in {path.name}")
            scopes.pop()
        else:
            match = declaration.match(line)
            if match and "private" not in match["modifiers"].split():
                namespace_name = ".".join(name for kind, name in scopes if kind == "namespace")
                names.add(".".join(filter(None, (namespace_name, match["name"]))))
    return names


def audit_commands(text: str) -> tuple[list[str], list[str]]:
    imports: list[str] = []
    printed: list[str] = []
    for raw_line in lean_code(text).splitlines():
        line = raw_line.strip()
        if not line:
            continue
        imported = re.fullmatch(r"import\s+(\S+)", line)
        audited = re.fullmatch(r"#print axioms\s+(\S+)", line)
        require(imported is not None or audited is not None,
                f"Audit.lean contains a command other than an import or #print axioms: {line}")
        if imported is not None:
            imports.append(imported[1])
        else:
            assert audited is not None
            printed.append(audited[1])
    return imports, printed


def inventory() -> tuple[dict[str, str], list[str]]:
    expected_files = {name + ".lean" for name in MODULES} | {"Audit.lean"} | EXCLUDED
    actual_files = {path.name for path in TASK.glob("*.lean")}
    require(actual_files == expected_files,
            f"Update the audit module inventory: missing={sorted(expected_files - actual_files)}, "
            f"unlisted={sorted(actual_files - expected_files)}")
    imports, printed = audit_commands((TASK / "Audit.lean").read_text())
    require(len(imports) == len(MODULES)
            and set(imports) == {PREFIX + "." + module for module in MODULES},
            "Audit.lean must import exactly the clean task modules listed in MODULES")
    require(len(printed) == len(set(printed)), "Duplicate #print axioms declarations")
    declared: set[str] = set()
    hashes = {}
    for module in MODULES:
        path = TASK / (module + ".lean")
        code = lean_code(path.read_text())
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|sorryAx|native_decide)\b", code)
        require(not forbidden, f"Forbidden proof shortcut in {path.name}: {forbidden}")
        require(not re.search(r"^import\s+HeckeSkeleton\.Moments(?:\s|$)", code, re.M),
                f"{path.name} imports the admitted skeleton")
        require("MOM_ENGINE_INDUCTION.SkeletonFamily" not in code,
                f"{path.name} imports the separate skeleton adapter")
        declared.update(declarations(path))
        hashes[str(path.relative_to(ROOT))] = digest(path)
    require(set(printed) == declared,
            f"Audit declaration inventory mismatch: missing={sorted(declared - set(printed))}, "
            f"extra={sorted(set(printed) - declared)}")
    require(REQUIRED_TARGETS <= declared,
            f"Missing target declarations: {sorted(REQUIRED_TARGETS - declared)}")
    for path in (TASK / "Audit.lean", TASK / "verify.py", ROOT / "lean-toolchain",
                 ROOT / "lake-manifest.json", ROOT / "lakefile.toml"):
        hashes[str(path.relative_to(ROOT))] = digest(path)
    return hashes, sorted(declared)


def verify_checkout(expected: str) -> None:
    require(re.fullmatch(r"[0-9a-f]{40}", expected) is not None, "Expected a full commit SHA")
    actual = command("git", "rev-parse", "HEAD")
    require(actual == expected, f"Checking {actual}, expected head {expected}")
    paths = [str((TASK / (module + ".lean")).relative_to(ROOT)) for module in MODULES]
    paths += [str((TASK / name).relative_to(ROOT)) for name in ("Audit.lean", "verify.py")]
    paths += [".github/workflows/mom-engine-induction.yml"]
    subprocess.run(["git", "ls-files", "--error-unmatch", "--"] + paths, cwd=ROOT,
                   check=True, stdout=subprocess.DEVNULL)
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)


def preflight(expected: str, output: Path) -> None:
    verify_checkout(expected)
    hashes, names = inventory()
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain pin changed")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    package = next((p for p in manifest["packages"] if p["name"] == "mathlib"), None)
    require(package is not None and package.get("rev") == MATHLIB, "Mathlib manifest pin changed")
    actual_mathlib = command("git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
    require(actual_mathlib == MATHLIB, f"Unexpected Mathlib checkout: {actual_mathlib}")
    version = command("lake", "env", "lean", "--version")
    require("version 4.35.0-rc3," in version and COMPILER_COMMIT in version,
            f"Unexpected compiler: {version}")
    output.mkdir(parents=True, exist_ok=True)
    record = dict(head_sha=expected, toolchain=TOOLCHAIN, compiler=version, mathlib=MATHLIB,
                  source_sha256=hashes, declarations=names,
                  modules=[PREFIX + "." + name for name in MODULES],
                  excluded_integration_modules=sorted(EXCLUDED),
                  runner_resources=runner_resources())
    (output / "preflight.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Preflight: exact head {expected}, {len(MODULES)} modules, {len(names)} declarations")
    print("Runner resources: " + json.dumps(record["runner_resources"], sort_keys=True))


def axiom_records(text: str, expected: set[str],
                  allowed: set[str] = ALLOWED) -> dict[str, list[str]]:
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    pairs = re.findall(pattern, text, re.S)
    names = [name for name, _ in pairs]
    require(len(names) == len(set(names)), "Duplicate axiom audit records")
    records = {name: sorted({item.strip() for item in axioms.split(",") if item.strip()})
               for name, axioms in pairs}
    require(set(records) == expected,
            f"Incomplete axiom output: missing={sorted(expected - records.keys())}, "
            f"unexpected={sorted(records.keys() - expected)}")
    for name, axioms in records.items():
        require(set(axioms) <= allowed,
                f"{name}: disallowed axioms {sorted(set(axioms) - allowed)}")
    return records


def check(expected: str, output: Path) -> None:
    verify_checkout(expected)
    hashes, names = inventory()
    before = json.loads((output / "preflight.json").read_text())
    require(before["head_sha"] == expected, "Preflight belongs to another commit")
    require(before["source_sha256"] == hashes, "Sources changed during verification")
    require(before["declarations"] == names, "Audited declaration inventory changed")
    build = (output / "build.log").read_text()
    audit = (output / "axioms.log").read_text()
    for kind, log in (("BUILD", build), ("AUDIT", audit)):
        require(f"MOM_ENGINE_INDUCTION_{kind}_OK {expected}" in log,
                f"Missing successful {kind.lower()} completion marker")
        require(re.search(r"(?:^|\n)(?:[^\n]*?:\d+:\d+: )?error:", log) is None,
                f"Error diagnostic in {kind.lower()} log")
    records = axiom_records(audit, set(names))
    record = dict(before, status="passed", axioms=records,
                  allowed_axioms=sorted(ALLOWED),
                  build_log_sha256=digest(output / "build.log"),
                  axiom_log_sha256=digest(output / "axioms.log"))
    (output / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: {len(MODULES)} modules and {len(names)} declarations at {expected}; "
          f"all axioms belong to {sorted(ALLOWED)}")


def skeleton_inventory() -> tuple[str, list[str]]:
    path = TASK / "SkeletonFamily.lean"
    subprocess.run(["git", "ls-files", "--error-unmatch", "--",
                    str(path.relative_to(ROOT))], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|sorryAx|native_decide)\b",
                           lean_code(path.read_text()))
    require(not forbidden, f"New proof shortcut in skeleton adapter: {forbidden}")
    names = sorted(declarations(path))
    require(REQUIRED_SKELETON_TARGETS <= set(names),
            f"Missing source adapter targets: {sorted(REQUIRED_SKELETON_TARGETS - set(names))}")
    return digest(path), names


def skeleton_preflight(expected: str, output: Path) -> None:
    preflight(expected, output)
    source_hash, names = skeleton_inventory()
    record = json.loads((output / "preflight.json").read_text())
    record.update(kind="skeleton-integration", skeleton_source_sha256=source_hash,
                  integration_declarations=names, upstream_probes=list(UPSTREAM_PROBES))
    (output / "preflight.json").write_text(json.dumps(record, indent=2) + "\n")
    # Generated audit commands and evidence stay outside the source checkout.
    audit = "import " + PREFIX + ".SkeletonFamily\n\n"
    audit += "\n".join("#print axioms " + name for name in names) + "\n"
    (output / "SkeletonAudit.lean").write_text(audit)
    upstream = "import HeckeSkeleton.Moments\n\n"
    upstream += "-- Existing declarations; excluded from the new declaration inventory.\n"
    upstream += "\n".join("#print axioms " + name for name in UPSTREAM_PROBES) + "\n"
    (output / "UpstreamAudit.lean").write_text(upstream)
    print(f"Separate skeleton integration: {len(names)} declarations; "
          "inherited sorryAx is recorded, not accepted by the clean audit")
    print(f"Separate upstream probes: {len(UPSTREAM_PROBES)} existing declarations")


def skeleton_check(expected: str, output: Path) -> None:
    verify_checkout(expected)
    hashes, names = inventory()
    source_hash, integration_names = skeleton_inventory()
    before = json.loads((output / "preflight.json").read_text())
    require(before.get("kind") == "skeleton-integration", "Wrong preflight kind")
    require(before["head_sha"] == expected, "Preflight belongs to another commit")
    require(before["source_sha256"] == hashes and before["declarations"] == names,
            "Clean sources changed during integration verification")
    require(before["skeleton_source_sha256"] == source_hash
            and before["integration_declarations"] == integration_names,
            "Skeleton adapter changed during integration verification")
    require(before["upstream_probes"] == list(UPSTREAM_PROBES),
            "Upstream probe inventory changed")
    imports, printed = audit_commands((output / "SkeletonAudit.lean").read_text())
    require(imports == [PREFIX + ".SkeletonFamily"]
            and printed == integration_names,
            "Generated integration audit commands changed")
    imports, printed = audit_commands((output / "UpstreamAudit.lean").read_text())
    require(imports == ["HeckeSkeleton.Moments"] and printed == list(UPSTREAM_PROBES),
            "Generated upstream audit commands changed")
    for kind, filename in (("BUILD", "build.log"), ("AUDIT", "axioms.log"),
                           ("UPSTREAM_BUILD", "upstream-build.log"),
                           ("UPSTREAM_AUDIT", "upstream-axioms.log")):
        log = (output / filename).read_text()
        require(f"MOM_ENGINE_INDUCTION_SKELETON_{kind}_OK {expected}" in log,
                f"Missing successful skeleton {kind.lower()} completion marker")
        require(re.search(r"(?:^|\n)(?:[^\n]*?:\d+:\d+: )?error:", log) is None,
                f"Error diagnostic in skeleton {kind.lower()} log")
    integration_allowed = ALLOWED | {"sorryAx"}
    records = axiom_records((output / "axioms.log").read_text(),
                            set(integration_names), integration_allowed)
    upstream_records = axiom_records((output / "upstream-axioms.log").read_text(),
                                     set(UPSTREAM_PROBES), integration_allowed)
    inherited = sorted(name for name in integration_names if "sorryAx" in records[name])
    upstream_inherited = sorted(name for name in UPSTREAM_PROBES
                                if "sorryAx" in upstream_records[name])
    record = dict(before, status="integration-compiled",
                  axioms={name: records[name] for name in integration_names},
                  upstream_probe_axioms=upstream_records,
                  integration_allowed_axioms=sorted(integration_allowed),
                  declarations_with_inherited_sorryAx=inherited,
                  upstream_probes_with_sorryAx=upstream_inherited,
                  build_log_sha256=digest(output / "build.log"),
                  axiom_log_sha256=digest(output / "axioms.log"),
                  upstream_build_log_sha256=digest(output / "upstream-build.log"),
                  upstream_axiom_log_sha256=digest(output / "upstream-axioms.log"))
    (output / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS integration compilation: {len(integration_names)} declarations at {expected}; "
          f"{len(inherited)} inherit sorryAx. This is separate from the clean axiom gate.")
    print("Existing upstream probes depending on sorryAx: " + json.dumps(upstream_inherited))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    phases = {"preflight": preflight, "check": check,
              "skeleton-preflight": skeleton_preflight, "skeleton-check": skeleton_check}
    parser.add_argument("phase", choices=tuple(phases))
    parser.add_argument("--expected-sha", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT), "Place verification logs outside the repository")
    phases[args.phase](args.expected_sha, output)


if __name__ == "__main__":
    main()
