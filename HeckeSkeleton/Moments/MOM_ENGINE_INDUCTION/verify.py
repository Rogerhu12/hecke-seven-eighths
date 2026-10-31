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
    "SourceData", "SourceAdapter", "ScheduleCompatibility",
    "BaseTerminal", "SourceConsumers",
    "LengthStages", "BaseUniformity", "BranchedIntegralRecursion", "BaseBranch",
    "StepOutputAdapter", "BranchAssembly", "MomentProfileScaling", "ProfileControlScaling",
    "ProfileScaling", "SourceReindex",
    "CoreGeometry", "ReflectionBranch", "ReflectedRoot",
    "CoreStages", "GeneralBaseTerminal", "RecipeRoot", "ProfileSupremum",
    "CoreRecursion", "RecipeInduction", "AnnularMellin", "AnnularReflection",
    "OrdinaryReflection", "OrdinaryGamma", "OrdinaryReflectionDecay",
)
# Exact published interface files, kept under the producer's own namespace.
# These are imports of its canonical type, not competing local definitions.
PRODUCER_COMMIT = "9d50cdc3c83c60be3fcf0054c2a051a348969903"
PRODUCER_SOURCES = {
    "HeckeSkeleton/Moments/MOM_ENGINE_STEP/ReductionOutput.lean":
        "d3987e85aa8cb748c4f28fdd5797ee05a57b6e8974b405afcf1d1c144cc25df1",
    "HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentMoment.lean":
        "2ad71b4fcede7f07ec9fd898dc154aa37597d94ac0ea1a0e40f4d25f9612e391",
    "HeckeSkeleton/Moments/MOM_ENGINE_STEP/Pool.lean":
        "98a8f2bc36a6c8095bf7a169cd66ad763875ddd0d27236bcf879804daf525601",
}
SOURCE_COMMIT = 'acc0c254a8e9aef3d7e4b04c03782b28d81a8de8'
SOURCE_SOURCES = {'ExpansionInterfaces/DyadicCount.lean': 'a52681bd30d1e18c7c20b32165ddf11136870f357a21f267502caffb13f95331',
 'ExpansionInterfaces/DyadicShells.lean': 'a8330e7066ff7a3b3c53f9b4e8b6d6af137041a29cb6b0dab5d1bd31b3123610',
 'ExpansionInterfaces/ParameterChoices.lean': '371926930bf1e35af484c711c2e2d0668f4dd978f466ca34009c8c425fc86d61',
 'HeckeSkeleton/Base.lean': 'fa480e94cbdc76a93ea1da49df13078ee07e28fd4a43f1ed5e5316668ab93266',
 'HeckeSkeleton/ExpansionModels/Core.lean': '537b4afd82871e007cb438518e663e9a45c064c3cefecaa81a7ce557eda0f6f4',
 'HeckeSkeleton/ExpansionModels/DyadicMomentEnvelope.lean': '63bd533c5a5b4bd2be880ceeb22ef5880f0753e01a2139dfd051bf98f899fcea',
 'HeckeSkeleton/ExpansionModels/RecipeSchedule.lean': '48b1838bd6aa0a1c7229424653ca47c8ca8ebba1abe850592c968964e41a3b48',
 'HeckeSkeleton/ExpansionModels/ScaleCutoff.lean': '98a5345a361d159a7d17d02b7953cf7f9e562402cda8d3eec912321fd43cad65',
 'HeckeSkeleton/ExpansionModels/SharedWitnessRecipe.lean': '78011ed1fb6076260b23abae7dc22ab40c34686ec032a9e5e39e2b7a83d9d611',
 'HeckeSkeleton/ExpansionModels/SourceData.lean': '4b40c6980a5cb1e4e4f6b5196c4034049b6c9af107b8bf21356ad7f681f8cdc3',
 'HeckeSkeleton/ExpansionModels/SourceGeometry.lean': '71cf993ca28b14f63ed4fe02456e0227a0affdb9dc02c1bff156cb2d048b6419',
 'HeckeSkeleton/ExpansionModels/WitnessHeightNormalization.lean': '31c92678b8e973f1c1ff65ae9e0ff3d43c17c2d440c2a90d5fea63204ed58520',
 'HeckeSkeleton/Moments.lean': 'ad32874b4e7f6da6d8ae670ccc5c588d26ca796041c4906a5ce0adad6db435ba',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileControl.lean': '328a45dd8b9bea367aea65f9fd837482d3342c515550d3d1307c60bfe28c8ad1',
 'HeckeSkeleton/SourceData.lean': 'f8956f17c60594f51eb17349d0d94f55a9c412a54d764d1f5588d51f670f9345',
 'lakefile.toml': 'e3cec2fe7dd91f5d84903ece25f7dbc37c9f82dfe728a95c376e9bbec4ca3cac'}
REINDEX_COMMIT = '778b4220d3d4bc8538549bf74998a78e570d01d9'
REINDEX_SOURCES = {'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/FiniteSectorCore.lean': 'aec890cdfe84c6a6bb97fa3d48ac88117ced794a5ead2b5aded1b469d1d636eb', 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/FiniteSectorReindex.lean': 'c9cc4fb6c7156db541c69b1e50dd709cd198d9ab791572ffcb72e4857178de9b'}
CANONICAL_SOURCES = PRODUCER_SOURCES | SOURCE_SOURCES | REINDEX_SOURCES
SOURCE_MODULES = ("SkeletonFamily", "SkeletonSource")
EXCLUDED = {name + ".lean" for name in SOURCE_MODULES}
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
    "HeckeSkeleton.Moments.EngineInduction.skeletonSourceIndexEquiv",
    "HeckeSkeleton.Moments.EngineInduction.skeleton_uniformMomentBound_iff",
    "HeckeSkeleton.Moments.EngineInduction.skeleton_plainSource_of_generic_model_bounds",
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
    "HeckeSkeleton.Moments.EngineInduction.Source.SourceMomentIndexFor",
    "HeckeSkeleton.Moments.EngineInduction.Source.SourceMomentModelsFor",
    "HeckeSkeleton.Moments.EngineInduction.sourceFamily",
    "HeckeSkeleton.Moments.EngineInduction.moment_mesh_total_loss_budget",
    "HeckeSkeleton.Moments.EngineInduction.Node.normalizedEnergy_absolute_bound",
    "HeckeSkeleton.Moments.EngineInduction.Node.absoluteBaseComponents",
    "HeckeSkeleton.Moments.EngineInduction.Node.exists_absolute_base_components",
    "HeckeSkeleton.Moments.EngineInduction.Source.plainSource_of_dyadic_model_bounds",
    "HeckeSkeleton.Moments.EngineInduction.SourceFamily.uniformBound_of_rowWidth_le_from",
    "HeckeSkeleton.Moments.EngineInduction.slotProduct_sq_uniform_absolute_bound",
    "HeckeSkeleton.Moments.EngineInduction.uniform_absolute_base_components",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.comparison_earlier_of_lengths",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.positive_comparison_earlier",
    "HeckeSkeleton.Moments.EngineInduction.uniformBaseConstant_height_le",
    "HeckeSkeleton.Moments.EngineInduction.uniform_polynomial_height_base_components",
    "HeckeSkeleton.Moments.EngineInduction.BranchedIntegralStep.uniform_rank_bound",
    "HeckeSkeleton.Moments.EngineInduction.branchedIntegralStep_power_bound",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.baseBranch_mass",
    "HeckeSkeleton.Moments.EngineInduction.uniform_polynomial_height_base_branch",
    "HeckeSkeleton.Moments.EngineInduction.engineOutputToBranchedAt",
    "HeckeSkeleton.Moments.EngineInduction.engineOutputsToBranchedStep",
    "HeckeSkeleton.Moments.EngineInduction.engineOutputsToClosedParentReduction",
    "HeckeSkeleton.Moments.EngineInduction.BranchedIntegralAt.combine_mass",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.core_reflection_earlier",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.earlier_core_of_length",
    "HeckeSkeleton.Moments.EngineInduction.CoreReflectionData.toAt",
    "HeckeSkeleton.Moments.EngineInduction.CoreReflectionData.toAt_mass",
    "HeckeSkeleton.Moments.EngineInduction.general_uniform_polynomial_height_base_components",
    "HeckeSkeleton.Moments.EngineInduction.uniform_modelProfileControl_base_components",
    "HeckeSkeleton.Moments.EngineInduction.sliceControl_norm_le",
    "HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_slotCount_le",
    "HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_length",
    "HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_fitsMesh",
    "HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_uniform_profiles",
    "HeckeSkeleton.Moments.EngineInduction.Node.base_length_of_zero_padded_core",
    "HeckeSkeleton.Moments.EngineInduction.Node.base_length_of_positive_capacity",
    "HeckeSkeleton.Moments.EngineInduction.Node.quarterCentered_energy_decomposition",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.comparison_same_length_schedule",
    "HeckeSkeleton.Moments.EngineInduction.ReflectedComparisonData.earlier",
    "HeckeSkeleton.Moments.EngineInduction.ReflectedComparisonData.toAt",
    "HeckeSkeleton.Moments.EngineInduction.ReflectedComparisonData.toAt_mass",
    "HeckeSkeleton.Moments.EngineInduction.OuterReflectionAt.power_bound",
    "HeckeSkeleton.Moments.EngineInduction.ReflectedRootInput.sectorBound",
    "HeckeSkeleton.Moments.EngineInduction.paired_zero_slot_of_reflected_core",
    "HeckeSkeleton.Moments.EngineInduction.moment_mesh_loss_budget_with_outer_reflection",
    "HeckeSkeleton.Moments.EngineInduction.Node.plainPair_scaleProfiles",
    "HeckeSkeleton.Moments.EngineInduction.Node.energy_scaleProfiles",
    "HeckeSkeleton.Moments.EngineInduction.Node.normalizedEnergy_normalizeProfiles",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_source_reindex",
    "HeckeSkeleton.Moments.EngineInduction.engineOutput_zero_parameters",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.centeredComparisonBranch",
    "HeckeSkeleton.Moments.EngineInduction.CoreRecursionInput.toClosedParentReduction",
    "HeckeSkeleton.Moments.EngineInduction.Source.RecipeLocalInput.toParentReductionInput",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_zero_slot_recipe",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_recipe_below_one",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_recipe_endpoint",
    "HeckeSkeleton.Moments.EngineInduction.annularIdealSum_mellin",
    "HeckeSkeleton.Moments.EngineInduction.annularHeckeSum_mellin",
    "HeckeSkeleton.Moments.EngineInduction.annularHeckeSum_shift",
    "HeckeSkeleton.Moments.EngineInduction.annularHeckeSum_reflectedContour",
    "HeckeSkeleton.Moments.EngineInduction.pairedEnergy_normalizedMomentProfiles",
    "HeckeSkeleton.Moments.EngineInduction.sqrt_pairedEnergy_normalizedMomentProfiles",
    "HeckeSkeleton.Moments.EngineInduction.normalizedMomentProfiles_unit_control",
    "HeckeSkeleton.Moments.EngineInduction.annularHeckeSum_reflection",
    "HeckeSkeleton.Moments.EngineInduction.ordinaryGammaRatio_strip_bound",
    "HeckeSkeleton.Moments.EngineInduction.ordinaryReflectedProfile_decay_seminorm",
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
        require(all("MOM_ENGINE_INDUCTION." + source not in code for source in SOURCE_MODULES),
                f"{path.name} imports the separate skeleton adapter")
        declared.update(declarations(path))
        hashes[str(path.relative_to(ROOT))] = digest(path)
    require(set(printed) == declared,
            f"Audit declaration inventory mismatch: missing={sorted(declared - set(printed))}, "
            f"extra={sorted(set(printed) - declared)}")
    require(REQUIRED_TARGETS <= declared,
            f"Missing target declarations: {sorted(REQUIRED_TARGETS - declared)}")
    for relative, pinned in CANONICAL_SOURCES.items():
        path = ROOT / relative
        require(path.is_file(), f"Missing canonical producer interface: {relative}")
        actual = digest(path)
        require(actual == pinned,
                f"Canonical imported source differs from its published pin: {relative}")
        hashes[relative] = actual
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
    paths += list(CANONICAL_SOURCES)
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
                  producer_interface_commit=PRODUCER_COMMIT,
                  producer_interface_sha256=PRODUCER_SOURCES,
                  canonical_source_commit=SOURCE_COMMIT, canonical_source_sha256=SOURCE_SOURCES,
                  finite_reindex_commit=REINDEX_COMMIT, finite_reindex_sha256=REINDEX_SOURCES,
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


def skeleton_inventory() -> tuple[dict[str, str], list[str]]:
    hashes: dict[str, str] = {}
    declared: set[str] = set()
    for module in SOURCE_MODULES:
        path = TASK / (module + ".lean")
        subprocess.run(["git", "ls-files", "--error-unmatch", "--",
                        str(path.relative_to(ROOT))], cwd=ROOT, check=True,
                       stdout=subprocess.DEVNULL)
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|sorryAx|native_decide)\b",
                               lean_code(path.read_text()))
        require(not forbidden, f"New proof shortcut in {path.name}: {forbidden}")
        hashes[str(path.relative_to(ROOT))] = digest(path)
        declared.update(declarations(path))
    names = sorted(declared)
    require(REQUIRED_SKELETON_TARGETS <= set(names),
            f"Missing source adapter targets: {sorted(REQUIRED_SKELETON_TARGETS - set(names))}")
    return hashes, names


def skeleton_preflight(expected: str, output: Path) -> None:
    preflight(expected, output)
    source_hash, names = skeleton_inventory()
    record = json.loads((output / "preflight.json").read_text())
    record.update(kind="skeleton-integration", skeleton_source_sha256=source_hash,
                  integration_declarations=names, upstream_probes=list(UPSTREAM_PROBES))
    (output / "preflight.json").write_text(json.dumps(record, indent=2) + "\n")
    # Generated audit commands and evidence stay outside the source checkout.
    audit = "\n".join("import " + PREFIX + "." + module for module in SOURCE_MODULES) + "\n\n"
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
    require(imports == [PREFIX + "." + module for module in SOURCE_MODULES]
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


def original_check(expected: str, output: Path) -> None:
    """Enforce the task's original-name acceptance gate after source compilation."""
    verify_checkout(expected)
    integration = json.loads((output / "verification.json").read_text())
    require(integration.get("head_sha") == expected
            and integration.get("status") == "integration-compiled",
            "Original targets require successful exact-head source integration")
    log = output / "upstream-axioms.log"
    require(digest(log) == integration["upstream_axiom_log_sha256"],
            "Original target axiom log changed after integration verification")
    records = axiom_records(log.read_text(), set(UPSTREAM_PROBES), ALLOWED | {"sorryAx"})
    targets = UPSTREAM_PROBES[:3]
    unexpected = {name: sorted(set(records[name]) - ALLOWED) for name in targets
                  if set(records[name]) - ALLOWED}
    result = dict(head_sha=expected, status="passed" if not unexpected else "blocked",
                  targets=list(targets), axioms={name: records[name] for name in targets},
                  allowed_axioms=sorted(ALLOWED), unexpected_axioms=unexpected,
                  upstream_axiom_log_sha256=digest(log))
    (output / "original-targets.json").write_text(json.dumps(result, indent=2) + "\n")
    for name in targets:
        print(name + ": " + json.dumps(records[name]))
    require(not unexpected,
            "Original target axiom gate failed: " + json.dumps(unexpected)
            + ". Conditional clean theorems do not satisfy this acceptance gate.")
    print(f"PASS original targets: {len(targets)} declarations at {expected}; "
          f"all axioms belong to {sorted(ALLOWED)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    phases = {"preflight": preflight, "check": check,
              "skeleton-preflight": skeleton_preflight, "skeleton-check": skeleton_check,
              "original-check": original_check}
    parser.add_argument("phase", choices=tuple(phases))
    parser.add_argument("--expected-sha", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT), "Place verification logs outside the repository")
    phases[args.phase](args.expected_sha, output)


if __name__ == "__main__":
    main()
