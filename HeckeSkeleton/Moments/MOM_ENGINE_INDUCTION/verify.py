#!/usr/bin/env python3
"""Verify all conditional paired-induction modules at one exact commit.

The explicit STEP hypothesis remains a theorem parameter. The original-name
unconditional integration (MOM_ENGINE_INTEGRATION) is not part of this gate:
it lands after the STEP producer modules it needs are merged into the base.
Evidence belongs outside the checkout, in RUNNER_TEMP on Actions.
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
import tomllib
from functools import lru_cache
from pathlib import Path

TASK = Path(__file__).resolve().parent
ROOT = TASK.parents[2]
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION"
INTEGRATION_PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION"
STEP_PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP"
SCOPE = "conditional-engine-induction"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
COMPILER_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
STEP_HYPOTHESIS = "HeckeSkeleton.Moments.EngineInduction.Source.PairedStepHypothesis"
CONDITIONAL_TARGETS = (
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_zero_slot_models_of_step",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_below_one_of_step",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_endpoint_of_step",
)
REQUIRED_TARGETS = set(CONDITIONAL_TARGETS) | {
    STEP_HYPOTHESIS,
    "HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeScalarInputs_of_step",
    "HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeCompleteMellinFamily_preparation",
    "HeckeSkeleton.Moments.EngineInduction.Source.RecipeScalarLocalInput.sectorBound",
    "HeckeSkeleton.Moments.EngineInduction.MellinCoreRecursionInput.energy_bound",
    "HeckeSkeleton.Moments.EngineInduction.scalarRecursion_power_bound",
    "HeckeSkeleton.Moments.EngineInduction.Source.uniformMomentBound_recipe_physical",
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
        r"(?:def|abbrev|theorem|lemma|structure|inductive|class)\s+(?P<name>[^\s({:]+)"
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


def core_modules() -> list[str]:
    return sorted(path.stem for path in TASK.glob("*.lean") if path.name != "Audit.lean")


def generate() -> None:
    modules = core_modules()
    names: set[str] = set()
    for module in modules:
        names.update(declarations(TASK / (module + ".lean")))
    text = "/- Complete declaration audit for the conditional induction. -/\n"
    text += "\n".join("import " + PREFIX + "." + name for name in modules) + "\n\n"
    text += "\n".join("#print axioms " + name for name in sorted(names)) + "\n"
    (TASK / "Audit.lean").write_text(text)
    print(f"Generated Audit.lean for {len(modules)} modules and {len(names)} declarations")


@lru_cache(maxsize=1)
def repository_layout() -> tuple[tuple[Path, ...], tuple[Path, ...]]:
    """Resolve every library source root, including repository path packages."""
    manifest_path = ROOT / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    package_roots = [ROOT]
    for package in manifest["packages"]:
        if package["type"] == "path":
            package_root = (ROOT / package["dir"]).resolve()
            require(package_root.is_relative_to(ROOT),
                    f"Untracked path dependency outside the checkout: {package_root}")
            package_roots.append(package_root)
    sources: list[Path] = []
    configs: list[Path] = [manifest_path]
    for package_root in package_roots:
        config_path = package_root / "lakefile.toml"
        require(config_path.is_file(), f"Cannot inspect path-package configuration: {config_path}")
        config = tomllib.loads(config_path.read_text())
        configs.append(config_path)
        default = config.get("srcDir", ".")
        directories = [default] + [library.get("srcDir", default)
                                   for library in config.get("lean_lib", [])]
        for directory in directories:
            source_root = (package_root / directory).resolve()
            require(source_root.is_relative_to(ROOT),
                    f"Source directory lies outside the checkout: {source_root}")
            if source_root not in sources:
                sources.append(source_root)
        package_manifest = package_root / "lake-manifest.json"
        if package_manifest.is_file() and package_manifest not in configs:
            configs.append(package_manifest)
    return tuple(sources), tuple(configs)


def repository_source(module: str) -> Path | None:
    relative = Path(module.replace(".", "/") + ".lean")
    for base in repository_layout()[0]:
        path = base / relative
        if path.is_file():
            return path
    return None


def source_closure(roots: list[str]) -> tuple[dict[str, str], list[str], list[str]]:
    seen: set[str] = set()
    external: set[str] = set()
    hashes: dict[str, str] = {}
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = repository_source(module)
        if path is None:
            external.add(module)
            continue
        hashes[str(path.relative_to(ROOT))] = digest(path)
        for line in lean_code(path.read_text()).splitlines():
            match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$", line)
            if match:
                # Lean's module system permits `import all Foo` and meta
                # imports. These modifiers are not module names.
                imported = [name for name in match[1].split() if name not in {"all", "meta"}]
                require(bool(imported), f"Import without a module in {path}: {line}")
                require(all(re.fullmatch(r"[A-Za-z0-9_'.]+", name) for name in imported),
                        f"Unrecognized import in {path}: {line}")
                pending.extend(imported)
    return dict(sorted(hashes.items())), sorted(seen - external), sorted(external)


def source_inventory() -> dict:
    modules = core_modules()
    require(bool(modules), "The core module directory is empty")
    roots = [PREFIX + "." + module for module in modules]
    imports, printed = audit_commands((TASK / "Audit.lean").read_text())
    require(imports == roots, "Audit.lean must import every core module once in sorted order")
    require(len(printed) == len(set(printed)), "Duplicate axiom audit declarations")
    declared: set[str] = set()
    for module in modules:
        path = TASK / (module + ".lean")
        code = lean_code(path.read_text())
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|sorryAx|native_decide)\b", code)
        require(not forbidden, f"Forbidden proof shortcut in {path.name}: {forbidden}")
        names = declarations(path)
        require(not (declared & names), f"Duplicate public declarations in {path.name}")
        declared.update(names)
    require(set(printed) == declared,
            f"Audit declaration mismatch: missing={sorted(declared - set(printed))}, "
            f"extra={sorted(set(printed) - declared)}")
    require(REQUIRED_TARGETS <= declared, f"Missing targets: {sorted(REQUIRED_TARGETS - declared)}")
    hashes, closure, external = source_closure(roots)
    require("HeckeSkeleton.Moments" not in closure, "Conditional core imports the integrated skeleton")
    require(not any(m.startswith(INTEGRATION_PREFIX + ".") for m in closure),
            "Conditional core imports a deferred integration module")
    step = sorted(m for m in closure if m.startswith(STEP_PREFIX + "."))
    permitted = json.loads((TASK / "step-interface-modules.json").read_text())
    require(isinstance(permitted, list) and all(isinstance(m, str) for m in permitted),
            "Invalid STEP interface manifest")
    require(permitted == sorted(set(permitted)), "STEP interface manifest is not canonical")
    require(step == permitted,
            f"STEP closure changed: new={sorted(set(step) - set(permitted))}, "
            f"unused={sorted(set(permitted) - set(step))}")
    for forbidden in ("ActualGaussFiniteLeaves", "ExceptionalOriginalLabel", "PairedEngineStep",
                      "CanonicalPrimitiveUniformEngine", "CanonicalPrimitiveDirectEngine",
                      "CanonicalPrimitivePooledEngine"):
        require(STEP_PREFIX + "." + forbidden not in closure,
                f"Conditional gate imports STEP producer {forbidden}")
    for path in (TASK / "Audit.lean", TASK / "verify.py", TASK / "step-interface-modules.json",
                 ROOT / "lean-toolchain", ROOT / ".github/workflows/mom-engine-induction.yml",
                 *repository_layout()[1]):
        hashes[str(path.relative_to(ROOT))] = digest(path)
    return dict(modules=roots, declarations=sorted(declared),
                source_sha256=dict(sorted(hashes.items())), repository_import_closure=closure,
                external_imports=external, step_interface_modules=step)


def verify_checkout(expected: str, paths: list[str] | None = None) -> None:
    require(re.fullmatch(r"[0-9a-f]{40}", expected) is not None, "Expected a full commit SHA")
    actual = command("git", "rev-parse", "HEAD")
    require(actual == expected, f"Checking {actual}, expected head {expected}")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=ROOT,
                   check=True, stdout=subprocess.DEVNULL)
    if paths:
        subprocess.run(["git", "ls-files", "--error-unmatch", "--"] + sorted(set(paths)),
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)


def environment() -> dict:
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain pin changed")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = manifest["packages"]
    mathlib = next((p for p in packages if p["name"] == "mathlib"), None)
    require(mathlib is not None and mathlib.get("rev") == MATHLIB, "Mathlib pin changed")
    revisions: dict[str, str] = {}
    for package in packages:
        if package["type"] != "git":
            continue
        name = package["name"]
        checkout = ROOT / manifest.get("packagesDir", ".lake/packages") / name
        actual = command("git", "-C", str(checkout), "rev-parse", "HEAD")
        require(actual == package["rev"], f"Unexpected {name} checkout: {actual}")
        subprocess.run(["git", "-C", str(checkout), "diff", "--exit-code", "HEAD", "--"],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        revisions[name] = actual
    version = command("lake", "env", "lean", "--version")
    require("version 4.35.0-rc3," in version and COMPILER_COMMIT in version,
            f"Unexpected compiler: {version}")
    return dict(toolchain=TOOLCHAIN, compiler=version, mathlib=MATHLIB, dependency_revisions=revisions)


def preflight(expected: str, output: Path) -> None:
    verify_checkout(expected)
    inventory = source_inventory()
    verify_checkout(expected, list(inventory["source_sha256"]))
    record = dict(head_sha=expected, scope=SCOPE, step_hypothesis=STEP_HYPOTHESIS,
                  conditional_targets=list(CONDITIONAL_TARGETS),
                  unconditional_integration="not-checked-by-this-gate", **inventory,
                  **environment(), runner_resources=runner_resources())
    output.mkdir(parents=True, exist_ok=True)
    (output / "preflight.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Conditional preflight: {expected}, {len(inventory['modules'])} modules, "
          f"{len(inventory['declarations'])} declarations; {len(inventory['step_interface_modules'])} STEP interface modules")


def successful_log(path: Path, marker: str) -> str:
    log = path.read_text()
    require(marker in log, f"Missing completion marker in {path.name}: {marker}")
    require(re.search(r"(?:^|\n)(?:[^\n]*?:\d+:\d+: )?error:", log) is None,
            f"Error diagnostic in {path.name}")
    return log


def check(expected: str, output: Path) -> None:
    verify_checkout(expected)
    inventory = source_inventory()
    before = json.loads((output / "preflight.json").read_text())
    require(before.get("head_sha") == expected and before.get("scope") == SCOPE,
            "Preflight belongs to another commit or verification scope")
    for key, value in inventory.items():
        require(before.get(key) == value, f"Inventory changed during verification: {key}")
    for key, value in environment().items():
        require(before.get(key) == value, f"Environment changed during verification: {key}")
    successful_log(output / "build.log", f"MOM_ENGINE_INDUCTION_BUILD_OK {expected}")
    audit = successful_log(output / "axioms.log", f"MOM_ENGINE_INDUCTION_AUDIT_OK {expected}")
    records = axiom_records(audit, set(inventory["declarations"]))
    record = dict(before, status="conditional-induction-passed", axioms=records,
                  conditional_target_axioms={name: records[name] for name in CONDITIONAL_TARGETS},
                  allowed_axioms=sorted(ALLOWED), build_log_sha256=digest(output / "build.log"),
                  axiom_log_sha256=digest(output / "axioms.log"))
    (output / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS conditional induction: {len(inventory['modules'])} modules and "
          f"{len(inventory['declarations'])} declarations at {expected}; "
          f"all axioms belong to {sorted(ALLOWED)}")
    for name in CONDITIONAL_TARGETS:
        print(name + ": " + json.dumps(records[name]))
    print("The STEP hypothesis remains a parameter; unconditional integration is separate.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("generate", "inventory", "preflight", "check"))
    parser.add_argument("--expected-sha")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.phase == "generate":
        generate()
        return
    if args.phase == "inventory":
        print(json.dumps({key: len(value) for key, value in source_inventory().items()}, indent=2))
        return
    require(args.expected_sha is not None and args.output is not None,
            "Verification requires --expected-sha and --output")
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT), "Place verification logs outside the repository")
    {"preflight": preflight, "check": check}[args.phase](args.expected_sha, output)


if __name__ == "__main__":
    main()
