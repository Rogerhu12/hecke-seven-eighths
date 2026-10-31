#!/usr/bin/env python3
"""Validate the exact-head native build and recursive axiom audit for this task.

The workflow runs Lake and Lean explicitly with pipefail before invoking `check`.
All generated records live in the caller's output directory (RUNNER_TEMP in CI).
The existing skeleton adapter is a separate integration boundary: it imports
admitted upstream definitions and is not included in the clean proof target.
The optional foundation seed preserves immutable native outputs and their
original Lake traces; it never substitutes for the current-head proof gates.
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
import tarfile
import tempfile
import tomllib
from pathlib import Path, PurePosixPath

TASK = Path(__file__).resolve().parent
ROOT = TASK.parents[2]
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION"
MODULES = (
    "Order", "Recursion", "IntegralRecursion", "Reduction", "Family", "Terminal", "ExceptionalCounting",
    "TerminalCertificate", "Interface", "Centering", "Induction", "ChildStepCompatibility",
)
EXCLUDED = {"SkeletonFamily.lean"}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
COMPILER_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
# Immutable, genuine native Lake output from the same repository. These are
# only a build-cache seed: every restored module still goes through Lake's
# ordinary source/dependency trace checks before either proof gate can pass.
FOUNDATION_RUN = 41126752041
FOUNDATION_HEAD = "984b0de3ddf8bd9ea8051e0325765532c7c6550f"
FOUNDATION_FINGERPRINT = "6707201d5789aca4222679e9dbf24b924367c460eda132ec71296300fcfb8a40"
FOUNDATION_SCHEMA = 1
FOUNDATION_BUILDS = (Path(".lake/build"), Path("vendor/class-field-theory/.lake/build"))
FOUNDATION_CONFIGS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml",
                      "vendor/class-field-theory/lakefile.toml")
# artifact ID, name, immutable outer ZIP SHA256, inner tar SHA256
FOUNDATION_ARTIFACTS = (
    (13012376359, "prime-foundation-40-0", "6c48a54613d0064719d04bf4d4ad6d0491b39b98251bc3808961c0c6afde1324", "eeaae4ba35ea0b43578e132afdd904caef3fb7010baa8a3ad963b7e96bcb768e"),
    (13011719707, "prime-foundation-40-1", "7620df2fdd8bc50d9ae6f43bd14d18732a2fd2cd9c52de010b99e59701975f82", "4efd5cfae24809b98675993cd5544dfe6caf7d0ffb8d823f22a64f79c8102a8d"),
    (13011754956, "prime-foundation-40-2", "b01697611b3584fa210abd61876a3ccb1e6122a3c217fe55e1a283300aebaf88", "6d65e704af89126677dfe1dc1142f0e47fdb1f6f07ab7fea3ae5f632d4058c7a"),
    (13013018508, "prime-foundation-40-3", "29fb1b025d9226a3d8bebb4849443770b04d90c0a4efeb6a406c6cf0c2d9968b", "30d2e905cb617a50757b884176ecac1f4adc920cc25141efd104964b4318fa64"),
    (13017749400, "prime-foundation-100-0", "384365645f5c02dacf5f8d05bfa4eb6211a2ab5ca9afddcefb39df51b63750be", "0fb746e74ef721d8167905d35361d87ffee0a563bf807405ed729c8a1dec6d43"),
    (13018611868, "prime-foundation-100-1", "57dfd63d075039e0c150635df09c534bfdf8060b88f8602457b2c271f8079fc1", "1b4ac7498c77c8f84f05390429c1b20539f32585ab5b1350e0a7c5b4f7c9f780"),
    (13018074066, "prime-foundation-100-2", "aa98e4d6970f2350fcd65f8be16fd66fbf069799813a40f682524b7c9e3d82c0", "f422c5449fc4ee1732a86ce815954f5161816d11cda1c87bce2e540693a7d27b"),
    (13015618946, "prime-foundation-100-3", "9ad599dfa01ff6e197493379480f2d7a62228e783a183e00e3f28841f7cb2f6d", "d53889d14a536536028254ecbeb445f193e6afd41eff716f4cedcd3edfe9b1cc"),
    (13021712535, "prime-foundation-180-0", "5e5137138741b9932002167dd64de9f71e6ee336de1ad47fe14ead193400d18b", "60234f15f055d6dabff28edb8b10069a2f4bf9fc8ab5d0aac864905efaf51bbf"),
    (13021514563, "prime-foundation-180-1", "14bb73f02e0f2631ca4bf4595cda97f0f90e615ab52cf71b340923fb37036e0f", "263454fb7a76f21cc7b333d6e82a31f37875c70330afb8468a5444bbb391abcd"),
    (13021895900, "prime-foundation-180-2", "80467b2b0110ab6ff10a862ebbfa2742587c00fe0738140b1da54824e096510e", "c8b2152ce1a47dcae03984d53fcc96ec45f16bc9e9ed5e5d9d38f2373684b3e9"),
    (13022623396, "prime-foundation-180-3", "bf58ea2a7645a5ac1c10095f03b8bda3a7ed5b4380d7516412e26c160f79f423", "85cc022948406ffd11dc2fcbd5fd03bc8dd127ca07864b75e2ffca90ec1492b4"),
)
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


def foundation_imports(text: str) -> list[str]:
    """Read only the Lean import header, including nested comments."""
    imports, depth = [], 0
    for raw in text.splitlines():
        code, index = [], 0
        while index < len(raw):
            if raw.startswith("/-", index):
                depth += 1
                code.append(" ")
                index += 2
            elif depth and raw.startswith("-/", index):
                depth -= 1
                index += 2
            elif depth:
                index += 1
            elif raw.startswith("--", index):
                break
            else:
                code.append(raw[index])
                index += 1
        line = "".join(code).strip()
        if not line or line in {"prelude", "module"}:
            continue
        match = re.fullmatch(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)", line)
        if not match:
            break
        names = match[1].split()
        require(all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", name)
                    for name in names), f"Unsupported import header: {line}")
        imports.extend(names)
    return list(dict.fromkeys(imports))


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def foundation_graph() -> tuple[dict, str]:
    """Current original Moments dependency closure, not a replacement target."""
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    roots = [(ROOT, FOUNDATION_BUILDS[0])]
    prefixes = set()
    for library in config.get("lean_lib", []):
        roots.append((ROOT / library.get("srcDir", "."), FOUNDATION_BUILDS[0]))
        prefixes.update(name.split(".")[0] for name in library.get("roots", [library["name"]]))
    vendor = ROOT / "vendor/class-field-theory"
    roots.append((vendor / "Lean4", FOUNDATION_BUILDS[1]))
    for library in tomllib.loads((vendor / "lakefile.toml").read_text()).get("lean_lib", []):
        prefixes.add(library["name"].split(".")[0])
    roots = list(dict.fromkeys(roots))
    nodes, external, visiting = {}, set(), set()

    def visit(name: str) -> None:
        if name in nodes or name in external:
            return
        relative = Path(*name.split(".")).with_suffix(".lean")
        found = next(((root / relative, build) for root, build in roots
                      if (root / relative).is_file()), None)
        if found is None:
            require(name.split(".")[0] not in prefixes, f"Missing project source: {name}")
            external.add(name)
            return
        require(name not in visiting, f"Import cycle at {name}")
        visiting.add(name)
        path, build = found
        raw = path.read_bytes()
        dependencies = foundation_imports(raw.decode("utf-8-sig"))
        for dependency in dependencies:
            visit(dependency)
        nodes[name] = dict(source=str(path.relative_to(ROOT)), build=str(build),
                           source_sha256=hashlib.sha256(raw).hexdigest(), source_blob=git_blob(raw),
                           dependencies=[dep for dep in dependencies if dep in nodes])
        visiting.remove(name)

    visit("HeckeSkeleton.Moments")
    fingerprint = hashlib.sha256(json.dumps(dict(
        modules={name: node["source_sha256"] for name, node in nodes.items()},
        config={name: digest(ROOT / name) for name in FOUNDATION_CONFIGS}),
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return nodes, fingerprint


def foundation_plan(expected: str, output: Path) -> None:
    verify_checkout(expected)
    nodes, fingerprint = foundation_graph()
    output.mkdir(parents=True, exist_ok=True)
    marker = ROOT / FOUNDATION_BUILDS[0] / "mom-engine-induction-foundation.json"
    try:
        cached = json.loads(marker.read_text()) if marker.is_file() else {}
    except json.JSONDecodeError:
        cached = {}  # An interrupted cache receipt is a cache miss, not evidence.
    if not isinstance(cached, dict):
        cached = {}
    pins = [list(pin) for pin in FOUNDATION_ARTIFACTS]
    reusable = (cached.get("schema") == FOUNDATION_SCHEMA
                and cached.get("status") == "restored-cache-only"
                and cached.get("producer_head") == FOUNDATION_HEAD
                and cached.get("source_fingerprint") == fingerprint
                and cached.get("artifact_pins") == pins
                and all(foundation_destination(record["path"]).is_file()
                        and foundation_destination(record["path"]).stat().st_size == record["bytes"]
                        and digest(foundation_destination(record["path"])) == record["sha256"]
                        for record in cached.get("files", []))
                and bool(cached.get("files")))
    available = True
    availability = dict(mode="verified-cache-reuse")
    if not reusable:
        try:
            metadata = json.loads(command("gh", "api",
                f"repos/Rogerhu12/hecke-seven-eighths/actions/runs/{FOUNDATION_RUN}/artifacts?per_page=100"))
        except subprocess.CalledProcessError as error:
            available = False
            availability = dict(mode="source-build-only", metadata_exit_code=error.returncode)
        else:
            artifacts = {entry["id"]: entry for entry in metadata["artifacts"]}
            unavailable = []
            for artifact_id, name, outer, _ in FOUNDATION_ARTIFACTS:
                entry = artifacts.get(artifact_id)
                if entry is None or entry.get("expired"):
                    unavailable.append(artifact_id)
                    continue
                require(entry.get("name") == name and entry.get("digest") == "sha256:" + outer
                        and entry.get("workflow_run", {}).get("id") == FOUNDATION_RUN
                        and entry.get("workflow_run", {}).get("head_sha") == FOUNDATION_HEAD,
                        f"Unexpected immutable foundation artifact metadata: {artifact_id}")
            available = not unavailable
            availability = dict(mode="pinned-native-artifacts" if available else "source-build-only",
                                missing_or_expired_artifacts=unavailable)
    restore_needed = not reusable and available
    plan = dict(head_sha=expected, source_fingerprint=fingerprint, project_modules=len(nodes),
                restore_needed=restore_needed, producer_run=FOUNDATION_RUN,
                producer_head=FOUNDATION_HEAD, artifact_pins=pins, availability=availability)
    (output / "foundation-plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    if reusable:
        (output / "foundation-restore.json").write_text(json.dumps(
            dict(cached, reused_for_head=expected), indent=2) + "\n")
    github_output = os.environ.get("GITHUB_OUTPUT")
    if github_output:
        with open(github_output, "a") as stream:
            stream.write(f"restore_needed={str(restore_needed).lower()}\n")
    print(f"Foundation cache seed needed: {restore_needed}; {len(nodes)} current source modules")
    print("Cache selection: " + json.dumps(availability, sort_keys=True))
    if not reusable and not available:
        print("No foundation bytes will be restored; the complete standard source build is required.")
    print("This cache decision does not replace any Lake build or axiom check.")


def foundation_destination(name: str) -> Path:
    relative = PurePosixPath(name)
    require(not relative.is_absolute() and ".." not in relative.parts and "\\" not in name,
            f"Unsafe foundation path: {name}")
    require(any(relative.parts[:len(root.parts)] == root.parts
                and len(relative.parts) > len(root.parts) for root in FOUNDATION_BUILDS),
            f"Foundation member is outside native project build directories: {name}")
    path = ROOT
    for part in relative.parts:
        path /= part
        require(not path.is_symlink(), f"Refusing to restore through a symlink: {path}")
    return path


def foundation_restore(expected: str, output: Path, downloads: Path) -> None:
    verify_checkout(expected)
    require(not downloads.is_relative_to(ROOT), "Keep downloaded foundation archives outside the repository")
    nodes, fingerprint = foundation_graph()
    plan = json.loads((output / "foundation-plan.json").read_text())
    require(plan["head_sha"] == expected and plan["source_fingerprint"] == fingerprint,
            "Sources changed since foundation cache planning")
    require(plan["restore_needed"], "Foundation restoration was not requested by the plan")
    # Fetch an immutable source commit for per-file comparisons. No checkout,
    # tracked-file mutation, trace construction, or compiler modification occurs.
    subprocess.run(["git", "fetch", "--no-tags", "--depth=1", "origin", FOUNDATION_HEAD],
                   cwd=ROOT, check=True)
    require(command("git", "rev-parse", FOUNDATION_HEAD + "^{commit}") == FOUNDATION_HEAD,
            "Unexpected foundation source commit")
    tree = {}
    listing = subprocess.check_output(["git", "ls-tree", "-rz", FOUNDATION_HEAD], cwd=ROOT)
    for entry in listing.split(b"\0"):
        if entry:
            header, path = entry.split(b"\t", 1)
            mode, kind, blob = header.decode().split()
            if kind == "blob" and mode in {"100644", "100755"}:
                tree[path.decode()] = blob
    for name in FOUNDATION_CONFIGS:
        require(tree.get(name) == git_blob((ROOT / name).read_bytes()),
                f"Foundation configuration differs: {name}")
    matched = {}
    for name, node in nodes.items():  # dependencies precede their consumers
        matched[name] = (tree.get(node["source"]) == node["source_blob"]
                         and all(matched[dep] for dep in node["dependencies"]))
    # The fixed payload hash below is checked locally. The API also binds each
    # outer ZIP digest to the immutable producer run and source head.
    metadata = json.loads(command("gh", "api",
        f"repos/Rogerhu12/hecke-seven-eighths/actions/runs/{FOUNDATION_RUN}/artifacts?per_page=100"))
    artifacts = {entry["id"]: entry for entry in metadata["artifacts"]}
    for artifact_id, name, outer, _ in FOUNDATION_ARTIFACTS:
        entry = artifacts.get(artifact_id, {})
        require(entry.get("name") == name and entry.get("digest") == "sha256:" + outer
                and not entry.get("expired")
                and entry.get("workflow_run", {}).get("id") == FOUNDATION_RUN
                and entry.get("workflow_run", {}).get("head_sha") == FOUNDATION_HEAD,
                f"Unexpected immutable foundation artifact metadata: {artifact_id}")
    restored, files, seen, manifests = {}, [], set(), []
    allowed_extensions = {".olean", ".olean.server", ".olean.private", ".ilean", ".c",
                          ".ir", ".ir.sig", ".bc", ".ltar", ".trace"}
    allowed_extensions |= {extension + ".hash" for extension in allowed_extensions}
    for artifact_id, name, outer, inner in FOUNDATION_ARTIFACTS:
        stem = name.removeprefix("prime-")
        candidates = list(downloads.rglob(stem + ".tar.gz"))
        require(len(candidates) == 1, f"Missing or duplicate foundation archive: {name}")
        archive = candidates[0]
        manifest = json.loads(archive.with_name(stem + ".manifest.json").read_text())
        require(manifest.get("format") == 1
                and manifest.get("fingerprint") == FOUNDATION_FINGERPRINT
                and manifest.get("archive_sha256") == inner and digest(archive) == inner,
                f"Foundation archive identity/hash mismatch: {name}")
        manifests.append(dict(artifact_id=artifact_id, name=name, outer_sha256=outer, **manifest))
        grouped, raw_traces, member_count = {}, {}, 0
        # Two sequential passes avoid repeatedly seeking through multi-GB
        # compressed setup files. The first validates; the second copies only
        # the original native outputs of source-matched modules.
        with tarfile.open(archive, "r|gz") as bundle:
            for member in bundle:
                member_count += 1
                destination = foundation_destination(member.name)
                require(member.isfile() and member.name not in seen,
                        f"Non-regular or duplicate foundation member: {member.name}")
                seen.add(member.name)
                relative = destination.relative_to(ROOT)
                for build in FOUNDATION_BUILDS:
                    for area in ("lib/lean", "ir"):
                        prefix = build / area
                        if relative.is_relative_to(prefix):
                            suffix = relative.relative_to(prefix)
                            leaf, dot, extension = suffix.name.partition(".")
                            module = ".".join((*suffix.parts[:-1], leaf))
                            node = nodes.get(module)
                            if node and matched[module] and node["build"] == str(build):
                                # setup.json is regenerated only on a real compile;
                                # it is not a Lake output or required replay input.
                                # Keep every native output and its original hash/trace.
                                if dot and "." + extension in allowed_extensions:
                                    grouped.setdefault(module, []).append(member)
                                    if extension == "trace":
                                        raw_traces[module] = bundle.extractfile(member).read()
        require(member_count == manifest["file_count"], f"Foundation file count mismatch: {name}")
        selected = set()
        for module, outputs in grouped.items():
            node = nodes[module]
            trace_path = str(Path(node["build"]) / "lib/lean" /
                             Path(*module.split(".")).with_suffix(".trace"))
            traces = [member for member in outputs if member.name == trace_path]
            require(len(traces) == 1, f"Missing original Lake trace for {module}")
            raw_trace = raw_traces[module]
            trace = json.loads(raw_trace)
            source_path = "/home/runner/work/hecke-seven-eighths/hecke-seven-eighths/" + node["source"]
            input_names = {entry[0] for entry in trace.get("inputs", [])}
            require(trace.get("synthetic") is False
                    and trace.get("schemaVersion") == "2025-09-10"
                    and source_path in input_names
                    and f"Lean 4.35.0, commit {COMPILER_COMMIT}" in input_names
                    and all(entry.get("level") != "error" for entry in trace.get("log", [])),
                    f"Missing real source/compiler provenance in Lake trace: {module}")
            relative = Path(*module.split("."))
            required = {str(Path(node["build"]) / directory / relative.with_suffix(extension))
                        for directory, extension in (("lib/lean", ".olean"),
                                                     ("lib/lean", ".ilean"), ("ir", ".c"))}
            if trace.get("outputs", {}).get("m"):
                required |= {str(Path(node["build"]) / "lib/lean" /
                                 relative.with_suffix(extension))
                             for extension in (".olean.server", ".olean.private", ".ir", ".ir.sig")}
            require(required <= {member.name for member in outputs},
                    f"Incomplete original native outputs for {module}")
            require(module not in restored, f"Duplicate foundation module ownership: {module}")
            restored[module] = dict(source=node["source"], source_sha256=node["source_sha256"],
                                    source_blob=node["source_blob"], artifact_id=artifact_id,
                                    trace_sha256=hashlib.sha256(raw_trace).hexdigest())
            selected.update(member.name for member in outputs)
        with tarfile.open(archive, "r|gz") as bundle:
            for member in bundle:
                if member.name in selected:
                    destination = foundation_destination(member.name)
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    with bundle.extractfile(member) as source:
                        with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as target:
                            temporary = Path(target.name)
                            try:
                                shutil.copyfileobj(source, target)
                                target.flush()
                                os.chmod(temporary, member.mode & 0o777)
                                os.utime(temporary, (member.mtime, member.mtime))
                                sha = digest(temporary)
                                os.replace(temporary, destination)
                            finally:
                                temporary.unlink(missing_ok=True)
                    files.append(dict(path=member.name, sha256=sha, bytes=member.size,
                                      artifact_id=artifact_id))
        print(f"Restored original native outputs from {name}; cumulative modules={len(restored)}", flush=True)
        # Only the downloaded compressed input is removed; the evidence keeps
        # its immutable ID/digest, per-source identity, and all output hashes.
        archive.unlink()
    verify_checkout(expected)
    _, after = foundation_graph()
    require(after == fingerprint, "Sources changed during foundation restoration")
    record = dict(schema=FOUNDATION_SCHEMA, status="restored-cache-only", head_sha=expected,
                  producer_run=FOUNDATION_RUN, producer_head=FOUNDATION_HEAD,
                  producer_fingerprint=FOUNDATION_FINGERPRINT, source_fingerprint=fingerprint,
                  artifact_pins=[list(pin) for pin in FOUNDATION_ARTIFACTS], manifests=manifests,
                  project_modules=len(nodes), source_and_dependency_matches=sum(matched.values()),
                  restored_modules=restored, files=files,
                  remaining_for_standard_lake_build=sorted(set(nodes) - restored.keys()),
                  source_or_dependency_mismatches=sorted(name for name in nodes if not matched[name]))
    serialized = json.dumps(record, indent=2) + "\n"
    (output / "foundation-restore.json").write_text(serialized)
    (ROOT / FOUNDATION_BUILDS[0] / "mom-engine-induction-foundation.json").write_text(serialized)
    print(f"Native cache restored: {len(restored)}/{len(nodes)} project modules, {len(files)} files.")
    print("No trace was rewritten. The normal Lake build and both axiom audits still must succeed.")


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
              "skeleton-preflight": skeleton_preflight, "skeleton-check": skeleton_check,
              "foundation-plan": foundation_plan}
    parser.add_argument("phase", choices=(*phases, "foundation-restore"))
    parser.add_argument("--expected-sha", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--downloads", type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT), "Place verification logs outside the repository")
    if args.phase == "foundation-restore":
        require(args.downloads is not None, "foundation-restore needs --downloads")
        foundation_restore(args.expected_sha, output, args.downloads.resolve())
    else:
        require(args.downloads is None, "--downloads is only for foundation-restore")
        phases[args.phase](args.expected_sha, output)


if __name__ == "__main__":
    main()
