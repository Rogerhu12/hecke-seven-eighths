#!/usr/bin/env python3
"""Compile MOM_BASE from real sources and check its recursive axiom allowlist.

Run after `lake exe cache get` in the pinned repository. The compiler, import
search path, and package options come from this checkout's Lake environment.
Project objects are built from their real sources. A previous successful
object may be reused only when its source, options, complete project import
closure, pinned external environment and object hashes still match. The
recursive axiom audit itself is always recompiled.
"""
from __future__ import annotations

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / "mom-base-verification"
OUT = ROOT / ".lake/build/lib/lean"
STATE = ROOT / ".lake/build/mom-base-state.json"
TASK_DIR = ROOT / "HeckeSkeleton/Moments/MOM_BASE"
AUDIT = TASK_DIR / "Audit.lean"
TARGETS = sys.argv[1:] or [".".join(p.relative_to(ROOT).with_suffix("").parts)
                        for p in sorted(TASK_DIR.glob("*.lean"))]
if not TARGETS:
    raise SystemExit("No MOM_BASE source modules found")
EXPECTED_LEAN = "4.35.0-rc3"
EXPECTED_LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
EXPECTED_MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
LOGS.mkdir(exist_ok=True)
OUT.mkdir(parents=True, exist_ok=True)


def checked(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


lean = checked("lake", "env", "which", "lean")
version = checked(lean, "--version")
if EXPECTED_LEAN not in version or EXPECTED_LEAN_COMMIT not in version:
    raise SystemExit(f"Unexpected Lean version: {version}")
manifest_bytes = (ROOT / "lake-manifest.json").read_bytes()
manifest = json.loads(manifest_bytes)
mathlib_entry = next(p for p in manifest["packages"] if p["name"] == "mathlib")
if mathlib_entry["rev"] != EXPECTED_MATHLIB:
    raise SystemExit("Unexpected Mathlib revision")
actual_mathlib = checked("git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
if actual_mathlib != EXPECTED_MATHLIB:
    raise SystemExit(f"Unexpected checked-out Mathlib revision: {actual_mathlib}")
env = os.environ.copy()
env["LEAN_PATH"] = checked("lake", "env", "printenv", "LEAN_PATH")
paths = [(ROOT / p).resolve() for p in env["LEAN_PATH"].split(os.pathsep)]
env["LEAN_PATH"] = os.pathsep.join(map(str, [OUT] + [p for p in paths if p != OUT]))
sysroot = Path(lean).resolve().parent.parent
paths.append(sysroot / "lib/lean")
external_paths = [path for path in paths if path != OUT]
config = tomllib.loads((ROOT / "lakefile.toml").read_text())


def library_definitions(package: Path, package_config: dict) -> list[dict]:
    libraries = []
    for lib in package_config.get("lean_lib", []):
        roots = lib.get("roots", [lib["name"]])
        prefixes = list(roots) + [g.removesuffix(".+").removesuffix(".*")
                                 for g in lib.get("globs", [])]
        libraries.append({
            "root": package / lib.get("srcDir", package_config.get("srcDir", ".")),
            "prefixes": prefixes,
            "options": {**package_config.get("leanOptions", {}), **lib.get("leanOptions", {})},
        })
    return libraries


source_libraries = []
for package in (ROOT, ROOT / "vendor/class-field-theory"):
    package_config = tomllib.loads((package / "lakefile.toml").read_text())
    source_libraries.extend(library_definitions(package, package_config))


def find_source(module: str, libraries=None, exists=None):
    libraries = source_libraries if libraries is None else libraries
    exists = Path.is_file if exists is None else exists
    candidates = []
    for library in libraries:
        lengths = [len(p) for p in library["prefixes"]
                   if module == p or module.startswith(p + ".")]
        path = library["root"] / module_path(module, ".lean")
        if lengths and exists(path):
            candidates.append((max(lengths), path, library["root"], library["options"]))
    candidates.sort(key=lambda row: row[0], reverse=True)
    return candidates[0][1:] if candidates else None


def module_path(module: str, suffix: str) -> Path:
    return Path(*module.split(".")).with_suffix(suffix)


def option_flags(options: dict, prefix: str = "") -> list[str]:
    result = []
    for key, value in options.items():
        name = f"{prefix}.{key}" if prefix else key
        if isinstance(value, dict):
            result.extend(option_flags(value, name))
        else:
            text = str(value).lower() if isinstance(value, bool) else str(value)
            result.append(f"-D{name}={text}")
    return result


def imports(text: str) -> list[str]:
    """Read the Lean import header, excluding nested documentation comments."""
    output, index, depth = [], 0, 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == "/-":
            depth += 1
            output.extend("  ")
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            output.extend("  ")
            index += 2
        elif depth:
            output.append("\n" if text[index] == "\n" else " ")
            index += 1
        elif pair == "--":
            newline = text.find("\n", index)
            if newline < 0:
                break
            output.append("\n")
            index = newline + 1
        else:
            output.append(text[index])
            index += 1
    result = []
    for line in "".join(output).splitlines():
        line = line.strip()
        if not line or line in {"module", "prelude"}:
            continue
        match = re.fullmatch(
            r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+(?:\s+[\w.]+)*)", line)
        if not match:
            break
        result.extend(match.group(1).split())
    return result


nodes, order, seen, active = {}, [], set(), set()
external_environment = hashlib.sha256(version.encode() + manifest_bytes).hexdigest()
fingerprints = {}


def discover(module: str) -> None:
    if module in seen:
        return
    if module in active:
        raise RuntimeError(f"Import cycle: {module}")
    source = find_source(module)
    if source is None:
        if not any((root / module_path(module, ".olean")).is_file() for root in external_paths):
            raise RuntimeError(f"Missing cached external module: {module}; run lake exe cache get")
        fingerprints[module] = hashlib.sha256(
            f"{external_environment}:{module}".encode()).hexdigest()
        seen.add(module)
        return
    path, root, options = source
    raw = path.read_bytes()
    deps = imports(raw.decode())
    active.add(module)
    for dep in deps:
        discover(dep)
    active.remove(module)
    seen.add(module)
    nodes[module] = {
        "path": path, "root": root, "options": options, "deps": deps,
        "source_sha256": hashlib.sha256(raw).hexdigest(),
    }
    fingerprints[module] = hashlib.sha256(json.dumps({
        "verifier_format": 1,
        "environment": external_environment,
        "source": nodes[module]["source_sha256"],
        "source_path": str(path.relative_to(ROOT)),
        "options": option_flags(options),
        "imports": [(dep, fingerprints[dep]) for dep in deps],
    }, sort_keys=True).encode()).hexdigest()
    order.append(module)


for path in TASK_DIR.glob("*.lean"):
    text = path.read_text()
    # The source scanner is supplemental; recursive #print axioms is the gate.
    without_comments = re.sub(r"/-.*?-/|--[^\n]*", " ", text, flags=re.S)
    forbidden = re.findall(r"\b(?:sorry|axiom|native_decide)\b", without_comments)
    if forbidden:
        raise RuntimeError(f"Forbidden proof token in {path.relative_to(ROOT)}: {forbidden}")
for target in TARGETS:
    discover(target)
(LOGS / "environment.json").write_text(json.dumps({
    "lean": version, "mathlib": actual_mathlib,
    "git_head": checked("git", "rev-parse", "HEAD"), "targets": TARGETS,
    "dependency_order": order,
}, indent=2) + "\n")
try:
    state = json.loads(STATE.read_text())
except (FileNotFoundError, json.JSONDecodeError):
    state = {}


def artifact_hashes(output: Path) -> dict[str, str]:
    # Include every emitted companion, especially .olean.private and .ir.sig.
    artifacts = list(output.parent.glob(output.stem + ".*"))
    return {str(path.relative_to(OUT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in artifacts if path.is_file()}


def reusable(module: str, output: Path) -> bool:
    old = state.get(module, {})
    if module.startswith("HeckeSkeleton.Moments.MOM_BASE.") or old.get("fingerprint") != fingerprints[module]:
        return False
    return (old.get("exit_code") == 0 and output.is_file()
            and bool(old.get("artifacts"))
            and artifact_hashes(output) == old["artifacts"])


print(f"Verifying {len(order)} actual project modules", flush=True)
results = []
failed = set()
errors = []
finished = set()
workers = 1  # One compiler at a time keeps large import closures within runner memory.
positions = {module: index for index, module in enumerate(order, 1)}


def compile_module(module: str) -> tuple[dict, str, Path]:
    node = nodes[module]
    output = OUT / module_path(module, ".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    flags = option_flags(node["options"])
    # Never write through a cached output symlink.
    for previous in output.parent.glob(output.stem + ".*"):
        if previous.is_symlink():
            previous.unlink()
    command = [lean, "-j1", *flags, "-R", str(node["root"]), "-o", str(output), str(node["path"])]
    started = time.monotonic()
    result = subprocess.run(command, cwd=node["root"], env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    unchanged = hashlib.sha256(node["path"].read_bytes()).hexdigest() == node["source_sha256"]
    record = {
        "module": module, "source": str(node["path"].relative_to(ROOT)),
        "source_sha256": node["source_sha256"], "source_unchanged": unchanged,
        "exit_code": result.returncode, "seconds": round(time.monotonic() - started, 3),
        "command": command,
        "fingerprint": fingerprints[module], "reused": False,
    }
    return record, result.stdout, output


def write_json_atomic(path: Path, value: object) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def save_results() -> None:
    write_json_atomic(LOGS / "results.json", results)


BASELINE_COMMIT = "5e4c85f172c101fd0c201219c13aa28f8b520d42"
BASELINE_FINGERPRINT = "6707201d5789aca4222679e9dbf24b924367c460eda132ec71296300fcfb8a40"
BASELINE_RUN = 41126752041
BASELINE_ARTIFACTS = [
    (13018074066, "prime-foundation-100-2", "aa98e4d6970f2350fcd65f8be16fd66fbf069799813a40f682524b7c9e3d82c0", "f422c5449fc4ee1732a86ce815954f5161816d11cda1c87bce2e540693a7d27b"),
    (13018611868, "prime-foundation-100-1", "57dfd63d075039e0c150635df09c534bfdf8060b88f8602457b2c271f8079fc1", "1b4ac7498c77c8f84f05390429c1b20539f32585ab5b1350e0a7c5b4f7c9f780"),
    (13015618946, "prime-foundation-100-3", "9ad599dfa01ff6e197493379480f2d7a62228e783a183e00e3f28841f7cb2f6d", "d53889d14a536536028254ecbeb445f193e6afd41eff716f4cedcd3edfe9b1cc"),
    (13021514563, "prime-foundation-180-1", "14bb73f02e0f2631ca4bf4595cda97f0f90e615ab52cf71b340923fb37036e0f", "263454fb7a76f21cc7b333d6e82a31f37875c70330afb8468a5444bbb391abcd"),
    (13013018508, "prime-foundation-40-3", "29fb1b025d9226a3d8bebb4849443770b04d90c0a4efeb6a406c6cf0c2d9968b", "30d2e905cb617a50757b884176ecac1f4adc920cc25141efd104964b4318fa64"),
    (13022623396, "prime-foundation-180-3", "bf58ea2a7645a5ac1c10095f03b8bda3a7ed5b4380d7516412e26c160f79f423", "85cc022948406ffd11dc2fcbd5fd03bc8dd127ca07864b75e2ffca90ec1492b4"),
    (13017749400, "prime-foundation-100-0", "384365645f5c02dacf5f8d05bfa4eb6211a2ab5ca9afddcefb39df51b63750be", "0fb746e74ef721d8167905d35361d87ffee0a563bf807405ed729c8a1dec6d43"),
    (13011754956, "prime-foundation-40-2", "b01697611b3584fa210abd61876a3ccb1e6122a3c217fe55e1a283300aebaf88", "6d65e704af89126677dfe1dc1142f0e47fdb1f6f07ab7fea3ae5f632d4058c7a"),
    (13021895900, "prime-foundation-180-2", "80467b2b0110ab6ff10a862ebbfa2742587c00fe0738140b1da54824e096510e", "c8b2152ce1a47dcae03984d53fcc96ec45f16bc9e9ed5e5d9d38f2373684b3e9"),
    (13011719707, "prime-foundation-40-1", "7620df2fdd8bc50d9ae6f43bd14d18732a2fd2cd9c52de010b99e59701975f82", "4efd5cfae24809b98675993cd5544dfe6caf7d0ffb8d823f22a64f79c8102a8d"),
    (13012376359, "prime-foundation-40-0", "6c48a54613d0064719d04bf4d4ad6d0491b39b98251bc3808961c0c6afde1324", "eeaae4ba35ea0b43578e132afdd904caef3fb7010baa8a3ad963b7e96bcb768e"),
    (13021712535, "prime-foundation-180-0", "5e5137138741b9932002167dd64de9f71e6ee336de1ad47fe14ead193400d18b", "60234f15f055d6dabff28edb8b10069a2f4bf9fc8ab5d0aac864905efaf51bbf"),
]
LOAD_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")


def baseline_graph(raw_files: dict[str, bytes]) -> tuple[dict, dict]:
    """Recompute the original successful CI source/configuration fingerprint."""
    original = tomllib.loads(raw_files["lakefile.toml"].decode())
    baseline_libraries = library_definitions(ROOT, original)
    baseline_libraries.extend(library_definitions(ROOT / "vendor/class-field-theory",
        tomllib.loads(raw_files["vendor/class-field-theory/lakefile.toml"].decode())))
    roots = ["."] + [lib.get("srcDir", ".") for lib in original["lean_lib"]]
    roots = list(dict.fromkeys(roots + ["vendor/class-field-theory/Lean4"]))
    baseline_nodes, visiting = {}, set()

    def visit(module):
        if module in baseline_nodes:
            return
        path = next((str(Path(root) / module_path(module, ".lean")) for root in roots
                     if str(Path(root) / module_path(module, ".lean")) in raw_files), None)
        if path is None:
            return
        if module in visiting:
            raise RuntimeError("Cycle in pinned CI baseline")
        visiting.add(module)
        raw = raw_files[path]
        deps = imports(raw.decode("utf-8-sig"))
        for dep in deps:
            visit(dep)
        build = ("vendor/class-field-theory/.lake/build/lib/lean"
                 if path.startswith("vendor/class-field-theory/Lean4/")
                 else ".lake/build/lib/lean")
        baseline_nodes[module] = {
            "source": path, "sha256": hashlib.sha256(raw).hexdigest(),
            "deps": [d for d in deps if d in baseline_nodes], "build": build,
        }
        resolved = find_source(module, baseline_libraries,
            lambda candidate: str(candidate.relative_to(ROOT)) in raw_files)
        if resolved is not None and str(resolved[0].relative_to(ROOT)) == path:
            baseline_nodes[module]["source_root"] = str(resolved[1].relative_to(ROOT))
            baseline_nodes[module]["options"] = resolved[2]
        visiting.remove(module)

    visit("HeckeSkeleton.Moments")
    configuration = {path: hashlib.sha256(raw_files[path]).hexdigest() for path in
                     ["lean-toolchain", "lake-manifest.json", "lakefile.toml",
                      "vendor/class-field-theory/lakefile.toml"]}
    payload = {"modules": {name: row["sha256"] for name, row in baseline_nodes.items()},
               "config": configuration}
    fingerprint = hashlib.sha256(json.dumps(payload, sort_keys=True,
                                           separators=(",", ":")).encode()).hexdigest()
    if fingerprint != BASELINE_FINGERPRINT:
        raise RuntimeError("Pinned baseline source/configuration fingerprint mismatch")
    # These pins must remain byte-identical. Library declarations may acquire
    # unrelated roots as the PR base advances: each selected module's resolved
    # source root and effective compiler options are compared below instead.
    for path in ("lean-toolchain", "lake-manifest.json"):
        if (ROOT / path).read_bytes() != raw_files[path]:
            raise RuntimeError("Current configuration differs from CI baseline: " + path)
    return baseline_nodes, configuration


def bootstrap_original_ci() -> None:
    """Reuse immutable successful CI bundles only for unchanged source closures.

    This optional bootstrap does not certify a new MOM_BASE theorem. New task
    files and their axiom audit always run through the actual compiler below.
    """
    import tarfile
    import tempfile
    import urllib.error
    import urllib.parse
    import urllib.request
    import zipfile
    from pathlib import PurePosixPath

    token = os.environ.get("GH_TOKEN")
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    if not token or repo != "Rogerhu12/hecke-seven-eighths":
        print("CI bootstrap unavailable; compiling required dependencies from source.", flush=True)
        return
    needed = {m for m in order if not m.startswith("HeckeSkeleton.Moments.MOM_BASE.")
              and not reusable(m, OUT / module_path(m, ".olean"))}
    if not needed:
        return
    api = "https://api.github.com/repos/" + repo
    headers = {"Authorization": "Bearer " + token, "Accept": "application/vnd.github+json",
               "X-GitHub-Api-Version": "2022-11-28"}

    class NoRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self, request, response, code, message, hdrs, newurl):
            return None

    opener = urllib.request.build_opener(NoRedirect)

    def download(url, destination, limit):
        request = urllib.request.Request(url, headers=headers)
        try:
            response = opener.open(request, timeout=120)
        except urllib.error.HTTPError as error:
            if error.code not in (301, 302, 303, 307, 308):
                raise
            location = error.headers["Location"]
            parsed = urllib.parse.urlparse(location)
            if parsed.scheme != "https" or not parsed.hostname:
                raise RuntimeError("Invalid GitHub download redirect")
            # The temporary storage redirect receives no API authorization header.
            response = urllib.request.urlopen(location, timeout=120)
        count = 0
        with response, destination.open("wb") as handle:
            while chunk := response.read(1024 * 1024):
                count += len(chunk)
                if count > limit:
                    raise RuntimeError("GitHub download exceeds its expected size")
                handle.write(chunk)
        return count

    def sha_file(path):
        with path.open("rb") as handle:
            return hashlib.file_digest(handle, "sha256").hexdigest()

    with tempfile.TemporaryDirectory(prefix="mom-base-bootstrap-") as directory:
        temp = Path(directory)
        source_archive = temp / "baseline.tar.gz"
        download(api + "/tarball/" + BASELINE_COMMIT, source_archive, 150_000_000)
        raw_files = {}
        with tarfile.open(source_archive, "r:gz") as archive:
            for member in archive:
                parts = PurePosixPath(member.name).parts
                if len(parts) < 2 or ".." in parts or not member.isfile():
                    continue
                path = PurePosixPath(*parts[1:]).as_posix()
                if path.endswith(".lean") or path in {"lean-toolchain", "lake-manifest.json",
                    "lakefile.toml", "vendor/class-field-theory/lakefile.toml"}:
                    if path in raw_files:
                        raise RuntimeError("Duplicate baseline archive path")
                    raw_files[path] = archive.extractfile(member).read()
        baseline, configuration = baseline_graph(raw_files)
        eligible = {}
        for module in order:
            node, previous = nodes[module], baseline.get(module)
            eligible[module] = bool(previous and previous["source"] == str(node["path"].relative_to(ROOT))
                and previous["sha256"] == node["source_sha256"]
                and previous.get("source_root") == str(node["root"].relative_to(ROOT))
                and previous.get("options") == node["options"]
                and previous["deps"] == [d for d in node["deps"] if d in nodes]
                and all(eligible.get(dep, False) for dep in previous["deps"]))
        wanted = {m for m in needed if eligible.get(m, False)}
        if not wanted:
            return
        del raw_files
        source_archive.unlink()
        selected_paths = {}
        for module in wanted:
            stem = str(Path(baseline[module]["build"]) / Path(*module.split(".")))
            for suffix in LOAD_SUFFIXES:
                selected_paths[stem + suffix] = (module, suffix)
        evidence = {"baseline_commit": BASELINE_COMMIT, "fingerprint": BASELINE_FINGERPRINT,
                    "configuration": configuration, "eligible_modules": sorted(wanted),
                    "current_configuration": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                                              for path in configuration},
                    "configuration_policy": "exact external pins; per-module source root and effective options",
                    "artifacts": [], "restored_modules": []}
        write_json_atomic(LOGS / "bootstrap.json", evidence)
        for artifact_id, name, outer_hash, inner_hash in BASELINE_ARTIFACTS:
            request = urllib.request.Request(api + f"/actions/artifacts/{artifact_id}", headers=headers)
            with urllib.request.urlopen(request, timeout=60) as response:
                metadata = json.load(response)
            if (metadata.get("id") != artifact_id or metadata.get("name") != name
                or metadata.get("expired") or metadata.get("digest") != "sha256:" + outer_hash
                or (metadata.get("workflow_run") or {}).get("id") != BASELINE_RUN):
                raise RuntimeError(f"Pinned CI artifact metadata mismatch: {artifact_id}")
            zipped = temp / "artifact.zip"
            size = download(api + f"/actions/artifacts/{artifact_id}/zip", zipped,
                            metadata["size_in_bytes"])
            if size != metadata["size_in_bytes"] or sha_file(zipped) != outer_hash:
                raise RuntimeError(f"Pinned CI artifact digest mismatch: {artifact_id}")
            per_module = {}
            with zipfile.ZipFile(zipped) as outer:
                names = outer.namelist()
                manifests = [n for n in names if n.endswith(".manifest.json")]
                bundles = [n for n in names if n.endswith(".tar.gz")]
                if len(names) != 2 or len(manifests) != 1 or len(bundles) != 1:
                    raise RuntimeError("Unexpected CI artifact structure")
                manifest = json.loads(outer.read(manifests[0]))
                if (manifest.get("format") != 1 or manifest.get("fingerprint") != BASELINE_FINGERPRINT
                    or manifest.get("archive_sha256") != inner_hash):
                    raise RuntimeError("CI inner manifest mismatch")
                with outer.open(bundles[0]) as handle:
                    actual = hashlib.file_digest(handle, "sha256").hexdigest()
                if actual != inner_hash:
                    raise RuntimeError("CI inner archive digest mismatch")
                member_names = set()
                with outer.open(bundles[0]) as stream, tarfile.open(fileobj=stream, mode="r|gz") as archive:
                    for member in archive:
                        parts = PurePosixPath(member.name)
                        if parts.is_absolute() or ".." in parts.parts or not member.isfile() or member.name in member_names:
                            raise RuntimeError("Unsafe or duplicate CI archive member")
                        member_names.add(member.name)
                        if member.name not in selected_paths:
                            continue
                        module, suffix = selected_paths[member.name]
                        if module not in per_module:
                            old_stem = OUT / Path(*module.split("."))
                            for old in old_stem.parent.glob(old_stem.name + ".*"):
                                if old.is_file() or old.is_symlink():
                                    old.unlink()
                        destination = Path(str(OUT / Path(*module.split("."))) + suffix)
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        staged = destination.with_name(destination.name + ".bootstrap-tmp")
                        if staged.is_symlink():
                            staged.unlink()
                        with archive.extractfile(member) as source, staged.open("wb") as target:
                            digest = hashlib.sha256()
                            count = 0
                            while chunk := source.read(1024 * 1024):
                                digest.update(chunk)
                                count += len(chunk)
                                target.write(chunk)
                        if count != member.size:
                            raise RuntimeError("Truncated CI object")
                        staged.replace(destination)
                        per_module.setdefault(module, {})[str(destination.relative_to(OUT))] = digest.hexdigest()
                if len(member_names) != manifest.get("file_count"):
                    raise RuntimeError("CI archive file count mismatch")
            for module, hashes in per_module.items():
                output = OUT / module_path(module, ".olean")
                if str(output.relative_to(OUT)) not in hashes:
                    raise RuntimeError("Missing native CI object for " + module)
                # Check bytes again after extraction, including every companion.
                if artifact_hashes(output) != hashes:
                    raise RuntimeError("Native CI output bundle mismatch for " + module)
                state[module] = {"module": module, "source": baseline[module]["source"],
                    "source_sha256": nodes[module]["source_sha256"], "source_unchanged": True,
                    "fingerprint": fingerprints[module], "exit_code": 0, "artifacts": hashes,
                    "origin": {"kind": "verified_original_ci", "artifact_id": artifact_id,
                        "baseline_commit": BASELINE_COMMIT, "baseline_fingerprint": BASELINE_FINGERPRINT,
                        "outer_sha256": outer_hash, "inner_sha256": inner_hash,
                        "source_dependency_closure_unchanged": True}}
            write_json_atomic(STATE, state)
            evidence["artifacts"].append({"id": artifact_id, "name": name,
                                         "restored_modules": sorted(per_module)})
            evidence["restored_modules"].extend(sorted(per_module))
            write_json_atomic(LOGS / "bootstrap.json", evidence)
            zipped.unlink()
            print(f"BOOTSTRAP: artifact {artifact_id}, {len(per_module)} verified original modules", flush=True)


try:
    bootstrap_original_ci()
except Exception as bootstrap_error:
    # A transport miss affects speed only. Missing dependencies still compile
    # below; neither a failed bootstrap nor a partial restore is a proof pass.
    safe_message = str(bootstrap_error) if isinstance(bootstrap_error, RuntimeError) else type(bootstrap_error).__name__
    print(f"::warning::Original CI bootstrap unavailable ({safe_message}); "
          "remaining dependencies will compile from source.", flush=True)
    (LOGS / "bootstrap-error.txt").write_text(type(bootstrap_error).__name__ + ": " + safe_message + "\n")


print(f"At most {workers} single-threaded Lean processes", flush=True)
pending = list(order)
running = {}
with ThreadPoolExecutor(max_workers=workers) as executor:
    while pending or running:
        for module in list(pending):
            deps = nodes[module]["deps"]
            if any(dep in nodes and dep not in finished for dep in deps):
                continue
            index = positions[module]
            blocked = [dep for dep in deps if dep in failed]
            output = OUT / module_path(module, ".olean")
            if blocked:
                failed.add(module)
                finished.add(module)
                pending.remove(module)
                print(f"[{index}/{len(order)}] BLOCKED {module}: {', '.join(blocked)}", flush=True)
                results.append({"module": module, "blocked_by": blocked})
                save_results()
            elif reusable(module, output):
                finished.add(module)
                pending.remove(module)
                print(f"[{index}/{len(order)}] REUSED {module} (verified source/import/object hashes)", flush=True)
                results.append({**state[module], "module": module, "reused": True})
                save_results()
            elif len(running) < workers:
                pending.remove(module)
                print(f"[{index}/{len(order)}] BUILD {module}", flush=True)
                running[executor.submit(compile_module, module)] = module
        if not running:
            if pending:
                raise RuntimeError(f"Unresolved project dependencies: {pending}")
            break
        completed, _ = wait(running, return_when=FIRST_COMPLETED)
        for future in completed:
            module = running.pop(future)
            record, stdout, output = future.result()
            finished.add(module)
            if record["exit_code"] or not record["source_unchanged"]:
                state.pop(module, None)
                failed.add(module)
                errors.append(module)
            else:
                record["artifacts"] = artifact_hashes(output)
                state[module] = record
            write_json_atomic(STATE, state)
            results.append(record)
            (LOGS / (module + ".log")).write_text(json.dumps(record, indent=2) + "\n\n" + stdout)
            save_results()
            print(f"[{positions[module]}/{len(order)}] EXIT {record['exit_code']} "
                  f"{record['seconds']}s {module}", flush=True)
            if stdout:
                print(stdout, flush=True)
if failed:
    print(f"FAIL: {len(errors)} compilation failures; {len(failed) - len(errors)} blocked modules", flush=True)
    print("\n".join(errors), flush=True)
    raise SystemExit(1)
print(f"PASS: verified actual project import closure for {', '.join(TARGETS)}", flush=True)

# Re-elaborate the audit with the same compiler, even if all objects were cached.
if not AUDIT.is_file():
    raise SystemExit("Missing MOM_BASE/Audit.lean: the axiom gate is mandatory")
expected = re.findall(r"^\s*#print\s+axioms\s+(\S+)\s*$", AUDIT.read_text(), re.M)
if not expected or len(expected) != len(set(expected)):
    raise SystemExit("The axiom audit must list distinct, fully qualified declarations")
audit_command = [lean, "-j1", *option_flags(config.get("leanOptions", {})), str(AUDIT)]
audit = subprocess.run(audit_command, cwd=ROOT, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(LOGS / "axioms.log").write_text(audit.stdout)
print(audit.stdout, flush=True)
if audit.returncode:
    raise SystemExit(f"Axiom audit compilation failed: {audit.returncode}")
pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
rows = re.findall(pattern, audit.stdout, re.S)
records = {}
for name, names in rows:
    if name in records:
        raise SystemExit(f"Duplicate axiom output: {name}")
    records[name] = {item.strip() for item in names.split(",") if item.strip()}
missing = set(expected) - records.keys()
if missing:
    raise SystemExit(f"Missing axiom records: {sorted(missing)}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
violations = {name: sorted(records[name] - allowed) for name in expected
              if records[name] - allowed}
summary = {"expected": expected, "allowed": sorted(allowed),
           "records": {name: sorted(records[name]) for name in expected},
           "violations": violations, "exit_code": audit.returncode,
           "complete": not violations}
write_json_atomic(LOGS / "axioms.json", summary)
if violations:
    raise SystemExit(f"Unexpected axioms: {violations}")
print(f"PASS: {len(expected)} target declarations use only the three standard axioms", flush=True)
