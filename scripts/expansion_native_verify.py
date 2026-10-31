#!/usr/bin/env python3
"""Verify EXPANSION with genuine, previously published native dependencies.

Only existing artifacts from the pinned successful foundation jobs are read.
No Lake trace is created or changed. Native bytes remain outside both existing
cache-save paths and the existing log-artifact directory. Changed sources and
their descendants are compiled from the current checkout before the same
declaration-wide axiom audit used by expansion_verify.py.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import tempfile
import time
import tomllib
import urllib.parse
import urllib.request
import zipfile

import expansion_verify as audit

REPOSITORY = "Rogerhu12/hecke-seven-eighths"
BASE_COMMIT = "984b0de3ddf8bd9ea8051e0325765532c7c6550f"
BASE_RUN = 41126752041
BASE_FINGERPRINT = "6707201d5789aca4222679e9dbf24b924367c460eda132ec71296300fcfb8a40"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
NATIVE_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
BUILD_ROOTS = (".lake/build", "vendor/class-field-theory/.lake/build")
CONFIG_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.toml",
                "vendor/class-field-theory/lakefile.toml")
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)")
# This pin list is derived from the existing artifact digests and successful
# source-fingerprint-checked exporter jobs; it never names newly uploaded data.
ARTIFACTS = [{'id': 13012376359,
  'name': 'prime-foundation-40-0',
  'outer_sha256': '6c48a54613d0064719d04bf4d4ad6d0491b39b98251bc3808961c0c6afde1324',
  'inner_sha256': 'eeaae4ba35ea0b43578e132afdd904caef3fb7010baa8a3ad963b7e96bcb768e',
  'lower': 0,
  'upper': 40,
  'shard': 0,
  'job_id': 124391311879},
 {'id': 13011719707,
  'name': 'prime-foundation-40-1',
  'outer_sha256': '7620df2fdd8bc50d9ae6f43bd14d18732a2fd2cd9c52de010b99e59701975f82',
  'inner_sha256': '4efd5cfae24809b98675993cd5544dfe6caf7d0ffb8d823f22a64f79c8102a8d',
  'lower': 0,
  'upper': 40,
  'shard': 1,
  'job_id': 124391349312},
 {'id': 13011754956,
  'name': 'prime-foundation-40-2',
  'outer_sha256': 'b01697611b3584fa210abd61876a3ccb1e6122a3c217fe55e1a283300aebaf88',
  'inner_sha256': '6d65e704af89126677dfe1dc1142f0e47fdb1f6f07ab7fea3ae5f632d4058c7a',
  'lower': 0,
  'upper': 40,
  'shard': 2,
  'job_id': 124391312354},
 {'id': 13013018508,
  'name': 'prime-foundation-40-3',
  'outer_sha256': '29fb1b025d9226a3d8bebb4849443770b04d90c0a4efeb6a406c6cf0c2d9968b',
  'inner_sha256': '30d2e905cb617a50757b884176ecac1f4adc920cc25141efd104964b4318fa64',
  'lower': 0,
  'upper': 40,
  'shard': 3,
  'job_id': 124391312403},
 {'id': 13017749400,
  'name': 'prime-foundation-100-0',
  'outer_sha256': '384365645f5c02dacf5f8d05bfa4eb6211a2ab5ca9afddcefb39df51b63750be',
  'inner_sha256': '0fb746e74ef721d8167905d35361d87ffee0a563bf807405ed729c8a1dec6d43',
  'lower': 40,
  'upper': 100,
  'shard': 0,
  'job_id': 124391312514},
 {'id': 13018611868,
  'name': 'prime-foundation-100-1',
  'outer_sha256': '57dfd63d075039e0c150635df09c534bfdf8060b88f8602457b2c271f8079fc1',
  'inner_sha256': '1b4ac7498c77c8f84f05390429c1b20539f32585ab5b1350e0a7c5b4f7c9f780',
  'lower': 40,
  'upper': 100,
  'shard': 1,
  'job_id': 124391313658},
 {'id': 13018074066,
  'name': 'prime-foundation-100-2',
  'outer_sha256': 'aa98e4d6970f2350fcd65f8be16fd66fbf069799813a40f682524b7c9e3d82c0',
  'inner_sha256': 'f422c5449fc4ee1732a86ce815954f5161816d11cda1c87bce2e540693a7d27b',
  'lower': 40,
  'upper': 100,
  'shard': 2,
  'job_id': 124391313176},
 {'id': 13015618946,
  'name': 'prime-foundation-100-3',
  'outer_sha256': '9ad599dfa01ff6e197493379480f2d7a62228e783a183e00e3f28841f7cb2f6d',
  'inner_sha256': 'd53889d14a536536028254ecbeb445f193e6afd41eff716f4cedcd3edfe9b1cc',
  'lower': 40,
  'upper': 100,
  'shard': 3,
  'job_id': 124391313199},
 {'id': 13021712535,
  'name': 'prime-foundation-180-0',
  'outer_sha256': '5e5137138741b9932002167dd64de9f71e6ee336de1ad47fe14ead193400d18b',
  'inner_sha256': '60234f15f055d6dabff28edb8b10069a2f4bf9fc8ab5d0aac864905efaf51bbf',
  'lower': 100,
  'upper': 180,
  'shard': 0,
  'job_id': 124391314109},
 {'id': 13021514563,
  'name': 'prime-foundation-180-1',
  'outer_sha256': '14bb73f02e0f2631ca4bf4595cda97f0f90e615ab52cf71b340923fb37036e0f',
  'inner_sha256': '263454fb7a76f21cc7b333d6e82a31f37875c70330afb8468a5444bbb391abcd',
  'lower': 100,
  'upper': 180,
  'shard': 1,
  'job_id': 124391313913},
 {'id': 13021895900,
  'name': 'prime-foundation-180-2',
  'outer_sha256': '80467b2b0110ab6ff10a862ebbfa2742587c00fe0738140b1da54824e096510e',
  'inner_sha256': 'c8b2152ce1a47dcae03984d53fcc96ec45f16bc9e9ed5e5d9d38f2373684b3e9',
  'lower': 100,
  'upper': 180,
  'shard': 2,
  'job_id': 124391313871},
 {'id': 13022623396,
  'name': 'prime-foundation-180-3',
  'outer_sha256': 'bf58ea2a7645a5ac1c10095f03b8bda3a7ed5b4380d7516412e26c160f79f423',
  'inner_sha256': '85cc022948406ffd11dc2fcbd5fd03bc8dd127ca07864b75e2ffca90ec1492b4',
  'lower': 100,
  'upper': 180,
  'shard': 3,
  'job_id': 124391314411}]


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def save(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def header(text: str) -> tuple[list[str], bool]:
    imports, depth, is_module = [], 0, False
    for raw in text.splitlines():
        code, i = [], 0
        while i < len(raw):
            if raw.startswith("/-", i):
                depth += 1
                code.append(" ")
                i += 2
            elif depth and raw.startswith("-/", i):
                depth -= 1
                i += 2
            elif depth:
                i += 1
            elif raw.startswith("--", i):
                break
            else:
                code.append(raw[i])
                i += 1
        line = "".join(code).strip()
        if not line or line == "prelude":
            continue
        if line == "module":
            is_module = True
            continue
        match = IMPORT.fullmatch(line)
        if not match:
            break
        names = match[1].split()
        if not all(MODULE.fullmatch(n) for n in names):
            raise ValueError(f"Unsupported import header: {line}")
        imports.extend(names)
    return list(dict.fromkeys(imports)), is_module


def flatten_options(value: dict, prefix="") -> dict:
    result = {}
    for key, item in value.items():
        name = prefix + key
        if isinstance(item, dict):
            result.update(flatten_options(item, name + "."))
        else:
            result[name] = item
    return result


class Graph:
    def __init__(self, repo: Path, targets: list[str]):
        self.repo, self.nodes, self.order, self.external = repo, {}, [], set()
        config = tomllib.loads((repo / "lakefile.toml").read_text())
        vendor = tomllib.loads((repo / CONFIG_FILES[-1]).read_text())
        self.config = config
        roots = [(repo, ".lake/build", config)]
        roots += [(repo / lib.get("srcDir", "."), ".lake/build", config)
                  for lib in config.get("lean_lib", [])]
        roots += [(repo / "vendor/class-field-theory/Lean4", BUILD_ROOTS[1], vendor)]
        self.roots = []
        seen = set()
        for root, build, package in roots:
            if root not in seen:
                seen.add(root)
                self.roots.append((root, build, package))
        prefixes = {name.split(".")[0] for package in (config, vendor)
                    for lib in package.get("lean_lib", [])
                    for name in lib.get("roots", [lib["name"]])}
        active = set()

        def visit(name):
            if name in self.nodes or name in self.external:
                return
            if name in active:
                raise ValueError("Import cycle: " + name)
            relative = Path(*name.split(".")).with_suffix(".lean")
            matches = [(root / relative, root, build, pkg)
                       for root, build, pkg in self.roots if (root / relative).is_file()]
            if len({entry[0].resolve() for entry in matches}) > 1:
                raise ValueError("Ambiguous project module source: " + name)
            found = matches[0] if matches else None
            if found is None:
                if name.split(".")[0] in prefixes:
                    raise FileNotFoundError("Missing project source: " + name)
                self.external.add(name)
                return
            active.add(name)
            path, root, build, package = found
            raw = path.read_bytes()
            deps, is_module = header(raw.decode("utf-8-sig"))
            for dep in deps:
                visit(dep)
            project_deps = [dep for dep in deps if dep in self.nodes]
            options = flatten_options(package.get("leanOptions", {}))
            for lib in package.get("lean_lib", []):
                names = lib.get("roots", [lib["name"]]) + [g.removesuffix(".+") for g in lib.get("globs", [])]
                if any(name == n or name.startswith(n + ".") for n in names):
                    options.update(flatten_options(lib.get("leanOptions", {})))
            if build == BUILD_ROOTS[0]:
                assert options.get("autoImplicit") is False and options.get("relaxedAutoImplicit") is False
            self.nodes[name] = {"path": path, "root": root, "build": build,
                                "sha256": hashlib.sha256(raw).hexdigest(),
                                "deps": project_deps, "is_module": is_module,
                                "depth": 1 + max((self.nodes[d]["depth"] for d in project_deps), default=0),
                                "options": options}
            self.order.append(name)
            active.remove(name)

        for target in targets:
            visit(target)

    def fingerprint(self):
        value = {"modules": {n: v["sha256"] for n, v in self.nodes.items()},
                 "config": {p: digest(self.repo / p) for p in CONFIG_FILES}}
        return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if urllib.parse.urlsplit(newurl).scheme != "https":
            raise ValueError("Refusing a non-HTTPS download redirect")
        new = super().redirect_request(req, fp, code, msg, headers, newurl)
        if urllib.parse.urlsplit(newurl).netloc != urllib.parse.urlsplit(req.full_url).netloc:
            new.remove_header("Authorization")
        return new


def request(url: str):
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "expansion-native-verifier"}
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = "Bearer " + token
    return urllib.request.build_opener(SafeRedirect()).open(urllib.request.Request(url, headers=headers), timeout=120)


def api(path: str):
    with request(f"https://api.github.com/repos/{REPOSITORY}/{path}") as response:
        return json.load(response)


def download(url: str, target: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_suffix(target.suffix + ".partial")
    with request(url) as response, temporary.open("wb") as output:
        shutil.copyfileobj(response, output, 1024 * 1024)
    temporary.replace(target)


def safe_name(name: str) -> PurePosixPath:
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or "\\" in name or not path.parts:
        raise ValueError("Unsafe archive path: " + name)
    return path


def baseline_checkout(work: Path) -> Path:
    archive, destination = work / "baseline.tar.gz", work / "baseline"
    download(f"https://api.github.com/repos/{REPOSITORY}/tarball/{BASE_COMMIT}", archive)
    destination.mkdir(exist_ok=True)
    names, top = set(), None
    with tarfile.open(archive, "r|gz") as stream:
        for member in stream:
            relative = safe_name(member.name)
            if top is None:
                top = relative.parts[0]
            if relative.parts[0] != top:
                raise ValueError("Multiple baseline archive roots")
            if member.isdir():
                continue
            if not member.isfile() or member.name in names:
                raise ValueError("Non-regular or duplicate baseline member")
            names.add(member.name)
            path = Path(*relative.parts[1:])
            if not (path.suffix == ".lean" or path.name in {"lakefile.toml", "lean-toolchain", "lake-manifest.json"}):
                continue
            output = destination / path
            output.parent.mkdir(parents=True, exist_ok=True)
            with stream.extractfile(member) as source, output.open("wb") as target:
                shutil.copyfileobj(source, target, 1024 * 1024)
    archive.unlink()
    return destination


def validate_configs(repo: Path, base: Graph):
    for filename in ("lean-toolchain", "lake-manifest.json", CONFIG_FILES[-1]):
        if digest(repo / filename) != digest(base.repo / filename):
            raise ValueError("Pinned configuration changed: " + filename)
    manifest = json.loads((repo / "lake-manifest.json").read_text())
    if next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib") != MATHLIB:
        raise ValueError("Wrong pinned Mathlib revision")
    current = tomllib.loads((repo / "lakefile.toml").read_text())
    extras = {"Expansion", "ExpansionDetector", "ExpansionInterfaces"}
    filtered = []
    for lib in current.get("lean_lib", []):
        if lib["name"] in extras:
            if lib != {"name": lib["name"], "globs": [lib["name"] + ".+"]}:
                raise ValueError("Unreviewed added-library configuration")
        else:
            filtered.append(lib)
    current["lean_lib"] = filtered
    if current != base.config:
        raise ValueError("Existing Lake libraries or package options changed")


def eligible_seeds(graph: Graph, base: Graph):
    eligible = set()
    for name in graph.order:
        node, original = graph.nodes[name], base.nodes.get(name)
        if original and original["depth"] <= 180 and original["sha256"] == node["sha256"] and original["deps"] == node["deps"] and original["build"] == node["build"] and all(d in eligible for d in node["deps"]):
            eligible.add(name)
    return eligible


def restore_zip(archive: Path, pin: dict, graph: Graph, base: Graph,
                wanted: set[str], output: Path, restored: dict):
    if digest(archive) != pin["outer_sha256"]:
        raise ValueError("Artifact ZIP digest mismatch")
    prefixes = {root + "/lib/lean/": root for root in BUILD_ROOTS}
    with zipfile.ZipFile(archive) as bundle:
        manifests = [n for n in bundle.namelist() if n.endswith(".manifest.json")]
        archives = [n for n in bundle.namelist() if n.endswith(".tar.gz")]
        if len(bundle.namelist()) != 2 or len(manifests) != 1 or len(archives) != 1:
            raise ValueError("Unexpected artifact ZIP structure")
        for name in bundle.namelist():
            safe_name(name)
        manifest = json.loads(bundle.read(manifests[0]))
        expected = {"format": 1, "fingerprint": BASE_FINGERPRINT,
                    "lower": pin["lower"], "upper": pin["upper"],
                    "shard": pin["shard"], "shards": 4,
                    "archive_sha256": pin["inner_sha256"]}
        if any(manifest.get(k) != v for k, v in expected.items()):
            raise ValueError("Foundation manifest mismatch")
        with bundle.open(archives[0]) as compressed:
            if hashlib.file_digest(compressed, "sha256").hexdigest() != pin["inner_sha256"]:
                raise ValueError("Inner archive digest mismatch")
        seen, owned = set(), set()
        with bundle.open(archives[0]) as compressed, tarfile.open(fileobj=compressed, mode="r|gz") as stream:
            for member in stream:
                relative = safe_name(member.name)
                if not member.isfile() or member.name in seen:
                    raise ValueError("Non-regular or duplicate native archive member")
                if not any(member.name.startswith(root + "/") for root in BUILD_ROOTS):
                    raise ValueError("Archive member outside original build roots")
                seen.add(member.name)
                prefix = next((p for p in prefixes if member.name.startswith(p)), None)
                suffix = next((s for s in reversed(NATIVE_SUFFIXES) if member.name.endswith(s)), None)
                if not prefix or not suffix:
                    continue
                name = member.name[len(prefix):-len(suffix)].replace("/", ".")
                if name not in base.nodes or not pin["lower"] < base.nodes[name]["depth"] <= pin["upper"]:
                    raise ValueError("Native module outside the original dependency stage")
                if base.nodes[name]["build"] != prefixes[prefix]:
                    raise ValueError("Native module/package collision")
                if suffix == ".olean":
                    owned.add(name)
                if name not in wanted:
                    continue
                result = restored.setdefault(name, {"status": "validated_existing_artifact", "artifact_id": pin["id"],
                    "source_sha256": graph.nodes[name]["sha256"], "files": {}})
                if result["artifact_id"] != pin["id"] or suffix in result["files"]:
                    raise ValueError("Duplicate native module across artifacts")
                target = output / (name.replace(".", "/") + suffix)
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.exists() or target.is_symlink():
                    raise ValueError("Refusing to overwrite an existing native seed")
                with stream.extractfile(member) as source, target.open("wb") as destination:
                    shutil.copyfileobj(source, destination, 1024 * 1024)
                if target.stat().st_size != member.size:
                    raise ValueError("Truncated native file")
                if suffix == ".olean":
                    with target.open("rb") as native:
                        signature = native.read(96)
                    if not signature.startswith(b"olean") or b"4.35.0-rc3" not in signature or LEAN_COMMIT.encode() not in signature:
                        raise ValueError("Native file compiler signature mismatch: " + name)
                result["files"][suffix] = {"sha256": digest(target), "size_bytes": member.size}
        if len(seen) != manifest["file_count"] or len(owned) != manifest["owned_modules"]:
            raise ValueError("Original artifact inventory mismatch")


def restore_seeds(work, output, graph, base, wanted):
    restored, evidence = {}, []
    for pin in ARTIFACTS:
        if not any(pin["lower"] < base.nodes[n]["depth"] <= pin["upper"] for n in wanted):
            continue
        metadata = api(f"actions/artifacts/{pin['id']}")
        job = api(f"actions/jobs/{pin['job_id']}")
        if metadata["expired"] or metadata["digest"] != "sha256:" + pin["outer_sha256"] or metadata["workflow_run"]["id"] != BASE_RUN or metadata["workflow_run"]["head_sha"] != BASE_COMMIT:
            raise ValueError("Published artifact provenance mismatch")
        if job["run_id"] != BASE_RUN or job["conclusion"] != "success" or not any(s["name"] == "Compile and package this dependency group" and s["conclusion"] == "success" for s in job["steps"]):
            raise ValueError("Original compiler/exporter job did not succeed")
        archive = work / f"artifact-{pin['id']}.zip"
        download(f"https://api.github.com/repos/{REPOSITORY}/actions/artifacts/{pin['id']}/zip", archive)
        restore_zip(archive, pin, graph, base, wanted, output, restored)
        evidence.append({**pin, "original_job_conclusion": "success", "zip_bytes": archive.stat().st_size})
        archive.unlink()
        print(f"VALIDATED EXISTING ARTIFACT {pin['id']}; accumulated {len(restored)} modules", flush=True)
    if set(restored) != wanted:
        raise ValueError("Missing required original native modules: " + repr(sorted(wanted - set(restored))))
    for name, record in restored.items():
        required = set(NATIVE_SUFFIXES) if graph.nodes[name]["is_module"] else {".olean"}
        if set(record["files"]) != required:
            raise ValueError("Incomplete native companion set: " + name)
    return restored, evidence


def lean_environment(repo: Path, output: Path):
    version = subprocess.check_output(["lean", "--version"], cwd=repo, text=True).strip()
    if "4.35.0-rc3" not in version or LEAN_COMMIT not in version:
        raise ValueError("Wrong native Lean compiler: " + version)
    mathlib_head = subprocess.check_output(["git", "-C", str(repo / ".lake/packages/mathlib"), "rev-parse", "HEAD"], text=True).strip()
    if mathlib_head != MATHLIB:
        raise ValueError("Installed Mathlib checkout differs from the pinned revision")
    paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, text=True).strip().split(os.pathsep)
    excluded = {(repo / root / "lib/lean").resolve() for root in BUILD_ROOTS}
    resolved = [(Path(p) if Path(p).is_absolute() else repo / p).resolve() for p in paths if p]
    external = [str(p) for p in resolved if p not in excluded]
    environment = dict(os.environ)
    environment.pop("GH_TOKEN", None)
    environment.pop("GITHUB_TOKEN", None)
    environment["LEAN_PATH"] = os.pathsep.join([str(output), *external])
    return environment, version


def compile_module(name, graph, output, environment, logs):
    node, start = graph.nodes[name], time.monotonic()
    artifact = output / (name.replace(".", "/") + ".olean")
    artifact.parent.mkdir(parents=True, exist_ok=True)
    options = [f"-D{k}={str(v).lower() if isinstance(v, bool) else v}" for k, v in node["options"].items()]
    command = ["lean", "-j2", *options, "-R", str(node["root"]), "-o", str(artifact), str(node["path"])]
    log = logs / (name + ".log")
    with log.open("w") as stream:
        process = subprocess.run(command, cwd=graph.repo, env=environment, stdout=stream, stderr=subprocess.STDOUT)
    unchanged = digest(node["path"]) == node["sha256"]
    passed = process.returncode == 0 and unchanged and artifact.is_file()
    files = {}
    for suffix in NATIVE_SUFFIXES:
        path = output / (name.replace(".", "/") + suffix)
        if path.is_file():
            if passed:
                files[suffix] = {"sha256": digest(path), "size_bytes": path.stat().st_size}
            else:
                path.unlink()
    return {"status": "native_pass" if passed else "native_failure", "source_sha256": node["sha256"],
            "source_unchanged": unchanged, "exit_code": process.returncode, "seconds": round(time.monotonic() - start, 3),
            "effective_lean_options": node["options"], "files": files,
            "source": str(node["path"].relative_to(graph.repo)), "compiler_log_sha256": digest(log)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--group", choices=("pure", "actual", "skeleton"), required=True)
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=2)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--baseline-dir", type=Path, help="Offline plan/provenance check only")
    args = parser.parse_args()
    if args.baseline_dir and not args.plan:
        parser.error("--baseline-dir is restricted to --plan")
    repo, logs = audit.ROOT, audit.OUT
    logs.mkdir(exist_ok=True)
    work = repo / ".lake/expansion-native" / args.group
    if work.exists() and not args.plan:
        raise SystemExit("Native workspace already exists; use a fresh CI checkout")
    work.mkdir(parents=True, exist_ok=True)
    baseline = args.baseline_dir or baseline_checkout(work)
    original = Graph(baseline, ["HeckeSkeleton.Moments"])
    if original.fingerprint() != BASE_FINGERPRINT or sum(n["depth"] <= 180 for n in original.nodes.values()) != 4433:
        raise ValueError("Original source/configuration fingerprint does not match the published artifacts")
    validate_configs(repo, original)
    targets = audit.groups(audit.sources())[args.group]
    graph = Graph(repo, targets)
    config_hashes = {path: digest(repo / path) for path in CONFIG_FILES}
    wanted = eligible_seeds(graph, original)
    plan = {"group": args.group, "original_commit": BASE_COMMIT, "original_run": BASE_RUN,
            "original_fingerprint": BASE_FINGERPRINT, "targets": targets,
            "project_modules": len(graph.nodes), "eligible_native_seed_modules": len(wanted),
            "fresh_compile_modules": len(graph.nodes) - len(wanted),
            "package_options_policy": "Current root proofs use autoImplicit=false and relaxedAutoImplicit=false; vendor dependencies retain their verified original package/library options."}
    save(logs / (args.group + "-native-plan.json"), plan)
    print(json.dumps(plan), flush=True)
    if args.plan:
        return
    output = work / "lib/lean"
    output.mkdir(parents=True)
    environment, compiler = lean_environment(repo, output)
    save(logs / (args.group + "-sources.json"), {"group": args.group,
        "audit_policy": "report all inherited axioms" if args.group == "skeleton" else "standard axioms only",
        "sources": [{"module": n, "path": str(graph.nodes[n]["path"].relative_to(repo)), "sha256": graph.nodes[n]["sha256"]} for n in targets]})
    results, artifacts = restore_seeds(work, output, graph, original, wanted)
    save(logs / (args.group + "-native-seeds.json"), {"compiler": compiler, "mathlib": MATHLIB,
        "source_fingerprint": BASE_FINGERPRINT, "artifacts": artifacts, "modules": results})
    build_log = logs / (args.group + "-build.log")
    pending = set(graph.nodes) - set(results)
    running = {}
    failures = set()
    with build_log.open("w") as combined, concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            for name in graph.order:
                if name not in pending:
                    continue
                deps = graph.nodes[name]["deps"]
                if any(d in failures for d in deps):
                    pending.remove(name)
                    failures.add(name)
                    results[name] = {"status": "blocked_by_failed_dependency", "source_sha256": graph.nodes[name]["sha256"]}
                elif len(running) < args.jobs and all(d in results for d in deps):
                    pending.remove(name)
                    running[pool.submit(compile_module, name, graph, output, environment, logs)] = name
            if not running:
                if pending:
                    raise RuntimeError("Native dependency scheduler made no progress")
                break
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                record = future.result()
                results[name] = record
                if record["status"] != "native_pass":
                    failures.add(name)
                line = f"NATIVE {record['status']} {name} ({record['seconds']}s)\n"
                text = (logs / (name + ".log")).read_text()
                print(line + text, end="", flush=True)
                combined.write(line + text)
                combined.flush()
                save(logs / (args.group + "-native-results.json"), results)
    save(logs / (args.group + "-native-results.json"), results)
    if failures:
        raise SystemExit(1)
    if any(digest(node["path"]) != node["sha256"] for node in graph.nodes.values()):
        raise ValueError("A project source changed during validation")
    if any(digest(repo / path) != value for path, value in config_hashes.items()):
        raise ValueError("A project configuration changed during validation")
    audit_path = logs / (args.group + "_audit.lean")
    audit_path.write_text(audit.audit_source(targets, args.group != "skeleton"))
    with (logs / (args.group + "-axioms.log")).open("w") as stream:
        process = subprocess.Popen(["lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", str(audit_path)],
            cwd=repo, env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            print(line, end="", flush=True)
            stream.write(line)
        raise SystemExit(process.wait())


if __name__ == "__main__":
    main()
