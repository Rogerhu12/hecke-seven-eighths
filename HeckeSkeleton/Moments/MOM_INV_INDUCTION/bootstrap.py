#!/usr/bin/env python3
"""Optionally restore genuine, exact-source MomentInputs prerequisites.

The pinned producer job built with ordinary Lake before exporting its archive.
The producer source snapshot is checked against its full manifest fingerprint;
the selected current source closure must match it exactly. The authenticated
archive supplies genuine objects, native companions and Lake traces. No new task
module is restored, and the mandatory Lake build and axiom checks always follow
this optimization.

`plan` checks the source closure and reports whether a download is useful.
`check DIR` verifies a downloaded archive without installing any files.
`restore DIR` additionally checks the live compiler/package revisions and
installs only the selected files, after all validation has finished.
`--optional` records an unavailable/incompatible bootstrap and leaves the normal
source build to proceed. It never converts a compilation or axiom failure.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import tempfile
import tomllib

REPO = Path(__file__).resolve().parents[3]
PRODUCER = {'repository': 'Rogerhu12/hecke-seven-eighths',
 'run_id': 41126752041,
 'job_id': 124391311879,
 'producer_commit': '984b0de3ddf8bd9ea8051e0325765532c7c6550f',
 'source_fingerprint': '6707201d5789aca4222679e9dbf24b924367c460eda132ec71296300fcfb8a40',
 'toolchain': 'leanprover/lean4:v4.35.0-rc3',
 'lean_commit': '470d5ce1400764999581fd26d5d72b00d990b0f4',
 'mathlib': '0493595ecd5da8ef14742febab99728f98e948e8',
 'target': 'HeckeGeneral.Analysis.MomentInputs',
 'artifact': {'artifact_id': 13012376359,
              'artifact_name': 'prime-foundation-40-0',
              'artifact_size_bytes': 290750533,
              'artifact_zip_sha256': '6c48a54613d0064719d04bf4d4ad6d0491b39b98251bc3808961c0c6afde1324',
              'expires_at': '2026-11-06T21:10:03Z',
              'archive_name': 'foundation-40-0.tar.gz',
              'archive_sha256': 'eeaae4ba35ea0b43578e132afdd904caef3fb7010baa8a3ad963b7e96bcb768e',
              'manifest_name': 'foundation-40-0.manifest.json',
              'canonical_manifest_sha256': 'e11ad340a387cd3767e3a7fe27621e09951cf6e72e8e86621bf20d719942e511',
              'manifest': {'format': 1,
                           'fingerprint': '6707201d5789aca4222679e9dbf24b924367c460eda132ec71296300fcfb8a40',
                           'lower': 0,
                           'upper': 40,
                           'shard': 0,
                           'shards': 4,
                           'owned_modules': 817,
                           'file_count': 7992,
                           'archive_sha256': 'eeaae4ba35ea0b43578e132afdd904caef3fb7010baa8a3ad963b7e96bcb768e'},
              'unpacked_size_bytes': 4214065847}}
CONFIG_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.toml",
                "vendor/class-field-theory/lakefile.toml")
BUILD_ROOTS = (".lake/build", "vendor/class-field-theory/.lake/build")
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)")
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(raw):
    return json.loads(raw, object_pairs_hook=unique_object)


def file_hash(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def canonical_hash(value):
    raw = json.dumps(value, sort_keys=True, separators=(",", ":"),
                     ensure_ascii=True, allow_nan=False).encode()
    return hashlib.sha256(raw).hexdigest()


def header_imports(text):
    """Read the Lean import header, including nested comments/public imports."""
    result, depth = [], 0
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
        if not line or line in ("prelude", "module"):
            continue
        match = IMPORT.fullmatch(line)
        if not match:
            break
        names = match[1].split()
        if not all(MODULE.fullmatch(name) for name in names):
            raise ValueError(f"Unsupported import header: {line}")
        result.extend(names)
    return list(dict.fromkeys(result))


def project_graph(repo, target):
    config = tomllib.loads((repo / "lakefile.toml").read_text())
    roots = [(repo, BUILD_ROOTS[0])]
    roots.extend((repo / lib.get("srcDir", "."), BUILD_ROOTS[0])
                 for lib in config["lean_lib"])
    roots.append((repo / "vendor/class-field-theory/Lean4", BUILD_ROOTS[1]))
    roots = list(dict.fromkeys(roots))
    found, external, visiting = {}, set(), set()

    def visit(name):
        if name in found or name in external:
            return
        if name in visiting:
            raise ValueError(f"Project import cycle: {name}")
        relative = Path(*name.split(".")).with_suffix(".lean")
        location = next(((root / relative, build) for root, build in roots
                         if (root / relative).is_file()), None)
        if location is None:
            external.add(name)
            return
        path, build = location
        visiting.add(name)
        for dependency in header_imports(path.read_text(encoding="utf-8-sig")):
            visit(dependency)
        visiting.remove(name)
        found[name] = {"source": path.relative_to(repo).as_posix(),
                       "source_sha256": file_hash(path), "build": build}

    visit(target)
    if target not in found:
        raise ValueError(f"Missing project target: {target}")
    return found


def checked_sources(repo, producer):
    revision = subprocess.check_output(["git", "-C", str(producer), "rev-parse", "HEAD"],
                                       text=True).strip()
    if revision != PRODUCER["producer_commit"]:
        raise ValueError("The producer source checkout is not the pinned commit")
    original = project_graph(producer, "HeckeSkeleton.Moments")
    configuration = {name: file_hash(producer / name) for name in CONFIG_FILES}
    fingerprint = canonical_hash({"modules": {name: row["source_sha256"]
                                               for name, row in original.items()},
                                  "config": configuration})
    if fingerprint != PRODUCER["source_fingerprint"]:
        raise ValueError("Producer source/configuration fingerprint differs from its native manifest")
    if any(file_hash(repo / name) != digest for name, digest in configuration.items()):
        raise ValueError("Current compiler/package configuration differs from the producer")
    current = project_graph(repo, PRODUCER["target"])
    previous = project_graph(producer, PRODUCER["target"])
    if current != previous:
        raise ValueError("The current MomentInputs source/dependency closure differs from the producer")
    return current


def checked_environment(repo, catalog):
    version = subprocess.check_output(["lake", "env", "lean", "--version"],
                                      cwd=repo, text=True).strip()
    if ("version 4.35.0-rc3" not in version
            or catalog["lean_commit"] not in version):
        raise ValueError(f"Unexpected Lean compiler: {version}")
    manifest = read_json((repo / "lake-manifest.json").read_bytes())
    packages = {}
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        directory = repo / manifest["packagesDir"] / package["name"]
        revision = subprocess.check_output(["git", "-C", str(directory),
                                            "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(directory), "status",
                                         "--porcelain", "--untracked-files=no"], text=True)
        if revision != package["rev"] or dirty:
            raise ValueError(f"Package source/revision differs: {package['name']}")
        packages[package["name"]] = revision
    if packages.get("mathlib") != catalog["mathlib"]:
        raise ValueError("Mathlib revision differs from the native producer")
    return {"lean": version, "packages": packages}


def safe_path(base, name):
    relative = PurePosixPath(name)
    if (relative.is_absolute() or ".." in relative.parts or "\\" in name
            or relative.as_posix() != name
            or not any(name.startswith(root + "/") for root in BUILD_ROOTS)):
        raise ValueError(f"Unsafe artifact path: {name}")
    path = base
    for part in relative.parts:
        path = path / part
        if path.is_symlink():
            raise ValueError(f"Refusing an artifact destination through a symlink: {name}")
    return path


class HashedReader:
    def __init__(self, source):
        self.source, self.digest = source, hashlib.sha256()

    def read(self, size=-1):
        data = self.source.read(size)
        self.digest.update(data)
        return data


def checked_archive(stream, catalog, staging=None):
    """Authenticate every compressed byte; stage selected files without publishing."""
    artifact = catalog["artifact"]
    stems, required = {}, set()
    for name, row in catalog["modules"].items():
        relative = name.replace(".", "/")
        for directory in ("lib/lean", "ir"):
            stems[f"{row['build']}/{directory}/{relative}"] = name
        for suffix in (".olean", ".trace"):
            required.add(f"{row['build']}/lib/lean/{relative}{suffix}")
    reader, seen, selected = HashedReader(stream), set(), []
    total = 0
    with tarfile.open(fileobj=reader, mode="r|gz", bufsize=1024 * 1024) as archive:
        for member in archive:
            safe_path(Path("/not-an-installation-directory"), member.name)
            if not member.isfile() or member.name in seen or member.size < 0:
                raise ValueError(f"Nonregular or duplicate artifact member: {member.name}")
            seen.add(member.name)
            total += member.size
            path = PurePosixPath(member.name)
            stem = (path.parent / path.name.split(".", 1)[0]).as_posix()
            name = stems.get(stem)
            if name is None:
                continue
            output = safe_path(staging, member.name) if staging else None
            if output:
                output.parent.mkdir(parents=True, exist_ok=True)
            digest, count = hashlib.sha256(), 0
            with archive.extractfile(member) as source:
                destination = output.open("xb") if output else None
                try:
                    while block := source.read(1024 * 1024):
                        digest.update(block)
                        count += len(block)
                        if destination:
                            destination.write(block)
                finally:
                    if destination:
                        destination.close()
            if count != member.size:
                raise ValueError(f"Truncated artifact member: {member.name}")
            if output:
                os.chmod(output, 0o644)
                os.utime(output, (member.mtime, member.mtime))
            selected.append({"path": member.name, "sha256": digest.hexdigest(), "bytes": count})
    while reader.read(1024 * 1024):
        pass
    if reader.digest.hexdigest() != artifact["archive_sha256"]:
        raise ValueError("Pinned native archive digest differs")
    if (len(seen) != artifact["manifest"]["file_count"]
            or total != artifact["unpacked_size_bytes"]
            or not required <= {row["path"] for row in selected}):
        raise ValueError("Artifact count, size, or selected native/trace coverage differs")
    return selected


def verify_download(directory, catalog, staging=None):
    artifact = catalog["artifact"]
    manifest_path = directory / artifact["manifest_name"]
    if manifest_path.stat().st_size > 65536:
        raise ValueError("Oversized artifact manifest")
    manifest = read_json(manifest_path.read_bytes())
    if (manifest != artifact["manifest"]
            or canonical_hash(manifest) != artifact["canonical_manifest_sha256"]):
        raise ValueError("Pinned producer manifest differs")
    with (directory / artifact["archive_name"]).open("rb") as stream:
        return checked_archive(stream, catalog, staging)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "check", "restore"))
    parser.add_argument("directory", nargs="?", type=Path)
    parser.add_argument("--producer-source", type=Path)
    parser.add_argument("--optional", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.action != "plan" and (args.directory is None or args.producer_source is None):
        parser.error("check/restore require an artifact directory and --producer-source")
    report = {"operation": args.action, "status": "unavailable", "producer_run": PRODUCER["run_id"],
              "producer_job": PRODUCER["job_id"], "artifact": PRODUCER["artifact"]["artifact_id"]}
    try:
        if args.action == "plan":
            modules = project_graph(REPO, PRODUCER["target"])
            needed = any(not (REPO / row["build"] / "lib/lean" /
                              name.replace(".", "/")).with_suffix(suffix).is_file()
                         for name, row in modules.items() for suffix in (".olean", ".trace"))
            expiry = datetime.fromisoformat(PRODUCER["artifact"]["expires_at"].replace("Z", "+00:00"))
            if datetime.now(timezone.utc) >= expiry:
                needed = False
                report["notice"] = "Pinned optional artifact expired; ordinary Lake compilation follows"
            report.update(status="planned", source_modules=len(modules), needed=needed)
        else:
            modules = checked_sources(REPO, args.producer_source)
            catalog = {**PRODUCER, "modules": modules}
            report.update(source_modules=len(modules), sources=modules)
            if args.action == "check":
                files = verify_download(args.directory, catalog)
                report.update(status="verified", files=files)
            else:
                report["environment"] = checked_environment(REPO, PRODUCER)
                # The full uncompressed archive bounds the smaller selected staging set.
                if shutil.disk_usage(REPO).free < PRODUCER["artifact"]["unpacked_size_bytes"] + 512 * 1024 ** 2:
                    raise ValueError("Insufficient free space for isolated bootstrap validation")
                with tempfile.TemporaryDirectory(prefix=".mom-inv-bootstrap-", dir=REPO) as temporary:
                    staging = Path(temporary)
                    files = verify_download(args.directory, catalog, staging)
                    checked_sources(REPO, args.producer_source)
                    for row in files:
                        safe_path(REPO, row["path"])
                    # Publish complete native companions before their original Lake trace.
                    for row in sorted(files, key=lambda row: row["path"].endswith(".trace")):
                        destination = safe_path(REPO, row["path"])
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        os.replace(staging / row["path"], destination)
                    report.update(status="restored", files=files)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError, tarfile.TarError) as error:
        report.update(status="unavailable", needed=False, reason=str(error))
        if not args.optional:
            raise
        print(f"::notice::Optional native bootstrap unavailable: {error}. Ordinary Lake compilation follows.")
    finally:
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2) + "\n")
        if args.action == "plan" and os.environ.get("GITHUB_OUTPUT"):
            with open(os.environ["GITHUB_OUTPUT"], "a") as output:
                output.write(f"needed={str(report.get('needed', False)).lower()}\n")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "sources")}))
    if "files" in report:
        print(f"{report['status']}: {len(report['files'])} genuine files for {report['source_modules']} source modules")


if __name__ == "__main__":
    main()
