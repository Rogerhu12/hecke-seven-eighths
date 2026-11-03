#!/usr/bin/env python3
"""Build and transfer four shards of the genuine Moments dependency graph.

Examples (Python 3.11+, no third-party Python dependencies):
  python scripts/prime_cancellation_foundation.py --fingerprint
  python scripts/prime_cancellation_foundation.py 0 40 0 --plan-only
  python scripts/prime_cancellation_foundation.py 40 180 0 --restore downloaded
  python scripts/prime_cancellation_foundation.py --restore downloaded

Only a successful real Lake build can produce an archive. Earlier depth ranges
are supplied by the preceding stage's artifacts; they are never replaced by
placeholder modules. Lake checks its ordinary build traces on every invocation.
"""
from __future__ import annotations

import argparse
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

TARGET = "HeckeSkeleton.Moments"
SHARDS = 4
BUILD_DIRS = (Path(".lake/build"), Path("vendor/class-field-theory/.lake/build"))
FACTORS = (1.05, 1.15, 1.25, 1.5, 2.0, 3.0)
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)")
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def header_imports(text: str) -> list[str]:
    """Read Lean's import header, including nested comments and public imports."""
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
        modules = match[1].split()
        if not all(MODULE.fullmatch(name) for name in modules):
            raise ValueError(f"Unsupported import header: {line}")
        result.extend(modules)
    return list(dict.fromkeys(result))


class ProjectGraph:
    def __init__(self, repo: Path):
        self.repo = repo
        config = tomllib.loads((repo / "lakefile.toml").read_text())
        self.roots = [(repo, BUILD_DIRS[0])]
        self.project_prefixes = set()
        for library in config.get("lean_lib", []):
            self.roots.append((repo / library.get("srcDir", "."), BUILD_DIRS[0]))
            for name in library.get("roots", [library["name"]]):
                self.project_prefixes.add(name.split(".")[0])
        package = repo / "vendor/class-field-theory"
        self.roots.append((package / "Lean4", BUILD_DIRS[1]))
        for library in tomllib.loads((package / "lakefile.toml").read_text()).get("lean_lib", []):
            self.project_prefixes.add(library["name"].split(".")[0])
        self.roots = list(dict.fromkeys(self.roots))
        self.nodes, self.depth, self.external = {}, {}, set()
        visiting, found = set(), {}

        def find(name):
            if name not in found:
                relative = Path(*name.split(".")).with_suffix(".lean")
                found[name] = next(((root / relative, build) for root, build in self.roots
                                    if (root / relative).is_file()), None)
                if found[name] is None and name.split(".")[0] in self.project_prefixes:
                    raise FileNotFoundError(f"Missing project module {name}")
            return found[name]

        def visit(name):
            if name in self.nodes or name in self.external:
                return
            source = find(name)
            if source is None:
                self.external.add(name)
                return
            if name in visiting:
                raise ValueError(f"Import cycle at {name}")
            visiting.add(name)
            path, build = source
            raw = path.read_bytes()
            dependencies = header_imports(raw.decode("utf-8-sig"))
            for dependency in dependencies:
                visit(dependency)
            dependencies = [d for d in dependencies if d in self.nodes]
            self.nodes[name] = {"source": path, "build": build, "deps": dependencies,
                                "sha256": sha256(raw)}
            self.depth[name] = 1 + max((self.depth[d] for d in dependencies), default=0)
            visiting.remove(name)

        visit(TARGET)
        self.names = sorted(self.nodes, key=lambda n: (self.depth[n], n))
        self.index = {name: i for i, name in enumerate(self.names)}
        self.closure, self.children = {}, {name: [] for name in self.names}
        for name in self.names:
            bits = 1 << self.index[name]
            for dependency in self.nodes[name]["deps"]:
                bits |= self.closure[dependency]
                self.children[dependency].append(name)
            self.closure[name] = bits
        self.config_files = [repo / name for name in
            ("lean-toolchain", "lake-manifest.json", "lakefile.toml",
             "vendor/class-field-theory/lakefile.toml")]
        self.fingerprint = self.source_fingerprint()

    def source_fingerprint(self) -> str:
        sources = {name: file_sha256(self.nodes[name]["source"]) for name in self.names}
        config = {str(path.relative_to(self.repo)): file_sha256(path) for path in self.config_files}
        return sha256(json.dumps({"modules": sources, "config": config},
                                 sort_keys=True, separators=(",", ":")).encode())


def partition(graph: ProjectGraph, lower: int, upper: int) -> dict:
    """Balance exact dependency closures; repeat only unavoidable shared inputs."""
    base = sum(1 << graph.index[n] for n in graph.names if graph.depth[n] <= lower)
    selected = [n for n in graph.names if lower < graph.depth[n] <= upper]
    targets = [n for n in selected
               if not any(graph.depth[c] <= upper for c in graph.children[n])]
    targets.sort(key=lambda n: (graph.closure[n] & ~base).bit_count(), reverse=True)
    alternatives = []
    for factor in FACTORS:
        parts, counts, roots = [0] * SHARDS, [0] * SHARDS, [[] for _ in range(SHARDS)]
        cap = len(selected) / SHARDS * factor
        for name in targets:
            closure = graph.closure[name] & ~base
            added = [(closure & ~part).bit_count() for part in parts]
            if min(added) == 0:
                continue
            fitting = [i for i in range(SHARDS) if counts[i] + added[i] <= cap]
            if fitting:
                shard = min(fitting, key=lambda i: (added[i], counts[i], i))
            else:
                shard = min(range(SHARDS), key=lambda i: (counts[i] + added[i], added[i], i))
            parts[shard] |= closure
            counts[shard] = parts[shard].bit_count()
            roots[shard].append(name)
        alternatives.append((max(counts), sum(counts), factor, parts, counts, roots))
    _, total, factor, parts, counts, roots = min(alternatives, key=lambda item: item[:3])
    owners = {}
    for name in selected:
        bit = 1 << graph.index[name]
        containing = [i for i, part in enumerate(parts) if part & bit]
        if not containing:
            raise AssertionError(f"Uncovered project module {name}")
        owners[name] = min(containing)
    for part in parts:
        for name in selected:
            if part & (1 << graph.index[name]) and graph.closure[name] & ~(part | base):
                raise AssertionError(f"Missing dependency in shard for {name}")
    return {"target": TARGET, "fingerprint": graph.fingerprint, "lower": lower, "upper": upper,
            "shards": SHARDS, "project_modules": len(graph.names), "max_depth": max(graph.depth.values()),
            "base_modules": base.bit_count(), "stage_modules": len(selected), "total_work": total,
            "cap_factor": factor, "shard_work": counts, "roots": roots, "owners": owners}


def export_bundle(graph: ProjectGraph, plan: dict, shard: int, output: Path) -> None:
    if graph.source_fingerprint() != graph.fingerprint:
        raise RuntimeError("Project sources/configuration changed during the Lake build")
    files, owned = set(), [name for name, owner in plan["owners"].items() if owner == shard]
    for name in owned:
        relative = Path(*name.split("."))
        build = graph.repo / graph.nodes[name]["build"]
        stem = build / "lib/lean" / relative
        for extension in (".olean", ".trace"):
            if not stem.with_suffix(extension).is_file():
                raise FileNotFoundError(f"Lake did not produce {stem.with_suffix(extension)}")
        for directory in (build / "lib/lean", build / "ir"):
            stem = directory / relative
            for path in stem.parent.glob(stem.name + ".*"):
                if path.is_symlink():
                    raise ValueError(f"Refusing a symlink in project build output: {path}")
                if path.is_file():
                    files.add(path)
    output.mkdir(parents=True, exist_ok=True)
    prefix = f"foundation-{plan['upper']}-{shard}"
    archive = output / (prefix + ".tar.gz")
    with tarfile.open(archive, "w:gz", compresslevel=1, dereference=True) as bundle:
        for path in sorted(files):
            relative = path.relative_to(graph.repo).as_posix()
            safe_destination(graph.repo, relative)
            bundle.add(path, arcname=relative, recursive=False)
    manifest = {"format": 1, "fingerprint": graph.fingerprint, "lower": plan["lower"],
                "upper": plan["upper"], "shard": shard, "shards": SHARDS,
                "owned_modules": len(owned), "file_count": len(files),
                "archive_sha256": file_sha256(archive)}
    (output / (prefix + ".manifest.json")).write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"archive": str(archive), **manifest}), flush=True)


def safe_destination(repo: Path, name: str) -> Path:
    relative = PurePosixPath(name)
    if relative.is_absolute() or ".." in relative.parts or "\\" in name:
        raise ValueError(f"Unsafe archive path: {name}")
    if not any(relative.parts[:len(root.parts)] == root.parts and len(relative.parts) > len(root.parts)
               for root in BUILD_DIRS):
        raise ValueError(f"Archive path outside project build directories: {name}")
    path = repo
    for part in relative.parts:
        path = path / part
        if path.is_symlink():
            raise ValueError(f"Refusing to restore through a symlink: {path}")
    return path


def restore_bundles(graph: ProjectGraph, directory: Path) -> None:
    archives = sorted(directory.rglob("foundation-*-*.tar.gz"))
    if not archives:
        raise FileNotFoundError(f"No foundation archives under {directory}")
    seen = set()
    for archive in archives:
        manifest_path = archive.with_name(archive.name.removesuffix(".tar.gz") + ".manifest.json")
        manifest = json.loads(manifest_path.read_text())
        if manifest.get("format") != 1 or manifest.get("fingerprint") != graph.fingerprint:
            raise ValueError(f"Foundation source/configuration mismatch: {archive}")
        if manifest.get("archive_sha256") != file_sha256(archive):
            raise ValueError(f"Foundation archive digest mismatch: {archive}")
        with tarfile.open(archive, "r:gz") as bundle:
            members = bundle.getmembers()
            if len(members) != manifest["file_count"]:
                raise ValueError(f"Foundation file count mismatch: {archive}")
            for member in members:
                destination = safe_destination(graph.repo, member.name)
                canonical = destination.relative_to(graph.repo).as_posix()
                if not member.isfile() or canonical in seen:
                    raise ValueError(f"Non-regular or duplicate archive member: {member.name}")
                seen.add(canonical)
            for member in members:
                destination = safe_destination(graph.repo, member.name)
                destination.parent.mkdir(parents=True, exist_ok=True)
                source = bundle.extractfile(member)
                with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as temporary:
                    temporary_path = Path(temporary.name)
                    try:
                        with source:
                            shutil.copyfileobj(source, temporary)
                        temporary.flush()
                        os.chmod(temporary_path, member.mode & 0o777)
                        os.utime(temporary_path, (member.mtime, member.mtime))
                        os.replace(temporary_path, destination)
                    finally:
                        temporary_path.unlink(missing_ok=True)
        print(json.dumps({"restored": archive.name, "files": len(members)}), flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lower", nargs="?", type=int)
    parser.add_argument("upper", nargs="?", type=int)
    parser.add_argument("shard", nargs="?", type=int, choices=range(SHARDS), default=0)
    parser.add_argument("--plan-only", action="store_true")
    parser.add_argument("--fingerprint", action="store_true")
    parser.add_argument("--restore", type=Path, metavar="DIR")
    parser.add_argument("--output-dir", type=Path, default=Path("prime-foundation-artifacts"))
    args = parser.parse_args()
    if (args.lower is None) != (args.upper is None):
        parser.error("lower and upper must be supplied together")
    if args.lower is not None and not 0 <= args.lower < args.upper:
        parser.error("require 0 <= lower < upper")
    if args.fingerprint and (args.lower is not None or args.restore or args.plan_only):
        parser.error("--fingerprint is a standalone operation")
    if args.lower is None and not (args.restore or args.fingerprint):
        parser.error("supply a depth range, --restore, or --fingerprint")
    repo = Path(__file__).resolve().parent.parent
    graph = ProjectGraph(repo)
    if args.fingerprint:
        print(graph.fingerprint)
        return
    if args.restore:
        restore_bundles(graph, args.restore)
    if args.lower is None:
        return
    plan = partition(graph, args.lower, args.upper)
    if args.plan_only:
        print(json.dumps(plan, indent=2))
        return
    print(json.dumps({key: value for key, value in plan.items() if key not in ("roots", "owners")}), flush=True)
    roots = plan["roots"][args.shard]
    if roots:
        subprocess.run(["lake", "--fail-fast", "build", *[f"+{name}:olean" for name in roots]],
                       cwd=repo, check=True)
    export_bundle(graph, plan, args.shard, args.output_dir)


if __name__ == "__main__":
    main()
