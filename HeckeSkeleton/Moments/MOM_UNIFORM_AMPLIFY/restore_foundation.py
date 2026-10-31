#!/usr/bin/env python3
"""Restore genuine, pinned Lake build products before an ordinary --rehash build.

The twelve exporter jobs of run 41126752041 succeeded. The later depth-260
jobs failed, so this is only a dependency-prefix cache, never proof evidence
for the current revision. Download the twelve fixed artifact IDs documented
in the workflow and check out BASE_COMMIT into a separate, clean directory.
The original exporter checks its complete source/configuration fingerprint,
archive digests, file counts and paths. No trace or hash is created or edited.

Usage: python HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/restore_foundation.py BASELINE_CHECKOUT DOWNLOADS
Always follow this with `lake --rehash build ...`; on any restore
failure, the same ordinary source build remains the required verification.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


BASE_COMMIT = "984b0de3ddf8bd9ea8051e0325765532c7c6550f"
BASE_FINGERPRINT = "6707201d5789aca4222679e9dbf24b924367c460eda132ec71296300fcfb8a40"
BUILD_DIRS = (Path(".lake/build"), Path("vendor/class-field-theory/.lake/build"))
PIN_FILES = ("lean-toolchain", "lake-manifest.json")
GROUPS = {f"foundation-{upper}-{shard}": (lower, upper, shard)
          for lower, upper in ((0, 40), (40, 100), (100, 180)) for shard in range(4)}


def run(*args: str) -> str:
    return subprocess.run(args, check=True, text=True, stdout=subprocess.PIPE).stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("downloads", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    baseline, downloads = args.baseline.resolve(), args.downloads.resolve()
    if baseline == repo or run("git", "-C", str(baseline), "rev-parse", "HEAD") != BASE_COMMIT:
        raise ValueError("Require a separate checkout at the pinned foundation commit")
    subprocess.run(["git", "-C", str(baseline), "diff", "--quiet", "HEAD", "--"], check=True)
    for name in PIN_FILES:
        if (repo / name).read_bytes() != (baseline / name).read_bytes():
            raise ValueError(f"Compiler/dependency pin changed; use the source build: {name}")
    for name in ("lakefile.toml", "vendor/class-field-theory/lakefile.toml"):
        if (repo / name).read_bytes() != (baseline / name).read_bytes():
            print(f"Configuration changed: {name}; ordinary Lake traces decide reuse.")
    for relative in BUILD_DIRS:
        if (baseline / relative).exists() or (baseline / relative).is_symlink():
            raise ValueError(f"Baseline build directory must initially be absent: {relative}")

    original = baseline / "scripts/prime_cancellation_foundation.py"
    fingerprint = run(sys.executable, str(original), "--fingerprint")
    if fingerprint != BASE_FINGERPRINT:
        raise ValueError("Pinned baseline source/configuration fingerprint mismatch")

    manifests = list(downloads.rglob("foundation-*-*.manifest.json"))
    archives = list(downloads.rglob("foundation-*-*.tar.gz"))
    manifest_names = [p.name.removesuffix(".manifest.json") for p in manifests]
    archive_names = [p.name.removesuffix(".tar.gz") for p in archives]
    if (len(manifest_names) != len(GROUPS) or set(manifest_names) != set(GROUPS)
            or len(archive_names) != len(GROUPS) or set(archive_names) != set(GROUPS)):
        raise ValueError("Require exactly the twelve successful depth-40/100/180 artifact groups")
    for manifest_path in manifests:
        manifest = json.loads(manifest_path.read_text())
        group = GROUPS[manifest_path.name.removesuffix(".manifest.json")]
        if (manifest.get("format") != 1 or manifest.get("fingerprint") != fingerprint
                or manifest.get("shards") != 4
                or tuple(manifest.get(k) for k in ("lower", "upper", "shard")) != group):
            raise ValueError(f"Unexpected foundation manifest: {manifest_path}")

    moved = 0
    try:
        # This is the unchanged script from the pinned commit, not a weaker importer.
        subprocess.run([sys.executable, str(original), "--restore", str(downloads)], check=True)
        for relative in BUILD_DIRS:
            for source in sorted((baseline / relative).rglob("*")):
                if source.is_symlink():
                    raise ValueError(f"Unexpected source symlink: {source}")
                if not source.is_file():
                    continue
                target_relative = source.relative_to(baseline)
                destination = repo
                for part in target_relative.parts:
                    destination /= part
                    if destination.is_symlink():
                        raise ValueError(f"Refusing a symlink in the destination: {destination}")
                destination.parent.mkdir(parents=True, exist_ok=True)
                # Same-filesystem transfer preserves bytes, traces and mtimes,
                # without a second full uncompressed dependency cache.
                os.replace(source, destination)
                moved += 1
    finally:
        # Both directories were absent on entry and belong to this restore only.
        # Release a partially unpacked cache before a fallback source build.
        for relative in BUILD_DIRS:
            shutil.rmtree(baseline / relative, ignore_errors=True)
    print(f"Restored {moved} files from 12 verified exporter groups at {BASE_COMMIT}.")
    print("Required next step: lake --rehash build <current targets>")


if __name__ == "__main__":
    main()
