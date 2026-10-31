#!/usr/bin/env python3
"""Optional exact-source native prerequisites for the original skeleton audit.

The producer's complete source/configuration fingerprint must match its pinned
manifest. A current module is eligible only when its source and every project
dependency are unchanged. Missing/changed sources and all reverse dependents
are excluded. Thus AllIdealTransfer and its affected consumers are rebuilt.

Only fixed successful producer archives are used. Each archive is completely
authenticated in isolation before its selected native files are published,
with Lake traces last. A missing archive leaves the ordinary Lake build to
compile those modules. Detailed source/object records are written only to the
requested CI artifact report; this script never performs a proof build.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile

import bootstrap as common

TARGET = "HeckeSkeleton.Moments"
FACTORS = (1.05, 1.15, 1.25, 1.5, 2.0, 3.0)

# Fixed successful native artifacts from the pinned producer run.
# id, upper depth, shard, owned modules, file count, ZIP bytes, expanded bytes,
# archive SHA256, canonical manifest SHA256, ZIP SHA256, recorded expiration.
BUNDLE_PINS = [
    (13012376359, 40, 0, 817, 7992, 290750533, 4214065847,
     'eeaae4ba35ea0b43578e132afdd904caef3fb7010baa8a3ad963b7e96bcb768e',
     'e11ad340a387cd3767e3a7fe27621e09951cf6e72e8e86621bf20d719942e511',
     '6c48a54613d0064719d04bf4d4ad6d0491b39b98251bc3808961c0c6afde1324', '2026-11-06T21:10:03Z'),
    (13011719707, 40, 1, 769, 12224, 284075649, 3456718495,
     '4efd5cfae24809b98675993cd5544dfe6caf7d0ffb8d823f22a64f79c8102a8d',
     'c499294fbf5afc8218eca3aa69fbe14c02d0ff4ef6e6798312dc1c853842a34e',
     '7620df2fdd8bc50d9ae6f43bd14d18732a2fd2cd9c52de010b99e59701975f82', '2026-11-06T21:23:20Z'),
    (13011754956, 40, 2, 706, 11288, 170594766, 1815749298,
     '6d65e704af89126677dfe1dc1142f0e47fdb1f6f07ab7fea3ae5f632d4058c7a',
     '546073802003a3ae84b8864234f34acb3a7a6cd4dce0e8f87e8d7e01acf9a6a3',
     'b01697611b3584fa210abd61876a3ccb1e6122a3c217fe55e1a283300aebaf88', '2026-11-06T21:32:01Z'),
    (13013018508, 40, 3, 364, 5816, 89080866, 1410837818,
     '30d2e905cb617a50757b884176ecac1f4adc920cc25141efd104964b4318fa64',
     '2cb9d33bf65ed4141a33eeb372340b1466caeb259e44fb2da0638393d4e36bb6',
     '29fb1b025d9226a3d8bebb4849443770b04d90c0a4efeb6a406c6cf0c2d9968b', '2026-11-06T21:35:40Z'),
    (13017749400, 100, 0, 334, 5328, 116744342, 1260761914,
     '0fb746e74ef721d8167905d35361d87ffee0a563bf807405ed729c8a1dec6d43',
     '549f1b846bff90fb10fc40bfe6872e19b0188a0de1e91b800c50a2f7118b2ca2',
     '384365645f5c02dacf5f8d05bfa4eb6211a2ab5ca9afddcefb39df51b63750be', '2026-11-06T22:54:39Z'),
    (13018611868, 100, 1, 90, 1208, 29083644, 477762762,
     '1b4ac7498c77c8f84f05390429c1b20539f32585ab5b1350e0a7c5b4f7c9f780',
     '1153763ad5572b678d8320a1cebf14215db1c9b1fa6644e662f84ab877a0d6a7',
     '57dfd63d075039e0c150635df09c534bfdf8060b88f8602457b2c271f8079fc1', '2026-11-06T22:43:12Z'),
    (13018074066, 100, 2, 74, 1120, 21358487, 314276858,
     'f422c5449fc4ee1732a86ce815954f5161816d11cda1c87bce2e540693a7d27b',
     'bcc70397e478e524d8f649b7ba3bdd5a123a05e63855ddac3a3579d42be51e34',
     'aa98e4d6970f2350fcd65f8be16fd66fbf069799813a40f682524b7c9e3d82c0', '2026-11-06T22:54:37Z'),
    (13015618946, 100, 3, 135, 2144, 29358074, 455314810,
     'd53889d14a536536028254ecbeb445f193e6afd41eff716f4cedcd3edfe9b1cc',
     '8b70509f572ba6c9b96f3f879706f9367cac8544ca0247b76f79760d45626c2f',
     '9ad599dfa01ff6e197493379480f2d7a62228e783a183e00e3f28841f7cb2f6d', '2026-11-06T22:13:59Z'),
    (13021712535, 180, 0, 595, 9504, 294553470, 4395458117,
     '60234f15f055d6dabff28edb8b10069a2f4bf9fc8ab5d0aac864905efaf51bbf',
     '8c1c8ad8813c3a6699e54cda3ab1bb5ca8b8e5dd2a98a4e72aabae7a0d3c9b2a',
     '5e5137138741b9932002167dd64de9f71e6ee336de1ad47fe14ead193400d18b', '2026-11-06T23:59:28Z'),
    (13021514563, 180, 1, 78, 1040, 43570758, 692459555,
     '263454fb7a76f21cc7b333d6e82a31f37875c70330afb8468a5444bbb391abcd',
     '2449c9142b5fa33a382b7e64ab51a52b994fb3f10794cdd93225c7fce5360fc1',
     '14bb73f02e0f2631ca4bf4595cda97f0f90e615ab52cf71b340923fb37036e0f', '2026-11-07T00:14:26Z'),
]


def bundles():
    result = []
    for (artifact_id, upper, shard, owned, count, compressed, expanded,
         archive_hash, manifest_hash, zip_hash, expiry) in BUNDLE_PINS:
        lower = {40: 0, 100: 40, 180: 100}[upper]
        stem = f"foundation-{upper}-{shard}"
        manifest = {"format": 1, "fingerprint": common.PRODUCER["source_fingerprint"],
                    "lower": lower, "upper": upper, "shard": shard, "shards": 4,
                    "owned_modules": owned, "file_count": count, "archive_sha256": archive_hash}
        if common.canonical_hash(manifest) != manifest_hash:
            raise ValueError(f"Pinned artifact manifest metadata differs: {artifact_id}")
        result.append({"artifact_id": artifact_id, "artifact_name": "prime-" + stem,
                       "artifact_size_bytes": compressed, "unpacked_size_bytes": expanded,
                       "archive_name": stem + ".tar.gz", "archive_sha256": archive_hash,
                       "manifest_name": stem + ".manifest.json", "manifest": manifest,
                       "canonical_manifest_sha256": manifest_hash,
                       "artifact_zip_sha256": zip_hash, "expires_at": expiry})
    return result


def project_dependencies(repo, rows):
    return {name: [dependency for dependency in common.header_imports(
                      (repo / row["source"]).read_text(encoding="utf-8-sig"))
                   if dependency in rows]
            for name, row in rows.items()}


def producer_owners(rows, dependencies, lower, upper):
    """Reproduce the pinned producer's deterministic four-owner partition."""
    depth = {}
    # project_graph inserts a node only after visiting all of its dependencies.
    for name in rows:
        depth[name] = 1 + max((depth[d] for d in dependencies[name]), default=0)
    names = sorted(rows, key=lambda name: (depth[name], name))
    index = {name: i for i, name in enumerate(names)}
    closure, children = {}, {name: [] for name in names}
    for name in names:
        bits = 1 << index[name]
        for dependency in dependencies[name]:
            bits |= closure[dependency]
            children[dependency].append(name)
        closure[name] = bits
    base = sum(1 << index[name] for name in names if depth[name] <= lower)
    selected = [name for name in names if lower < depth[name] <= upper]
    targets = [name for name in selected
               if not any(depth[child] <= upper for child in children[name])]
    targets.sort(key=lambda name: (closure[name] & ~base).bit_count(), reverse=True)
    alternatives = []
    for factor in FACTORS:
        parts, counts = [0] * 4, [0] * 4
        cap = len(selected) / 4 * factor
        for name in targets:
            required = closure[name] & ~base
            added = [(required & ~part).bit_count() for part in parts]
            if min(added) == 0:
                continue
            fitting = [i for i in range(4) if counts[i] + added[i] <= cap]
            if fitting:
                shard = min(fitting, key=lambda i: (added[i], counts[i], i))
            else:
                shard = min(range(4), key=lambda i: (counts[i] + added[i], added[i], i))
            parts[shard] |= required
            counts[shard] = parts[shard].bit_count()
        alternatives.append((max(counts), sum(counts), factor, parts))
    parts = min(alternatives, key=lambda item: item[:3])[3]
    return {name: min(i for i, part in enumerate(parts) if part & (1 << index[name]))
            for name in selected}


def derive_source_plan(repo, producer):
    previous = common.project_graph(producer, TARGET)
    configuration = {name: common.file_hash(producer / name) for name in common.CONFIG_FILES}
    fingerprint = common.canonical_hash({"modules": {name: row["source_sha256"]
                                                     for name, row in previous.items()},
                                         "config": configuration})
    if fingerprint != common.PRODUCER["source_fingerprint"]:
        raise ValueError("Producer sources/configuration differ from the native manifest")
    if any(common.file_hash(repo / name) != digest for name, digest in configuration.items()):
        raise ValueError("Current compiler/package configuration differs from the producer")
    current = common.project_graph(repo, TARGET)
    old_dependencies = project_dependencies(producer, previous)
    dependencies = project_dependencies(repo, current)
    eligible = {name for name, row in current.items() if row == previous.get(name)}
    pruned = {name: "missing or changed producer source" for name in current if name not in eligible}
    while True:
        removed = {}
        for name in eligible:
            affected = (set(dependencies[name]) | set(old_dependencies[name])) - eligible
            if affected:
                removed[name] = "depends on excluded sources: " + ", ".join(sorted(affected))
        if not removed:
            break
        eligible.difference_update(removed)
        pruned.update(removed)
    ownership = {}
    for lower, upper in ((0, 40), (40, 100), (100, 180)):
        ownership[upper] = producer_owners(previous, old_dependencies, lower, upper)
    groups = []
    for artifact in bundles():
        manifest = artifact["manifest"]
        owned = {name for name, owner in ownership[manifest["upper"]].items()
                 if owner == manifest["shard"]}
        if len(owned) != manifest["owned_modules"]:
            raise ValueError(f"Producer owner coverage differs: {artifact['artifact_name']}")
        safe = owned & eligible
        selected = {}
        for name in sorted(safe):
            row = current[name]
            stem = repo / row["build"] / "lib/lean" / name.replace(".", "/")
            # Existing cache entries are left for normal Lake trace validation.
            if not all(stem.with_suffix(suffix).is_file() for suffix in (".olean", ".trace")):
                selected[name] = row
        groups.append({"artifact": artifact, "safe_modules": sorted(safe), "modules": selected})
    return {"current": current, "configuration": configuration, "pruned": pruned,
            "eligible": sorted(eligible), "groups": groups}


def source_plan(repo, producer):
    revision = subprocess.check_output(["git", "-C", str(producer), "rev-parse", "HEAD"],
                                       text=True).strip()
    if revision != common.PRODUCER["producer_commit"]:
        raise ValueError("The producer source checkout is not the pinned commit")
    return derive_source_plan(repo, producer)


def recheck_current(repo, state):
    for name, digest in state["configuration"].items():
        if common.file_hash(repo / name) != digest:
            raise ValueError(f"Configuration changed during native restoration: {name}")
    for name, row in state["current"].items():
        if common.file_hash(repo / row["source"]) != row["source_sha256"]:
            raise ValueError(f"Source changed during native restoration: {name}")


def restore_one(repo, directory, group, state):
    artifact, modules = group["artifact"], group["modules"]
    if shutil.disk_usage(repo).free < artifact["unpacked_size_bytes"] + 512 * 1024 ** 2:
        raise ValueError(f"Insufficient isolated staging space for {artifact['artifact_name']}")
    catalog = {**common.PRODUCER, "artifact": artifact, "modules": modules}
    with tempfile.TemporaryDirectory(prefix=".mom-inv-original-bootstrap-", dir=repo) as temporary:
        staging = Path(temporary)
        files = common.verify_download(directory / artifact["artifact_name"], catalog, staging)
        recheck_current(repo, state)
        for row in files:
            common.safe_path(repo, row["path"])
        for row in sorted(files, key=lambda row: row["path"].endswith(".trace")):
            destination = common.safe_path(repo, row["path"])
            destination.parent.mkdir(parents=True, exist_ok=True)
            os.replace(staging / row["path"], destination)
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("need", "plan", "restore"))
    parser.add_argument("directory", nargs="?", type=Path)
    parser.add_argument("--producer-source", type=Path)
    parser.add_argument("--optional", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.action != "need" and args.producer_source is None:
        parser.error("plan/restore require --producer-source")
    if args.action == "restore" and args.directory is None:
        parser.error("restore requires the downloaded artifact directory")
    report = {"operation": args.action, "status": "unavailable", "needed": False,
              "artifact_ids": "", "producer_run": common.PRODUCER["run_id"]}
    try:
        if args.action == "need":
            stem = common.REPO / ".lake/build/lib/lean" / TARGET.replace(".", "/")
            report.update(status="planned", needed=not all(stem.with_suffix(suffix).is_file()
                          for suffix in (".olean", ".trace")))
        else:
            state = source_plan(common.REPO, args.producer_source)
            now = datetime.now(timezone.utc)
            groups = [group for group in state["groups"] if group["modules"]
                      and now < datetime.fromisoformat(group["artifact"]["expires_at"].replace("Z", "+00:00"))]
            report.update(status="planned", source_modules=len(state["current"]),
                          eligible_modules=len(state["eligible"]), pruned=state["pruned"],
                          sources=state["current"], configuration=state["configuration"],
                          needed=bool(groups),
                          artifact_ids=",".join(str(group["artifact"]["artifact_id"]) for group in groups),
                          selected_modules=sum(len(group["modules"]) for group in groups))
            if args.action == "restore":
                report["environment"] = common.checked_environment(common.REPO, common.PRODUCER)
                report["restored"], report["unavailable"] = [], []
                for group in groups:
                    try:
                        files = restore_one(common.REPO, args.directory, group, state)
                        row = {"artifact": group["artifact"]["artifact_id"],
                               "source_modules": len(group["modules"]), "files": files}
                        report["restored"].append(row)
                        print(f"Restored {len(files)} authenticated files for {len(group['modules'])} unchanged modules", flush=True)
                    except (OSError, ValueError, KeyError, tarfile.TarError) as error:
                        if not args.optional:
                            raise
                        report["unavailable"].append({"artifact": group["artifact"]["artifact_id"], "reason": str(error)})
                        print(f"::notice::Optional archive unavailable: {error}; ordinary Lake will compile its missing modules", flush=True)
                report["status"] = "partial" if report["unavailable"] else "restored"
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError, tarfile.TarError) as error:
        report.update(status="unavailable", needed=False, artifact_ids="", reason=str(error))
        if not args.optional:
            raise
        print(f"::notice::Optional original-target bootstrap unavailable: {error}. Ordinary Lake compilation follows.")
    finally:
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2) + "\n")
        if args.action in ("need", "plan") and os.environ.get("GITHUB_OUTPUT"):
            with open(os.environ["GITHUB_OUTPUT"], "a") as output:
                output.write(f"needed={str(report['needed']).lower()}\nartifact_ids={report['artifact_ids']}\n")
    excluded = {"sources", "configuration", "pruned", "restored", "environment"}
    print(json.dumps({key: value for key, value in report.items() if key not in excluded}))


if __name__ == "__main__":
    main()
