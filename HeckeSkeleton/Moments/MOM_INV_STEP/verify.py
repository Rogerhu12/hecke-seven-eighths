#!/usr/bin/env python3
"""Run normal Lake builds and retain compiler/recursive-axiom evidence.

The workflow restores the repository's published Lake cache before this
script. Lake alone decides which objects to rebuild. This script does not
maintain another cache, checkpoint, import scheduler, or object database.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
LOGS = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "mom-inv-step-verification"
TARGETS = sys.argv[1:] or [
    "HeckeSkeleton.Moments.MOM_INV_STEP.SpectralAudit",
    "HeckeSkeleton.Moments.MOM_INV_STEP.CoreAudit",
    "HeckeSkeleton.Moments.MOM_INV_STEP.Audit",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_LEAN = "4.35.0-rc3"
EXPECTED_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
EXPECTED_MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
LOGS.mkdir(parents=True, exist_ok=True)


def checked(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def run_logged(command: list[str], name: str) -> tuple[int, str]:
    print("$ " + " ".join(command), flush=True)
    chunks = []
    with (LOGS / name).open("w") as log:
        log.write("$ " + " ".join(command) + "\n")
        log.flush()
        with subprocess.Popen(command, cwd=ROOT, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              bufsize=1) as process:
            assert process.stdout is not None
            for line in process.stdout:
                chunks.append(line)
                log.write(line)
                log.flush()
                print(line, end="", flush=True)
            code = process.wait()
        log.write(f"\nExit code: {code}\n")
    return code, "".join(chunks)


version = checked("lake", "env", "lean", "--version")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
configured_mathlib = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
actual_mathlib = checked("git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
environment = {
    "lean": version,
    "mathlib_configured": configured_mathlib,
    "mathlib_checked_out": actual_mathlib,
    "git_head": checked("git", "rev-parse", "HEAD"),
    "targets": TARGETS,
}
(LOGS / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
if EXPECTED_LEAN not in version or EXPECTED_COMMIT not in version:
    raise SystemExit(f"Unexpected Lean version: {version}")
if configured_mathlib != EXPECTED_MATHLIB or actual_mathlib != EXPECTED_MATHLIB:
    raise SystemExit("Unexpected Mathlib revision")

build_code, build_output = run_logged(["lake", "build", *TARGETS], "lake-build.log")
errors = [] if build_code == 0 else [f"lake build exited {build_code}"]
errors.extend(
    line.strip()
    for line in build_output.splitlines()
    if "warning: HeckeSkeleton/Moments/MOM_INV_STEP/" in line
    and "declaration uses `sorry`" in line
)
all_axioms = {}
for target in TARGETS:
    if not target.endswith("Audit"):
        continue
    if not re.fullmatch(r"HeckeSkeleton\.Moments\.MOM_INV_STEP\.\w+", target):
        errors.append(f"Unexpected audit target: {target}")
        continue
    source = ROOT.joinpath(*target.split(".")).with_suffix(".lean")
    expected = set(re.findall(r"^#print axioms (\S+)", source.read_text(), re.M))
    if not expected:
        errors.append(f"{target}: empty axiom audit")
        continue
    code, output = run_logged(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         str(source.relative_to(ROOT))],
        target + ".log",
    )
    if code:
        errors.append(f"{target}: audit elaboration exited {code}")
        continue
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    records = dict(re.findall(pattern, output, re.S))
    missing = expected - records.keys()
    if missing:
        errors.append(f"{target}: missing kernel records {sorted(missing)}")
    for name in sorted(expected & records.keys()):
        axioms = {x.strip() for x in records[name].split(",") if x.strip()}
        all_axioms[name] = sorted(axioms)
        if axioms - ALLOWED:
            errors.append(f"{name}: unexpected axioms {sorted(axioms - ALLOWED)}")
    if not missing and all(not (set(all_axioms[n]) - ALLOWED) for n in expected):
        print(f"PASS: {target}: {len(expected)} recursive axiom checks", flush=True)

(LOGS / "axioms.json").write_text(json.dumps(all_axioms, indent=2) + "\n")
(LOGS / "result.json").write_text(json.dumps({
    "lake_build_exit_code": build_code,
    "allowed_axioms": sorted(ALLOWED),
    "audited_declarations": len(all_axioms),
    "errors": errors,
}, indent=2) + "\n")
if errors:
    print("\n".join(errors), flush=True)
    raise SystemExit(1)
print("PASS: normal Lake build and recursive kernel axiom audit", flush=True)
