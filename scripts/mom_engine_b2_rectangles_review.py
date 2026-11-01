#!/usr/bin/env python3
"""Compile the complete, unapproved Rectangles namespace proposal as a diagnostic.

The production source is never edited. This result is not acceptance of the
original module or its downstream closure, even when the candidate exits zero.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import tomllib

from mom_engine_b2_native_watch import (
    atomic_json, group_members, process_state, source_identity, stop_group,
)

SOURCE = Path("HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRectangles.lean")
BASE_SHA256 = "d45546114dd17f14bc535ce61226ceb4da17c45c79acc2a27734d5138b280cb5"
CANDIDATE_SHA256 = "1aa5322992c8a3540cbfac532cf0c2a828b57d18c45bc1eedd2dce2b8a90667a"
ANCHOR = b"open HeckeGeneral.Analysis.ConditionalMoments\n"
ADDITION = b"open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)\n"
IMPORTS = [
    "HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTerms",
    "HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralLocations",
    "HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalGaussScaleProduction",
]
TEMPORARY = Path("MOM_B2RectanglesNamespaceReview.lean")


def run_command(command: list[str], log: Path, group: dict,
                timeout: float | None = None) -> dict:
    started = time.monotonic()
    timed_out = False
    child = None
    handlers = {sig: signal.getsignal(sig) for sig in (signal.SIGTERM, signal.SIGINT)}
    with log.open("xb") as stream:
        try:
            child = subprocess.Popen(command, stdin=subprocess.DEVNULL,
                                     stdout=stream, stderr=subprocess.STDOUT)
            try:
                child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
        finally:
            try:
                if group_members(group, keep_self=True):
                    stop_group(group, keep_self=True)
                if child is not None:
                    child.wait(timeout=1)
            finally:
                for sig, handler in handlers.items():
                    signal.signal(sig, handler)
    raw_code = child.returncode
    return {
        "command": command,
        "raw_process_returncode": raw_code,
        "exit_code": 124 if timed_out else (raw_code if raw_code >= 0 else 128 - raw_code),
        "timed_out": timed_out,
        "wall_clock_limit_seconds": timeout,
        "elapsed_seconds": time.monotonic() - started,
    }


def main() -> int:
    repo = Path.cwd().resolve()
    evidence = repo / "mom-b2-rectangles-review"
    evidence.mkdir(exist_ok=False)
    result = {
        "diagnostic_only": True, "acceptance": False,
        "production_module_acceptance": False, "downstream_acceptance": False,
        "source_path": str(SOURCE), "source_sha256": BASE_SHA256,
        "candidate_sha256": CANDIDATE_SHA256, "candidate_bytes": 14257,
        "temporary_module": TEMPORARY.stem,
        "line_mapping": "candidate lines after original line 26 are original line + 1",
        "status": "failure", "exit_code": 1, "source_unchanged": False,
    }
    before = None
    candidate = None
    temporary_created = False
    temporary_complete = False
    group = None
    started = time.monotonic()

    def interrupted(signum: int, _frame: object) -> None:
        raise RuntimeError(f"Diagnostic interrupted by signal {signum}")

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        state = process_state(os.getpid())
        if state is None or state[2:] != (os.getpid(), os.getpid()):
            raise RuntimeError("Run this diagnostic with setsid --wait")
        group = {"pid": os.getpid(), "start_ticks": state[1]}
        before = source_identity(repo)
        atomic_json(evidence / "source-before.json", before)
        baseline = (repo / SOURCE).read_bytes()
        assert len(baseline) == 14186
        assert hashlib.sha256(baseline).hexdigest() == BASE_SHA256
        assert baseline.count(ANCHOR) == 1 and ADDITION not in baseline
        assert [line.removeprefix("import ") for line in baseline.decode().splitlines()
                if line.startswith("import ")] == IMPORTS
        candidate = baseline.replace(ANCHOR, ANCHOR + ADDITION, 1)
        assert len(candidate) == 14257 and len(ADDITION) == 71
        assert hashlib.sha256(candidate).hexdigest() == CANDIDATE_SHA256
        assert candidate.replace(ADDITION, b"", 1) == baseline
        config = tomllib.loads((repo / "lakefile.toml").read_text())
        assert config["weakLeanArgs"] == ["-j2"]
        assert config["leanOptions"]["autoImplicit"] is False
        assert config["leanOptions"]["relaxedAutoImplicit"] is False
        assert (repo / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc3"
        if (repo / TEMPORARY).exists():
            raise RuntimeError("Refusing to replace an existing temporary module")
        (evidence / "candidate.lean").write_bytes(candidate)
        result["original_prints"] = [line for line in baseline.decode().splitlines()
                                     if line.startswith("#print axioms ")]
        assert len(result["original_prints"]) == 4

        result["toolchain"] = run_command(
            ["lake", "env", "lean", "--version"], evidence / "toolchain.log", group)
        version = (evidence / "toolchain.log").read_text()
        if (result["toolchain"]["exit_code"] != 0 or "4.35.0-rc3" not in version
                or "470d5ce1400764999581fd26d5d72b00d990b0f4" not in version):
            raise RuntimeError(f"Unexpected Lean compiler: {version}")
        result["mathlib"] = run_command(
            ["git", "-C", str(repo / ".lake/packages/mathlib"), "rev-parse", "HEAD"],
            evidence / "mathlib.log", group)
        mathlib = (evidence / "mathlib.log").read_text().strip()
        if (result["mathlib"]["exit_code"] != 0
                or mathlib != "0493595ecd5da8ef14742febab99728f98e948e8"):
            raise RuntimeError(f"Unexpected mathlib revision: {mathlib}")

        dependencies = ["lake", "build", *["+" + name + ":olean" for name in IMPORTS]]
        result["dependencies"] = run_command(dependencies, evidence / "dependencies.log", group)
        atomic_json(evidence / "result.json", result)
        if result["dependencies"]["exit_code"] != 0:
            result["status"] = "dependencies-failed"
            result["exit_code"] = result["dependencies"]["exit_code"]
        else:
            assert (repo / SOURCE).read_bytes() == baseline
            with (repo / TEMPORARY).open("xb") as stream:
                temporary_created = True
                stream.write(candidate)
            temporary_complete = True
            command = ["lake", "env", "lean", "-j2", "-DautoImplicit=false",
                       "-DrelaxedAutoImplicit=false", str(TEMPORARY)]
            result["candidate"] = run_command(
                command, evidence / "candidate.log", group, timeout=300)
            result["exit_code"] = result["candidate"]["exit_code"]
            result["status"] = ("candidate-compiled-diagnostic-only"
                                if result["exit_code"] == 0 else "candidate-not-compiled")
    except BaseException as error:
        result.update(status="failure", exit_code=1,
                      error=f"{type(error).__name__}: {error}")
    finally:
        try:
            if group is not None and group_members(group, keep_self=True):
                stop_group(group, keep_self=True)
            if temporary_created:
                if temporary_complete and (repo / TEMPORARY).read_bytes() != candidate:
                    raise RuntimeError("Temporary candidate changed unexpectedly")
                (repo / TEMPORARY).unlink()
            result["temporary_removed"] = not (repo / TEMPORARY).exists()
            after = source_identity(repo)
            atomic_json(evidence / "source-after.json", after)
            result["source_unchanged"] = before is not None and before == after
            if not result["source_unchanged"] or not result["temporary_removed"]:
                raise RuntimeError("Source identity or temporary cleanup check failed")
        except BaseException as error:
            result.update(status="failure", exit_code=1,
                          cleanup_error=f"{type(error).__name__}: {error}")
        result["elapsed_seconds"] = time.monotonic() - started
        atomic_json(evidence / "result.json", result)
    print(json.dumps(result, ensure_ascii=False, indent=2), flush=True)
    return int(result["exit_code"])


if __name__ == "__main__":
    raise SystemExit(main())
