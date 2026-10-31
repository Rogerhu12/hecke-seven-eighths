"""In-memory scheduler regression tests; these are not Lean proof evidence.

No Lean process is run. All Fixture.* source bytes, compiled artifacts, and
verification records live in a virtual filesystem, never in repository caches.
"""
from __future__ import annotations

from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import low_energy_verify as verifier


class MemoryPath:
    """The path operations needed by the verifier, backed only by memory."""

    files: dict[str, bytes] = {}

    def __init__(self, *parts):
        self.path = PurePosixPath(*(str(part) for part in parts))

    def __str__(self):
        return str(self.path)

    def __truediv__(self, part):
        return type(self)(self.path / str(part))

    @property
    def name(self):
        return self.path.name

    @property
    def parent(self):
        return type(self)(self.path.parent)

    def relative_to(self, path):
        return type(self)(self.path.relative_to(str(path)))

    def with_name(self, name):
        return type(self)(self.path.with_name(name))

    def with_suffix(self, suffix):
        return type(self)(self.path.with_suffix(suffix))

    def is_absolute(self):
        return self.path.is_absolute()

    def is_file(self):
        return str(self) in self.files

    def mkdir(self, **kwargs):
        pass

    def read_bytes(self):
        return self.files[str(self)]

    def read_text(self):
        return self.read_bytes().decode()

    def write_text(self, text):
        self.files[str(self)] = text.encode()
        return len(text)

    def unlink(self, missing_ok=False):
        if not missing_ok and str(self) not in self.files:
            raise FileNotFoundError(str(self))
        self.files.pop(str(self), None)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


class SchedulerTests(unittest.TestCase):
    MODULE_NAMES = (
        "Fail", "Blocked", "Exact", "ExactChild", "SourceChanged",
        "OutputChanged", "DependencyChanged", "LogChanged", "BadAxioms", "Cold",
    )
    DEPENDENCIES = {
        "Blocked": ["Fail"],
        "ExactChild": ["Exact"],
        "DependencyChanged": ["Exact"],
    }
    NEW_SOURCE_NAMES = {"Exact", "ExactChild", "BadAxioms"}
    VERSION = "FIXTURE ONLY (version 4.35.0-rc3, no compiler executed)"
    FLAGS = ["-j1", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]

    def setUp(self):
        # Give every test a fresh virtual filesystem and restore it afterwards.
        filesystem_patch = patch.object(MemoryPath, "files", {})
        filesystem_patch.start()
        self.addCleanup(filesystem_patch.stop)
        self.root = MemoryPath("/MEMORY_FIXTURE_ONLY")
        self.out = self.root / "out"
        self.log = self.root / "records"
        self.seed_fixture()
        self.preserved_outputs = {
            name: self.output_path(name).read_bytes()
            for name in ("Exact", "ExactChild")
        }
        self.run_verifier()

    def source_path(self, name):
        return self.root / "Fixture" / (name + ".lean")

    def output_path(self, name):
        return self.out / "Fixture" / (name + ".olean")

    def output_hashes(self, name):
        return {".olean": sha256(self.output_path(name).read_bytes())}

    def seed_fixture(self):
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0-rc3\n")
        lock = self.root / "lake-manifest.json"
        lock.write_text(json.dumps({
            "packages": [{"name": "mathlib", "rev": verifier.MATHLIB_REV}],
        }))
        (self.root / "docs/low-energy/source_manifest.json").write_text(json.dumps({
            "files": [
                {"path": "Fixture/" + name + ".lean"}
                for name in sorted(self.NEW_SOURCE_NAMES)
            ],
        }))
        for name in self.MODULE_NAMES:
            imports = "".join(
                "import Fixture." + dependency + "\n"
                for dependency in self.DEPENDENCIES.get(name, [])
            )
            self.source_path(name).write_text(imports + "def fixture_marker : Nat := 0\n")
            if name != "Cold":
                self.output_path(name).write_text("IN-MEMORY FIXTURE " + name)

        for name in self.MODULE_NAMES:
            if name in {"Fail", "Cold"}:
                continue
            output = ""
            if name in self.NEW_SOURCE_NAMES:
                axiom = "Fixture.untrusted_assumption" if name == "BadAxioms" else "propext"
                output = f"'Fixture.{name}.checked' depends on axioms: [{axiom}]\n"
            (self.log / ("Fixture." + name + ".log")).write_text(output)
            record = {
                "fixture_only": True,
                "module": "Fixture." + name,
                "cache_schema": verifier.CACHE_SCHEMA,
                "source_sha256": sha256(self.source_path(name).read_bytes()),
                "exit_code": 0,
                "audit_ok": True,
                "lean": self.VERSION,
                "flags": self.FLAGS,
                "mathlib": verifier.MATHLIB_REV,
                "package_lock_sha256": sha256(lock.read_bytes()),
                "new_source": name in self.NEW_SOURCE_NAMES,
                "local_dependency_artifact_hashes": {
                    "Fixture." + dependency: self.output_hashes(dependency)
                    for dependency in self.DEPENDENCIES.get(name, [])
                },
                "output_artifact_hashes": self.output_hashes(name),
                "log_sha256": sha256(output.encode()),
            }
            if name == "DependencyChanged":
                record["local_dependency_artifact_hashes"]["Fixture.Exact"][".olean"] = (
                    "stale dependency"
                )
            (self.log / ("Fixture." + name + ".json")).write_text(json.dumps(record))

        # Tamper only after recording the original hashes, so each cache is stale.
        self.source_path("SourceChanged").write_text("def fixture_changed : Nat := 1\n")
        self.output_path("OutputChanged").write_text("changed fixture output")
        (self.log / "Fixture.LogChanged.log").write_text("changed fixture output log\n")

    def run_verifier(self):
        clock_calls = 0

        def clock():
            nonlocal clock_calls
            clock_calls += 1
            # Start/end the failed build and set its deadline at time zero.
            # All later observations are beyond the 600-second diagnostic budget.
            return 0.0 if clock_calls <= 3 else 601.0

        def fake_compiler(command, **kwargs):
            self.assertEqual(command[-1], str(self.source_path("Fail")),
                             "Compiler work was scheduled after the deadline")
            return subprocess.CompletedProcess(
                command, 1, stdout="error: deliberate in-memory fixture failure\n",
            )

        arguments = ["verifier-fixture", "actual", "--direct-env", "--diagnostic-seconds", "600"]
        for name in self.MODULE_NAMES:
            arguments += ["--target", "Fixture." + name]
        printed = io.StringIO()
        with patch.multiple(
            verifier, Path=MemoryPath, ROOT=self.root, OUT=self.out, LOG=self.log,
            SOURCE_ROOTS=[self.root],
        ), patch.object(
            verifier.subprocess, "check_output", return_value=self.VERSION,
        ) as version_check, patch.object(
            verifier.subprocess, "run", side_effect=fake_compiler,
        ) as compiler, patch.object(
            verifier.time, "monotonic", side_effect=clock,
        ), patch.dict(
            os.environ, {"LEAN_PATH": str(self.out)},
        ), patch.object(sys, "argv", arguments), redirect_stdout(printed):
            self.exit_code = verifier.main()

        self.compiler = compiler
        self.version_check = version_check
        self.printed = printed.getvalue()
        self.records = {
            record["module"]: record
            for record in json.loads((self.log / "actual.json").read_text())
        }
        self.diagnostics = json.loads((self.log / "actual_diagnostics.json").read_text())

    def assert_exact_cache_preserved(self, name):
        record = self.records["Fixture." + name]
        self.assertTrue(self.diagnostics["budget_exhausted"])
        self.assertTrue(record["reused_exact_cache"])
        self.assertTrue(record["audit_ok"])
        self.assertEqual(self.output_path(name).read_bytes(), self.preserved_outputs[name])

    def assert_budget_skip(self, name):
        record = self.records["Fixture." + name]
        self.assertEqual(record["skip_reason"], "diagnostic_budget_exhausted")
        self.assertFalse(record["audit_ok"])
        self.assertEqual(record["output_artifact_hashes"], {})
        self.assertFalse(self.output_path(name).is_file())

    def test_expired_exact_cache_is_preserved(self):
        self.assert_exact_cache_preserved("Exact")

    def test_expired_exact_cached_child_is_preserved(self):
        self.assert_exact_cache_preserved("ExactChild")

    def test_failed_dependency_is_rejected_before_cache_or_budget_checks(self):
        record = self.records["Fixture.Blocked"]
        self.assertEqual(record["skip_reason"], "failed_or_skipped_dependency")
        self.assertEqual(record["blocked_dependencies"], ["Fixture.Fail"])
        self.assertFalse(record["audit_ok"])
        self.assertEqual(record["output_artifact_hashes"], {})
        self.assertFalse(self.output_path("Blocked").is_file())

    def test_changed_source_cache_is_rejected(self):
        self.assert_budget_skip("SourceChanged")

    def test_changed_output_cache_is_rejected(self):
        self.assert_budget_skip("OutputChanged")

    def test_changed_dependency_hash_cache_is_rejected(self):
        self.assert_budget_skip("DependencyChanged")

    def test_changed_log_cache_is_rejected(self):
        self.assert_budget_skip("LogChanged")

    def test_disallowed_printed_axiom_cache_is_rejected(self):
        self.assert_budget_skip("BadAxioms")

    def test_cold_compilation_is_not_started_after_expiry(self):
        self.assert_budget_skip("Cold")
        self.compiler.assert_called_once()
        self.assertEqual(self.compiler.call_args.args[0][-1], str(self.source_path("Fail")))

    def test_failure_status_is_retained_and_final_axiom_gate_is_not_run(self):
        self.assertEqual(self.exit_code, 1)
        self.assertFalse(self.records["Fixture.Fail"]["audit_ok"])
        self.assertFalse(self.output_path("Fail").is_file())
        self.assertEqual(len(self.records), len(self.MODULE_NAMES))
        self.compiler.assert_called_once()
        self.version_check.assert_called_once()
        self.assertEqual(self.version_check.call_args.args[0], ["lean", "--version"])
        self.assertEqual(self.diagnostics["final_axiom_gate"],
                         "not_run_due_to_failed_or_skipped_modules")
        self.assertEqual(self.diagnostics["failed_modules"], [
            {"module": "Fixture.Fail", "exit_code": 1, "reason": "compiler_error"},
        ])
        self.assertEqual(len(self.diagnostics["skipped_modules"]), 7)
        self.assertNotIn("AXIOM GATE", self.printed)


if __name__ == "__main__":
    unittest.main()
