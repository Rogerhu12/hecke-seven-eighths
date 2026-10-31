"""Native-receipt regression tests using synthetic, non-proof fixtures.

No Lean or Lake process is run. Sources, logs, and deliberately non-Lean artifact
bytes exist only in a disposable temporary directory. Passing these tests is
not Lean proof evidence and does not validate a real native build.
"""
from __future__ import annotations

from contextlib import contextmanager
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import low_energy_verify as verifier


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class NativeReceiptTests(unittest.TestCase):
    MODULE = "Fixture.Native"
    DEPENDENCY = "Fixture.Dependency"
    SOURCE = "Fixture/Native.lean"
    VERSION = "FIXTURE ONLY (version 4.35.0-rc3, no compiler executed)"
    RUNTIME_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
    CONFIG_CONTENTS = {
        "lean-toolchain": "leanprover/lean4:v4.35.0-rc3\n",
        "lake-manifest.json": '{"fixture_only": true, "packages": []}\n',
        "lakefile.toml": 'name = "synthetic-receipt-fixture"\n',
        "vendor/class-field-theory/lakefile.toml": 'name = "synthetic-dependency-fixture"\n',
    }

    def setUp(self):
        self.root = Path(self.enterContext(TemporaryDirectory(prefix="native-receipt-test-")))
        self.out = self.root / "outputs"
        self.log = self.root / "records"
        self.log.mkdir()
        self.enterContext(patch.multiple(
            verifier, ROOT=self.root, OUT=self.out, LOG=self.log, SOURCE_ROOTS=[self.root],
        ))
        for name in ("run", "check_output", "Popen"):
            blocked = self.enterContext(patch.object(
                verifier.subprocess, name,
                side_effect=AssertionError("No external process is allowed in native-receipt tests"),
            ))
            self.addCleanup(blocked.assert_not_called)

        for relative, contents in self.CONFIG_CONTENTS.items():
            self.write_file(relative, contents.encode())
        self.write_file(self.SOURCE, (
            "-- SYNTHETIC FIXTURE ONLY: not Lean proof evidence.\n"
            "import Fixture.Dependency\n"
            "def fixtureMarker : Nat := 0\n"
        ).encode())
        self.write_file("Fixture/Dependency.lean", (
            "-- SYNTHETIC FIXTURE ONLY: not Lean proof evidence.\n"
            "def dependencyMarker : Nat := 0\n"
        ).encode())
        for module in (self.MODULE, self.DEPENDENCY):
            for suffix in self.RUNTIME_SUFFIXES:
                path = self.artifact_path(module, suffix)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(f"SYNTHETIC NON-LEAN ARTIFACT: {module}{suffix}\n".encode())

        config_hashes = {relative: sha256(self.root / relative) for relative in self.CONFIG_CONTENTS}
        self.catalog = {
            "fixture_only": True,
            "not_lean_proof_evidence": True,
            "schema": "native-lake-foundation-catalog-v1",
            "toolchain": "leanprover/lean4:v4.35.0-rc3",
            "lean": self.VERSION,
            "mathlib": verifier.MATHLIB_REV,
            "config_sha256": deepcopy(config_hashes),
            "artifacts": {"12345": {"name": "synthetic-non-lean-fixture", "fixture_only": True}},
            "modules": {
                module: self.catalog_entry(module, relative)
                for module, relative in (
                    (self.MODULE, self.SOURCE), (self.DEPENDENCY, "Fixture/Dependency.lean"),
                )
            },
        }
        self.catalog_path = self.write_file(
            "docs/low-energy/native_foundation_catalog.json", json.dumps(self.catalog).encode(),
        )
        self.enterContext(patch.object(verifier, "NATIVE_CATALOG_SHA256", sha256(self.catalog_path)))
        self.validation_log = self.log / "native_foundation_validation.log"
        self.validation_log.write_text(
            "SYNTHETIC VALIDATION LOG: no Lean or Lake process ran; not proof evidence.\n"
        )
        self.receipt = {
            "fixture_only": True,
            "not_lean_proof_evidence": True,
            "schema": "native-lake-foundation-v1",
            "status": "validated_native_dependencies",
            "lean": self.VERSION,
            "mathlib": verifier.MATHLIB_REV,
            "config_sha256": config_hashes,
            "catalog_sha256": sha256(self.catalog_path),
            "validation": {
                "command": ["lake", "--rehash", "--no-cache", "--no-build", "build",
                            "+Fixture.Native:olean"],
                "exit_code": 0,
                "log_file": self.validation_log.name,
                "log_sha256": sha256(self.validation_log),
            },
            "modules": {
                self.MODULE: {
                    "source": self.SOURCE,
                    "source_sha256": sha256(self.root / self.SOURCE),
                    "artifact_id": 12345,
                    "validated_dependency_artifact_hashes": self.dependency_hashes(),
                    "output_artifact_hashes": verifier.artifact_hashes(self.MODULE),
                },
                self.DEPENDENCY: {
                    "source": "Fixture/Dependency.lean",
                    "source_sha256": sha256(self.root / "Fixture/Dependency.lean"),
                    "artifact_id": 12345,
                    "validated_dependency_artifact_hashes": {},
                    "output_artifact_hashes": verifier.artifact_hashes(self.DEPENDENCY),
                },
            },
        }
        self.receipt_path = self.log / "native_foundation.json"
        self.write_receipt()

    def write_file(self, relative, content):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        return path

    def artifact_path(self, module, suffix):
        base = self.out / Path(*module.split("."))
        return base.with_name(base.name + suffix)

    def dependency_hashes(self):
        return {self.DEPENDENCY: verifier.artifact_hashes(self.DEPENDENCY)}

    def catalog_entry(self, module, relative_source):
        return {
            "source": relative_source,
            "source_sha256": sha256(self.root / relative_source),
            "build_root": ".lake/build",
            "artifact_id": 12345,
            "artifacts": {
                suffix: {
                    "sha256": sha256(self.artifact_path(module, suffix)),
                    "size_bytes": self.artifact_path(module, suffix).stat().st_size,
                }
                for suffix in self.RUNTIME_SUFFIXES
            },
        }

    def write_catalog(self, *, trust_synthetic_catalog):
        """Rehash fixture bytes, explicitly choosing whether to repin the fixture.

        Semantic checks use a newly pinned synthetic catalog so a stale outer
        pin cannot hide a broken metadata or module check. The separate pin
        regression deliberately preserves the original trusted fixture hash.
        """
        self.catalog_path.write_text(json.dumps(self.catalog))
        self.receipt["catalog_sha256"] = sha256(self.catalog_path)
        if trust_synthetic_catalog:
            verifier.NATIVE_CATALOG_SHA256 = sha256(self.catalog_path)
        self.write_receipt()

    def write_receipt(self):
        self.receipt_path.write_text(json.dumps(self.receipt))

    def load_receipt(self):
        return verifier.load_native_foundation(self.VERSION)

    def native_record(self, *, module=MODULE, relative_source=SOURCE, is_new_source=False):
        return verifier.native_module_record(
            self.load_receipt(), module, relative_source,
            sha256(self.root / relative_source), self.dependency_hashes(), is_new_source,
        )

    @contextmanager
    def altered_file(self, path, *, missing=False):
        original = path.read_bytes()
        if missing:
            path.unlink()
        else:
            path.write_bytes(original + b"\nCHANGED SYNTHETIC FIXTURE BYTES\n")
        try:
            yield
        finally:
            path.write_bytes(original)

    def test_valid_receipt_is_accepted_as_distinct_native_provenance(self):
        loaded = self.load_receipt()
        self.assertEqual(loaded, {**self.receipt, "_catalog_modules": self.catalog["modules"]})
        record = self.native_record()
        self.assertIsNotNone(record)
        self.assertEqual(record["status"], "validated_native_dependency")
        self.assertEqual(record["native_schema"], "native-lake-foundation-v1")
        self.assertTrue(record["reused_native_foundation"])
        self.assertFalse(record["new_source"])
        self.assertEqual(record["native_artifact_id"], 12345)
        self.assertEqual(record["source_sha256"], sha256(self.root / self.SOURCE))
        self.assertEqual(record["validated_dependency_artifact_hashes"], self.dependency_hashes())
        self.assertEqual(record["output_artifact_hashes"], verifier.artifact_hashes(self.MODULE))
        canonical_command = (
            b'["lake","--rehash","--no-cache","--no-build","build","+Fixture.Native:olean"]'
        )
        self.assertEqual(record["native_validation"], {
            "receipt": "native_foundation.json",
            "log_file": self.validation_log.name,
            "log_sha256": sha256(self.validation_log),
            "command_sha256": hashlib.sha256(canonical_command).hexdigest(),
        })
        self.assertNotIn("command", record["native_validation"])
        self.assertNotIn("_catalog_modules", record)

    def test_receipt_is_not_relabelled_as_a_schema_two_compiler_result(self):
        forged_fields = {
            "cache_schema": 2, "exit_code": 0, "flags": ["-DautoImplicit=false"],
            "audit_ok": True, "reused_exact_cache": True,
        }
        self.receipt.update(forged_fields)
        self.receipt["modules"][self.MODULE].update(forged_fields)
        self.write_receipt()
        record = self.native_record()
        self.assertIsNotNone(record)
        for field in forged_fields:
            with self.subTest(field=field):
                self.assertNotIn(field, record)
        self.assertNotIn("exit_code", record["native_validation"])
        self.assertEqual(record["native_validation"]["receipt"], "native_foundation.json")

    def test_changed_source_is_rejected(self):
        with self.altered_file(self.root / self.SOURCE):
            self.assertIsNone(self.native_record())

    def test_changed_output_artifact_is_rejected(self):
        for suffix in self.RUNTIME_SUFFIXES:
            with self.subTest(suffix=suffix), self.altered_file(self.artifact_path(self.MODULE, suffix)):
                self.assertIsNone(self.native_record())

    def test_missing_output_artifact_is_rejected(self):
        for suffix in self.RUNTIME_SUFFIXES:
            with self.subTest(suffix=suffix), self.altered_file(
                self.artifact_path(self.MODULE, suffix), missing=True,
            ):
                self.assertIsNone(self.native_record())

    def test_changed_dependency_artifact_is_rejected(self):
        for suffix in self.RUNTIME_SUFFIXES:
            with self.subTest(suffix=suffix), self.altered_file(self.artifact_path(self.DEPENDENCY, suffix)):
                self.assertIsNone(self.native_record())

    def test_different_source_path_is_rejected_even_with_identical_bytes(self):
        relative = "Fixture/Other.lean"
        self.write_file(relative, (self.root / self.SOURCE).read_bytes())
        self.assertIsNone(self.native_record(relative_source=relative))

    def test_changed_configuration_is_rejected(self):
        for relative in self.CONFIG_CONTENTS:
            with self.subTest(config=relative), self.altered_file(self.root / relative):
                self.assertIsNone(self.load_receipt())

    def test_missing_configuration_is_rejected(self):
        for relative in self.CONFIG_CONTENTS:
            with self.subTest(config=relative), self.altered_file(self.root / relative, missing=True):
                self.assertIsNone(self.load_receipt())

    def test_changed_catalog_is_rejected(self):
        with self.altered_file(self.catalog_path):
            self.assertIsNone(self.load_receipt())

    def test_missing_catalog_is_rejected(self):
        with self.altered_file(self.catalog_path, missing=True):
            self.assertIsNone(self.load_receipt())

    def test_module_absent_from_catalog_is_rejected(self):
        del self.catalog["modules"][self.MODULE]
        self.write_catalog(trust_synthetic_catalog=True)
        self.assertIsNone(self.native_record())

    def test_validation_root_accepts_its_current_local_dependency_closure(self):
        data = self.load_receipt()
        self.assertIsNotNone(data)
        self.assertIsNotNone(self.native_record())
        dependency = verifier.native_module_record(
            data, self.DEPENDENCY, "Fixture/Dependency.lean",
            sha256(self.root / "Fixture/Dependency.lean"), {}, False,
        )
        self.assertIsNotNone(dependency)
        self.assertEqual(dependency["module"], self.DEPENDENCY)
        self.assertEqual(dependency["validated_dependency_artifact_hashes"], {})

    def test_unrelated_catalogued_receipt_module_is_outside_validation_closure(self):
        module, relative = "Fixture.Unrelated", "Fixture/Unrelated.lean"
        self.write_file(relative, b"-- SYNTHETIC NON-PROOF FIXTURE\ndef unrelatedMarker : Nat := 0\n")
        for suffix in self.RUNTIME_SUFFIXES:
            target = self.artifact_path(module, suffix)
            target.write_bytes(f"SYNTHETIC NON-LEAN ARTIFACT: {module}{suffix}\n".encode())
        self.catalog["modules"][module] = self.catalog_entry(module, relative)
        self.receipt["modules"][module] = {
            "source": relative,
            "source_sha256": sha256(self.root / relative),
            "artifact_id": 12345,
            "validated_dependency_artifact_hashes": {},
            "output_artifact_hashes": verifier.artifact_hashes(module),
        }
        self.write_catalog(trust_synthetic_catalog=True)
        self.assertEqual(self.receipt["validation"]["command"][-1], "+Fixture.Native:olean")
        self.assertIsNone(self.load_receipt())

    def test_missing_validation_dependency_source_is_rejected(self):
        with self.altered_file(self.root / "Fixture/Dependency.lean", missing=True):
            self.assertIsNone(self.load_receipt())

    def test_changed_validation_dependency_source_is_rejected(self):
        with self.altered_file(self.root / "Fixture/Dependency.lean"):
            self.assertIsNone(self.load_receipt())

    def test_updating_catalog_and_receipt_cannot_override_trusted_pin(self):
        self.assertIsNotNone(self.native_record())
        trusted_hash = verifier.NATIVE_CATALOG_SHA256
        self.catalog["fixture_note"] = "Changed metadata; still a synthetic non-proof fixture."
        self.write_catalog(trust_synthetic_catalog=False)
        self.assertEqual(self.receipt["catalog_sha256"], sha256(self.catalog_path))
        self.assertNotEqual(self.receipt["catalog_sha256"], trusted_hash)
        self.assertEqual(verifier.NATIVE_CATALOG_SHA256, trusted_hash)
        self.assertIsNone(self.load_receipt())

    def test_receipt_artifact_id_must_match_catalog(self):
        self.receipt["modules"][self.MODULE]["artifact_id"] = 54321
        self.write_receipt()
        self.assertIsNone(self.native_record())

    def test_receipt_source_path_cannot_override_catalog(self):
        relative = "Fixture/RenamedNative.lean"
        self.write_file(relative, (self.root / self.SOURCE).read_bytes())
        self.receipt["modules"][self.MODULE]["source"] = relative
        self.write_receipt()
        self.assertIsNone(self.native_record(relative_source=relative))

    def test_receipt_source_hash_cannot_reauthorize_changed_source(self):
        with self.altered_file(self.root / self.SOURCE):
            self.receipt["modules"][self.MODULE]["source_sha256"] = sha256(self.root / self.SOURCE)
            self.write_receipt()
            self.assertIsNone(self.native_record())

    def test_receipt_output_hashes_cannot_reauthorize_changed_artifacts(self):
        for suffix in self.RUNTIME_SUFFIXES:
            with self.subTest(suffix=suffix), self.altered_file(self.artifact_path(self.MODULE, suffix)):
                self.receipt["modules"][self.MODULE]["output_artifact_hashes"] = (
                    verifier.artifact_hashes(self.MODULE)
                )
                self.write_receipt()
                self.assertIsNone(self.native_record())

    def test_receipt_cannot_drop_catalogued_runtime_artifacts(self):
        # Keep .olean present so rejection requires the complete catalog map.
        for suffix in self.RUNTIME_SUFFIXES[1:]:
            with self.subTest(suffix=suffix), self.altered_file(
                self.artifact_path(self.MODULE, suffix), missing=True,
            ):
                self.receipt["modules"][self.MODULE]["output_artifact_hashes"] = (
                    verifier.artifact_hashes(self.MODULE)
                )
                self.write_receipt()
                self.assertIsNone(self.native_record())

    def test_uncatalogued_runtime_artifact_is_rejected(self):
        del self.catalog["modules"][self.MODULE]["artifacts"][".ir"]
        self.write_catalog(trust_synthetic_catalog=True)
        self.assertIsNone(self.native_record())

    def test_mismatched_catalog_metadata_is_rejected_even_after_rehashing(self):
        original = deepcopy(self.catalog)
        for key, value in (
            ("schema", "schema-2"),
            ("lean", self.VERSION + " CHANGED"),
            ("mathlib", "0" * 40),
        ):
            with self.subTest(field=key):
                self.catalog = deepcopy(original)
                self.catalog[key] = value
                self.write_catalog(trust_synthetic_catalog=True)
                self.assertIsNone(self.load_receipt())

    def test_each_catalog_config_hash_is_bound_to_current_configuration(self):
        original = deepcopy(self.catalog)
        for relative in self.CONFIG_CONTENTS:
            with self.subTest(config=relative):
                self.catalog = deepcopy(original)
                self.catalog["config_sha256"][relative] = "0" * 64
                self.write_catalog(trust_synthetic_catalog=True)
                self.assertIsNone(self.load_receipt())

    def test_catalog_and_receipt_cannot_jointly_override_current_configuration(self):
        relative = "lakefile.toml"
        self.catalog["config_sha256"][relative] = "0" * 64
        self.receipt["config_sha256"][relative] = "0" * 64
        self.write_catalog(trust_synthetic_catalog=True)
        self.assertIsNone(self.load_receipt())

    def test_malformed_catalog_types_are_rejected_without_raising(self):
        cases = [("top-level", value) for value in (None, [], 1, True, "catalog")]
        for key in ("config_sha256", "modules"):
            for value in (None, [], 1, True, "invalid"):
                cases.append((key, {**self.catalog, key: value}))
        for label, value in cases:
            with self.subTest(field=label, value=value):
                self.catalog = value
                self.write_catalog(trust_synthetic_catalog=True)
                self.assertIsNone(self.load_receipt())

    def test_malformed_catalog_module_entries_are_rejected_without_raising(self):
        for entry in (None, [], 1, True, "invalid", {}):
            with self.subTest(entry=entry):
                self.catalog["modules"][self.MODULE] = entry
                self.write_catalog(trust_synthetic_catalog=True)
                self.assertIsNone(self.native_record())

    def test_malformed_catalog_artifact_maps_are_rejected_without_raising(self):
        for artifacts in (None, [], 1, True, "invalid"):
            with self.subTest(artifacts=artifacts):
                self.catalog["modules"][self.MODULE]["artifacts"] = artifacts
                self.write_catalog(trust_synthetic_catalog=True)
                self.assertIsNone(self.native_record())

    def test_internal_catalog_override_in_receipt_is_ignored(self):
        self.receipt["_catalog_modules"] = {"Injected.Fake": {"fixture_only": True}}
        self.write_receipt()
        loaded = self.load_receipt()
        self.assertEqual(loaded["_catalog_modules"], self.catalog["modules"])
        self.assertNotIn("_catalog_modules", self.native_record())

    def test_changed_validation_log_is_rejected(self):
        with self.altered_file(self.validation_log):
            self.assertIsNone(self.load_receipt())

    def test_missing_validation_log_is_rejected(self):
        with self.altered_file(self.validation_log, missing=True):
            self.assertIsNone(self.load_receipt())

    def test_unexpected_validation_log_name_is_rejected(self):
        other = self.log / "other_validation.log"
        other.write_bytes(self.validation_log.read_bytes())
        self.receipt["validation"]["log_file"] = other.name
        self.write_receipt()
        self.assertIsNone(self.load_receipt())

    def test_changed_compiler_version_is_rejected(self):
        self.assertIsNone(verifier.load_native_foundation(self.VERSION + " CHANGED"))

    def test_changed_mathlib_revision_is_rejected(self):
        self.receipt["mathlib"] = "0" * 40
        self.write_receipt()
        self.assertIsNone(self.load_receipt())

    def test_no_build_rehash_and_no_cache_are_required(self):
        original = self.receipt["validation"]["command"][:]
        for required in ("--no-build", "--rehash", "--no-cache"):
            with self.subTest(required=required):
                self.receipt["validation"]["command"] = [arg for arg in original if arg != required]
                self.write_receipt()
                self.assertIsNone(self.load_receipt())

    def test_old_and_extra_validation_options_are_rejected(self):
        original = self.receipt["validation"]["command"][:]
        for option in ("--old", "--jobs=2", "-DautoImplicit=false", "-KbuildType=release", "--"):
            for position in (1, len(original)):
                with self.subTest(option=option, position=position):
                    command = original[:]
                    command.insert(position, option)
                    self.receipt["validation"]["command"] = command
                    self.write_receipt()
                    self.assertIsNone(self.load_receipt())

    def test_empty_or_invalid_validation_targets_are_rejected(self):
        prefix = self.receipt["validation"]["command"][:5]
        for targets in ([], ["Fixture.Native"], ["+Fixture.Native:lean"], ["+Fixture.Native:olean", 7]):
            with self.subTest(targets=targets):
                self.receipt["validation"]["command"] = prefix + targets
                self.write_receipt()
                self.assertIsNone(self.load_receipt())

    def test_failed_validation_exit_is_rejected(self):
        for exit_code in (1, 124, -1):
            with self.subTest(exit_code=exit_code):
                self.receipt["validation"]["exit_code"] = exit_code
                self.write_receipt()
                self.assertIsNone(self.load_receipt())

    def test_noninteger_validation_exit_is_rejected(self):
        for exit_code in (False, True, 0.0, "0", None):
            with self.subTest(exit_code=exit_code):
                self.receipt["validation"]["exit_code"] = exit_code
                self.write_receipt()
                self.assertIsNone(self.load_receipt())

    def test_wrong_receipt_schema_or_status_is_rejected(self):
        original = deepcopy(self.receipt)
        for key, value in (("schema", 2), ("schema", "schema-2"), ("status", "restored_unverified")):
            with self.subTest(key=key, value=value):
                self.receipt = deepcopy(original)
                self.receipt[key] = value
                self.write_receipt()
                self.assertIsNone(self.load_receipt())

    def test_missing_receipt_is_rejected(self):
        self.receipt_path.unlink()
        self.assertIsNone(self.load_receipt())

    def test_malformed_json_is_rejected(self):
        for content in ("", "{", '{"validation":', "not json"):
            with self.subTest(content=content):
                self.receipt_path.write_text(content)
                self.assertIsNone(self.load_receipt())

    def test_malformed_receipt_types_are_rejected_without_raising(self):
        cases = [("top-level", value) for value in (None, [], 1, True, "receipt")]
        for key in ("validation", "config_sha256", "modules"):
            for value in (None, [], 1, True, "invalid"):
                cases.append((key, {**self.receipt, key: value}))
        for label, value in cases:
            with self.subTest(field=label, value=value):
                self.receipt_path.write_text(json.dumps(value))
                self.assertIsNone(self.load_receipt())

    def test_missing_receipt_fields_are_rejected(self):
        original = deepcopy(self.receipt)
        for field in ("schema", "status", "lean", "mathlib", "config_sha256",
                      "catalog_sha256", "validation", "modules"):
            with self.subTest(field=field):
                self.receipt = deepcopy(original)
                del self.receipt[field]
                self.write_receipt()
                self.assertIsNone(self.load_receipt())

    def test_missing_validation_fields_are_rejected(self):
        original = deepcopy(self.receipt["validation"])
        for field in ("command", "exit_code", "log_file", "log_sha256"):
            with self.subTest(field=field):
                self.receipt["validation"] = deepcopy(original)
                del self.receipt["validation"][field]
                self.write_receipt()
                self.assertIsNone(self.load_receipt())

    def test_malformed_module_entries_are_rejected_without_raising(self):
        for entry in (None, [], 1, True, "invalid", {}):
            with self.subTest(entry=entry):
                self.receipt["modules"][self.MODULE] = entry
                self.write_receipt()
                self.assertIsNone(self.native_record())

    def test_missing_module_entry_fields_are_rejected(self):
        original = deepcopy(self.receipt["modules"][self.MODULE])
        for field in ("source", "source_sha256", "artifact_id",
                      "validated_dependency_artifact_hashes", "output_artifact_hashes"):
            with self.subTest(field=field):
                self.receipt["modules"][self.MODULE] = deepcopy(original)
                del self.receipt["modules"][self.MODULE][field]
                self.write_receipt()
                self.assertIsNone(self.native_record())

    def test_unlisted_module_is_rejected(self):
        self.receipt["modules"] = {}
        self.write_receipt()
        self.assertIsNone(self.native_record())

    def test_new_source_is_never_accepted(self):
        self.assertIsNotNone(self.native_record(is_new_source=False))
        self.assertIsNone(self.native_record(is_new_source=True))

    def test_principal_is_never_accepted_even_with_matching_receipt_and_files(self):
        module = "HeckeSkeleton.Principal"
        relative = "HeckeSkeleton/Principal.lean"
        self.write_file(relative, (self.root / self.SOURCE).read_bytes())
        for suffix in self.RUNTIME_SUFFIXES:
            target = self.artifact_path(module, suffix)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(self.artifact_path(self.MODULE, suffix).read_bytes())
        entry = deepcopy(self.receipt["modules"][self.MODULE])
        entry["source"] = relative
        self.receipt["modules"][module] = entry
        self.receipt["validation"]["command"].append("+HeckeSkeleton.Principal:olean")
        self.catalog["modules"][module] = self.catalog_entry(module, relative)
        self.write_catalog(trust_synthetic_catalog=True)
        self.assertIsNotNone(self.load_receipt())
        self.assertEqual(entry["source_sha256"], sha256(self.root / relative))
        self.assertEqual(entry["output_artifact_hashes"], verifier.artifact_hashes(module))
        self.assertIsNone(self.native_record(module=module, relative_source=relative))

    def test_absent_native_foundation_is_rejected(self):
        self.assertIsNone(verifier.native_module_record(
            None, self.MODULE, self.SOURCE, sha256(self.root / self.SOURCE),
            self.dependency_hashes(), False,
        ))


if __name__ == "__main__":
    unittest.main()
