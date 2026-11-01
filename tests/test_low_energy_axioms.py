"""Output-parser regression tests. These do not run Lean or prove a theorem."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from low_energy_axioms import inspect_axiom_output

TARGET = "HeckeSkeleton.completedMarkedEnergy"


class AxiomOutputTests(unittest.TestCase):
    def check(self, text: str, expected: bool) -> dict:
        result = inspect_axiom_output(text, required=[TARGET])
        self.assertEqual(result["ok"], expected, result)
        return result

    def test_standard_axioms(self):
        self.check(f"'{TARGET}' depends on axioms: [propext, Classical.choice, Quot.sound]\n", True)

    def test_multiline_output(self):
        self.check(f"'{TARGET}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", True)

    def test_empty_list(self):
        self.check(f"'{TARGET}' depends on axioms: []\n", True)

    def test_no_axioms_report(self):
        self.check(f"'{TARGET}' does not depend on any axioms\n", True)

    def test_sorry_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [propext, sorryAx]\n", False)

    def test_arbitrary_new_axiom_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [propext, MyProject.energy_bound]\n", False)

    def test_native_trust_axiom_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [Lean.ofReduceBool]\n", False)

    def test_missing_target_rejected(self):
        self.check("'Different.target' depends on axioms: [propext]\n", False)

    def test_empty_output_rejected(self):
        self.check("", False)

    def test_truncated_report_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [propext,\n", False)

    def test_empty_entry_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [propext,,Quot.sound]\n", False)

    def test_duplicate_reports_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [propext]\n" * 2, False)

    def test_extra_output_allowed(self):
        self.check("warning: unused section variable\n" +
                   f"'{TARGET}' depends on axioms: [propext]\n", True)

    def test_ansi_and_crlf(self):
        self.check(f"\x1b[32m'{TARGET}' depends on axioms: [propext]\x1b[0m\r\n", True)

    def test_apostrophe_name(self):
        name = "Example.map_one'"
        result = inspect_axiom_output(f"'{name}' depends on axioms: [propext]\n", required=[name])
        self.assertTrue(result["ok"], result)

    def test_no_reports_is_not_inferred_axiom_freedom(self):
        result = inspect_axiom_output("warning: unused argument\n")
        self.assertTrue(result["ok"])
        self.assertEqual(result["printed_declaration_count"], 0)
        self.assertEqual(result["reports"], {})

    def test_malformed_unrequired_report_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [propext]\n"
                   "'Another.name' depends on axioms: [propext,\n", False)

    def test_disallowed_unrequired_report_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [propext]\n"
                   "'Another.name' depends on axioms: [Custom.axiom]\n", False)

    def test_trailing_garbage_rejected(self):
        self.check(f"'{TARGET}' depends on axioms: [propext] garbage\n", False)

    def test_admitted_marker_outside_target_report_rejected(self):
        self.check("warning: sorryAx occurs in a dependency\n" +
                   f"'{TARGET}' depends on axioms: [propext]\n", False)

    def test_sorry_warning_rejected(self):
        self.check("warning: declaration uses 'sorry'\n" +
                   f"'{TARGET}' depends on axioms: [propext]\n", False)

    def test_required_string_is_not_list_of_characters(self):
        with self.assertRaises(TypeError):
            inspect_axiom_output("", required=TARGET)

    def test_invalid_required_names(self):
        for names in [[""], [" bad"], [TARGET, TARGET], [None]]:
            with self.assertRaises(ValueError):
                inspect_axiom_output("", required=names)


if __name__ == "__main__":
    unittest.main()
