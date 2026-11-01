#!/usr/bin/env python3
"""Strictly inspect Lean's printed axiom reports.

This module checks compiler *output*, not proofs. A successful result is usable
only together with a successful invocation of the pinned Lean compiler on the
actual sources. No report is inferred for declarations absent from the output.
"""
from __future__ import annotations

import re
from collections.abc import Iterable
from typing import Any

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
POLICY_VERSION = 1
_ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
_HEADER = re.compile(
    r"^'[^\n]+' (?:depends on axioms:|does not depend on any axioms)",
    re.MULTILINE,
)
_REPORT = re.compile(
    r"^'(?P<name>[^\n]+)' "
    r"(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
    r"|(?P<empty>does not depend on any axioms))[^\S\n]*$",
    re.MULTILINE,
)


def inspect_axiom_output(
    output: str, *, required: Iterable[str] = ()
) -> dict[str, Any]:
    """Return a JSON-compatible audit; reject unknown or malformed reports.

    `required` contains exact, fully qualified declarations whose printed
    reports must occur. Leave it empty only for a module-level supplementary
    check. In that case zero reports are allowed but explicitly counted as zero.
    Duplicate declarations are rejected rather than selecting a preferred copy.
    """
    if not isinstance(output, str):
        raise TypeError("Compiler output must be text.")
    if isinstance(required, (str, bytes)):
        raise TypeError("Pass required declarations as an iterable of names.")
    names = list(required)
    if any(not isinstance(name, str) or not name or name.strip() != name for name in names):
        raise ValueError("Required declarations must be nonempty exact names.")
    if len(set(names)) != len(names):
        raise ValueError("Required declarations must not be repeated.")
    clean = _ANSI.sub("", output.replace("\r\n", "\n"))
    reports: dict[str, list[str]] = {}
    errors: list[str] = []
    if 'sorryAx' in clean or "declaration uses 'sorry'" in clean:
        errors.append("Admitted-proof marker in compiler output.")
    matches = list(_REPORT.finditer(clean))
    parsed_offsets = {match.start() for match in matches}
    for header in _HEADER.finditer(clean):
        if header.start() not in parsed_offsets:
            errors.append("Malformed axiom report: " + header.group(0))
    for match in matches:
        name = match.group("name")
        raw = match.group("axioms")
        axioms = [] if raw is None or not raw.strip() else [s.strip() for s in raw.split(",")]
        if any(not axiom for axiom in axioms):
            errors.append("Empty axiom entry in " + name)
        if name in reports:
            errors.append("Duplicate axiom report for " + name)
        else:
            reports[name] = axioms
        unknown = sorted(set(axioms) - ALLOWED_AXIOMS)
        if unknown:
            errors.append("Disallowed axioms for " + name + ": " + ", ".join(unknown))
    for name in names:
        if name not in reports:
            errors.append("Missing required axiom report for " + name)
    return {
        "policy_version": POLICY_VERSION,
        "ok": not errors,
        "required_declarations": names,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "printed_declaration_count": len(reports),
        "reports": reports,
        "errors": errors,
        "scope": "Printed compiler-output audit only; not a new compilation or kernel check.",
    }
