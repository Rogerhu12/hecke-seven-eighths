#!/usr/bin/env python3
"""CI-only import/command probes; diagnostic results are NEVER proof evidence.

Run from a repository checkout after setup/cache restoration. The existing V2
build helper first builds the exact original imports, then runs temporary probes
sequentially with its configured per-Lean-process watchdog (300 or 600 seconds).
The diagnostic follows that exact limit without overriding it. No canonical
Lean file is edited and no probe .olean is written. Full-copy probes disable
Elab.async and print flushed stderr checkpoints at complete command boundaries.
stderrAsMessages is disabled in probes so #eval cannot buffer stderr as messages.

Use --module OrdinaryData or --module RawContracts for a smaller job; the default
runs both import-only probes before either full-copy probe. Optional Raw variants
run as separate full-source probes with separate logs and watchdogs. Each can
consume the shared limit, so budget the diagnostic job accordingly. A local
--prepare-only invocation only creates probes/metadata and never imports the gate
or executes Lean/Lake. Execution otherwise requires GITHUB_ACTIONS=true.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

MODULES = ("OrdinaryData", "RawContracts")
KNOWN_WATCHDOG_LIMITS = (300, 600)
SOURCE_DIR = Path("HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2")
CHECKPOINTS = {
    "OrdinaryData": (
        ("attribute [local instance]", "before-local-instances"),
        ("variable {K : Type}", "after-local-instances"),
        ("def leftIdeal ", "before-leftIdeal"),
        ("def rightIdeal ", "after-leftIdeal"),
        ("def leftWhole ", "after-rightIdeal"),
        ("def rightWhole ", "after-leftWhole"),
        ("end RawLeafPacket", "after-rightWhole"),
        ("structure OrdinaryData ", "before-OrdinaryData"),
        ("namespace OrdinaryData", "after-OrdinaryData"),
        ("abbrev rows ", "before-rows"),
        ("abbrev leftFrame ", "after-rows"),
        ("abbrev rightFrame ", "after-leftFrame"),
        ("end OrdinaryData", "after-rightFrame"),
    ),
    "RawContracts": (
        ("attribute [local instance]", "before-local-instances"),
        ("local instance rawContractsCircleFintype", "after-local-instances"),
        ("variable {c : TargetContext", "after-circle-instance"),
        ("structure OriginalCover ", "before-OriginalCover"),
        ("namespace OriginalCover", "after-OriginalCover"),
        ("structure Realizes : Prop", "before-cover-Realizes"),
        ("end OriginalCover", "after-cover-Realizes"),
        ("structure RawCovers ", "before-RawCovers"),
        ("namespace RawCovers", "after-RawCovers"),
        ("def predicates ", "before-predicates"),
        ("abbrev ClassKey ", "after-predicates"),
        ("abbrev Key ", "after-ClassKey"),
        ("def classKey ", "after-Key"),
        ("def leaf ", "after-classKey"),
        ("abbrev LiveKey ", "after-leaf"),
        ("end RawCovers", "after-LiveKey"),
        ("structure RawFamily ", "before-RawFamily"),
        ("theorem active ", "after-RawFamily"),
        ("def packet ", "after-active"),
        ("def Realizes : Prop :=", "after-packet"),
    ),
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def marker(module: str, stage: str, label: str) -> str:
    message = f"V2_DIAG MOM_ENGINE_STEP_V2 {module} {stage} {label}"
    return ("\n#eval (show IO Unit from do\n  let stderr ← IO.getStderr\n"
            f"  stderr.putStrLn {json.dumps(message)}\n  stderr.flush)\n\n")


def boundary(source: str, needle: str) -> int:
    """Exact known declaration anchor; keep its doc/`set_option ... in` wrapper."""
    modifier = r"(?:noncomputable )?" if needle.startswith("def ") else ""
    matches = list(re.finditer(r"^" + modifier + re.escape(needle), source, re.MULTILINE))
    if len(matches) != 1:
        raise ValueError(f"Expected one complete-command anchor {needle!r}, got {len(matches)}")
    position = matches[0].start()
    while True:
        preceding = source[:position].rstrip()
        if preceding.endswith("-/"):
            start = preceding.rfind("/--")
            if start >= 0 and preceding.find("-/", start) == len(preceding) - 2:
                position = start
                continue
        start = preceding.rfind("\n") + 1
        if re.fullmatch(r"set_option .+ in", preceding[start:]):
            position = start
            continue
        return position


def import_header(source: str) -> tuple[str, list[str]]:
    lines = source.splitlines(keepends=True)
    imports = []
    count = 0
    for line in lines:
        match = re.fullmatch(r"import ([A-Za-z0-9_.]+)\s*", line)
        if not match:
            break
        imports.append(match[1])
        count += 1
    if not imports:
        raise ValueError("Expected the known module's contiguous leading import block")
    return "".join(lines[:count]), imports


def prerequisite_plan(imports: list[str]) -> dict:
    excluded = [name for name in imports if name == "Lean" or name.startswith("Lean.")]
    return {"excluded_toolchain_imports": excluded,
            "prerequisite_targets": ["+" + name + ":olean" for name in imports
                                     if name not in excluded]}


def configured_watchdog_limit(source: str) -> int:
    values = re.findall(r"^MODULE_TIMEOUT_SECONDS\s*=\s*(\d+)\s*$", source, re.MULTILINE)
    if len(values) != 1 or int(values[0]) not in KNOWN_WATCHDOG_LIMITS:
        raise RuntimeError("Expected the shared watchdog's known 300/600-second literal; inspect the gate")
    return int(values[0])


def raw_source_variant(source: str, variant: str) -> str:
    """Change only a temporary full-source probe; never the canonical file."""
    anchor = "noncomputable def leaf "
    if len(re.findall(r"^" + re.escape(anchor), source, re.MULTILINE)) != 1:
        raise ValueError("Raw variants require the canonical explicit noncomputable leaf")
    if variant == "canonical":
        return source
    if variant == "trace":
        options = (
            "set_option maxHeartbeats 20000 in\n"
            "set_option diagnostics true in\n"
            "set_option trace.Elab.definition.header true in\n"
            "set_option trace.Elab.definition.value true in\n"
            "set_option trace.addDecl true in\n"
            "set_option trace.Kernel true in\n"
            "set_option trace.Compiler true in\n")
        return source.replace(anchor, options + anchor, 1)
    if variant == "projections":
        original = "  match key with\n  | ⟨⟨i, v⟩, allocation⟩ =>\n      secondSourceLeaf (K := K) (c := c) (call := call) (p := p)\n        (second.source i) (covers.left i).cover (covers.right i).cover v\n        (RawCovers.predicates\n          (K := K) (c := c) (call := call) (p := p)\n          (F := F) (family := family) (expansion := expansion)\n          (second := second) covers i)\n        allocation"
        replacement = "  secondSourceLeaf (K := K) (c := c) (call := call) (p := p)\n    (second.source key.1.1) (covers.left key.1.1).cover (covers.right key.1.1).cover\n    key.1.2\n    (RawCovers.predicates\n      (K := K) (c := c) (call := call) (p := p)\n      (F := F) (family := family) (expansion := expansion)\n      (second := second) covers key.1.1)\n    key.2"
        if source.count(original) != 1:
            raise ValueError("Raw projection diagnostic requires the exact B008 two-Sigma body")
        return source.replace(original, replacement, 1)
    raise ValueError(f"Unknown Raw source diagnostic variant: {variant}")


def prepare(root: Path, evidence: Path, modules: list[str],
            raw_noncomputable_leaf: bool = False,
            raw_variants: list[str] | None = None) -> dict:
    probes = evidence / "probes"
    probes.mkdir(parents=True, exist_ok=True)
    manifest = {"purpose": "DIAGNOSTIC ONLY; NOT ACCEPTED PROOF OUTPUT",
                "accepted_as_proof": False, "canonical_sha256": {},
                "diagnostic_variants": ({"RawContracts": ["explicit-noncomputable-leaf"]}
                                        if raw_noncomputable_leaf else {}),
                "gate_sha256": digest(root / ".github/v2/build.py"),
                "module_timeout_seconds": configured_watchdog_limit(
                    (root / ".github/v2/build.py").read_text(encoding="utf-8")),
                "import_modules": [], "probes": []}
    if raw_variants:
        manifest["diagnostic_variants"]["RawContracts"] = raw_variants
        manifest["trace_heartbeat_limit"] = 20000 if "trace" in raw_variants else None
    for module in modules:
        relative = SOURCE_DIR / f"{module}.lean"
        source = (root / relative).read_text(encoding="utf-8")
        manifest["canonical_sha256"][str(relative)] = digest(root / relative)
        header, imports = import_header(source)
        manifest["import_modules"].extend(imports)
        probe_options = "\nset_option stderrAsMessages false\nset_option Elab.async false\n"
        events = [(len(header), probe_options + marker(module, "source", "imports-ok"))]
        for needle, label in CHECKPOINTS[module]:
            events.append((boundary(source, needle), marker(module, "source", label)))
        copied = source
        for position, insertion in sorted(events, reverse=True):
            copied = copied[:position] + insertion + copied[position:]
        if module == "RawContracts" and raw_noncomputable_leaf:
            anchor = "\ndef leaf ("
            replacement = "\nnoncomputable def leaf ("
            if copied.count(anchor) != 1 or replacement in copied:
                raise ValueError("Expected exactly one ordinary RawCovers.leaf definition")
            original_copy = copied
            copied = copied.replace(anchor, replacement, 1)
            if copied.replace(replacement, anchor, 1) != original_copy:
                raise RuntimeError("The noncomputable-leaf diagnostic changed more than its modifier")
        copied += marker(module, "source", "source-end")
        copies = [("imports", None,
                   header + probe_options + marker(module, "imports", "imports-ok"))]
        if module == "RawContracts" and raw_variants:
            copies.extend(("source", variant, raw_source_variant(copied, variant))
                          for variant in raw_variants)
        else:
            copies.append(("source", None, copied))
        for stage, variant, text in copies:
            suffix = variant.title() if variant else ""
            path = probes / f"N7Diag{module}{stage.title()}{suffix}.lean"
            path.write_text(text, encoding="utf-8")
            entry = {"module": module, "stage": stage,
                     "path": str(path), "sha256": digest(path)}
            if variant:
                entry["variant"] = variant
                original_anchor = re.search(r"^(?:noncomputable )?def leaf ", source, re.MULTILINE)
                probe_anchor = re.search(r"^(?:noncomputable )?def leaf ", text, re.MULTILINE)
                assert original_anchor is not None and probe_anchor is not None
                entry["leaf_canonical_line"] = source.count("\n", 0, original_anchor.start()) + 1
                entry["leaf_probe_line"] = text.count("\n", 0, probe_anchor.start()) + 1
            manifest["probes"].append(entry)
    manifest["import_modules"] = list(dict.fromkeys(manifest["import_modules"]))
    manifest.update(prerequisite_plan(manifest["import_modules"]))
    (evidence / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path)
    parser.add_argument("--module", action="append", choices=MODULES)
    parser.add_argument("--imports-only", action="store_true")
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--raw-noncomputable-leaf", action="store_true",
                        help="Diagnostic copy only: make RawCovers.leaf explicitly noncomputable")
    parser.add_argument("--raw-variant", action="append",
                        choices=("canonical", "trace", "projections"),
                        help="Independent full-source Raw probe variants; none is proof evidence")
    args = parser.parse_args()
    if not args.prepare_only and os.environ.get("GITHUB_ACTIONS") != "true":
        parser.error("Lean/Lake execution is CI-only; local usage requires --prepare-only")
    root = args.root.resolve()
    evidence = (args.output or root / "v2-build/n7-diagnostics").resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    modules = list(dict.fromkeys(args.module or MODULES))
    if args.raw_noncomputable_leaf and "RawContracts" not in modules:
        parser.error("--raw-noncomputable-leaf requires RawContracts")
    if args.raw_variant and "RawContracts" not in modules:
        parser.error("--raw-variant requires RawContracts")
    if args.raw_variant and args.raw_noncomputable_leaf:
        parser.error("Raw variants use the canonical noncomputable leaf; do not combine modifiers")
    raw_variants = list(dict.fromkeys(args.raw_variant or []))
    manifest = prepare(root, evidence, modules, args.raw_noncomputable_leaf, raw_variants)
    print(f"DIAGNOSTIC ONLY; NOT ACCEPTED PROOF OUTPUT: {evidence}", flush=True)
    if args.prepare_only:
        print("Prepared probes only; Lean/Lake were not executed.", flush=True)
        return 0

    os.chdir(root)
    spec = importlib.util.spec_from_file_location("n7_v2_shared_gate", root / ".github/v2/build.py")
    assert spec is not None and spec.loader is not None
    gate = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = gate
    spec.loader.exec_module(gate)  # Imported under another name: never calls main().
    gate.EVIDENCE = evidence
    if (gate.MODULE_TIMEOUT_SECONDS not in KNOWN_WATCHDOG_LIMITS or
            gate.MODULE_TIMEOUT_SECONDS != manifest["module_timeout_seconds"]):
        raise RuntimeError("Shared watchdog changed or is unsupported; inspect the gate and prepare again")
    results = {"accepted_as_proof": False,
               "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
               "module_timeout_seconds": gate.MODULE_TIMEOUT_SECONDS,
               "diagnostic_variants": manifest["diagnostic_variants"],
               "excluded_toolchain_imports": manifest["excluded_toolchain_imports"],
               "prerequisites": None, "stages": [], "canonical_sources_unchanged": None}

    def save() -> None:
        (evidence / "result.json").write_text(json.dumps(results, indent=2) + "\n")

    try:
        targets = manifest["prerequisite_targets"]
        if targets:
            prerequisite = gate.logged(["lake", "build", *targets], "build.log")
        else:
            prerequisite = 0
            print("No repository prerequisite targets; skipping lake build.", flush=True)
        results["prerequisites"] = {
            "exit_code": prerequisite, "targets": targets, "skipped": not targets,
            "log": "build.log" if targets else None}
        save()
        if prerequisite != 0:
            return prerequisite if 0 < prerequisite < 256 else 1
        import_results = {}
        codes = []
        for stage in ("imports", "source"):
            if stage == "source" and args.imports_only:
                break
            for probe in (p for p in manifest["probes"] if p["stage"] == stage):
                module = probe["module"]
                if stage == "source" and import_results.get(module) != 0:
                    results["stages"].append({**probe, "skipped": "import probe failed"})
                    save()
                    continue
                variant_suffix = "_" + probe["variant"] if probe.get("variant") else ""
                log_name = f"{module}_{stage}{variant_suffix}.log"
                started = time.monotonic()
                code = gate.logged(["lake", "env", "lean", probe["path"]], log_name)
                lines = (evidence / log_name).read_text(encoding="utf-8", errors="replace").splitlines()
                checkpoints = [line for line in lines if line.startswith("V2_DIAG MOM_ENGINE_STEP_V2 ")]
                terminal = "imports-ok" if stage == "imports" else "source-end"
                expected = f"V2_DIAG MOM_ENGINE_STEP_V2 {module} {stage} {terminal}"
                marker_present = expected in checkpoints
                effective_code = 1 if code == 0 and not marker_present else code
                if code == 0 and not marker_present:
                    print(f"INVALID DIAGNOSTIC: missing final checkpoint {expected!r}", flush=True)
                codes.append(effective_code)
                if stage == "imports":
                    import_results[module] = effective_code
                results["stages"].append({**probe, "exit_code": code,
                    "effective_exit_code": effective_code,
                    "expected_final_checkpoint": expected, "final_checkpoint_present": marker_present,
                    "elapsed_seconds": time.monotonic() - started, "log": log_name,
                    "checkpoints": checkpoints,
                    "last_checkpoint": checkpoints[-1] if checkpoints else None})
                save()
        return 124 if 124 in codes else (1 if any(codes) else 0)
    finally:
        results["canonical_sources_unchanged"] = all(
            digest(root / path) == expected
            for path, expected in manifest["canonical_sha256"].items())
        save()
        print("DIAGNOSTIC ONLY; canonical build and axiom gate remain required.", flush=True)
        if not results["canonical_sources_unchanged"]:
            raise RuntimeError("Canonical source changed during diagnostics; results are invalid")


if __name__ == "__main__":
    sys.exit(main())
