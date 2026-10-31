#!/usr/bin/env python3
"""Build the EXPANSION source manifest and audit every imported declaration.

The three groups are reported separately.  The skeleton group deliberately
records inherited admissions; it is not counted as an admission-free proof.
No dependency source or compiled artifact is changed by this script.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "expansion-verification"
PREFIXES = ("Expansion", "ExpansionDetector", "ExpansionInterfaces")
PROJECT_PATHS = (
    "HeckeGeneral/Analysis/Expansion*.lean",
    "HeckeSkeleton/ExpansionDetectorBridge.lean",
    "HeckeSkeleton/ExpansionModels/*.lean",
    "HeckeSkeleton/SourceData.lean",
    "HeckeSkeleton/HighBinSupport/*.lean",
)
SKELETON = (
    "HeckeSkeleton/Base.lean",
    "HeckeSkeleton/HighBin.lean",
    "HeckeSkeleton/Expansion.lean",
    "HeckeSkeleton/Moments.lean",
    "HeckeSkeleton/ExpansionModels/SourceRecipeNormalization.lean",
    "HeckeGeneral/Analysis/TInputRanges.lean",
    "HeckeGeneral/Analysis/TInputFixedBinTransfer.lean",
)
STRICT_SOURCE_MODULES = (
    "HeckeSkeleton.SourceData",
    "HeckeSkeleton.ExpansionModels.SourceData",
)


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def sources() -> dict[str, Path]:
    paths = {p for prefix in PREFIXES for p in (ROOT / prefix).glob("*.lean")}
    for pattern in PROJECT_PATHS:
        paths.update(ROOT.glob(pattern))
    paths.update(ROOT / p for p in SKELETON)
    return {module_name(p): p for p in sorted(paths)}


def imports(path: Path) -> list[str]:
    text = re.sub(r"/\-.*?\-/", "", path.read_text(), flags=re.S)
    return [m for line in text.splitlines()
            if (match := re.match(r"\s*(?:(?:public|private|meta)\s+)*import\s+(.+)", line))
            for m in match[1].split("--", 1)[0].split()]


def groups(all_sources: dict[str, Path]) -> dict[str, list[str]]:
    admitted_skeleton = {
        "HeckeSkeleton.Base", "HeckeSkeleton.HighBin",
        "HeckeSkeleton.Expansion", "HeckeSkeleton.Moments",
    }
    cache: dict[str, int] = {}
    source_roots = (ROOT, ROOT / "PrimeCancellation", ROOT / "SkeletonInputs", ROOT / "GramCoreInputs",
                    ROOT / "GramAssemblyInputs", ROOT / "vendor/openai",
                    ROOT / "vendor/flt", ROOT / "vendor/zeta23",
                    ROOT / "vendor/tauceti", ROOT / "vendor/class-field-theory/Lean4")

    def level(mod: str, stack: frozenset[str] = frozenset()) -> int:
        if mod.startswith(("Mathlib", "Lean", "Std", "Batteries")):
            return 0
        if mod in admitted_skeleton:
            return 2
        if mod in cache:
            return cache[mod]
        if mod in stack:
            raise RuntimeError(f"Cyclic source imports involving {mod}")
        relative = Path(*mod.split(".")).with_suffix(".lean")
        path = all_sources.get(mod)
        if path is None:
            path = next((root / relative for root in source_roots
                         if (root / relative).is_file()), None)
        if path is None:
            return 1
        dependencies = [level(dep, stack | {mod}) for dep in imports(path)]
        # An external project dependency is actual arithmetic even if its
        # own imports happen to be Mathlib-only.  Skeleton inheritance is
        # propagated through every intervening project module.
        result = max([0 if mod in all_sources else 1, *dependencies])
        cache[mod] = result
        return result

    return {group: sorted(mod for mod in all_sources if level(mod) == rank)
            for group, rank in (("pure", 0), ("actual", 1), ("skeleton", 2))}


def command(args: list[str], log: Path) -> None:
    with log.open("w") as stream:
        proc = subprocess.Popen(args, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        assert proc.stdout is not None
        for line in proc.stdout:
            print(line, end="", flush=True)
            stream.write(line)
        code = proc.wait()
    if code:
        raise SystemExit(code)


def audit_source(modules: list[str], strict: bool) -> str:
    return "\n".join([
        *[f"import {mod}" for mod in modules],
        "import Lean.Util.CollectAxioms",
        "open Lean in",
        "run_cmd do",
        "  let env ← getEnv",
        "  let selected : Array Name := #[" + ", ".join("`" + m for m in modules) + "]",
        "  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]",
        "  let mut count : Nat := 0",
        "  let mut nonstandard : Nat := 0",
        "  for (name, _) in env.constants.toList do",
        "    if let some idx := env.getModuleIdxFor? name then",
        "      if selected.contains env.header.moduleNames[idx.toNat]! then",
        "        count := count + 1",
        "        let axioms ← collectAxioms name",
        "        let extra := axioms.filter fun ax => !allowed.contains ax",
        "        if !extra.isEmpty then",
        "          nonstandard := nonstandard + 1",
        ('          throwError "EXPANSION unexpected axioms: {name}: {extra}"' if strict else
         '          logInfo m!"EXPANSION inherited axioms: {name}: {extra}"'),
        '  if count == 0 then throwError "EXPANSION audit selected no declarations"',
        '  logInfo m!"EXPANSION audit: {count} declarations; {nonstandard} nonstandard dependencies"',
        "",
    ])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--group", choices=("pure", "actual", "skeleton"), required=True)
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    all_sources = sources()
    selected = groups(all_sources)[args.group]
    if not selected:
        raise SystemExit("No source modules selected")
    OUT.mkdir(exist_ok=True)
    manifest = {
        "group": args.group,
        "audit_policy": "standard axioms only" if args.group != "skeleton" else "report all inherited axioms",
        "sources": [{"module": m, "path": str(all_sources[m].relative_to(ROOT)),
                     "sha256": hashlib.sha256(all_sources[m].read_bytes()).hexdigest()}
                    for m in selected],
    }
    (OUT / f"{args.group}-sources.json").write_text(json.dumps(manifest, indent=2) + "\n")
    audit = OUT / f"{args.group}_audit.lean"
    audit.write_text(audit_source(selected, args.group != "skeleton"))
    if args.plan:
        print(json.dumps(manifest, indent=2))
        return
    # Finish independent modules after an error so a single proof failure
    # does not discard unrelated diagnostics or reusable compilation work.
    # Lake still exits nonzero on any required failure; the audit stays gated.
    command(["lake", "build", *[f"+{m}:olean" for m in selected]],
            OUT / f"{args.group}-build.log")
    command(["lake", "env", "lean", str(audit.relative_to(ROOT))],
            OUT / f"{args.group}-axioms.log")
    # These modules import the actual context, but their explicit source data
    # must not depend on its unfinished raw-expansion choice, even in types.
    # Audit every declaration separately with the unchanged strict allowlist.
    if args.group == "skeleton":
        strict_audit = OUT / "source_data_audit.lean"
        strict_audit.write_text(audit_source(list(STRICT_SOURCE_MODULES), True))
        command(["lake", "env", "lean", str(strict_audit.relative_to(ROOT))],
                OUT / "source-data-axioms.log")


if __name__ == "__main__":
    main()
