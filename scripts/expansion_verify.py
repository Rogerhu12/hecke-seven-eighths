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
    skeleton = {module_name(ROOT / p) for p in SKELETON}
    cache: dict[str, bool] = {}

    def pure(mod: str, stack: frozenset[str] = frozenset()) -> bool:
        if mod.startswith(("Mathlib", "Lean", "Std", "Batteries")):
            return True
        if mod in cache:
            return cache[mod]
        if mod not in all_sources or mod in skeleton or mod in stack:
            return False
        result = all(pure(dep, stack | {mod}) for dep in imports(all_sources[mod]))
        cache[mod] = result
        return result

    pure_names = {mod for mod in all_sources if pure(mod)}
    return {
        "pure": sorted(pure_names),
        "actual": sorted(set(all_sources) - pure_names - skeleton),
        "skeleton": sorted(skeleton),
    }


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
        "  let mut count := 0",
        "  let mut nonstandard := 0",
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
    command(["lake", "--fail-fast", "build", *[f"+{m}:olean" for m in selected]],
            OUT / f"{args.group}-build.log")
    command(["lake", "env", "lean", str(audit.relative_to(ROOT))],
            OUT / f"{args.group}-axioms.log")


if __name__ == "__main__":
    main()
