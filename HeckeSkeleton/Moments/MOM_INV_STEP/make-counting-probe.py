#!/usr/bin/env python3
"""Generate an external, diagnostics-only aggregate of the small-radius chain.

The normal per-module build and axiom audit remain the acceptance gate.
This probe only lets Lean report independent later errors in the same pass
when an earlier module would otherwise block its imports. It changes no
proof source, injects no axiom, and must not supply project build artifacts.
"""

from pathlib import Path
import argparse

NAMES = [
    "LogLatticeCounting", "SUnitLogCounting", "SUnitHeightCounting",
    "SUnitSmallPowerCount", "SparseFiniteSum", "SUnitSmallRadius",
    "SharpCommonKernelBounds",
]

parser = argparse.ArgumentParser()
parser.add_argument("repo", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
base = args.repo / "HeckeSkeleton/Moments/MOM_INV_STEP"
internal = {"HeckeSkeleton.Moments.MOM_INV_STEP." + n for n in NAMES}
imports = []
bodies = []
for name in NAMES:
    body = []
    for line in (base / (name + ".lean")).read_text().splitlines():
        if line.startswith("import ") or line.startswith("public import "):
            mod = line.split("import ", 1)[1].strip()
            if mod not in internal and mod not in imports:
                imports.append(mod)
        elif line.strip() not in {"module", "@[expose] public section"}:
            body.append(line)
    bodies.append("/- BEGIN " + name + " -/\n" + "\n".join(body))
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(
    "/- Diagnostics only. Formal modules and recursive axiom audit remain mandatory. -/\n"
    + "\n".join("import " + m for m in imports)
    + "\n\n" + "\n\n".join(bodies) + "\n"
)
print(str(args.output))
