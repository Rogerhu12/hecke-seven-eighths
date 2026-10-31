# Actual exterior wiring: verification record

This record concerns `cloud_tasks/WIRE_LOW_HYBRID.md` and the actual-object
entry point `HeckeSkeleton.LowHybridExterior`. The tested implementation commit
is [`e76cda656fe7ab7d73d4681ac7502d45889a7b18`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/e76cda656fe7ab7d73d4681ac7502d45889a7b18).
The subsequent commit adding this record changes documentation only.

## Environment and actual commands

- Lean: **4.35.0-rc3**.
- Lean commit: **470d5ce1400764999581fd26d5d72b00d990b0f4**.
- Mathlib: **0493595ecd5da8ef14742febab99728f98e948e8**.
- Runner: GitHub Actions `ubuntu-latest`, two single-threaded Lean compiler
  processes at most (`WIRE_BUILD_WORKERS=2`, compiler `-j1`).
- Mathlib objects come from the official cache for the pinned revision. Each
  project object, including those for the vendored class-field-theory sources
  in this dependency closure, is compiled from its repository source or reused
  from an earlier successful build after the checks below.

The workflow runs these commands after installing the pinned toolchain and
retrieving the pinned Mathlib cache:

```bash
python3 -u scripts/verify_low_hybrid_exterior.py HeckeSkeleton.LowFrozenCube.ExteriorCoefficientBounds
python3 -u scripts/verify_low_hybrid_exterior.py
```

The first command validates the arithmetic, symbols, local tables, original
reflected coefficient, and coefficient norm bounds. The default target of the
second command is `HeckeSkeleton.LowHybridExteriorAudit`; its complete project
import closure also includes both actual sieve providers and all final energy
endpoints.

The script invokes the real Lean compiler with Lake's import search path and
the package-level Lean options recorded in the compiler command. It checks the full Lean commit, Mathlib manifest
revision and Mathlib checkout revision before building. A successful project
object is reused only if the source, transitive project import closure, package
options, pinned external environment, and every emitted companion object's
hash match the recorded successful build. A failed or blocked dependency cannot
supply a reusable object. The audit module is always recompiled.

Successful-state and results JSON are installed by atomic replacement. Cache
keys include the run ID and attempt, allowing later attempts at the same commit
to save additional validated objects. The full compilation step has a
300-minute limit within the 360-minute job limit, leaving time to save successful
objects and verification evidence if the step times out. An incomplete or failed
compilation remains a failing run; these checkpoints do not satisfy the proof gate.

## Observed result

- Successful workflow: [run 41160961436](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41160961436).
- Successful job: [proofs](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41160961436/job/124418187012).
- Complete project closure: **3321 modules**.
- Final full-stage accounting: **3 compiled, 3318 reused,
  0 failed, 0 blocked**.
- The preflight command also completed successfully.
- Final recursive audit of the new adapter declarations: **271 declarations**, all with axiom
  dependencies contained in `propext`, `Classical.choice`, `Quot.sound`.

The final artifact is [artifact 13027241337](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41160961436/artifacts/13027241337). Its downloaded ZIP has SHA-256
`8ecf1bc42a083598906e733d2ef789b60c4bfa5a18e2153a214cf46f88dce131`, matching GitHub's recorded digest.

The `low-hybrid-exterior-verification` workflow artifact contains
`environment.json`, `results.json`, and compiler logs for modules compiled in
that run. The results include source hashes, exact compiler commands, elapsed
times, exit codes and reuse status for the complete project closure. For reused
modules, the commands, elapsed times and exit codes describe the originating
successful build; the final run revalidates the recorded fingerprints and object
hashes. Earlier
workflow artifacts retain the logs from the builds that supplied reused
objects; the final audit log records every audited declaration's axiom set.

## New Lean modules validated

| Module | Purpose |
|---|---|
| `HeckeSkeleton.LowHybrid.ExteriorArithmetic` | Actual ideal multiplication, prime coordinates, norm and counting |
| `HeckeSkeleton.LowHybrid.ExteriorSymbol` | Allowed-generator error cancellation and exact symbol laws |
| `HeckeSkeleton.LowHybrid.ExteriorSieve` | Actual quadratic and cubic sieve providers |
| `HeckeSkeleton.LowHybrid.ExteriorEnergy` | Actual mixed energy and completed quadratic endpoints |
| `HeckeSkeleton.LowFrozenCube.ExteriorData` | Actual frozen data and original reflection indices |
| `HeckeSkeleton.LowFrozenCube.ExteriorLocalBounds` | Finite Gauss/Weyl scalar estimates |
| `HeckeSkeleton.LowFrozenCube.ExteriorLocalTable` | Exact actual local-table dictionary |
| `HeckeSkeleton.LowFrozenCube.ExteriorPhases` | Actual positive, negative and mixed phase dictionaries |
| `HeckeSkeleton.LowFrozenCube.ExteriorReflection` | Original reflected term equals the raw source term |
| `HeckeSkeleton.LowFrozenCube.ExteriorCoefficientBounds` | Actual coefficient bounds and annular-support constructor |
| `HeckeSkeleton.LowFrozenCube.ExteriorBounds` | Uniform actual frozen block and family energy endpoints |
| `HeckeSkeleton.LowHybridExterior` | Consumer entry point |
| `HeckeSkeleton.LowHybridExteriorAudit` | Recursive axiom guard and explicit endpoint audits |

## Axiom audit and preservation of existing proofs

The audit selects all declaration kinds under the six adapter namespaces,
including private helpers after recovering their user names and generated
structure declarations. It checks each namespace is present, recursively
collects axiom dependencies, and fails on any axiom outside the three listed
above. The observed 271 declarations include 33 private declarations. It also
prints the axiom dependencies of 13 main energy, reflection, support-constructor
and frozen-family endpoints explicitly; each of those endpoint lists contains
only the same three standard axioms.

No existing definition or proof body was changed. The only existing-file edit
narrows the import header of
`DedekindZetaZeroFree/LargeSieve/CharacterBounds/AllIdealTransfer.lean`;
[`EXTERIOR_IMPORTS.json`](EXTERIOR_IMPORTS.json) records the original and new
imports and the SHA-256 of the unchanged body. For that checksum, take the UTF-8
text after the final import line and remove its leading newline separators
(`.lstrip("\n")`); the resulting SHA-256 is
`3baad3fef4af28117d067a98388460a2ae64744f1be900de37745eb12381385f`.
The original and final file also agree byte-for-byte after removing only import
lines, so this checksum convention does not hide a body change. All existing
FLT sources are unchanged.

This verification establishes the actual-object adapters and their dependence
on the proved sieve providers. It does not assert that the downstream
`Principal.completedMarkedEnergy` obligation is complete. Its remaining Mellin
kernel and full reflected-series assembly are described in
[`ACTUAL_WIRING.md`](ACTUAL_WIRING.md).
That downstream Mellin identification must also respect the radial-sign
correction in the [theta-local wiring report](https://github.com/Rogerhu12/hecke-seven-eighths/blob/556fd33068f5914887e850ed2dce9e9272d9b8c2/cloud_notes/theta_local/WIRING_REPORT.md); the literal
reflected-term identity here retains the original project kernel.
