# LOW-REFLECTED-ENERGY status

## Current work and acceptance

This branch implements the physical completed marked row budget and the general
canonical terminal requested in PR #3. The public general statement is
`HeckeSkeleton.completedMarkedEnergy`; the original physical statement remains
`HeckeSkeleton.CompletedMarkedEnergy`, with proof
`HeckeSkeleton.physicalCompletedMarkedEnergy`.

The general source includes the original product-mark projection's energy, exact
reconstruction of canonical product marks and their original reflection indices,
finite retained-column decompositions, arbitrary-power bounds for their actual
discarded complements, and both conductor comparisons on the actual row annuli.
The height versions choose constants before finite-order children and real norm
twists, with explicit polynomial factors. The finite support and
coefficient records contain no energy or tail hypothesis. The two analytic sieve
inputs and the original marked reflection input remain explicit.

**Verification is pending for the current general source.** Source completion is
not a native Lean build result. PR #3 remains draft until the current exact commit
passes the complete build, the three energy axiom audits, and the changed
normalization consumer's axiom audit.

## Latest completed full build

[Run 41223690903](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41223690903)
built commit `bcb308443216fb32e60d3f5be03cc832ffd2461d` with the official pinned
native dependency release. Its native Lake process exited 1 after 1598.445
seconds, without a timeout. It reported nine diagnostics in two source modules:
coercion, association and nonnegativity proofs in `GeneralHeight`, and two local
subtype reductions in `GeneralConductor`. `GeneralRows` and
`GeneralInactiveMass` were genuinely rebuilt, with their printed declarations
using only the three standard axioms. The run built 496 modules, including 90
of its 119 explicit targets. The failed dependencies prevented the general and
physical endpoints and the final audit from running. The current source repairs
these diagnostics and still requires a complete build.

The earlier `ActualTupleReconstruction` backward powerset-rewrite problem is
replaced by an explicit motive, a finite-sum swap, and the forward subset
identity. The latest completed run could not check that correction because its
changed common-kernel dependency failed first.

The completed run's logs and native outputs are Actions artifacts. They are not
source verification for subsequent changes, and the CI never restores its own
proof outputs. The general modules added after that commit have not yet passed
the complete native pipeline.

## Statement and coefficient changes

See [GENERAL_STATEMENT.md](GENERAL_STATEMENT.md) for the old/new statement,
quantifier order, exact reflected exponent, source reconstruction, and consumer
interface. The original top-level Hecke L zero-free-region theorem is unchanged.

The independent EXPANSION calibration `7e44ea4` is retained as a separate commit:
`physicalResidueNormalizer = c_K * N0`, with the same positive factor in the
compensated kernel numerator. The exact compensated kernel is unchanged, while
the normalized probe has the recorded fixed inverse factor. The follow-up source
corrections to the calibration bridge are included. See
`cloud_tasks/EXPANSION_POISSON_NORMALIZATION.md`.

## Native verification

Environment: Lean `leanprover/lean4:v4.35.0-rc3`, Lean commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`, Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`.

The single workflow `.github/workflows/low-energy-verify.yml` restores the official
`lake-cache-76c696e` dependency release through the pinned repository action. It
checks that the proof build roots are empty, rehashes the native Lake graph, and
requests every source in `source_manifest.json`, `HeckeSkeleton.Principal`,
`Expansion.PhysicalFourierNormalization`, and the changed normalization consumer
`HeckeGeneral.Analysis.CompensatedRowKernelFactorization`. It then starts a fresh Lean process for
the three energy endpoint audits and the normalization factorization audit.
Allowed axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The manifest contains only current reviewed source paths and hashes. Compilation
logs, reports and native outputs belong in Actions artifacts. Old custom proof
cache/checkpoint scripts, their fixtures, and committed compilation receipts have
been removed. Historical results remain in Git history and their original Actions
runs; none is relabelled as a current success.
