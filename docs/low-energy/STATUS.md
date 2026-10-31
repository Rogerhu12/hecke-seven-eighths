# LOW-REFLECTED-ENERGY status

## Current work and acceptance

This branch implements the physical completed marked row budget and the general
canonical terminal requested in PR #3. The public general statement is
`HeckeSkeleton.completedMarkedEnergy`; the original physical statement remains
`HeckeSkeleton.CompletedMarkedEnergy`, with proof
`HeckeSkeleton.physicalCompletedMarkedEnergy`.

The general result includes the literal source-block energy, exact reconstruction
of canonical product marks, arbitrary-power tails from bounded length data, and
both conductor comparisons on the actual row annuli. The finite support and
coefficient records contain no energy or tail hypothesis. The two analytic sieve
inputs and the original marked reflection input remain explicit.

**Verification is pending for the current general source.** Source completion is
not a native Lean build result. PR #3 remains draft until the current exact commit
passes the complete build and the three public/physical axiom audits.

## Latest completed full build

[Run 41218050060](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41218050060)
built commit `da1cd936b24ede2c6b9d352cf9d1e8adb8c37d40` with the official pinned
native dependency release. It reported one source error in
`ActualTupleReconstruction.completedThetaSum_eq_fixedPhysicalRows`: Lean could
not infer the dependent motive when rewriting a powerset sum backwards.
The current source supplies that motive explicitly, swaps the two finite sums,
and applies the powerset identity forwards. This correction still needs the next
native build. The failed run did not reach the final energy audit.

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
requests every source in `source_manifest.json`, `HeckeSkeleton.Principal`, and
`Expansion.PhysicalFourierNormalization`. It then starts a fresh Lean process for
all three required endpoint audits. Allowed axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The manifest contains only current reviewed source paths and hashes. Compilation
logs, reports and native outputs belong in Actions artifacts. Old custom proof
cache/checkpoint scripts, their fixtures, and committed compilation receipts have
been removed. Historical results remain in Git history and their original Actions
runs; none is relabelled as a current success.
