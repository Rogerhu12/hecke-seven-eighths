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

Acceptance requires the exact current commit to pass the complete independent
module build, the three energy axiom audits, and the changed normalization
consumer's axiom audit. The current result and review state are recorded on
[PR #3](https://github.com/Rogerhu12/hecke-seven-eighths/pull/3).

## Where to review native evidence

Open the **Low reflected energy verification** check for the PR's current head.
Its Actions artifact records the exact commit and tree, reviewed source hashes,
pinned dependency metadata, native Lake exit status, and the fresh final axiom
report. These records establish acceptance for that source commit. Earlier
completed runs and the errors they exposed are linked in
[VERIFICATION_LEDGER.md](VERIFICATION_LEDGER.md).

The CI never restores its own proof outputs. Its optional combined-source
diagnostic is a separate aid for finding downstream errors; acceptance uses the
ordinary module build and final audit described below.

## Statement and coefficient changes

See [GENERAL_STATEMENT.md](GENERAL_STATEMENT.md) for the old/new statement,
quantifier order, exact reflected exponent, source reconstruction, and consumer
interface. The original top-level Hecke L zero-free-region theorem is unchanged.

The independent EXPANSION calibration `7e44ea4` is integrated separately in
commit `dfca5da`:
`physicalResidueNormalizer = c_K * N0`, with the same positive factor in the
compensated kernel numerator. The exact compensated kernel is unchanged, while
the normalized probe has the recorded fixed inverse factor. The follow-up source
corrections to the calibration bridge are included. See
`cloud_tasks/EXPANSION_POISSON_NORMALIZATION.md`.

The shared `LowFrozenCube.PrimeCoordinates` consumer explicitly imports
`Mathlib.Data.Finsupp.SMulWithZero` for its existing `valuation_pow_apply`
proof. Its definitions and statements are unchanged. The consumer is included
in the reviewed source manifest and the independent native build targets.

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

After a failed ordinary build, a diagnostic command can check a single temporary
source unit containing the general and physical endpoints. Its source map records
the exact checkout blobs and original line positions, and its complete import
closure is checked for duplicate inlined declarations. This exposes downstream
errors in the same run. The command writes only diagnostic logs and generated
source metadata to the run artifact; the independent module build and fresh
four-declaration axiom audit remain the acceptance gate.

The manifest contains only current reviewed source paths and hashes. Compilation
logs, reports and native outputs belong in Actions artifacts. Old custom proof
cache/checkpoint scripts, their fixtures, and committed compilation receipts have
been removed. Historical results remain in Git history and their original Actions
runs; none is relabelled as a current success.
