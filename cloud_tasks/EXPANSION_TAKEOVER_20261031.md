# EXPANSION continuation — 2026-10-31

## Starting evidence

Continuation of PR #5 on `codex/expansion-detector-20261030`, starting from
`c79bd5590ce98dddeea04f461b23cfea9c7357e1`; the baseline remains `dtests-handoff`.
The complete actual-job log was read, not inferred from the PR description.

- Run `41164718328`: pure job `124429967040` succeeded; actual job
  `124429967091` failed at 2026-10-31 03:38:50 UTC.
- The actual verification artifact is `13028877340`, SHA-256
  `9d0ca1d88674c6951e3d2e73b60c16711f987272313f22001fff5e3a2530c62b`.
- Ten root modules failed, blocking their downstream targets and the
  exhaustive actual declaration audit. No failed-module axiom printout is
  counted as a successful audit.

## First repair batch

The changes preserve the mathematical statements and their hypotheses:

1. `ExpansionBufferedPolynomials`: explicit monotonicity of addition on the
   correct side, for both rectangle height estimates and the initial tail.
2. `CoefficientZeroCalibration`: expose the actual exterior-ideal coercion
   before applying calibration; retain the original common mask while
   rewriting the already-proved signed background coefficient identity.
3. `ExpansionModels.Core`: prove support using the everywhere-nonzero
   `profilePower`; close literal structure-update identities by reduction;
   repair the selected-slot field-notation parse error.
4. `ExpansionDetectorBridge`: open the actual functional-equation namespace,
   prove positivity of the ideal mass explicitly, and normalize the initial
   zeta exponent without changing it.
5. `ActualPrimeLogSeries`: apply actual finite-preimage membership directly;
   transport ideal logarithmic summability pointwise along the prime-power
   injection and `Prod.swap`.
6. `PhysicalLogDerivative`: resolve the actual archimedean-weight and
   conductor-scale names from their defining namespace.
7. `PhysicalRowPoleExclusion`: apply the proved finite-family fiber result
   directly to the set subtype instead of relying on an inferred instance.
8. `CanonicalDetectorBounds`: expose `idealNorm` before casting the original
   arithmetic bound; replace the final expanded nonlinear search by an
   explicit nonnegative addition and ring identity, with a local heartbeat
   allowance for this conductor theorem only.
9. `ProjectMeromorphicDetector`: expose `rowMaximum` and the actual Hecke
   function before transporting the maximum and meromorphic-order facts.
10. `WitnessAmplitude`: repair the two subdivision field-notation parses.

## Verification status of this batch

The batch is submitted for the existing exact-environment CI. At this
commit, no new full actual/skeleton success is claimed. Lean remains
`4.35.0-rc3`; Mathlib remains
`0493595ecd5da8ef14742febab99728f98e948e8`; strict implicit-parameter options
are unchanged. No workflow, cache policy, theorem hypothesis, axiom,
`sorry`, or native-decide proof is introduced by this batch.

The finite-height prime cancellation chain still uses the literal finite
zero buffer, not all-height zero-free data. The global obligations listed
in `EXPANSION_REPORT.md` remain separate and open; this compilation repair
is not a claim that `expansionRecipeRaw`, `actualHighPresentation`, the
joint budget/cutoffs, or the final `BlockSource` have been constructed.
