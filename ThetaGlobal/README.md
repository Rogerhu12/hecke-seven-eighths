# Fixed-choice marked theta construction

This directory implements the `THETA_GLOBAL` work against the actual
definitions in `HeckeGeneral`, `HeckeAxiom`, `HeckeSkeleton`, and
`DedekindZetaZeroFree`. The base is commit
`503ad9895e5f8affef55b22fea082e251bf33aa7` on `dtests-handoff`.

**Work in progress: the project-facing source is not yet certified by a
successful dependency-complete Lean build.** The remaining literal marked
coefficient assembly and validation status are tracked in
[`../docs/THETA_GLOBAL.md`](../docs/THETA_GLOBAL.md). Source-level proof
scripts are distinguished from successful compiler results there.

## Principal paths

| Part | Modules |
| --- | --- |
| One arithmetic choice, embedding and allowed generators | `GlobalChoice`, `GlobalSameChoice`, `GlobalSkeletonChoice` |
| Actual finite source and target-character projection | `FiniteFixedSource`, `FiniteTargetCutoff`, `FiniteProjectedFullSource` |
| Literal rotated shell integrals, cutoff and decay | `FiniteProjectedMellin`, `FiniteProjectedIntegral`, `FiniteSkeletonSource` |
| Explicit local archimedean boundary | `FiniteLocalHighK` |
| Normalized direct/reflected Mellin transforms | `FiniteNormalizedMellin`, `FiniteActualProfiles` |
| Full three-ideal absolute convergence | `ReflectedArithmetic`, `ReflectedAbsoluteProject` |
| All-core Fourier summability and orbit integration | `GlobalProjectFourierSmooth`, `GlobalProjectWeightedSheet`, `GlobalProjectOrbitEvaluation` |
| Derived frequency seed | `GlobalProjectFrequencySeed` |
| Explicit local exterior digit boundary | `GlobalProjectLocalDigitTables` |
| Actual index support, uniqueness and coverage | `GlobalIndexSupport`, `GlobalActualReindex`, `GlobalActualCoordinates`, `GlobalProjectMarkedSupport` |
| Scalar deconvolution and actual annular transfer | `GammaReciprocalGrowth`, `GammaDeconvolverProject`, `ActualAnnularProfiles`, `ActualAnnularTransfer` |

The two local boundary types contain local representation vectors,
Whittaker/Mellin formulas, local integrability and local digit formulas.
They contain no theta reflection equality, global frequency bijection,
global coefficient formula, or global summability assertion.

The raw reflected index deliberately retains zero coefficients. Its map
to frequencies is not injective. The support-level reindexing proves
uniqueness only after the actual local zero conditions have been used,
then restores the full original index.

Generated verification bundles are not library modules in the PR. The
portable bundle builder and its manifest describe exactly which source
bodies are checked together. A combined-body check is reported separately
from native, per-module dependency validation.
