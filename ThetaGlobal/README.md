# Fixed-choice marked theta construction

This directory implements the `THETA_GLOBAL` work against the actual
definitions in `HeckeGeneral`, `HeckeAxiom`, `HeckeSkeleton`, and
`DedekindZetaZeroFree`. The base is commit
`503ad9895e5f8affef55b22fea082e251bf33aa7` on `dtests-handoff`; publication
preserves the subsequent changes through
`5e4c85f172c101fd0c201219c13aa28f8b520d42`.

**Work in progress: the project-facing source is not yet certified by a
successful dependency-complete Lean build.** All five target entry points
now have source implementations, including the literal marked coefficient
assembly. Validation status is tracked in
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
| Literal direct/reflected coefficient dictionaries and seed | `GlobalSkeletonDirect`, `GlobalProjectReflectedDictionary`, `GlobalProjectReflectedReindex`, `GlobalProjectLiteralSeed` |
| Final source entry point | `GlobalProjectMarkedReflection`, `HeckeSkeleton.Theta.marked_reflection` |
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

The checked standalone bundle is in `verification/theta_global`, outside
the `ThetaGlobal` library glob. Its 45 source bodies compile with the
pinned Lean and Mathlib versions, exit code 0, and no `sorryAx` in the
printed axiom audits. The portable bundle builder and manifest identify
the exact checked source hashes. This combined-body check is reported
separately from native, per-module dependency validation.

The separate 188-module transformed actual-project bundle also passed with
exit code 0. It checks the actual reflected absolute-convergence theorem
and coefficient bound, including strict gates allowing only `propext`,
`Classical.choice`, and `Quot.sound`. Its manifest records every source
hash and harness transformation; the raw log and portable builder are
included. This result does not certify the native import closure of the
final five entry points.

A nine-module increment over that foundation passed the same strict gate
for actual nonzero-coefficient support, supported-index uniqueness, and
the equality between the symmetric and literal arithmetic coefficients.
Its exact source and foundation hashes are recorded in
`verification/theta_global/index_support_manifest.json`.

The actual frequency representative's local class and norm formulas also
passed their own increment. A further 54-module increment passed with the
native implicit-parameter options and strict axiom gates for the actual
kernel tail, regularized reflected-series limit, deconvolver moments, test
limit, and scalar-to-actual term identity. Its manifest preserves the exact
historical foundation artifact used by that run. The 45-module bundle has
also passed on GitHub with both native implicit-parameter options.

The 188-module foundation subsequently passed its own replay with both
native implicit-parameter options. Its five compiled artifacts are
byte-for-byte identical to the historical foundation used by the
54-module check; the separate comparison record preserves that chronology.
