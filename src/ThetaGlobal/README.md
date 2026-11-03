# Fixed-choice marked theta construction

**The source implementation is wired; complete native validation remains
pending.** This revision constructs both the archimedean high K-type input
and finite-place digit certificate on the same actual fixed source.
Public Theta, Principal, Moments and Main require neither L/localData
nor H/localDigits. Their generic helpers retain local input parameters;
the original `marked_reflection` argument `hkernel` is preserved.

This work uses actual definitions in `HeckeGeneral`, `HeckeAxiom`,
`HeckeSkeleton`, and `DedekindZetaZeroFree`. Its original base is
`503ad9895e5f8affef55b22fea082e251bf33aa7` on `dtests-handoff`, with upstream
changes preserved through `6e67559f4285ab833a746db021a0d73200e47590`.
Detailed statements and validation scope are in
[`../docs/THETA_GLOBAL_STATEMENTS.md`](../docs/THETA_GLOBAL_STATEMENTS.md)
and [`../docs/THETA_GLOBAL.md`](../docs/THETA_GLOBAL.md).

## Principal paths

| Part | Modules |
| --- | --- |
| One arithmetic choice, aligned embedding and allowed generators | `GlobalChoice`, `GlobalSameChoice`, `GlobalSkeletonChoice` |
| Actual source, target projector and retained continuous Whittaker certificate | `FiniteFullProduct`, `FiniteFixedSource`, `FiniteTargetCutoff`, `FiniteProjectedFullSource` |
| Literal rotated shell integrals, cutoff and decay | `FiniteProjectedMellin`, `FiniteProjectedIntegral`, `FiniteSkeletonSource` |
| Existing 17-field generic archimedean interface | `FiniteLocalHighK` |
| Actual inverse-character root-core vector and profile | `LocalArchRootCore`, `LocalArchProfile` |
| Actual Haar transport, Mellin pair and Bessel power bounds | `LocalArchHaar`, `LocalArchMellin`, `LocalArchBounds` |
| Complete local input and same-source skeleton adapter | `LocalArchInput`, `LocalArchSource` |
| Normalized global Mellin transforms and character orientation | `FiniteNormalizedMellin`, `FiniteActualProfiles`, `LocalGammaOrientation` |
| Full three-ideal absolute convergence | `ReflectedArithmetic`, `ReflectedAbsoluteProject` |
| All-core Fourier summability and orbit integration | `GlobalProjectFourierSmooth`, `GlobalProjectWeightedSheet`, `GlobalProjectOrbitEvaluation` |
| Derived frequency seed | `GlobalProjectFrequencySeed` |
| Literal direct/reflected coefficient dictionaries and seed | `GlobalSkeletonDirect`, `GlobalProjectReflectedDictionary`, `GlobalProjectReflectedReindex`, `GlobalProjectLiteralSeed` |
| Final source entry point | `GlobalProjectMarkedReflection`, `HeckeSkeleton.marked_reflection` |
| Actual exterior digit calculation and fixed-source certificate | `LocalDigitArithmetic`, `LocalDigitEvaluation`, `LocalDigitAverage`, `LocalDigitInput`, `LocalDigitSource` |
| Actual supported-index uniqueness and coverage | `GlobalIndexSupport`, `GlobalActualReindex`, `GlobalActualCoordinates`, `GlobalProjectMarkedSupport` |
| Scalar deconvolution and actual annular transfer | `GammaReciprocalGrowth`, `GammaDeconvolverProject`, `ActualAnnularTransfer` |

The seven new `LocalArch` modules lift the actual THETA_LOCAL vector
at the angular weight of θ⁻¹ into `complexCore`, evaluate it by the actual
continuous Jacquet functional, transport the exact completion-unit Haar
measure, and prove Mellin formulas and whole-positive-axis power bounds.
The source's continuous Whittaker restriction certificate is retained
through the spherical construction and finite projector. Whittaker
uniqueness then transfers nonvanishing to the stored functional without
adding a premise to `source_nonempty` or using a global ratio circularly.

The actual angular Haar mass is retained in each local Mellin constant;
both constants also divide by the same positive `besselKThird (4 * Real.pi)`.
The bound uses the Schlafli integral's Bessel monotonicity and the exact
power integral to convert local Mellin integrability into a pointwise
estimate. The 17 fields and their precise sources are listed in the
statement report. No global seed, frequency bijection, reflected-series
convergence or final reflection identity is a field of the local package.

The four-field `GlobalProjectLocalDigitTables.Input` is already constructed
in the source using the actual local Bruhat coefficient and
proved residue-field tables with the same character and phase. Its full
native proof chain and 12-declaration strict audit remain pending.

The construction defines `localHighKMellinInput K c` on the already selected
`thetaFiniteSource K c`, then uses it inside `finiteMellinData K c`.
Public Theta, Principal, Moments and Main take neither L/localData
nor H/localDigits. Generic `FiniteSkeletonSource.data` and fixed-source
reflection helpers retain L; `thetaRecipe_marked_reflection` retains L
and H. The original explicit `hkernel` on `marked_reflection` is retained.
Main's unrelated admissions remain, even though its signature
has no added local premise.

The original task explicitly permits these local inputs and is preserved
in [`../docs/THETA_GLOBAL_TASK.md`](../docs/THETA_GLOBAL_TASK.md).
`LocalGammaOrientation` identifies the direct Gamma product with
`archGammaProduct θ⁻¹` and the reflected product with `archGammaProduct θ`.
The implementation applies the local inverse-character convention at θ⁻¹,
matching the fixed source's direct positive character.

The raw reflected index retains three independent ideal coordinates and
genuine zero coefficients, so its frequency map is not injective. The
support-level reindexing proves uniqueness after applying the actual
local zero conditions, then restores the original full index. The
convergence argument retains all three ideal factors.

## Verification scope

At commit `b45484e24f3d4e28cc8092ff6b296f38f4a0f94f`, the
[standalone job](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41166970094/job/124436512226)
passed 45 transformed source bodies and all 56 strict records. Those
45 source hashes still match this revision. The archived
[evidence record](../verification/theta_global/ci_41166970094_standalone.json)
and [compiler log](../verification/theta_global/ci_41166970094_standalone.log)
preserve the exact checked scope. This check does not include the canonical
archimedean construction or certify the full native H/Theta chain. The
independent Haar attempt ended at its 20-minute budget with exit -15,
an empty log and no axiom output. Its
[resource-inconclusive record](../verification/theta_global/native_local_arch_haar_20261031.json)
and [raw log](../verification/theta_global/native_local_arch_haar_20261031.log)
establish neither a native pass nor a Lean proof error. The independent
Bounds check also ended at its 15-minute resource budget with exit -15,
an empty log and no axiom reports; its [record](../verification/theta_global/native_local_arch_bounds_20261031.json)
likewise establishes neither a native pass nor a Lean proof error.

The same historical run passed the actual arithmetic foundation and saved
both dependency caches, then failed in `LocalDigitArithmetic` elaboration.
The revision fixes the reported cast, namespace, extensionality and prime-wrapper
issues; those fixes still await native verification. `LocalDigitEvaluation`,
the full H chain and subsequent entry/consumer gates were not completed.
The [native result](../verification/theta_global/ci_41166970094_native.json) and
[unaltered artifact](../verification/theta_global/ci_41166970094_native_artifact.zip)
record the failed revision separately from the standalone success.

EntryAudit checks **49 = 5 targets + 44 interfaces**, extending the previous
21 checks by 28. LocalDigitAudit has 12 checks and consumer signatures have
seven. The strict gates reject `sorryAx`; consumer compatibility checks
retain the legacy allowance. The existing 35-minute early `lake build`
checks LocalDigitAverage, LocalArchHaar and LocalArchBounds together without
`--fail-fast`, followed by the local-digit and new four-minute
LocalArchAnalyticAudit steps. The latter checks eight strict records
(six Haar and two bounds). Input and fixed-source construction are checked
by the complete 49-declaration EntryAudit. The actual-entry job limit is
330 minutes, with 309 minutes of explicit step timeouts. These configuration
facts do not imply that the native runs have passed.

The historical paragraphs below retain their original verification scope
and provenance.

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
