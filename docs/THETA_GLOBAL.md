# THETA_GLOBAL implementation and verification record

## Current status

This is a source implementation on `codex/theta-global-20261030`, with
project dependency validation still in progress.
It is not a claim that the repository's seven-eighths endpoint is proved.
The upstream skeleton contains unrelated admissions that this work does
not discharge.

### Continuation on 2026-10-31

The continuation restores every file of PR head
`4988fbd89fde953539b77c9930ebe9fd206fb0ea` by its Git blob hash and incorporates
the upstream changes through `556fd33068f5914887e850ed2dce9e9272d9b8c2`.
The original task is preserved in `docs/THETA_GLOBAL_TASK.md`; it explicitly
permits the archimedean high K-type/Mellin and exterior-prime digit results
as local assumptions. Their actual input types remain explicit below.

`LocalGammaOrientation` records the character inversion convention at the
level of the actual Hecke parameters. The expanded native gate also checks
the coefficient-shell specification, its two normalization constants,
the fixed source, and the returned `markedReflection` package.

The modified `Principal`, `Moments`, and `Main` consumers receive a separate
native build followed by `ConsumerSignatures.lean`. That file checks all
seven affected consumer declarations against their complete expected
types and reports their existing axioms. Its allowlist includes the
pre-existing `sorryAx`; the Theta entry gate continues to reject it.
These added checks are pending until their exact native run succeeds.

The task targets five declarations in `HeckeSkeleton/Theta.lean`:

| Target | Source implementation | Validation |
| --- | --- | --- |
| `finiteMellinData` | Constructed from the actual fixed projected source; an explicit local high K-type input supplies the archimedean vectors and Mellin pairs. | Project dependency build pending. |
| `finite_valuation_cutoff` | Derived from the actual local rotated shell bounds. | Project dependency build pending. |
| `finite_valuation_decay` | Derived from the actual local rotated shell bounds. | Project dependency build pending. |
| `marked_reflected_absolute` | Replaced by the three-ideal arithmetic majorant proof. | Actual project theorem passes the 188-module transformed source-body check and strict axiom gate; native entry build pending. |
| `marked_reflection` | The actual frequency seed is converted to the literal marked seed using the direct/reflected coefficient dictionaries and support reindexing, then transferred to arbitrary annular tests. Connected to the original entry point with explicit local inputs. | Project dependency build pending. |

No new `sorry`, `axiom`, or `native_decide` is introduced in `ThetaGlobal`.
This syntactic check does not replace elaboration or an axiom audit.

## Arithmetic choice and normalization

`Base.complexEmbedding` aligns the family's primitive twelfth root before
`Base.axiomChoice` is made. `GlobalSameChoice` constructs the theta recipe
with exactly that choice's arithmetic set, complement, correction data,
embedding and allowed-generator section. It does not independently
enlarge or reselect the arithmetic data when switching to the target
infinity type.

The source is selected before the local high K-type data. The finite
target-character projector preserves the source factorization and its
actual archimedean ratios. `FiniteSkeletonSource.coefficient_shell_spec`
displays each returned table entry as the literal integral of the rotated
KP vector, target local period, power-class mask and unit Haar measure.

The direct local profile uses the positive infinite component of the
target character; the reflected profile uses its inverse and the Weyl
action. Write `ρ = heckeComplexParameter`; the repository convention is
`τ = archRadial = -ρ`. Their Gamma factors therefore have radial signs
`-iτ = +iρ` and `+iτ = -iρ`, respectively. Evaluating the direct transform at `-s` yields the literal
denominator Gamma factors of `reflectionMultiplier`.

Both global profiles are divided by the same actual `W_x(1)` and reflected
Mellin constant. `W_x(1)` is retained throughout the two orbit evaluations
and cancelled only after their common nonzero scalar has been identified.
The constants of the finite Mellin datum are derived as

```
A₀ = product of the local positive scales
C₀ = actual finite cutoff volume * product(direct constants)
     / product(reflected constants).
```

## Explicit local inputs

`FiniteLocalHighK.Input R θ C` specifies, at each actual infinite place:

- a vector in the actual complex core and a continuous Whittaker functional
  in the actual completed representation;
- nonvanishing at that vector, including the stored source functional;
- a positive scale and nonzero direct/reflected Mellin constants;
- weighted local Haar integrability and pointwise bounds;
- the two displayed one-place Mellin formulas.

`GlobalProjectLocalDigitTables.Input R D Adata` is a proposition about one
exterior place at a time. It states the spherical diagonal formula, the
nonzero-residue digit average of the actual matrix `A(x) W N(-s/g_p)`, the
zeroth Weyl/Gauss normalization and the finite forward Fourier mask.
The zero digit and the marked average are then derived, using the actual
compact invariance and `q⁻¹ = δ₀ - digitMask₀`.

Neither input contains the global reflected sum, an arbitrary-test
identity, a global seed, a frequency parametrization, or a convergence
assertion about the final ideal series. Existence of the local high
K-type input is exposed explicitly to callers; it is not silently
obtained by an admitted choice.

The endpoint `generalHeckeSevenEighths_skeleton` now has the explicit
conditional type

```lean
(∀ (F : Type) [Field F] [NumberField F] (c : TargetContext F),
  Nonempty (LocalHighKMellinInput F c)) →
(∀ (F : Type) [Field F] [NumberField F] (c : TargetContext F),
  LocalExteriorDigitInput F c) →
GeneralHeckeSevenEighths
```

It also retains the other tasks' original admissions. The five Theta
targets prove the global construction under the permitted local input
boundary; they do not provide those local inputs for every number field.

The arithmetic embedding is refined before making the shared choice:
`complexEmbedding K c` sends the family's selected primitive twelfth root
to the prescribed complex root, and `axiomChoice` uses this aligned
embedding. Every finite table, allowed generator and global source then
uses that same choice. The new `c` argument and the explicit local inputs
are API changes; the consumer signature checks record their propagation.

The original `Theta` entry point receives `LocalHighKMellinInput` and
`LocalExteriorDigitInput`. These are propagated through the actual
`Principal`, `Moments`, and `Main` constructors. The five target
declarations contain no direct admission. That is a source check, not
a claim that all their transitive dependencies have passed an axiom audit.

## Actual reflected index and convergence

`ReflectionIndex` has three independent infinite ideal coordinates:
the frozen numerator, the squarefree column and the cube coordinate.
The absolute-convergence proof retains all three. A quadratic kernel tail
and the actual number-field inverse-square ideal sum give a product of
three summable factors for each of finitely many active/unit branches.

The enlarged raw index has genuine duplicate valuations. For example,
an inactive column exponent one and an active numerator exponent three
both give valuation one after the active denominator shift. The latter
zeroth-digit Weyl coefficient is zero. `GlobalFrequency` records this
counterexample and proves uniqueness on the correct nonzero support.
`GlobalIndexSupport` derives that support from the actual coefficients;
`GlobalActualReindex` and `GlobalActualCoordinates` identify the actual
field-frequency quotient and reconstruct every proof field of the
original `ReflectionIndex`.

Zero-extended residue symbols are treated as zero-or-unit-valued, which
is necessary when they occur with negative powers. No lower bound on a
possibly zero symbol is assumed.

## Global and analytic assembly

The source-level frequency seed is obtained from all-core smooth Fourier
summability on compact families, the nonzero angular character, actual
exterior digit extraction and a measurable compact norm-sheet fundamental
domain. Full-sheet integrability is derived from compact Fourier masses;
it is not a new input. Orbit grouping then cancels the same common scalar
on the two sides.

`GlobalProjectLiteralSeed.thetaRecipe_literal_seed` discharges the literal
seed using the actual source and the separate arithmetic dictionaries.
`GlobalProjectMarkedReflection.thetaRecipe_marked_reflection` supplies
that theorem to the analytic assembly in `ActualAnnularTransfer`; no
global seed is left as an input to the final theorem. The assembly
constructs a Gaussian deconvolver from the actual Gamma
profile, proves the necessary power moments and absolute sum/integral
interchanges, derives positive-regularizer identities, and uses the
actual direct/reflected dominated-convergence theorems. The noncompact
regularized test is never treated as an annular test.

The reciprocal Gamma strip estimate is proved from Euler reflection,
Gamma's integral bound, recurrence and compactness. A separate Stirling
bound is no longer an input to `GammaDeconvolverProject.actualDeconvolver`.

## Verification protocol

Required versions:

- Lean `4.35.0-rc3`, commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`.

Verification results are tied to SHA-256 hashes of the exact source files.
A successful combined-body check means those source bodies elaborate
together with consolidated imports and isolated file scopes. It does not
mean their native project import closures have been built individually.

The native Lake libraries disable both `autoImplicit` and
`relaxedAutoImplicit`. The original direct-compiler checks below did not
pass these two global options; each source file's own option settings were
preserved. The reproduction scripts now pass the native options explicitly.
Historical logs retain their actual commands, and any stricter replay is
recorded separately rather than relabeling an earlier result.

The reflected-project combined-body check contains 188 actual source
bodies. The ten original FLT vendor umbrella imports are preserved: an early attempt
to narrow umbrella imports removed transitive names needed by downstream
files and was reverted after native CI exposed the regression. Curated
imports are used only by the separately labelled transformed QA harness,
with its exact import substitutions and source hashes recorded. The
finite/source closure is much larger and is validated separately.

The current environment has an 8 GiB shared memory limit. Missing private
Mathlib companion artifacts and incomplete cache-root lookup caused early
attempts to fail before theorem elaboration. A single exact-version union
cache was constructed from matching artifact sets. Such infrastructure
failures are not counted as successful proof checks.

### Successful standalone check

The 45-module combined-body bundle passed the pinned compiler with exit
code 0. All original source hashes match the manifest, the checked bundle
was unchanged during compilation, and the printed axiom audits contain
no `sorryAx`.

- Bundle: `verification/theta_global/Standalone.lean`.
- Bundle SHA-256:
  `076e5a154df8572bfacfe3cc36f21375733a9c456b30c468e6b3b5d112818179`.
- Exact original module hashes and result: `verification/theta_global/manifest.json`.
- Unfiltered compiler output: `verification/theta_global/Standalone.build.log`.
- Reproduction command: `python scripts/build_theta_global_bundle.py --check`.

This check includes finite shell/Mellin lemmas, the three-ideal reflected
majorant and dominated limits, support reconstruction, quotient Fourier
lemmas, weighted unfolding, scalar Mellin convolution, Gaussian
deconvolution, reciprocal Gamma growth and full-sheet absolute unfolding.
It checks their consolidated source bodies; it does not establish the
native import closure of the final project entry point.

`GammaReciprocalGrowth.lean` also passed a native standalone compile.
Its SHA-256 is
`2dcaa41abcae69d2675085ed9e32c797247d99bcdcbff6d0f4bee6401e37a2e6`;
the exact log is `verification/theta_global/GammaReciprocalGrowth.native.log`.

`GlobalDiagonalNorm.archimedean_product` also passed its native Mathlib-only
check. Source SHA-256:
`27f5688c4809a08d9ff4e178747bd186f86fea99bfe3506857574e5cc85c4a5e`.
The unfiltered log is `verification/theta_global/GlobalDiagonalNorm.native.log`;
its printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

The same 45-module source bundle additionally passed on GitHub with both
native implicit-parameter options explicitly disabled. The successful
[job 124330035893](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41133369503/job/124330035893)
checked PR head `4a8ea50c821443e2d999d97a2563af89c701832d` through merge
checkout `16fbade39e535e157d24c0cce9a5d59f3fbc2ea6`.
Its log records `Exit: 0 sources unchanged: True`, 56 printed axiom reports
containing only the three standard axioms, and successful repository and
runtime version-pin checks. The command, source-builder identity, and
unfiltered job log are in
`verification/theta_global/Standalone.strict.CI.manifest.json` and
`verification/theta_global/Standalone.strict.CI.log`.
This strengthens the compiler-option check while retaining the same
combined-body scope; it does not certify the final native entry.

### Successful actual reflected-project source-body check

The 188-module actual reflected-project bundle completed on
2026-10-30 at 21:17:01 UTC with exit code 0. The compiler checked the
actual definitions and proof bodies for both
`ThetaGlobal.ReflectedAbsoluteProject.marked_reflected_absolute` and
`ThetaGlobal.ReflectedArithmetic.norm_reflectedCoefficient_le`.
The strict gate verified that both declarations exist and that each
depends only on `propext`, `Classical.choice`, and `Quot.sound`.
All 188 original source hashes and the generated bundle hash remained
unchanged during compilation.

- Bundle SHA-256:
  `ca7bc30fa84a775939c7974b4f5361e8993522698bfa9fd118d4e73b5bf943a3`.
- Source hashes, transformations, observed runtime and result:
  `verification/theta_global/actual_reflected_manifest.json`.
- Unfiltered compiler output:
  `verification/theta_global/ActualReflectedVerification.build.log`.
- Log SHA-256:
  `4e6e11cf9704ee0671354bf093f8d5c228ab8e75b9be39448fadc53417155a0a`.
- Reproduction command:
  `python scripts/build_theta_global_project_bundle.py --output ThetaGlobal/ActualReflectedVerification.lean --check`.

This is explicitly transformed combined source-body QA. The builder
consolidates imports, isolates file scopes, restores scopes left open at
EOF, normalizes line endings, and records the legacy visibility settings,
one command-helper meta annotation, one private-helper visibility change,
and two Fourier-name qualifications. The ten vendor umbrella-import
substitutions apply only to the generated QA header. The manifest records
raw, normalized and transformed-body hashes separately. No theorem is
omitted or replaced by a new assumption. Those ten FLT production import
interfaces remain unchanged; the later Zeta23 direct-import repair is
recorded below. These transformations make this result distinct from a native
per-module build; the five-entry native gate remains necessary.

The same 188-module source bundle subsequently passed a separate replay
with `-DautoImplicit=false` and `-DrelaxedAutoImplicit=false`, using four
elaboration threads. It completed at 22:02:35 UTC on 2026-10-30 with exit
code 0, all original source hashes unchanged, and both strict axiom gates
containing only the three standard axioms. The bundle SHA remained
`ca7bc30fa84a775939c7974b4f5361e8993522698bfa9fd118d4e73b5bf943a3`.
Its independent record is `verification/theta_global/actual_reflected_strict_manifest.json`;
the raw output is `verification/theta_global/ActualReflectedVerification.strict.build.log`.

### Successful supported-index and arithmetic-product increment

A nine-module increment over that exact 188-module foundation completed
on 2026-10-30 at 21:21:55 UTC with exit code 0. It exposed four elaboration
errors in finite-set and subtype product rewrites. The production proofs
in `GlobalIndexSupport` and `GlobalProjectArithmeticProduct` were corrected
against the actual APIs without changing their statements or assumptions.
The corrected source passed strict axiom gates for:

- `GlobalIndexSupport.supported`;
- `GlobalIndexSupport.index_eq_of_branch_unit`;
- `GlobalProjectArithmeticProduct.symmetricCoefficient_eq`.

Each has only the three standard axioms. The nine source hashes, all
foundation source hashes, and the generated bundle remained unchanged.
The bundle SHA-256 is
`7a0fc3da65508c3aa6ce7beb897234058dfaaeddedae6813ebc369cefee92e90`.
The exact reproduction command and foundation hashes are in
`verification/theta_global/index_support_manifest.json`; the raw output
is `verification/theta_global/IndexSupportVerification.build.log`.
The portable builder writes compiled artifacts into Lake's normal library
directory so the increment can import the reproduced foundation without
a custom `LEAN_PATH`. This is again transformed source-body QA, not a
successful native build of the five final entry points.

### Successful actual frequency-representative increment

The actual `GlobalActualFrequency` source also passed a one-module
increment over the same 188-module foundation, with exit code 0 and strict
gates for `localClass_representative`, `norm_representative`, and
`scaled_norm_representative`. No production change was needed.
The generated source SHA-256 is
`2db0f5ae399a28897f4266f2b52e4bebf94d6869187c9e935957b32e7b71d4b3`.
The original and foundation source hashes and all three standard-axiom
results are recorded in
`verification/theta_global/actual_frequency_manifest.json`, with raw output
in `verification/theta_global/ActualFrequencyVerification.build.log`.
This checks the actual representative's local class and two norm formulas;
the complete frequency reindexing still belongs to the larger native gate.

### Successful actual kernel and regularizer increment with native options

A 54-module increment completed on 2026-10-30 at 21:52:53 UTC with exit
code 0. It contains 36 project source bodies and 18 real pinned Mathlib
source bodies, and explicitly passes both native implicit-parameter
options. Its strict gates validate:

- `RegularizedTestProject.pointwise_tendsto`;
- `RegularizedKernelProject.uniform_quadratic_tail`;
- `ReflectedLimitProject.regularized_reflected_sum_tendsto`;
- `GammaDeconvolverProject.actualDeconvolver_all_power_moments`;
- `ScalarKernelProject.regularizedTerm_eq_scalar`.

All five report only `propext`, `Classical.choice`, and `Quot.sound`.
The checked generated source SHA-256 is
`dae728ac736758ba69f148c31ffe787d3f0d3ffbfeb89f097b28d5d2e074530b`.
The exact command, original and transformed source hashes, and result are
in `verification/theta_global/regularizer_project_initial_strict_manifest.json`;
the raw compiler output is
`verification/theta_global/RegularizerProjectVerification.initial_strict.build.log`.

The compiler diagnostics led to local elaboration corrections in
`RegularizedKernelProject`, `ReflectedLimitProject`, and
`RegularizedTestProject`, plus the direct `Complex.LogDeriv` import needed
by the existing `Zeta23.GammaFacts.StirlingVert` source. No theorem statement
or hypothesis was changed; the original `ThetaKernel` proof body was
preserved. The strict gate rejected all failed attempts.

This increment imported the exact previously checked 188-module foundation
artifact, whose original run did not explicitly pass the two global options.
The manifest records that historical artifact and option boundary. The
subsequent strict replay of the foundation is a separate result; it is not
retroactively substituted into this run's provenance.
After that replay succeeded, all five foundation artifacts were compared
and found byte-for-byte identical to the artifacts actually used by the
54-module run. `verification/theta_global/foundation_strict_artifact_comparison.json`
records the two timestamps, manifest hashes and five matching artifact
hashes while preserving the historical order of the checks.

### Remaining validation boundary

The project-facing construction and the final five entry points have not
yet passed a dependency-complete Lean build. The separate actual
reflected-convergence bundle checks a smaller closure and must not be
interpreted as validation of the entire global reflection construction.
The draft PR remains reviewable source work until this boundary is closed.

The PR workflow `.github/workflows/theta-global.yml` runs two independent
checks: the standalone bundle and the actual module target
`+HeckeSkeleton.Theta:olean`. After the latter builds, it runs
`verification/theta_global/EntryAudit.lean`, which rejects `sorryAx` or any
axiom other than `propext`, `Classical.choice`, and `Quot.sound` for each of
the five actual entry points. Workflow configuration is not itself a
successful result; the run must exit successfully and print all five
`THETA_GLOBAL_AXIOMS` records. Both jobs check the repository and runtime
version pins and retain the raw diagnostics as artifacts.

The workflow retains only the project's own dependency build artifacts
in its incremental GitHub cache. Official Mathlib cache downloads remain
enabled. Whole-project setup-cache packaging is disabled because native
CI recorded a disk-space failure while duplicating the large Mathlib
artifacts into a second archive.
Successive runs for the same PR are queued so that an active dependency
build can finish and save its cache before the latest correction starts.
Every result remains tied to its own commit; an earlier run does not
certify a later source change.

The completed native attempt
[41127856107](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41127856107)
failed with filesystem error 28 (`No space left on device`) while compiling
upstream `FLTReuse` dependencies, before reaching the new `ThetaGlobal`
or `HeckeSkeleton` entry modules. Its strict gate was skipped. The cache
action reported a successful step but its log also recorded a disk-space
failure, so that attempt did not preserve the new dependency artifacts.
The [unfiltered diagnostic artifact](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41127856107/artifacts/13014345990)
records this infrastructure failure; it is not a theorem-validation result.
The actual-entry job now frees the unused preinstalled Android SDK and
.NET SDK directories on its ephemeral Ubuntu runner before installing Lean.
It leaves the repository, Python, Lean, and Mathlib paths intact and records
disk availability before and after cleanup. The strict native gate is
unchanged and still requires a successful subsequent run.

The local checkout was based on `503ad9895e5f8affef55b22fea082e251bf33aa7`.
The published tree preserves upstream work through parent
`5e4c85f172c101fd0c201219c13aa28f8b520d42`, including the additional
`HeckePort.PrimeCancellation` library configuration.
