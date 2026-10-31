# THETA_GLOBAL — actual fixed-source construction

**Source implementation wired; complete native validation remains pending.**
This revision constructs the canonical archimedean high K-type input L
and finite-place digit certificate H on the same actual fixed source.
The public Theta, Principal, Moments and Main interfaces require neither
L/localData nor H/localDigits. Generic constructors retain their local
parameters, and the original explicit `hkernel` on `marked_reflection`
remains.

The five target source implementations are connected to the actual finite
shell coefficients, coefficient dictionaries and analytic reflection
assembly. Their native dependency build and recursive axiom checks have
not completed. The unrelated admissions in the upstream seven-eighths
skeleton remain; removing an added local premise from Main does not prove
the full endpoint without admissions.

### Continuation on 2026-10-31

The continuation restores PR head
`4988fbd89fde953539b77c9930ebe9fd206fb0ea` by its Git blob hashes and
incorporates upstream changes through
`556fd33068f5914887e850ed2dce9e9272d9b8c2`, then the low-hybrid merge
`6e67559f4285ab833a746db021a0d73200e47590`, preserving the latter's 20
changed files by exact Git blob hashes. All three workflows retain
`cancel-in-progress: true`. The original task remains in
`docs/THETA_GLOBAL_TASK.md` and explicitly permits local archimedean and
exterior-digit inputs. Both local chains in this revision use actual repository definitions
and proved local results to construct those inputs.

`EntryAudit.lean` retains the original 21 strict checks and
adds 28, for **49 = 5 target + 44 interface checks**. The separate early
`LocalDigitAudit.lean` remains a 12-declaration strict gate. The seven
`ConsumerSignatures.lean` types are updated in this revision, with
their existing `sorryAx` allowance retained for unrelated skeleton proofs.
The existing 35-minute early `lake build`, without `--fail-fast`, builds
`LocalArchHaar` and `LocalArchBounds` alongside `LocalDigitAverage`, followed
by an additional
4-minute `LocalArchAnalyticAudit` for eight declarations (six Haar and
two bounds). The build-stage order and 330-minute actual-entry limit
remain unchanged; explicit step timeouts total 309 minutes. These are
configured checks, not recorded successes.

### Native module compatibility

The pinned Lean compiler rejects a modern `module` importing a legacy
file, and also rejects `public import` in a legacy file. Both failures
were reproduced with native two-file probes; the ordinary legacy import
probe passed with `autoImplicit=false` and `relaxedAutoImplicit=false`.

The dependency audit found this boundary in 70 newly added `ThetaGlobal`
modules and the two task audits. Their headers now use the same legacy
format as the existing skeleton: remove `module`, use ordinary `import`,
and remove the modern `@[expose] public section` command. All theorem
statements, assumptions, proof bodies and compiler options are preserved.
The before/after source hashes and equal normalized-body hashes are in
`verification/theta_global/native_header_compatibility.json`.

`GlobalProjectOrbitCoefficients` also now imports its actual
`GlobalProjectWeightedDigits` dependency directly. It also imports
`Digits.SphericalValueBounds`, which defines the actual
`OrbitFrequencies.exteriorDigitValue_eq_slot` lemma used by the proof.
These files were outside the historical consolidated-body verification
lists; inspection of the larger native source closure exposed the missing
edges. The header hash certificate records the preceding header-only
transition; subsequent import corrections remain visible in commit history.

The complete statements and local-input fields are recorded in
[`THETA_GLOBAL_STATEMENTS.md`](THETA_GLOBAL_STATEMENTS.md).

The five target declarations in `HeckeSkeleton/Theta.lean` are:

| Target | Source implementation | Validation scope |
| --- | --- | --- |
| `finiteMellinData` | `FiniteSkeletonSource.data K c (localHighKMellinInput K c)`, on the same fixed projected source. | Canonical-L source wired; full native closure pending. |
| `finite_valuation_cutoff` | The original actual local rotated-shell bound at the same canonical input. | Full native entry validation pending. |
| `finite_valuation_decay` | The original actual local rotated-shell decay at the same canonical input. | Full native entry validation pending. |
| `marked_reflected_absolute` | The existing three-ideal arithmetic majorant applied to the canonical finite table and constructed kernel. | The generic actual-project result passed its historical 188-module transformed check; the changed public entry and full closure remain pending. |
| `marked_reflection` | Actual frequency seed, coefficient dictionaries and supported reindexing, followed by annular transfer; canonical L and H are selected internally. The original `hkernel` remains explicit. | Source wired; full native recursive axiom gate pending. |

The new local proof sources introduce no direct `sorry`, `axiom`, or `native_decide` in
the new local proof chain. This source property does not certify elaboration
or absence of inherited admissions; the native gate must establish that.

## Arithmetic choice and normalization

The existing `HeckeSkeleton.complexEmbedding` aligns the family's
primitive twelfth root before `axiomChoice`. `GlobalSameChoice` then uses
that choice's arithmetic set, complement, correction, embedding and
allowed-generator section throughout. `RootAligned` is derived at the
fixed skeleton entry, not supplied as a new user premise.

`thetaFiniteSource K c` is chosen before the canonical high K-type vector.
The implementation keeps the source's actual factorization, projector and Haar
data and retains an additional local certificate already proved by its
spherical construction. The constructor does not select another source.
`LocalHighKMellinInput K c` unfolds to `FiniteLocalHighK.Input` at exactly
the recipe, period character and fixed source used by
`LocalArchSource.localHighKMellinInput`; the adapter needs no cast or new
type-equality hypothesis.

The actual direct coefficient multiplies the positive infinite component
of θ; reflection multiplies its inverse and applies Weyl. The implementation
root vector has the angular weight of θ⁻¹, and applies the merged local
direct/reflected formulas at θ⁻¹. Write ρ = heckeComplexParameter and
τ = archRadial = -ρ: the two Gamma factors have radial signs -iτ and +iτ.
The direct product is `archGammaProduct θ⁻¹`; the reflected product is
`archGammaProduct θ`. Evaluating the direct transform at -s gives the
existing denominator of `reflectionMultiplier`; its definition is unchanged.

At each place let ν be the source's actual angular Haar measure, let
κ = besselKThird(4π) > 0, and use the weight and parameter of θ⁻¹. The
source local constants are exactly

```
scale = archScale(4π) = 4 / (4π)^2
directConstant = (ν(univ)).toReal * archDirectConstant(4π, weight, parameter) / κ
reflectedConstant = (ν(univ)).toReal * archReflectedConstant(4π, weight, parameter) / κ.
```

No probability or 2π normalization is imposed on ν. Its finite positive
mass is retained by the radial Haar pushforward and in both constants.
The unchanged generic finite-table normalization therefore specializes to

```
A₀ = product of these local positive scales
C₀ = actual finite cutoff volume * product(direct constants)
     / product(reflected constants).
```

`FiniteSkeletonSource.coefficient_shell_spec` still displays each table
entry as the literal integral of the rotated KP vector, target local
period, power-class mask and unit Haar measure. Both global profiles use
the same actual W_x(1) and reflected Mellin constant. W_x(1) is cancelled
only after the common nonzero scalar has been identified.

## Canonical archimedean construction

The seven new modules have the following concrete roles. Their source implementations are wired into the public entry; successful
native validation of the complete chain remains pending.

| Module | Actual construction |
| --- | --- |
| `ThetaGlobal.LocalArchRootCore` | Lifts the actual root-string vector into `complexCore` using harmonic sections and Weyl invariance; proves its `harmonicInclusion` and actual continuous Jacquet value. |
| `ThetaGlobal.LocalArchProfile` | Uses the inverse-character angular weight, actual completion-to-complex isometry and diagonal/Weyl action to identify both normalized local profiles. |
| `ThetaGlobal.LocalArchHaar` | Pushes the literal completion-unit Haar measure along norm-squared, retaining angular mass, and transports the positive-axis `dt/t` Mellin integral. |
| `ThetaGlobal.LocalArchMellin` | Combines the proved local Mellin pair with those exact profile and measure identities, with the correct direct/reflected Gamma signs. |
| `ThetaGlobal.LocalArchBounds` | Proves actual Bessel monotonicity from the Schlafli integral and derives whole-positive-axis power bounds from Mellin integrability. |
| `ThetaGlobal.LocalArchInput` | Divides the bounds by the actual nonzero Bessel value and fills all 17 existing input fields. |
| `ThetaGlobal.LocalArchSource` | Instantiates that constructor at the same already selected `thetaFiniteSource K c`. |

Three source-record replacements accompany them: `FiniteFullProduct`,
`FiniteProjectedFullSource`, and `FiniteFixedSource`. The strengthened
record retains `LocalWhittakerForms`: each stored archimedean functional
is the restriction of an actual continuous Whittaker functional. The
existing `SphericalTransportData.localForm`, `restriction`, and `whittaker`
are carried through the actual coordinate transport, then through the
finite projector that changes the selected tensor. `source_nonempty`
receives no new hypothesis.

`local_value_nonzero_of_whittaker` uses the stored functional's detected
nonzero vector and the actual continuous Whittaker uniqueness theorem.
Consequently a core vector detected by the canonical Jacquet functional
is detected by the source functional as well. The proof does not use
`LocalArchRatio` circularly, and does not assume a global nonzero period
for the newly selected high K-type vector.

For the pointwise bound, set a = archWeight(m) + σ > 0 with σ > -1/3.
The norm of the actual profile is t^archWeight(m) KThird(c√t), and the
proved Mellin convergence makes M = ∫₀∞ u^(a-1) KThird(c√u) du finite.
Bessel monotonicity on 0 < u ≤ t and the exact power integral t^a/a give
t^a KThird(c√t) ≤ aM. Thus B = aM ≥ 0 controls every t > 0; reflection
changes only the radial twist. This is a derived local estimate without
an additional asymptotic or global summability hypothesis.

The complete field mapping is:

| Existing `FiniteLocalHighK.Input` field | Source |
| --- | --- |
| `vector` | `LocalArchProfile.vector`: the actual core lift with the angular weight of `θ⁻¹`. |
| `functional` | The actual continuous `thetaJacquetFunctional traceFrequency`. |
| `whittaker` | `LocalArchRootCore.traceJacquet_whittaker`. |
| `functional_nonzero` | `LocalArchProfile.functional_nonzero`, from the positive value `besselKThird (4 * Real.pi)`. |
| `source_nonzero` | `FiniteFixedSource.Source.archimedean_nonzero`, using the retained local Whittaker form and uniqueness. |
| `scale` | The existing `archScale (4 * Real.pi) = 4 / (4 * Real.pi) ^ 2`. |
| `scale_pos` | The existing `archScale_pos`. |
| `directConstant` | `LocalArchMellin.directConstant R θ C.transport`, including the actual angular mass and Bessel denominator. |
| `directConstant_nonzero` | `LocalArchMellin.directConstant_nonzero`. |
| `reflectedConstant` | `LocalArchMellin.reflectedConstant R θ C.transport`, with the same Haar and Bessel normalization. |
| `reflectedConstant_nonzero` | `LocalArchMellin.reflectedConstant_nonzero`. |
| `direct_integrable` | The first component of `LocalArchMellin.direct_mellin`. |
| `reflected_integrable` | The first component of `LocalArchMellin.reflected_mellin`. |
| `direct_bound` | `LocalArchInput.direct_bound`, from the actual Bessel power bound divided by the normalizing value. |
| `reflected_bound` | `LocalArchInput.reflected_bound`. |
| `direct_mellin` | The second component of `LocalArchMellin.direct_mellin`, with `directGammaPair R θ w s`. |
| `reflected_mellin` | The second component of `LocalArchMellin.reflected_mellin`, with `gammaPair R θ w s`. |

The constructor takes only the actual R, θ and C. No global seed,
frequency bijection, reflected ideal summability assertion or arbitrary-test
reflection identity is among its fields. Full signatures, literal source
excerpts and source fingerprints are in
[`THETA_GLOBAL_STATEMENTS.md`](THETA_GLOBAL_STATEMENTS.md).

## Exterior-digit construction and public API

`GlobalProjectLocalDigitTables.Input R D Adata` has four local fields:
spherical diagonal values, the actual nonzero-residue digit average at
`A(x) W N(-s/g_p)`, zeroth Weyl/Gauss normalization, and the finite forward
Fourier mask. The source constructs all four on the same fixed
source. The zero digit and marked average are derived afterward from
compact invariance and `q⁻¹ = δ₀ - digitMask₀`.

| Existing new local-digit module | Actual connection |
| --- | --- |
| `LocalDigitArithmetic` | Recipe residue character and additive phase are identified with the same arithmetic datum; spherical, zeroth Weyl and mask formulas use the actual `ThetaLocal.ProjectFinite` theorems. |
| `LocalDigitEvaluation` | The actual matrix coefficient is computed using only `JointExteriorCoefficientSources`, its factorization, spherical values and root alignment. |
| `LocalDigitAverage` | Nonzero residue lifts are summed using the proved finite-field phase-separation formula. |
| `LocalDigitInput` | The computed matrix coefficient is identified with `GlobalProjectDigitProduct.localDigit`, filling all four fields. |
| `LocalDigitSource` | `thetaRecipe_arithmeticData` preserves the same allowed-generator choice and constructs `localExteriorDigitInput` on `thetaFiniteSource`. |

This H construction uses `C.exterior.rational_exact` and has no additional
global Mellin, packet, convergence or reflection premise. Its full native
chain remains pending; the historical standalone check is a separate scope.

The canonical-L wiring removes L from public Theta, Principal,
Moments and Main, and removes localData from familyInputs and the endpoint.
It leaves the two explicit consumer `hreflection` parameters, the original
`marked_reflection` parameter `hkernel`, and all unrelated admissions.
The endpoint has declaration

```lean
theorem generalHeckeSevenEighths_skeleton : GeneralHeckeSevenEighths
```

The generic helpers retain their reusable parameters:
`FiniteSkeletonSource.data K c L`,
`thetaFiniteSource_marked_reflection K c L …`, and
`thetaRecipe_marked_reflection K c θ C L H …`.
The public `markedReflection K c` chooses `mellinKernel K c`, canonical L,
and the existing canonical H internally. Removing an added local premise
does not discharge the original Principal/Moments/other upstream `sorryAx`.

## Actual reflected index and convergence

`ReflectionIndex` retains three separate ideal coordinates:
`numeratorFrozen`, the squarefree column `c`, and the cube coordinate `n`.
They satisfy the structure's support conditions, congruence conditions
on valuations, squarefreeness and coprimality conditions. The convergence
proof injects this constrained index into a product of three ideal
indices and retains all three. A quadratic kernel tail and the actual
number-field inverse-square ideal sum give a product of three summable
factors for each of finitely many active/unit branches.

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

`HeckeSkeleton.thetaRecipe_literal_seed`, defined in
`ThetaGlobal/GlobalProjectLiteralSeed.lean`, discharges the literal seed
using the actual source and the separate arithmetic dictionaries.
`HeckeSkeleton.thetaRecipe_marked_reflection`, defined in
`ThetaGlobal/GlobalProjectMarkedReflection.lean`, supplies that theorem
to the analytic assembly in `ActualAnnularTransfer`; no global seed is
left as an input to the final theorem. The assembly
constructs a Gaussian deconvolver from the actual Gamma
profile, proves the necessary power moments and absolute sum/integral
interchanges, derives positive-regularizer identities, and uses the
actual direct/reflected dominated-convergence theorems. The noncompact
regularized test is never treated as an annular test.

The reciprocal Gamma strip estimate is proved from Euler reflection,
Gamma's integral bound, recurrence and compactness. A separate Stirling
bound is no longer an input to `GammaDeconvolverProject.actualDeconvolver`.

## Standalone checkpoint at b454 and outstanding native checks

At commit `b45484e24f3d4e28cc8092ff6b296f38f4a0f94f`,
[job 124436512226](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41166970094/job/124436512226)
completed successfully at `2026-10-31T04:05:38Z`: 45 transformed source
bodies and all 56 expected strict axiom records. Those 45 source hashes
still match this revision. The downloaded
[artifact](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41166970094/artifacts/13029900190)
has SHA-256 `7f3d0592a8f2ec9ea13582f711f061a4c614f2f439892733e1b7f8cd5c265f6e`.
The archived [evidence record](../verification/theta_global/ci_41166970094_standalone.json)
and [compiler log](../verification/theta_global/ci_41166970094_standalone.log)
preserve the exact commit and verification scope. The check does not
include the canonical-L construction, certify the H chain, or close
the full native entry boundary.

### Native LocalArchHaar attempt: resource-inconclusive

The exact `LocalArchHaar` source with SHA-256
`04fcd6397486b8309beb1b0c7c18fd9551df6c795c17cc46b6e9e5e4edea5e3b`
was stopped at its 20-minute resource budget on
`2026-10-31T04:42:03Z`, after 1201.156 seconds, with exit code -15.
Its compiler log has zero bytes and contains no axiom output. This is
classified as `resource-inconclusive`: it establishes neither a native
pass nor a Lean proof error. The measured peak was 44,911 mappings,
below the host limit of 65,530. An interim snapshot at `04:32:48Z`
recorded 159,596,322,816 read bytes (about 159.6 GB) and 699,776 major
faults; those snapshot counters are not whole-run totals. The
[exact-source run record](../verification/theta_global/native_local_arch_haar_20261031.json),
[raw log](../verification/theta_global/native_local_arch_haar_20261031.log)
and [mapping samples](../verification/theta_global/native_local_arch_haar_20261031.maps.jsonl)
preserve the scope and diagnostics.

The independent check of the actual `LocalArchBounds` source
`1a0ebeb15576956ca65f09cc6526a1b9d0522081cd61820cd14761c67f43dd8f`
is still running; no result is recorded here. The historical sections
below retain their original commits, source transformations, compiler
options and artifact provenance.

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

`build_theta_global_bundle.py --check` also requires every requested
`#print axioms` record to appear with the expected multiplicity. It accepts
only `propext`, `Classical.choice`, and `Quot.sound`, rejects missing or
unexpected records, and stores the complete audit in the generated manifest.
The parser handles wrapped output and declarations with no axioms. It was
checked against the saved 56-record successful log and failure fixtures for
missing, duplicate, truncated and forbidden-axiom records. A compiler error
or changed source still fails the check independently of that audit.

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

### Native finite-shell module on 2026-10-31

The actual `ThetaGlobal.FiniteLocalShellProject` source compiled as its own
native module at 02:45:09 UTC with exit code 0 and unchanged source hash
`179eabf85cc5f7fbf80af0dc0aef08a1ef6a75ab48c19a928c8d8d9c2152711d`.
Both `ProjectLocalShell.shellPoint_norm` and `shellData_bounds` report only
the three standard axioms. The command disables both implicit-parameter
options and uses the exact pinned compiler.

This check reused existing dependency artifacts. The recorded Hecke
dependency manifests match their current source and artifact hashes, and
the required import artifacts are present. The historical native
`FiniteShellCoefficients` dependency was compiled without the two global
implicit-parameter flags; its own source disables `autoImplicit`. This
boundary is recorded without relabeling that historical dependency run.
The native command, dependency provenance, source/artifact hashes and raw
compiler log are in `verification/theta_global/native_finite_shell_20261031.json`
and `verification/theta_global/native_finite_shell_20261031.log`.
This is a native check of one module, not the complete five-target entry.

### Native aligned-embedding module on 2026-10-31

The unchanged `ThetaGlobal.GlobalEmbedding` source compiled as its own
native module at 03:01:15 UTC with exit code 0. Its source SHA-256 is
`42d71b175d8208d4e4c072f5d6b3d098a16259ca5e932e0bcbb206ee091b246f`.
The command uses the pinned compiler and disables both implicit-parameter
options. The import check covers 4,942 existing dependency modules.

This original source has no `#print axioms` commands, so this invocation
adds a native compilation result, not an independent axiom-list report.
It reused cached dependencies; it did not rebuild them or freshly hash
every cached artifact. The command, source/output hashes, dependency-check
scope and raw log are preserved in
`verification/theta_global/native_global_embedding_20261031.json` and
`verification/theta_global/native_global_embedding_20261031.log`.
The downstream arithmetic interfaces and the complete entry gate remain
separate checks.

### Arithmetic checkpoint from run 41159434388

The actual-entry job at continuation head `42deaca4` stopped at the
75-minute arithmetic-foundation limit on 2026-10-31 at 03:38:04 UTC.
Its complete log contains no Lean compilation error. The last completed
target was `ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv`
at progress counter `[10409/10422]`; that counter is Lake's scheduling
progress, not a guarantee about the number of remaining source files.

Both the foundation checkpoint and final project cache were saved before
the job completed. The actual Theta build, strict entry audit, Main build
and consumer checks were all skipped. The next revision can reuse the
saved dependency work, but this run does not validate those skipped gates.
The exact cache keys, timestamps and artifact metadata are in
`verification/theta_global/ci_41159434388_native.json`; the unfiltered job
log is `verification/theta_global/ci_41159434388_native.log`.

### Native import resource diagnostic on 2026-10-31

A local native attempt at `GlobalProjectEmbedding` failed while importing
`HilbertSymbolCompletionNaturality.olean.private`, before elaborating the
target. The file and its companion parts match their prior native cache
hashes and sizes. A sampled replay reached 65,531 memory mappings against
the host's `vm.max_map_count` of 65,530; peak resident memory was 592,804 KiB.
The pinned loader falls back to allocation and reading after a failed
mapping. The observed ceiling is consistent with allocation failure in
that path, which reports a generic file-read error.

The failed command, exact source hashes, mapping samples, cache-part checks
and raw log are retained as
`verification/theta_global/native_import_map_limit_20261031.json`,
`verification/theta_global/native_import_map_limit_20261031.jsonl`, and
`verification/theta_global/native_import_map_limit_20261031.log`.
This is a failed import diagnostic, not a proof check. The workflow now
ensures at least 262,144 mappings on its dedicated ephemeral runner,
preserving any larger existing setting. The shared local host setting
has not been changed.

### Standalone replay on 2026-10-31

At continuation commit `42deaca4ef14b01566a13588ba78feb079cd7e09`,
[job 124413821059](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41159434388/job/124413821059)
completed the 45-module standalone check successfully. The downloaded
artifact was checked against every source hash in the continuation checkout.
All 56 expected axiom records are present and use only `propext`,
`Classical.choice`, and `Quot.sound`. The runtime pin check has no errors,
both implicit-parameter options were disabled, and Lean exited with code 0.

The bundle SHA-256 is
`4a2886504c0010bf861085a4809fcaa9442f1f713f8afcaba598b31999a2f667`.
The complete compiler log and artifact manifest, runtime pins, source hashes
and per-declaration axiom records are preserved in
`verification/theta_global/ci_41159434388_standalone.log` and
`verification/theta_global/ci_41159434388_standalone.json`.
This replay checks consolidated source bodies; it does not certify the
native five-target entry or the downstream consumers.

### Historical standalone check

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

### Remaining native validation boundary

The canonical-L construction and changed final five entry points have
not passed a dependency-complete native Lean build. The standalone and
transformed actual-project results certify only their recorded scopes.
Source implementation and API wiring are complete in this revision;
the recursive native gate remains outstanding.

The [workflow](../.github/workflows/theta-global.yml) has separate standalone
and actual-entry jobs. The latter retains its 330-minute total limit;
its explicit step timeouts sum to 309 minutes. After the arithmetic
foundation checkpoint, the existing 35-minute early build runs one
`lake build` without `--fail-fast` for
`+ThetaGlobal.LocalDigitAverage:olean`, `+ThetaGlobal.LocalArchHaar:olean`
and `+ThetaGlobal.LocalArchBounds:olean`. The original four-minute
12-declaration LocalDigitAudit is followed by a four-minute
LocalArchAnalyticAudit, checking six Haar and two Bessel-bound declarations.
The later build order remains Theta/LocalGammaOrientation, EntryAudit,
Main and the seven consumer signature checks.

[EntryAudit.lean](../verification/theta_global/EntryAudit.lean) checks
5 targets and 44 interfaces, or 49 declarations total: the previous 21
plus 28 canonical-archimedean and source-certificate checks. A successful
run must produce all five `THETA_GLOBAL_AXIOMS` and all 44
`THETA_GLOBAL_INTERFACE_AXIOMS` records, then exit with code 0.
[LocalDigitAudit.lean](../verification/theta_global/LocalDigitAudit.lean)
retains 12 `THETA_GLOBAL_LOCAL_DIGIT_AXIOMS` records;
[LocalArchAnalyticAudit.lean](../verification/theta_global/LocalArchAnalyticAudit.lean)
requires eight `THETA_GLOBAL_LOCAL_ARCH_AXIOMS` records and successful exit.
Every strict gate permits only `propext`, `Classical.choice`, and
`Quot.sound`. The complete input and retained source certificate remain
in the 49-declaration recursive gate. The seven consumer type checks retain
their distinct legacy `sorryAx` allowance. None of these configured checks
is recorded as successful before its actual run completes.

The workflow retains only the project's own dependency build artifacts
in its incremental GitHub cache. Official Mathlib cache downloads remain
enabled. Whole-project setup-cache packaging is disabled because native
CI recorded a disk-space failure while duplicating the large Mathlib
artifacts into a second archive.
All three workflows set `concurrency.cancel-in-progress: true`: a new commit
cancels an obsolete build for the same PR or branch. The actual-entry job
first builds the shared `HeckeAxiom.ArithmeticChoice` dependency closure
and saves a separate foundation cache checkpoint. This preserves completed
common dependencies before it starts the Theta proofs and consumer checks.
The final cache uses a distinct key so it can also retain later artifacts.
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

The original implementation checkout was based on
`503ad9895e5f8affef55b22fea082e251bf33aa7`. Its first published tree
preserved upstream work through parent
`5e4c85f172c101fd0c201219c13aa28f8b520d42`, including the additional
`HeckePort.PrimeCancellation` library configuration. The current continuation
also incorporates the upstream parent recorded at the top of this report.
