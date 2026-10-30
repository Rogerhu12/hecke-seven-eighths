# THETA_GLOBAL implementation and verification record

## Current status

This is an implementation in progress on `codex/theta-global-20261030`.
It is not a claim that the repository's seven-eighths endpoint is proved.
The upstream skeleton contains unrelated admissions that this work does
not discharge.

The task targets five declarations in `HeckeSkeleton/Theta.lean`:

| Target | Source implementation | Validation |
| --- | --- | --- |
| `finiteMellinData` | Constructed from the actual fixed projected source; an explicit local high K-type input supplies the archimedean vectors and Mellin pairs. | Project dependency build pending. |
| `finite_valuation_cutoff` | Derived from the actual local rotated shell bounds. | Project dependency build pending. |
| `finite_valuation_decay` | Derived from the actual local rotated shell bounds. | Project dependency build pending. |
| `marked_reflected_absolute` | Replaced by the three-ideal arithmetic majorant proof. | Project dependency build pending. |
| `marked_reflection` | Frequency seed, actual support reconstruction and scalar transfer are written; the final literal coefficient assembly is still being completed. | The original admitted endpoint remains until that assembly is connected. |

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
action. Their Gamma factors therefore have radial signs `-iτ` and `+iτ`,
respectively. Evaluating the direct transform at `-s` yields the literal
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

`ActualAnnularTransfer` is an explicitly conditional analytic assembly
whose premise `LiteralSeed` is to be discharged by the separate arithmetic
dictionary. It constructs a Gaussian deconvolver from the actual Gamma
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

The initial native reflected-project closure contains 184 actual source
bodies. Ten vendored `FLTReuse` files have only their broad `import Mathlib`
replaced by the exact required Mathlib imports; their declaration bodies
are unchanged. The finite/source closure is much larger. Its imports and
source hashes are audited separately.

The current environment has an 8 GiB shared memory limit. Missing private
Mathlib companion artifacts and incomplete cache-root lookup caused early
attempts to fail before theorem elaboration. A single exact-version union
cache was constructed from matching artifact sets. Such infrastructure
failures are not counted as successful proof checks.

The final PR update will replace this in-progress section with exact
successful commands, source hashes, axiom outputs and any remaining gaps.
