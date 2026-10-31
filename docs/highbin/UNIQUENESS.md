# Uniqueness of the actual row Euler continuation

The continuation comparison has two levels. The first proves pointwise
uniqueness on the repository's original `rowEulerRegion`. The second uses the
actual finite rational tables to prove almost-everywhere equality on vertical
real parameter spaces, and hence equality of the literal contour integrals
throughout the larger high-bin swept tube. Neither level requires equality of
two `RowEulerData` records. The second level includes the nonpositive real parts
of the `w` coordinate needed at the high-bin endpoint.

The actual arithmetic and presentation applications described here remain
source candidates pending a complete native build. They do not construct the
named admitted presentation, its heights, companions, or retained-block count.

The implementation is split between
[EulerRegionUniqueness.lean](../../HeckeSkeleton/HighBinSupport/EulerRegionUniqueness.lean)
and
[ActualEulerUniqueness.lean](../../HeckeSkeleton/HighBinSupport/ActualEulerUniqueness.lean).
The first contains only the region geometry and the analytic identity principle.
The second applies it to the original characters, deleted L-functions, correction,
continuation, zero detectors, and compensated kernel.

## Verification status

The current pure three-declaration module passed a local native Lean check with
exit code 0 in 22.756 seconds. Each checked declaration used only `propext`,
`Classical.choice`, and `Quot.sound`. The generated verification-source SHA-256
is `f73d7cdf772b6f9058e9612a9fff62ba59ab54c44ee8509ef0c95e51dea72653`.
This check contains the source module and all three public type/axiom checks;
the separate repository CI check also passed at `45b507f4995fe107e2e98041f91971c8c78d5860`
as part of the 57-module, 442-declaration core audit. Exact run and artifact
references are recorded in [REPORT.md](REPORT.md).

The actual module has not yet passed a complete native build or its transitive
axiom audit. Its signatures below record source candidates until that check
finishes. The successful pure identity-principle check does not verify the
arithmetic instantiation or the upstream original `TRowEulerInput` constructor.

## Original domain and the analytic theorem

The domain is exactly the existing definition in
[RowEulerRegion.lean](../../HeckeGeneral/Analysis/RowEulerRegion.lean):

```lean
def rowEulerRegion : Set (ℂ × ℂ × ℂ) :=
  {v | 1 / 2 < v.1.re ∧ 0 < v.2.1.re ∧ 0 < v.2.2.re ∧
    1 < v.1.re + v.2.1.re ∧ 5 / 6 < v.1.re + v.2.2.re ∧
      2 < v.1.re + v.2.1.re + 6 * v.2.2.re ∧
      1 < v.2.1.re + 6 * v.2.2.re ∧ 1 < v.1.re + 6 * v.2.2.re}
```

Each condition is an open affine half-space over the underlying real vector
space. Their intersection is convex, hence preconnected. The point `(5,5,5)`
belongs both to this region and to the initial open domain
`4 < Re(s)`, `4 < Re(w)`, `2 < Re(z)`. The general Banach-space analytic identity
principle therefore applies to three complex variables together:

```lean
theorem eqOn_rowEulerRegion_of_initial
    {f g : (ℂ × ℂ × ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f rowEulerRegion)
    (hg : AnalyticOnNhd ℂ g rowEulerRegion)
    (hinitial : ∀ v : ℂ × ℂ × ℂ,
      4 < v.1.re → 4 < v.2.1.re → 2 < v.2.2.re → f v = g v) :
    EqOn f g rowEulerRegion
```

The source namespace is `HeckeSkeleton.HighBinContinuation`. This theorem uses
joint `AnalyticOnNhd`; separate coordinate differentiability is not substituted
for that premise.

## What the original arithmetic calibration determines

The ambient arithmetic parameters are the repository's original ones:

```lean
(K : Type) [Field K] [NumberField K]
(S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
(P : ProbeData K S)
(ψ : HeckeCharacter K)
```

The source namespace for the remaining declarations is
`HeckeSkeleton.HighBinEulerUniqueness`.

First, the two providers' row characters agree. This uses the existing
[RowCharacterInputUniqueness.lean](../../SkeletonInputs/RowCharacterInputUniqueness.lean)
theorem `rowCharacterInput_character_unique`. Its proof compares the true prime
coefficients away from the finite set consisting of `S` and the row support,
then invokes the finite-order Hecke-character uniqueness theorem. The proof does
not infer ramification at row primes from the masked ideal-coefficient field.

Consequently, for any two `RowEulerData` providers, the literal
`physicalRowFamily` is equal and both `rowZeroBelow` and `rowZeroAbove` are
equivalent. These conclusions do not require equality of the exceptional
finite rational tables, and the character calibration already belongs to the
original `RowCharacterInput` field.
`physicalRowBin_eq_of_calibrated` consequently identifies the original finite
fixed bins for all detector heights and real bin endpoints.

Second, the two `initial_identity` fields identify the same actual
`initialRowEulerSeries` with the two continuations. On that initial domain the
three actual deleted Hecke factors are nonzero: their arguments have real parts
greater than one. Their common product/quotient can therefore be cancelled,
giving equality of `rowCorrection`. No nonvanishing of the correction or of a
finite Gauss polynomial is assumed.

Third, the original `correction_analytic` fields and the pure theorem above
propagate correction equality to the entire original region:

```lean
theorem rowCorrection_eq_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : TRowEulerInput K S P ψ E₁) (h₂ : TRowEulerInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    rowCorrection K S P ψ E₁ Q u v.1 v.2.1 v.2.2 =
      rowCorrection K S P ψ E₂ Q u v.1 v.2.1 v.2.2
```

After multiplying by the common literal deleted L-ratio, the continuation itself
agrees there:

```lean
theorem rowEulerContinuation_eq_of_calibrated
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : TRowEulerInput K S P ψ E₁) (h₂ : TRowEulerInput K S P ψ E₂)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    rowEulerContinuation K S P ψ E₁ Q u v.1 v.2.1 v.2.2 =
      rowEulerContinuation K S P ψ E₂ Q u v.1 v.2.1 v.2.2
```

This last equality does not add nonvanishing or regularity assumptions for the
L-factors at the later point. Once the corrections and row characters are equal,
the two repository expressions are identical, including Lean's original
totalized division.

## Specialization to the constructed arithmetic provider

The arithmetic side supplies its original `TRowEulerInput` through
`arithmeticTRowEulerInput`; no equality of provider structures is a premise.
The other side supplies the original input it claims to realize:

```lean
theorem rowEulerContinuation_eq_arithmetic
    (P : ProbeData K S) (hP : AllowedGeneratorInput K S P.arithmetic)
    (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K S, UnramifiedAt K ψ p.val)
    (E : RowEulerData K S P) (hE : TRowEulerInput K S P ψ E)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    rowEulerContinuation K S P ψ E Q u v.1 v.2.1 v.2.2 =
      rowEulerContinuation K S P ψ (arithmeticHighEulerData K S P ψ)
        Q u v.1 v.2.1 v.2.2
```

Here `hP` is the repository's allowed-generator input; `hcal` is the actual
mixed theta/Gauss calibration; and `hψ` states that the target character is
unramified at the exterior primes. These are the same arithmetic assumptions
used to construct the genuine provider. There is no added Fourier identity,
Euler-product conclusion, or final boundary estimate among the premises.

`rowCorrection_eq_arithmetic` is the corresponding correction equality.
`compensatedRowMellinKernel_eq_of_calibrated` rewrites all of the marked
continuations in the literal finite prime/subset sum and gives equality of the
original compensated kernels at every point of `rowEulerRegion`. Its extra
ambient parameters are exactly the existing local measurable spaces, Borel
instances, Haar measures, and norm-one measurable/Borel instances required by
the kernel definition.

`rowContourBox_eq_of_calibrated` carries this equality through the repository's
original three nested finite integrals whenever
`((σ : ℂ), (ν : ℂ), (zLine : ℂ)) ∈ rowEulerRegion`. Adding the three imaginary
coordinates preserves all eight domain inequalities. The proof rewrites the
integrands pointwise and retains the original normalization, with no added
integrability assumption. It does not remove that real-part domain condition.

## Why pointwise equality on the original region is insufficient

The high-bin contour uses

$$
\operatorname{Re}(w)=1-a-6e.
$$

For the allowed endpoint `a = 1` and `e > 0`, this is `-6e < 0`. Such points lie
outside `rowEulerRegion`, which explicitly requires `0 < Re(w)`. The domain
limitation is present in the existing repository definitions; it is not a loss
introduced by the uniqueness proof.

Moreover, `FiniteEulerRational` permits an arbitrary finite Laurent numerator
and denominator. Multiplying both by a factor which has no zeros on the
original region but vanishes outside it can preserve values on the original
region while changing the totalized quotient at its exterior zero. Equality on
the original region therefore does not establish pointwise equality of every
such presentation outside it. The pointwise theorem consequently makes no
assertion about those exterior denominator zeros. The new argument below
proves that the exceptional sets relevant to the contour integrals are null,
without asserting pointwise equality there.

## Entire finite tables and vertical null sets

[EntireVerticalZeros.lean](../../HeckeSkeleton/HighBinSupport/EntireVerticalZeros.lean)
uses the literal volume measure on `ℝ × (ℝ × ℝ)`. Its main statement is:

```lean
theorem entire_triple_ne_zero_ae_vertical {f : (ℂ × ℂ × ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {v : ℂ × ℂ × ℂ} (hv : f v ≠ 0)
    (σ : ℝ × ℝ × ℝ) :
    ∀ᵐ t : ℝ × (ℝ × ℝ),
      f ((σ.1 : ℂ) + (t.1 : ℂ) * Complex.I,
        (σ.2.1 : ℂ) + (t.2.1 : ℂ) * Complex.I,
        (σ.2.2 : ℂ) + (t.2.2 : ℂ) * Complex.I) ≠ 0
```

A nonzero entire function of one complex variable has a countable zero set.
The proof starts at the single supplied nonzero complex point, varies the first
coordinate on its vertical line, and then varies the second and third
coordinates successively. At each step the preceding nonzero value supplies
the base point for the next entire slice. The nonzero sets are measurable;
two applications of the actual product-measure almost-everywhere equivalence
assemble the three statements. No nonzero slice or vertical-line condition is
assumed separately.

`finiteEulerPolynomialValue_entire` applies this framework to the repository's
original finite Laurent polynomial definition. For a positive norm base `q`,
each monomial is a constant times

$$
\exp\!\left(\log(q)\,[-(e_1s+e_2w+e_3z)]\right),
$$

with the original integer exponents. Hence the numerator and denominator of
every finite rational table are jointly entire. This does not make its
quotient entire at a zero of its denominator.

[EntireQuotientVerticalAE.lean](../../HeckeSkeleton/HighBinSupport/EntireQuotientVerticalAE.lean)
proves `entire_quotients_ae_eq_vertical`: if two quotients of entire functions
agree on a nonempty complex open set, they agree almost everywhere on every
three-dimensional vertical real parameter space. The theorem supplies no
nonvanishing hypothesis for either denominator.

The proof handles identically-zero denominators explicitly, using Lean's
actual `x / 0 = 0` convention. If an entire quotient vanishes on the initial
open set, then either its denominator is identically zero or its numerator
vanishes on a smaller nonempty open set where that denominator is nonzero.
The entire identity principle gives the required global zero quotient in both
cases. When both denominators are nonzero entire functions, the proof first
finds a nonempty open set where both are nonzero, establishes the cross-product
identity there, extends that entire identity, and divides only away from their
proved vertical null zero sets.

`EntireVerticalZeros` passed its exact standalone native Lean build in
263.990 seconds. All five public theorem reports contain only `propext`,
`Classical.choice`, and `Quot.sound`; none contains `sorryAx`. The source SHA-256
is `4e17c7c55858f3646088d278c9d05ce1d3fdb769e6c891bb6bd7b8bebdc5a265`.
`EntireQuotientVerticalAE` also passed its exact native build in 91.902 seconds;
its public comparison theorem uses only the same three standard axioms. Its
source SHA-256 is
`3e87cd7dbf1100c1cd8bd22598015cd48860310bfb2f1ddb81c204dca98d5348`.
Together the two modules verify six public declarations. These pure checks
are separate from the arithmetic instantiation below.

## Cancelling only the common regular product

[ActualEulerRegularNonvanishing.lean](../../HeckeSkeleton/HighBinSupport/ActualEulerRegularNonvanishing.lean)
and
[ActualEulerVerticalAE.lean](../../HeckeSkeleton/HighBinSupport/ActualEulerVerticalAE.lean)
connect the preceding lemmas to the original Euler product. For each actual
finite exceptional set `F = rowExceptionalPrimes K S Q u`, the correction is
split as

$$
\operatorname{rowCorrection}
 = \left(\prod_{p\in F}\operatorname{finiteEulerRationalValue}_p\right)
   \left(\prod_{p\notin F}^{\prime}\operatorname{localRowCorrection}_p\right).
$$

This is the original product, including every marked or ramified exceptional
factor. Finite exceptional factors may be zero; the product-splitting theorem
does not divide them out.

On the original open domain `Re(s)>4`, `Re(w)>4`, `Re(z)>2`, the actual regular
factor satisfies

$$
\lVert f_p-1\rVert\le 88\,(Np)^{-7}<1.
$$

The bound uses the existing five-face Euler estimate at margin `6`, with the
proved fixed denominator margin at least `1/8`. Ideal counting proves
summability of the norm errors. Each factor is nonzero, so the regular product
over the complement of any finite set is nonzero. This gives
`localRowCorrection_tprod_compl_ne_zero_initial` without an exceptional-factor
nonvanishing premise.

Character calibration identifies the two row characters. The original
initial-series identities then identify their corrections, as in the original
region argument. Cancelling only the common nonzero regular product proves
`finiteExceptionalProduct_eq_initial_of_calibrated`. The finite product itself
is the quotient of the actual product numerator and actual product denominator,
including zero denominators, by `Finset.prod_div_distrib`. The entire-quotient
lemma therefore gives
`finiteExceptionalProduct_ae_eq_vertical_of_calibrated` for every vertical real
parameter space.

To return from the finite product to `rowCorrection`, the proof uses genuine
regular-product convergence throughout `sweptTube a e`. This convergence is
proved from `summable_exteriorPrime_swept_error` and the actual local bound,
under `51/100 ≤ a ≤ 1` and `0 < e ≤ 1/10000`. It is not assumed for the arbitrary
provider. Multiplying by the common regular product and the identical deleted
L-ratio yields `rowEulerContinuation_ae_eq_vertical_of_calibrated`.

## Literal contour equality, including negative w

The finite prime-tuple and subset sums in `compensatedRowMellinKernel` use only
finitely many mark sets. Intersecting their full-measure equality sets retains
every original slot factor, subset, Hecke coefficient, and norm power. Thus
`compensatedRowMellinKernel_ae_eq_vertical_of_calibrated` compares the full
original kernels. Its conclusion is with respect to volume on
`ℝ × (ℝ × ℝ)`, not a new measure on the kernel values.

The final contour statement is:

```lean
theorem rowContourBox_eq_of_calibrated_sweptTube
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E₁ E₂ : RowEulerData K S P)
    (h₁ : RowEulerCalibrationInput K S P ψ E₁)
    (h₂ : RowEulerCalibrationInput K S P ψ E₂)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z height σ ν zLine : ℝ)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hσ : ((σ : ℂ), (ν : ℂ), (zLine : ℂ)) ∈ sweptTube a e) :
    rowContourBox K S μ P ψ E₁ g T u Z height σ ν zLine =
      rowContourBox K S μ P ψ E₂ g T u Z height σ ν zLine
```

The ambient `K,S,μ` parameters and their measurable/Borel/Haar instances are
exactly those required by the original contour definition. Two applications of
`Measure.ae_ae_of_ae_prod`, restriction to each actual interval `Icc (-height)
height`, and three applications of `integral_congr_ae` prove this equality.
The factor `(2π)^(-3)` remains unchanged. No integrability assumption for the
arbitrary old provider is needed to compare the literal Bochner integrals.
The same full-volume kernel equality also restricts to any original measurable
height region.

Only the original `RowEulerCalibrationInput` is consumed on either side; the
comparison does not assume a stronger continuation or an almost-everywhere
identity. In particular, the original `FullHighEulerControl` hypothesis supplies
this calibration through `hEuler.1.initial`. The arithmetic side is supplied by
`targetRowEulerCalibrationInput` at the actual target data.

This remains an equality of contour integrals and almost-everywhere kernels.
It is not pointwise equality at every exterior denominator zero, a new
holomorphy claim for an arbitrary provider on the swept tube, or a construction
of the named expansion.

## Preserving an existing presentation

[ActualBoundaryCalibration.lean](../../HeckeSkeleton/HighBinSupport/ActualBoundaryCalibration.lean)
defines `arithmeticPresentationOfCalibration`. This replaces the Euler field
of an existing calibrated `ActualHighPresentation` and proves its two dependent
fields again. The `e` and `zeta` parameters, companions, all three heights,
labels, shifted pieces, and both numerical block-range fields are unchanged.

The already-calibrated character identifies both branches of the original
`highFixedRowBin`, including the floor bin. The new contour equality then
transports `shifted_identification` at `s=a+16e`, `w=1-a-6e`, `z=17/50`.
The initial line `s=B+20e` is in the same swept tube. Consequently
`presentationInitialBlock_eq_arithmeticPresentation` and
`wholeBinBoundary_eq_arithmeticPresentation` preserve the actual initial
blocks and the actual whole boundary. The latter is proved through the existing
identity “initial retained-block sum minus actual block values”; the sign is
unchanged.

`highBoundaryControl_of_calibrated_lower_geometry` therefore removes the
provider-record equality from the strongest boundary consumer. It uses the
same actual companion membership, lower contour-height and upper-detector gap,
and retained-block count as before, and produces exactly the same original
`HighBoundaryControl` proposition. No estimate is added to the presentation.
The named companion, height-choice, block-count, and actual expansion
obligations in [BOUNDARY.md](BOUNDARY.md) remain. All arithmetic declarations
in this new chain still await their complete native build and transitive
axiom audit.
