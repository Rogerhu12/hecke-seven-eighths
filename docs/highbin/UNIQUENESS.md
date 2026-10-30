# Uniqueness of the actual row Euler continuation

This addition proves uniqueness on the repository's original `rowEulerRegion`
without requiring two `RowEulerData` structures to be equal. It does not identify
arbitrary exceptional tables pointwise outside that region. In particular, it
does not remove the provider condition from the full high-bin boundary consumer,
whose contours include nonpositive real parts of the second coordinate.

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
the separate repository CI check of this addition is pending.

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

## Why this does not close the full boundary provider obligation

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
such presentation outside it. The present theorem makes no assertion about
that exterior set or its contour integrals.

The arithmetic provider has separately proved candidates for the larger swept
tube needed by the boundary argument. To transfer those facts to the named
`actualHighPresentation`, that presentation must be constructed with the actual
provider, or an appropriately justified equality on the required larger domain
must be established from additional genuine information about its tables. The
original `TRowEulerInput` alone does not provide this larger-domain statement.
The companion, height-choice, block-count, and actual expansion obligations in
[BOUNDARY.md](BOUNDARY.md) also remain.
