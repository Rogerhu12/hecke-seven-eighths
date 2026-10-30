# Actual Euler construction, calibration and analytic continuation

This document records the Euler chain on
`codex/highbin-euler-norm-boundary-20261030`. The main source endpoint is
`HeckeSkeleton.HighBinActualInitial.targetTRowEulerInput`, which constructs
the repository's original `TRowEulerInput` for the arithmetic Euler provider.
Its arithmetic dependency chain has **not yet passed a complete native build**.
The existing named obligations in `HeckeSkeleton.HighBin` remain separate:
`actualHighPresentation` has not been constructed with an identified Euler field.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.

## 1. Verification boundary

At commit `45b507f`, the native CI core build and public audit passed all
**57 modules and 442 public declarations**. The audit permits only
`propext`, `Classical.choice`, and `Quot.sound`.
The run is
[41133265844](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41133265844),
with core job `124329335921` and artifact `13013913423`. The recorded
`beyond_standard_axioms` result is empty. This covers the pure modules below, including
the complete joint-analytic limit theorem and corrected-region analytic
lemmas and `EulerRegionUniqueness`. It does not verify the actual arithmetic adapters.

| Component | Recorded native evidence | What remains unverified |
| --- | --- | --- |
| Finite Fourier tables, generator-unit invariance, contractive Gauss phases, rational local factors and scalar Euler bounds | The corresponding pure core modules passed individual Lean builds. The completed earlier core audit used only `propext`, `Classical.choice`, and `Quot.sound`. | Actual number-field instantiations are separate modules. |
| `PrimeBlockEuler` and `LocalSeriesFactorization` | Both passed individual native builds at `6e3d24ca4579aa615ef0a23769c1695cb8f4b55d`. | The actual four-ideal reindexing and calibration consumers have not been checked. |
| `LocalBlockSummation` | Passed a local standalone check of all 17 public declarations and an individual native build at `a2ea91210ece94f7969fb6bd060d4b95e7cd4ed0`. Its recorded axiom sets are the three standard axioms. | `ActualLocalBlockSummation` is an arithmetic instantiation and remains pending. |
| `JointAnalyticLimit` | The complete local single-module check passed in 321.551 seconds with exit code 0 and unchanged source. Both public theorem types and transitive axiom sets were checked; only the three standard axioms occur. Its individual native build and public audit also passed in the 57-module, 442-declaration CI check at `45b507f`. | This verifies the general three-variable limit theorem, not the complete arithmetic chain. |
| `EulerRegionAnalytic` and the original `rowEulerRegion` definition | The local 12-declaration check passed in 16.139 seconds; the complete native core build and public audit passed at `45b507f`. | The actual ideal-norm summability and number-field normal-product consumers remain pending. |
| `EulerRegionUniqueness` | All three public declarations passed the native core build and audit at `45b507f`: convexity, preconnectedness, and the joint analytic identity principle on the original region. | Its actual arithmetic consumers are separate modules; the theorem does not extend the region to nonpositive real part of `w`. |
| Actual prime-power Gauss/Poisson formulas, CRT, exponent indexing, initial calibration, corrected-region normal product and original `TRowEulerInput` constructor | Complete source candidates with static interface review | Native build and transitive axiom audit of the actual chain |
| Original `highInitialEulerControl` and `highExceptionalEulerControl` for `actualHighPresentation` | Existing obligations retained | Construction/identification of the named presentation, followed by the relevant native checks |

[REPORT.md](REPORT.md) records the toolchain, exact CI commits, run links and
verification protocol. The first complete arithmetic job timed out while
building deep dependencies; it had not reached the Euler chain above.
The source inventories are [core_modules.json](core_modules.json),
[core_public_declarations.json](core_public_declarations.json),
[actual_modules.json](actual_modules.json), and
[actual_public_declarations.json](actual_public_declarations.json).
The recorded source signatures below describe candidate declarations until
the corresponding actual modules and their axiom audits pass.

The successful `JointAnalyticLimit` check recorded original-source SHA-256
`992742c85b088e8e9fc334d3fe10b895e8c68a21c6ba2082856acea6661acf1f` and
generated verification-source SHA-256
`d72b9a7591f42c02141c06e2cfbfa8f9b62bbc6dbb1c8cd8711d469fdbadb272`.
The generated module contains the one source module plus its two public
type/axiom checks. This is distinct from a combined check with imports
hoisted from multiple source files.

## 2. Ambient data and the original objects

The arithmetic Euler declarations use the following ambient parameters:

```lean
(K : Type) [Field K] [NumberField K]
(S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
(P : ProbeData K S)
(psi : HeckeCharacter K)
(Q : Finset (ExteriorPrime K S))
(u : FrequencyRow K S)
```

`ProbeData` and `FrequencyRow` retain their existing repository definitions.
In particular, the row's unit sector and sixth-power-free ideal are part
of the actual row. Local residue-field and `Fintype` instances are constructed
for `𝓞 K ⧸ p.val.asIdeal`; their cardinality is identified with the actual
prime ideal norm. There are no new free local Gauss coefficients or row
character hypotheses in the constructed data.

The original
[initialRowEulerTerm](../../HeckeGeneral/Analysis/PhysicalProbeRows.lean)
is indexed by the four exterior ideals `(c, n, den, r)`. It retains:

* The squarefree condition on `c` and the whole-index mark on `A = c * n^3`.
* `thetaGamma ... c 2`, the actual Hecke coefficient of `A`, and the literal
  `finitePoissonFactor ... den A (poissonFrequency ... u r)`.
* The norm powers `Nc^(-1/2-s)`, `Nn^(-1-3s)`, `Nden^(-w)` and `Nr^(-6z)`.

`initialRowEulerSeries` remains the `tsum` of this term. It is not redefined
as an Euler product. The original
[rowEulerContinuation](../../HeckeGeneral/Analysis/PhysicalProbeContours.lean)
is the product of the deleted zeta factor at `6z`, the deleted row L-function
at `w`, the reciprocal deleted target-times-conjugate-row L-function at `s`,
and `rowCorrection`.

The source constructor

```lean
HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K S P psi
```

has the original type `RowEulerData K S P`. Its `rows` field is the actual
`arithmeticRowCharacterInput`; its exceptional factors have the original
`FiniteEulerRational` type. The finite Laurent definitions were moved verbatim
to [FiniteEulerRational.lean](../../HeckeGeneral/Analysis/FiniteEulerRational.lean)
and reexported by their original module.

## 3. From the original four ideals to actual prime blocks

The local exponent tuple is

```lean
FourExponent = (ℕ × ℕ) × (ℕ × ℕ)
```

with coordinates `(e, l, k, m)` for the valuations of `(c, n, den, r)`.
The completed index has valuation `t = e + 3*l`; the local frequency has
valuation `j + 6*m`, where `j = primeExponents u.ideal.val p.val`.

[ActualPrimeExponentIndex.lean](../../HeckeSkeleton/HighBinSupport/ActualPrimeExponentIndex.lean)
constructs an equivalence between the actual `FourIdealIndex K S` and
`ExteriorPrime K S →₀ FourExponent`, using the repository's ideal prime
exponents and their inverse. Its support-coprimality lemma identifies a
single prime block with the corresponding four actual prime-power ideals.

The finite CRT proof is in
[ActualEulerCRT.lean](../../HeckeSkeleton/HighBinSupport/ActualEulerCRT.lean).
The finite Poisson factor by itself carries a cross-symbol twist. The proof
combines it with `thetaGamma ... c 2`, uses `A = c*n^3`, and cancels the
resulting sixth-power phases. Its final
`fourIdeal_finite_coefficient_coprime_product` retains all four ideals and
the actual row frequency. The other block's `r` generator is removed using
sixth-power invariance for a unit in the relevant quotient. It is not
assumed to be a global unit.

[ActualInitialMultiplicative.lean](../../HeckeSkeleton/HighBinSupport/ActualInitialMultiplicative.lean)
then proves coprime multiplicativity and the value at the unit tuple for the
original unmarked coefficient. It also identifies the original mark with
`∀ p ∈ Q, 0 < e_p + 3*l_p`.

The definitions in
[ActualInitialEulerProduct.lean](../../HeckeSkeleton/HighBinSupport/ActualInitialEulerProduct.lean)
specialize this original coefficient:

```lean
primeBlockBase ... p n :=
  initialRowEulerTerm K S P psi ∅ u s w z (primeFourIdealIndex K S p n)

primeBlockTerm ... Q ... p n :=
  if p ∈ Q ∧ n.1.1 + 3 * n.1.2 = 0 then 0
  else primeBlockBase ... p n
```

A mark deletes every completed-unit term, including its denominator and
sixth-power descendants. It does not merely delete the all-zero tuple.
Absolute convergence is proved first for norms of the original four-ideal
term. The statement `initialRowEulerSeries_hasProd_primeBlocks` then uses
the actual index equivalence, true coprime factorization and the pure
`PrimeBlockEuler.hasProd_of_term_factorization`. Its only analytic-domain
assumptions are `4 < s.re`, `4 < w.re`, and `2 < z.re`.

## 4. Local tables and the required arithmetic calibration

At an exterior prime write

$$
q=N\mathfrak p,\quad
X=q^{-s},\quad Y=q^{-w},\quad V=q^{-6z},\quad
\theta=\operatorname{primeCoefficient}(\operatorname{thetaPeriod}(P,\psi),\mathfrak p).
$$

`G` is the actual `gaussFamily` for `thetaPrimeCharacter` and
`primeAddCharacter`. The unit phase `rho` is the value of that prime
character at `rowPrimeUnit`, constructed from the actual row frequency.

[ActualInitialLocal.lean](../../HeckeSkeleton/HighBinSupport/ActualInitialLocal.lean)
identifies the literal prime-block coefficient with `localBlockValue`.
It proves the squarefree zero branch `2 ≤ e`, the completed-unit branch
`t = 0`, and the positive branch `0 < t` from the actual prime-power
Fourier/Poisson formulas. Allowed generators are related by sixth powers
of global units; the proof performs the required quotient change of
variables. It does not identify additive phases solely from a quotient-ring
equivalence.

The completed-unit sum is

$$
U_j=\frac1{1-V}+
  \begin{cases}\dfrac{\rho Y}{1-\rho Y},&j=0,\\0,&j\ne0.\end{cases}
$$

The source theorem
`primeBlockTerm_tsum_eq_markedSeries` in
[ActualLocalBlockSummation.lean](../../HeckeSkeleton/HighBinSupport/ActualLocalBlockSummation.lean)
states that the local four-exponent sum is
`(if p ∈ Q then 0 else U_j) + markedSeries q theta G rho X Y V j`.
All summability hypotheses of the pure Fubini/reindexing argument are
discharged from the original absolute-convergence majorant.

Two arithmetic identifications are essential:

1. `eta q theta G = -theta * G 1 * G 2 / q` must be identified with
   `primeCoefficient K psi p.val`. This is proved in
   [ActualGaussCalibration.lean](../../HeckeSkeleton/HighBinSupport/ActualGaussCalibration.lean)
   using the existing `ThetaCalibrationInput.mixed_calibration` together
   with its unramifiedness statements for `Lambda` and `G`.
2. Away from the row support, `rho` is the actual row prime coefficient.
   Its inverse is its conjugate because it has norm one. Thus
   `eta * rho⁻¹` is precisely the original regular `D` phase.

`G 1 * G 5 = q` is proved in
[ActualGaussSigns.lean](../../HeckeSkeleton/HighBinSupport/ActualGaussSigns.lean).
The sign at `-1` comes from the actual twelfth root and the order-six
character. Normalized Gauss-family identification is used only at nonzero
residue classes of the exponent; the trivial-character Gauss sum is kept
in its separate branch.

The local-to-global calibration adds exactly these generic hypotheses:

```lean
(hP : AllowedGeneratorInput K S P.arithmetic)
(hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
(hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
```

`hP` supplies the permitted generator comparisons, and `hcal` supplies
the mixed arithmetic normalization. `hpsi` is needed to multiply the
target and conjugate-row prime coefficients even at row-ramified primes.
Two arbitrary ramified prime coefficients are not treated as multiplicative.
None of these hypotheses asserts the desired initial Euler identity.

[LocalSeriesFactorization.lean](../../HeckeSkeleton/HighBinSupport/LocalSeriesFactorization.lean)
contains the pure regular and ramified rational identities.
[ActualInitialCalibration.lean](../../HeckeSkeleton/HighBinSupport/ActualInitialCalibration.lean)
instantiates them in `actualValuationSeries_eq_localEuler` and obtains
`primeBlockTerm_tsum_eq_localEuler`. The independent genuine deleted Hecke
Euler products in
[ActualDeletedEulerProduct.lean](../../HeckeSkeleton/HighBinSupport/ActualDeletedEulerProduct.lean)
give `rowEulerContinuation_hasProd_initial`. Uniqueness of the two products
then proves `initialRowEulerSeries_eq_rowEulerContinuation`.

## 5. The exact corrected region and joint analyticity

The original region, now reexported from
[RowEulerRegion.lean](../../HeckeGeneral/Analysis/RowEulerRegion.lean), is

$$
\begin{gathered}
\Re s>\tfrac12,\quad\Re w>0,\quad\Re z>0,\\
\Re(s+w)>1,\quad\Re(s+z)>\tfrac56,\\
\Re(s+w+6z)>2,\quad\Re(w+6z)>1,\quad\Re(s+6z)>1.
\end{gathered}
$$

The branch retains the two mixed conditions already added upstream;
they control the actual `W*V` and `D*V` monomials. At each point, all five
summability faces have a positive common margin `delta`. The eleven actual
numerator monomials give

$$
|H_{\mathfrak p}-1|
\le \frac{11}{\mathrm{sweptTubeEulerMargin}}q^{-1-\delta}.
$$

Actual ideal-norm summability supplies the convergent prime majorant.
The same estimate on open sets with a fixed smaller margin gives
`rowCorrection_hasProdLocallyUniformlyOn_rowEulerRegion`. All finitely
many marked and row-ramified factors are retained in that product.
`rowCorrection_multipliable_rowEulerRegion` allows arbitrary finite
exceptional tables; joint analyticity of the individual factors and the
normal product is proved for the constructed arithmetic tables.
These statements are in
[ActualEulerRegion.lean](../../HeckeSkeleton/HighBinSupport/ActualEulerRegion.lean)
and its pure dependency
[EulerRegionAnalytic.lean](../../HeckeSkeleton/HighBinSupport/EulerRegionAnalytic.lean).

[JointAnalyticLimit.lean](../../HeckeSkeleton/HighBinSupport/JointAnalyticLimit.lean)
supplies the required theorem for the actual three-dimensional domain:

```lean
analyticOnNhd_of_tendstoLocallyUniformlyOn
  (hlim : TendstoLocallyUniformlyOn F f l U)
  (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) U)
  (hU : IsOpen U) : AnalyticOnNhd ℂ f U
```

Its implicit parameters are `{ι : Type*}`, `{l : Filter ι}` with `[l.NeBot]`,
`U : Set (ℂ × ℂ × ℂ)`, `F : ι → (ℂ × ℂ × ℂ) → ℂ`, and
`f : (ℂ × ℂ × ℂ) → ℂ`.

The proof first derives continuity and holomorphy of each scalar coordinate
slice from existing scalar locally uniform-limit results. Around each point
it chooses a closed polydisc inside `U`. On its product of boundary circles
`T`, the three Cauchy resolvents are jointly analytic as functions into the
Banach algebra `C(T, ℂ)`. Inversion is used at units because a point inside
the polydisc differs from every boundary coordinate. The iterated normalized
circle integral is a continuous linear functional on that algebra. Three
applications of the ordinary Cauchy formula identify its value with `f`.
This proves joint `AnalyticOnNhd`, including its power-series meaning; the
final field is not replaced by slice differentiability.

Finite zero Euler factors remain valid throughout. The proof does not take
a logarithm of the Euler product, divide by a Gauss numerator, or assume the
entire product is nonzero.

## 6. The original `TRowEulerInput` fields and target specialization

The source endpoint in
[ActualEulerInput.lean](../../HeckeSkeleton/HighBinSupport/ActualEulerInput.lean)
is:

```lean
theorem arithmeticTRowEulerInput (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) :
    TRowEulerInput K S P psi (arithmeticHighEulerData K S P psi)
```

| Original field | Source of its candidate proof |
| --- | --- |
| `initial.initial_absolute` | Norm summability of the literal four-ideal term for `4 < Re(s)`, `4 < Re(w)`, `2 < Re(z)` |
| `initial.initial_identity` | Actual CRT and prime-exponent rearrangement, exact local sums, mixed-Gauss calibration, and uniqueness of the genuine prime products |
| `local_product` | Actual ideal-norm summability of the eleven-monomial regular error, with finite exceptional modifications |
| `correction_analytic` | Joint analyticity of each actual local factor and the three-variable locally uniform-limit theorem |

The named specialization has the following source type, under only the
ambient number-field assumptions and the existing `TargetContext`:

```lean
theorem targetTRowEulerInput (c : HeckeSkeleton.TargetContext K) :
    TRowEulerInput K (HeckeSkeleton.places K c)
      (HeckeSkeleton.probeData K c) (HeckeSkeleton.targetCharacter K c)
      (arithmeticHighEulerData K (HeckeSkeleton.places K c)
        (HeckeSkeleton.probeData K c) (HeckeSkeleton.targetCharacter K c))
```

It uses the repository's `allowedGenerators`, `arithmeticCalibration`, and
`target_unramified_outside`. The statement names `places` and `probeData`
directly. They are the actual providers behind the corresponding
`targetData` projections; spelling them directly prevents unrelated
admitted expansion fields inside the full `targetData` definition from
being traversed merely because they occur in a theorem's type.

## 7. Exceptional estimates and the named presentation gap

For the constructed data,
`ActualEulerData.exceptional_unmarked_dynamic_bound` has explicit constant
`9` and cutoff `2`. It assumes `1/2 ≤ a`, `0 ≤ e`, `p` exceptional and
`p ∉ Q`, and the actual contour equations

$$
\Re s=a+16e,\qquad\Re w=1-a-6e,\qquad\Re z=17/50.
$$

Its conclusion is `|factor_p - 1| ≤ 9 q^(-10e)`, uniformly in all imaginary
parts. No Gauss nonvanishing condition is used. The complete marked
correction also has the source bounds `rowCorrection_coarse_bound` and
`exists_uniform_rowCorrection_subpower` on `sweptTube a e`, with
`51/100 ≤ a ≤ 1` and `0 < e ≤ 1/10000`. The latter gives, for every fixed
`eta > 0`, one constant multiplying `frequencyRowNorm^eta * markedBound^Q.card`.
The constant is uniform in the probe, target, row, marks, bin endpoint and
point of the stated swept tube. These swept-tube estimates do not replace
the distinct whole-region analyticity argument above.

[ActualExceptionalControl.lean](../../HeckeSkeleton/HighBinSupport/ActualExceptionalControl.lean)
provides a consumer of the original `HighExceptionalEulerControl` with
constants `9, 2`, under the explicit data identity

```lean
P.euler = arithmeticHighEulerData K _
  (targetData K c).probe (targetCharacter K c)
```

The named `actualHighPresentation K c` remains an admitted construction.
Its type permits an arbitrary `RowEulerData`; no equality of its `euler`
field with the constructed arithmetic tables follows from the fields
currently provided. Consequently `targetTRowEulerInput` is not, by itself,
a proof of the original `highInitialEulerControl`, and the exceptional
consumer does not close `highExceptionalEulerControl` for the named
presentation. Analytic uniqueness can compare correction functions when
both providers already satisfy the original Euler input, but it does not
identify each individual stored finite table. This comparison is on the
original region, which requires `Re(w) > 0`; some high-bin contours also
have negative `Re(w)`. It therefore does not by itself supply the actual
negative-`w` continuation or its finite-table regularity. The
constructor/identification work and the complete native arithmetic
verification must remain explicit before these original obligations are
reported as discharged.

## Corrected-region normal product: separate pure verification

`EulerRegionProduct.lean` uses the actual `explicitLocalEuler` four-case
family and the unchanged repository `rowEulerRegion`. Its complete hypotheses
are elementary phase norm bounds, `2 ≤ q i`, and summability of `q i ^ (-σ)`
for every `σ > 1`. It proves both normal convergence and full joint
`AnalyticOnNhd`; neither is an input hypothesis. The finite sets `R` and `Q`
retain ramified and marked zero factors literally. The declaration statements are:

```lean
theorem explicitEuler_hasProdLocallyUniformlyOn_rowEulerRegion
    {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5)
    (hq : ∀ i, 2 ≤ q i) (hW : ∀ i, ‖cW i‖ ≤ 1)
    (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable (fun i => (q i) ^ (-σ))) :
    HasProdLocallyUniformlyOn (explicitLocalEuler R Q q cW cD cE P j)
      (fun v => ∏' i, explicitLocalEuler R Q q cW cD cE P j i v)
      rowEulerRegion

theorem explicitEuler_analyticOnNhd_rowEulerRegion
    {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5)
    (hq : ∀ i, 2 ≤ q i) (hW : ∀ i, ‖cW i‖ ≤ 1)
    (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable (fun i => (q i) ^ (-σ))) :
    AnalyticOnNhd ℂ
      (fun v => ∏' i, explicitLocalEuler R Q q cW cD cE P j i v)
      rowEulerRegion
```

The ambient namespace is `HeckeSkeleton.HighBinContinuation`; the only
implicit type/instance parameters are `{ι : Type*} [DecidableEq ι]`.
`ActualEulerRegion.rowCorrection_hasProdLocallyUniformlyOn_rowEulerRegion`
now applies this theorem using the actual ideal-norm summability and then
transports finite products and their limits through the proved local-factor
identity on the original region. No identity outside that region is used.

The exact new source body passed Lean 4.35.0-rc3 in a combined dependency
wrapper in **18.706 seconds**, with both public types and axiom sets printed.
Both use only `propext`, `Classical.choice`, and `Quot.sound`. The wrapper
imports the previously compiled exact `EulerRegionAnalytic` and
`JointAnalyticLimit` bodies; this check is distinct from a native separate
module build. That separate native build and both public type/axiom audits
have now also passed in the 57-module core CI at `45b507f`. Source SHA-256: `65790197956fee62f0753b5f69df9c30e9bf54d50e261c2c9a5ded7d57323134`.
