# Boundary implementation and remaining presentation obligations

The new boundary chain is connected to the repository's literal
`compensatedRowMellinKernel`, `rowContourBox`, fixed frequency-row bins, and
`wholeBinBoundary`. Its arithmetic endpoint gives an arbitrary external-height
tail with fixed scale and height degrees. The original named
`HeckeSkeleton.highBoundaryControl` is **not closed by this checkpoint**: its
specific presentation still needs an arithmetic-provider identity, companion
membership, actual height choices, and a retained-block count.

## Verification status

The pure modules `BoundaryRectangle`, `BoundaryBox`, `BoundaryTailAssembly`,
`LogFourierDecay`, `PositiveNormalizer`, `BoundaryTupleScalar`,
`BoundaryEulerCoarse`, and `HighNormFormHeight` have passed individual native
Lean compilation in the core verification jobs. The corresponding completed
core audits reported only `propext`, `Classical.choice`, and `Quot.sound`.
These checks establish the generic analytic and scalar arguments; they do
not establish the actual arithmetic instantiations below.

The actual boundary chain has **not yet passed a complete native build or its
transitive axiom audit**. The first full actual build reached
`ActualOrbitalRapidDecay` and reported two function-equality elaboration errors.
Those two source errors have been repaired by proving explicit pointwise
function equalities and rewriting the original moment/Fourier evidence. The
full build subsequently timed out while compiling other dependencies. A
repaired source file, a static review, or a downstream `#print axioms` command
in a file that has not built successfully is not a passing verification.

The source signatures reproduced below are extracted from the actual source
files. They describe the current candidate proofs, including their remaining
hypotheses. Verification status must be updated from the relevant successful
CI artifact rather than inferred from this document.

## Original objects and normalization

[PhysicalProbeContours.lean](../../HeckeGeneral/Analysis/PhysicalProbeContours.lean)
defines the kernel and the contour. Every compensated term retains its actual
prime tuple, selected and marked subsets, Hecke coefficient, all norm powers,
and its marked `rowEulerContinuation`. The denominator remains
`physicalResidueNormalizer * primeNormalizer` with Lean's original totalized
division. The boundary argument does not insert a lower bound for the prime
normalizer or divide by a possibly zero finite Gauss polynomial.

The original contour is

```lean
rowContourBox K S μ P ψ E g T u Z height σ ν zLine =
  (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
    ∫ ts in Icc (-height) height,
      ∫ tw in Icc (-height) height,
        ∫ tz in Icc (-height) height,
          compensatedRowMellinKernel K S μ P ψ E g T u Z
            ((σ : ℂ) + ts * Complex.I)
            ((ν : ℂ) + tw * Complex.I)
            ((zLine : ℂ) + tz * Complex.I)
```

Here the `T` argument is a finite ray-character filter. In the tail theorems,
`Text` denotes the real external height. These are distinct parameters.
`H` is the actual contour half-height, and `U` is the upper-zero detector
height. The selected-zero height remains a separate parameter of the bin.

[ActualContourTransport.lean](../../HeckeSkeleton/HighBinSupport/ActualContourTransport.lean)
introduces `HighBinBoundary.ActualContour.rowKernel` solely to group the two
unchanged `w,z` height coordinates. Its
`rowContourBox_eq_parameterBox` proves the Fubini identification with the
original nested integral and retains the factor `(2π)^(-3)`.

`rowContourBox_rectangle_identity` identifies the original right contour
minus the final left contour with

$$
(2\pi)^{-3}\int_{[-H,H]^2}
 i\left(\int_l^r F(x-iH,q)\,dx-
         \int_l^r F(x+iH,q)\,dx\right)\,dq.
$$

The row, ray filter and finite prime subsets are held fixed. This is a move
of the original fixed-bin integrand before any amplitude-label subdivision.

The general transport theorem explicitly requires the following data. The
arithmetic endpoint later supplies its analytic requirements.

| Requirement | Exact source condition |
| --- | --- |
| Probe and measures | A number field, finite `S`, the original `ProbeData`, Borel structures on the norm-one and finite local spaces, and the supplied additive Haar measures `μ` |
| Companions | `hΘ : 1 ∈ Θ` |
| No pure-norm pole | Both `E.rows.character u` and `ψ * conjugate (E.rows.character u)` differ from every `heckeNormTwist K t` |
| Rectangle | `0 < Z`, `0 ≤ H`, `H ≤ U`, `1 / 2 ≤ α`, `α < l`, and `l ≤ r` |
| Zero detector | `rowZeroBelow K S₀ ψ Θ P E u U α` |
| Vertical-face integrability | Derived in `rowKernel_integrable_heightBox` from actual factor continuity; correction continuity is supplied for every finite mark set on the two endpoint height boxes |
| Holomorphy | Correction differentiability in `s` for every finite mark set on the closed swept rectangle; the deleted L denominator is handled using the actual detector |

The stronger quantitative transport theorem
`HighBinBoundary.ActualContour.exists_rowContourBox_external_tail` also has
`1 ≤ Z`, `1 ≤ Text ≤ H`, `1 / 2 ≤ l ≤ r ≤ 2`, and `-1 ≤ ν ≤ 1`.
At this general layer it consumes a nonnegative pointwise bound `M` for the
actual marked Euler continuations on the horizontal faces and concludes

$$
\lVert\operatorname{Box}(r)-\operatorname{Box}(l)\rVert
 \le C_N Z^5 M\,|r-l|\,T_{\rm ext}^{-N}.
$$

This pointwise Euler bound is an intermediate requirement, not a hypothesis
of the arithmetic endpoint below.

## Why the external tail has every order

The Gaussian in the original kernel is coupled:
`exp (-((s.im + z.im)^2))`. It does not decay uniformly on a horizontal face
by itself, because `z.im` can cancel `s.im`. The verified
`gaussian_corner_no_decay` records this obstruction.

The proof instead combines the coupled Gaussian with arbitrary vertical
Mellin decay of the original additive test. The actual profile chain is:

1. `ActualOrbitalRapidDecay.exists_orbitalMellin_rapid_bound` obtains all
   logarithmic Euler derivatives and their weighted L1 bounds from the
   repository's Schwartz-tensor and positive-moment theorems, then uses the
   verified Fourier integration-by-parts argument in `LogFourierDecay`.
2. `ActualAdditiveMellinRapidDecay.additiveMellin_eq_orbitalMellin` identifies
   the physical additive Mellin integral with that profile. The infinite
   Schwartz Fourier transform and finite locally constant compact-support
   Fourier transforms are the original transforms. Their Haar masses remain
   in the finite profile. The `ActualAdditiveBorel` theorems transport only
   Borel structures, retaining the supplied Haar measures.
3. `ActualKernelEnvelope.exists_compensated_kernel_envelope` bounds the
   literal complete compensation sum by
   `C * Z^5 * M * exp(-((s.im+z.im)^2)) * ‖additiveMellin ... z‖`.
   This includes the zero-normalizer branch of the original definition.
4. `BoundaryTailAssembly.coupled_box_external_tail` uses the profile order
   `N + 2`. The extra two derivatives absorb the two-dimensional height-box
   mass through `H^2 / (1+H)^(N+2) ≤ Text^(-N)` for `1 ≤ Text ≤ H`.

Increasing `N` changes the profile seminorm constant. It does not increase
the powers of `Z`, the row norm, or the detector height.

## Arithmetic endpoint: actual rows and actual Euler data

The main arithmetic theorems are in
[ActualBoundaryEstimate.lean](../../HeckeSkeleton/HighBinSupport/ActualBoundaryEstimate.lean),
namespace `HighBinBoundary.ActualEstimate`. Their ambient parameters are

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K S₀)]
  [BorelSpace (sLocalNormOneGroup K S₀)]
variable [∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S₀) → Measure (p.val.adicCompletion K))
variable [∀ p : S₀, (μ p).IsAddHaarMeasure]
```

The provider in the conclusion is exactly
`HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K S₀ P ψ`.
The fixed height degree is defined in
[ActualLRatioStrip.lean](../../HeckeSkeleton/HighBinSupport/ActualLRatioStrip.lean):

```lean
def HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree : ℕ :=
  6 * Fintype.card (InfinitePlace K)
```

The strip argument gives a deleted L-ratio bound
`C * frequencyRowNorm^3 * (2+U)^boundaryHeightDegree`. Its conductor bound
uses the actual canonical row character and the actual ideal radical. The
coarse Euler-product estimate contributes `frequencyRowNorm^4`, with at most
`g.slots` marked primes. Their product is the row exponent `7` below.
The totally-complex field property follows from the primitive twelfth root
in `P.arithmetic`; it is not an additional field hypothesis in these endpoints.

### Exact single-row signature

```lean
theorem exists_arithmetic_rowContourBox_external_tail
    (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S₀,
      Z ^ d ≤ frequencyRowNorm K S₀ u → ∀ a B H U Text : ℝ,
      51 / 100 ≤ a → a ≤ B → B ≤ 1 →
      1 ≤ Text → Text ≤ H → H + 3 / 2 ≤ U →
      rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u U (a + 2 * e) →
      ‖rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ) g T u Z H
          (B + 20 * e) (1 - a - 6 * e) (17 / 50) -
        rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ) g T u Z H
          (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
        C * Z ^ 5 * frequencyRowNorm K S₀ u ^ 7 *
          (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K * Text ^ (-(N : ℝ))
```

The cutoff `Z₀` precedes `N`. The constant may depend on `N` and on the fixed
ambient data, probe, character, companion set, geometry and `e`. It is uniform
in the ray filter, scale, shell exponent, row, bin endpoints and allowed
heights quantified after `C`.

There is no conductor-bound, correction-regularity, marked-Euler-bound,
normalizer-lower-bound, row-count, or contour-tail premise in this signature.
The actual buffered detector and the explicit rectangle geometry remain
necessary inputs. The non-norm-twist exclusions are derived internally for
all sufficiently large rows.

### Exact fixed-family signature

```lean
theorem exists_arithmetic_fixedRows_external_tail
    (P : ProbeData K S₀) (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ R : Finset (FrequencyRow K S₀), R ⊆ frequencyRows K S₀ (2 * Z ^ d) →
      (∀ u ∈ R, Z ^ d ≤ frequencyRowNorm K S₀ u) → ∀ a B H U Text : ℝ,
      51 / 100 ≤ a → a ≤ B → B ≤ 1 →
      1 ≤ Text → Text ≤ H → H + 3 / 2 ≤ U →
      (∀ u ∈ R, rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ)
        u U (a + 2 * e)) →
      ‖(∑ u ∈ R, rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
          g T u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50)) -
        (∑ u ∈ R, rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ)
          g T u Z H (a + 16 * e) (1 - a - 6 * e) (17 / 50))‖ ≤
        C * Z ^ 13 * (2 + U) ^ ActualLRatioStrip.boundaryHeightDegree K *
          Text ^ (-(N : ℝ))
```

Here `R` is the actual fixed finite family of frequency rows. The envelope
membership and lower shell bound are retained explicitly. The proof invokes
`frequencyRows_linear_count`; it does not assume a cardinality estimate.
For `d ≤ 1`, both the row norm and the count are bounded by fixed multiples
of `Z`. Consequently the scale exponent is `5 + 7 + 1 = 13`. The two contour
sums use exactly the same `R`.

## From fixed bins to the original whole boundary

[ActualBoundaryPresentation.lean](../../HeckeSkeleton/HighBinSupport/ActualBoundaryPresentation.lean),
namespace `HeckeSkeleton.HighBinBoundaryPresentation`, uses the original
`ActualHighPresentation K c` and `HighBlockIndex K c Z T`.

`presentationBoundaryPiece` is exactly one initial-minus-final summand of
`wholeBinBoundary`. The theorem `wholeBinBoundary_eq_sum` is `rfl`; no alternate
boundary is substituted. `highFixedRowBin_member_data` obtains the envelope,
strict lower shell bound and upper-zero detector from both the floor-bin
branch and the live buffered-bin branch. It keeps the presentation's original
selected height. No selected-height growth assumption is needed for this
boundary estimate because only the upper detector enters the contour move.

The existing presentation fields give `e ≤ 1/10000`, `d ≤ 1`, and the required
bin range, through `presentation_e_small`, `presentation_shell_le_one` and
`P.bin_range`. The piece theorem additionally requires

```lean
hEuler : P.euler = arithmeticHighEulerData K _
  (targetData K c).probe (targetCharacter K c)
hcompanions : 1 ∈ P.companions
hδ : 0 < δ
```

and, for each retained block, `1 ≤ δ*T`,
`δ*T ≤ P.contourHeight Z T b`, and
`P.contourHeight Z T b + 3/2 ≤ P.upperHeight Z T b`.
It applies the fixed-row estimate with `Text = δ*T` and absorbs `δ^(-N)` into
the tail constant.

`exists_wholeBinBoundary_heightSum_bound` then gives the literal finite sum:

$$
\lVert\operatorname{wholeBinBoundary}(Z,T)\rVert
 \le C_N Z^{13}
 \left(\sum_{b:\operatorname{HighBlockIndex}(Z,T)}(2+U_b)^k\right)T^{-N},
 \qquad k=6\,\#\operatorname{InfinitePlace}(K).
$$

This intermediate conclusion displays the remaining geometric mass. It
contains neither amplitude labels nor an assumed boundary estimate.

## Power-height consumer with the original quantifier order

The repository defines `HighBoundaryControl K c P` as
`PowerHeightTailBound (wholeBinBoundary K c P)`. In particular, the required
order is

```lean
∃ A R ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
  ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∀ N : ℕ,
    ∃ k Z₀ : ℝ, 0 < k ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ‖wholeBinBoundary K c P Z (Z ^ τ)‖ ≤
        k * Z ^ R * (1 + Z ^ τ) ^ A * (Z ^ τ) ^ (-(N : ℝ))
```

The following exact source signature follows that order. Polynomial degrees
are fixed first. After `τ`, geometric constants and a geometric threshold may
be chosen. The hypotheses concern the actual block count and heights only
at `T = Z^τ`; they do not require a single constant over all real heights
`1 ≤ T ≤ Z^ceiling`.

```lean
theorem highBoundaryControl_of_arithmetic_power_geometry
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ)
    (AB RB AU RU ceiling : ℝ)
    (hAB : 0 ≤ AB) (hAU : 0 ≤ AU) (hceiling : 0 < ceiling)
    (hgeometry : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
      ∃ Cb Cu Zg : ℝ, 0 < Cb ∧ 0 < Cu ∧ 1 ≤ Zg ∧
        ∀ Z : ℝ, Zg ≤ Z →
          (((targetData K c).expansion Z (Z ^ τ)).blockCount : ℝ) ≤
              Cb * Z ^ RB * (1 + Z ^ τ) ^ AB ∧
          ∀ b : HighBlockIndex K c Z (Z ^ τ),
            δ * (Z ^ τ) ≤ P.contourHeight Z (Z ^ τ) b ∧
            P.contourHeight Z (Z ^ τ) b + 3 / 2 ≤ P.upperHeight Z (Z ^ τ) b ∧
            2 + P.upperHeight Z (Z ^ τ) b ≤ Cu * Z ^ RU * (1 + Z ^ τ) ^ AU) :
    HighBoundaryControl K c P
```

Its fixed output degrees are

$$
A=A_B+A_U k,\qquad R=13+R_B+R_U k.
$$

The proof chooses `Zδ = (1/δ)^(1/τ)` so that `Z ≥ Zδ` implies
`1 ≤ δ*Z^τ`. Its final threshold is the maximum of the arithmetic cutoff,
the geometric threshold and `Zδ`. The final constant is
`C_N * Cb * Cu^k`. Neither output degree depends on `τ` or `N`.
`AB` and `AU` must be nonnegative; `RB` and `RU` are arbitrary real scale
exponents, exactly as in the signature.

The older `highBoundaryControl_of_arithmetic_geometry` remains as a wrapper
for stronger geometry uniform over the full height range. It derives the
new power-height hypotheses and does not change the original definition of
`HighBoundaryControl`.

### Concrete buffered heights

`buffered_height_geometry` proves the scalar geometry for

$$
H_{\mathrm{int}}=\max(T,Z^\kappa),\qquad
H=\delta H_{\mathrm{int}},\qquad
U=3(i+1)H_{\mathrm{int}},\qquad i\le I,
$$

under `1 ≤ Z`, `1 ≤ T`, `0 ≤ κ`, and `0 < δ ≤ 1`. It proves both
`δ*T ≤ H`, `H+3/2 ≤ U`, and

$$
2+U\le (3(I+1)+2)Z^\kappa(1+T).
$$

The exact power-height specialization is:

```lean
theorem highBoundaryControl_of_buffered_power_schedule
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions)
    (δ κ : ℝ) (I : ℕ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ)
    (AB RB ceiling : ℝ) (hAB : 0 ≤ AB) (hceiling : 0 < ceiling)
    (hgeometry : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
      ∃ Cb Zg : ℝ, 0 < Cb ∧ 1 ≤ Zg ∧
        ∀ Z : ℝ, Zg ≤ Z →
          (((targetData K c).expansion Z (Z ^ τ)).blockCount : ℝ) ≤
              Cb * Z ^ RB * (1 + Z ^ τ) ^ AB ∧
          ∀ b : HighBlockIndex K c Z (Z ^ τ), ∃ i : ℕ, i ≤ I ∧
            P.contourHeight Z (Z ^ τ) b =
              δ * HighBinVerified.NormForm.internalHeight Z (Z ^ τ) κ ∧
            P.upperHeight Z (Z ^ τ) b =
              3 * ((i : ℝ) + 1) * HighBinVerified.NormForm.internalHeight Z (Z ^ τ) κ) :
    HighBoundaryControl K c P
```

Its output degrees are `A = AB + k` and `R = 13 + RB + κ*k`. The index bound
`I`, the internal exponent `κ`, and `δ` are chosen before `τ` and `N`.
The theorem requires these formulas to be the **actual presentation's**
contour and upper heights. It does not replace the named presentation by
one with convenient unrelated heights.

## What remains for the named `highBoundaryControl`

[HighBin.lean](../../HeckeSkeleton/HighBin.lean) still declares
`actualHighPresentation` with an admitted construction. The following
obligations are not supplied by the new consumer:

| Named-presentation obligation | Why it is still needed |
| --- | --- |
| `P.euler = arithmeticHighEulerData ...` | `ActualHighPresentation.euler` is an arbitrary `RowEulerData` field; the structure does not identify it with the constructed finite-table provider. |
| `1 ∈ P.companions` | The companion field is a finite set with no membership field. The actual upper-zero argument needs the trivial companion. |
| Buffered contour and detector heights | The three height functions are arbitrary fields. No field gives the contour lower bound, the `3/2` upper-detector gap, or polynomial height growth. |
| Retained-block count | `TargetData.rows_in_norm_envelope` bounds which rows can occur; it does not bound how many blocks the expansion repeats or retains. `Expansion.expansion_blockCount` remains an upstream admitted obligation. |
| Original block and label construction | `Base.highExpansion` is admitted. The real shell/bin selection, selected-height subdivisions, actual label contributions and their integral identifications must be constructed together. |

The presentation's `shell_range`, `bin_range`, `rows_in_bin`,
`block_identification`, and `shifted_identification` are retained. No empty
block family, zeroed contour, artificial amplitude, or assumed final boundary
estimate is used to bypass their construction. The original
`HeckeSkeleton.highBoundaryControl` theorem has not been replaced by one of
the conditional consumers above.

There is also a transitive-dependency distinction. The generic arithmetic
row estimates are stated for actual `ProbeData`, actual row objects and the
constructed arithmetic Euler provider. The presentation consumers necessarily
mention `targetData K c`, whose definition includes the admitted
`Base.highExpansion` and support construction. Lean's axiom collector follows
both declaration types and values, including such referenced definitions.
Therefore a presentation consumer can report upstream `sorryAx` even though
its own proof contains no admission. It must not be advertised as an
admission-free closure of the named HIGHBIN obligation.

## Reproduction

The repository verification scripts record each public declaration's exact
type and transitive axiom set. The relevant commands, run from the repository
with its pinned Lean/mathlib environment, are:

```sh
python3 scripts/highbin_verify.py core
python3 scripts/highbin_verify.py mellin
python3 scripts/highbin_verify.py actual
```

The actual command builds the real `HighBinSupport` and `HighBin` entrypoints.
A successful actual build is still needed before its public-type and axiom
report can establish the arithmetic endpoint's verification status. Consult
`actual-build.log`, `actual-public-types-and-axioms.log`, and
`actual-axioms.json`; additional upstream axioms are reported explicitly.
