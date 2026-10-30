# Actual HIGHBIN norm form: statements, hypotheses and verification boundary

This document records the norm-form implementation on
`codex/highbin-euler-norm-boundary-20261030`. It describes declarations in
the repository's actual arithmetic, prime-window and contour definitions.
It does **not** certify `HighBin.highShiftedNormForm`: the original named
presentation and expansion identifications remain missing.

The status below is recorded on 2026-10-30. The exact source signatures in
the appendix are candidates until the corresponding individual actual
modules have elaborated successfully. A source declaration with a proof
body is not, by itself, an elaborated theorem or an exact-type audit.

## 1. Verification status

| Part | Recorded result | Scope of the result |
|---|---|---|
| `ActualNormFormHigherPrimePowers`, `ActualNormFormMellinInversion`, `ActualNormFormPrimeDetector`, `ActualNormFormUniformMellin` | Native separate-module build and all 55 public declaration audits passed at `6e3d24ca4579aa615ef0a23769c1695cb8f4b55d`, and again at `a2ea91210ece94f7969fb6bd060d4b95e7cd4ed0` | Their axiom sets contain only `propext`, `Classical.choice`, `Quot.sound`; `mellin-axioms.json` has an empty `beyond_standard_axioms` object. |
| `ActualOrbitalRapidDecay` and the four preceding Mellin modules | Native five-module / 59-public-declaration audit passed at `c71511a569ed8b98c243b66ead8d8ec8c83d59b9` | All axiom sets contain only the three standard axioms; [verified_mellin_axioms.json](verified_mellin_axioms.json) preserves the full mapping. |
| The same Mellin dependency chain, combined locally | 40 source files and 577 public declarations passed | This is additional combined-source evidence, distinct from separate-module verification. |
| `HighNormFormScalar`, including `exists_full_normForm_parameter_budget` | The native core run at `a2ea91210ece94f7969fb6bd060d4b95e7cd4ed0` compiled the file successfully; the subsequent run at `03410972118500ef9fdd9ce4045d964bed6cd167` passed all 55 modules and 438 public declaration audits | Its printed parameter-budget axiom set is the same three standard axioms. The current core run references are maintained in `REPORT.md`; this core success does not verify the deep actual norm-form chain. |
| Actual window detector, zero-free prime contour/cap, complete-slot correction, sharp factors, amplitude construction, kernel, integral, label grouping and target presentation consumer | Source implementation and static interface review only | The complete actual build had not reached these declarations. Their displayed source signatures and their transitive axiom sets have **not** been confirmed by Lean. |
| Original `HighShiftedNormForm K c (actualHighPresentation K c)` | Not discharged | The original `HB-NORMFORM`, `HB-PRESENT` and `D-EXPANSION` admissions are not replaced by this chain. |

The reproducible module lists and audit machinery are
[mellin_modules.json](mellin_modules.json),
[mellin_public_declarations.json](mellin_public_declarations.json),
[core_modules.json](core_modules.json),
[actual_modules.json](actual_modules.json), and
[highbin_verify.py](../../scripts/highbin_verify.py). The complete status
and native run references are maintained in [REPORT.md](REPORT.md).

The initial actual job's approximately 65-minute timeout occurred while
building deep repository dependencies. It is neither a proof failure nor
a successful verification of the unreached norm-form modules.

### Pinned integral and target API review

A second source-level review compared `ActualNormFormIntegral` and
`ActualNormFormTarget` with the exact Mathlib revision in
`lake-manifest.json`, `0493595ecd5da8ef14742febab99728f98e948e8`, and
Lean `v4.35.0-rc3`. It found no further definite API correction in those
two files. This is static evidence; it does not change their unelaborated
status above.

| Call or dependency | Exact source-level check |
|---|---|
| Fubini slices | [`Integral/Prod.lean`](https://github.com/leanprover-community/mathlib4/blob/0493595ecd5da8ef14742febab99728f98e948e8/Mathlib/MeasureTheory/Integral/Prod.lean) defines `prod_right_ae` as almost-everywhere integrability in the right variable for fixed left variable. This is the required `(tw,tz)` slice at fixed `ts`; `prod_left_ae` has the opposite direction. Both applications of `integral_prod f hf` use the corresponding product measure. |
| Restricted product measure | [`Measure/Prod.lean`](https://github.com/leanprover-community/mathlib4/blob/0493595ecd5da8ef14742febab99728f98e948e8/Mathlib/MeasureTheory/Measure/Prod.lean) gives `prod_restrict`; `prod.measureSpace` defines product volume by `volume.prod volume`, and `volume_eq_prod` is `rfl`. Thus the nested restricted measures have the same actual product-space volume used by `ae_restrict_mem`. |
| Finite mass and norm bound | The same product file supplies the finite-product-measure instance and `measureReal_prod_prod`. [`Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/0493595ecd5da8ef14742febab99728f98e948e8/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean) requires `IsFiniteMeasure` and an almost-everywhere constant bound for `norm_integral_le_of_norm_le_const`; its result is `C * μ.real univ`, in the order used here. The actual integrability proof is separately retained for Fubini. |
| Target measure instances | The local instances are the original `ProbeMeasures.normOneSpace`, `normOneBorel`, `localSpace`, `localBorel`, and `haar_isAddHaar` projections, with the same types as [HighBin.lean](../../HeckeSkeleton/HighBin.lean). Their definitions reduce to the same target data rather than introducing new Borel or Haar choices. |
| Dependent amplitude choice | [`Tactic/Choose.lean`](https://github.com/leanprover-community/mathlib4/blob/0493595ecd5da8ef14742febab99728f98e948e8/Mathlib/Tactic/Choose.lean) retains propositional arguments for ordinary `choose`; removal of those arguments is a `choose!` feature. Hence the chosen family retains the displayed scale, height, label-membership and row-membership proof arguments, matching `PresentationFullSlotAmplitudes`. |

## 2. Actual data, typeclasses and notation

### Arithmetic statements

The slot, conductor and amplitude modules use exactly:

```lean
(K : Type) [Field K] [NumberField K]
(S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
(psi : HeckeCharacter K)
(companions : Finset (HeckeCharacter K))
(hcomp : (1 : HeckeCharacter K) ∈ companions)
(P : ProbeData K S)
(g : PrimeWindowGeometry)
(hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
(hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
```

`ProbeData`, `PrimeWindowGeometry` and `ThetaCalibrationInput` retain all
their existing fields; they are not replaced by new analytic records.
`hcal` is an arithmetic calibration hypothesis and `hpsi` is the original
outside-`S` unramifiedness hypothesis. At the named target, the repository
provides `HeckeSkeleton.arithmeticCalibration` in
[Theta.lean](../../HeckeSkeleton/Theta.lean) and
`target_unramified_outside` in [Base.lean](../../HeckeSkeleton/Base.lean).
The generic norm-form statements do not silently manufacture either
hypothesis.

Throughout, the Euler provider is the concrete

```lean
arithmeticHighEulerData K S P psi
```

and its character is the actual `arithmeticRowCharacter K S P u`. A free
Euler provider, a proposed prime-sum estimate, a conductor estimate, or a
row-integral estimate is not an input to the main kernel/label theorems.
The cap and norm-form statements use the empty ray filter `∅`. This is
the original target choice: `Base.rayFilter` is defined to be `∅`.
The new
[ActualNormFormTarget.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormTarget.lean)
records the target projection equality by `rfl` and instantiates the
row-integral theorem with the actual target probe, character, geometry,
Haar measures, calibration and outside-`S` unramifiedness. No additional
finite-filter estimate or replacement arithmetic input is required for
this specialization.

### Kernel and integral statements

The kernel, integral and label modules use `S` as a finite set and add
the original Borel and Haar data:

```lean
(K : Type) [Field K] [NumberField K]
(S : Finset (HeightOneSpectrum (𝓞 K)))
-- S₀ denotes (S : Set (HeightOneSpectrum (𝓞 K))).
[MeasurableSpace (sLocalNormOneGroup K S₀)]
[BorelSpace (sLocalNormOneGroup K S₀)]
[∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
[∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
(μ : (p : S₀) → Measure (p.val.adicCompletion K))
[∀ p : S₀, (μ p).IsAddHaarMeasure]
```

The arithmetic inputs above are then taken over `S₀`. Finiteness of
`S₀` is inferred from the finite set. Total complexity of the number
field is derived from `P.arithmetic.primitive12` where the actual
additive Mellin theorem needs it; it is not an extra caller hypothesis.

For the formulas below, write:

| Notation | Exact repository value |
|---|---|
| `J` | `g.slots`, with `g.slots_pos : 0 < g.slots` |
| `ell` | `(1 / 6 : ℝ) / g.slots` |
| `k` | `((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ)` |
| `pScale` | `primeScale g Z = Z ^ ell` |
| `Nu` | `frequencyRowNorm K S u`, the actual ideal norm |
| `Ru` | `(u.ideal.val.val.radical.absNorm : ℝ)` |
| `H` | `NormForm.internalHeight Z T kappa = max T (Z ^ kappa)` |
| `U` in the amplitude/kernel/row theorems | `2 * H + 2` |
| `E` | `arithmeticHighEulerData K S P psi` |

The three real contour heights are `x = (ts, tw, tz)`, with
`heightBox H = [-H,H] × ([-H,H] × [-H,H])`. The actual arguments are

\[
s=a+16e+i t_s,\qquad w=1-a-6e+i t_w,\qquad z=17/50+i t_z.
\]

These are the existing `sLine`, `wLine`, `zLine` definitions. In
particular `a = 1` is included and the resulting negative real part of
`w` is retained.

## 3. The complete actual slot and its cap

Sources:
[ActualNormFormFullCorrection.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormFullCorrection.lean),
[ActualNormFormSlotCap.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormSlotCap.lean).

For each actual exterior prime `p`, put `q = p.asIdeal.absNorm`. The
definitions use the constructed local factors literally:

\[
H_p=\operatorname{localFactor}(Q=\varnothing),\qquad
M_p=\operatorname{localFactor}(Q=\{p\}),
\]

\[
A_p=\overline{\psi(p)}q^{s+z-1},\qquad
B_p=q^{z-w-1},\qquad
\operatorname{comp}_p=\frac{A_pM_p-B_pH_p}{H_p}.
\]

`actualFullCorrectionSlot ... i` is exactly

\[
S_i=\sum_{p\in\operatorname{primeWindow}(i)}
       \operatorname{windowWeight}(i,p)\operatorname{comp}_p.
\]

The eventual cutoff proves nonvanishing of every selected local `H_p`
from the actual tables, uniformly in the row and contour. The exact
candidate `exists_actualFullCorrection_product_cutoff` then gives

\[
\operatorname{compensatedRowFullCorrection}
=\operatorname{rowCorrection}(Q=\varnothing)\prod_i S_i.
\]

No nonvanishing of the entire unselected Euler product is used in this
factorization. All original tuple and subset terms remain present.

### Error classes

`actualFullCorrectionSlot_decomposition` is an exact decomposition into
minus the actual conjugate-character main sum, a regular error, a
valuation-one contribution, and a repeated-prime contribution. At row
primes the actual row-character coefficient is proved zero, rather
than assumed zero as auxiliary data. The local bounds used in the
subsequent slot estimate are:

| Local class | Candidate bound on the final contour |
|---|---|
| Regular prime | Main term `-conj(chi(p)) * q^(z-1)` plus an error at most `regularCompensationErrorConstant * q^(-29/25)` |
| Row valuation one | `13 * q^(-4/25)` |
| Row valuation at least two | `19 * q^(a - 33/50 + 6*e)` |

The regular error is summed with ideal-norm summability. The
valuation-one count uses the actual prime support of `u.ideal`. The
repeated contribution is initially kept as its literal finite sum.

### Raw complete-slot estimate

`exists_actualFullCorrectionSlot_bound` fixes the original arithmetic
inputs, then assumes only

\[
0<e\le 1/10000,\qquad \epsilon,\eta,\kappa>0.
\]

Its quantifier order is

\[
\exists C,Z_0>0\ (Z_0\ge1),\quad
\forall Z,T,d,u,a,U,s,w,z,i.
\]

Here the required conditions, in source order, are:

1. `Z0 ≤ Z` and `1/16 ≤ d`;
2. `Z^d ≤ Nu`;
3. `51/100 ≤ a ≤ 1`;
4. the three displayed real-part equalities for `s,w,z`;
5. `internalHeight Z T kappa + |z.im| + 2 ≤ U`;
6. the actual detector
   `rowZeroBelow K S psi companions P E u U (a + 2*e)`.

This slot theorem does **not** require `T ≥ 1`, `T ≤ Z^kappa`, `d ≤ 1`,
or an upper dyadic row-norm bound. It is uniform in the imaginary parts
of `s` and `w`. It concludes

\[
\begin{aligned}
\lVert S_i\rVert\le C\bigg(&R_u^\epsilon(2+U)^{k\epsilon}
 pScale^{a-33/50+8e}\;+
 N_u^\eta pScale^{-4/25+\eta}\\
 &+pScale^{-4/25}
   \sum_{p\in\operatorname{repeatedPrimeWindow}(i)}
       q_p^{a-1/2+6e}\bigg).
\end{aligned}
\]

The main prime-sum bound is supplied by the actual divided-log Mellin
detector, actual logarithmic derivative, buffered zero-free contour,
both horizontal faces, initial vertical tails, higher prime powers and
the finite `S` deletion. No desired prime bound occurs in the final
cap's hypotheses. The zero-free contour/cap portion remains unverified
as noted in Section 1.

### Cap for binning the complete slot

With exactly the same inputs and quantifier order,
`exists_actualFullCorrectionSlot_power_cap` concludes

\[
\boxed{\ \lVert S_i\rVert\le
C N_u^{\epsilon+\eta}(2+U)^{k\epsilon}
 pScale^{a-33/50+8e+\eta}.\ }
\]

This uses the actual support-count subpower bound to control the
repeated-prime sum. The resulting amplitude measures the complete
slot, including its repeated-prime terms. The separate tuplewise
radical-allocation identities are retained in
[ActualNormFormRepeatedTuples.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRepeatedTuples.lean);
the later complete-slot kernel route uses `M = 1` in the pure factor
theorem and does not insert a second repeated-prime factor.

## 4. Constructed amplitude grid

Source:
[ActualNormFormAmplitudeGrid.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormAmplitudeGrid.lean),
using the actual continuity and compact maximum construction in
[ActualNormFormAmplitudes.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormAmplitudes.lean).

In addition to the arithmetic inputs and positive `e,epsilon,eta,kappa`,
choose `theta > 0` and `N : ℕ`, subject only to the scalar conditions

\[
\frac12\le N\theta,\qquad
\epsilon+\eta+\kappa(k\epsilon)+\ell(8e+\eta)
\le\frac{\ell\theta}{2}.
\]

The grid theorem chooses `Z0 ≥ 1` before all `Z,T,d,u,a`. Its later
hypotheses are exactly

\[
Z\ge Z_0,\quad 1\le T\le Z^\kappa,\quad
1/16\le d\le1,\quad Z^d\le N_u\le2Z^d,\quad
51/100\le a\le1,
\]

and

```lean
rowZeroBelow K S psi companions P E u
  (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e)
```

The output is a genuine finite label
`label : Fin g.slots → Fin (N+1)` and actual points `point i ∈ heightBox H`.
For

\[
g_i=\min(\operatorname{label}(i)\theta,a-1/2),
\]

it establishes all three properties:

\[
0\le g_i\le a-1/2,
\]

\[
\forall x\in\operatorname{heightBox}(H),\quad
\lVert S_i(x)\rVert\le pScale^{-4/25+g_i+\theta},
\]

\[
g_i>0\quad\Longrightarrow\quad
pScale^{g_i}<
\lVert pScale^{4/25}S_i(\operatorname{point}(i))\rVert.
\]

Thus the nonzero lower witnesses involve the literal full correction.
The zero-amplitude case requires no artificial nonzero witness. The
label is fixed over the entire three-height integration box; it is not
chosen pointwise under an integral.

`ActualFullSlotAmplitude` packages precisely these fields.
`exists_actualFullSlotAmplitude` constructs that object from the
original data; its analytic fields are conclusions. Its mean is

\[
q(A)=\frac1J\sum_i g_i.
\]

The number of possible vectors is exactly `(N+1)^J`, independent of
`Z,T,d,u,a` and of the retained row family. The eventual threshold
absorbs the fixed analytic cap constant using the positive grid budget.

## 5. Actual compensated kernel

Source:
[ActualNormFormKernel.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormKernel.lean).

`exists_actual_kernel_normForm` uses the finite-set/Borel/Haar context
from Section 2. It takes the same scalar hypotheses as the grid and an
additional `nu > 0`. Its quantifiers are

\[
\exists C>0,Z_0\ge1,\quad
\forall Z,T,d,u,a\text{ satisfying Section 4},\quad
\exists A:\operatorname{ActualFullSlotAmplitude},\quad
\forall x\in\operatorname{heightBox}(H).
\]

For the literal `compensatedRowMellinKernel K S₀ μ P psi E g ∅`, the
conclusion is

\[
\lVert\operatorname{kernel}_u(x)\rVert
\le C Z^{\operatorname{rowExponent}(d,a,q(A))+L_{\rm ker}},
\]

where

\[
\operatorname{rowExponent}(d,a,q)
=\frac{25}{48}a-\frac{63}{100}
 +d\left(a-\frac{21}{25}\right)+\frac q6,
\]

\[
L_{\rm ker}
=\left(\frac{105}{8}+6d\right)e+d(2\epsilon+\eta)
 +\frac\theta6+\nu+\kappa(k+2k\epsilon).
\]

The pure `rowExponent_eq_moderate` identity gives

\[
\operatorname{rowExponent}(d,a,q)
=3/16+\operatorname{moderateExponent}(d,2a-1,q,0).
\]

The `q/6` contribution is a power of `Z`. No row cardinality has entered
this estimate. Inserting a later row count contributes `dR` through the
separate pure counting identity.

The actual factors consumed in the proof are:

| Factor | Bound or identity actually consumed |
|---|---|
| Geometric powers | The original `Z^(17/48)`, `Z`, `Z^(23/48)`, and `Nu^(-z)` from `compensatedRowMellinKernel_factorization` |
| Gaussian and both Mellin tests | `exists_actual_profile_bound` on `s.re ∈ [1/2,2]`, `w.re ∈ [-1,1]`, `z.re = 17/50`, including the original physical residue normalizer |
| Three deleted L-factors | `exists_actual_threeLFactor_radical_bound`: `C * Ru^(a - 1/2 + 6*e + 2*epsilon) * (2+U)^(k + 2*k*epsilon)` |
| Unmarked Euler correction | The actual uniform `Nu^eta` bound, with `Q = ∅` |
| Complete slots | The constructed `A.upper` fields, combined into `Z^(-2/75 + q(A)/6 + theta/6)` |
| Prime normalizer | `exists_actual_primeNormalizer_inverse_subpower`, giving `CN * Z^nu`; its inherited PIT dependence is listed separately below |

The radical is the actual ideal radical, with `1 ≤ Ru ≤ Nu`. On the
allowed height range, `H = Z^kappa` and `2+U ≤ 6*Z^kappa`, producing
the displayed height loss. The constants and thresholds may depend on
the fixed arithmetic data, tests, geometry and chosen small parameters;
they are chosen before the scale, height, shell, bin, row and amplitude.

## 6. Actual row integral and the lambda/4 form

Source:
[ActualNormFormIntegral.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormIntegral.lean).

### Integrability and Fubini are explicit

`exists_actual_rowContour_normForm` has the kernel's hypotheses and
quantifier order. It returns an actual amplitude object **and**
`Integrable` for the original kernel against

\[
\mu_H=(\operatorname{volume}|_{[-H,H]})
 \times\big((\operatorname{volume}|_{[-H,H]})
 \times(\operatorname{volume}|_{[-H,H]})\big).
\]

That premise is obtained from actual correction continuity and the
buffered denominator detector before `integral_prod` is used. The
original `rowContourBox` remains

\[
(2\pi)^{-3}\int_{-H}^{H}\int_{-H}^{H}\int_{-H}^{H}
\operatorname{kernel}_u(t_s,t_w,t_z)\,dt_z\,dt_w\,dt_s.
\]

The exact finite-box mass is `8*H^3`. The resulting bound is

\[
\lVert\operatorname{rowContourBox}_u\rVert
\le C Z^{\operatorname{rowExponent}(d,a,q(A))+L_{\rm int}},
\qquad L_{\rm int}=L_{\rm ker}+3\kappa.
\]

The `(2*pi)^(-3)` factor is retained in the fixed constant. The proof
does not rely on a nonintegrable Bochner integral defaulting to zero.

### Selection of all small parameters

The separately native-compiled pure theorem
`NormForm.exists_full_normForm_parameter_budget` assumes only

```lean
(J : ℕ) (hJ : 0 < J)
(k lam e : ℝ) (hk : 0 ≤ k) (hlam : 0 < lam)
(he : 0 ≤ e) (heLam : e ≤ lam / 100)
```

It produces positive `epsilon,eta,kappa,theta,nu` and `N : ℕ` satisfying
the full grid budget and

\[
\forall d\in[0,1],\quad L_{\rm int}\le\lambda/4.
\]

Its proof uses `L = min lam 1` and the concrete choices

\[
\epsilon=\eta=\frac{\ell L}{10000(k+1)},\quad
\kappa=\frac{L}{10000(k+4)},\quad
\theta=\frac\lambda5,\quad\nu=\frac\lambda{1000},
\]

with `N` chosen so that `1/2 ≤ N*theta`.

### Main rowwise candidate

`exists_actual_rowContour_normForm_quarter_loss` requires the original
arithmetic/Borel/Haar inputs and only the scalar assumptions

\[
0<e,\quad e\le1/10000,\quad 0<\lambda,\quad e\le\lambda/100.
\]

It **outputs** `kappa,theta,N,C,Z0` before all `Z,T,d,u,a`. For the
same scale, dyadic-row, bin and actual upper-detector hypotheses of
Section 4, it constructs an actual `A` and concludes

\[
\boxed{\ \lVert\operatorname{rowContourBox}_u\rVert
\le C Z^{\operatorname{rowExponent}(d,a,q(A))+\lambda/4}.\ }
\]

`epsilon,eta,nu` are chosen inside this theorem; no caller has to supply
an analytic budget. Genuine integrability is established by the
upstream integral theorem, although the shorter quarter-loss conclusion
does not repeat that field.

## 7. Actual finite labels and exact sum identity

Source:
[ActualNormFormLabels.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormLabels.lean).

`exists_actual_labelled_rowContour_normForm` has the same fixed inputs
and scalar assumptions as the quarter-loss theorem. Its full choice
order is

\[
\exists\kappa,\theta>0,\ N:\mathbb N,\ C>0,\ Z_0\ge1,
\quad\forall Z,T,d,a,\quad\forall F:\operatorname{Finset}(\operatorname{FrequencyRow}).
\]

Before `F` is introduced, the scale/height/shell/bin hypotheses are

\[
Z\ge Z_0,\quad1\le T\le Z^\kappa,\quad
1/16\le d\le1,\quad51/100\le a\le1.
\]

The **only** conditions on each `u ∈ F` are

\[
Z^d\le N_u\le2Z^d
\]

and the original
`rowZeroBelow ... u (2*internalHeight Z T kappa + 2) (a+2*e)`.
There is no row-count bound, proposed piece estimate or presentation
field among the inputs.

The theorem constructs a total selector

```lean
selector : FrequencyRow K S₀ → (Fin g.slots → Fin (N + 1))
```

and, for every retained row, an `ActualFullSlotAmplitude A` satisfying
`A.label = selector u`. The selector outside `F` is immaterial to the
fibers. Put

\[
F_\ell=\{u\in F:\operatorname{selector}(u)=\ell\},\qquad
q_\ell=\frac1J\sum_i\min(\ell_i\theta,a-1/2).
\]

Then, for **every** label, including empty fibers,

\[
\boxed{\ \sum_{u\in F_\ell}
 \lVert\operatorname{rowContourBox}_u\rVert
 \le C\,\#F_\ell\,
 Z^{\operatorname{rowExponent}(d,a,q_\ell)+\lambda/4}.\ }
\]

It also gives the exact identity

\[
\sum_{\ell:\operatorname{Fin}(J)\to\operatorname{Fin}(N+1)}
 \sum_{u\in F_\ell}\operatorname{rowContourBox}_u
=\sum_{u\in F}\operatorname{rowContourBox}_u.
\]

The identity uses the actual contour integrals and the constructed
selector. No arbitrary cancelling quantities are added as label
pieces. The finite label count is exactly `(N+1)^J`, so this constructed
packet has no additional height degree in its norm-form bound.

## 8. Inherited PR-WINDOW-PIT dependence

[ActualNormFormNormalization.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormNormalization.lean)
isolates the exact use of the original normalizer theorem:

```lean
HeckeSkeleton.PrimeNormalizer.normalizer_smallPower K S g nu hnu
```

It turns the existing `IsBigO` conclusion into a uniform positive
constant and scale threshold for

```lean
‖(primeNormalizer K S g ∅ Z)⁻¹‖ ≤ C * Z ^ nu
```

The existing `normalizer_smallPower` proof depends on the admitted
`window_prime_lower`, labelled **PR-WINDOW-PIT**, in
[PrimeNormalizer.lean](../../HeckeSkeleton/PrimeNormalizer.lean).
Consequently the sharp kernel, row-integral and labelled norm-form
route inherits that admission. The new normalization module neither
proves PIT nor replaces it by an assumed desired estimate.

The character-cancellation prime cap and complete-slot amplitude
construction do not call this normalizer theorem. The positive window
mass cancellation used for coarse boundary bounds cannot simply be
substituted here: the sharp signed character cap has no common positive
slot-mass factor to cancel. This is why the dependency is explicitly
retained.

No new `sorry`, `admit`, `axiom` or `native_decide` is introduced in these
norm-form modules. That source observation does **not** establish a
standard-axiom-only transitive audit for the uncompiled actual chain.
The full actual audit must enumerate all inherited repository axioms
once those declarations elaborate. PR-WINDOW-PIT is an identified
dependency, not a claim that it is the only possible nonstandard
dependency in the whole repository.

## 9. What still separates this chain from `HighShiftedNormForm`

The original statement is in
[HighBin.lean](../../HeckeSkeleton/HighBin.lean). It quantifies over
`(targetData K c).expansion Z T`, its block labels, each block's
`amplitudeSet`, and `actualHighPresentation.shiftedPiece`. The candidate
theorems above construct a different, explicit family of actual
amplitude fibers. An equality of total sums alone does not identify
the norms of arbitrary individual pieces.

### An exact original-type conditional consumer

[ActualNormFormTarget.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormTarget.lean)
now supplies a candidate connection to the **literal original type**,
`HighShiftedNormForm K c P`, for any original
`P : ActualHighPresentation K c`. This consumer retains the original
block and label types, original row sets and original mean fields.
It does not replace the original norm-form proposition with a new one.

The declaration
`HeckeSkeleton.HighBinNormFormTarget.exists_target_highShiftedNormForm_connection`
has the following exact order of dependence:

1. Fix `K`, its original field and number-field instances, `c`, and `P`.
   Supply the identity of `P.euler` with the actual arithmetic provider
   and the structural fact `1 ∈ P.companions`.
2. The theorem chooses `kappa > 0`, `theta > 0`, `N : ℕ`, `C > 0`, and
   `Z0 ≥ 1`, using the actual target row-integral theorem. None depends
   on `Z,T,b,label,u`.
3. On `Z0 ≤ Z`, `1 ≤ T ≤ Z^kappa`, identify
   `P.contourHeight Z T b = internalHeight Z T kappa` and require
   `2*internalHeight Z T kappa+2 ≤ P.upperHeight Z T b` for each original
   block. The latter transfers the original buffered zero detector to
   the smaller height by its actual definition.
4. The theorem constructs a dependent family `A` of actual full-slot
   amplitude witnesses on **each original retained label row**. The
   family is an output. Neither the record's analytic fields nor any
   numerical row or integral estimate is a caller hypothesis.
5. Two structural identities imply the original conclusion: the original
   label's `.mean` equals the mean of this constructed `A` on every
   retained row, and its original `P.shiftedPiece` equals the literal
   original `rowContourBox` at `P.contourHeight`.

The proof derives the required shell and bin ranges, lower and upper
row norms, zero detector, `e ≤ 1/10000`, and `e ≤ c.lamB/100` from the
existing presentation fields. In particular, the upper norm bound is
derived from actual `frequencyRows` membership, rather than supplied as
an added norm estimate. The exponent is proved equal to the original
`highRowExponent`, using the repository's actual `moderateExponent`.
The constructed witness of `HighShiftedNormForm` uses `A = 0` for its
external `(1+T)^A` exponent; the height loss has already been absorbed
in the internal `Z^(c.lamB/4)` budget.

The original labels may overlap. The consumer bounds each label's
finite row sum individually, so it requires no artificial partition and
no row-count estimate. Its result does not establish the two structural
identities for `actualHighPresentation`: those remain part of the genuine
expansion construction. As with the rest of the deep actual chain, the
target consumer has not yet been elaborated by Lean.

### Identities still required of the named expansion

To construct the named presentation itself and use the finite-label
theorem as its source, all of the following genuine identifications
remain relevant:

| Required original field or fact | Concrete object needed from this chain |
|---|---|
| `.euler` | `arithmeticHighEulerData` for the target probe and character |
| `.companions` | A fixed original family containing `1` |
| `.e` | Positive, at most `1/10000`, and at most the original lambda margins divided by `100` |
| `.contourHeight` | The selected `internalHeight Z T kappa` |
| `.upperHeight` | A height sufficient for the detector at `2*internalHeight Z T kappa+2` |
| `.labels` | The fixed finite complete-slot grid, or a proved identified refinement |
| `.amplitudeSet.rows` | The actual selector fibers of the retained fixed-bin row set |
| `.amplitudeSet.amplitude` | The values `min (label_i*theta) (a-1/2)` of that same label |
| `.amplitudeSet.mean` | `actualFullSlotLabelMean` of that same grid label |
| `.shiftedPiece` | The literal `rowContourBox` used above, with all original tests and normalizers |
| `.block_identification` | The original expansion block value equals the sum of these actual pieces |
| `.shifted_identification` | The selected fibers exhaust the intended fixed-bin rows and preserve their original contour sum |

The selected-zero height and the upper-zero height are distinct choices
in the original presentation. Their required arithmetic/bin support
identities must also be established; the norm-form estimate does not
choose them by changing an existing definition.

The wider expansion also contains `AmplitudeSet.slotValue` and genuine
inverse/plain witness subdivisions, defined in
[TIPSources.lean](../../HeckeGeneral/Analysis/TIPSources.lean). The actual
normalized values `pScale^(4/25) * S_i(point_i)` provide the intended
slot witnesses. Their transfer to the named expansion, and the
`WitnessCover` required by `BlockSource` above the floor bin, remain
separate construction obligations. This norm-form chain does not fill
those fields with empty or dummy subdivisions.

At the time of this record, `Base.highExpansion` is still an opaque
definition with the original `D-EXPANSION` admission, and
`actualHighPresentation` still has the original `HB-PRESENT` admission.
The record's existing sum fields do not supply the per-label identities
in the table. In particular, the hypotheses `FullHighEulerControl`,
`HighPureNormPoleExclusion`, and `HighConductorDeficit` of the original
`highShiftedNormForm` theorem do not identify arbitrary presentation
means or pieces with the constructed full-slot labels.

### Review of possible restricted-height label pieces

A direct review of the existing types found **no representation of an
original label as a measurable height region**. This is a structural
absence, before any analytic estimate:

- `AmplitudeSet` has exactly `rows`, `amplitude`, `slotValue`,
  `subdivisionCount`, and `subdivision`. Its `slotValue` is a complex
  number for a slot and a row; it has no contour-height argument.
- `ModerateBlock.Label` is an arbitrary `Type`. Its associated
  `amplitudeSet` supplies no region, indicator function, measurability,
  or per-label contour formula.
- `WitnessSubdivision` has row sets, lengths, and inverse/plain witness
  values. The real parameter indexing subdivisions is the witness
  parameter `t`; it does not define a region in the three imaginary
  contour coordinates.
- `ActualHighPresentation.shiftedPiece` is a complex-valued function of
  the scale, external height, block, label, and row. Its only integral
  connection is `shifted_identification`, which identifies the total
  double sum with the full fixed-bin contour sum.

The comment describing the labels as pointwise amplitude sets does not
add any of these missing fields or identities. Also, the pure
`HighNormFormPacket.fullSlotKernel_integral_decomposition` is a theorem
about its supplied kernels and selectors; the repository does not
identify that packet with the named target's `shiftedPiece`.

For a construction that uses restricted-height pieces, the missing
identification theorem must have the following concrete content. For
each actual `K,c,P,Z,T,b`, it must construct

```lean
regions : HighLabel K c Z T b → HighRow K c → Set (ℝ × (ℝ × ℝ))
```

and, for every `ℓ ∈ P.labels Z T b` and every original retained row
`u ∈ (block.amplitudeSet ℓ).rows`, prove both

```lean
MeasurableSet (regions ℓ u)
regions ℓ u ⊆ HighBinBoundary.ActualIntegrability.heightBox
  (P.contourHeight Z T b)
```

and the actual identity

\[
P.\operatorname{shiftedPiece}(Z,T,b,\ell,u)
= (2\pi)^{-3}\int_{\operatorname{regions}(\ell,u)}
     K_u(t_s,t_w,t_z)\,dt_s\,dt_w\,dt_z.
\]

Here the normalization is exactly the Lean complex value
`(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))`. The function `K_u` must be the
repository's literal `compensatedRowMellinKernel`, with the target's
actual probe and Haar measures, `P.euler`, `c.geometry`, the original
ray filter, and real contour coordinates
`a+16*P.e`, `1-a-6*P.e`, `17/50`, where `a = block.bin`.
The integral above uses the ordinary product Lebesgue measure on
`ℝ × (ℝ × ℝ)` restricted to the constructed region. These displays
specify a **missing theorem**, not a newly proved declaration.

If the total decomposition is to be recovered from these regions, it
also needs the almost-everywhere finite indicator identity: for each
row of the original fixed bin and almost every height in the original
box, the sum of the region indicators over labels retaining that row
equals one. Merely allowing overlapping row sets does not provide
this identity. Conversely, a total-sum identity cannot force a
per-piece norm estimate: changing two pieces by opposite complex
quantities preserves the total while their individual norms can grow.

There is a second independent identification needed for the requested
exponent. The original label's amplitude vector and mean must be tied
to the **actual complete-slot values on that same region**. The current
`ActualFullSlotAmplitude` construction chooses a grid vector valid over
the whole box. That vector need not equal the pointwise label's vector
on a smaller region. Integrating its whole-box estimate on an arbitrary
subset therefore does not by itself produce the original label mean in
`highRowExponent`.

Consequently no additional generic restricted-integral consumer was
added during this review. It would leave both missing identities
untouched and would not consume an object presently constructed in
the repository. The existing target consumer remains explicitly
conditional on its stronger whole-row piece identity. A genuine
restricted-piece extension should follow the construction of the
regions and their complete-slot label identities, using the existing
pointwise kernel factorization and the finite box-volume estimate.

Accordingly this document records a proposed actual analytic chain and
its exact remaining connection. It does not assert that the original
`highShiftedNormForm`, `HighBinInput`, or the complete project has been
proved.

## 10. Exact source signatures

The following blocks are copied from the named source declarations.
They use the section contexts and `S₀` notation listed in Section 2.
They are source signatures, **not** substituted for Lean's elaborated
`#check` output. File hashes bind the copied statements to the reviewed
source snapshot. Subsequent edits require regeneration of these blocks
and the repository declaration inventory.

### `HighBinVerified.NormFormSlotCap.exists_actualFullCorrectionSlot_power_cap`

Source: [ActualNormFormSlotCap.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormSlotCap.lean).  
Source SHA-256: `e53c4fa528baea1a9e7b5c5ff7c898e147eb96f7b7cc0624ae66a5efbe1d0640`.

```lean
theorem exists_actualFullCorrectionSlot_power_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
    {e eps eta kappa : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a U : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
      NormForm.internalHeight Z T kappa + |z.im| + 2 ≤ U →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u U (a + 2 * e) →
      ∀ i : Fin g.slots,
        ‖actualFullCorrectionSlot K S P psi g ∅ u Z s w z i‖ ≤
          C * frequencyRowNorm K S u ^ (eps + eta) *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
            (primeScale g Z) ^ (a - 33 / 50 + 8 * e + eta)
```

### `HighBinVerified.NormFormAmplitudeGrid.exists_actual_fullSlot_amplitude_grid`

Source: [ActualNormFormAmplitudeGrid.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormAmplitudeGrid.lean).  
Source SHA-256: `57810d7064fa8d26c7dbede4c67bb301b9fe03560f836d77a85e6efac4edb446`.

```lean
theorem exists_actual_fullSlot_amplitude_grid
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
    {e eps eta kappa theta : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) (htheta : 0 < theta)
    (hbudget : eps + eta + kappa *
        (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) +
        ((1 / 6 : ℝ) / g.slots) * (8 * e + eta) ≤
      ((1 / 6 : ℝ) / g.slots) * theta / 2)
    (N : ℕ) (hN : (1 / 2 : ℝ) ≤ (N : ℝ) * theta) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
        frequencyRowNorm K S u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∃ q : Fin g.slots → ℝ × (ℝ × ℝ), ∃ label : Fin g.slots → Fin (N + 1),
        (∀ i, q i ∈ heightBox (NormForm.internalHeight Z T kappa)) ∧
        ∀ i, let amplitude := min (((label i).val : ℝ) * theta) (a - 1 / 2)
          0 ≤ amplitude ∧ amplitude ≤ a - 1 / 2 ∧
          (∀ x ∈ heightBox (NormForm.internalHeight Z T kappa),
            ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖ ≤
              (primeScale g Z) ^ (-(4 / 25 : ℝ) + amplitude + theta)) ∧
          (0 < amplitude → (primeScale g Z) ^ amplitude <
            ‖((primeScale g Z ^ (4 / 25 : ℝ) : ℝ) : ℂ) *
              actualSlotHeightProfile K S P psi g ∅ u Z a e i (q i)‖)
```

### `HighBinVerified.NormFormKernel.exists_actual_kernel_normForm`

Source: [ActualNormFormKernel.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormKernel.lean).  
Source SHA-256: `6e6e492bddfce70f870ce9111fa667528f9b28a97828bb48acc6d7d80b245176`.

```lean
theorem exists_actual_kernel_normForm
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e eps eta kappa theta nu : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) (htheta : 0 < theta)
    (hnu : 0 < nu)
    (hbudget : eps + eta + kappa *
        (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) +
        ((1 / 6 : ℝ) / g.slots) * (8 * e + eta) ≤
      ((1 / 6 : ℝ) / g.slots) * theta / 2)
    (N : ℕ) (hN : (1 / 2 : ℝ) ≤ (N : ℝ) * theta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S₀, Z ^ d ≤ frequencyRowNorm K S₀ u →
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∃ A : ActualFullSlotAmplitude K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N,
        ∀ x ∈ heightBox (NormForm.internalHeight Z T kappa),
          ‖compensatedRowMellinKernel K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
            (sLine (a + 16 * e) x) (wLine (1 - a - 6 * e) x) (zLine x)‖ ≤
            C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) +
              (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu) +
              kappa * (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
                2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps))
```

### `HighBinVerified.NormFormIntegral.exists_actual_rowContour_normForm`

Source: [ActualNormFormIntegral.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormIntegral.lean).  
Source SHA-256: `52525599f344ae8345137536b64de79f8381c756d14cdeed7a87b6568fbda8da`.

```lean
theorem exists_actual_rowContour_normForm
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e eps eta kappa theta nu : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) (htheta : 0 < theta)
    (hnu : 0 < nu)
    (hbudget : eps + eta + kappa *
        (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) +
        ((1 / 6 : ℝ) / g.slots) * (8 * e + eta) ≤
      ((1 / 6 : ℝ) / g.slots) * theta / 2)
    (N : ℕ) (hN : (1 / 2 : ℝ) ≤ (N : ℝ) * theta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S₀, Z ^ d ≤ frequencyRowNorm K S₀ u →
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∃ A : ActualFullSlotAmplitude K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N,
        Integrable (fun x : ℝ × (ℝ × ℝ) =>
          compensatedRowMellinKernel K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
            (sLine (a + 16 * e) x) (wLine (1 - a - 6 * e) x) (zLine x))
          ((volume.restrict (Icc (-NormForm.internalHeight Z T kappa)
            (NormForm.internalHeight Z T kappa))).prod
              (twoHeightMeasure (NormForm.internalHeight Z T kappa))) ∧
        ‖rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
            (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) +
            (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu) +
            kappa * (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
              2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps + 3))
```

### `HighBinVerified.NormFormIntegral.exists_actual_rowContour_normForm_quarter_loss`

Source: [ActualNormFormIntegral.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormIntegral.lean).  
Source SHA-256: `52525599f344ae8345137536b64de79f8381c756d14cdeed7a87b6568fbda8da`.

```lean
theorem exists_actual_rowContour_normForm_quarter_loss
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e lam : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hlam : 0 < lam) (heLam : e ≤ lam / 100) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S₀, Z ^ d ≤ frequencyRowNorm K S₀ u →
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∃ A : ActualFullSlotAmplitude K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N,
        ‖rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
            (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) + lam / 4)
```

### `HighBinVerified.NormFormLabels.exists_actual_labelled_rowContour_normForm`

Source: [ActualNormFormLabels.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormLabels.lean).  
Source SHA-256: `83f2a08a52a1337b27f835a334a8615c8bd33db46c3b63f67fe71139bb3be2b8`.

```lean
theorem exists_actual_labelled_rowContour_normForm
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e lam : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hlam : 0 < lam) (heLam : e ≤ lam / 100) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      ∀ F : Finset (FrequencyRow K S₀),
      (∀ u ∈ F, Z ^ d ≤ frequencyRowNorm K S₀ u ∧
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d ∧
        rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
          (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e)) →
      ∃ selector : FrequencyRow K S₀ → (Fin g.slots → Fin (N + 1)),
        (∀ u ∈ F, ∃ A : ActualFullSlotAmplitude K S₀ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N,
          A.label = selector u) ∧
        (∀ label : Fin g.slots → Fin (N + 1),
          (∑ u ∈ NormForm.labelledRows F selector label,
            ‖rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
              (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖) ≤
          C * ((NormForm.labelledRows F selector label).card : ℝ) *
            Z ^ (NormForm.rowExponent d a (actualFullSlotLabelMean g a theta N label) + lam / 4)) ∧
        (∑ label : Fin g.slots → Fin (N + 1),
          ∑ u ∈ NormForm.labelledRows F selector label,
            rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
              (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)) =
          ∑ u ∈ F,
            rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
              (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)
```

### `HighBinVerified.NormForm.exists_full_normForm_parameter_budget`

Source: [HighNormFormScalar.lean](../../HeckeSkeleton/HighBinSupport/HighNormFormScalar.lean).  
Source SHA-256: `b956c321076fbd1f34b3bc3ce75e0cb1a504ee3cf0f71d60c66b63ba962b7f5b`.

```lean
theorem exists_full_normForm_parameter_budget (J : ℕ) (hJ : 0 < J)
    (k lam e : ℝ) (hk : 0 ≤ k) (hlam : 0 < lam) (he : 0 ≤ e)
    (heLam : e ≤ lam / 100) :
    ∃ eps eta kappa theta nu : ℝ, ∃ N : ℕ,
      0 < eps ∧ 0 < eta ∧ 0 < kappa ∧ 0 < theta ∧ 0 < nu ∧
      (1 / 2 : ℝ) ≤ (N : ℝ) * theta ∧
      eps + eta + kappa * (k * eps) + ((1 / 6 : ℝ) / J) * (8 * e + eta) ≤
        ((1 / 6 : ℝ) / J) * theta / 2 ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
        (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu) +
          kappa * (k + 2 * k * eps + 3) ≤ lam / 4
```

### `HeckeSkeleton.HighBinNormFormTarget.exists_target_rowContour_normForm_quarter_loss`

Source: [ActualNormFormTarget.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormTarget.lean). SHA-256: `e7c104d03e4c7843c9df707e0a698c3423ef73cc88e9d0bc851d6ee94f05fa4f`.

The declaration uses the target measure instances specified by `targetData.measures`; all other parameters and hypotheses are displayed below. This is an unelaborated source signature.

```lean
theorem exists_target_rowContour_normForm_quarter_loss
    (c : TargetContext K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) (heLam : e ≤ c.lamB / 100) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : HighRow K c, Z ^ d ≤ frequencyRowNorm K _ u →
        frequencyRowNorm K _ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K _ (targetCharacter K c) companions (targetData K c).probe
        (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c)) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∃ A : ActualFullSlotAmplitude K _ (targetData K c).probe
          (targetCharacter K c) c.geometry u Z a e
          (NormForm.internalHeight Z T kappa) theta N,
        ‖rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
            (targetCharacter K c)
            (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
            c.geometry (targetData K c).rayFilter u Z
            (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K _ A) + c.lamB / 4)
```

### `HeckeSkeleton.HighBinNormFormTarget.exists_target_highShiftedNormForm_connection`

Source: [ActualNormFormTarget.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormTarget.lean). SHA-256: `e7c104d03e4c7843c9df707e0a698c3423ef73cc88e9d0bc851d6ee94f05fa4f`.

The declaration uses the target measure instances specified by `targetData.measures`; all other parameters and hypotheses are displayed below. `PresentationFullSlotAmplitudes` is the dependent function type described in Section 9: for every admissible scale, height, original retained label and row, an `ActualFullSlotAmplitude` for the actual target probe at the original bin and the chosen height and grid. This is an unelaborated source signature.

```lean
theorem exists_target_highShiftedNormForm_connection
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcomp : (1 : HeckeCharacter K) ∈ P.companions) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ((∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          P.contourHeight Z T b = NormForm.internalHeight Z T kappa) →
      (∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          2 * NormForm.internalHeight Z T kappa + 2 ≤ P.upperHeight Z T b) →
      ∃ A : PresentationFullSlotAmplitudes K c P kappa theta N Z0,
        (∀ (Z T : ℝ) (hZ : Z0 ≤ Z) (hT : 1 ≤ T) (hTcap : T ≤ Z ^ kappa)
          (b : HighBlockIndex K c Z T) (ℓ : HighLabel K c Z T b)
          (hℓ : ℓ ∈ P.labels Z T b) (u : HighRow K c)
          (hu : u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows),
          ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).mean =
            ActualFullSlotAmplitude.mean K _ (A Z T hZ hT hTcap b ℓ hℓ u hu)) →
        (∀ (Z T : ℝ) (_hZ : Z0 ≤ Z) (_hT : 1 ≤ T) (_hTcap : T ≤ Z ^ kappa)
          (b : HighBlockIndex K c Z T) (ℓ : HighLabel K c Z T b)
          (_hℓ : ℓ ∈ P.labels Z T b) (u : HighRow K c)
          (_hu : u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows),
          P.shiftedPiece Z T b ℓ u =
            rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
              (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u Z
              (P.contourHeight Z T b)
              ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
              (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)) →
        HighShiftedNormForm K c P)
```
