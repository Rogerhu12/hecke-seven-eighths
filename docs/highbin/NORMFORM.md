# Actual HIGHBIN norm form: statements, hypotheses and verification boundary (historical snapshot)

> **Historical snapshot — PR #7 at `d88663c8`.**
> Status statements, unresolved obligations and native evidence below describe
> that checkpoint and its earlier recorded stages. See the
> [current integration report](INTEGRATION_20261101.md) for shared interfaces
> and verification gates, and the
> [PR #7 description](https://github.com/Rogerhu12/hecke-seven-eighths/pull/7)
> for the latest commit, native results and acceptance status.

This document records the norm-form implementation on
`codex/highbin-canonical-partitions-20261031`, continuing the original
HIGHBIN branch. It describes declarations in
the repository's actual arithmetic, prime-window and contour definitions.
It does **not** certify `HeckeSkeleton.highShiftedNormForm`: the original named
presentation and expansion identifications remain missing.

The status below was updated on 2026-10-31. The exact source signatures in
the appendix are candidates until the corresponding individual actual
modules have elaborated successfully. A source declaration with a proof
body is not, by itself, an elaborated theorem or an exact-type audit.

## 1. Verification status at this checkpoint

| Part | Recorded result | Scope of the result |
|---|---|---|
| `ActualNormFormHigherPrimePowers`, `ActualNormFormMellinInversion`, `ActualNormFormPrimeDetector`, `ActualNormFormUniformMellin` | Native separate-module build and all 55 public declaration audits passed at `6e3d24ca4579aa615ef0a23769c1695cb8f4b55d`, and again at `a2ea91210ece94f7969fb6bd060d4b95e7cd4ed0` | Their axiom sets contain only `propext`, `Classical.choice`, `Quot.sound`; `mellin-axioms.json` has an empty `beyond_standard_axioms` object. |
| `ActualOrbitalRapidDecay`, `ActualAdditiveMellinRapidDecay` and the four preceding Mellin modules | Native six-module / 67-public-declaration audit passed at `011125ed7144684ad0d1a817dd21ddb5ec9c2b66`, and again at `357effad` | All axiom sets contain only the three standard axioms; [verified_mellin_axioms.json](verified_mellin_axioms.json) preserves the complete current source-bound mapping. This extends the earlier five-module / 59-declaration checkpoint at `c71511a5`. |
| The same Mellin dependency chain, combined locally | 40 source files and 577 public declarations passed | This is additional combined-source evidence, distinct from separate-module verification. |
| `HighNormFormScalar`, including `exists_full_normForm_parameter_budget` | The native core run at `a2ea91210ece94f7969fb6bd060d4b95e7cd4ed0` compiled the file successfully; the subsequent run at `45b507f4995fe107e2e98041f91971c8c78d5860` passed all 57 modules and 442 public declaration audits | Its printed parameter-budget axiom set is the same three standard axioms. The current core run references are maintained in `REPORT.md`; this core success does not verify the deep actual norm-form chain. |
| `HighNormFormPointwisePartition` | Native separate-module build passed on 2026-10-31 with the original imports, in 117.609 seconds; source SHA-256 `0f7dfba42ccb069d843cd585cc557dd5d7e626fbdb4cd22f617c469c808d5023` | The four printed main declarations—measurable bucket index, bucket bounds, measurable regions and exact integral decomposition—contain only the three standard axioms. This does not verify the actual arithmetic instantiation. |
| Actual window detector, zero-free prime contour/cap, complete-slot correction, sharp factors, amplitude construction, kernel, integral, label grouping, computed height regions, calibrated-provider transport and target presentation consumers | Source implementation and static interface review only | These actual norm-form declarations have not yet passed their individual native builds. Their displayed source signatures and their transitive axiom sets have **not** been confirmed by Lean. |
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

The analytic estimate chain uses the concrete Euler provider

```lean
arithmeticHighEulerData K S P psi
```

and its character is the actual `arithmeticRowCharacter K S P u`. A free
Euler provider, a proposed prime-sum estimate, a conductor estimate, or a
row-integral estimate is not an input to the main kernel/label theorems.
Section 9 separately transports the literal restricted integral from
an original provider using its original `RowEulerCalibrationInput`.
That transport assumes no equality of provider records and no analytic
estimate for the original provider.
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
The code now spells out the set coercion in each `variable` declaration.
This avoids the captured `K`/`S` parameter mismatch found by the native
build in the analogous Borel adapter; `S₀` remains notation in theorem
statements, as in this display.

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

### Computed restricted-height pieces

The 2026-10-31 extension constructs actual regions instead of accepting
arbitrary regions as input. The pure
[HighNormFormPointwisePartition.lean](../../HeckeSkeleton/HighBinSupport/HighNormFormPointwisePartition.lean)
defines a total bucket index by `Nat.find`: take the first geometric
threshold reached, retaining index `N` as a fallback. The final amplitude
is clipped at `a-1/2`. Measurability follows from the threshold predicates,
so it does not depend on the measurability of an arbitrary choice function.

[ActualNormFormRegions.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegions.lean)
instantiates this recipe at the literal values

\[
M_i(u,x)=pScale^{4/25}\lVert S_i(u,x)\rVert.
\]

For a label `ell : Fin g.slots → Fin (N+1)`, its region is the subset of
the actual `heightBox H` where all computed bucket indices equal `ell`.
All slots use the repository's common `primeScale g Z`; their different
window positions remain inside the original slot functions. These regions
are measurable, pairwise disjoint and exhaust the box for each row.
Different labels may retain the same row because their height regions can
both be nonempty. The corresponding amplitude vector and mean are

\[
\alpha_{\ell,i}=\min(\ell_i\theta,a-1/2),\qquad
q_\ell=\frac1J\sum_i\alpha_{\ell,i}.
\]

The declarations `actualSlotHeightProfile_measurable` and
`actualSlotRegion_measurable` prove measurability for **every** real scale
`Z`, height `H`, mesh `theta` and finite grid `N`, with only `51/100 ≤ a`
and `0 < e`. There is no scale cutoff, upper bound on `a`, upper bound
on `e`, zero detector, or nonvanishing premise. Each literal slot is a
finite sum of quotients of continuous local factors and complex powers.
The proof uses measurable complex division, which remains valid at the
actual totalized value when a local denominator is zero. It does not
claim continuity or an upper bound there. The existing
`exists_actualSlotRegion_measurable` signature is unchanged and now uses
the cutoff `1`.

The actual arithmetic cap proves the complete-slot upper bound throughout
each region. If an amplitude is positive, every point in that region
also supplies its strict lower witness. In particular, all positive slot
witnesses can be evaluated at the same point; separate slot maxima are
not substituted for a simultaneous region witness.

[ActualNormFormRegionIntegral.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionIntegral.lean)
defines `actualRegionPiece` to be exactly `(2*pi)^(-3)` times the original
compensated kernel integrated over this computed region. The separate
`sum_actualRegionPiece_eq_rowContourBox` proves the exact sum identity
for every `Z,H,theta,N` under `51/100 ≤ a`, `0 < e` and genuine
`IntegrableOn` of that literal kernel on `heightBox H`. It requires no
scale, shell, detector, arithmetic calibration, slot bound or norm bound.
This removes the scale restriction from the finite-partition/Fubini
argument itself; it does **not** establish integrability at every scale.
The complete eventual theorem proves its own integrability and calls
this exact decomposition theorem. Its original signature is unchanged.

The theorem
`exists_actual_region_normForm_quarter_loss` has the same fixed arithmetic,
Borel and Haar inputs as the whole-box theorem, and assumes only
`0 < e ≤ 1/10000`, `0 < lam`, and `e ≤ lam/100` before choosing
`kappa,theta,N,C,Z0`. After those choices, it quantifies over `Z,T,d,u,a`
with the same scale, dyadic shell, closed bin range and upper-detector
conditions. It returns, for **every** label:

- measurability of the computed region and genuine integrability of its
  literal restricted kernel;
- the actual slot upper bounds and same-point positive lower witnesses;
- the individual estimate
  `‖actualRegionPiece label‖ ≤ C*Z^(rowExponent d a q_label + lam/4)`.

It also returns the exact identity `sum label, actualRegionPiece label =
rowContourBox`, with the original tests, Euler provider and normalizers.
The proof bounds the mass of each region by the actual box mass `8*H^3`
and uses the same native scalar budget. No piece norm bound, slot bound,
region, or integrability assertion is a premise of this complete theorem.
The auxiliary kernel factor lemma accepts pointwise slot bounds; this
complete theorem supplies them from the constructed regions and the
actual arithmetic cap. The deep actual extension remains unelaborated
until its separate native build succeeds.

### The original TIP data types receive concrete fields

[ActualNormFormRegionPacket.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionPacket.lean)
uses the existing `TIP.AmplitudeSet` and `TIP.ModerateBlock` types. It
does not introduce substitute block or amplitude-set types. For a retained
finite row family `F`, it defines a label's row set by

\[
F_\ell=\{u\in F:\operatorname{actualSlotRegion}(u,\ell)\ne\varnothing\}.
\]

Every original row belongs to at least one such label when `H ≥ 0`.
One actual height point is chosen in each nonempty region, and every slot
value of that row and label is evaluated at this same point, with the
original factor `pScale^(4/25)`. The constructor's amplitude vector is
`actualRegionAmplitude`; its original `.mean` is definitionally
`actualRegionMean`. Its positive slot values satisfy the exact
`BlockSource` lower-witness expression
`Z^(((1/6)/g.slots)*amplitude_i) ≤ ‖slotValue i u‖`.

The moderate-block constructor sets `.value` to the complete original
fixed-bin row contour sum and uses the finite grid as its label type.
The packet theorem proves both the individual finite-row norm bound

\[
\sum_{u\in F_\ell}\lVert\operatorname{actualRegionPiece}(u,\ell)\rVert
\le C\,\#F_\ell\,Z^{\operatorname{rowExponent}(d,a,q_\ell)+\lambda/4}
\]

and the exact sum of all its literal pieces. Removing rows with empty
regions does not change that sum because their restricted integrals are
zero. No bound on `#F` or on `#F_ell` is supplied.

The constructors take `subdivisionCount` and `subdivision` as explicit
recipe arguments. They neither choose empty subdivisions nor assert
`WitnessCover`. The actual inverse/plain detector witnesses and their
uniform subdivision count remain separate obligations. Likewise, these
constructed `ModerateBlock` values have not yet been identified with the
opaque blocks of `Base.highExpansion`.

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

The bin range is the full closed range required by the original
obligation: `P.bin_range` gives `51/100 ≤ a ≤ c.family.B`, and
`c.family.B_upper` gives `c.family.B ≤ 1`. The actual slot cap,
amplitude grid, kernel, integral and finite-label source interfaces all
use `a ≤ 1`, so the specialization includes `a = B = 1`; it does not
require `a < 1` or a positive gap `1-a`. At that endpoint the actual
real contour coordinates are `1+16*P.e`, `-6*P.e`, and `17/50`, within
the closed ranges consumed by the kernel proof. The grid cap is
`a-1/2 = 1/2`, covered by the existing choice `1/2 ≤ N*theta`. This is
a source-interface and scalar-range check, not additional native
verification of the uncompiled analytic modules.

The order in steps 4 and 5 matters: the mean identity concerns the
particular amplitude family already constructed by the theorem. The
caller cannot choose new analytic fields after supplying the original
means. Neither that mean identity nor the whole-row piece identity is
proved satisfiable for an arbitrary presentation. In particular,
requiring every retained `shiftedPiece` to equal a complete row contour
is a stronger construction requirement than the record's total-sum
`shifted_identification`; no implication from the latter to the former
is asserted.

The original labels may overlap. The consumer bounds each label's
finite row sum individually, so it requires no artificial partition and
no row-count estimate. Its result does not establish the two structural
identities for `actualHighPresentation`: those remain part of the genuine
expansion construction. As with the rest of the deep actual chain, the
target consumer has not yet been elaborated by Lean.

### A restricted-piece consumer of the same original proposition

[ActualNormFormRegionTarget.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionTarget.lean)
adds `exists_target_highShiftedNormForm_region_connection`. Its conclusion
is again the literal `HighShiftedNormForm K c P`, using the original
block types, label types, row sets, means and `P.shiftedPiece`.

It first fixes `c`, `P` and `1 ∈ P.companions`, then chooses
`kappa,theta,N,C,Z0`. After the same contour-height and upper-detector-height
conditions, it takes a grid code for each original label. The code depends
on `Z,T,b,label`, and is independent of the row and integration point.
Its two remaining identities require the original `.mean` to equal
`actualRegionMean` of that code and the original `shiftedPiece` to equal
`actualRegionPiece` at `P.contourHeight`. The real arithmetic theorem
supplies the individual piece estimate internally, and summing it proves
the original bound with external height exponent zero.

This consumer does **not** assume equality of Euler-provider records.
The existing `rowZeroBelow_iff_of_calibrated` transfers the presentation's
detector to the arithmetic provider using the calibrated row-character
uniqueness theorem. The piece identity is explicitly with the arithmetic
provider's computed restricted integral. Equality of an arbitrary
provider's kernel with that integral is not inferred from character
uniqueness. The following module supplies the separate analytic
transport from the original initial-series calibration.

No norm-form conclusion, slot estimate, row count or amplitude-family
analytic field is a premise of this consumer. Its structural label and
piece identities still have to be proved for `actualHighPresentation`.
The declaration and its deep dependencies remain source candidates until
their actual native build and axiom audit succeed.

### Calibrated original providers on the same restricted regions

[ActualNormFormRegionCalibration.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionCalibration.lean)
adds the literal definition `actualRegionPieceWithEuler`. It integrates
`compensatedRowMellinKernel ... E` over the **same** computed
`actualSlotRegion`, with the original `(2*pi)^(-3)` normalization and
the three final contour lines. The region's arithmetic slot functions,
its code, and its mean are unchanged.

The source theorem `actualRegionPieceWithEuler_eq_of_calibrated` takes
the original `RowEulerCalibrationInput` for `E` and for
`arithmeticHighEulerData`, together with `51/100 ≤ a ≤ 1` and
`0 < e ≤ 1/10000`. Its conclusion is the exact equality

```lean
actualRegionPieceWithEuler K S μ P psi E g u Z a e H theta N label =
  actualRegionPiece K S μ P psi g u Z a e H theta N label
```

It applies
`HighBinEulerUniqueness.compensatedRowMellinKernel_ae_eq_vertical_of_calibrated`
from
[ActualEulerVerticalAE.lean](../../HeckeSkeleton/HighBinSupport/ActualEulerVerticalAE.lean),
restricts that almost-everywhere identity to the actual label region,
and uses `integral_congr_ae`. The strict swept-tube margins are `e`,
`e`, and `e` on the three final real coordinates. Thus the closed
`a = 1` endpoint and its negative `w` line remain covered. The theorem
does not ask for a separate measurability or integrability proof for
the original provider, and does not assume that a finite exceptional
table or its denominator is nonzero.

The final source consumer is
`HeckeSkeleton.HighBinNormFormRegionTarget.exists_target_highShiftedNormForm_calibrated_region_connection`.
It fixes `c`, the original presentation `P`, its original initial
calibration `hinit`, and `1 ∈ P.companions`; it then chooses
`kappa,theta,N,C,Z0` in precisely the same order as the preceding region
consumer. All height, grid-code, and original mean identities remain
unchanged. The required original shifted-piece identity now uses
`actualRegionPieceWithEuler ... P.euler`. Its equality with the arithmetic
piece is a conclusion of the transport theorem, rather than another
identity supplied by the caller. The arithmetic calibration is supplied
by the actual target's `targetRowEulerCalibrationInput`; the original
`FullHighEulerControl` already contains the presentation's initial
calibration through its `TRowEulerInput` component.

This removes the provider identity from the required per-label integral
identification. It does **not** construct that identification for an
arbitrary `P.shiftedPiece`, identify the original `.mean`, choose the
original expansion's labels or witness subdivisions, or discharge the
named `HB-NORMFORM`. Both new theorems and their deep actual dependencies
remain **unverified by native Lean** at this source snapshot. The
PR-WINDOW-PIT dependence of the transported norm bound is unchanged.

### Identities still required of the named expansion

To construct the named presentation itself and use the finite-label
theorem as its source, all of the following genuine identifications
remain relevant:

| Required original field or fact | Concrete object needed from this chain |
|---|---|
| `.euler` / detector | Calibrated-character uniqueness transfers the detector. The new calibrated-region consumer uses the original `RowEulerCalibrationInput` to transport the original provider's literal integral; no record equality is needed. The older whole-row consumer still has its original record-equality premise. |
| `.companions` | A fixed original family containing `1` |
| `.e` | Positive, at most `1/10000`, and at most the original lambda margins divided by `100` |
| `.contourHeight` | The selected `internalHeight Z T kappa` |
| `.upperHeight` | A height sufficient for the detector at `2*internalHeight Z T kappa+2` |
| `.labels` | The fixed finite complete-slot grid, or a proved identified refinement |
| `.amplitudeSet.rows` | The nonempty computed height-region fibers of the retained fixed-bin row set, permitting overlapping rows |
| `.amplitudeSet.amplitude` | The values `min (label_i*theta) (a-1/2)` of that same label |
| `.amplitudeSet.mean` | `actualRegionMean` of that same grid label |
| `.shiftedPiece` | The literal `actualRegionPieceWithEuler ... P.euler` over the computed height region, with all original tests and normalizers; original initial calibration then identifies it with `actualRegionPiece` |
| `.block_identification` | The original expansion block value equals the sum of these actual pieces |
| `.shifted_identification` | The computed regions partition each retained row's box and preserve the original fixed-bin contour sum |

The selected-zero height and the upper-zero height are distinct choices
in the original presentation. Their required arithmetic/bin support
identities must also be established; the norm-form estimate does not
choose them by changing an existing definition.

The wider expansion also contains `AmplitudeSet.slotValue` and genuine
inverse/plain witness subdivisions, defined in
[TIPSources.lean](../../HeckeGeneral/Analysis/TIPSources.lean). The actual
normalized values `pScale^(4/25) * S_i(point(u,label))` now populate the
constructed amplitude sets' slot values, using the same actual point
for all slots. Their transfer to the named expansion, and the
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

The original construction also has a wider quantifier range than the
eventual norm theorem: `ActualHighPresentation` requires its support and
sum identities for every `Z ≥ 1` and `T ≥ 1`. The new global measurable
partition and exact sum theorem separate that structural issue from the
norm estimate, but the exact sum theorem still requires genuine kernel
integrability. The current complete analytic chain supplies it only
after its large-row cutoff. `Expansion.expansion_blocks` does not fill
this gap: it is itself an admitted obligation, applies only eventually
with `T = Z^tau`, and its `BlockSource` shell lower bound is `1/100`,
whereas `ActualHighPresentation.shell_range` requires `1/16`.

No existing physical-probe-to-initial-row-integral identity or instantiated
buffered-bin construction was found in this review. The source
`TFixedBinTransferInput` explicitly leaves that initial identity open.
The literal `rowZeroAbove` and `rowZeroBelow` both include their real
boundary; adjacent complete zero bins can therefore overlap at a shared
boundary zero. A future expansion construction must account for that
when proving its total identity. The presentation does not itself demand
disjoint block row sets, and this observation does not assert that its
construction is impossible.

### Review of possible restricted-height label pieces

A direct review of the original types, repeated against upstream
`245e38879fecf3d4a52655c027ac14eb3bf178f2`, found **no representation of an
original label as a measurable height region**. The new concrete regions
in Section 6 supply such objects for the actual slot functions, but the
original named expansion has not yet been identified with them:

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

For the named presentation to use restricted-height pieces, the remaining
identification theorem must select the constructed regions for each
original label. For each actual `K,c,P,Z,T,b`, this supplies a map of type

```lean
regions : HighLabel K c Z T b → HighRow K c → Set (ℝ × (ℝ × ℝ))
```

and, for every `ℓ ∈ P.labels Z T b` and every original retained row
`u ∈ (block.amplitudeSet ℓ).rows`, must retain

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
`ℝ × (ℝ × ℝ)` restricted to the constructed region. The equality with
the original `P.shiftedPiece` is still a **missing identification**.
Measurability, the subset property and the integral formula for the new
`actualRegionPiece` itself are now supplied by the concrete region chain;
the calibrated-provider transport also identifies its integral with the
literal integral using `P.euler`. Neither fact forces equality with the
opaque original presentation's `shiftedPiece`.

If the total decomposition is to be recovered from these regions, it
also needs the almost-everywhere finite indicator identity: for each
row of the original fixed bin and almost every height in the original
box, the sum of the region indicators over labels retaining that row
equals one. Merely allowing overlapping row sets does not provide
this identity. Conversely, a total-sum identity cannot force a
per-piece norm estimate: changing two pieces by opposite complex
quantities preserves the total while their individual norms can grow.

There is a second independent identification needed for the requested
exponent. The original label's amplitude vector and mean must equal the
computed `actualRegionAmplitude` and `actualRegionMean` of its assigned
grid label. The new restricted integral theorem proves the estimate with
this precise region mean. It does not substitute the whole-box maximum
mean from `ActualFullSlotAmplitude`. Thus the analytic region estimate is
now available as source code, while its equality with the named
expansion's `.mean` remains a construction obligation.

The existing whole-row target consumer remains explicitly conditional on
its stronger whole-row piece identity. The new region chain avoids that
identity for the pieces it constructs. Neither route changes the opaque
`Base.highExpansion`, fabricates a witness subdivision, or derives a
per-piece identity merely from the original total-sum identity.

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
Source SHA-256: `b17d13b31c842b214e1af4d2b14560fc63d04a5b2debe87765f4bcdf809dba6d`.

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
Source SHA-256: `59fec086818ec36437e9e927f62cd56ddf94edc88f70e599e65678a7674126af`.

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
Source SHA-256: `59fec086818ec36437e9e927f62cd56ddf94edc88f70e599e65678a7674126af`.

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
Source SHA-256: `5f8a37404d4f6339a6ce96ad30000af200f03e4b0b3b3908e293e8fe5127d348`.

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


### `HighBinVerified.NormFormRegions.actualSlotHeightProfile_measurable`

Source: [ActualNormFormRegions.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegions.lean). SHA-256: `9c311bc0844b7e007af00ddaccf2b8e7ff4721ba4c0781fc3882c535731119fc`.

This uses the set/Fintype context in Section 2 and no Borel or Haar inputs. The finite ray filter `T` is arbitrary. All real scales are included, and complex division is measurable even where its denominator vanishes. This is an unelaborated source signature.

```lean
theorem actualSlotHeightProfile_measurable
    (P : ProbeData K S) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (Z a e : ℝ)
    (ha : 51 / 100 ≤ a) (he : 0 < e) (i : Fin g.slots) :
    Measurable (actualSlotHeightProfile K S P psi g T u Z a e i)
```


### `HighBinVerified.NormFormRegions.actualSlotRegion_measurable`

Source: [ActualNormFormRegions.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegions.lean). SHA-256: `9c311bc0844b7e007af00ddaccf2b8e7ff4721ba4c0781fc3882c535731119fc`.

This uses the set/Fintype context in Section 2 and no Borel or Haar inputs. All scales, heights, meshes and finite grids are included. No slot cap or integrability assertion is a hypothesis. This is an unelaborated source signature.

```lean
theorem actualSlotRegion_measurable (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z a e H theta : ℝ)
    (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (ha : 51 / 100 ≤ a) (he : 0 < e) :
    MeasurableSet (actualSlotRegion K S P psi g u Z a e H theta N label)
```


### `HighBinVerified.NormFormRegionIntegral.sum_actualRegionPiece_eq_rowContourBox`

Source: [ActualNormFormRegionIntegral.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionIntegral.lean). SHA-256: `0ecd715ec1c608f87e5667775d5a7e6783fdf63ba7adfe56494723efdf8c3794`.

This uses the finite-set/Borel/Haar context in Section 2. Its only analytic premise is genuine integrability of the literal kernel on the literal height box. It establishes the exact finite sum without assuming a norm bound or asserting all-scale integrability. This is an unelaborated source signature.

```lean
theorem sum_actualRegionPiece_eq_rowContourBox
    (P : ProbeData K S₀) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (u : FrequencyRow K S₀) (Z a e H theta : ℝ) (N : ℕ)
    (ha : 51 / 100 ≤ a) (he : 0 < e)
    (hi : IntegrableOn (actualRegionKernel K S μ P psi g u Z a e) (heightBox H)) :
    (∑ label : Fin g.slots → Fin (N + 1),
      actualRegionPiece K S μ P psi g u Z a e H theta N label) =
      rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z H
        (a + 16 * e) (1 - a - 6 * e) (17 / 50)
```

### `HighBinVerified.NormFormRegionIntegral.exists_actual_region_normForm_quarter_loss`

Source: [ActualNormFormRegionIntegral.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionIntegral.lean). SHA-256: `0ecd715ec1c608f87e5667775d5a7e6783fdf63ba7adfe56494723efdf8c3794`.

This uses the finite-set/Borel/Haar context in Section 2. `actualSlotRegion`, `actualRegionMean` and `actualRegionPiece` are the computed objects from Section 6. `ActualRegionSlotBounds` is an output proposition containing the actual slot upper bounds and same-point strict lower witnesses. This is an unelaborated source signature.

```lean
theorem exists_actual_region_normForm_quarter_loss
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
      (∀ label : Fin g.slots → Fin (N + 1),
        MeasurableSet (actualSlotRegion K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) ∧
        ActualRegionSlotBounds K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label ∧
        IntegrableOn (actualRegionKernel K S μ P psi g u Z a e)
          (actualSlotRegion K S₀ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label) ∧
        ‖actualRegionPiece K S μ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label‖ ≤
          C * Z ^ (NormForm.rowExponent d a (actualRegionMean g a theta N label) + lam / 4)) ∧
      (∑ label : Fin g.slots → Fin (N + 1),
        actualRegionPiece K S μ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) =
        rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
          (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)
```


### `HighBinVerified.NormFormRegionPacket.exists_actual_region_packet_normForm_quarter_loss`

Source: [ActualNormFormRegionPacket.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionPacket.lean). SHA-256: `2cdbbb583f42586a55f5f774a63c8588c3bb24b5e60e3670fadef14565b5fbb3`.

This uses the finite-set/Borel/Haar context in Section 2. The row sets are the nonempty computed regions, and the original TIP amplitude-set and block constructors are described in Section 6. Their subdivision recipes are not inputs to this norm estimate. This is an unelaborated source signature.

```lean
theorem exists_actual_region_packet_normForm_quarter_loss
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
      (∀ label : Fin g.slots → Fin (N + 1),
        (∀ u ∈ actualRegionRows K S P psi g F Z a e
            (NormForm.internalHeight Z T kappa) theta N label,
          ActualRegionSlotBounds K S₀ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label) ∧
        (∑ u ∈ actualRegionRows K S P psi g F Z a e
            (NormForm.internalHeight Z T kappa) theta N label,
          ‖actualRegionPiece K S μ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label‖) ≤
          C * ((actualRegionRows K S P psi g F Z a e
            (NormForm.internalHeight Z T kappa) theta N label).card : ℝ) *
            Z ^ (NormForm.rowExponent d a (actualRegionMean g a theta N label) + lam / 4)) ∧
      (∑ label : Fin g.slots → Fin (N + 1),
        ∑ u ∈ actualRegionRows K S P psi g F Z a e
          (NormForm.internalHeight Z T kappa) theta N label,
        actualRegionPiece K S μ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) =
        ∑ u ∈ F, rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
          (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)
```


### `HeckeSkeleton.HighBinNormFormRegionTarget.exists_target_highShiftedNormForm_region_connection`

Source: [ActualNormFormRegionTarget.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionTarget.lean). SHA-256: `d24c33ede39588c65cf39c4251105accf092260eeca608c4ee23d507271f6f23`.

The target supplies its original Borel and Haar instances. PresentationRegionLabels is a code depending only on Z,T,b,label. The statement has no Euler-record equality premise; calibrated-character uniqueness transfers the detector. The original named mean and piece identities remain explicit. This is an unelaborated source signature.

```lean
theorem exists_target_highShiftedNormForm_region_connection
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hcomp : (1 : HeckeCharacter K) ∈ P.companions) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ((∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          P.contourHeight Z T b = NormForm.internalHeight Z T kappa) →
      (∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          2 * NormForm.internalHeight Z T kappa + 2 ≤ P.upperHeight Z T b) →
      ∀ code : PresentationRegionLabels K c N,
        (∀ (Z T : ℝ), Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
          ∀ (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b),
          label ∈ P.labels Z T b →
          ((((targetData K c).expansion Z T).block b).amplitudeSet label).mean =
            actualRegionMean c.geometry (((targetData K c).expansion Z T).block b).bin
              theta N (code Z T b label)) →
        (∀ (Z T : ℝ), Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
          ∀ (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b),
          label ∈ P.labels Z T b → ∀ u : HighRow K c,
          u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows →
          P.shiftedPiece Z T b label u =
            actualRegionPiece K (targetData K c).S (targetData K c).measures.haar
              (targetData K c).probe (targetCharacter K c) c.geometry u Z
              (((targetData K c).expansion Z T).block b).bin P.e
              (P.contourHeight Z T b) theta N (code Z T b label)) →
        HighShiftedNormForm K c P)
```


### `HighBinVerified.NormFormRegionCalibration.actualRegionPieceWithEuler_eq_of_calibrated`

Source: [ActualNormFormRegionCalibration.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionCalibration.lean). SHA-256: `5e50743ac1fd8574cbce4cd8a41041a245d9c83ff109359587f2c35a8cbaf996`.

The section context is the finite-S Borel/Haar context in Section 2. Both calibration hypotheses are the original RowEulerCalibrationInput. No measurability, integrability, nonvanishing or norm estimate for the arbitrary provider is supplied. This is an unelaborated source signature.

```lean
theorem actualRegionPieceWithEuler_eq_of_calibrated
    (P : ProbeData K S₀) (psi : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (hE : RowEulerCalibrationInput K S₀ P psi E)
    (hA : RowEulerCalibrationInput K S₀ P psi (arithmeticHighEulerData K S₀ P psi))
    (g : PrimeWindowGeometry) (u : FrequencyRow K S₀)
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    actualRegionPieceWithEuler K S μ P psi E g u Z a e H theta N label =
      actualRegionPiece K S μ P psi g u Z a e H theta N label
```


### `HeckeSkeleton.HighBinNormFormRegionTarget.exists_target_highShiftedNormForm_calibrated_region_connection`

Source: [ActualNormFormRegionCalibration.lean](../../HeckeSkeleton/HighBinSupport/ActualNormFormRegionCalibration.lean). SHA-256: `5e50743ac1fd8574cbce4cd8a41041a245d9c83ff109359587f2c35a8cbaf996`.

The target supplies its original Borel and Haar instances. The constants precede every scale, block, label and row. The structural shifted-piece identity uses the original P.euler; the theorem transports its literal restricted integral using the original initial calibration. This is an unelaborated source signature.

```lean
theorem exists_target_highShiftedNormForm_calibrated_region_connection
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (hcomp : (1 : HeckeCharacter K) ∈ P.companions) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ((∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          P.contourHeight Z T b = NormForm.internalHeight Z T kappa) →
      (∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          2 * NormForm.internalHeight Z T kappa + 2 ≤ P.upperHeight Z T b) →
      ∀ code : PresentationRegionLabels K c N,
        (∀ (Z T : ℝ), Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
          ∀ (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b),
          label ∈ P.labels Z T b →
          ((((targetData K c).expansion Z T).block b).amplitudeSet label).mean =
            actualRegionMean c.geometry (((targetData K c).expansion Z T).block b).bin
              theta N (code Z T b label)) →
        (∀ (Z T : ℝ), Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
          ∀ (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b),
          label ∈ P.labels Z T b → ∀ u : HighRow K c,
          u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows →
          P.shiftedPiece Z T b label u =
            actualRegionPieceWithEuler K (targetData K c).S (targetData K c).measures.haar
              (targetData K c).probe (targetCharacter K c) P.euler c.geometry u Z
              (((targetData K c).expansion Z T).block b).bin P.e
              (P.contourHeight Z T b) theta N (code Z T b label)) →
        HighShiftedNormForm K c P)
```
