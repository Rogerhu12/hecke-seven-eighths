# Actual physical Poisson normalization

## The correction

The Fourier transform used by the physical probe is the mixed-space Fourier
integral with Lebesgue measure, multiplied by the local Fourier integrals
divided by the Haar masses of the local integer rings. For exactly this
transform, the proved S-integer Poisson theorem has the positive scalar

\[
c_K=\frac{2^{r_2(K)}}{\sqrt{|\operatorname{disc}K|}}.
\]

The previous physical residue normalizer omitted this scalar. The same
scalar was also absent from the displayed Poisson row kernel. Including it
in both locations preserves every numerical row kernel and corrects the
normalization of the literal compensated physical probe. The final theorem,
the principal line signal, all contours, all prime windows, and all detector
exponents remain the same.

This is a definition correction, not a new analytic assumption. It uses the
actual discriminant and the already proved Poisson formula. No exact physical
identity, target bound, zero error, or freely chosen residue is added as data.

## Original and corrected definitions

Write the previous literal residue expression as

\[
N_0=\tfrac16 R_S^2\,\mathcal M(\tfrac16)\,
       \widehat W_{1,\mathrm{add}}(1),
\]

where `R_S = deletedZetaResidue K S` and `M = additiveMellin K S μ P.additive`.
Write `A(u,Z;s,w,z)` for the entire previous row numerator, including its
actual finite prime-tuple/subset compensation. Let `Nprime(Z)` be the
unchanged `primeNormalizer`.

| Object | Previous definition | Corrected definition |
| --- | --- | --- |
| `physicalResidueNormalizer` | `N₀` | `(c_K : ℂ) * N₀` |
| `normalizedProbe` | `compensatedProbe / (N₀ * Nprime)` | `compensatedProbe / ((c_K * N₀) * Nprime)` |
| `compensatedRowMellinKernel` | `A / (N₀ * Nprime)` | `((c_K : ℂ) * A) / ((c_K * N₀) * Nprime)` |
| `additiveFourier`, `additiveFourierAtZero`, `additiveMellin` | Original actual transforms | Unchanged |
| `principalLineProbe` | Original height-independent line integral | Unchanged |

`physicalPoissonScalar_pos` and `physicalPoissonScalar_ne_zero` prove the
required positivity and nonvanishing. `physicalResidueNormalizer_cancel`
proves exact cancellation for arbitrary complex numerator and remaining
denominator; it does not require nonvanishing of either Mellin value or the
prime normalizer. Consequently `compensatedRowMellinKernel_eq_unscaled` is an
identity with the complete previous literal row formula at every scale.

`normalizedProbe_eq_unscaled` records the distinct change to the physical
probe itself: the new normalized probe is `c_K⁻¹` times the previous one.
This gives leading principal-residue coefficient one once the actual Poisson
and residue calculation is connected. The scalar is not silently absorbed
into the principal signal.

## Literal source audit

The statements below concern the definitions present before this correction.

1. `HeckeGeneral/Analysis/PhysicalProbePrincipal.lean`, original lines
   116–139, defines Fourier/Mellin using mixed Lebesgue measure and the
   inverse masses of the local integer rings. Original lines 142–149 define
   `N₀` and divide the compensated probe only by `N₀ * Nprime`.
2. `HeckeGeneral/Bridge/SIntegerFourierFactorization.lean`, lines 87–109,
   proves that the actual normalized adelic Fourier transform is `c_K`
   times this mixed/normalized-local tensor. The actual standard trace
   character is retained.
3. `HeckeGeneral/Bridge/TraceSchwartzFourier.lean`, lines 141–179, identifies
   the trace-Schwartz transform with that same mixed Fourier integral. Its
   inverse Jacobian is already accounted for; it does not remove the
   separate discriminant factor in Poisson.
4. `HeckeGeneral/Analysis/SIntegerPeriodicOrbitalPoisson.lean`, lines
   138–153, displays `r⁻¹ * c_K * q_c⁻¹` and keeps both actual zero terms.
   The primal and dual orbital profiles use the same norm-one Haar measure.
5. `HeckeGeneral/Analysis/LocalThetaInput.lean`, lines 39–52 and 82–91,
   contains arithmetic generator/root data and the finite Gauss normalization
   `q_I⁻¹/²`. `GlobalThetaData.lean`, lines 51–72, contains the literal
   completed ideal sum. Neither introduces an inverse `c_K`.
6. `HeckeAxiom/ProbeNormalization.lean` identifies the deleted residue with
   the actual Dedekind-zeta residue times the deleted Euler factors. Both
   occurrences of this residue are the same arithmetic quantity; its class
   number formula does not cancel an additional external Poisson scalar.
7. `HeckeAxiom/ProbeTestChoice.lean`, lines 134–149 and 183–217, explicitly
   compares its test to the Axiom Fourier convention using `kappa`. This
   changes the test/Fourier comparison, not the Poisson lattice factor.
   Rescaling the chosen test rescales both the physical probe and `N₀`, so
   it cannot remove the residual ratio `c_K`.

There is no declaration named `physicalResidueData` in this repository.
The relevant actual interfaces are `ProbeData`, `physicalResidueNormalizer`,
`ProbeIntegralInput`, and `TPrincipalInput`.

## Paper locations and compatibility

The repository paper `weil_seven_eighths_revised.tex` uses a different,
covolume-one additive normalization:

- Lines 446–448: arithmetic calibration states that the S-integer lattice
  is self-dual with covolume one.
- Lines 489–495: the adelic-Poisson argument gives scalar one in that
  normalization.
- Lines 3275–3281: the physical-probe section explicitly adopts that
  arithmetic normalization.
- Lines 3313–3319: `M` is the Mellin transform of the corresponding Fourier
  transform.
- Lines 3364–3367: the Poisson multiplier after the square-root factors is
  `X^(1/2) / q_A` in that normalization.
- Lines 3369–3388: the initial triple-Mellin expansion uses that multiplier
  and the same common transform `M`.
- Lines 3524–3531: the principal residue is `(1/6) R_S² M(1/6) Ŵ₁(1)`;
  the text explicitly says that a different fixed measure normalization
  changes this scalar by a nonzero constant.
- Lines 3535–3542: division by that actual residue produces the fixed
  principal line signal with coefficient one.

The corrected definition implements precisely the fixed-measure adjustment
allowed by lines 3529–3531. It does not change the final zero-free/nonvanishing
statement or replace any source function with an arbitrary function.

## Consumer impact

| Consumer | Required change |
| --- | --- |
| `HeckeAxiom.ProbeNormalization.physicalResidueNormalizer_pos` | The displayed real value gains the positive factor `physicalPoissonScalar K`; the statement and hypotheses are unchanged. |
| `HeckeSkeleton.Principal` | Existing wrappers retain their statements and call the corrected positivity theorem. |
| `TPrincipalInput` / principal source | Realness and positivity fields refer to the corrected actual normalizer; no new field or premise. The principal line signal is unchanged. |
| `HeckeSkeleton.LowCauchy.General.lc_normalizedProbe_isBigO` | No statement or proof change: its proof already multiplies by the arbitrary fixed constant `physicalResidueNormalizer⁻¹` at lines 609–613. |
| `CompensatedRowKernelFactorization` | Its displayed numerator gains `c_K` while its denominator continues to name the actual corrected normalizer. The same finite algebra proof applies. |
| HIGHBIN local corrections, prime slots, characters, masks | No change: these do not contain the global Fourier-measure scalar. |
| Bounds using the displayed kernel factorization | Absorb `c_K` in a fixed constant, or use the proved cancellation identity. No scale-dependent exponent or height quantifier changes. |
| `rowContourBox` and physical block values | No numerical change because their integrands satisfy the unconditional cancellation identity. |

## New actual Fourier/Poisson bridge and remaining work

`Expansion/PhysicalFourierNormalization.lean` proves pointwise identities
between the actual physical test/Fourier test and the genuine upstream
Poisson tensors, including the actual values at zero. Its
`probePeriodicOrbitalPoisson` specializes the proved orbital theorem to
`P.additive` and `P.arithmetic.different_outside`, retains every original
subgroup sector, and displays `c_K` explicitly. The coefficient assumption
is only literal subgroup invariance of a finite periodic coefficient.
There is no assumed Poisson identity or convergence premise.

This bridge is not yet the complete compensated physical-probe expansion.
The actual product of the Gauss coefficient and residue symbol still needs
its quotient-periodicity/finite-transform bridge, followed by the actual
completed-theta sums, orbit-to-sixth-power row reindexing, absolute Mellin
interchanges, and initial Euler calibration. The zero frequency must be
removed using the actual chosen test theorem, not by defining a zero error.

Validation status at authoring: source proofs written without `sorry`,
`axiom`, or `native_decide`; compilation and the new `#print axioms` outputs
are pending the single coordinated CI build. This document does not label
uncompiled declarations as verified.
