# Canonical inverse induction

This directory contains the relative induction consumer for §4.5 and
Theorem 4.1, using explicit source data and local analytic inputs. The
original `HeckeSkeleton.canonical_inverse_models` remains a separate
unresolved declaration; see [STATEMENT_AUDIT.md](STATEMENT_AUDIT.md).

## Main statements and assumptions

`ActualMoments.canonical_inverse_models` bounds the repository's literal
`HeckeGeneral.Analysis.ConditionalMoments.inverseEnergy` for an explicitly
supplied `MomentData`. `CanonicalDatum.energy` is the actual normalized
finite ideal sum with the canonical coefficient, squarefree labels,
product-form prime marks and common puncture. Neither energy is a field
of the input records.

The local inputs are explicit:

1. `StepEnergy` and `StepGeometry` give one two-transform reduction, its
   exact prefactors, positive frozen-triple measure, child row decrease
   and two child margins.
2. `CanonicalInputs.terminal_labels` gives the three reflected terminal
   exponents on genuine terminal blocks. The terminal classifier also
   records short label and short extracted-cube conditions. The fixed
   physical `CompletedMarkedEnergy` in the skeleton does not currently
   provide this general transport.
3. `InitialInputs` gives the initial masked Poisson reduction of the
   source inverse polynomial, with its actual overlap, puncture and
   clipping lengths.
4. Constants `C`, `L`, `A`, the margin, and the loss budget are common to
   the entire source family. `Uniform.lean` preserves this quantifier
   order; it does not infer it from per-row slice bounds.

From these inputs, the proof constructs a finite depth and simultaneous
loss budget, proves both margins stay at least half the initial margin,
derives the initial row and total-length bounds from the source's marked
margin, closes the recursion, restores the initial normalization, and obtains
the uniform bound

\[
E_{\mathrm{inverse}}\le (9CL)^{D+1}
  Z^{m+\varepsilon}H^{A(D+1)}.
\]

`canonical_unmarked_inverse` applies the same proof to the literal
sixth-free unmarked ball energy with independent `U,D`, using
`D ≤ U^(1/(1+a))`. The logarithmic reparameterization includes `U=D=1`.
An eventual source construction still requires a separate bounded-scale
estimate; the corresponding gluing lemma is explicit.
The uniform sector versions sum the actual fixed finite sector family;
the common scalar acquires a factor of at most the number of sectors plus
one, while the height order stays unchanged.

`CompletedEnergyTransport` supplies a separate bridge from the exact
general-data physical hypothesis `LowCauchy.MarkedEnergy`. It proves the
finite-row estimate from an exact row-polynomial realization in the physical
marked polynomial, an injective map into the original orbit space, and
the actual support and scalar bounds. It then performs the normalized
label sum with a single mass factor. Constructing these realizations for
all canonical terminal backgrounds, punctures, labels and profiles is
still an explicit unresolved obligation.

## Proof modules

| Module | Content |
| --- | --- |
| `Interface` | Consumer-side one-step statement; prefactors remain separate |
| `InductionGeometry` | Simultaneous budget, strict margins, finite branch length, terminal gains |
| `InductionClosure` | Finite backward induction and canonical admissibility |
| `EnergyClosure` | Weighted child-energy consumption; explicit constants and height order |
| `Terminal` | Three terminal branches and exact single cancellation of label mass |
| `CanonicalEnergy` | Literal canonical ideal sums and normalization identities |
| `CompletedEnergyTransport` | Exact physical-energy transport through injective row realizations |
| `CanonicalClosure` | Geometry and analytic recursion combined |
| `InitialTransfer` | Initial margins, overlap prefactor and source-energy transfer |
| `InductionCapacity` | Marked capacity, independent scales and bounded-scale gluing |
| `ActualMoments` | Corrected relative endpoints on the actual ideal polynomials |
| `Uniform` | Common constants for an entire parameter family and its finite sector sum |
| `Audit` | Clean declarations and their axiom lists |
| `CompletedEnergyTransportAudit` | Independent audit of the physical-energy adapter |
| `OriginalAudit` | Separate audit of the original skeleton target |

## Remaining source integration

The directory does not construct the two Poisson transforms, the initial
source reduction, or the transport from the fixed physical energy to all
canonical terminals. Those are visible hypotheses, not admissions.
The existing skeleton source types transitively use `highExpansion`,
`rows_in_norm_envelope`, `momentModels`, and `finiteMellinData`, which are
admitted in the task's base commit. Consequently replacing only the
original theorem's proof cannot give that declaration a clean axiom list.
The original theorem has not been weakened, renamed or silently replaced.

## Verification

Use the pinned Lean `4.35.0-rc3` and Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`:

```sh
lake build HeckeSkeleton.Moments.MOM_INV_INDUCTION.Audit
lake env lean HeckeSkeleton/Moments/MOM_INV_INDUCTION/Audit.lean
lake build HeckeSkeleton.Moments.MOM_INV_INDUCTION.CompletedEnergyTransportAudit
lake env lean HeckeSkeleton/Moments/MOM_INV_INDUCTION/CompletedEnergyTransportAudit.lean
lake build HeckeSkeleton.Moments
lake env lean HeckeSkeleton/Moments/MOM_INV_INDUCTION/OriginalAudit.lean
```

The dedicated Actions workflow has separate mandatory jobs for the new
relative theorem, the physical-energy adapter, and the original skeleton
theorem. Each enforces the
allowlist `{propext, Classical.choice, Quot.sound}`; the original job must
report a failure while its admissions remain. Compiler logs, environment
details, and axiom reports are uploaded as Actions artifacts. They are not
committed to the repository.

Implementation and review were AI-assisted with GPT-6 Astra Pro.
