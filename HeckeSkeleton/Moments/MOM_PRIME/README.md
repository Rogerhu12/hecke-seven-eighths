# MOM_PRIME: the actual prime endpoint and exceptional terminal

This task proves the absolute prime endpoint in manuscript §4.6 and the
same-mask, equal-product exceptional terminal in Lemma 4.11 (§4.7).
The results use the repository's actual ideal coefficients, finite prime
products, row sets, common masks, and finite plain polynomials.

## Actual prime endpoint

The original `HeckeSkeleton.paired_primes_endpoint` calls
`actual_recipe_paired_primes_endpoint`. Its existing signature is preserved.
The proof supplies the absolute endpoint before the calibration,
row-eligibility, profile-control, and `B = 1` hypotheses are used downstream.

`RecipeEndpoint.lean` uses the canonical source and the same explicit
recipe for every index and model. The actual slot count is the cardinality
of the selected set, the total length is `selectedLengthFor`, and the
frozen windows keep their original annular support. A common upper bound
on the real parts of their powers gives a profile bound before every
source index, scale, sector, and height.

`ActualEndpoint.lean` computes the physical power's real part as `-33/50`.
The physical row width is the dyadic exponent `rho`, with `U^rho = 2*U`.
Consequently the actual finite sector/row sum satisfies

```text
sum_sector sum_u ||slotProduct u||^2 <= C * U^(1 + selectedLength).
```

The fixed factor two is absorbed into the constant. The source's uniform
quantifier order holds with height order zero, ceiling one, and threshold
one. Both empty-slot and positive-slot row filters are retained.

The auxiliary fixed-window and general profile-family endpoints in
`Endpoint.lean` and `ProfileEndpoint.lean` remain available. The actual
source proof uses its true dyadic width directly.

## Constructed exceptional analytic input

| Module | Result |
| --- | --- |
| `AnnularMellin` | Mellin inversion of the actual finite annular ideal sum on an absolute line. |
| `ExceptionalContinuation` | Polynomial control of the actual principal pole numerator and nonnorm Hecke continuation, with the actual residue. |
| `ExceptionalAnnular` | Exact contour shift from `Re(s)=11/10` to `Re(s)=0`, crossing the principal residue. |
| `ExceptionalAnnularBounds` | A remainder uniform over every positive scale, controlled by finite Euler seminorms of the original test and polynomial norm-phase height. |

For a norm-reduced character `chi`, a smooth annular test `W`, and every
`X > 0`, the unmasked sum has the form

```text
sum_I chi(I) * N(I)^(i*t) * W(N(I)/X)
  = poleCoefficient(chi) * X^(1+i*t) * integral(W(y)*y^(i*t), y>0)
    + error.
```

The pole coefficient is the actual Dedekind-zeta residue for `chi = 1`
and zero for a nonnorm character. The order and constant precede `W`, `t`,
and `X`. Moving the norm phase into the Mellin argument expresses the
error bound through a translated fixed integrable envelope.

The analytic statements use a totally complex field and the alternative
`chi = 1` or `chi` is not a global norm twist. The original source supplies
these facts: `isComplex_of_family` follows from its primitive twelfth root.
`ExceptionalNormReduction.lean` proves norm reduction for a radially
normalized generator, its finite-order backgrounds, and the permitted
plain backgrounds with finite-order row characters. It uses the generic
`MomentData` interface without the physical source construction.
`ExceptionalBackgrounds.lean` retains the actual paired-model specialization
from `targetCharacter_radial_zero` and re-exports all these generic results,
so existing imports remain compatible.

## Lemma 4.11 with the original seminorm

`ExceptionalAnnularTerminal.lean` inserts the original common mask by
finite inclusion-exclusion. The divisor phase cancels the reciprocal phase
at scale `X/N(D)`, giving the actual coefficient

```text
heckeExceptionalResidue chi R
  = poleCoefficient(chi) * sum_(D|R) mu(D) * chi(D) / N(D).
```

`exists_actualMaskedExceptional_bound` gives the all-scale asymptotic
uniformly for `R != bottom`, `N(R) <= Z^B`, `Z >= 1`, `B >= 0`, and any
prescribed positive loss `epsilon`.

`exists_actualAnnularExceptional_equal_product_seminorm` chooses `J`, `N`,
and `C > 0` before the tests, mask, phase, and four scales. For a fixed
annulus upper bound `b`, if `X1*X2 = Y1*Y2 = T`, `a >= 0`, and all four
scales are at least `Z^a`, the normalized difference is bounded by

```text
C * Z^epsilon * sqrt(T) * Z^(-a)
  * (testSeminorm W1 J 0 + testSeminorm W2 J 0)^2
  * (1 + ||t||)^N.
```

The all-scale asymptotic and absolute ideal count also control the actual
main coefficient. The final bound therefore retains a single divisor
loss `Z^epsilon`. An absolute fallback covers all positive scales with
equal products.

`ExceptionalAnnularFiniteFamily.lean` chooses a common seminorm order,
height degree, and constant for a fixed finite family of backgrounds,
including the empty family.

`ActualExceptionalMomentBridge.lean` transfers the constructed analytic
result to the original finite `plainPolynomial`. Its hypotheses identify
the actual character, common mask, and phase-carrying tests pointwise.
The two equal products preserve the same total phase during normalization.
This bridge imports `ExceptionalNormReduction` directly; the source-specific
specialization and its `SourceData` dependency remain in
`ExceptionalBackgrounds` and the full audit.

`ActualExceptionalFiniteFamilyBridge.lean` chooses the constants before
every family member and original model or row. Its canonical specialization
uses one radially normalized generator and a fixed finite family of
finite-order twists. Character membership, mask equality, and test-phase
identities are explicit identifications of the original summands.
The same module's seminorm fallback covers every positive scale without
requiring character reduction or a lower-length assumption.

## Ordinary masks and reusable interfaces

`OrdinaryMasks.lean` proves the exact normalized divisor identity, with
coefficient `mu(D)*chi(D)*N(D)^(i*t)/sqrt(N(D))` and scale `X/N(D)`.
`OrdinaryMaskMass.lean` gives uniform subpower coefficient mass for
polynomial-size masks, and `AbsoluteMasks.lean` gives absolute deletion
bounds. The earlier exceptional modules retain their reusable algebraic
consumers; the new annular chain constructs the needed residue and error.

## Shared source prerequisites

The canonical source, actual recipe, and required import closure are
consumed from PR #5 commit `0263481ab8c8f2ef30d909f6a665ed22d64e5b8c`.
They replace the former admitted source/model objects with the same
constructed recipe. Shared profile control is the owner's
`MOM_UNIFORM_AMPLIFY/ProfileControl` interface.

Imported source proofs needed native API/elaboration repairs:
`PhysicalCompletedPoisson`, `PhysicalRecipeAssembly`,
`ActualRowKernelHolomorphy`, `ActualNormFormFullCorrection`,
`SmallRowCorrection`, `PhysicalInitialMellinTerm`,
`ActualPrincipalInitialTransport`, `ActualModerateSweepHolomorphy`,
`ActualOuterKernelDecay`, `PhysicalInitialMellinAbsolute`,
`LargeRowAllScales`, `SmallRowKernel`, `PrincipalRowLocal`,
`ActualModerateCorrectionBound`, `LargeRowKernel`,
`ActualPrincipalKernelBound`, `ActualPrincipalZShift`, `ActualModerateKernelDecay`,
`PhysicalInitialRowSum`, `PhysicalInitialMellinIdentity`, and
`PhysicalInitialRowTruncation`, together with `SmallRowSum`,
`PhysicalCompensatedInitial`, `ActualPrincipalUniformDecay`,
`ActualPrincipalSweepDecay`, and `ActualPrincipalResidueAssembly`.
The joint-analytic repairs consume the source owner's proof fixes from
PR #5 commit `496aee9914912e54feac9fced688ce6e61bc7f6f`.
The initial-row-sum proof matches the owner's blob
`9a57bd1f04916c1ad4f0b40c42315ef6067f3cbe` exactly.
The initial moderate-kernel decay and row-truncation API repairs follow
the owner's blobs `daddc476018e69046ff9f4800b6a59cd2bbc5b8c` and
`b2fa94108ee705437a33a187020a2185b06629bf`; subsequent native failures
are resolved by explicit local bounds and an explicit box-height sum identity.
The principal residue-assembly proof matches the owner's blob
`347f7203afb77545ef38a60792324a3c758fa1d7` exactly.
Their existing statements and mathematical definitions are preserved.
The top-level zero-free theorem's statement is unchanged.

## Compilation and axiom gates

The environment is Lean `4.35.0-rc3`, with Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`.

```sh
lake --rehash build HeckeSkeleton.Moments.MOM_PRIME.Audit \
  HeckeSkeleton.Moments.MOM_PRIME.SkeletonAudit
lake env lean HeckeSkeleton/Moments/MOM_PRIME/Audit.lean
lake env lean HeckeSkeleton/Moments/MOM_PRIME/SkeletonAudit.lean
```

`Audit.lean` names the task interfaces and analytic producers.
`SkeletonAudit.lean` independently checks the original
`HeckeSkeleton.paired_primes_endpoint`. The workflow requires every
explicit audit record and checks that its axioms are contained in
`{propext, Classical.choice, Quot.sound}`.

The workflow restores the shared project cache and runs Lake with
`--rehash`. Build, environment, and axiom records are uploaded as Actions
artifacts; the environment record identifies the exact checkout.
