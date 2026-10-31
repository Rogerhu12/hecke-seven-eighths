# MOM_PRIME: absolute prime endpoint and exceptional cancellation

This directory implements the actual finite-polynomial endpoint and the
equal-product terminal consumers of manuscript §§4.6–4.7. The source-model
construction and the general-field volume input remain explicit interfaces.
The PR targets `dtests-handoff` from `cloud/mom-prime`.

## Endpoint statements

`exists_slotProductAbsoluteBound` works with the existing `MomentData`,
`primePolynomial`, and `slotProduct`. For at most `N` prime windows with
support in `(1, 2)` and profile norm at most `B * V ^ H`, it proves

```text
‖slotProduct d u Z t‖² ≤ C * Z^(d.geometry.totalLength) * V^(2*N*H).
```

Here `Z,V ≥ 1`, `B ≥ 0`, and `H ≥ 0`; the row-sum estimate also assumes
`0 ≤ a.m + a.q`. The constant is chosen before the actual data,
rows, masks, characters, lengths, scales, and heights. Linear ideal counting
then gives `exists_pairedPrimeAbsoluteBound`:

```text
∑ u ∈ pairedRows d a Z, ‖slotProduct d u Z t‖²
  ≤ C * Z^(a.m + a.q + d.geometry.totalLength) * V^(2*N*H).
```

The two branches of `pairedRows` and all original zero masks are retained.
These estimates require no additional zero-free premise, capacity condition, or
finite-order condition beyond the existing `MomentData` structure.

`AbsoluteGeometry.lean` derives the profile bound from the actual fixed
`PrimeWindowGeometry`. The one required identification is

```lean
d.geometry =
  ((momentPrimeGeometry K g).changeBase shell hshell).restrictSlots I
```

The bound is uniform over all positive shell lengths, all selections
(including the empty selection), and every other field of `MomentData`.
Its exponent is the literal sum of the existing `TIP.slotLength`.

`PrimeEndpointFamily` records this geometry identification and row width
`m + q = 1` for an arbitrary dependent index family and finite sector type.
The new theorem

```lean
HeckeSkeleton.Moments.MOM_PRIME.paired_primes_endpoint
```

proves the exact exponent `1 + selectedLength` after summing all sectors.
`paired_primes_endpoint_uniform` gives the source's required quantifier
order with height order zero, ceiling one, and threshold one. Every
nonnegative exponent loss is permitted.

`AbsoluteMasks.lean` also proves the exact subtraction of the original
prime terms at primes dividing an additional mask, for each slot and
simultaneously for the full product. The row filters remain unchanged.
`OrdinaryMasks.lean` proves the actual
normalized divisor identity for the Hecke ideal sums and the original
`plainPolynomial`, with the exact coefficient `μ(D) χ(D) / sqrt(N D)` and
the shortened scale `X / N D`. `OrdinaryMaskMass.lean` bounds the absolute
coefficient mass, including an independent norm phase, by `C * Z^ε` when
the mask norm is at most `Z^B`. This constant precedes the character,
mask, height, and scale.

## Equal-product terminal

`ExceptionalTerminal.lean` retains the common mask and the common norm
phase. It proves exact finite Möbius deletion, exact extraction of the
scale/height-independent residue coefficient, direct absolute bounds for
all positive scales, and equal-product cancellation before absolute values.

For `ε > 0`, `B ≥ 0`, `Z ≥ 1`, a nonzero mask, and a whole profile family
with common support, seminorm control, and the explicit `IdealVolumeInput`
error estimate, one constant works for all profiles, masks of norm at most
`Z^B`, heights, and four scales. If `X₁*X₂ = Y₁*Y₂ = T`, `a ≥ 0`, and every
scale is at least `Z^a`, the normalized rectangle is bounded by

```text
C * Z^ε * sqrt(T) * Z^(-a) * (p(W₁)+p(W₂))² * (1+‖t‖)^n.
```

The proof uses an absolute bound for a complete factor and hence needs
only one divisor loss. A second theorem gives the absolute fallback
without any lower-length or volume-input assumption.

`ExceptionalHecke.lean` uses the real repository coefficient
`idealCoefficientHom (primeCoefficient K χ)`, identifies it with
`heckeIdealCoefficient` on nonzero ideals, and rewrites the original ideal
sum as a finite `boundedNormIdeals` sum. The main-term identification is
explicit; the nonprincipal branch is conditional on that identification.

`ExceptionalSmooth.lean` constructs the actual Schwartz realization of
`y^(it) W(y)` from smoothness and compact support away from zero.
`ExceptionalFiniteFamily.lean` makes the constants uniform over the finite
Hecke background family. `ExceptionalMomentBridge.lean` identifies the
original `plainPolynomial`, with arbitrary actual profile parameter and
an independent norm phase, with the normalized Hecke sum. The equal-product
and fallback estimates consequently apply to the original finite moment
polynomials.

## Interfaces still required from the other constructions

The source model must provide its actual prime-geometry calibration. The
old `WholeMomentProfileControl` controls only the inverse and two plain
`IdealTest`s. It contains no prime-window bound or slot-count bound. Its
height/shift bounds also apply only inside specified parameter ranges;
`SourceMomentModels` does not certify that its chosen values lie in them.
The geometry equality above is a sufficient replacement for the endpoint
and derives all of the needed prime-profile bounds automatically.

For the exceptional terminal, the analytic inputs are:

1. `IdealVolumeInput` for the actual Hecke ideal coefficients;
2. its uniform seminorm and polynomial-height error control;
3. identification of its density with the Hecke residue times the Mellin
   profile integral, when the full main-term formula is needed.

The equal-product estimate itself does not assume its desired conclusion.
The remaining inputs are unmasked linear volume estimates and profile
control, as in the existing `HeckePort/CenteredMoment/Volume.lean` interface.
They are not constructed here from general-field Tate continuation.

## Why the old skeleton declaration is unchanged

At base commit `182769d49e5c184547c0949ddc328b9e7a87e6f7`, the original
`HeckeSkeleton.paired_primes_endpoint` has two independent obstacles:

* Its hypotheses do not supply the missing prime-window calibration.
* Its **type** refers to `momentModels`, whose definition is admitted, and
  through `SourceMomentIndex` to admitted `highExpansion` and
  `rows_in_norm_envelope`. Lean's axiom collector traverses theorem types
  as well as proof terms. Replacing this theorem's own proof cannot remove
  those dependencies on `sorryAx`.

The task's rule against editing existing definitions therefore prevents an
honest claim that the original declaration passes the standard-axiom gate
in this PR alone. The clean endpoint theorem is parameterized over the
actual model data and its structural calibration. It is not presented as
an unconditional proof of the old admitted source construction. The old
`Moments.lean` is left unchanged.

## Reproduction and audit

The required environment is Lean `4.35.0-rc3` and Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`, exactly as pinned by the repository.

```sh
lake --rehash build HeckeSkeleton.Moments.MOM_PRIME.Audit
lake env lean HeckeSkeleton/Moments/MOM_PRIME/Audit.lean
```

The dedicated `mom-prime.yml` workflow checks the explicit `#print axioms`
records against `{propext, Classical.choice, Quot.sound}` and rejects
missing records. Environment, build, and audit logs are uploaded as an
Actions artifact and are not committed to the repository. The PR records
the observed verification status and links to its exact commit/run.

The workflow may seed dependency artifacts from pinned archive digests.
Only facets in the current source import closure are restored; ordinary
Lake checking with `--rehash` then validates their original traces against
the current sources, options, and artifacts. This cache is optional, and
missing artifacts are rebuilt from source.
