# EXPANSION: actual-definition integration and verification

Work in progress on `codex/expansion-detector-20261030`, targeting
`dtests-handoff`. This report is updated with the native verification results
before final delivery. **The complete expansion obligation is not yet closed.**

## Current construction

The new modules use the repository's actual Hecke characters, ordinary
continuation, conductor scale, nonzero ideals, original complete-row prime
mask, source polynomials, and moment models. In particular the deleted set
contains the fixed exceptional set, primes above six, and every prime dividing
the complete row. It is not replaced by the conductor support.

The terminal source is the actual truncated convolution. Its finite dyadic
decomposition and one common Fourier frequency produce inverse and ordinary
normalized polynomials. Uniform Fourier moments precede all varying scale
parameters. With terminal height `H = U^21`, the product coefficient mass has
power `U^84`; the squared dyadic count costs at most `U^2`. Choosing `N` with
`τ*N ≥ 87` and radius `U^τ/(8π+8)` gives a tail of order at most `U^(-1)`.
One explicit eventual threshold makes that tail at most `1/8`.

`Expansion.Project.exists_original_masked_product` connects an actual Hecke
zero to this product with the original mask. Its hypotheses are: a totally
complex number field, fixed infinity type, a character which is not a norm
twist, conductor at most `R*U`, row norm at most `2U`, `2 ≤ D ≤ U^(3/2)`, a
smooth cutoff with its stated plateau/support/norm properties, and a zero
with real part in `[51/100,1]` and height at most `U^θ`, where
`heightDegree K * θ ≤ 1`. The common constant and threshold precede the
character, row, length and zero. It does not assume a detector lower bound,
Fourier-tail bound, calibration, or desired polynomial spike.

The actual finite Mellin estimates are separately normalized into uniform
square upper bounds for the same deleted coefficients. Their remaining
hypotheses are explicit buffered zero control, fixed infinity type,
conductor/ideal norm bounds and height geometry. No polynomial upper bound is
introduced as a premise of those estimates.

## Shared recipe and the remaining obligations

`HeckeSkeleton.ExpansionModels` supplies one data-only recipe for source
witnesses and moment polynomials. The six coordinates retain a common physical
point, half the cutoff exponent, a finite presentation code and physical
height. The block's shell is decoded from the actual dyadic schedule. The
original inverse and plain finite sums are equal to the recipe projections.

The named construction `expansionRecipeRaw` is still the original open
`D-EXPANSION` obligation, now at the shared data entry point. Proving facts
about its projections does not discharge that admission. The actual global
finite label family, witness subdivisions, shifted physical integrals,
`actualHighPresentation`, and joint analytic `expansionBudget` /
`expansionCutoffsRaw` still require construction. The existing expansion
identity, principal/small/large estimates, final `BlockSource` and moving
tail statements remain open. No empty recipe or assumed spike is used to
claim them.

The cutoff envelope makes the common scale at least `2^16` and includes the
explicit shell-count constant. It does not prove the remaining analytic
choice. The small-row constants are corrected to `1/16` and `1/50`; the
large-row saving `63/800` is intentionally retained. Wide zero-control bins
overlap and are not treated as a disjoint partition. Row selection is fixed
before contour integration, and the final dyadic shell is clipped to the
global retained endpoint.

## Verification policy

Pinned environment: Lean `4.35.0-rc3` at
`470d5ce1400764999581fd26d5d72b00d990b0f4`, Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`; project options
`autoImplicit=false`, `relaxedAutoImplicit=false`.

`scripts/expansion_verify.py` records SHA-256 hashes of the exact source
files, compiles their original module paths, and inspects recursive axioms
for every declaration in the selected modules. Pure and actual-definition
groups permit only `propext`, `Classical.choice`, and `Quot.sound`. The
separate skeleton group reports all inherited admissions explicitly; success
of that compilation is not an admission-free correctness claim.

At this initial checkpoint, new terminal and saturation endpoints are still
under native compilation. The workflow preserves complete logs, including
failed builds. No whole-project success is claimed until the corresponding
job has completed. Final per-module results and the exact remaining axiom
dependencies will be recorded here.
