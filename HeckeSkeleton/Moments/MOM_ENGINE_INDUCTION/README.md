# Paired fourth-moment induction

This directory contains the finite-rank induction from revised §4.8, its terminal
arithmetic and exceptional-row counting, and exact adapters for the original
finite `MomentData` polynomials. The three public projections are:

* `EngineInduction.paired_zero_slot_models`;
* `EngineInduction.paired_positive_below_one`;
* `EngineInduction.paired_positive_endpoint`.

Their explicit remaining input is `ParentReductionInput`. It includes the
parent's normalized positive decomposition and uniform coefficient estimates.
The decomposition may use finite sums or finite positive measures on actual
child nodes, so continuous Fourier parameters are retained.
The published child-step theorem supplies one part of this input. The source
specialization in `SkeletonFamily.lean` records the exact original conclusions
with this additional hypothesis visible.

## Relation to the authoritative child step

The parallel task's interface at commit
`04cc5c645c7f79bb19439b6f8fddbc7fd820882e` is
`HeckeSkeleton.Moments.EngineStep.paired_child_step`. It proves:

1. the actual child effective width is at most the parent width minus `σ / 2`;
2. one whole-slot removal leaves zero slots or the required capacity;
3. the actual child energy is bounded by the retained-slot energy times
   the specified product of prime-factor constants and the paid exponent.

`ChildStepCompatibility.lean` records this conclusion using the existing
`MomentData.restrictSlots` operation. It preserves the unchanged width and
converts the actual-energy inequality to its centrally normalized version.
The successor enters the finite state order proved here.

The published child theorem explicitly leaves parent analytic assembly open.
The newer `OrbitalTransform`, `ChildAssembly` and `JointKernel` modules also
provide genuine orbital Poisson and common-cutoff truncation, exact finite
Moebius/phase separation, and paired Cauchy with a common Fourier measure.
The remaining step is to connect these expressions to the actual parent
moment and bound their coefficient masses and tails uniformly over the
recursive profile family. Integrability alone does not provide the uniform
weight mass required here. The stronger parent reduction therefore remains
an additional obligation. For a zero-slot child, the published energy
comparison can reduce to a multiple of the same child energy; it cannot by
itself bound the parent or initialize induction.

`ExceptionalRows` at that pin still takes the sixth-power classification as
an explicit input. `ExceptionalAmplitude` supplies estimates for whole
masked rectangles from volume, profile and error controls; those controls
and the outer sum over frozen cores must still be charged to the common
terminal coefficient mass. The additional `hcharge` and zero-slot premise
in the updated child theorem do not change its conclusion, so the exact
`ChildStepConclusion` consumed here is unchanged.

## The finite order and quantitative conclusion

The order is lexicographic:

1. zero-slot states precede every positive-slot state;
2. within a slot regime, width bands have length `σ / 4`;
3. the first proof stage precedes the second proof stage in each band.

The actual post-clipping drop `σ / 2` crosses a band. A comparison call uses
the earlier proof stage, while removing the last slot may return to any
already completed zero-slot band. With widths bounded by `W`, the explicit
natural rank is less than

```text
N = 4 * (floor(4 * W / σ) + 1).
```

The third coordinate is an explicit proof stage, supplied by
`PolynomialSystem.proofStage`. It is independent of `Node.centered`, which
changes the actual coefficient. In particular, an ordinary target with
`A > 5*M/6` may occupy the later proof stage. The algebraic comparison
rectangle preserves the original scale product; reflecting its longer factor
and identifying the result with an admissible shorter ordinary model remain
analytic producer obligations. A same-band comparison edge therefore needs
explicit earlier-stage evidence. Strict-width children may use either proof
stage.

The local reduction has nonnegative weights or a finite positive child measure.
Its terminal remainder
has bound `C (1+T)^H U^β`, and its total normalized weight mass has bound
`C (1+T)^H U^δ`. Finite induction proves the uniform normalized estimate

```text
C * (1+C)^N * U^(β + N*δ) * (1+T)^(H*(N+1)).
```

The coarse terminal loss `β` is charged once. Only the local edge loss is
multiplied by the finite depth. The number of finite child labels may vary
with the scale, and integral children may have continuous frequency labels;
their total weight mass is the controlled quantity. Undoing
the normalization restores `U^(m+q)`. At an original source root this width
is exactly one, and `β + N*δ ≤ loss` gives the requested exponent.

All constants precede the moving index and sector. The height degree and
ceiling precede `τ`; the scalar and threshold may depend on fixed `τ`, exactly
as in the original `UniformMomentBound`. Summing sectors introduces the
fixed sector cardinality once.

`IntegralRecursion.lean` proves the same estimate for finite positive measures.
The actual child energy is integrable and the child is earlier almost
everywhere. The proof uses pointwise strong induction followed by monotonicity
of the Bochner integral and the exact integral of a constant. No finite
representative or supremum is substituted for the genuine Fourier integral.
`Reduction.lean` exposes one interface with explicit finite-sum and integral
constructors; both feed the same three source projections. Constructing the
measure and proving its uniform mass bound remain producer obligations,
including any frequency growth from the recursive profile bounds.

## Terminal and exceptional-row proofs

`Terminal.lean` proves the strict width calculation, slot-removal budget,
comparison margins, divisor saving, and exceptional optimization

```text
A - 5*M/6 - 2*v/3 - max(M/4-v, 0) ≤ A-M.
```

It also proves the paper's strict-call count and ordered coarse/fine choices.
The complete parameter-selection theorem chooses the coarse width drop first,
evaluates the resulting finite depth, and only then chooses the fine errors.
Its total budget includes both the unmultiplied terminal boundary error and
every accumulated edge loss.
`TerminalCertificate.lean` applies these calculations to the original finite
terminal components. Its raw cases are the width floor, uncentered exceptional,
centered positive, centered zero-slot, diagonal, and tail contributions. The
final terminal bound is derived from the component masses and local ledgers.

`ExceptionalCounting.lean` uses actual nonzero ideals and a finite sector
coordinate. An exact classification `u = h₀ * a^6`, injective in
`(sector, row ideal)`, gives an injective encoding by `(sector, a)`. For

```text
N(u) ≤ C^6 * U^m,       U^(2*f) ≤ N(h₀),
```

the field's linear ideal-count estimate yields a constant times

```text
card(Sector) * C * U^((m-2*f)/6).
```

For `f ≥ 0` this implies the displayed paper exponent `(m-f)/6`. Root cutoffs
below one force the row family to be empty. This is a fixed-core counting
result; outer sums over varying frozen cores remain in the coefficient-mass
input. The actual row cutoff `m` is kept separate from effective width `m+q`.

## Actual source data and integration boundary

`SourceFamily.energy` is a sum of the repository's actual `pairedEnergy` over
every original finite sector. `Node.energy` retains the whole centered pair,
the same two profiles, character, common mask, and complete live slot product.
The comparison scales have equal product before absolute values are taken.

`Centering.lean` proves the actual energy decomposition
`pairedEnergy ≤ 2 * centeredEnergy + 2 * comparisonEnergy` on this unchanged
row set. It also proves that the ordinary comparison has the same slot regime
and width band, and is earlier when the explicit stage-0/stage-1 evidence
is supplied. The raw `comparisonOrdinary` has not yet undergone reflection.
This supplies the algebraic centering part of the parent assembly; identifying
a reflected shorter model and bounding both terms still require the analytic
parent producer.

`SkeletonFamily.lean` identifies the base, selected length, parameters,
capacity, energy and uniform-bound quantifiers definitionally with
`HeckeSkeleton.Moments`. It provides the three `_of_parent_reduction` wrappers.

At the task base `182769d49e5c184547c0949ddc328b9e7a87e6f7`, the original
theorem types already refer to admitted constructions:

```text
SourceMomentIndex → targetData → highExpansion / rows_in_norm_envelope
momentModels
```

Lean's recursive axiom collector visits declaration types as well as proof
bodies. Thus even a completed proof body at those original signatures
inherits `sorryAx` until the upstream constructions are completed. Their
signatures also lack the permitted single-step argument and the additional
parent-assembly input. This directory leaves those existing declarations
unchanged and records corrected, explicit sufficient statements.

The original averaged `PairedPrimeProductBound` concerns the original row
family. The published child step requires pointwise prime-factor bounds on
its recursively generated rows. The parent producer must supply those
masked estimates and source calibration. `RootCertificate.base_one_le`
also records the source condition needed to increase power exponents.

The original `WholeMomentProfileControl` controls the listed one-variable
inverse and plain profiles. Prime-window bounds and the mixed-parameter,
locality, and recursive profile estimates needed for the uniform Fourier
mass remain separate obligations. The corrected statements expose the
resulting uniform local estimates in their parent certificates; they do not
assert that the original profile hypothesis constructs those certificates.

## Verification

The pinned environment is Lean `4.35.0-rc3`, compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`, with Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`.

```bash
lake build HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Audit
lake env lean HeckeSkeleton/Moments/MOM_ENGINE_INDUCTION/Audit.lean
```

The dedicated Actions workflow checks the exact PR head, inventories all
explicit public declarations in the clean modules, and enforces the allowlist
`propext`, `Classical.choice`, `Quot.sound`. Compilation and axiom evidence are
stored in Actions artifacts. The source specialization has an explicitly
different inherited-axiom boundary and is checked by a separate integration
job. That job also prints the axioms of the original three targets and their
upstream data definitions. An inherited `sorryAx` is recorded there as a
remaining obstruction; it is never admitted by the clean proof audit.

AI-assisted implementation and review: ChatGPT, GPT-6 Astra Pro and collaborating agents.
