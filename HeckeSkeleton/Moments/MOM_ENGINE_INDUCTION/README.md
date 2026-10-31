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
`3820604a66b6c3a41d93dec1bf6156a69029be74` is
`HeckeSkeleton.Moments.EngineStep.paired_child_step`. It proves:

1. the actual child effective width is at most the parent width minus `σ / 2`;
2. one whole-slot removal leaves zero slots or the required capacity;
3. the actual child energy is bounded by the retained-slot energy times
   the specified product of prime-factor constants and the paid exponent.

`ChildStepCompatibility.lean` records this conclusion using the existing
`MomentData.restrictSlots` operation. It preserves the unchanged width and
converts the actual-energy inequality to its centrally normalized version.
The successor enters the finite state order proved here.

The published child theorem still leaves the complete positive parent reduction
open, but the companion modules now establish substantial parts of its actual
construction. `ParentSource` and `ParentTruncation` connect the same ordinary or
centered paired energy to the genuine first orbital transform and a common
finite cutoff. They preserve both zero terms and prove a quantitative tail.
Their `ParentSourceCalibration` still needs an actual instance: the complete
row polynomial, periodic phases, Haar Gram profiles, original common mask,
admissible row map, and its fiber and weight bounds.

`ActualFrequencyPartition` derives the residual frequency, its exterior ideal
and the exact norm factorization from a nonzero complete correlation.
`ActualChildren` descends that complete correlation together with its common
Schwartz kernel. `ChildTermDictionary` reconstructs the actual two plain
polynomials and full slot product from single-ideal and single-prime identities;
`ChildMomentDataAdapter` proves the finite row-fiber energy comparison.
`KernelMomentDescent` combines those comparisons with two actual child moment
estimates. Those estimates are intended to come from the induction, so they
are not inserted here as new assumptions on the final result.

The mass estimates also have proved components. `JointKernelBounds` bounds the
polynomially weighted Fourier L1 mass by finitely many original Schwartz
seminorms, for a fixed continuous linear transport. `FinitePhase` proves the
finite Fourier expansion and its coefficient mass once the actual fixed-ray
quotient is calibrated. `AllocationMass`, `FirstCommonMass`, `CommonHarmonicMass`
and `RankinLabels` supply subpower estimates for the indicated actual ideal
labels. Instantiating the label hypotheses and controlling the seminorms over
the entire recursively generated profile family remain part of the producer's
uniform assembly.

The actual model identification must respect the norm-profile form of
`IdealTest`. The untruncated `traceJointOrbitalKernel` already factors through
the two arithmetic log norms. `ChildTermDictionary` now derives the whole-column
identity from explicit termwise `hW₁`, `hW₂` and slot-profile equalities; it does
not construct the `MomentData` or prove those profile equalities. The generic
joint Fourier API permits arbitrary embedding-valued column maps, so the
separated and truncated columns still require this calibration. A frequency
label alone does not establish it. There is no demonstrated need to enlarge
the polynomial state used here.

The first tail is a genuine proved decay estimate. Its normalized moving mass
is the fiber constant times the sum of the original profile seminorms and
`truncationMass`, divided by the parent width power. The actual producer must
bound this quantity uniformly before choosing a common cutoff. Likewise, the
positive recursive weights must include both Poisson factors, the complete
quotient cardinality, common-kernel and divisor/phase masses, the parent/child
normalization ratio, and one slot-removal charge. A complex first-transform
sum is not itself the positive child measure required by `IntegralStep`.

`ExceptionalRows` at this pin still takes sixth-power classification as an
explicit input. `ExceptionalAmplitude` bounds whole masked rectangles from
calibrated volume, profile and error controls. The varying frozen cores and
all retained zero terms still need their terminal coefficient-mass accounting.
The full local reduction, admissible earlier children, terminal ledgers and
uniform mass bound are therefore still exposed through `ParentReductionInput`.
For a zero-slot child, the published slot-removal comparison can reduce to a
multiple of the same child energy; it cannot by itself initialize induction.

The conclusion of `paired_child_step` is unchanged from the earlier pin;
its nonnegative charge and zero-slot defect premises remain producer inputs.
The new modules are not imported or counted in this branch's clean audit.

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
the normalization restores `U^(m+q)`. At a source root this is its actual
`rowWidth`, and `β + N*δ ≤ loss` gives the corresponding row-width exponent.
The row width is allowed to depend on the original base, which is preserved
by the no-slot map. Physical capacity remains bounded by one, and the
prime-product power remains `1 + kappa * selectedLength`.

`RootNormalization.lean` proves the return to physical power one when
`U^rowWidth ≤ D*U`, by multiplying only the scalar constant by `D`. In the
actual dyadic row window `U < N(u) ≤ 2*U`, the exponent
`1 + log(2)/log(U)` satisfies `U^rowWidth = 2*U`, and is at most two for
`U ≥ 2`. This costs a factor of two without consuming a new power loss or
altering the height degree, ceiling, or threshold. This agrees with the
EXPANSION correction in PR #5 and the physical row window at paper lines
3756–3828; the final seven-eighths conclusion is unchanged.

All constants precede the moving index and sector. The height degree and
ceiling precede `τ`; the scalar and threshold may depend on fixed `τ`, exactly
as in the original `UniformMomentBound`. Summing sectors introduces the
fixed sector cardinality once.

`ScheduleCompatibility.lean` uses the skeleton's original `momentMeshValue`,
fixed before the geometry. It bounds the full rank count by eight times the
existing strict-width schedule depth. At width limit two, the existing
reserve pays for the terminal error and every boundary, mesh and local edge
loss. No smaller replacement mesh is selected after the source is fixed.

`IntegralRecursion.lean` proves the same estimate for finite positive measures.
The actual child energy is integrable and the child is earlier almost
everywhere. The proof uses pointwise strong induction followed by monotonicity
of the Bochner integral and the exact integral of a constant. No finite
representative or supremum is substituted for the genuine Fourier integral.
`Reduction.lean` exposes one interface with explicit finite-sum and integral
constructors; both feed the same three source projections.

`KernelReduction.lean` now constructs the required positive measure from
a genuine common Cauchy kernel. For child-column factors `aL, aR`, its density
is `sqrt(aL*U^widthL) * sqrt(aR*U^widthR) / U^widthParent`. Each child receives
one half of the pushforward of that same weighted kernel. The module proves
the exact mass identity, weighted integrability, almost-everywhere earlier
children, and AM–GM after each child's own width normalization. It produces
both `IntegralStep` and `RawParentReduction`; no final child moment bound is
an input. Actual source/column calibration, the integral bound on this
explicit density, and raw terminal components still come from the producer.

`LogNormProfiles.lean` realizes scalar log-norm Fourier columns with the
existing `freezeTwist` and `separatedProfiles` constructors. It proves the
termwise and complete plain/prime polynomial identities while preserving
the original mask, rows, characters, slots, lengths and mesh. The Fourier
frequency of each prime slot is fixed independently of the arithmetic row.
Identifying an orbital kernel's chart with these log-norm coordinates and
controlling the resulting profile family remain explicit source obligations.

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

`BaseTerminal.lean` constructs the actual width-floor terminal certificate.
Linear ideal counting, unitary Hecke coefficients and the original mask bound
each normalized plain polynomial by an explicit constant times `sqrt(N)`.
The proof includes all positive subunit scales: support is forced empty only
when `2*N < 1`, and the unit ideal is retained whenever it can occur. Both
rectangles keep their equal product. The existing absolute prime-product
bound then gives normalized exponent `n1+n2+z`. Its slot cost is `z`; it is
not relabelled `kappa*z`. Actual positive capacity implies this exponent is
at most the width. The zero-slot corollary uses the reflected padded core.
The profile/count constant is explicit, and the resulting base certificate
does not assume a terminal moment estimate. The log-norm Fourier twists
preserve the exact profile supremum and support used by this base proof;
higher derivative seminorms still incur their actual frequency costs.

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

`SourceData.lean` fixes a single explicit expansion and row exponent before
defining its block/amplitude/witness indices and actual inverse, paired and
unmarked models. Its data types contain no globally selected unfinished
expansion, default argument, energy estimate or analytic admissibility
field. `SourceAdapter.lean` maps this same datum and model to `SourceFamily`,
with definitional identities for rows, parameters, capacities, energies and
all uniform quantifiers. Neither module imports `Moments.lean`; they can
therefore be consumed by the source declarations without a circular import.
The shared-source aliases are being coordinated with EXPANSION before the
original source types are migrated.

`SourceConsumers.lean` proves the corresponding physical `PSource` consumer
for an explicitly identified `TargetData` and the same expansion. It joins
the positive- and zero-slot bounds, uses the literal finite witness sum and
its full-sector reindexing, and preserves the original no-slot model index.
The row-envelope transfer only needs its fixed large-scale threshold on
retained bins; the output threshold is the maximum of the two thresholds,
with only the fixed factor two in the scalar. Thus completing the original
three model estimates feeds the unchanged physical source conclusion.

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
parent-assembly input. The updated task rules allow correcting these source
types and require continuing past relative statements. Work is proceeding on
an explicit common expansion/model core and an acyclic source adapter, with
ownership coordinated in PR #5; the current source wrappers are a verified
intermediate boundary, not completion of the original obligations.

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
`propext`, `Classical.choice`, `Quot.sound`. Both jobs restore the repository's
precompiled project artifacts with
`Rogerhu12/hecke-seven-eighths/.github/actions/restore-lake-cache@dtests-handoff`
after the pinned Lean setup and Mathlib cache. There is no task-specific
cache/bootstrap or checkpoint restoration. Standard Lake still checks the
sources and dependencies before reuse. Compilation and axiom evidence are
stored in Actions artifacts. The source specialization has an explicitly
different inherited-axiom boundary and is checked by a separate integration
job. That job also prints the axioms of the original three targets and their
upstream data definitions. An inherited `sorryAx` is recorded there as a
remaining obstruction; it is never admitted by the clean proof audit.

AI-assisted implementation and review: ChatGPT, GPT-6 Astra Pro and collaborating agents.
