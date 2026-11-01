# Paired fourth-moment induction

## Current implementation and verification status

This directory implements the finite-rank induction in revised §4.8 and
Theorem 4.2, with the actual source specialization used by PR #12. The
implementation at `da3e9806` registers **211 clean task modules and 1,595
explicit public declarations**. These are source inventory counts; the
complete native build and recursive axiom audit for this revision are still
pending CI acceptance.

The three original declarations in `HeckeSkeleton/Moments.lean` now call the
actual source pipeline:

- `HeckeSkeleton.paired_zero_slot_models`;
- `HeckeSkeleton.paired_positive_below_one`;
- `HeckeSkeleton.paired_positive_endpoint`.

Their statements are byte-for-byte identical to the statements at base
`6eb687277d73bc16b4a3e537ba6cdd1fa0fca073`. In particular, each conclusion uses
physical exponent **one**, and the two positive-slot declarations retain
the original `PairedPrimeProductBound` premise. The proof first obtains the
actual dyadic row-width estimate, then applies
`uniformMomentBound_repaired_power` inside each original declaration. The
identity `U ^ rowWidth = 2 * U` costs only a fixed factor of two. The
statements acquire no volume, strict-family, child-energy, or completed
moment-bound assumption. The final `GeneralHeckeSevenEighths` statement is
unchanged.

The previous CI70 run failed before completing the clean audit. The current
batch repairs its induction-side diagnostics, restores the original three
statements, and consumes the newer STEP source with separately registered
compatibility repairs. Acceptance requires the complete clean audit, source
integration build, and original-target axiom gate on the same revision.
Source wiring and successful leaf checks do not constitute that acceptance.

## The actual source pipeline

`Source.actualRecipeScalarInputs c` in `ActualCompleteLocalInputs.lean`
constructs both the unrestricted no-slot and positive-capacity inputs from
one actual target. The implementation follows this chain:

1. **Original source and profiles.** `ActualCompleteSourceFamily.lean`
   consumes the shared `expansionRecipeRaw`, its actual geometry and row
   eligibility, and `UniformAmplify.actual_source_profile_control`.
   `RecipeRoot.lean` retains the selected physical witness, complete finite
   sector set, original slot geometry, and the original mesh. The same
   target's canonical finite theta family is fixed before moving indices.
2. **Supported character volume.** `ActualAnnularVolume.lean` and
   `ActualCatalogueVolume.lean` use the principal/nonnorm continuation
   results for the original finite character catalogue. They supply the
   STEP owner's supported `VolumePrimitive` with continuous finite Schwartz
   remainder seminorms. The hypothesis `tsupport phi ⊆ Icc lo hi` remains
   explicit throughout this analytic conversion.
3. **Finite order selection.** `ActualStrictOrders.lean` first takes the
   finite union of volume orders over all numerical ranks. Child Euler
   requirements, prime orders, and the two original logarithmic profile
   transformations then determine the backward profile schedule.
   `FiniteSchwartzProfileBridge.lean` and
   `RankedSchwartzProfileBridge.lean` connect those Schwartz requirements to
   the original Euler integral controls.
4. **Literal Mellin source.** `MellinSourcePreparation.lean`,
   `ActualStrictSource.lean`, and `LocalizedCompleteSource.lean` construct
   the normalized per-frequency model, its original norm profiles, complete
   moving recipe, and exact allowed-row localization. The complete parent
   energy and the full row/mask budget are retained.
5. **Original strict producer.** `ActualStrictEngine.lean` calls
   `originalMeshPairedEngineStep` with the actual arithmetic choices,
   analytic provider, supported volume, and original source profiles. The
   numerical cutoff uses the owner's loss while the original `momentMesh`
   is passed independently. The actual mass exponent `b.ε + mesh` is paid
   by the existing induction edge budget.
6. **Same actual children.** The annulus modules follow the producer's
   chosen children through active clipping, original slot restriction,
   radius normalization, and time freezing. `ActualEngineProfiles.lean`
   and `ActualEngineLabels.lean` transport those children into the scheduled
   primitive family. The narrow `Icc (lo / hi) hi` window and prime
   `Ioo 1 2` support are preserved separately from the larger internal
   exceptional-volume box.
7. **Scalar induction and original names.** `ActualStrictFamily.lean`,
   `ActualLocalInputs.lean`, and `ActualLocalInputMeasures.lean` assemble
   the strict and reflection families with the target's actual Haar and
   Borel instances. `RecipeMellinInduction.lean` obtains the three recipe
   projections, and `Moments.lean` converts their dyadic exponent to the
   original physical exponent one.

These are the current source constructions. Their complete kernel
validation is the pending CI work described above.

## Complete moving recipes and the two arithmetic budgets

The recursive source uses the STEP owner's `CompleteMovingRowRecipe`.
Its character retains the actual displayed moving factors together with
its fixed finite correction and original residual ideal. Its common zero
mask retains the full fixed remaining ideal. The moving factors are
charged to the moving-support exponent rather than placed in the fixed
finite theta family.

`CompleteSourceBudgets.lean` and the actual source adapters retain both:

- `SupportBudget`, controlling the displayed support before cancellation;
- `FullJointBudget`, controlling the original row norm together with the
  complete mask support at exponent `m + q`.

`OriginalRowLocalization.lean` restricts to the exact allowed parent rows
and keeps their complete energy. The same complete recipe and both budgets
pass through Mellin preprocessing and reflection. Child admission is
constructed for the producer's actual chosen child, including its original
character, mask, slot injection, and frozen profiles.

`SourceData.lean` supplies transparent compatibility names for the shared
`HeckeSkeleton.SourceData` interface. `SourceAdapter.lean` and
`SourceReindex.lean` retain the same scale-indexed expansion, full-sector
sum, model parameters, and uniform quantifiers. `SkeletonFamily.lean` and
`SkeletonSource.lean` remain separate integration adapters, compiled after
the clean task audit. Their conditional low-level wrappers are useful
interfaces; the three original targets use the actual pipeline above.

## Finite rank, reflection, and the original mesh

The induction order has three coordinates:

1. zero-slot states precede positive-slot states;
2. width bands have length `sigma / 4`;
3. the two core stages precede the outer ordinary-reflection stage.

For widths bounded by `W`, the natural rank is less than

```text
N = 6 * (floor(4 * W / sigma) + 1).
```

A strict child drops width by at least `sigma / 2`, so it crosses a band.
`StrictChildRank.lean` also uses zero-slot preservation when comparing the
slot-regime contribution. The proof stage records the actual geometric
case independently of the centered flag.

`MellinCoreRecursion.lean` supplies the local case split. Small widths use
actual terminal components. An ordinary zero-slot node outside the padded
core uses its genuine outer reflection. A core ordinary node with a short
plain factor uses short reflection. With both factors long, the actual
quarter-centered coefficient and equal-product comparison rectangle are
substituted locally. The comparison is reflected before it becomes a
recursive child. Centering contributes the common factor four.

Each local reduction has a terminal bound `C * (1+T)^H * U^beta` and
normalized child-weight mass at most `C * (1+T)^H * U^delta`. The finite
scalar induction gives

```text
C * (1+C)^N * U^(beta + N*delta) * (1+T)^(H*(N+1)).
```

For the assembled centered cases, use `4*C` in place of `C`. The terminal
loss is charged once; the edge loss is multiplied by the finite rank
bound. Restoring normalization contributes the child's or parent's actual
`U^(m+q)` factor as appropriate. At the physical root, `W = 2` and the exact
row-width identity returns the required exponent one with the fixed
factor two.

`ScheduleCompatibility.lean` uses the original `momentMeshValue`, chosen
before the geometry, and bounds the full rank by twelve times the original
strict-width schedule depth. `RecipeStrictEngineBox.lean` checks the
existing reserve against the genuine terminal exponent and the separate
mesh charge. `ClippedAnnulusSchedule.lean` keeps the positive support range
compatible with each earlier rank.

## Common kernels, terminal terms, and uniform constants

The complete row energy retains both plain profiles, the actual character,
full common mask, and whole live slot product. Equal-product cancellation
occurs before absolute values. `RowIntegralKernel.lean` applies weighted
Cauchy using one common positive kernel and then interchanges the finite
row sum with its integral. `KernelReduction.lean` normalizes each actual
child by its own width; the two half weights pay their common kernel mass
once.

`MellinScalarStep.lean` and `MellinCoreRecursion.lean` apply scalar strong
induction at each literal Mellin frequency and then integrate the scalar
estimate. `BranchedIntegralRecursion.lean` handles the actual continuous
child kernels. Only the numerical energies need their stated integrability;
the argument retains the original frequency spaces and child maps.

The base and terminal modules retain the genuine width-floor, first and
second zero-frequency, exceptional, diagonal, and tail contributions.
`GeneralBaseTerminal.lean` uses the actual fixed support endpoint and linear
ideal counting, including positive subunit scales. `ProfileSupremum.lean`
derives pointwise control from the original order-one Euler integral. The
actual slot cost is its total length. `ExceptionalCounting.lean` records
the fixed-core sixth-power count with row cutoff `m` separate from effective
width `m + q`; the producer's coefficient masses account for the outer
frozen-core sums.

The choices occur in the following order:

1. fixed source, finite character catalogue, rank bound, and annulus;
2. finite volume orders and backward profile orders;
3. minimum child-profile coefficient, then the common source `Cp` and `Hp`;
4. finite-rank Mellin masses, engine coefficient, and physical threshold;
5. moving scale, height, source index, node, sector, and frequency.

At the public `UniformMomentBound` interface, the height degree and ceiling
precede `tau`; its scalar and threshold precede all moving indices and
sectors. Summing sectors costs their fixed finite cardinality once.

## Source provenance and explicit STEP repairs

`verify.py` records exact imported-source hashes separately from integrated
files and proof-only compatibility repairs. The current principal pins are:

| Source | Immutable commit | Use |
| --- | --- | --- |
| MOM_ENGINE_STEP | `5c432b677f9c58fabe2771194a32adb2d7b4a2a4` | Original producer and its dependency closure |
| Source/profile | `896cec08ff832c5fcf136adcc12f0239e7ab9728` | Shared source, profile, Fourier, and eligibility definitions |
| Source follow-up | `f606882b1da6e40f4ec752d568fe361caed28120` | Base and actual-row-eligibility repairs |
| MOM_PRIME | `1cf8548809ee3753a5a8af0f5793a3e37a22fa1e` | Seven annular-volume dependency files |
| Finite-sector reindex | `778b4220d3d4bc8538549bf74998a78e570d01d9` | Two finite-sum source modules |

The `PRODUCER_REPAIRS` registry records the owner commit, original SHA256,
repair SHA256, and reason for each local STEP repair. It includes the
concrete native diagnostics at the owner pin, along with declaration
parameters already supplied by actual callers and corrected doc-comment
placement around `include` commands. The underlying original atoms,
profiles, arithmetic data, and producer output remain explicit.

These files are recorded separately from byte-for-byte owner sources.
The registry establishes provenance; complete native acceptance is still
provided by the build and recursive axiom checks below.

## Verification and completion gate

The pinned environment is unmodified Lean **4.35.0-rc3**, compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`, with Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`.

The dedicated `mom-engine-induction.yml` workflow uses one checkout and one
job for all acceptance stages:

1. Check the exact source revision, registered hashes, and full inventory.
2. Build `HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Audit`, run its complete
   declaration audit, and enforce the strict axiom allowlist.
3. Build `HeckeSkeleton.Moments`, then `SkeletonFamily` and `SkeletonSource`,
   and record their separate source-integration audit.
4. Run `verify.py original-check` for the three original theorem names.

The allowed axioms for the clean declarations and original targets are
exactly:

```text
propext
Classical.choice
Quot.sound
```

Lean's recursive axiom collection checks both declaration types and proof
bodies. The original-target gate rejects `sorryAx` and every other extra
axiom even if the generic core or source-adapter checks pass. The other
nine admissions in `Moments.lean` belong to other tasks and remain outside
this task's three obligations; they are not permitted dependencies of the
three accepted targets.

The workflow restores Mathlib through `use-mathlib-cache: "true"` and the
repository's project artifacts through
`Rogerhu12/hecke-seven-eighths/.github/actions/restore-lake-cache@dtests-handoff`.
`use-github-cache` is `false`. Standard Lake validates source and dependency
hashes. Branch-based concurrency cancels obsolete runs when a new head is
published.

Compilation logs, inventory records, provenance, and axiom reports are saved
only in the two Actions evidence artifacts, including failed-run diagnostics.
They are not committed to the repository. PR #12 becomes ready for review
when all acceptance stages pass for the reviewed revision; that full result
is still pending for the implementation documented here.

AI-assisted implementation and review: ChatGPT, GPT-6 Astra Pro and collaborating agents.
