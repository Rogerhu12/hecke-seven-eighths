# Paired fourth-moment induction

## Implementation and acceptance requirements

This directory implements the finite-rank induction in revised §4.8 and
Theorem 4.2, with the actual source specialization used by PR #12. The
implementation registers **211 clean task modules and 1,595 explicit public
declarations**. These are source inventory counts. Acceptance also requires
the complete native build and recursive axiom audit of the exact reviewed
revision; PR #12 records the corresponding Actions run and results.

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

The integrated baseline is now
`c92578b1fa556b72d01c6ff49bac7f27885f09d7`. Its three intermediate targets
used the dyadic row exponent; this PR strengthens those conclusions to the
original physical exponent one, with the same objects and hypotheses.
`plainSource` consumes the resulting bounds directly, so it no longer
applies the dyadic conversion a second time. The seven sibling proofs
merged through that baseline are retained, including the six
`MOM_UNIFORM_AMPLIFY` obligations and the `MOM_PRIME` absolute endpoint.

The shared source integration replaces the original base's admitted
`momentModels` placeholder with the actual `recipeMomentModels` construction. Its dyadic
row width is `1 + log 2 / log U`, so the row cutoff is `2 * U`. Compared
with width one, this enlarges only the outer row set of the same model;
the prime/plain factors, common mask, sector, and other parameters remain
the same. Since the energy is a sum of nonnegative squared norms, this
enlargement strengthens the required estimate. It also covers the actual
physical witnesses, whose norms range up to `2 * U`.

`actualRecipeMoment_paired_rows` in `ExpansionModels/ActualRowEligibility.lean`
proves membership for those original witnesses, including the zero-slot
principal-character and positive-slot theta exclusions. The
`paired_source_reindex` theorem in `SourceReindex.lean` preserves the
original ideal/sector injection and every polynomial factor.
Statement-text equality with the base therefore needs to be read together
with this explicit construction and cutoff repair; it is not an assertion
of definitional equality with the former admitted placeholder.

The induction preserves the original three statements and consumes the
pinned STEP source with separately registered compatibility repairs.
Acceptance requires the complete clean audit, source integration build,
and original-target axiom gate on the same revision, together with the
whole-project integration build for that PR revision. Source wiring and
successful leaf or private-helper checks do not constitute that acceptance.

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

The workflow below validates the complete source construction with the
standard Lean kernel.

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
files and proof/elaboration compatibility repairs. The current principal pins are:

| Source | Immutable commit | Use |
| --- | --- | --- |
| MOM_ENGINE_STEP | `76904bc272e28e0de866bea0aa60b53a54d6c01e` | Original producer and its dependency closure |
| Source/profile | `c92578b1fa556b72d01c6ff49bac7f27885f09d7` | Shared source, profile, Fourier, and eligibility definitions |
| Source follow-up | `c92578b1fa556b72d01c6ff49bac7f27885f09d7` | Base and actual-row-eligibility interfaces |
| MOM_PRIME | `c92578b1fa556b72d01c6ff49bac7f27885f09d7` | Annular-volume dependencies and the actual endpoint |
| Finite-sector reindex | `c92578b1fa556b72d01c6ff49bac7f27885f09d7` | Finite-sum source modules |
| Inverse induction | `907494761e69835a65441353524781130019a556` | Merged PR #8 and its closed canonical inverse model proof |

The shared `Expansion`, `ExpansionModels`, `HighBinSupport`, `Base`,
`HighBin`, `SourceData`, `MOM_UNIFORM_AMPLIFY`, and `MOM_PRIME` sources
match this integrated baseline byte for byte. `Moments.lean` is recorded
separately: it retains the baseline's sibling proofs and adds the three
actual induction calls and the corresponding `plainSource` adjustment.
The subsequent `90749476` baseline merge retains both task imports and
the completed `canonical_inverse_models` call from PR #8. All 147 Lean
files of `MOM_INV_INDUCTION` match that baseline byte for byte and are
included in the recorded source hashes. The clean task inventory remains
211 modules and 1595 declarations; the complete source/configuration
inventory now contains 1601 hashes.

The `PRODUCER_REPAIRS` registry records the owner commit, original SHA256,
repair SHA256, and reason for each of the 47 local STEP repair files. It
includes the concrete native diagnostics at the owner pin, along with declaration
parameters already supplied by actual callers and corrected doc-comment
placement around `include` commands. The underlying original atoms,
profiles, arithmetic data, and producer output remain explicit.

`CanonicalLogProfileBounds.lean` is adopted byte for byte from the
owner-reviewed `ea5e384fc84dca2408cbda293e60492e7f0824c2` commit. Its proof
repairs transport the same restricted and frozen families along their
existing data, count, and time equalities. Public signatures, actual
support, profiles, selected slots, and all numerical bounds are preserved.

`ActualCoveredLabels.lean` likewise matches the published STEP repair
`a48360581b2b0ed368a375911d937cc4b44228f8`. It retains the original finite
tagged sum and closes the remaining definitionally equal tag-point
functions after polynomial normalization.

`ActualGaussFiniteLeaves.lean` reuses the proved
`fullCorrelationHybridCost_eq_leaf_sum` for its original phase identity.
Explicit row-set and coefficient equalities connect that theorem to the
same chart, instead of repeatedly expanding the complete leaf and four
nested sums. A private complex scalar identity handles the common phase;
the original allocation labels, kernels, weights, positions, exceptional
predicate, and positive phase on each coefficient remain unchanged.
Whole-module compilation and performance still require native evidence.

`ExceptionalOriginalLabel.lean` isolates the complete real product
inequality in a private scalar lemma, in addition to the scalar and
divisor equalities. Its public wrapper supplies the same two Moebius
norms, two phase-coefficient norms, radical denominators, and original
bounds. The dyad weight is transported by its exact defining equality;
the original field, branch, and ray arguments are explicit at the source
consumer. No nonnegativity premise or numerical factor is added.

The frozen singleton witnesses inside the norm-complete and moving
admissibility propositions use explicit `PUnit.{1}` indices. This resolves
the otherwise unconstrained field universe, as in the existing
`ParentArithmeticAtoms` consumer. The orbit and Fourier-space parameters
retain their arbitrary universes, and the profile identities and both
moving-row budgets are unchanged.

The two factory-fibre modules and their two global-mass consumers provide
uniquely named local `Fintype.ofFinite` instances for the original
`SixthUnitClasses` quotient. Its finite proof is already supplied by
`GlobalThetaData`; no public finiteness assumption, carrier, cardinality
formula, or mass constant is changed. The two factory files match the
published STEP repair `ed52f87c0805a0836bfc62496b65d158b09e0330` exactly.
All four files also match the subsequent owner candidate
`3f9458433d29131b29bb72202badbee49c715d82` byte for byte.

`CanonicalFullKappaPrime.lean` matches the published STEP repair
`c57d7991c746025313ab86dbc44412abc5cd0c00` byte for byte. It addresses
native diagnostics from STEP run `41299915844` against the same original
file. The uniform Mellin provider
is instantiated at the actual `Type 0` prime carrier in all five existing
choice/specification uses; `orders` and `analyticCoefficient` remain
parameter-free choices made before the field, characters, and profiles.
The two prime-divisibility binders spell out their original
`HeightOneSpectrum (𝓞 K)` type. The remaining changes explicitly transport
the same profile support, seminorm, endpoint and radius expressions,
coprimality, and ideal norm. No analytic input, full-kappa interval,
physical mask, or numerical estimate is changed.

The subsequent native whole-project run `41309867891` reduced the
diagnostics to one numeral-cast rewrite at the radius endpoint. The
published B12 repair adds `Nat.cast_ofNat` to the existing simplification
so that the natural exponent produced by `rpow_mul_natCast` is the same
real numeral used by the next rewrite. All 40 declaration headers remain
unchanged from B11; whole-module acceptance still requires native evidence.

In particular, the original `ScaleWindows` certificate, raw profile control,
centered parent domain, original length/normalization allowance window,
and complete-child/parent-character certificates
must appear in the helper signatures that use them. The repairs restore
those previously declared section inputs with
`include`; the actual callers already supply the same objects. These repairs
correct helper signatures as well as proof terms. They preserve the
original scale-window and comparison-rectangle hypotheses of the induction
(paper lines 2748–2810 and 2934–2944). The three final task statements and
their hypotheses remain unchanged.

The corresponding induction consumers restore their previously declared
child, computed-profile, positive-window, and narrow-window certificates
in the same way. Their existing callers already provide these objects;
the frozen data, calibration, and selected annuli are unchanged.

These files are recorded separately from byte-for-byte owner sources.
The registry establishes provenance; complete native acceptance is still
provided by the build and recursive axiom checks below.

## Verification and completion gate

The pinned environment is unmodified Lean **4.35.0-rc3**, compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`, with Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`.

The dedicated `mom-engine-induction.yml` workflow uses one checkout and one
job for all task acceptance stages:

1. Check the exact source revision, registered hashes, and full inventory.
2. Build `HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Audit`, run its complete
   declaration audit, and enforce the strict axiom allowlist.
3. Build `HeckeSkeleton.Moments`, then `SkeletonFamily` and `SkeletonSource`,
   and record their separate source-integration audit.
4. Run `verify.py original-check` for the three original theorem names.

The separate `integration-build.yml` workflow must also succeed for the
reviewed PR revision. It builds every `lean_lib` in `lakefile.toml` and
records the integrated endpoint axiom report. Evidence must identify its
tested SHA and its association with the reviewed PR head, including a PR
merge SHA when that workflow uses one.

The allowed axioms for the clean declarations and original targets are
exactly:

```text
propext
Classical.choice
Quot.sound
```

Lean's recursive axiom collection checks both declaration types and proof
bodies. The original-target gate rejects `sorryAx` and every other extra
axiom even if the generic core or source-adapter checks pass. The only
remaining admission in `Moments.lean` is `paired_primes_below_one`, owned
by the separate `MOM_PRIME_BELOW_ONE` task. It is not a permitted
dependency of the three accepted targets. Its presence in the broader
integration report does not establish the final global theorem.

Targeted performance probes must state their exact source, compiler,
heartbeat budget, and scope. A whole-module probe checks more than an
isolated private helper, and neither replaces the complete task and
integration gates. In particular, private conductor-helper probes must
not be reported as successful builds of `MovingRowConductor` or
`MovingRecipeConductor`.

The workflow restores Mathlib through `use-mathlib-cache: "true"` and the
repository's project artifacts through
`Rogerhu12/hecke-seven-eighths/.github/actions/restore-lake-cache@dtests-handoff`.
`use-github-cache` is `false`. Standard Lake validates source and dependency
hashes. Branch-based concurrency cancels obsolete runs when a new head is
published.

Compilation logs, inventory records, provenance, and axiom reports are saved
only in the two task evidence artifacts and the whole-project integration
artifact, including failed-run diagnostics.
They are not committed to the repository. PR #12 becomes ready for review
only when all acceptance stages pass for the reviewed revision. Its
description records the exact accepted head and links to the evidence.

AI-assisted implementation and review: ChatGPT, GPT-6 Astra Pro and collaborating agents.
