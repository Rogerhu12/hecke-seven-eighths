# Paired fourth-moment induction from an explicit single step

## Review scope

This directory implements the finite-rank induction in revised §4.8 and
Theorem 4.2. The coordinator's 2026-11-01 15:00 UTC instruction separates
its acceptance from PR #9's construction of the paired engine step.
`StepHypothesis.lean` records the single-step input explicitly;
`ConditionalTargets.lean` proves the three actual-source projections from
that input. The dedicated workflow compiles **all 184 core modules** and
audits all 1,456 explicit public declarations on one exact revision.

The actual producer and unconditional source integration
(`HeckeSkeleton/Moments/MOM_ENGINE_INTEGRATION/`) are not part of this PR:
they need STEP producer modules that are not yet merged into the base, and
they land after those modules. The independent induction gate checks that
its transitive import graph stays outside that directory and outside the
STEP producer implementation. Its STEP dependencies are
an explicit set of 228 data, profile, and transport modules; the actual
`PairedEngineStep`, Gauss leaf, and exceptional-label producer are outside
this graph. The separate whole-project workflow retains its original
scope.

The conditions for review of this phase are a complete core build and a
recursive axiom audit of every public core declaration, including all
three actual conditional targets. The later integration phase checks the
three original unconditional names and the complete project. PR #12
records the exact tested commit, Actions run, and results for each phase.

## The explicit single-step interface

`Source.PairedStepHypothesis Ωengine c` supplies the strict paired-engine
output for the original target's prepared recursive family. Its quantifier
order is:

1. The actual source preparation fixes the positive annulus, decay exponent,
   and reflection schedule.
2. The step provider selects its backward engine orders and minimum child
   profile coefficient.
3. Source preparation selects common `Cp` and `Hp` satisfying that minimum.
4. The step family selects its coefficient, height degree, and threshold.
5. Moving scale, height, source index, node, and frequency are supplied.

The output type follows the existing exact chain:

```text
RecipeMellinStrictFamily.outputs
  : MellinStrictBranchAt
      → LabeledEngineOutput
      → Node.EngineOutput
      → EngineStep.PairedEngineConclusion
```

`Node.EngineOutput` is an abbreviation of the STEP owner's structure in
`MOM_ENGINE_STEP/ReductionOutput.lean`. That structure and its parent-energy
definitions are unchanged between the previous induction head `e4950f2d`
and STEP head `ac6b6800`. It records the literal parent and children, their
parameters, the shared positive kernel, strict width descent, capacities,
all four terminal contributions, and their local mass bounds. The
hypothesis supplies these single-step outputs and their profile/child
admissibility data. Final source moment bounds and recursive child moment
bounds are proved by the induction.

The required child admissibility belongs to the **same produced children**:
complete moving arithmetic recipe, full joint mask budget, original mesh,
theta catalogue and kappa, positive annular profiles, and prime support in
`Ioo 1 2`. The raw STEP predicate has a larger `[0, hi]` window, so its
narrow-support transport is an explicit part of the later integration.
`OriginalMeshPairedSupport.narrowAnnulusSupport` and
`actualRecipeEngineOutput` retain that proof obligation. Review of the
conditional result does not assert that this instance has been compiled.

`Source.actualRecipeScalarInputs_of_step` combines the hypothesis with
`actualRecipeCompleteMellinFamily_preparation`, which already constructs
the source roots, base cases, and reflection families. Thus the hypothesis
is consumed before the finite scalar induction runs.

## The three actual-source targets

All names in the table have prefix
`HeckeSkeleton.Moments.EngineInduction.Source`.

| Conditional target | Original conclusion and premises |
| --- | --- |
| `paired_zero_slot_models_of_step` | Unrestricted `i.noSlots` bound, with no plain-length capacity condition |
| `paired_positive_below_one_of_step` | `B < 1`, original positive capacity and selected-set nonemptiness, prime-product premise at `kappa = 2*B-1` |
| `paired_positive_endpoint_of_step` | `B = 1`, the same positive conditions, absolute prime-product premise at `kappa = 1` |

Each target retains the original calibration, row eligibility, whole-profile,
and quadratic-sieve premises and adds `PairedStepHypothesis` explicitly.
The models use the same `expansionRecipeRaw`, full sector family, original
mask, and selected slots. The conclusion has physical exponent **one**.
The `For` types are the definitions underlying the compatibility names in
`Moments.lean`; `PairedInductionQuadraticSieveBound` has exactly the original
quadratic-sieve definition body.

The actual row window is `U ^ rowWidth = 2*U`. The scalar recipe induction
first proves its dyadic bound; `uniformMomentBound_recipe_physical` changes
the constant by the fixed factor two while retaining the threshold order,
height degree, model and index quantifiers. This covers the physical
witnesses in the original double shell (paper lines 1653–1678 and 4231).
The final `GeneralHeckeSevenEighths` statement remains unchanged.

## Source and arithmetic invariants

The base is `cbc44997e3baaede3bdfb8423d7c1c6bf4887424` on
`dtests-handoff`. Shared source, profile, prime, and inverse-induction
changes from that baseline are retained. `HeckeSkeleton/Moments.lean` is unchanged
from the base in this PR; its three paired targets keep their original
statements until the unconditional integration lands.

The recursive dictionary uses the STEP owner's `CompleteMovingRowRecipe`.
Its displayed moving factors remain in the moving-support budget; its
common zero mask retains the full remaining ideal. `CompleteSourceBudgets`
keeps both `SupportBudget` and `FullJointBudget`. `OriginalRowLocalization`
restricts to the exact allowed rows and proves the complete parent energy
unchanged. Mellin preprocessing and reflection retain the same data.

This phase also restores six already isolated induction fixes from
`971d2b1c0561274d400c8ca93d8998fd6d3b3b97`: Boolean simplification in
`MovingRecipeArithmetic` and `RankedAnnulusPrimitive`, and explicit record
fields in the four recipe reflection-family modules. Five consumed STEP
proof/API repairs are copied from that candidate or published owner head
`ac6b6800`; their local source hashes are included in the exact dependency
evidence. Heartbeat settings are not increased.

Native elaboration repairs make singleton universes, data imports and
canonical local instances explicit, and use typed transports for frozen
slot indices, localized profile records and character-dependent analytic
certificates. Scale inequalities retain their original constants. These
repairs preserve the mathematical statements and source data; each exact
revision is rebuilt by the independent native gate.

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
strict-width schedule depth. The later integration adapter `RecipeStrictEngineBox.lean` checks the
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

## Separate producer integration

The following 31 modules form the later
`HeckeSkeleton/Moments/MOM_ENGINE_INTEGRATION/` phase. Each one transitively
imports STEP producer modules that are not yet in the base, so they are not
part of this PR; they remain in this branch's history (commit
`d49002a147cb65a7a45b2db1d5df698808929dd1`) and land after those STEP
modules are merged:

```text
ActualCatalogueVolume           ActualCompleteLocalInputs
ActualEngineArithmetic          ActualLocalInputMeasures
ActualLocalInputs               ActualStrictConstants
ActualStrictEngine              ActualStrictFamily
ActualStrictOrders              ActualStrictSource
EngineAnnulusSupport            LiteralCalibrationSupport
LiteralDirectFamilyAnnulus      LiteralPassiveFamilyAnnulus
LiteralPassiveSideAnnulus       LiteralPooledFamilyAnnulus
LiteralSideAnnulus              OriginalFamilySupport
OriginalMeshDirectAnnulus       OriginalMeshDirectEngine
OriginalMeshEngineMass          OriginalMeshPairedAnnulus
OriginalMeshPairedEngineStep    OriginalMeshPooledAnnulus
OriginalMeshPooledEngine        OriginalMeshUniformAnnulus
OriginalMeshUniformEngine       RecipeStrictEngineBox
SideAnnulusSupport              SkeletonFamily
SkeletonSource
```

They retain the actual arithmetic producer and the construction intended
to instantiate the explicit step interface, including the narrow-support
transport on its actual children and the original `Moments.lean` route. Their workflow will retain
the original unconditional target check with the standard three-axiom
allowlist. The independent phase and its evidence have distinct names and
scopes.

## Native validation

The pinned environment is unmodified Lean **4.35.0-rc3**, compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`, with Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`.

The independent workflow uses one exact checkout to:

1. Enumerate every core module and public declaration and verify the complete
   transitive import boundary.
2. Record the revision, dependency pins, toolchain, and source hashes.
3. Run ordinary `lake build HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Audit`.
4. Print and validate the recursive axioms of every public core declaration,
   including the three `of_step` targets.
5. Recheck that source hashes and declaration inventories stayed unchanged.

The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Types and proof bodies are both covered by Lean's recursive axiom collector.
The source scan rejects admissions, custom axioms, and `native_decide` in
the core; the import boundary excludes the integration producer.

Mathlib is restored using `use-mathlib-cache: "true"`; project artifacts
use the repository's official `restore-lake-cache@dtests-handoff` action.
`use-github-cache` remains `false`, and newer heads cancel obsolete runs
on the same branch. All build logs, source inventories, and axiom reports
are saved in Actions artifacts. They are not repository sources.

AI-assisted implementation and review: ChatGPT, GPT-6 Astra Pro and collaborating agents.
