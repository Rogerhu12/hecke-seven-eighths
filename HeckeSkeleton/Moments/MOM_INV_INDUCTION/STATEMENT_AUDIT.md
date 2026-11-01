# Canonical inverse induction: statement and dependency audit

## Implemented integration and acceptance

The original `HeckeSkeleton.canonical_inverse_models` proof body calls
`SourceModelClosure.actual_canonical_inverse_models`. Its original type,
actual `momentModels`, and all original arguments are preserved. The helper
constructs both fields from the original quadratic/cubic sieve inputs;
it adds no terminal energy, source energy, or endpoint bound premise.
The final general-number-field 7/8 zero-free statement is unchanged.

The actual provider is PR #13's complete `CanonicalStep.exists_uniform_step`
at `ddf7569086bbe703352609b01f23db0ce720eee0`, whose full native workflow
`41253770207` succeeded. The old `fixed_triple_energy_step` boundary below
is historical. `ProviderUniformMarks` runs finite backwards induction on
the literal canonical node class. The node's energy is the actual
`normalizedChildEnergy`; its real generated children retain all original
masks, coefficients, labels, sectors and puncture.

The general reflected source has fixed-X atoms with the actual N(P)^2
kernel, minimum-valuation charges, full cubes, original masks, the paper's
E_ref, and the genuine off-threshold tail. `SourceActualArithmetic` builds
the fixed finite period inventory and each character's Mellin data.
`TerminalProviderShortBound` discharges the actual short contribution from
the two primitive sieves; long cubes use the genuine single-step descent.
The physical moving-X normalization is never identified with fixed X.

The actual marked path is `SourceMarkedActual` → `SourceMarkedRawBound` →
`SourceMarkedClosure` → `SourceMarkedUniform`. All original slots share one
fixed coefficient cap before any overlap split. Literal tuple counting and
column normalization give exact cancellation of their base powers; the
original sector sum and external threshold are then restored.

The unmarked path is `SourceScaleSup` → `SourceScaleSupRows` →
`SourceScaleSupClosure` → `SourceUnmarkedComplete` → `SourceCanonicalClosure`.
It supplies one nonnegative row majorant simultaneously over every strict
smaller column scale, for complete ideal rows and the same inherited
profile. It consumes the exact `CompleteUnmarkedScaleSupBound` interface
required by PR #10, including its order of quantifiers.

This section describes the source implementation. Acceptance requires
successful normal Lake compilation and all four strict audits: `Audit`,
`CompletedEnergyTransportAudit`, `ProviderAudit`, and `OriginalAudit`.
Every audited declaration may depend only on `propext`, `Classical.choice`,
and `Quot.sound`; inherited unfinished objects do not exempt the original
target. The 129-module, 973-public-declaration provider inventory is a
source count. Neither that count, isolated kernel checks, auxiliary gate
successes, nor a non-draft flag establishes completion or readiness for review.

The current-head evidence is maintained in
[PR #8](https://github.com/Rogerhu12/hecke-seven-eighths/pull/8) and the
[MOM_INV_INDUCTION Actions runs](https://github.com/Rogerhu12/hecke-seven-eighths/actions/workflows/mom-inv-induction.yml).
Each accepted run must identify the source commit/tree actually checked
and match the current PR head. `README.md` records the pinned environment,
dependency pins, and full verification contract. Its `00841cc` failure and
`1aa3b526` in-progress records are explicitly historical observations,
not claims about a later head.

The source identities correspond to manuscript lines 1564–1607 and
2550–2614; the reflected input retains lines 2120–2155, especially 2144–2148.
No new final moment inequality is used to repair the historical issues below.

## Historical audit of the 914f13f relative layer

The following sections refer to the earlier skeleton and provider
revision. They are retained to explain why the old relative result alone
did not close the requested obligation. Claims of missing operations below
must be read with the implementation summary above and the verification
contract and current-head evidence links in `README.md`.

## 1. The original target's type already depends on admissions

The original declaration is `HeckeSkeleton.canonical_inverse_models` in
`HeckeSkeleton/Moments.lean`. Its conclusion is
`CanonicalInverseModelBounds (momentModels K c)`. Merely replacing its proof
body cannot make its axiom list consist of the three standard axioms.

| Dependency | Definition in the base revision | Consequence |
| --- | --- | --- |
| `momentModels K c` | `HeckeSkeleton/Moments.lean`, definition `momentModels`, has an admitted body | The fixed model in the conclusion carries an admitted dependency. |
| `SourceMomentModels` | Its `inverse`, `paired`, and parameter fields quantify over `SourceMomentIndex` | Generalizing just `momentModels` to an arbitrary `SourceMomentModels` does not remove the following dependency. |
| `SourceMomentIndex` | Its block, label, and subdivision types use `(targetData K c).expansion` | The index type itself depends on the admitted expansion. |
| `targetData K c` | `HeckeSkeleton/Base.lean`, definition `targetData`, uses `highExpansion` and `rows_in_norm_envelope` | Both named dependencies have admitted bodies in the base revision. |
| The original `hreflection` argument | Its type uses `finiteMellinData K c` from `HeckeSkeleton/Theta.lean` | `finiteMellinData` has an admitted body independently of the expansion. |

Lean's axiom traversal visits declaration types as well as proof terms.
Passing an admitted construction as a theorem parameter, or adding a
hypothesis whose type still mentions that construction, does not erase the
dependency. Importing a file which contains unrelated admissions is a
different matter: those admissions are absent from the audit only when the
theorem's transitive type and value dependencies do not reference them.

The axiom-clean formulation must parameterize the actual source expansion,
the index family, and the moment data before inserting the named incomplete
construction. Its energies should still be the literal finite ideal sums
from `HeckeGeneral/Analysis/MomentInputs.lean`. Specialization back to
`momentModels` is a separate boundary and retains the base revision's
admitted construction until the expansion task is complete. Neither
changing a display name nor hiding the dependency in an abbreviation
changes this fact.

## 2. The old profile hypothesis is insufficient for the stated conclusion

`WholeMomentProfileControl` in `HeckeSkeleton/Moments.lean` quantifies over
the three tests of the inverse and paired models. Its own comment says
explicitly that it does not assert mixed parameter derivatives or locality.
The following are absent:

1. Uniform control of `M.unmarked U D s ξ σ τ` for independent `U,D`.
   `StrictUnmarkedMomentBound` quantifies over all such independent scales,
   sectors, and rowwise parameter maps, but the profile hypothesis never
   examines this family.
2. Bounds for the prime-window profiles in `d.geometry.slots`. These enter
   `primePolynomial` and therefore the marked energy, although they are
   absent from the list of tests in `WholeMomentProfileControl`.
3. Mixed derivatives and a common separated-profile bound of sufficiently
   high finite order. The paper's real-parameter argument uses these, not
   just one-variable slices; see the discussion before Theorem 4.1 and
   Proposition `prop:can-uniformity`.
4. Bounds on the actual vectors `M.heights`, `M.realShifts`, and
   `M.imagShifts` used by `inverseModel`. The available profile estimate is
   conditional on `‖ξ‖ ≤ T`, on a real-shift bound of 8, and on an
   imaginary-shift bound of `1 + ‖ξ‖`. Neither
   `SourcePolynomialCalibration` nor `SourceRowEligibility` supplies those
   three conditions for the chosen vectors.

The polynomial calibration does identify the unmarked polynomial at the
particular source witness scales and parameters. It does not identify or
bound the whole independent-scale unmarked family. Row eligibility and
the two large-sieve bounds also do not supply that missing uniformity.

There is also a scale-range distinction. `StrictUnmarkedMomentBound`
starts at every `U,D ≥ 1`, with no lower asymptotic threshold. Passing from
an eventual canonical estimate to this statement requires a uniform
bounded-scale estimate for the remaining compact range. If logarithmic
lengths are defined by `log D / log U`, the case `U = 1` must be separated
first; its width constraint forces `D = 1`.

A corrected source-level statement needs a common admissible profile
family covering the marked and unmarked models, prime windows, and mixed
parameter derivatives, together with bounds on the actual chosen
parameters. The order of quantifiers matters: constants, finite derivative
orders, and the permitted height exponent precede the varying scales,
indices, and rowwise parameter maps. An unrelated bound for each profile
does not establish the uniform conclusion.

## 3. The named completed-energy statement is narrower than Lemma 4.8

The permitted input's type is `HeckeSkeleton.CompletedMarkedEnergy K c`,
defined in `HeckeSkeleton/Principal.lean`. Its theorem
`HeckeSkeleton.completedMarkedEnergy` is itself admitted on the base
revision, so it must be passed as a hypothesis rather than invoked as a
proved fact in this task.

`CompletedMarkedEnergy` concerns the fixed physical row sum
`completedMarkedRow`: the profile is `logGaussianProfile`, the window
geometry is `c.geometry`, the coefficients are the specified target
coefficients, the initial puncture is empty, and the row budget is
`B * Z^(5/6) / q^2`. It gives an upper bound
`C * Z^(5/6 + ε) / q^2`, uniformly in the selected tuple and subset.

Paper Lemma `lem:can-marked-energy` has substantially more variables. The
completed polynomial `eq:can-completed-marked` includes a squarefree label,
a fixed puncture, a permitted background, arbitrary bounded product-form
marks, and an annular profile. Its conclusion controls each retained
powerful/residual/dual block with exponent `E_ref` in `eq:can-Eref`,
includes the conductor comparisons in `eq:can-conductor-comparison`, and
gives arbitrary saving for the frequency tails. These are precisely the
features used for the three terminal exponents in
`eq:can-terminal-ledger`.

The physical statement cannot simply be renamed the generic lemma. A
source-level proof needs a proved transport from each terminal block to
the permitted completed-energy input, retaining its coefficients, masks,
labels, norms, and uniform profile constants. If that transport requires
the general form of Lemma 4.8, the stronger hypothesis must be stated and
the difference from `CompletedMarkedEnergy` recorded. An implication from
the fixed physical energy directly to all terminal estimates would itself
be an additional analytic input; it is not the finite induction.

The paper's terminal classification also includes a short cube-completion
block, whose extracted cube length is less than `d₀` up to the localization
error. Small label length `V < d₀` alone does not describe every condition
on that block: the remaining blocks can have `V < d₀` and a large cube
length, with `V + ℓ ≥ d₀`, and must use the two-transform step. A provider
must retain that short-block decomposition or record the complete terminal
condition explicitly.

There is an axiom-clean general-data version of the physical definition:
`HeckeSkeleton.LowCauchy.MarkedEnergy` in
`HeckeSkeleton/LowCauchy/General.lean`. It is definitionally the same
physical expression with explicit `S`, `ProbeData`, character, geometry,
and ray filter. This avoids named expansion choices but does not enlarge
the analytic conclusion.

`CompletedEnergyTransport.lean` gives a concrete consumer of this exact
input. `CompletedLabelRealization` requires an exact row-polynomial identity
between a canonical row polynomial and a bounded scalar times the actual
physical `markedRow`, an injective map to the original sixth-unit orbit
space, and the prescribed row-norm cutoff. The theorem
`completedEnergy_label_transport` then bounds the literal `labelEnergy`
using `MarkedEnergy`. `completedEnergy_normalized_transport` combines
those identities with purely numerical scale bounds and cancels the label
normalization. Neither theorem assumes a canonical row-energy bound.
The finite-to-infinite sum comparison uses the existing proved
`lc_sum_le_tsum_orbit_box`, whose support is finite; no divergent-series
convention enters. What remains is to construct the stated polynomial
identities and support maps for the actual general terminal blocks. In
particular, the adapter does not construct a term-by-term correspondence
between the finite squarefree column and the infinite completed theta
sum, nor a uniform transform replacing its Gaussian by an arbitrary
annular profile.

## 4. Precise division between the step and its closure

The relative induction should consume an actual family of node energies
and the following data, with a common constant budget for the entire
family.

- **Nodes and admissibility.** Each node carries the canonical lengths
  `F,M,Q`, the surviving marks with the original cap `z₀`, the squarefree
  label measure, puncture, background, and exact polynomial. Nonnegative
  row length and the two inequalities in `eq:can-invariants` are retained.
- **One reduction step.** A nonterminal node is bounded by the primitive
  principal terms, controlled tails, and a positive aggregate of genuine
  child energies. The children preserve the canonical data and satisfy
  `eq:can-child-margins`. The extracted weights and their total mass occur
  once in the inequality. The normalization identity is
  `κᵢ + λc + Cc + 2Fc = F` (`eq:can-energy-identity`).
- **Terminal reduction.** The terminal node's exact energy is related to
  the permitted marked completed sums. The three exponent alternatives
  are `F-c`, `F-2c+5d₀`, and
  `F-M/4-3c/4+5d₀/2`, with their explicitly allocated errors.
- **Initial reduction.** To deduce Theorem 4.1, the original inverse
  polynomial must be transported to initial canonical nodes. This is the
  overlap allocation and first masked Poisson step following Proposition
  4.10. It has margins `eq:can-initial-margins` and normalization
  `κ_init + P₁ + 2F_init = m`. A theorem about already-canonical nodes does
  not by itself establish this initial polynomial identity.
- **Uniform analytic control.** The constants and profile orders needed
  for the finite reductions and terminals are bounded uniformly as in
  Proposition `prop:can-uniformity`. The independent-scale empty-slot
  specialization additionally needs the full unmarked family described
  in Section 2 above.

The closure's mathematical work is to choose `d₀`, a finite depth `D`, and
positive localization/loss parameters; propagate the margins; establish a
strict row-length descent; prove finite termination; and run backward
energy induction with the correct normalization and common constants.
This is not equivalent to assuming `MIInput`,
`CanonicalInverseModelBounds`, or a row bound at the target exponent.

### Published single-step interface and the remaining parent reconstruction

The provider has published
`HeckeSkeleton.Moments.MOMInvStep.fixed_triple_energy_step` in
`HeckeSkeleton/Moments/MOM_INV_STEP/Interface.lean` on
`cloud/mom-inv-step` (reviewed interface blob
`92e1f0ded5bbf2df6ed6714dd94b57368327d38a`). It bounds the actual
`physicalStepScalar * ‖ReconstructionPacket.signedValue F G‖` of a fixed
reconstructed block. Its two induction premises now bound
`normalizedChildEnergy Z Nchild Vchild slotCap P.labels P.rows F γ`
and the corresponding expression for `G`, for every frozen triple.
Their target is `Cchild * Z^(Fchild + eps)`, where
`Fchild = Nchild + Vchild` and the column length is clipped at zero.
The provider restores the unnormalized bounds with power
`2 * Fchild + eps` internally, using `childEnergy_bound_of_normalized`.
The conclusion has power
`Fparent + 40 * eta + tau + pi + eps` and uses the distinct-triple mass once.
The provider explicitly leaves construction of the packet from every
original parent, including its common kernel and coefficient reindexing,
as a separate obligation.

`CanonicalDatum.rawEnergy` and `rawEnergy_eq_totalLength_mul_energy` supply
the exact numerical normalization bridge:

`rawEnergy Z = Z^F * energy Z`.

Consequently `rawEnergy_le_of_energy_le` turns a canonical child bound
`energy Z ≤ B * Z^(F + eps)` into `rawEnergy Z ≤ B * Z^(2F + eps)` without
another label-mass estimate. This agrees with the normalization conversion
now performed inside the provider theorem; the provider no longer asks
its caller for raw-energy induction hypotheses. Identifying our literal
canonical energy with its normalized packet energy still requires the
following identities and uniform bounds:

- The packet's squarefree ideal labels correspond to the datum's nonzero
  ideal labels, and the datum's weights equal the packet's explicit
  divisor weights `#idealDivisors(f)^(9 + 4 * slotCap)`.
- The packet's rows are ideals paired with sectors. They must be
  reindexed as the relevant canonical rows and a finite sector sum;
  zero rows must be excluded or their columns shown to vanish.
- Its functions `F` and `G` must equal the corresponding literal
  `columnSum`, with their masks and original product-form marks retained.
- Its clipped column-plus-label length must equal each datum's
  `totalLength`.
- The same child constant must cover every triple, sector, and both
  columns; the finite sector mass must be included in that constant once.

The fixed reconstructed blocks must then be assembled into the original
parent's energy, with all outer scalar and localization losses accounted
for. The physical ray factor and the count's small-power parameter must
have common bounds for the whole tree.

`PairedMeasure.lean` supplies the finite-measure linearization between the
provider's two Cauchy roots and a linear child sum. It bounds their product
by one half of the sum of the two positive energies, indexes the children
by the original triple times `Bool`, and assigns weights `wγ / (2D)`.
When the original triple mass is at most `D > 0`, the paired mass is at
most one. `paired_constant_rescale` proves the exact identity
`D * sum_paired(weight * H) = H * sum_triples(wγ)`, so passing to two
children does not charge the frozen-triple mass twice. This calculation
does not supply any of the source identifications listed above.

The consumer's `StepEnergy` is a whole-parent linear reduction. It is not
the statement of `fixed_triple_energy_step`, and the provider's theorem
does not by itself instantiate it. Until the listed identities and
outer aggregation are proved, `StepEnergy` remains an additional
explicit source-reduction obligation in the relative closure. The
normalization theorem agrees with the provider's current exponent
convention and supports an exact polynomial identification. It does not
resolve the parent reconstruction gap.

Existing useful arithmetic is already proved in
`HeckePort/Moments/Descent/Basic.lean`:

- `canonical_transition`, `child_margins_sharp`, `child_margins`;
- `child_row_decrease`, `childF_upper`, `clipping_bounds`;
- `step_energy_exponent`, `total_step_loss`, `depth_margin`;
- `initial_margins_sharp`, `initial_margins`,
  `initial_prefactor_identity`, and `initial_energy_exponent`.

For the terminal arithmetic,
`HeckePort/Moments/Inversion/TerminalWidths.lean` proves
`reflected_terminal_cases`, `reflected_terminal_saving`, and
`actual_terminal_saving`. These use concrete conductor-width and norm
hypotheses. They prove the exponent calculation, while the analytic
identification and energy estimate of each terminal block remain distinct.

## 5. What an axiom audit establishes

A clean audit of the relative induction verifies that the stated
single-step, terminal, and source-reduction hypotheses imply its
conclusion. It does not instantiate those hypotheses for the repository's
named source. The resulting PR must report each audited declaration,
its exact hypotheses, and any remaining source specialization separately.

The original type contamination, incomplete profile family, and terminal
statement mismatch are independent issues. None can be resolved by using
an admitted theorem indirectly, choosing a degenerate model, altering the
polynomials, treating an empty index family as the actual source, or
assuming the endpoint in a record field.
