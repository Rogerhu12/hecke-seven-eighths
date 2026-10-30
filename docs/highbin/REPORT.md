# HIGHBIN implementation and verification report

Working branch: `codex/highbin-euler-norm-boundary-20261030`.
Original base: `503ad9895e5f8affef55b22fea082e251bf33aa7`.
Merged current base: `5e4c85f172c101fd0c201219c13aa28f8b520d42` (`dtests-handoff`).
PR: https://github.com/Rogerhu12/hecke-seven-eighths/pull/1.
Toolchain: Lean `4.35.0-rc3`; Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.

## Current task status

This is a draft implementation. The four original obligations have not yet
been discharged in `HighBin.lean`. Their existing admissions are retained,
and the new support files contain no `sorry`, `axiom`, or `native_decide`.
Verification claims below are tied to their exact source commits and
downloaded CI artifacts.

| Original obligation | Implemented connection | Remaining work |
|---|---|---|
| HB-EULER-INITIAL | Actual prime-power quotient Fourier formula, finite Poisson/CRT, absolutely convergent four-ideal prime product, local-to-global calibration and complete original `TRowEulerInput` constructor candidates | Native verification of the arithmetic chain and named presentation identification |
| HB-EULER-EXCEPTIONAL | Arithmetic `RowEulerData`, actual finite Laurent tables, uniform `9 q^(-10e)` estimate and a consumer of the original `HighExceptionalEulerControl` type | Native verification and the named `actualHighPresentation.euler` identification |
| HB-NORMFORM | Actual repeated-prime conductor deficit, Mellin prime detector, exact full-correction factors, normalized slots, compact-box amplitude labels, actual contour-integral norm-form candidates and a consumer of the original `HighShiftedNormForm` type | Native verification, inherited prime-normalizer dependency and identification with the named labelled presentation |
| HB-MOVE-BOUNDARY | Actual row-contour rectangle, arbitrary-order external tails with the entire height cost absorbed, original whole-bin consumer and main-term/boundary identity | Native verification, actual Euler provider, companion membership, lower-height/buffer conditions and retained-block count |

## Repository changes

`rowEulerRegion` includes the necessary conditions
`1 < Re(w) + 6 Re(z)` and `1 < Re(s) + 6 Re(z)`.
The current base independently acquired the same correction in commit
`51dce0e4`; the branch preserves it rather than reverting the upstream fix.
The finite Laurent data definitions have moved verbatim from
`PhysicalProbeRows` to `FiniteEulerRational`; the former imports and reexports
the same definitions. Their names and types are unchanged.

The five Euler-derivative/annular-test declarations similarly move verbatim
from `GlobalThetaData` to `AnnularTest`, and `PrimeWindowGeometry` plus
`primeScale` move verbatim from `PhysicalProbeData` to their own module.
The original modules import the new modules, preserving their public API.
`ThetaKernel.TestMellin` can therefore check the same actual test objects
without importing unrelated arithmetic constructions.
`rowEulerRegion` also moves verbatim into its own module, reexported by
`TInputRanges`; this permits its analytic estimates to be checked without
the arithmetic dependency chain.
All 12 moved declarations were compared against the pinned current base;
their declaration text is unchanged after ignoring comments and whitespace.
The result is recorded in [definition_moves.json](definition_moves.json).

`HighBin.lean` now imports the actual regular-prime adapter and proves the
regular branch's error estimate and joint analyticity on an open tube around
the complete s-move. The original high-bin target statements are unchanged.

The support entry point is `HeckeSkeleton.HighBinSupport`. The arithmetic
Euler provider is `HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData`.
Finite tables are built in the repository's `FiniteEulerRational` type;
their Gauss coefficients retain ramified zeros and whole-index markings.

## Verification protocol

Run:

```sh
python scripts/highbin_inventory.py
python scripts/highbin_verify.py core
python scripts/highbin_verify.py mellin
python scripts/highbin_verify.py actual
```

The inventory command records source hashes and public declarations.
The `core` verification command builds the listed core files as separate Lean modules,
then asks Lean for every enumerated named source declaration's exact type and transitive axiom
set. Its allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The `mellin` command separately checks five actual prime-power/Mellin modules
and requires the same standard axiom set. The `actual` command checks the
complete arithmetic adapters and `HighBin.lean`, then records every additional
transitive axiom explicitly in `actual-axioms.json`.
The existing upstream admissions remain relevant to any transitive audit of
the complete project; no claim of a globally admission-free project is made.

A local combined verification unit also records source hashes and closes
file-local sections at each boundary. Its imports are hoisted, so a passing
combined check is recorded separately from individual-module verification.
An uncompiled source file is not counted as a verified theorem.

## Presentation properties still needed

`ActualHighPresentation` currently supplies no proof that `1` belongs to its
companions, a positive uniform lower bound `delta*T ≤ contourHeight`, that
`contourHeight + 3/2 ≤ upperHeight`, or that the retained block count obeys a fixed polynomial bound. The strengthened
boundary consumer needs no polynomial upper bound on either height: shortening
the analytic detector to `H+3/2` and choosing decay order `N+6*r_infty` absorbs
the complete height cost. The label-count hypothesis is a
per-block bound and does not establish a bound on the number of blocks. The
exact matching repository theorem is `HeckeSkeleton.expansion_blockCount`
(EX-BLOCK-COUNT), whose body remains admitted; its `expansionBudget` and
`expansionCutoffs` providers are also admitted. The source wrapper therefore
does not close this construction gap.

The current definition of `shiftedPiece` and its sum identities also do not
identify each labelled piece with its full-correction integral. Cancellation
between arbitrary pieces prevents deducing the desired norm-form estimate
from these identities alone. A concrete construction of the named
presentation is required; this observation is not a counterexample to a
correctly constructed presentation.

## Recorded native verification

The recorded core audit is commit
`45b507f4995fe107e2e98041f91971c8c78d5860`: **57 separately compiled modules
and 442 public declarations passed**. The downloaded `core-axioms.json`
contains an empty `beyond_standard_axioms` map. Every declaration uses only
`propext`, `Classical.choice`, and `Quot.sound` (or a subset). This includes
the complete three-variable `JointAnalyticLimit`, `EulerRegionAnalytic`,
`LocalBlockSummation`, `PrimeBlockEuler`, `LocalSeriesFactorization`,
`EulerRegionUniqueness`, `EulerRegionProduct`, `BoundaryHeightAbsorption` and
the full parameter budget in `HighNormFormScalar`.

Run: https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41135382154
Job: `124336425848`; artifact: `13015787518`.
The full declaration-to-axiom mapping is preserved in
[verified_core_axioms.json](verified_core_axioms.json). This is evidence for
that exact commit; it does not establish subsequent edits or the full
arithmetic chain.

The actual Mellin audit passed **5 separate modules and 59 public
declarations** at `c71511a569ed8b98c243b66ead8d8ec8c83d59b9`. These cover
higher prime powers, divided-log Mellin inversion, uniform profiles, the
actual logarithmic prime detector and `ActualOrbitalRapidDecay`. The complete
axiom mapping has an empty `beyond_standard_axioms` map and is preserved in
[verified_mellin_axioms.json](verified_mellin_axioms.json). The prior four-module,
55-declaration audits also passed at `6e3d24ca` and `a2ea9121`.

Run: https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41127250262
Job: `124308854297`; artifact: `13012239754`.

That successful proof job could not save its previous whole-`.lake` cache:
archive compression ran out of runner disk space. The current workflow
therefore caches only the root, class-field-theory and TauCeti `build`
directories, after dependency setup, and releases already-extracted Mathlib
`.ltar` downloads. Mathlib's own cache supplies its binaries. This repairs
the identified cache-storage failure without treating a cached build or a
successful cache step as proof verification. The first v3 core job successfully
released 452191602 bytes of downloaded archives and saved its project-build
cache after its 57-module proof and axiom audit passed.

The older complete arithmetic build at `29d6f4d` reached its 65-minute job
timeout while compiling the class-field-theory dependencies. Its preserved
log reported two orbital-Mellin elaboration errors. Both are repaired in
the current snapshot. The arithmetic adapters and their all-public axiom
audit remain unverified. The later `a2ea9121` arithmetic job also reported
only those same two orbital errors and stopped; the fixed orbital module has
since passed its separate native audit above. Its whole-`.lake` cache save
also ran out of disk space. The current workflow preserves running arithmetic/Mellin checks while
new revisions queue, checks the small core prerequisites first, and
preserves the smaller completed project-build caches after a proof failure
or the build subprocess timeout.


The arithmetic run at `61699e94` checks the source before four final tactic
sequencing adjustments in `ActualEulerCRT`, `ActualPrimePowerSymbols`, and
`ActualNormFormFullCorrection`: an independent `rfl` after `simp only` is
replaced by `simp only ... <;> rfl`. These preserve every declaration
statement and handle either a residual definitional-equality goal or a goal
already closed by simplification. The actual audit for this revised source
is queued separately; no successful complete arithmetic build is claimed.

Local checks provide additional, separately identified evidence:

| Check | Result | Scope |
|---|---|---|
| Complete `JointAnalyticLimit` | Passed, 321.551 seconds; both public types and standard-axiom reports | Original single-module Mathlib imports; now also covered by native CI |
| `EulerRegionAnalytic` and original region definition | Passed, 16.139 seconds; 12 public declarations | A combined dependency wrapper; now also covered by native CI |
| `EulerRegionUniqueness` | Passed, 22.756 seconds; three public declarations | Exact current source in a combined dependency wrapper; now also covered by native CI |
| `EulerRegionProduct` | Passed, 18.706 seconds; two public declarations and standard axioms only | Exact current body in a combined dependency wrapper; now also covered by native separate-module CI |
| `BoundaryHeightAbsorption` | Passed, 34.736 seconds; both public axiom reports use only the standard three axioms | Exact native separate module with its original Mathlib imports; now also covered by core CI |
| Combined actual Mellin unit | Passed, 499.327 seconds; 40 source bodies and 577 public declarations, standard axioms only | Imports hoisted; not 40 separate native modules |

The combined Mellin source SHA-256 is
`a69fdee42c5804b56bab177384824ae6791ce6cd783e07140db92bb9e3cb0c79`;
its complete log SHA-256 is
`78c74b9e256f12d76aa9096f9b999d36baf7aa9e4436987d529e342a17e53ddb`.
Source hashes were unchanged during the recorded local checks.

The generated `*_public_declarations.json` inventories contain source paths,
line locations and SHA-256 hashes. The verification script checks those
hashes, asks Lean for `#check @name` and `#print axioms name`, and requires an
axiom report for every enumerated public source declaration. Exact types,
including implicit section parameters and typeclasses, are preserved in
the CI artifact `*-public-types-and-axioms.log`.

## Main arithmetic interfaces and their remaining inputs

* `arithmeticHighEulerData` takes the actual `ProbeData` and target Hecke
  character. Its row character is the canonical arithmetic row character;
  exceptional values are literal `FiniteEulerRational` tables.
* `exceptional_unmarked_dynamic_bound` has constant 9 and cutoff 2. Its
  scalar assumptions are `1/2 ≤ a`, `0 ≤ e` and the actual contour equations
  `Re(s)=a+16e`, `Re(w)=1-a-6e`, `Re(z)=17/50`. The exceptional prime is
  outside the mark set; no Gauss nonvanishing hypothesis is used.
* `highExceptionalEulerControl_of_arithmetic` consumes an actual presentation
  and the data equality `P.euler = arithmeticHighEulerData ...`. This
  equality remains to be established for the named admitted constructor.
* `arithmeticRowEulerCalibrationInput` now builds the original
  `RowEulerCalibrationInput` from `AllowedGeneratorInput`, the original
  mixed `ThetaCalibrationInput`, and exterior unramifiedness of the target.
  Initial absolute summability and the series/continuation identity are
  conclusions. The named target specialization uses `places`/`probeData`
  directly to avoid unrelated admitted expansion fields in its type.
  This complete source-level connection still awaits native verification.
* Actual local finite-Poisson/CRT lemmas retain the denominator generators,
  arbitrary sixth-unit sectors and whole-index masks. Their structural
  arithmetic input is the repository's `AllowedGeneratorInput`; the target
  provider is `Theta.allowedGenerators`. Identifying eta with the target
  prime coefficient uses the existing mixed `ThetaCalibrationInput`, not an
  extra assumed Euler identity.
* `exists_actual_primeWindow_radical_cap` retains the actual zero-free
  detector, a lower norm shell, the internal height `max(T,Z^kappa)`, and
  the upper-height gap. Its output is proportional to
  `(radical Nu)^eps (2+U)^(2 r_infty eps) P^(a-1/2+8e)`.
  It bounds the unnormalized prime polynomial. It does not assert the
  missing lower bound for the prime normalizer.
* `exists_actualFullCorrection_product_cutoff` identifies the original
  complete compensation sum with the actual unmarked row product times
  the product of explicitly defined slot factors. It retains all subsets
  and only divides by a regular local factor after proving its nonvanishing
  on sufficiently large prime windows. It assumes no global nonvanishing
  of the Euler product or a Gauss polynomial.
* `exists_target_highShiftedNormForm_connection` specializes the actual
  row theorem to the target's own Haar measures, calibration and character.
  `targetData.rayFilter` is definitionally empty, so the actual target is
  covered by the existing complete-slot formula. The theorem constructs
  the per-row amplitude witnesses internally and concludes the original
  `HighShiftedNormForm`, with external height exponent `A = 0`. Remaining
  inputs identify the Euler data, include `1` among companions, choose
  `H = max(T,Z^kappa)` and upper height at least `2H+2`, and identify the
  original means and each literal shifted piece. No row or integral bound
  is assumed. The per-piece identity is stronger than the existing sum
  identities and is still a missing part of the named construction.
* The arithmetic fixed-row boundary bound has the form
  `C_N Z^13 (2+U)^(6 r_infty) T_ext^(-N)`. The finite family is an actual
  frequency-row envelope; row counting and Euler bounds are conclusions,
  not supplied tail estimates.
* `highBoundaryControl_of_arithmetic_lower_geometry` now consumes only the
  original presentation, its arithmetic Euler-provider equality, `1` in the
  companion set, `H >= delta*T`, `H+3/2 <= upperHeight`, and a retained-block
  count bounded by `Cb*Z^RB*(1+T)^AB`. It first requests tail order `N+k`
  with `k=6*r_infty` and tail parameter `H`; the verified scalar absorption
  removes the complete height factor. The original `HighBoundaryControl`
  follows with fixed degrees `A=AB`, `R=13+RB`, selected before `tau` and `N`.
  No upper growth bound on either height is required. The buffered schedule
  specialization therefore no longer requires a bounded detector index.
* `presentationInitialSum_eq_blocks_add_boundary` follows directly from the
  original presentation's two identification fields. It proves that the
  complete initial fixed-bin sum equals the sum of actual block values plus
  this same `wholeBinBoundary`. It does not supply the missing identification
  of the expansion's other tail components or individual labelled pieces.

## Unresolved dependencies that must not be hidden

`Base.highExpansion` is still an admitted construction. Its target record
allows arbitrary blocks, labels and slot values; it does not itself construct
the retained fixed-bin integral or identify each label with its complete
compensation amplitude. The new slot formula does not establish those
identifications automatically.

The existing `PrimeNormalizer.window_prime_lower` contains the admitted
`PR-WINDOW-PIT` obligation. A later call to `PrimeNormalizer.subpower` would
inherit that dependency. The unnormalized prime-window cap does not use it,
and the coarse boundary estimate uses exact positive-mass cancellation.
`ActualNormFormNormalization` deliberately isolates the call to the existing
normalizer lower bound and therefore inherits `PR-WINDOW-PIT`. Its output
must not be described as an admission-free sharp normalized estimate.

`JointAnalyticLimit` now supplies a complete source proof of the local
uniform-limit theorem for the three-complex-variable domain. Its proof
uses three Cauchy integrals and analytic inversion in the Banach algebra of
continuous functions on a product of circles. `ActualEulerRegion` applies
it to the actual normal product. `ActualEulerInput` fills all three fields
of the original `TRowEulerInput`, including joint `AnalyticOnNhd`, without
an analyticity premise. These source candidates still require the exact
native checks recorded above; the named presentation identification remains
an independent missing construction.

Detailed main-statement reports, including all ambient typeclasses and
quantifier order, are in [EULER.md](EULER.md), [NORMFORM.md](NORMFORM.md),
[BOUNDARY.md](BOUNDARY.md), and [UNIQUENESS.md](UNIQUENESS.md). Their unelaborated arithmetic candidates are
explicitly distinguished from native verified modules.

The six existing admissions in `HighBin.lean` are retained. No new support
file introduces `sorry`, `admit`, `axiom`, or `native_decide`. A declaration
that inherits an upstream admission is still reported as such by the
transitive axiom audit; absence of a local `sorry` is not a substitute for
that audit.
