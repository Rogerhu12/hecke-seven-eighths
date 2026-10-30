# HIGHBIN implementation and verification report

Working branch: `codex/highbin-euler-norm-boundary-20261030`.
Original base: `503ad9895e5f8affef55b22fea082e251bf33aa7`.
Merged current base: `5e4c85f172c101fd0c201219c13aa28f8b520d42` (`dtests-handoff`).
PR: https://github.com/Rogerhu12/hecke-seven-eighths/pull/1.
Toolchain: Lean `4.35.0-rc3`; Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.

## Current task status

This is a draft implementation. The four original obligations have not yet
been discharged in `HighBin.lean`. Their existing admissions are retained,
and the new support files contain no `sorry`, `axiom`, or `native_decide`.
The report will be updated with the final verification results before this
work session ends.

| Original obligation | Implemented connection | Remaining work |
|---|---|---|
| HB-EULER-INITIAL | Actual prime-power quotient Fourier formula, generator sixth-unit invariance, all local finite-Poisson branches, CRT phase cancellation, initial absolute-convergence candidate | Native verification and four-ideal Euler-product rearrangement |
| HB-EULER-EXCEPTIONAL | Arithmetic `RowEulerData`, actual finite Laurent tables, uniform `9 q^(-10e)` estimate and a consumer of the original `HighExceptionalEulerControl` type | Native verification and the named `actualHighPresentation.euler` identification |
| HB-NORMFORM | Actual repeated-prime conductor deficit, higher-prime-power errors, Mellin inversion, uniform shifted prime detector, radical conductor cap and exact full-correction slot product | Native verification, normalized slot estimates and actual labelled integral presentation |
| HB-MOVE-BOUNDARY | Actual row-contour rectangle, fixed-row arbitrary-order external tail bound, original whole-bin consumer and concrete buffered-height schedule | Native verification and actual presentation provider/schedule/retained-block count |

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

The first command builds the listed core files as separate Lean modules,
then asks Lean for every public declaration's exact type and transitive axiom
set. Its allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The `mellin` command separately checks four actual prime-power/Mellin modules
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
companions, that `T ≤ contourHeight`, that
`contourHeight + 3/2 ≤ upperHeight`, or that all upper heights and the retained
block count obey fixed polynomial bounds. The label-count hypothesis is a
per-block bound and does not establish a bound on the number of blocks.

The current definition of `shiftedPiece` and its sum identities also do not
identify each labelled piece with its full-correction integral. Cancellation
between arbitrary pieces prevents deducing the desired norm-form estimate
from these identities alone. A concrete construction of the named
presentation is required; this observation is not a counterexample to a
correctly constructed presentation.

## Recorded native verification

At commit `29d6f4d30ee5d08de3597e3ff932944c1e1076ac`, the GitHub Actions
core step passed **44 separately compiled modules and 358 public declaration
checks**. Each printed axiom set was contained in
`{propext, Classical.choice, Quot.sound}`. This verifies that snapshot;
it does not verify subsequent edits or the arithmetic adapters.

Run: https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41116744429

The complete arithmetic build in that run was still in progress at this
checkpoint. The later canonical-type split, indexed compensation lemma,
CRT files and new arithmetic consumers require their own new native result.
The revised workflow checks core, Mellin and complete arithmetic in separate
jobs so their outcomes remain visible independently.

A local 17-source joint unit for `ActualNormFormHigherPrimePowers` completed
with three errors in that new module. All three were repaired and a second
check is running. The failed run is not a successful verification result.
Joint units hoist imports and are never counted as separate-module builds.

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
* The arithmetic fixed-row boundary bound has the form
  `C_N Z^13 (2+U)^(6 r_infty) T_ext^(-N)`. The finite family is an actual
  frequency-row envelope; row counting and Euler bounds are conclusions,
  not supplied tail estimates.
* `highBoundaryControl_of_buffered_schedule` consumes the original
  presentation type, the arithmetic Euler-provider equality, `1` in the
  companion set, positive `delta ≤ 1`, nonnegative `kappa`, a bounded
  buffered-height index and a genuine retained-block count. It uses
  `H=delta*max(T,Z^kappa)` and `U=3(i+1)*max(T,Z^kappa)`.
  With block degrees `AB,RB`, its fixed degrees are
  `A=AB+6 r_infty` and `R=13+RB+6 r_infty*kappa`, chosen before the tail
  order. These are structural hypotheses missing from the named provider,
  not a restatement of the desired boundary estimate.

## Unresolved dependencies that must not be hidden

`Base.highExpansion` is still an admitted construction. Its target record
allows arbitrary blocks, labels and slot values; it does not itself construct
the retained fixed-bin integral or identify each label with its complete
compensation amplitude. The new slot formula does not establish those
identifications automatically.

The existing `PrimeNormalizer.window_prime_lower` contains the admitted
`PR-WINDOW-PIT` obligation. A later call to `PrimeNormalizer.subpower` would
inherit that dependency. The prime-window cap written here does not use it,
and the coarse boundary estimate uses exact positive-mass cancellation.
A sharp normalized norm-form estimate still has to handle this issue.

Normal convergence and joint continuity of the actual Euler correction,
and holomorphy in the moving `s` variable, are separate proved candidates.
They must not be reported as the full three-complex-variable
`AnalyticOnNhd` field of `TRowEulerInput`; that field still needs a complete
argument on the specified corrected region.

The six existing admissions in `HighBin.lean` are retained. No new support
file introduces `sorry`, `admit`, `axiom`, or `native_decide`. A declaration
that inherits an upstream admission is still reported as such by the
transitive axiom audit; absence of a local `sorry` is not a substitute for
that audit.
