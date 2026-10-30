# HIGHBIN implementation and verification report

Working branch: `codex/highbin-euler-norm-boundary-20261030`.
Base: `503ad9895e5f8affef55b22fea082e251bf33aa7` (`dtests-handoff`).
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
| HB-EULER-INITIAL | Actual prime-power quotient Fourier formula, generator sixth-unit invariance, finite local Gauss tables, initial absolute-convergence candidate | Actual finitePoisson expansion, CRT twists and four-ideal Euler-product rearrangement |
| HB-EULER-EXCEPTIONAL | Arithmetic `RowEulerData`, actual finite Laurent tables and the uniform `9 q^(-10e)` estimate | Native verification and the named `actualHighPresentation.euler` construction |
| HB-NORMFORM | Actual repeated-prime conductor deficit, higher-prime-power errors, Mellin inversion and initial logarithmic-derivative detector | Uniform shifted prime detector and actual labelled integral presentation |
| HB-MOVE-BOUNDARY | Actual row-contour rectangle, fixed-row arbitrary-order external tail bound and Euler-product/L-ratio connections | Native verification, actual presentation heights and retained block count |

## Repository changes

`rowEulerRegion` now includes the missing conditions
`1 < Re(w) + 6 Re(z)` and `1 < Re(s) + 6 Re(z)`.
The finite Laurent data definitions have moved verbatim from
`PhysicalProbeRows` to `FiniteEulerRational`; the former imports and reexports
the same definitions. Their names and types are unchanged.

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
python scripts/highbin_verify.py core
python scripts/highbin_verify.py actual
```

The first command builds the listed core files as separate Lean modules,
then asks Lean for every public declaration's exact type and transitive axiom
set. Its allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The second command checks the real arithmetic adapters and `HighBin.lean`.
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
