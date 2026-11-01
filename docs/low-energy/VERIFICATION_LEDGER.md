# Native verification ledger

This file records where to review actual runs. It contains no compiler output,
compiled checkpoint, reusable success receipt, or inferred process exit code.

| Source commit | Native run | Observed result |
| --- | --- | --- |
| `8f75a240f4ae820cf93594a5c1415330df70dbd4` | [41211296149](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41211296149) | Failed at the dependent powerset rewrite in `ActualTupleReconstruction`; downstream terminal and final audit not reached. |
| `da1cd936b24ede2c6b9d352cf9d1e8adb8c37d40` | [41218050060](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41218050060) | One source error at the same backward rewrite after exposing the frozen-state projections. Current source instead supplies the motive and applies the finite-subset identity forwards. |
| `46ac7a70064c83cf1a7cea7ed275d5fd39346cc3` | [41220627816](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41220627816) | Lake exit 1 after 1650.518 seconds, not a timeout. Twelve diagnostics in `GeneralSeparatedEnergy`, `GeneralRows`, `GeneralConductor`, and `GeneralInactiveMass`. Downstream terminal and final axiom audit not reached. |
| `bcb308443216fb32e60d3f5be03cc832ffd2461d` | [41223690903](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41223690903) | Lake exit 1 after 1598.445 seconds, not a timeout. Nine diagnostics in `GeneralHeight` and `GeneralConductor`; 496 actual Built events, including 90 of 119 explicit targets. `GeneralRows` and `GeneralInactiveMass` built with standard-axiom reports. Endpoint and final axiom audit still blocked by failed dependencies. |
| `7abe5414ae7e531e0e3b57c8d27d720aea32e918` | [41226591691](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41226591691) | Lake exit 1 after 1850.285 seconds, not a timeout. Twelve diagnostics in `ActualTupleReconstruction`, `GeneralAggregation`, `GeneralHeightTail`, and `GeneralProductReconstruction`; 509 actual Built events, including 103 of 120 explicit targets. The common scale-law kernel, general reflected block, marked exponent, conductor and normalization factorization modules built. Final endpoint audits remain blocked. |
| `3aa9665d10689f257fea502d0790fbe1204654d4` | [41264411216](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41264411216) | Lake exit 1 after 1932.858 seconds, not a timeout. 516 actual Built events, including 110 of 120 explicit targets. `ActualResidualDyadicEnergy`, `GeneralKernelTail`, and `GeneralTupleBlocks` failed; downstream endpoints and final audits were blocked. The 34-source diagnostic completed in 152.387 seconds and exposed additional cutoff and physical assembly errors. Its raw log includes typed errors as well as plain errors; the current diagnostic mapper recognizes both. |
| `c38ef28daf8138982a0088cea483e0215aa833ff` | [41267627754](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41267627754) | Lake exit 1 after 1902.015 seconds, not a timeout. 520 actual Built events, including 114 of 120 explicit targets. The original physical completed-energy theorem built and printed only the three standard axioms. Two primary modules failed: `GeneralColumnCutoff` and `GeneralTupleBlocks`; the 34-source diagnostic exposed two unqualified `FixedData` references in the final general structure. The fresh final four-declaration audit was not reached. |
| Current PR head | [PR #3 checks](https://github.com/Rogerhu12/hecke-seven-eighths/pull/3/checks) | Inspect the run whose recorded checkout matches the current head. Acceptance requires a zero native build exit and all four strict axiom audits. |

Each run preserves `.low-energy-lake-verification` as an Actions artifact,
including the exact checkout, requested source hashes, pinned Lean/Mathlib/cache
metadata, native build log and any final audit actually reached. The separate
native-output artifact is for diagnosis only; it is never restored by this CI.

Acceptance requires the exact current head to build all reviewed new sources and
`HeckeSkeleton.Principal`, followed by successful strict `#print axioms` checks
for all of:

- `HeckeSkeleton.completedMarkedEnergy` (general canonical terminal).
- `HeckeSkeleton.physicalCompletedMarkedEnergy` (original physical row budget).
- `HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy.completedMarkedEnergy`.
- `HeckeGeneral.ThetaSkeleton.Physical.compensatedRowMellinKernel_factorization`
  (the changed normalization consumer, explicitly built and imported for this audit).

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Missing,
malformed, duplicate, unexpected or admitted axiom reports fail the gate. A
failed build cannot produce a passing overall report. Python fixture tests check
these gate semantics and source validation; they are not Lean proof evidence.
