# Native verification ledger

This file records where to review actual runs. It contains no compiler output,
compiled checkpoint, reusable success receipt, or inferred process exit code.

| Source commit | Native run | Observed result |
| --- | --- | --- |
| `8f75a240f4ae820cf93594a5c1415330df70dbd4` | [41211296149](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41211296149) | Failed at the dependent powerset rewrite in `ActualTupleReconstruction`; downstream terminal and final audit not reached. |
| `da1cd936b24ede2c6b9d352cf9d1e8adb8c37d40` | [41218050060](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41218050060) | One source error at the same backward rewrite after exposing the frozen-state projections. Current source instead supplies the motive and applies the finite-subset identity forwards. |
| `46ac7a70064c83cf1a7cea7ed275d5fd39346cc3` | [41220627816](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41220627816) | Lake exit 1 after 1650.518 seconds, not a timeout. Twelve diagnostics in `GeneralSeparatedEnergy`, `GeneralRows`, `GeneralConductor`, and `GeneralInactiveMass`. Downstream terminal and final axiom audit not reached. |
| Current general source | Next complete workflow run | Pending. No current acceptance claim. |

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

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Missing,
malformed, duplicate, unexpected or admitted axiom reports fail the gate. A
failed build cannot produce a passing overall report. Python fixture tests check
these gate semantics and source validation; they are not Lean proof evidence.
