import CubicSieve.PoissonTail
import CubicSieve.AnalyticSmoothingKernel
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let names := #[
    `CubicSieve.Profile.Gaussian.canonical_mellin_inversion,
    `CubicSieve.Profile.Gaussian.profileWeightedRow_block_bound,
    `CubicSieve.PoissonBlocks.actual_profile_block_bound,
    `CubicSieve.PoissonTail.actual_tail,
    `CubicSieve.AnalyticSmoothing.B_le_of_smoothEnergy_bound]
  for name in names do
    unless (← getEnv).contains name do
      throwError "Missing endpoint {name}"
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"CUBIC_TAIL_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"CUBIC_TAIL_AUDIT_CHECKED|{names.size}"
