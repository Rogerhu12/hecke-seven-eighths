import CubicSieve.CompleteBridge
import Lean.Util.CollectAxioms

/-! Strict recursive guards for the independent endpoint and the exact
original-context consumer. Both must use only the three standard axioms. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `CubicSieve.PoissonEstimate.actual_annular_bound,
    `CubicSieve.GcdPoissonAssembly.annular_smoothEnergy_bound,
    `CubicSieve.Complete.full_smooth_bound,
    `CubicSieve.Complete.fullEstimate,
    `CubicSieve.Complete.targetBound,
    `CubicSieve.CompleteBridge.moment_cubic_sieve]
  for name in names do
    unless (← getEnv).contains name do
      throwError "Missing endpoint {name}"
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"CUBIC_COMPLETE_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"CUBIC_COMPLETE_AUDIT_CHECKED|{names.size}"
  let bridge := `CubicSieve.CompleteBridge.moment_cubic_sieve
  unless (← getEnv).contains bridge do
    throwError "Missing bridge {bridge}"
  let deps ← Lean.collectAxioms bridge
  logInfo m!"CUBIC_CONTEXT_BRIDGE_AXIOMS|{bridge}|{String.intercalate "," (deps.toList.map toString)}"

#print axioms CubicSieve.Complete.targetBound
#print axioms CubicSieve.CompleteBridge.moment_cubic_sieve
