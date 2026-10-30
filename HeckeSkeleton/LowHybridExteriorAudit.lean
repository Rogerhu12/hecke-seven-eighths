import HeckeSkeleton.LowHybridExterior
import Lean.Util.CollectAxioms

/-!
# Recursive axiom guard for the actual exterior-ideal wiring

Check every theorem and definition introduced by the actual-object adapters,
including private helper declarations after recovering their user names.
An unexpected axiom makes compilation fail.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes : Array Name := #[
    `HeckeSkeleton.LowHybrid.ExteriorArithmetic,
    `HeckeSkeleton.LowHybrid.ExteriorSymbol,
    `HeckeSkeleton.LowHybrid.ExteriorSieve,
    `HeckeSkeleton.LowHybrid.Exterior,
    `HeckeSkeleton.LowFrozenCube.ExteriorLocalBounds,
    `HeckeSkeleton.LowFrozenCube.Exterior]
  let names := (env.constants.toList.filterMap fun (name, info) =>
    let userName := privateToUserName name
    if (info.isTheorem || info.isDefinition) &&
      prefixes.any (fun prefix => prefix.isPrefixOf userName)
    then some name else none).toArray.qsort Name.lt
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"EXTERIOR WIRING AUDIT PASSED: {names.size} declarations."

#print axioms HeckeSkeleton.LowHybrid.Exterior.hybrid_energy
#print axioms HeckeSkeleton.LowHybrid.Exterior.hybrid_energy_with_beta_mass
#print axioms HeckeSkeleton.LowHybrid.Exterior.hybrid_energy_bounded
#print axioms HeckeSkeleton.LowHybrid.Exterior.completed_quadratic_energy_bounded
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.primitiveLocalBounds
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.uniform_actual_source_energy_ledger
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.uniform_family_source_energy_power_saving
