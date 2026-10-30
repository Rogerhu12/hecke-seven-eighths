import HeckeSkeleton.LowHybrid
import HeckeSkeleton.LowFrozenCube
import Lean.Util.CollectAxioms

/-! Check every theorem in the two new namespaces, including private
auxiliaries after normalizing their internal names. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.filterMap fun (name, info) =>
    let userName := privateToUserName name
    if info.isTheorem &&
      ((`HeckeSkeleton.LowHybrid).isPrefixOf userName ||
       (`HeckeSkeleton.LowFrozenCube).isPrefixOf userName)
    then some name else none).toArray.qsort Name.lt
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"AUDIT PASSED: {names.size} theorems; every dependency is among propext, Classical.choice, Quot.sound."

#print axioms HeckeSkeleton.LowHybrid.hybrid_energy
#print axioms HeckeSkeleton.LowHybrid.hybrid_energy_bounded
#print axioms HeckeSkeleton.LowHybrid.hybrid_energy_with_beta_mass
#print axioms HeckeSkeleton.LowHybrid.completed_quadratic_energy_bounded
#print axioms HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_source_energy_ledger
#print axioms HeckeSkeleton.LowFrozenCube.FrozenReduction.uniform_source_energy_power_saving
