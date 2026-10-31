import HeckeSkeleton.LowHybridExterior
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Recursive axiom guard for the actual exterior-ideal wiring

Check every declaration introduced by the actual-object adapters, including
private helpers after recovering their user names and the declarations generated
for structures.  No declaration-kind filter is used: an unused axiom or opaque
definition must not escape the audit.  Every adapter namespace must be present,
and an unexpected axiom makes compilation fail.
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
  let names := (env.constants.toList.filterMap fun (name, _) =>
    let userName := privateToUserName name
    if prefixes.any (fun nsPrefix => nsPrefix.isPrefixOf userName)
    then some name else none).toArray.qsort Name.lt
  for nsPrefix in prefixes do
    unless names.any (fun name => nsPrefix.isPrefixOf (privateToUserName name)) do
      throwError "Missing exterior adapter namespace in axiom audit: {nsPrefix}"
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
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.ofReflectionIndex
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.primitiveLocalBounds
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.reflectedTerm_eq_rawSourceTerm
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.reflectionSourceBlock_annularSupport
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.uniform_weighted_raw_hybrid_bound
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.uniform_actual_source_energy_ledger
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.uniform_family_source_energy_power_saving
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.uniform_actual_family_source_energy_subpower
#print axioms HeckeSkeleton.LowFrozenCube.Exterior.uniform_actual_family_source_energy_power_saving
