module

public import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FiniteSectorCore
public import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FinitePropagation
public import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.InterfaceObstructions
public import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.WitnessCalibration
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

/-! A small independent CI gate for the arithmetic-free proofs.  The full
`Audit` gate additionally imports and checks every actual-model adapter. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefix := `HeckeSkeleton.Moments.UniformAmplify
  let names := (env.constants.fold (init := (#[] : Array Name)) fun acc name _ =>
    if prefix.isPrefixOf (privateToUserName name) then acc.push name else acc).qsort Name.lt
  let required : Array Name := #[
    `HeckeSkeleton.Moments.UniformAmplify.finite_sector_sum_le,
    `HeckeSkeleton.Moments.UniformAmplify.ReductionTree.propagate,
    `HeckeSkeleton.Moments.UniformAmplify.log_power_absorption,
    `HeckeSkeleton.Moments.UniformAmplify.diagonalCutoffEnergy_violates_amplification,
    `HeckeSkeleton.Moments.UniformAmplify.uniform_witness_calibration]
  for name in required do
    unless names.contains name do
      throwError "Missing pure task theorem: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"MOM_UNIFORM_AMPLIFY_AXIOMS|{name}|{dependencies}"
  logInfo m!"MOM_UNIFORM_AMPLIFY_PURE_AUDIT_PASSED|{names.size}"

#print axioms HeckeSkeleton.Moments.UniformAmplify.finite_sector_sum_le
#print axioms HeckeSkeleton.Moments.UniformAmplify.ReductionTree.propagate
#print axioms HeckeSkeleton.Moments.UniformAmplify.log_power_absorption
#print axioms HeckeSkeleton.Moments.UniformAmplify.diagonalCutoffEnergy_violates_amplification
#print axioms HeckeSkeleton.Moments.UniformAmplify.uniform_witness_calibration
