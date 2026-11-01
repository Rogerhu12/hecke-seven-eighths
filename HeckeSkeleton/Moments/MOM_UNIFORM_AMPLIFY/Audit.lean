import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FiniteSectorReindex
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FinitePropagation
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SharedFourierPropagation
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.InterfaceObstructions
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceGeometry
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.Eligibility
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerMasks
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.IndependentAmplification
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceProfileControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceActualReindex
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.AmplificationSource
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.WitnessSource
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileEuler
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileScaleJets
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FourierApplication
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceProfileJets
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceFourierControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileCommonFourier
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Every declaration in the task namespace is checked transitively,
including definitions, private helpers and generated declarations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let namespacePrefix := `HeckeSkeleton.Moments.UniformAmplify
  let names := (env.constants.fold (init := (#[] : Array Name)) fun acc name _ =>
    if namespacePrefix.isPrefixOf (privateToUserName name) then acc.push name else acc).qsort Name.lt
  unless names.size > 0 do
    throwError "The MOM_UNIFORM_AMPLIFY namespace is missing"
  let required : Array Name := #[
    `HeckeSkeleton.Moments.UniformAmplify.inverse_finite_sector_reindex,
    `HeckeSkeleton.Moments.UniformAmplify.modelProfileControl_prime,
    `HeckeSkeleton.Moments.UniformAmplify.ReductionTree.propagate,
    `HeckeSkeleton.Moments.UniformAmplify.log_power_absorption,
    `HeckeSkeleton.Moments.UniformAmplify.shared_measure_integral_envelope,
    `HeckeSkeleton.Moments.UniformAmplify.shared_fourier_integral_envelope,
    `HeckeSkeleton.Moments.UniformAmplify.blockSource_witness_geometry,
    `HeckeSkeleton.Moments.UniformAmplify.paired_rows_eventual_eligibility,
    `HeckeSkeleton.Moments.UniformAmplify.decomposedZeroSlotMomentData_sixthPowerMasks,
    `HeckeSkeleton.Moments.UniformAmplify.actual_witness_energy,
    `HeckeSkeleton.Moments.UniformAmplify.witness_bound_of_independent_bound,
    `HeckeSkeleton.Moments.UniformAmplify.uniform_witness_calibration,
    `HeckeSkeleton.Moments.UniformAmplify.actual_source_profile_control,
    `HeckeSkeleton.Moments.UniformAmplify.source_moment_finite_sector_reindex,
    `HeckeSkeleton.Moments.UniformAmplify.recipeMomentModels_sixthPowerMasks,
    `HeckeSkeleton.Moments.UniformAmplify.recipe_inverse_independent_amplification,
    `HeckeSkeleton.Moments.UniformAmplify.actual_inverse_amplified_witness_models]
  for name in required do
    unless names.contains name do
      throwError "Missing task theorem: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"MOM_UNIFORM_AMPLIFY_AXIOMS|{name}|{dependencies}"
  logInfo m!"MOM_UNIFORM_AMPLIFY_AUDIT_PASSED|{names.size}"

#print axioms HeckeSkeleton.Moments.UniformAmplify.inverse_finite_sector_reindex
#print axioms HeckeSkeleton.Moments.UniformAmplify.paired_finite_sector_reindex
#print axioms HeckeSkeleton.Moments.UniformAmplify.unmarked_finite_sector_reindex
#print axioms HeckeSkeleton.Moments.UniformAmplify.modelProfileControl_prime
#print axioms HeckeSkeleton.Moments.UniformAmplify.ReductionTree.propagate
#print axioms HeckeSkeleton.Moments.UniformAmplify.log_power_absorption
#print axioms HeckeSkeleton.Moments.UniformAmplify.diagonalCutoffEnergy_violates_amplification
#print axioms HeckeSkeleton.Moments.UniformAmplify.paired_rows_eventual_eligibility
#print axioms HeckeSkeleton.Moments.UniformAmplify.decomposedZeroSlotMomentData_sixthPowerMasks
#print axioms HeckeSkeleton.Moments.UniformAmplify.actual_witness_energy
#print axioms HeckeSkeleton.Moments.UniformAmplify.witness_bound_of_independent_bound

#print axioms HeckeSkeleton.Moments.UniformAmplify.uniform_witness_calibration
#print axioms HeckeSkeleton.Moments.UniformAmplify.blockSource_witness_geometry
#print axioms HeckeSkeleton.Moments.UniformAmplify.shared_fourier_integral_envelope
#print axioms HeckeSkeleton.Moments.UniformAmplify.shared_measure_integral_envelope
