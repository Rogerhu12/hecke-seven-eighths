module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.BlueprintAssembly
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksFirstTransform
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksFirstAllowance
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksAmplification
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksSecondTransform
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksNominalGeometry
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksFiniteLeaves
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksOriginalAtoms
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksPassiveRefinement
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksOriginalCalibration
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksOriginalCapacity
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileFormulaTask
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksProfileWindows
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksFullKappa
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksChildArithmetic
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksChildProfiles
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksSourceIndex
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksNormalizedMass
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9OriginalWindowMass
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksFirstZero
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksSecondZero
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksExceptionalRecovery
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksExceptionalSummation
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksTails
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksUniform

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The paired engine step from the completed task proofs

The canonical source parameters are shared by all twenty-four task proofs.
The capacity field uses the uniform original-capacity theorem, and the
kernel field uses the original-window mass theorem.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]

/-- The full paired engine step on its two Fourier coordinates, with all
blueprint task premises discharged by their proved task theorems. -/
theorem pairedStepHypothesis (c : TargetContext K) :
    EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c := by
  let p : SourceParameters c := canonicalSourceParameters c
  have tasks : TaskProofs c p := {
    firstTransform := Tasks.firstTransform c p
    firstAllowance := Tasks.firstAllowance c p
    amplification := Tasks.amplification c p
    secondTransform := Tasks.secondTransform c p
    nominalGeometry := Tasks.nominalGeometry c p
    finiteLeaves := Tasks.finiteLeaves c p
    originalAtoms := Tasks.originalAtoms c p
    passiveRefinement := Tasks.passive_refinement c p
    originalCalibration := Tasks.original_calibration c p
    originalCapacity := Blueprint.originalCapacityTask_uniform c p
    profileFormula := Tasks.profile_formula_control
    profileWindows := Tasks.profile_windows c
    fullKappa := Tasks.fullKappaNormalization c
    childArithmetic := Tasks.child_arithmetic c p
    childProfiles := Tasks.child_profiles c p
    sourceIndex := Tasks.sourceIndex c p
    normalizedMass := Tasks.normalizedMass c p
    kernelMass := Tasks.originalWindowKernelMass c p
    firstZero := Tasks.firstZero c p
    secondZero := Tasks.secondZero c p
    exceptionalRecovery := Tasks.exceptional_recovery c p
    exceptionalSummation := Tasks.exceptional_summation c p
    tails := Tasks.tails c p
    uniform := Tasks.uniformPreparation c }
  exact pairedStepHypothesis_of_blueprint c tasks

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.pairedStepHypothesis
