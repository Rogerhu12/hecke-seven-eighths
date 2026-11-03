import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyNormalizationCertificate
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.GlobalAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileFormula

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The complete paired step from the named blueprint tasks

Each field below is one of the original public task propositions.
The original N8 task is represented by its two published parts, N8a
and N8b. The final theorem constructs the three internal certificates;
none of them is an additional premise. All original source, refinement,
capacity and kernel choices are shared by the assembled estimates.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

/-- Proofs of the published blueprint tasks, with N8a and N8b separate.
N5a is retained as an explicit task premise although the N5b contract
already packages the profile windows needed by the final assembly. -/
structure TaskProofs (c : TargetContext K) (p : SourceParameters c) : Prop where
  firstTransform : FirstTransformTask c p
  firstAllowance : FirstAllowanceTask c p
  amplification : AmplificationTask c p
  secondTransform : SecondTransformTask c p
  nominalGeometry : NominalGeometryTask c p
  finiteLeaves : FiniteLeafTask c p
  originalAtoms : OriginalAtomTask c p
  passiveRefinement : PassiveRefinementTask c p
  originalCalibration : OriginalCalibrationTask c p
  originalCapacity : UniformOriginalCapacityTask c p
  profileFormula : ProfileFormulaTask
  profileWindows : ProfileWindowTask c
  fullKappa : FullKappaTask c
  childArithmetic : ChildArithmeticTask c p
  childProfiles : ChildProfileTask c p
  sourceIndex : SourceIndexTask c p
  normalizedMass : NormalizedMassTask c p
  kernelMass : OriginalWindowKernelMassTask c p
  firstZero : FirstZeroTask c p
  secondZero : SecondZeroTask c p
  exceptionalRecovery : ExceptionalRecoveryTask c p
  exceptionalSummation : ExceptionalSummationTask c p
  tails : TailTask c p
  uniform : UniformChoiceTask c

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]

/-- All source, terminal and normalization certificates are derived
from the named task proofs before the uniform preparation is chosen. -/
theorem pairedStepHypothesis_of_taskProofs (c : TargetContext K)
    (p : SourceParameters c) (tasks : TaskProofs c p) :
    PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c := by
  classical
  let source (frame : SourceFrame) : SourceCertificate c frame p :=
    Classical.choice (sourceCertificate c frame p
      tasks.firstTransform tasks.firstAllowance tasks.amplification
      tasks.secondTransform tasks.nominalGeometry tasks.finiteLeaves)
  let terminal (frame : SourceFrame) : TerminalCertificates c frame p :=
    terminalCertificates c frame p tasks.firstZero tasks.secondZero
      tasks.exceptionalRecovery tasks.sourceIndex tasks.exceptionalSummation tasks.tails
  let normalization (frame : SourceFrame) : NormalizationCertificate c frame p :=
    Classical.choice (normalizationCertificate_of_tasks c p frame
      tasks.originalAtoms tasks.passiveRefinement tasks.originalCalibration
      tasks.originalCapacity tasks.profileWindows tasks.fullKappa
      tasks.childArithmetic tasks.childProfiles tasks.sourceIndex
      tasks.normalizedMass tasks.kernelMass)
  exact pairedStepHypothesis_of_certificates c p source terminal normalization tasks.uniform

/-- The requested full assembly on the actual two Fourier coordinates.
The source parameters are the existing canonical positive choices. -/
theorem pairedStepHypothesis_of_blueprint (c : TargetContext K)
    (tasks : TaskProofs c (canonicalSourceParameters c)) :
    EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c :=
  pairedStepHypothesis_of_taskProofs c (canonicalSourceParameters c) tasks

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.pairedStepHypothesis_of_taskProofs
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.pairedStepHypothesis_of_blueprint
