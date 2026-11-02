import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceFrame
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalInput
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceBudgets

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Mellin preparation separates profiles from the actual engine output

A prepared call stores the actual original profile control and the
fixed scalar factors selected for its literal Mellin models. The
continuous Fourier output and all source/terminal/mass inequalities
are constructed later. The same selected models provide the complete
moving recipe and its original two arithmetic budgets.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

local instance callReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance callReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

structure PreparedCall (n : Node K ω ψ) where
  cap : ℕ
  order : ℕ
  weight : ℝ
  lower : ℝ
  upper : ℝ
  weight_nonneg : 0 ≤ weight
  lower_pos : 0 < lower
  interval : lower ≤ upper
  profileBudget : ℝ
  profileBudget_one_le : 1 ≤ profileBudget
  slot_cap : n.data.geometry.slotCount ≤ cap
  profiles : ModelProfileControl n.data (order + 2) weight profileBudget 0 lower upper 0
  engineCoefficient : ℝ
  engineControl : ℝ
  engineCoefficient_nonneg : 0 ≤ engineCoefficient
  engineControl_nonneg : 0 ≤ engineControl

namespace PreparedCall

variable {n : Node K ω ψ}

def model (call : PreparedCall n) (frequency : ℝ × ℝ) : Node K ω ψ :=
  n.mellinStrictModel (Ω := CombinedParameter) call.cap call.order call.weight
    call.lower call.upper call.weight_nonneg call.lower_pos call.interval
    call.profileBudget call.profileBudget_one_le frequency

/-- The outer Mellin cost is purely a coefficient/profile quantity. -/
def mellinCost (call : PreparedCall n) : ℝ :=
  mellinStrictMassConstant (K := K) (ω := ω) (ψ := ψ) (Ω := CombinedParameter)
    call.cap call.order call.weight call.lower call.upper
    call.weight_nonneg call.lower_pos call.interval *
      call.profileBudget ^ (2 * (call.cap + 2)) *
        (call.engineCoefficient * call.engineControl)

theorem model_parameters (call : PreparedCall n) (frequency : ℝ × ℝ) :
    (call.model frequency).parameters = n.parameters := by
  sorry

theorem model_slotCount (call : PreparedCall n) (frequency : ℝ × ℝ) :
    (call.model frequency).data.geometry.slotCount = n.data.geometry.slotCount := by
  sorry

end PreparedCall

namespace SourceRequest

variable {c : TargetContext K} {frame : SourceFrame} {schedule : OrderSchedule}
variable {Cp Hp : ℝ} {bounds : UniformBounds}

/-- This is the original node's recipe on its literal prepared model;
the full mask, original prime support and both budgets are preserved. -/
def preparedSourceData (request : SourceRequest c frame schedule Cp Hp bounds)
    (call : PreparedCall request.parent) (frequency : ℝ × ℝ) :
    CompleteSourceBudgetData c
      (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
      request.base (call.model frequency).data
      (pairedInvariantParameters (call.model frequency).parameters) := by
  sorry

def preparedNormProfiles (request : SourceRequest c frame schedule Cp Hp bounds)
    (call : PreparedCall request.parent) :
    EngineStep.NormProfileRecipe (fun frequency : ℝ × ℝ =>
      (call.model frequency).data) := by
  sorry

/-- The leaf producer starts with these literal arithmetic atoms. -/
def originalInput (request : SourceRequest c frame schedule Cp Hp bounds)
    (call : PreparedCall request.parent) (frequency : ℝ × ℝ) :
    OriginalInput c (call.model frequency) request.base where
  theta := Expansion.Project.canonicalDetectorTheta K (targetCharacter K c)
  source := (request.preparedSourceData call frequency).source
  normProfiles := (request.preparedNormProfiles call).at frequency

end SourceRequest
end HeckeSkeleton.Moments.EngineStepV2
