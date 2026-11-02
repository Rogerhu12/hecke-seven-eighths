import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOutputConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.UnrestrictedSixthCapacity

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The same literal leaves produce the smaller admissible children

The merged side-frame and actual frozen-atom calibration are used once,
parameterized by the Cauchy side.  Capacity deletes one whole-slot
prefix only after all allocation and clipping defects are included.
The source recipe, slot mesh, theta and ranked profile invariant belong
to these same selected children.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

/-- This is the actual output of the per-leaf normalization construction,
including both integrability proofs and the ordinary Cauchy domination. -/
def selectedNormalization (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    NormalizedExpansion (selectedExpansion request frequency)
      (recipeInductionSigma c) (admissibleOfInvariant request.primitive) := by
  sorry

/-- Both side invariants refer to the existing children and measures. -/
theorem selectedNormalization_invariant
    (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)
    (side : Bool) (b : (selectedNormalization request frequency).Label)
    (ξ : EngineParameter) :
    admissibleOfInvariant request.primitive
      ((selectedNormalization request frequency).children.data side b ξ)
      ((selectedNormalization request frequency).children.parameters side b) := by
  sorry

theorem selectedNormalization_parent
    (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ) :
    (selectedModel request frequency).normalizedEnergy request.base 0 ≤
      ((selectedExpansion request frequency).normalizedTerminals
        (request_base_pos request).le).total +
          (selectedNormalization request frequency).kernels.pairIntegral := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2
