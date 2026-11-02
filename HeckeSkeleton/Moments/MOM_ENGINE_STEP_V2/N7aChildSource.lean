import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActiveChildAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceReflection
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualRecipeTheta

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N7a: the original complete source in the same frozen capacity child

The actual capacity child keeps the original moving factors, correction,
remaining ideal and all allowed-row arithmetic. Clipping and whole-slot
removal leave both m and q unchanged. Consequently the original support
and full joint budgets apply to every row of the child's own paired-row
filter, including when its last slot has been removed.

The separate open prime annulus is transported by the base theorem on
these same frozen profiles. The canonical theta then supplies reflection
arithmetic directly, with no new row-exclusion or analytic premise.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N7a

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Expansion.Project

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {H : Type} {k : ℕ}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}

/-- This certificate records the exact chosen child; its recipe is the
original recipe transported through that child's fixed removal set. -/
def frozenChildSource (D : OriginalCalibration call s)
    (conditions : D.SourceConditions)
    {G : D.calibration.NormalizedCapacityData} (out : G.Child)
    (ξ : EngineParameter) :
    CompleteSourceBudgetData c
      (canonicalDetectorTheta K (targetCharacter K c)) call.base
      (out.frozenData ξ) (pairedInvariantParameters out.parameters) where
  source := {
    recipe := (out.completeMovingRowRecipe D.recipe).at ξ
    theta_eq := (out.frozen_theta_eq ξ).trans
      ((D.theta_eq ξ).trans call.source.source.theta_eq)
    slot_characters := by
      intro i
      rw [← (D.theta_eq ξ).trans call.source.source.theta_eq]
      exact out.frozen_slot_in_theta ξ i
    timeIndependent :=
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ }
  primeSupport :=
    ActiveChildAnnulus.frozen_child_prime_support out conditions.primeSupport ξ
  supportBudget := out.completeMovingRowRecipe_supportBudget D.recipe call.base
    (by simpa only [D.base_eq] using conditions.support)
  pairedJointBudget := by
    intro u hu
    exact out.completeMovingRowRecipe_fullJointBudget D.recipe call.base
      (by simpa only [D.base_eq] using conditions.joint) ξ u
      (((out.frozenData ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1

/-- Both arithmetic primitives use the same certificate and the same
frozen child. The fixed finite theta is the original recipe theta. -/
theorem frozenChildArithmetic (D : OriginalCalibration call s)
    (conditions : D.SourceConditions)
    {G : D.calibration.NormalizedCapacityData} (out : G.Child)
    (ξ : EngineParameter) :
    actualCompleteSourceBudgetPrimitive c call.base (out.frozenData ξ)
        (pairedInvariantParameters out.parameters) ∧
      admissibleOfInvariant
        (reflectionArithmeticPrimitive (places K c) (probeData K c)
          (momentRowCharacters K c) (recipeThetaFamily (expansionRecipeRaw K c)) call.base)
        (out.frozenData ξ) out.parameters := by
  let source := frozenChildSource D conditions out ξ
  refine ⟨⟨source⟩, ?_⟩
  change reflectionArithmeticPrimitive (places K c) (probeData K c)
    (momentRowCharacters K c) (recipeThetaFamily (expansionRecipeRaw K c)) call.base
    (out.frozenData ξ) (pairedInvariantParameters out.parameters)
  rw [actualRecipeThetaFamily c]
  exact source.canonicalReflectionArithmetic

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N7a

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N7a.frozenChildSource
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N7a.frozenChildArithmetic
