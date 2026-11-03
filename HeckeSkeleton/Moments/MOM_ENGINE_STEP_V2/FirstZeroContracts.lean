import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TerminalData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.InputDemands

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: the first zero term on the original source

The displayed cost is the actual common-support zero transform. Its
full support, primitive coefficient, inverse budget and two centered
rectangles are those fixed by `FirstPresentation.Realizes`.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

structure FirstZeroCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  cost : UniformCost
  bound : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    cost.Ready call input → ∀ F : FirstPresentation call p, F.Realizes →
      F.normalizedZero ≤ cost.value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c

def FirstZeroTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ frame : SourceFrame, Nonempty (FirstZeroCertificate c frame p)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
