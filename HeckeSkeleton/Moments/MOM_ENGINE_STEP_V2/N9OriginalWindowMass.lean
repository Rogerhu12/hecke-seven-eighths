import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9OriginalWindowContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! N9: original windows and the capacities projected from their same N6 results. -/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem originalWindowKernelMass (c : TargetContext K) (p : SourceParameters c) :
    OriginalWindowKernelMassTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks
