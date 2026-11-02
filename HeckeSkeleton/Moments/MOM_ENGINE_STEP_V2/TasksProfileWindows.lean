import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileWindowContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! N5b: raw and clipped windows on the same original profiles. -/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem profile_windows (c : TargetContext K) :
    ProfileWindowTask c := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks
