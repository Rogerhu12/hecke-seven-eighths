import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4CalibrationContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! N4: capacity on the same original calibration, with the uniform fixed-frame demand. -/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem originalCapacityTask (c : TargetContext K) (p : SourceParameters c) :
    OriginalCapacityTask c p := by
  sorry

theorem originalCapacityTask_uniform (c : TargetContext K) (p : SourceParameters c) :
    UniformOriginalCapacityTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
