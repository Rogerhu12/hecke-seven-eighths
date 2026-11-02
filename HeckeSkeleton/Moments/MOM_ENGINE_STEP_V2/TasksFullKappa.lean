import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FullKappaContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! N6: fixed original analytic choices and full-kappa normalization of the same side. -/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem fullKappaNormalization (c : TargetContext K) :
    FullKappaTask c := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks
