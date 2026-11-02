import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedMassContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! N8b: arithmetic mass of the same canonical refined family. -/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem normalizedMass (c : TargetContext K) (p : SourceParameters c) :
    NormalizedMassTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks
