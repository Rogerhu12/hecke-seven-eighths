import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

/-- N2: residual mask expansion on the actual restored smooth carrier. -/
theorem passive_refinement (c : TargetContext K) (p : SourceParameters c) :
    PassiveRefinementTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks
