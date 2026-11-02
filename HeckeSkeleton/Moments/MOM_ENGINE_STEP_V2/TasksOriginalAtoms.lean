import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem originalAtoms (c : TargetContext K) (p : SourceParameters c) :
    OriginalAtomTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks
