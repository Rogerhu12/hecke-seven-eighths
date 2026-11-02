import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S4: independent source proof task

Paper: Section 4.8, lines 2883--2894 and 3004--3010. The complete statement and
its original-source data are in SecondContracts. This theorem is the
only admitted obligation in this module; data definitions are concrete.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem secondTransform (c : TargetContext K) (p : SourceParameters c) :
    SecondTransformTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.secondTransform

