import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S6: independent source proof task

Paper: Section 4.8, lines 2908--2925. The complete statement and
its original-source data are in RawContracts. This theorem is the
only admitted obligation in this module; data definitions are concrete.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem finiteLeaves (c : TargetContext K) (p : SourceParameters c) :
    FiniteLeafTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.finiteLeaves

