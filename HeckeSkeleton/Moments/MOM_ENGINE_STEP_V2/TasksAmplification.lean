import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S3: independent source proof task

Paper: Section 4.8, lines 2852--2881. The complete statement and
its original-source data are in PoolContracts. This theorem is the
only admitted obligation in this module; data definitions are concrete.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem amplification (c : TargetContext K) (p : SourceParameters c) :
    AmplificationTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.amplification

