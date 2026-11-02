import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S2: independent source proof task

Paper: Section 4.8, lines 2827--2850. The complete statement and
its original-source data are in FirstCauchyContracts. This theorem is the
only admitted obligation in this module; data definitions are concrete.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem firstAllowance (c : TargetContext K) (p : SourceParameters c) :
    FirstAllowanceTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.firstAllowance

