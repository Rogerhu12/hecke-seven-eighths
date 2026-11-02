import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroUniformEstimate

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: uniform first-zero estimate

Use the original powerful diagonal, full common-support dictionary and
prime-support budget to control the actual first zero transform. The
finite original seminorms and scalar witness precede every moving call.
This task does not estimate the second zero term or exceptional rows.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem firstZero (c : TargetContext K) (p : SourceParameters c) :
    FirstZeroTask c p := by
  intro frame
  exact FirstZeroProof.uniform_first_zero_certificate c p frame

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.firstZero
