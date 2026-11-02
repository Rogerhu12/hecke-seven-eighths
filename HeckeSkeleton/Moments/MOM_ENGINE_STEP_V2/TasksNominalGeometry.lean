import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.GeometryContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S5: independent source proof task

Paper: Section 4.8, lines 2895--2906. The complete statement and
its original-source data are in GeometryContracts. This theorem is the
only admitted obligation in this module; data definitions are concrete.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem nominalGeometry (c : TargetContext K) (p : SourceParameters c) :
    NominalGeometryTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.nominalGeometry

