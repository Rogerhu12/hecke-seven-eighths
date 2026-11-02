import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T4: uniform bounds for both original truncation discrepancies

Pay the first and second physical finite-source degrees by choosing
decay with `physicalDegree + (1 - decay) * cutoffExponent` below the
required saving. Use the two actual cutoffs and the same first Fourier
measure. The first common product remains whole before its truncation.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem tails (c : TargetContext K) (p : SourceParameters c) :
    TailTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.tails
