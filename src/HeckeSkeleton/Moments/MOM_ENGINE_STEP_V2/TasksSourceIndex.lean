import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceIndexProof

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8a proof task: source arithmetic index and physical fibres

The same raw common, divisor and full-allocation labels are summed
through their original source dictionaries.  The second common sum
retains the first-divisor density, the physical fibres have their
proved uniform subpower cost, and the one pool is paid exactly once.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem sourceIndex (c : TargetContext K) (p : SourceParameters c) :
    SourceIndexTask c p := by
  exact N8Source.sourceIndexTask c p

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.sourceIndex

