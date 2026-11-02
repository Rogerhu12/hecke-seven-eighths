import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceIndexContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8a proof task: source arithmetic index and physical fibres

Future proof budget: 3000--4000 lines. First map the same raw common,
divisor and full-allocation labels to the base arithmetic carrier;
then pay only its original physical fibres and the one pool.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem sourceIndex (c : TargetContext K) (p : SourceParameters c) :
    SourceIndexTask c p := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.sourceIndex
