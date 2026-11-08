module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveBounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

/-- N2: residual mask expansion on the actual restored smooth carrier. -/
theorem passive_refinement (c : TargetContext K) (p : SourceParameters c) :
    PassiveRefinementTask c p := by
  intro call input packet hpacket seed
  exact ⟨seed.canonicalSupport input, seed.canonicalSupport_spec input,
    seed.residualMaskIdentity hpacket, seed.canonicalRefinement_bound input hpacket⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.passive_refinement
