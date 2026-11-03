import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N6FullKappaConstruction

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N6: fixed analytic choices construct the same full-kappa normalization

The proof selects original analytic and contour constants before the
call, then constructs each side from its original calibration, geometry
and raw/clipped profile windows. Paper: 2927--2946 and 3043--3073.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem fullKappaNormalization (c : TargetContext K) : FullKappaTask c := by
  intro loss hloss
  let choices := N6.analyticChoices c loss hloss
  refine ⟨choices, ?_⟩
  intro call H Row ι finite decidable k R side s D G conditions B J₁ J₂ windows
  exact ⟨N6.sideResult choices G conditions windows⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.fullKappaNormalization
