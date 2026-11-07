module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S1SourceConstruction
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S1ExactBound

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S1: independent source proof task

Paper: Section 4.8, lines 2800--2828. The actual original source is
constructed from its whole centered coefficient and joint row budget.
The exact discrepancy at the physical divisor cutoffs is retained.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem firstTransform (c : TargetContext K) (p : SourceParameters c) :
    FirstTransformTask c p := by
  intro call active
  let F := S1.presentation call p
  refine ⟨F, S1.presentation_realizes call p active, ?_⟩
  intro N
  have h := S1ExactBound.pairedStageEnergy_le F.source N
  rw [S1.energy_eq call] at h
  exact h

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.firstTransform

