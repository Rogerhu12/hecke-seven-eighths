module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2FirstFamilyCost
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2FirstColumnWindows
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2FirstRetainedWindow

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S2: independent source proof task

Paper: Section 4.8, lines 2827--2850. One fixed annulus demand gives
the actual column windows. The finite family retains each independent
divisor and both Cauchy sides exactly once, with its original cost.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

theorem firstAllowance (c : TargetContext K) (p : SourceParameters c) :
    FirstAllowanceTask c p := by
  intro frame
  refine ⟨S2.columnDemand c p frame, ?_⟩
  intro call input hframe ready F hF
  refine ⟨S2.family F, S2.family_realizes F, S2.family_cost F, ?_⟩
  intro i
  let key : FirstCauchyKey F := (S2.family F).index i
  let N := S2.normalization F
  change (S2.source key N).Windows
  refine {
    retained_upper := ?_
    column_lower := ?_
    column_upper := ?_
    row_upper := ?_ }
  · intro hne
    apply S2.source_retained_upper hF _ key N hne
    intro j hj hcoeff
    exact (S2.source_full_column_window input hframe ready F hF j hj hcoeff).2
  · intro j hj hcoeff
    simpa only [S2.source, S2.coordinates, EngineStep.OriginalNominalTag.removedLength,
      sub_zero] using
      (S2.source_column_window input hframe ready F hF key N j hj hcoeff).1
  · intro j hj hcoeff
    simpa only [S2.source, S2.coordinates, EngineStep.OriginalNominalTag.removedLength,
      sub_zero] using
      (S2.source_column_window input hframe ready F hF key N j hj hcoeff).2
  · intro h hh
    exact S2.source_row_upper hF key N h hh

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.firstAllowance

