import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aRecovery

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T3a: original theta sectors and sixth-power frequency recovery

Use the original finite theta catalogue, its exterior unramifiedness,
the complete frequency reconstruction and the original nonzero frozen
mask. Apply the proved Kummer character laws, actual orbit fibre count
and `exceptional_frequency_base_fourth_power` to the same rows.
The source bridge uses the original rectangular atom formulas before
centering; no volume estimate is part of this arithmetic task.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem exceptional_recovery (c : TargetContext K) (p : SourceParameters c) :
    ExceptionalRecoveryTask c p :=
  fun _ packet hpacket => packet.exceptional_recovery_of_realizes hpacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.exceptional_recovery
