import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryFromAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryRawAtomFormula

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem originalAtoms (c : TargetContext K) (p : SourceParameters c) :
    OriginalAtomTask c p := by
  intro call packet hpacket
  obtain ⟨phases⟩ := OrdinaryPhaseFacts.ordinaryPhaseData packet hpacket
  exact ⟨packet.atomSeed hpacket phases
    (packet.beforeAtomTable_left hpacket phases) (packet.beforeAtomTable_right hpacket phases)⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.originalAtoms

