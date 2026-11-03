import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedMassProof

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8b proof task: unchanged normalized labels and original arithmetic index

The canonical original source, normalizers, calibrations and N6
capacities are retained. Whole-slot costs and all finite labels are
paid from their original atoms and source dictionaries. The fixed
index loss is p.loss on the same indexMass consumed by N8a.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem normalizedMass (c : TargetContext K) (p : SourceParameters c) :
    NormalizedMassTask c p :=
  N8Normalized.normalizedMassTask c p

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.normalizedMass
