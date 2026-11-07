module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4OriginalCapacity
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4UniformCapacity

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: original sixth-pattern geometry, windows and complete source budgets

This task consumes the exact primitive N3 identities on the canonical
N2 source family. The original S5 packet supplies all geometric facts.
No completed capacity, support budget, normalized child or mass estimate
is an input. The output retains the same fixed original pattern.
One additional fixed-frame demand makes the actual raw scale error
equal to p.loss on every member of this same original family.

Paper: Section 4.8, lines 2883--2946.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem originalCapacityTask (c : TargetContext K) (p : SourceParameters c) :
    OriginalCapacityTask c p := by
  intro call input packet hpacket seed support calibrations pattern bindings
  refine ⟨N4.originalCapacityCertificate seed support calibrations pattern bindings hpacket, ?_⟩
  exact N4.originalCapacityCertificate_pattern seed support calibrations pattern bindings hpacket

/-- The demand is fixed before the call, its original source and its
finite labels. The returned certificate has the same geometry and
pattern as the unrestricted construction, with the exact small error. -/
theorem originalCapacityTask_uniform (c : TargetContext K) (p : SourceParameters c) :
    UniformOriginalCapacityTask c p := by
  intro frame
  refine ⟨N4.annulusDemand p frame, ?_⟩
  intro call input hframe ready packet hpacket seed support calibrations pattern bindings
  let certificate :=
    N4.originalCapacityCertificate seed support calibrations pattern bindings hpacket
  refine ⟨certificate, ?_, ?_⟩
  · exact N4.originalCapacityCertificate_pattern seed support calibrations pattern bindings hpacket
  · exact N4.certificate_rawScaleError_eq hpacket seed frame input hframe ready
      support calibrations certificate

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.originalCapacityTask
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.originalCapacityTask_uniform
