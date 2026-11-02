import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4OriginalCapacity

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: original sixth-pattern geometry, windows and complete source budgets

This task consumes the exact primitive N3 identities on the canonical
N2 source family. The original S5 packet supplies all geometric facts.
No completed capacity, support budget, normalized child or mass estimate
is an input. The output retains the same fixed original pattern.

Paper: Section 4.8, lines 2883--2946.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

def OriginalCapacityTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (input : ProfileInput call) (packet : RawLeafPacket call p),
    packet.Realizes → ∀ (seed : OrdinarySeed packet)
      (support : seed.ordinary.PassiveSupport input)
      (calibrations : (seed.refinement input support).Calibrations)
      (pattern : Fin packet.block.primeCount → Bool),
    (∀ side a rectangle, N4.CalibrationBinding seed support side a rectangle
      (calibrations.side side a rectangle) pattern) →
    ∃ certificate : OriginalCapacityCertificate seed support calibrations,
      ∀ side a rectangle, (certificate.geometry side a rectangle).pattern = pattern

theorem originalCapacityTask (c : TargetContext K) (p : SourceParameters c) :
    OriginalCapacityTask c p := by
  intro call input packet hpacket seed support calibrations pattern bindings
  refine ⟨N4.originalCapacityCertificate seed support calibrations pattern bindings hpacket, ?_⟩
  exact N4.originalCapacityCertificate_pattern seed support calibrations pattern bindings hpacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.originalCapacityTask
