import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildInvariantData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementAssembly

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N7a: arithmetic invariants of the same retained, frozen children

The raw calibration's allowed rows are exactly its physical row image,
and its genuine moving recipe carries both support and joint budgets.
The task transports those fields through clipping, normalization,
whole-slot restriction and freezing. It also proves the ordinary
reflection arithmetic primitive, including non-norm-twist exclusion.
No scheduled profile estimate or child energy bound is requested here.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {input : ProfileInput call} {packet : RawLeafPacket call p}
variable {O : OrdinaryData packet} {R : RefinementData O input}

def RefinementData.Calibrations.SourceConditions (C : R.Calibrations) : Prop :=
  ∀ side a rectangle, (C.side side a rectangle).SourceConditions

/-- N7a applies to the actual family assembled from the displayed
calibrations and capacities. The source conditions concern those same
calibrations; an arbitrary normalized family is never supplied. -/
def ChildArithmeticTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (input : ProfileInput call)
    (trace : SourceTrace call p), trace.Realizes →
    ∀ (geometry : GeometryFamily trace.second), geometry.Realizes →
    ∀ (raw : RawFamily geometry), raw.Realizes →
    ∀ (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
      (R : ∀ j, RefinementData (O j) input)
      (C : ∀ j, (R j).Calibrations) (G : ∀ j, (C j).Capacities),
      (∀ j, (C j).SourceConditions) →
      (Assembly.refinedNormalizedData raw O R C G).ArithmeticInvariant

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
