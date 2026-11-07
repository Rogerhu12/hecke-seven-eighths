module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T3: exceptional rows of the original whole source

The exceptional indicator is the actual row character's membership
in the unchanged parent theta set. Its moving factors, sixth-unit
sector and both occurrence allocations are fixed by the raw carrier.
This task never estimates an arbitrarily selected row predicate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

structure ExceptionalCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  cost : UniformCost
  bound : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    cost.Ready call input → ∀ trace : SourceTrace call p, trace.Realizes →
    ∀ geometry : GeometryFamily trace.second, geometry.Realizes →
    ∀ raw : RawFamily geometry, raw.Realizes →
      raw.normalizedExceptional ≤ cost.value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c

def ExceptionalTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ frame : SourceFrame, Nonempty (ExceptionalCertificate c frame p)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
