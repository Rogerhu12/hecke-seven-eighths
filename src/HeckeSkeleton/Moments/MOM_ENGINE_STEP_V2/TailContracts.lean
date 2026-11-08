module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T4: both actual Poisson truncation discrepancies

The target is the sum of the two actual norm differences, at the
positive cutoff exponents fixed in the source parameters. In this
proof one chooses sufficient decay and original seminorms before any
moving source. An arbitrary tail majorant is never supplied as data.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

structure TailCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  cost : UniformCost
  bound : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    cost.Ready call input → ∀ trace : SourceTrace call p, trace.Realizes →
      trace.first.normalizedTail + trace.second.normalizedTail ≤
        cost.value input.amplitude call.request.height *
          call.base ^ recipeInductionTerminalLoss c

def TailTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ frame : SourceFrame, Nonempty (TailCertificate c frame p)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
