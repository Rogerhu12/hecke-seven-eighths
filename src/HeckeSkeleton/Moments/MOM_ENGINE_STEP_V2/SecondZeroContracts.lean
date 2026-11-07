module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T2: the second zero term after the same first Fourier measure

The first source, its exact Cauchy family, its one pool expansion and
the second transforms are all retained. The physical windows are the
intermediate conclusions of S2 and S3, rather than facts reproved by
this terminal task. The cost contains the actual second orbital fibre.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

structure SecondZeroCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  cost : UniformCost
  bound : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    cost.Ready call input → ∀ trace : SourceTrace call p, trace.Realizes →
      trace.second.normalizedZero ≤ cost.value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c

def SecondZeroTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ frame : SourceFrame, Nonempty (SecondZeroCertificate c frame p)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
