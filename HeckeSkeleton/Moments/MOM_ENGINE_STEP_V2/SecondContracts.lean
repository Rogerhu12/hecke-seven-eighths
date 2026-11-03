import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S4: second Poisson on the full nonprimitive common correlation

The source and all three terms retain their original full physical
cutoff. No artificial coprime extension, ordinary rectangle triangle,
capacity deletion or normalized child occurs in this task.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

def SecondTransformTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (F : FirstPresentation call p), F.Realizes →
    ∀ family : FirstCauchyFamily F, family.Realizes →
    ∀ expansion : PoolExpansion family, expansion.Realizes →
    (∀ i, (expansion.source i).Windows) →
    ∃ second : SecondFamily expansion, second.Realizes ∧
      expansion.cost ≤ second.zero + second.tail + second.nonzero

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
