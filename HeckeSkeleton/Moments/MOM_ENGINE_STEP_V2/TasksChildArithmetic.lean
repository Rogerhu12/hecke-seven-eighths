import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildArithmeticContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N7aChildSource

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N7a: both complete-source budgets and reflection arithmetic

Paper: Section 4.8, the child construction after the two allocations
and the original-source compatibility conditions. Use the actual
complete moving recipe, physical allowed-row image, fixed parent theta,
unchanged plain background and same capacity child. Both the displayed
support budget and joint row/full-mask budget must remain explicit.
The base moving-recipe and canonical-theta theorems perform the exact
transports. This proof identifies their children with the displayed
dependent family, retaining its actual labels and capacity choices.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem child_arithmetic (c : TargetContext K) (p : SourceParameters c) :
    ChildArithmeticTask c p := by
  intro call input trace _ geometry _ raw _ O R C G conditions
  intro side b ξ
  cases side with
  | false =>
      exact N7a.frozenChildArithmetic
        ((C b.val.1).side false b.val.2.1 b.val.2.2.2.1)
        (conditions b.val.1 false b.val.2.1 b.val.2.2.2.1)
        ((Assembly.refinedNormalizedData raw O R C G).family.leftChild
          (Assembly.refinedNormalizedData raw O R C G).labels b) ξ
  | true =>
      exact N7a.frozenChildArithmetic
        ((C b.val.1).side true b.val.2.2.1 b.val.2.2.2.2)
        (conditions b.val.1 true b.val.2.2.1 b.val.2.2.2.2)
        ((Assembly.refinedNormalizedData raw O R C G).family.rightChild
          (Assembly.refinedNormalizedData raw O R C G).labels b) ξ

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.child_arithmetic

