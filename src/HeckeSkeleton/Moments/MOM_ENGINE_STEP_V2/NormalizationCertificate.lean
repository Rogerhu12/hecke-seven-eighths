module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildInvariantData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.InputDemands

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Internal result of the normalization-task assembly

These records are bookkeeping for the fully proved composition of the
named normalization tasks. No task asserts their existence. In the
final conditional theorem they are constructed from those task proofs,
not supplied as an extra assumption. The two scalar witnesses and the
finite original-input demand precede the moving call.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second}

/-- All conclusions name one and the same assembled family. Its
ordinary source estimate is separate from the original parent estimate
and from all four terminal estimates. -/
structure NormalizationResult (raw : RawFamily geometry)
    (input : ProfileInput call) (arithmeticCost profileCost : UniformCost)
    (degree : ℕ) where
  data : NormalizedData call
  geometry : data.family.OutputGeometry data.labels call.node.data call.node.parameters
    (recipeInductionSigma c) Set.univ call.childWindow call.childOrders
  atoms : data.family.FourierAtomControl data.labels
    degree degree degree degree
  admissible : data.RecursiveAdmissible
  ordinary : raw.normalizedOrdinary ≤ data.sourceBudget
  arithmetic : data.arithmeticMass ≤ arithmeticCost.value input.amplitude call.request.height *
    call.base ^ (recipeInductionEdgeLoss c / 2)
  profile : data.kernelMass ≤ profileCost.value input.amplitude call.request.height *
    call.base ^ (recipeInductionEdgeLoss c / 2) * data.arithmeticMass

/-- A derived certificate, not a blueprint task or a final-theorem
hypothesis. The producer is proved by composing N1--N9 on the exact raw
source supplied by S1--S6. Every readiness condition is a fixed finite
order/scale condition, with no freely selected eligibility predicate. -/
structure NormalizationCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  demand : Finset (ℕ × ℕ) → UniformDemand
  degree : Finset (ℕ × ℕ) → ℕ
  arithmeticCost : Finset (ℕ × ℕ) → UniformCost
  profileCost : Finset (ℕ × ℕ) → UniformCost
  produce : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    (demand call.childOrders).Ready call input →
    (arithmeticCost call.childOrders).Ready call input →
    (profileCost call.childOrders).Ready call input →
    ∀ (trace : SourceTrace call p), trace.Realizes →
    ∀ (geometry : GeometryFamily trace.second), geometry.Realizes →
    ∀ (raw : RawFamily geometry), raw.Realizes →
      Nonempty (NormalizationResult raw input
        (arithmeticCost call.childOrders) (profileCost call.childOrders)
        (degree call.childOrders))

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
