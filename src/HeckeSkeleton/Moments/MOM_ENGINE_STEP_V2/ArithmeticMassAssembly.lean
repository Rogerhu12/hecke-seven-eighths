import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceIndexContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8a and N8b pay one actual arithmetic mass

The source-index coefficient and threshold are included in the cost
before U1 prepares any moving call. The two scale exponents then cancel
exactly; no second index sum or pool-density factor is introduced.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {p : SourceParameters c}
variable {loss : ℝ}

namespace Blueprint.SourceIndexCertificate

def combinedCost (index : SourceIndexCertificate c frame p loss)
    (cost : UniformCost) : UniformCost where
  orders := cost.orders
  coefficient := index.coefficient * cost.coefficient
  coefficient_nonneg := mul_nonneg index.coefficient_nonneg cost.coefficient_nonneg
  profileDegree := cost.profileDegree
  heightDegree := cost.heightDegree
  heightDegree_nonneg := cost.heightDegree_nonneg
  threshold := max index.threshold cost.threshold
  threshold_one_le := index.threshold_one.trans (le_max_left _ _)

theorem combinedCost_value (index : SourceIndexCertificate c frame p loss)
    (cost : UniformCost) (amplitude height : ℝ) :
    (index.combinedCost cost).value amplitude height =
      index.coefficient * cost.value amplitude height := by
  unfold combinedCost UniformCost.value
  ring

theorem ready_original {index : SourceIndexCertificate c frame p loss}
    {cost : UniformCost} {call : Call c} {input : ProfileInput call}
    (ready : (index.combinedCost cost).Ready call input) : cost.Ready call input where
  orders := ready.orders
  large := (le_max_right _ _).trans ready.large

theorem ready_index {index : SourceIndexCertificate c frame p loss}
    {cost : UniformCost} {call : Call c} {input : ProfileInput call}
    (ready : (index.combinedCost cost).Ready call input) : index.threshold ≤ call.base :=
  (le_max_left _ _).trans ready.large

end Blueprint.SourceIndexCertificate

namespace Assembly

theorem arithmeticMass_of_sourceIndex
    (index : SourceIndexCertificate c frame p loss) (cost : UniformCost)
    (call : Call c) (input : ProfileInput call) (hframe : call.frame = frame)
    (ready : (index.combinedCost cost).Ready call input)
    (trace : SourceTrace call p) (htrace : trace.Realizes)
    (geometry : GeometryFamily trace.second) (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes) (N : NormalizedData call)
    (reduction : N.arithmeticMass ≤ cost.value input.amplitude call.request.height *
      call.base ^ (recipeInductionEdgeLoss c / 2 - loss - p.loss) * raw.indexMass) :
    N.arithmeticMass ≤ (index.combinedCost cost).value
      input.amplitude call.request.height * call.base ^ (recipeInductionEdgeLoss c / 2) := by
  have hc : 0 ≤ cost.value input.amplitude call.request.height :=
    cost.value_nonneg (zero_le_one.trans input.amplitude_one_le)
      call.request.height_nonneg
  have hi := index.bound call input hframe
    (SourceIndexCertificate.ready_index ready) trace htrace geometry hgeometry raw hraw
  have hp : call.base ^ (recipeInductionEdgeLoss c / 2 - loss - p.loss) *
      call.base ^ (loss + p.loss) = call.base ^ (recipeInductionEdgeLoss c / 2) := by
    rw [← Real.rpow_add call.base_pos]
    congr 1
    ring
  calc
    _ ≤ cost.value input.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2 - loss - p.loss) * raw.indexMass := reduction
    _ ≤ cost.value input.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2 - loss - p.loss) *
          (index.coefficient * call.base ^ (loss + p.loss)) :=
      mul_le_mul_of_nonneg_left hi
        (mul_nonneg hc (Real.rpow_nonneg call.base_pos.le _))
    _ = (index.coefficient * cost.value input.amplitude call.request.height) *
        (call.base ^ (recipeInductionEdgeLoss c / 2 - loss - p.loss) *
          call.base ^ (loss + p.loss)) := by ring
    _ = _ := by rw [hp, SourceIndexCertificate.combinedCost_value]

end Assembly
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.arithmeticMass_of_sourceIndex
