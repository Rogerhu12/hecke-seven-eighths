import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ExceptionalSummationContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Summation of the same exceptional leaves with the N8a index

This is the final scalar step of T3b.  A bound for each original leaf
is summed using the original `RawFamily.indexMass` and the original
parent normalizer.  The arithmetic index coefficient and threshold are
incorporated into the same uniform cost.  The whole-centered analytic
leaf estimate remains an explicit argument of this assembly lemma.
-/

noncomputable section
open scoped BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {p : SourceParameters c}
variable {frame : SourceFrame} {loss : ℝ}

def indexedCost (cost : UniformCost)
    (index : SourceIndexCertificate c frame p loss) : UniformCost where
  orders := cost.orders
  coefficient := cost.coefficient * index.coefficient
  coefficient_nonneg := mul_nonneg cost.coefficient_nonneg index.coefficient_nonneg
  profileDegree := cost.profileDegree
  heightDegree := cost.heightDegree
  heightDegree_nonneg := cost.heightDegree_nonneg
  threshold := max cost.threshold index.threshold
  threshold_one_le := cost.threshold_one_le.trans (le_max_left _ _)

theorem indexedCost_value (cost : UniformCost)
    (index : SourceIndexCertificate c frame p loss) (amplitude height : ℝ) :
    (indexedCost cost index).value amplitude height =
      cost.value amplitude height * index.coefficient := by
  simp only [indexedCost, UniformCost.value]
  ring

theorem indexedCost_ready {cost : UniformCost}
    {index : SourceIndexCertificate c frame p loss}
    {call : Call c} {input : ProfileInput call}
    (ready : (indexedCost cost index).Ready call input) : cost.Ready call input where
  orders := ready.orders
  large := (le_max_left _ _).trans ready.large

theorem indexedCost_threshold {cost : UniformCost}
    {index : SourceIndexCertificate c frame p loss}
    {call : Call c} {input : ProfileInput call}
    (ready : (indexedCost cost index).Ready call input) : index.threshold ≤ call.base :=
  (le_max_right _ _).trans ready.large

theorem normalizedExceptional_eq_sum {call : Call c}
    {F : FirstPresentation call p} {family : FirstCauchyFamily F}
    {expansion : PoolExpansion family} {second : SecondFamily expansion}
    {geometry : GeometryFamily second} (raw : RawFamily geometry) :
    raw.normalizedExceptional =
      ∑ j, call.normalizedScalar (raw.packet j).leaf.exceptionalCost := by
  simp only [RawFamily.normalizedExceptional, RawFamily.exceptional,
    Call.normalizedScalar, Finset.sum_div]

/-- The finite sum pays exactly the same N8a mass.  No leaf, divisor,
pool density, or normalization is chosen again. -/
theorem sum_original_exceptional_le
    (cost : UniformCost) (index : SourceIndexCertificate c frame p loss)
    (call : Call c) (input : ProfileInput call) (hframe : call.frame = frame)
    (ready : (indexedCost cost index).Ready call input)
    (trace : SourceTrace call p) (htrace : trace.Realizes)
    (geometry : GeometryFamily trace.second) (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes)
    (hleaf : ∀ j,
      call.normalizedScalar (raw.packet j).leaf.exceptionalCost ≤
        cost.value input.amplitude call.request.height * raw.indexWeight j *
          call.base ^ (recipeInductionTerminalLoss c - loss - p.loss)) :
    raw.normalizedExceptional ≤
      (indexedCost cost index).value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c := by
  have hcost : 0 ≤ cost.value input.amplitude call.request.height :=
    cost.value_nonneg (zero_le_one.trans input.amplitude_one_le)
      call.request.height_nonneg
  have hmass := index.bound call input hframe (indexedCost_threshold ready)
    trace htrace geometry hgeometry raw hraw
  have hpowers : call.base ^ (loss + p.loss) *
      call.base ^ (recipeInductionTerminalLoss c - loss - p.loss) =
        call.base ^ recipeInductionTerminalLoss c := by
    rw [← Real.rpow_add call.base_pos]
    congr 1
    ring
  calc
    raw.normalizedExceptional =
        ∑ j, call.normalizedScalar (raw.packet j).leaf.exceptionalCost :=
      normalizedExceptional_eq_sum raw
    _ ≤ ∑ j, cost.value input.amplitude call.request.height * raw.indexWeight j *
        call.base ^ (recipeInductionTerminalLoss c - loss - p.loss) :=
      Finset.sum_le_sum (fun j _ => hleaf j)
    _ = cost.value input.amplitude call.request.height * raw.indexMass *
        call.base ^ (recipeInductionTerminalLoss c - loss - p.loss) := by
      simp only [RawFamily.indexMass, Finset.mul_sum, Finset.sum_mul]
    _ ≤ cost.value input.amplitude call.request.height *
        (index.coefficient * call.base ^ (loss + p.loss)) *
          call.base ^ (recipeInductionTerminalLoss c - loss - p.loss) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hcost)
        (Real.rpow_nonneg call.base_pos.le _)
    _ = (cost.value input.amplitude call.request.height * index.coefficient) *
        (call.base ^ (loss + p.loss) *
          call.base ^ (recipeInductionTerminalLoss c - loss - p.loss)) := by ring
    _ = (indexedCost cost index).value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c := by
      rw [hpowers, indexedCost_value]

/-- The analytic leaf bound and the already supplied N8a certificate
produce the precise existing exceptional uniform certificate. -/
def exceptionalCertificate_of_original_leaves
    (cost : UniformCost) (index : SourceIndexCertificate c frame p loss)
    (hleaf : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      cost.Ready call input → ∀ trace : SourceTrace call p, trace.Realizes →
      ∀ geometry : GeometryFamily trace.second, geometry.Realizes →
      ∀ raw : RawFamily geometry, raw.Realizes → ∀ j,
        call.normalizedScalar (raw.packet j).leaf.exceptionalCost ≤
          cost.value input.amplitude call.request.height * raw.indexWeight j *
            call.base ^ (recipeInductionTerminalLoss c - loss - p.loss)) :
    ExceptionalCertificate c frame p where
  cost := indexedCost cost index
  bound call input hframe ready trace htrace geometry hgeometry raw hraw :=
    sum_original_exceptional_le cost index call input hframe ready
      trace htrace geometry hgeometry raw hraw
      (hleaf call input hframe (indexedCost_ready ready)
        trace htrace geometry hgeometry raw hraw)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.sum_original_exceptional_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exceptionalCertificate_of_original_leaves
