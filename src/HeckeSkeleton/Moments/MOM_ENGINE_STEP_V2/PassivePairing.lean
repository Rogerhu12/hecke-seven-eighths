module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two residual expansions under the original ordinary integrand

The two comparison bits and the two independent passive allocations
are summed exactly once. This final finite calculation uses the
single-side estimates proved from the original coefficient expansion;
its denominator and outer weight remain those of the original leaf.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField
open HeckeGeneral.Analysis.ConditionalMoments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable {O : OrdinaryData packet}

namespace OrdinaryData

def rectangleEnergy (O : OrdinaryData packet) (side rectangle : Bool)
    (ξ : EngineParameter) : ℝ :=
  if side then (O.rightFrame rectangle).energy ξ
  else (O.leftFrame rectangle).energy ξ

theorem ordinary_le_sum_rectangles (O : OrdinaryData packet) (z : ℝ × ℝ) :
    packet.leaf.ordinaryIntegrand z ≤
      ∑ r : Bool, ∑ s : Bool,
        Real.sqrt (O.rectangleEnergy false r (WithLp.toLp 2 z)) *
          Real.sqrt (O.rectangleEnergy true s (WithLp.toLp 2 z)) := by
  have hbool (L R : Bool → ℝ) :
      (∑ r : Bool, ∑ s : Bool, L r * R s) =
        L false * R false + L false * R true +
          L true * R false + L true * R true := by
    simp only [Fintype.sum_bool]
    ring
  have hbinding : packet.leaf.ordinaryIntegrand z =
      O.rectangles.originalIntegrand (WithLp.toLp 2 z) :=
    O.binding.ordinaryIntegrand_eq z
  rw [hbinding]
  change O.rectangles.originalIntegrand (WithLp.toLp 2 z) ≤
    ∑ r : Bool, ∑ s : Bool,
      Real.sqrt ((O.leftFrame r).energy (WithLp.toLp 2 z)) *
        Real.sqrt ((O.rightFrame s).energy (WithLp.toLp 2 z))
  exact (O.rectangles.ordinary_le_rectangles
    (Arithmetic.context c) (WithLp.toLp 2 z)).trans_eq
      (hbool (fun r => Real.sqrt ((O.leftFrame r).energy (WithLp.toLp 2 z)))
        (fun s => Real.sqrt ((O.rightFrame s).energy (WithLp.toLp 2 z)))).symm

end OrdinaryData

namespace RefinementData

variable (R : RefinementData O input)

def sideRoot (side : Bool) (a : R.support.labels side) (rectangle : Bool)
    (ξ : EngineParameter) : ℝ :=
  Real.sqrt (‖R.normalizer side a rectangle‖ ^ 2 *
    (R.source side a rectangle).energy (σ := Arithmetic.embedding c) ξ)

def sideSum (side rectangle : Bool) (ξ : EngineParameter) : ℝ :=
  ∑ a : R.support.labels side, ‖PassiveAllocation.sign a.val‖ *
    R.sideRoot side a rectangle ξ

theorem sideSum_nonneg (side rectangle : Bool) (ξ : EngineParameter) :
    0 ≤ R.sideSum side rectangle ξ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem ordinary_le_sideSums
    (bound : ∀ side rectangle ξ,
      Real.sqrt (O.rectangleEnergy side rectangle ξ) ≤ R.sideSum side rectangle ξ)
    (z : ℝ × ℝ) :
    packet.leaf.ordinaryIntegrand z ≤
      ∑ r : Bool, ∑ s : Bool,
        R.sideSum false r (WithLp.toLp 2 z) * R.sideSum true s (WithLp.toLp 2 z) := by
  refine (O.ordinary_le_sum_rectangles z).trans ?_
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul (bound false r _) (bound true s _)
    (Real.sqrt_nonneg _) (R.sideSum_nonneg false r _)

/-- This is the exact finite label identity, including all four
rectangles. Neither a label cardinality nor an extra common scalar is
introduced when the two side bounds are multiplied. -/
theorem sum_sourcePairs (ξ : EngineParameter) :
    (∑ b : R.Label, R.outer b * R.sourcePair b ξ) =
      packet.leaf.weight *
        (∑ r : Bool, ∑ s : Bool, R.sideSum false r ξ * R.sideSum true s ξ) /
          call.base ^ (call.node.parameters.m + call.node.parameters.q) := by
  unfold outer OrdinaryData.PassiveSupport.outer sourcePair
  unfold leftNormalizer rightNormalizer leftSource rightSource
  simp only [Label, OrdinaryData.PassiveSupport.Label, Fintype.sum_prod_type]
  simp only [sideSum, sideRoot, Finset.sum_mul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext r
    arg 2
    ext a
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The pointwise conclusion consumed by the existing refinement
assembly is derived from the genuine single-side residual estimates. -/
theorem ordinary_pointwise_of_sideBounds
    (bound : ∀ side rectangle ξ,
      Real.sqrt (O.rectangleEnergy side rectangle ξ) ≤ R.sideSum side rectangle ξ)
    (z : ℝ × ℝ) :
    packet.leaf.weight * packet.leaf.ordinaryIntegrand z /
        call.base ^ (call.node.parameters.m + call.node.parameters.q) ≤
      ∑ b : R.Label, R.outer b * R.sourcePair b (WithLp.toLp 2 z) := by
  rw [R.sum_sourcePairs]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (R.ordinary_le_sideSums bound z)
      packet.leaf.weight_nonneg)
    (Real.rpow_nonneg call.base_pos.le _)

end RefinementData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RefinementData.sum_sourcePairs
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RefinementData.ordinary_pointwise_of_sideBounds
