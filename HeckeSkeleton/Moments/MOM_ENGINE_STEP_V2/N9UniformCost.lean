import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.EstimateData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original N5b profile coefficient pays the N9 polynomial cost

The coefficient, orders and threshold remain fixed before the moving
call.  Taking the finite power required by the two complete envelopes
changes only the numerical coefficient and the two degrees.  This is
the last scalar step after the actual N9 kernel estimate; it neither
selects a new family nor assumes an arithmetic mass estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction.Source

namespace UniformCost

/-- The exact fixed power needed to pay the N9 envelope coefficient. -/
def kernelPower (cost : UniformCost) (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient) (degree : ℕ) : UniformCost where
  orders := cost.orders
  coefficient := coefficient * (1 + cost.coefficient) ^ degree
  coefficient_nonneg := mul_nonneg coefficient_nonneg
    (pow_nonneg (by linarith [cost.coefficient_nonneg]) _)
  profileDegree := cost.profileDegree * degree
  heightDegree := cost.heightDegree * (degree : ℝ)
  heightDegree_nonneg := mul_nonneg cost.heightDegree_nonneg (Nat.cast_nonneg _)
  threshold := cost.threshold
  threshold_one_le := cost.threshold_one_le

theorem kernelPower_value (cost : UniformCost) (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient) (degree : ℕ)
    (amplitude height : ℝ) (height_nonneg : 0 ≤ height) :
    (cost.kernelPower coefficient coefficient_nonneg degree).value amplitude height =
      coefficient * (1 + cost.coefficient) ^ degree *
        (amplitude ^ cost.profileDegree * (1 + height) ^ cost.heightDegree) ^ degree := by
  dsimp only [kernelPower, value]
  rw [pow_mul, Real.rpow_mul (by linarith : (0 : ℝ) ≤ 1 + height)]
  simp only [Real.rpow_natCast, mul_pow]
  ring

/-- The original amplitude is at least one.  Consequently the
constant term of the complete envelope is paid by the same monomial. -/
theorem kernelPower_bound (cost : UniformCost) (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient) (degree : ℕ)
    (amplitude height : ℝ) (amplitude_one_le : 1 ≤ amplitude)
    (height_nonneg : 0 ≤ height) {B : ℝ} (B_nonneg : 0 ≤ B)
    (B_le : B ≤ cost.value amplitude height) :
    coefficient * (1 + B) ^ degree ≤
      (cost.kernelPower coefficient coefficient_nonneg degree).value amplitude height := by
  let P : ℝ := amplitude ^ cost.profileDegree * (1 + height) ^ cost.heightDegree
  have P_one : 1 ≤ P := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ amplitude_one_le)
    (Real.one_le_rpow (by linarith) cost.heightDegree_nonneg)
  have value_eq : cost.value amplitude height = cost.coefficient * P := by
    dsimp only [value, P]
    ring
  have hbase : 1 + B ≤ (1 + cost.coefficient) * P := by
    calc
      1 + B ≤ 1 + cost.value amplitude height := add_le_add le_rfl B_le
      _ = 1 + cost.coefficient * P := by rw [value_eq]
      _ ≤ P + cost.coefficient * P := add_le_add P_one le_rfl
      _ = _ := by ring
  calc
    _ ≤ coefficient * ((1 + cost.coefficient) * P) ^ degree :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + B) hbase degree)
        coefficient_nonneg
    _ = _ := by
      rw [kernelPower_value cost coefficient coefficient_nonneg degree
        amplitude height height_nonneg, mul_pow]
      dsimp only [P]
      ring

theorem kernelPower_ready {K : Type} [Field K] [NumberField K]
    {c : TargetContext K} {call : Call c} {input : ProfileInput call}
    {cost : UniformCost} {coefficient : ℝ} {coefficient_nonneg : 0 ≤ coefficient}
    {degree : ℕ}
    (ready : (cost.kernelPower coefficient coefficient_nonneg degree).Ready call input) :
    cost.Ready call input where
  orders := ready.orders
  large := ready.large

end UniformCost

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

/-- Close the uniform scalar part of N9 on the identical normalized
data.  The only supplied mass estimate is the actual analytic N9
estimate itself; no bound for its retained arithmetic sum is needed. -/
theorem kernelMass_le_uniformCost (N : NormalizedData call)
    (input : ProfileInput call) (cost : UniformCost)
    (coefficient : ℝ) (coefficient_nonneg : 0 ≤ coefficient) (degree : ℕ)
    (B loss : ℝ) (B_nonneg : 0 ≤ B)
    (B_le : B ≤ cost.value input.amplitude call.request.height)
    (loss_le : loss ≤ recipeInductionEdgeLoss c / 2)
    (mass : N.kernelMass ≤ coefficient * (1 + B) ^ degree *
      call.base ^ loss * N.arithmeticMass) :
    N.kernelMass ≤
      (cost.kernelPower coefficient coefficient_nonneg degree).value
        input.amplitude call.request.height *
      call.base ^ (recipeInductionEdgeLoss c / 2) * N.arithmeticMass := by
  have arithmetic_nonneg : 0 ≤ N.arithmeticMass := by
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (N.outer_nonneg b.val)
      (N.family.weight_nonneg N.labels N.parentWidth b call.base_pos)
  have coefficient_bound := cost.kernelPower_bound coefficient coefficient_nonneg
    degree input.amplitude call.request.height input.amplitude_one_le
    call.request.height_nonneg B_nonneg B_le
  have paid_nonneg : 0 ≤
      (cost.kernelPower coefficient coefficient_nonneg degree).value
        input.amplitude call.request.height :=
    UniformCost.value_nonneg _ (zero_le_one.trans input.amplitude_one_le)
      call.request.height_nonneg
  calc
    _ ≤ coefficient * (1 + B) ^ degree * call.base ^ loss * N.arithmeticMass := mass
    _ ≤ (cost.kernelPower coefficient coefficient_nonneg degree).value
          input.amplitude call.request.height * call.base ^ loss * N.arithmeticMass :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right coefficient_bound
          (Real.rpow_nonneg call.base_pos.le _)) arithmetic_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le loss_le) paid_nonneg)
      arithmetic_nonneg

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformCost.kernelPower_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.kernelMass_le_uniformCost
