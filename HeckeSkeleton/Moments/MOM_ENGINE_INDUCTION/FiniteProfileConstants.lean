import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedProfileControl

/-!
# Common constants for the finitely many actual analytic orders

Each strict or reflected call is instantiated at its requested rank's
Euler order before the moving height. Its scalar, height degree and
threshold are then dominated by one finite bound over those ranks.
The comparison below is only of these explicit numerical envelopes;
it contains no parent moment or child estimate as an input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open scoped BigOperators

/-- This finite scalar can be used for coefficients, height degrees or
scale thresholds. It is selected before the moving height and scale. -/
def finiteStageBound (depth : ℕ) (values : ℕ → ℝ) : ℝ :=
  2 + ∑ j ∈ Finset.range (depth + 1), |values j|

theorem finiteStageBound_two_le (depth : ℕ) (values : ℕ → ℝ) :
    2 ≤ finiteStageBound depth values := by
  have hs : 0 ≤ ∑ j ∈ Finset.range (depth + 1), |values j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (values j))
  unfold finiteStageBound
  linarith

theorem finiteStageBound_pos (depth : ℕ) (values : ℕ → ℝ) :
    0 < finiteStageBound depth values :=
  (by norm_num : (0 : ℝ) < 2).trans_le (finiteStageBound_two_le depth values)

theorem le_finiteStageBound (depth : ℕ) (values : ℕ → ℝ)
    {j : ℕ} (hj : j ≤ depth) : values j ≤ finiteStageBound depth values := by
  have hs : |values j| ≤ ∑ k ∈ Finset.range (depth + 1), |values k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (values k))
      (Finset.mem_range.mpr (by omega))
  unfold finiteStageBound
  linarith [le_abs_self (values j)]

/-- In particular, the common threshold covers every actual call. -/
theorem finiteStageBound_threshold (depth : ℕ) (thresholds : ℕ → ℝ)
    {j : ℕ} {U : ℝ} (hj : j ≤ depth) (hU : finiteStageBound depth thresholds ≤ U) :
    thresholds j ≤ U := (le_finiteStageBound depth thresholds hj).trans hU

/-- Uniformize the actual coefficients and height exponents after all
finite orders have been selected. No maximum depends on the height. -/
theorem finiteStageBound_height_envelope (depth : ℕ)
    (coefficients degrees : ℕ → ℝ) {j : ℕ} {T : ℝ}
    (hj : j ≤ depth) (hT : 0 ≤ T) :
    coefficients j * (1 + T) ^ degrees j ≤
      finiteStageBound depth coefficients * (1 + T) ^ finiteStageBound depth degrees := by
  exact mul_le_mul (le_finiteStageBound depth coefficients hj)
    (Real.rpow_le_rpow_of_exponent_le (by linarith)
      (le_finiteStageBound depth degrees hj))
    (Real.rpow_nonneg (by linarith) _) (finiteStageBound_pos depth coefficients).le

/-- The common positive scale factor leaves that exact envelope
comparison unchanged, so the actual terminal/mass exponents survive. -/
theorem finiteStageBound_height_scale_envelope (depth : ℕ)
    (coefficients degrees : ℕ → ℝ) {j : ℕ} {T U exponent : ℝ}
    (hj : j ≤ depth) (hT : 0 ≤ T) (hU : 0 ≤ U) :
    coefficients j * (1 + T) ^ degrees j * U ^ exponent ≤
      finiteStageBound depth coefficients * (1 + T) ^ finiteStageBound depth degrees *
        U ^ exponent :=
  mul_le_mul_of_nonneg_right
    (finiteStageBound_height_envelope depth coefficients degrees hj hT)
    (Real.rpow_nonneg hU exponent)

end HeckeSkeleton.Moments.EngineInduction
