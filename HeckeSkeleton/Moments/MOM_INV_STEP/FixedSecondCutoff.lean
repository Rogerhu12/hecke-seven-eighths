module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FixedDyadicCutoff

/-!
# One fixed logarithmic cutoff for the actual second parent tests

The first complete Mellin family has support in [1/8,21/8]. Its
inverse-square-root power test has the same support. This fixed smooth
two-variable logarithmic cutoff equals one on that entire rectangle.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

open scoped Classical ContDiff

def secondLogBound : ℝ := |Real.log (1 / 8 : ℝ)| + |Real.log (21 / 8 : ℝ)|

theorem secondLogBound_nonneg : 0 ≤ secondLogBound := by
  unfold secondLogBound
  positivity

def secondBump : ContDiffBump (0 : LogPlane) where
  rIn := 2 * (secondLogBound + 1)
  rOut := 2 * (secondLogBound + 1) + 1
  rIn_pos := by linarith [secondLogBound_nonneg]
  rIn_lt_rOut := by linarith

def secondCutoff (p : LogPlane) : ℂ := (secondBump p : ℂ)

theorem secondCutoff_contDiff : ContDiff ℝ ∞ secondCutoff :=
  Complex.ofRealCLM.contDiff.comp secondBump.contDiff

theorem secondCutoff_hasCompactSupport : HasCompactSupport secondCutoff :=
  secondBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

theorem norm_secondCutoff_le_one (p : LogPlane) : ‖secondCutoff p‖ ≤ 1 := by
  change ‖((secondBump p : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg secondBump.nonneg]
  exact secondBump.le_one

theorem second_log_bound (x : ℝ) (hx : 1 / 8 ≤ x) (hx' : x ≤ 21 / 8) :
    ‖Real.log x‖ ≤ secondLogBound := by
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 8) hx
  have hhi := Real.log_le_log (by linarith : 0 < x) hx'
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  unfold secondLogBound
  constructor
  · linarith [neg_abs_le (Real.log (1 / 8 : ℝ)), abs_nonneg (Real.log (21 / 8 : ℝ))]
  · linarith [le_abs_self (Real.log (21 / 8 : ℝ)), abs_nonneg (Real.log (1 / 8 : ℝ))]

theorem secondCutoff_one (x y : ℝ)
    (hx : 1 / 8 ≤ x) (hx' : x ≤ 21 / 8)
    (hy : 1 / 8 ≤ y) (hy' : y ≤ 21 / 8) :
    secondCutoff (logPoint (Real.log x) (Real.log y)) = 1 := by
  have hxn := second_log_bound x hx hx'
  have hyn := second_log_bound y hy hy'
  have hxs := pow_le_pow_left₀ (norm_nonneg (Real.log x)) hxn 2
  have hys := pow_le_pow_left₀ (norm_nonneg (Real.log y)) hyn 2
  have hp := WithLp.prod_norm_sq_eq_of_L2 (logPoint (Real.log x) (Real.log y))
  change ‖logPoint (Real.log x) (Real.log y)‖ ^ 2 =
    ‖Real.log x‖ ^ 2 + ‖Real.log y‖ ^ 2 at hp
  have hm : logPoint (Real.log x) (Real.log y) ∈
      Metric.closedBall (0 : LogPlane) secondBump.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖logPoint (Real.log x) (Real.log y)‖ ≤ 2 * (secondLogBound + 1)
    nlinarith [secondLogBound_nonneg,
      norm_nonneg (logPoint (Real.log x) (Real.log y))]
  change ((secondBump (logPoint (Real.log x) (Real.log y)) : ℝ) : ℂ) = 1
  rw [secondBump.one_of_mem_closedBall hm]
  norm_num

end HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

end
