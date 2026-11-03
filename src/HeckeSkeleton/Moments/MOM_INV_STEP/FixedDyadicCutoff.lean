module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FourierSeparation
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# One actual fixed cutoff for every normalized dyadic block

The cutoff does not depend on Z, the ideal labels, or the outer radius.
It equals one whenever both positive normalized norms lie in [1,2].
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

open scoped Classical ContDiff

def dyadicBump : ContDiffBump (0 : LogPlane) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def dyadicCutoff (p : LogPlane) : ℂ := (dyadicBump p : ℂ)

theorem dyadicCutoff_contDiff : ContDiff ℝ ∞ dyadicCutoff :=
  Complex.ofRealCLM.contDiff.comp dyadicBump.contDiff

theorem dyadicCutoff_hasCompactSupport : HasCompactSupport dyadicCutoff :=
  dyadicBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

theorem norm_dyadicCutoff_le_one (p : LogPlane) : ‖dyadicCutoff p‖ ≤ 1 := by
  change ‖((dyadicBump p : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg dyadicBump.nonneg]
  exact dyadicBump.le_one

theorem log_bounds_of_dyadic {x : ℝ} (hx : 1 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ Real.log x ∧ Real.log x ≤ 1 := by
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  exact ⟨Real.log_nonneg hx,
    (Real.log_le_log (zero_lt_one.trans_le hx) hx2).trans h2⟩

theorem norm_dyadic_logPoint_le (x y : ℝ)
    (hx : 1 ≤ x) (hx2 : x ≤ 2) (hy : 1 ≤ y) (hy2 : y ≤ 2) :
    ‖logPoint (Real.log x) (Real.log y)‖ ≤ 2 := by
  obtain ⟨hx0, hx1⟩ := log_bounds_of_dyadic hx hx2
  obtain ⟨hy0, hy1⟩ := log_bounds_of_dyadic hy hy2
  have hp := WithLp.prod_norm_sq_eq_of_L2 (logPoint (Real.log x) (Real.log y))
  change ‖logPoint (Real.log x) (Real.log y)‖ ^ 2 =
    ‖Real.log x‖ ^ 2 + ‖Real.log y‖ ^ 2 at hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0, abs_of_nonneg hy0] at hp
  have hxSq : (Real.log x) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hx0 hx1 2
  have hySq : (Real.log y) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hy0 hy1 2
  nlinarith [norm_nonneg (logPoint (Real.log x) (Real.log y)),
    sq_nonneg (Real.log x), sq_nonneg (Real.log y)]

/-- The cutoff-one condition is proved on the actual normalized dyadic
norm range, uniformly for every block and every outer parameter. -/
theorem dyadicCutoff_one (x y : ℝ)
    (hx : 1 ≤ x) (hx2 : x ≤ 2) (hy : 1 ≤ y) (hy2 : y ≤ 2) :
    dyadicCutoff (logPoint (Real.log x) (Real.log y)) = 1 := by
  have hm : logPoint (Real.log x) (Real.log y) ∈
      Metric.closedBall (0 : LogPlane) dyadicBump.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_dyadic_logPoint_le x y hx hx2 hy hy2
  change ((dyadicBump (logPoint (Real.log x) (Real.log y)) : ℝ) : ℂ) = 1
  rw [dyadicBump.one_of_mem_closedBall hm]
  norm_num

/-- In particular, two ordinary dyadic height intervals produce the
same cutoff after dividing by their actual positive lower endpoints. -/
theorem dyadicCutoff_one_of_height_intervals (a b X Y : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (ha : X ≤ a) (ha2 : a ≤ 2 * X)
    (hb : Y ≤ b) (hb2 : b ≤ 2 * Y) :
    dyadicCutoff (logPoint (Real.log (a / X)) (Real.log (b / Y))) = 1 := by
  apply dyadicCutoff_one
  · exact (le_div_iff₀ hX).mpr (by simpa only [one_mul] using ha)
  · exact (div_le_iff₀ hX).mpr ha2
  · exact (le_div_iff₀ hY).mpr (by simpa only [one_mul] using hb)
  · exact (div_le_iff₀ hY).mpr hb2

end HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

end
