import HeckeSkeleton.HighBinSupport.EulerRegionAnalytic

/-!
# The regular scalar Euler factor is nonzero in the initial domain

These three declarations are moved verbatim from
`ActualEulerRegularNonvanishing`. Their statements, names and proof bodies
are unchanged. They use only the existing scalar corrected-region bound;
the number-field product and its summability remain in the actual module.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

/-- A rational lower bound for the existing fixed denominator margin. -/
theorem sweptTubeEulerMargin_ge_one_eighth : (1 / 8 : ℝ) ≤ sweptTubeEulerMargin := by
  have hsq : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hroot : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    nlinarith [sq_nonneg ((2 : ℝ) ^ (-(1 / 2 : ℝ)) - 1)]
  unfold sweptTubeEulerMargin
  nlinarith

/-- All imaginary parts are allowed; the original initial real parts
put all five summability faces at distance at least six. -/
theorem phaseRowEuler_norm_initial
    {q : ℝ} (hq : 2 ≤ q) (cW cD cE s w z : ℂ)
    (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    ‖phaseRowEuler q cW cD cE s w z - 1‖ ≤ 88 * q ^ (-7 : ℝ) := by
  have hb := phaseRowEuler_region_bound (δ := 6) hq (by norm_num)
    cW cD cE s w z hW hD hE
    (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  norm_num only at hb
  have hC : 11 / sweptTubeEulerMargin ≤ 88 := by
    apply (div_le_iff₀ sweptTubeEulerMargin_pos).mpr
    nlinarith [sweptTubeEulerMargin_ge_one_eighth]
  exact hb.trans (mul_le_mul_of_nonneg_right hC
    (Real.rpow_nonneg (by linarith : 0 ≤ q) _))

/-- Every common regular factor is nonzero in the initial domain. This
assertion does not apply to any of the exceptional finite Laurent tables. -/
theorem phaseRowEuler_ne_zero_initial
    {q : ℝ} (hq : 2 ≤ q) (cW cD cE s w z : ℂ)
    (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    phaseRowEuler q cW cD cE s w z ≠ 0 := by
  have hb := phaseRowEuler_norm_initial hq cW cD cE s w z hW hD hE hs hw hz
  have hp : q ^ (-7 : ℝ) ≤ (2 : ℝ) ^ (-7 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
  have hsmall : ‖phaseRowEuler q cW cD cE s w z - 1‖ < 1 := by
    calc
      _ ≤ 88 * q ^ (-7 : ℝ) := hb
      _ ≤ 88 * (2 : ℝ) ^ (-7 : ℝ) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ < 1 := by norm_num
  intro hzero
  simpa only [hzero, zero_sub, norm_neg, norm_one, lt_self_iff_false] using hsmall

#print axioms sweptTubeEulerMargin_ge_one_eighth
#print axioms phaseRowEuler_norm_initial
#print axioms phaseRowEuler_ne_zero_initial

end HeckeSkeleton.HighBinContinuation
