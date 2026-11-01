import HeckeSkeleton.HighBinSupport.HighEulerScalarBounds
import HeckeSkeleton.HighBinSupport.EulerAnalytic
/-!
# The five ramified tables on the complete swept tube

This extends the previous final-line estimate to the open neighbourhood
used for the whole fixed-bin rectangle. It assumes only the explicit
PhaseData norm bounds, not a bound for the exceptional Euler product.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds

theorem specialTerm_swept_bound (P : PhaseData) (q b e : ℝ)
    (hq : 1 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w : ℂ) (hs : b + 15 * e ≤ s.re) (hw : 1 - b - 7 * e ≤ w.re)
    (j : Fin 5) : ‖specialTerm P q s w j‖ ≤ 2 * q ^ (-8 * e) := by
  have ht : 0 ≤ q ^ (-8 * e) := Real.rpow_nonneg (by linarith) _
  have h1 : ‖phaseMonomial q P.eta 1 s w 1 1‖ ≤ q ^ (-8 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.eta_bound
    norm_num
    linarith
  have h2 : ‖phaseMonomial q P.c2 (3 / 2) s w 3 0‖ ≤ q ^ (-8 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.c2_bound
    norm_num
    linarith
  have h31 : ‖phaseMonomial q P.c31 2 s w 3 1‖ ≤ q ^ (-8 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.c31_bound
    norm_num
    linarith
  have h32 : ‖phaseMonomial q P.c32 2 s w 4 0‖ ≤ q ^ (-8 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.c32_bound
    norm_num
    linarith
  have h4 : ‖phaseMonomial q P.c4 (5 / 2) s w 4 1‖ ≤ q ^ (-8 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.c4_bound
    norm_num
    linarith
  have h5 : ‖phaseMonomial q (P.alpha ^ 2) 3 s w 6 0‖ ≤ q ^ (-8 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.alpha_sq_bound
    norm_num
    linarith
  fin_cases j
  · simpa [specialTerm] using h1.trans (by linarith : q ^ (-8 * e) ≤ 2 * q ^ (-8 * e))
  · simpa [specialTerm] using h2.trans (by linarith : q ^ (-8 * e) ≤ 2 * q ^ (-8 * e))
  · exact (norm_sub_le _ _).trans (by simpa [two_mul] using add_le_add h31 h32)
  · simpa [specialTerm] using h4.trans (by linarith : q ^ (-8 * e) ≤ 2 * q ^ (-8 * e))
  · simpa [specialTerm] using h5.trans (by linarith : q ^ (-8 * e) ≤ 2 * q ^ (-8 * e))

theorem coordV_swept_quarter (q e : ℝ) (hq : 2 ≤ q) (he : e ≤ 1 / 10000)
    (z : ℂ) (hz : 17 / 50 - e ≤ z.re) : ‖coordV q z‖ ≤ 1 / 4 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  unfold coordV
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  have hh : (-6 * z).re ≤ (-2 : ℝ) := by
    norm_num [Complex.mul_re]
    linarith
  calc
    q ^ (-6 * z).re ≤ q ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 hh
    _ ≤ (2 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
    _ = 1 / 4 := by norm_num

theorem coordR_swept_decay (P : PhaseData) (q b e : ℝ)
    (hq : 1 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s z : ℂ) (hs : b + 15 * e ≤ s.re) (hz : 17 / 50 - e ≤ z.re) :
    ‖coordR P q s z‖ ≤ q ^ (-8 * e) := by
  unfold coordR
  apply phaseMonomial_norm_le_of_exponent_le q hq _ P.alpha_sq_bound
  norm_num
  linarith

theorem coordR_swept_half (P : PhaseData) (q b e : ℝ)
    (hq : 2 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s z : ℂ) (hs : b + 15 * e ≤ s.re) (hz : 17 / 50 - e ≤ z.re) :
    ‖coordR P q s z‖ ≤ 1 / 2 := by
  have hR : ‖coordR P q s z‖ ≤ q ^ (-1 : ℝ) := by
    unfold coordR
    apply phaseMonomial_norm_le_of_exponent_le q (by linarith) _ P.alpha_sq_bound
    norm_num
    linarith
  calc
    ‖coordR P q s z‖ ≤ q ^ (-1 : ℝ) := hR
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
    _ = 1 / 2 := by norm_num

theorem coordB_swept_bound (P : PhaseData) (q b e : ℝ)
    (hq : 1 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w z : ℂ) (hs : b + 15 * e ≤ s.re) (hw : 1 - b - 7 * e ≤ w.re)
    (hz : 17 / 50 - e ≤ z.re) : ‖coordB P q s w z‖ ≤ 2 * q ^ (-8 * e) := by
  have ht : 0 ≤ q ^ (-8 * e) := Real.rpow_nonneg (by linarith) _
  have hR := coordR_swept_decay P q b e hq hb he s z hs hz
  have hD : ‖phaseMonomial q P.eta 1 s w 1 1‖ ≤ q ^ (-8 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.eta_bound
    norm_num
    linarith
  have hsub : ‖coordR P q s z - phaseMonomial q P.eta 1 s w 1 1‖ ≤
      2 * q ^ (-8 * e) := (norm_sub_le _ _).trans (by linarith)
  unfold coordB
  rw [← sub_mul, norm_mul]
  calc
    _ ≤ (2 * q ^ (-8 * e)) * 1 :=
      mul_le_mul hsub (norm_one_sub_inv_le_one q hq) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- Uniformly in all imaginary parts, throughout the enlarged tube. -/
theorem ramifiedTable_swept_bound (P : PhaseData) (q a e : ℝ)
    (hq : 2 ≤ q) (ha : 1 / 2 ≤ a) (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (s w z : ℂ) (hs : a + 15 * e ≤ s.re)
    (hw : 1 - a - 7 * e ≤ w.re) (hz : 17 / 50 - e ≤ z.re) (j : Fin 5) :
    ‖ramifiedTableValue P q s w z j - 1‖ ≤ 9 * q ^ (-8 * e) := by
  have hq1 : 1 ≤ q := by linarith
  have hR := coordR_swept_half P q a e hq ha he s z hs hz
  rw [ramifiedTableValue_eq_correction P q (by linarith) s w z j
    (one_sub_R_ne_zero _ hR)]
  exact ramifiedCorrection_norm_sub_one_le _ _ _ _ _
    (Real.rpow_nonneg (by linarith) _) hR (coordV_swept_quarter q e hq he' z hz)
    (coordB_swept_bound P q a e hq1 ha he s w z hs hw hz)
    (specialTerm_swept_bound P q a e hq1 ha he s w hs hw j)

#print axioms ramifiedTable_swept_bound

private theorem phaseMonomial_analytic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : E → ℂ} {x : E} {q : ℝ} (hq : 0 < q)
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (c : ℂ) (r : ℝ) (m n : ℕ) :
    AnalyticAt ℂ (fun y => phaseMonomial q c r (f y) (g y) m n) x := by
  exact analyticAt_const.mul (analyticAt_realBase_cpow hq
    ((analyticAt_const.sub (analyticAt_const.mul hf)).sub (analyticAt_const.mul hg)))

/-- Every row in the concrete five-row table is jointly analytic on the
same open tube.  Its only denominator is 1-R, whose nonvanishing has been
proved from the explicit coordinates. -/
theorem ramifiedTable_analyticOnNhd (P : PhaseData) {q a e : ℝ}
    (hq : 2 ≤ q) (ha : 1 / 2 ≤ a) (he : 0 ≤ e) (j : Fin 5) :
    AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ × ℂ => ramifiedTableValue P q v.1 v.2.1 v.2.2 j)
      (sweptTube a e) := by
  intro v hv
  have hq0 : 0 < q := by linarith
  have hs : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.1) v := analyticAt_fst
  have hw : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.2.1) v :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.2.2) v :=
    analyticAt_snd.comp analyticAt_snd
  have hV : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => coordV q v.2.2) v :=
    analyticAt_realBase_cpow hq0 (analyticAt_const.mul hz)
  have hR : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => coordR P q v.1 v.2.2) v :=
    phaseMonomial_analytic hq0 hs hz _ _ _ _
  have hX : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => (q : ℂ) ^ (-v.1)) v :=
    analyticAt_realBase_cpow hq0 hs.neg
  have hY : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => (q : ℂ) ^ (-v.2.1)) v :=
    analyticAt_realBase_cpow hq0 hw.neg
  have hmono (c : ℂ) (r : ℝ) (m n : ℕ) :
      AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => phaseMonomial q c r v.1 v.2.1 m n) v :=
    phaseMonomial_analytic hq0 hs hw c r m n
  have hS : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => specialTerm P q v.1 v.2.1 j) v := by
    fin_cases j
    · exact hmono _ _ _ _
    · exact hmono _ _ _ _
    · exact (hmono _ _ _ _).sub (hmono _ _ _ _)
    · exact (hmono _ _ _ _).neg
    · exact (hmono _ _ _ _).neg
  have hn : 1 - coordR P q v.1 v.2.2 ≠ 0 :=
    one_sub_R_ne_zero _ (coordR_swept_half P q a e hq ha he v.1 v.2.2 hv.1.le hv.2.2.le)
  unfold ramifiedTableValue
  apply AnalyticAt.div
  · fun_prop
  · exact analyticAt_const.sub hR
  · exact hn

#print axioms ramifiedTable_analyticOnNhd
end HeckeSkeleton.HighBinContinuation
