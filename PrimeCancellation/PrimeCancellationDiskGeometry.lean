/-
Copyright (c) 2026. Released under the Apache 2.0 license.

Geometry and polynomial-growth specialization of the independently proved
zero-free-disk logarithmic-derivative estimate. Mathlib dependencies only.
-/
import PrimeCancellationLogDerivative

noncomputable section

open Set Metric Complex

namespace PrimeCancellationDiskGeometry

def verticalPoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem verticalPoint_re (σ t : ℝ) : (verticalPoint σ t).re = σ := by
  simp [verticalPoint]

@[simp] theorem verticalPoint_im (σ t : ℝ) : (verticalPoint σ t).im = t := by
  simp [verticalPoint]

theorem verticalPoint_sub_same_height (σ η t : ℝ) :
    verticalPoint σ t - verticalPoint η t = ((σ - η : ℝ) : ℂ) := by
  simp only [verticalPoint, Complex.ofReal_sub]
  ring

theorem verticalPoint_mem_inner {β δ σ t : ℝ}
    (hσ : β + δ ≤ σ) (hσ' : σ ≤ 2) :
    verticalPoint σ t ∈ closedBall (verticalPoint 2 t) (2 - β - δ) := by
  change dist (verticalPoint σ t) (verticalPoint 2 t) ≤ 2 - β - δ
  rw [dist_eq_norm, verticalPoint_sub_same_height, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
  linarith

theorem outer_ball_re_lower {β δ t : ℝ} {w : ℂ}
    (hw : w ∈ ball (verticalPoint 2 t) (2 - β - δ / 2)) :
    β + δ / 2 < w.re := by
  have hd : ‖w - verticalPoint 2 t‖ < 2 - β - δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hr : |w.re - 2| ≤ ‖w - verticalPoint 2 t‖ := by
    simpa only [Complex.sub_re, verticalPoint_re] using
      Complex.abs_re_le_norm (w - verticalPoint 2 t)
  have hneg := neg_le_abs (w.re - 2)
  linarith

theorem outer_ball_im_bound {β δ t : ℝ} (hβ : 1 / 2 ≤ β) (hδ : 0 < δ)
    {w : ℂ} (hw : w ∈ ball (verticalPoint 2 t) (2 - β - δ / 2)) :
    |w.im| ≤ |t| + 3 / 2 := by
  have hd : ‖w - verticalPoint 2 t‖ < 2 - β - δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hi : |w.im - t| ≤ ‖w - verticalPoint 2 t‖ := by
    simpa only [Complex.sub_im, verticalPoint_im] using
      Complex.abs_im_le_norm (w - verticalPoint 2 t)
  have ht := abs_add_le (w.im - t) t
  have heq : (w.im - t) + t = w.im := by ring
  rw [heq] at ht
  linarith

theorem polynomial_le_exp_log_bound {C Q H p : ℝ} (k : ℕ)
    (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hH : 1 ≤ H) :
    C * Q ^ p * H ^ k ≤
      Real.exp (1 + Real.log C + p * Real.log Q + (k : ℝ) * Real.log H) := by
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hQpow : 0 < Q ^ p := Real.rpow_pos_of_pos hQp p
  have hHpow : 0 < H ^ k := pow_pos hHp k
  have hprod : 0 < C * Q ^ p * H ^ k := mul_pos (mul_pos hCp hQpow) hHpow
  have hlog : Real.log (C * Q ^ p * H ^ k) =
      Real.log C + p * Real.log Q + (k : ℝ) * Real.log H := by
    rw [Real.log_mul (mul_pos hCp hQpow).ne' hHpow.ne',
      Real.log_mul hCp.ne' hQpow.ne', Real.log_rpow hQp p, Real.log_pow]
  calc
    C * Q ^ p * H ^ k = Real.exp (Real.log (C * Q ^ p * H ^ k)) :=
      (Real.exp_log hprod).symm
    _ ≤ Real.exp (1 + Real.log C + p * Real.log Q + (k : ℝ) * Real.log H) := by
      apply Real.exp_le_exp.mpr
      rw [hlog]
      linarith

/-- A uniform half-plane polynomial bound gives an explicit logarithmic
bound along every horizontal segment from `β+δ` to `2`. The center value
uses just one specified logarithm. -/
theorem norm_logDeriv_le_of_halfPlane_polynomial {F : ℂ → ℂ}
    {β δ σ t C Q p A : ℝ} {m : ℂ} (k : ℕ)
    (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hσ : β + δ ≤ σ) (hσ' : σ ≤ 2)
    (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hp : 0 ≤ p)
    (hF : Differentiable ℂ F)
    (hzero : ∀ w : ℂ, β < w.re → F w ≠ 0)
    (hm : Complex.exp m = F (verticalPoint 2 t)) (hmA : ‖m‖ ≤ A)
    (hpoly : ∀ w : ℂ, 1 / 2 ≤ w.re →
      ‖F w‖ ≤ C * Q ^ p * (2 + |w.im|) ^ k) :
    ‖deriv F (verticalPoint σ t) / F (verticalPoint σ t)‖ ≤
      48 * (1 + Real.log C + p * Real.log Q +
        (k : ℝ) * Real.log (4 + |t|) + A) / δ ^ 2 := by
  let M : ℝ := 1 + Real.log C + p * Real.log Q +
    (k : ℝ) * Real.log (4 + |t|)
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hH : 1 ≤ 4 + |t| := by linarith [abs_nonneg t]
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogH : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg hH
  have hM : 0 < M := by dsimp [M]; positivity
  have h0 : ∀ w ∈ ball (verticalPoint 2 t) (2 - β - δ / 2), F w ≠ 0 := by
    intro w hw
    apply hzero w
    have hwre := outer_ball_re_lower hw
    linarith
  have hb : ∀ w ∈ ball (verticalPoint 2 t) (2 - β - δ / 2),
      ‖F w‖ ≤ Real.exp M := by
    intro w hw
    have hwre := outer_ball_re_lower hw
    have hwim := outer_ball_im_bound hβ hδ hw
    have hheight : 2 + |w.im| ≤ 4 + |t| := by linarith
    calc
      ‖F w‖ ≤ C * Q ^ p * (2 + |w.im|) ^ k := hpoly w (by linarith)
      _ ≤ C * Q ^ p * (4 + |t|) ^ k := by
        apply mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hheight k)
        exact mul_nonneg hCp.le (Real.rpow_nonneg hQp.le p)
      _ ≤ Real.exp M := polynomial_le_exp_log_bound k hC hQ hH
  simpa only [M] using
    PrimeCancellationLogDerivative.norm_logDeriv_le_on_bufferedDisk
      hβ hβ' hδ hδ' hM hF.differentiableOn h0 hm hmA hb
      (verticalPoint_mem_inner hσ hσ')

#print axioms verticalPoint_re
#print axioms verticalPoint_im
#print axioms verticalPoint_sub_same_height
#print axioms verticalPoint_mem_inner
#print axioms outer_ball_re_lower
#print axioms outer_ball_im_bound
#print axioms polynomial_le_exp_log_bound
#print axioms norm_logDeriv_le_of_halfPlane_polynomial

end PrimeCancellationDiskGeometry
