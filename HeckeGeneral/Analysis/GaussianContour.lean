import HeckeGeneral.Analysis.LogGaussianMellin

/-!+# The Gaussian factor on vertical contours

This is the actual entire detector factor `exp ((s-a)^2)`. We prove its
vertical integrability, exact Gaussian norm, polynomially weighted absolute
integrability, and a uniform strip bound. No bound on an L-function or its
reciprocal is assumed or concluded here.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open MeasureTheory
open scoped BigOperators

def gaussianContourFactor (a : ℝ) (s : ℂ) : ℂ := Complex.exp ((s - a) ^ 2)

theorem gaussianContourFactor_ne_zero (a : ℝ) (s : ℂ) : gaussianContourFactor a s ≠ 0 :=
  Complex.exp_ne_zero _

theorem hasDerivAt_gaussianContourFactor (a : ℝ) (s : ℂ) :
    HasDerivAt (gaussianContourFactor a)
      (2 * (s - a) * gaussianContourFactor a s) s := by
  have hd : HasDerivAt (fun z : ℂ => (z - a) ^ 2) (2 * (s - a)) s := by
    simpa using! ((hasDerivAt_id s).sub_const (a : ℂ)).pow 2
  simpa only [gaussianContourFactor, mul_comm] using! hd.cexp

theorem analyticAt_gaussianContourFactor (a : ℝ) (s : ℂ) :
    AnalyticAt ℂ (gaussianContourFactor a) s := by
  have hd : Differentiable ℂ (gaussianContourFactor a) :=
    fun z => (hasDerivAt_gaussianContourFactor a z).differentiableAt
  exact hd.analyticAt s

theorem norm_gaussianContourFactor (a σ t : ℝ) :
    ‖gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      Real.exp ((σ - a) ^ 2 - t ^ 2) := by
  rw [gaussianContourFactor, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re]

theorem gaussianContourFactor_quadratic (a σ t : ℝ) :
    gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (-1 * (t : ℂ) ^ 2 +
        (2 * ((σ - a : ℝ) : ℂ) * Complex.I) * t + ((σ - a : ℝ) : ℂ) ^ 2) := by
  unfold gaussianContourFactor
  congr 1
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem integrable_vertical_gaussianContourFactor (a σ : ℝ) :
    Integrable (fun t : ℝ => gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  simp_rw [gaussianContourFactor_quadratic]
  exact integrable_cexp_quadratic' (b := (-1 : ℂ)) (by norm_num) _ _

theorem verticalIntegrable_gaussianContourFactor (a σ : ℝ) :
    Complex.VerticalIntegrable (gaussianContourFactor a) σ :=
  integrable_vertical_gaussianContourFactor a σ

theorem gaussianContourFactor_strip_bound (a B σ t : ℝ) (hB : 0 ≤ B) (hσ : |σ - a| ≤ B) :
    ‖gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.exp (B ^ 2) * Real.exp (-(t ^ 2)) := by
  rw [norm_gaussianContourFactor, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq : (σ - a) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (σ - a)) hB).mpr hσ
  linarith

/-- Absolute polynomial moments of a real Gaussian, derived from actual integrability. -/
theorem integrable_abs_pow_gaussian (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => |t| ^ k * Real.exp (-b * t ^ 2)) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb
    (by have hn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith : (-1 : ℝ) < (k : ℝ))).norm
  simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _)] using h

theorem integrable_one_add_abs_pow_gaussian (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => (1 + |t|) ^ k * Real.exp (-b * t ^ 2)) := by
  simp_rw [add_pow, Finset.sum_mul, one_pow, one_mul]
  apply integrable_finsetSum
  intro j _
  have h := (integrable_abs_pow_gaussian (k - j) hb).mul_const (k.choose j : ℝ)
  convert! h using 1
  funext t
  ring

/-- Every polynomial weight in height is absolutely integrable against the detector Gaussian. -/
theorem integrable_weighted_gaussianContourNorm (a σ : ℝ) (k : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ k *
      ‖gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
  simp_rw [norm_gaussianContourFactor, Real.exp_sub]
  have h := (integrable_one_add_abs_pow_gaussian k (b := 1) (by norm_num)).const_mul
    (Real.exp ((σ - a) ^ 2))
  convert! h using 1
  funext t
  rw [neg_one_mul, Real.exp_neg]
  ring

/-- Integrability for any measurable vertical factor with an explicit polynomial bound. -/
theorem integrable_gaussianContourFactor_mul {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) (a σ C : ℝ) (k : ℕ)
    (hbound : ∀ t, ‖f t‖ ≤ C * (1 + |t|) ^ k) :
    Integrable (fun t : ℝ => gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I) * f t) := by
  apply Integrable.mono'
    ((integrable_weighted_gaussianContourNorm a σ k).const_mul C)
  · exact (integrable_vertical_gaussianContourFactor a σ).aestronglyMeasurable.mul hf
  · filter_upwards [] with t
    rw [norm_mul]
    calc
      ‖gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * ‖f t‖ ≤
          ‖gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
            (C * (1 + |t|) ^ k) := mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)
      _ = C * ((1 + |t|) ^ k *
          ‖gaussianContourFactor a ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by ring

/-- The detector's shifted Gaussian is exactly a power-twisted Mellin transform. -/
theorem gaussianContourFactor_eq_mellin (a : ℝ) (s : ℂ) :
    gaussianContourFactor a s =
      mellin (fun x => (x : ℂ) ^ (-(a : ℂ)) * logGaussianProfile x) s := by
  rw [mellin_logGaussianProfile_power, gaussianContourFactor, sub_eq_add_neg]

end HeckeGeneral.Analysis
