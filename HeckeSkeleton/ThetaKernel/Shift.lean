import HeckeGeneral.Analysis.GaussianStripShift
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Vertical contour shift across a strip with a uniform polynomial decay
bound `C (1+|t|)^{-e}`, `e > 1`. -/

noncomputable section
namespace HeckeSkeleton.ThetaKernel

open MeasureTheory Set Filter
open scoped Topology

theorem integrable_one_add_abs_rpow_neg {e : ℝ} (he : 1 < e) :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-e)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := e) (by simpa using he)
  simpa [Real.norm_eq_abs] using this

theorem tendsto_one_add_abs_rpow_neg {e : ℝ} (he : 0 < e) :
    Tendsto (fun T : ℝ => (1 + T) ^ (-e)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => 1 + T) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  exact (tendsto_rpow_neg_atTop he).comp h1

theorem verticalIntegral_eq_of_poly_strip
    {f : ℂ → ℂ} {a b C e : ℝ} (hab : a ≤ b) (he : 1 < e)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ (-e)) :
    (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I) := by
  have hint (σ : ℝ) (hσ : σ ∈ Icc a b) :
      Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have hc : Continuous (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hr : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      exact (hf _ (hr.symm ▸ hσ.1) (hr.symm ▸ hσ.2)).continuousAt.comp
        (by fun_prop : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) t)
    apply ((integrable_one_add_abs_rpow_neg he).const_mul C).mono'
      hc.aestronglyMeasurable
    exact ae_of_all _ (fun t => hbound σ hσ t)
  let horizontal : ℝ → ℂ := fun T => ∫ x : ℝ in a..b,
    f ((x : ℂ) + (T : ℂ) * Complex.I)
  have hg : Tendsto (fun T : ℝ => C * (1 + T) ^ (-e) * |b - a|) atTop (𝓝 0) := by
    have := ((tendsto_one_add_abs_rpow_neg (by linarith : 0 < e)).const_mul C).mul_const |b - a|
    simpa using this
  have hh : Tendsto horizontal atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall (fun _ => norm_nonneg _))
    filter_upwards [eventually_ge_atTop 0] with T hT
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have := hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) T
    simpa [abs_of_nonneg hT] using this
  have hhn : Tendsto (fun T => horizontal (-T)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall (fun _ => norm_nonneg _))
    filter_upwards [eventually_ge_atTop 0] with T hT
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have := hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) (-T)
    simpa [abs_neg, abs_of_nonneg hT] using this
  let left : ℝ → ℂ := fun T => ∫ t : ℝ in -T..T, f ((a : ℂ) + (t : ℂ) * Complex.I)
  let right : ℝ → ℂ := fun T => ∫ t : ℝ in -T..T, f ((b : ℂ) + (t : ℂ) * Complex.I)
  have hrect (T : ℝ) : horizontal (-T) - horizontal T +
      Complex.I * right T - Complex.I * left T = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - (T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I) (by
        intro z hz
        have hre : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact (hf z hre.1 hre.2).differentiableWithinAt)
    simpa only [horizontal, left, right, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      sub_zero, zero_sub, Complex.ofReal_neg, smul_eq_mul] using h
  have hl := intervalIntegral_tendsto_integral (hint a ⟨le_rfl, hab⟩)
    tendsto_neg_atTop_atBot tendsto_id
  have hr := intervalIntegral_tendsto_integral (hint b ⟨hab, le_rfl⟩)
    tendsto_neg_atTop_atBot tendsto_id
  have heq := tendsto_nhds_unique
    (((hhn.sub hh).add (hr.const_mul Complex.I)).sub (hl.const_mul Complex.I))
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun T => (hrect T).symm)))
  simp only [sub_self, zero_add] at heq
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

end HeckeSkeleton.ThetaKernel
