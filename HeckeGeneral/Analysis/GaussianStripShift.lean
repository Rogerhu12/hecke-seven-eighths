import HeckeGeneral.Analysis.GaussianContour
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! A vertical contour can be moved across an analytic strip whose
horizontal tails have a uniform Gaussian bound. Both vertical integrals
and the vanishing horizontal edges are proved from that same bound. -/

noncomputable section
namespace HeckeGeneral.Analysis

open MeasureTheory Set Filter
open scoped Topology

theorem verticalIntegral_eq_of_gaussian_strip
    {f : ℂ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(t ^ 2))) :
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
    apply ((integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul C).mono'
      hc.aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa using hbound σ hσ t)
  let horizontal : ℝ → ℂ := fun T => ∫ x : ℝ in a..b,
    f ((x : ℂ) + (T : ℂ) * Complex.I)
  have hh : Tendsto horizontal atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun T : ℝ => C * Real.exp (-(T ^ 2)) * |b - a|) atTop (𝓝 0) := by
      have ht : Tendsto (fun T : ℝ => T ^ 2) atTop atTop :=
        tendsto_pow_atTop (by decide)
      have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
      simpa using (he.const_mul C).mul_const |b - a|
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall (fun _ => norm_nonneg _))
    exact Eventually.of_forall fun T =>
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
        hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) T
  have hhn : Tendsto (fun T => horizontal (-T)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht : Tendsto (fun T : ℝ => T ^ 2) atTop atTop := tendsto_pow_atTop (by decide)
    have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
    have hg : Tendsto (fun T : ℝ => C * Real.exp (-(T ^ 2)) * |b - a|) atTop (𝓝 0) := by
      simpa using (he.const_mul C).mul_const |b - a|
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall (fun _ => norm_nonneg _))
    exact Eventually.of_forall fun T =>
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        simpa only [neg_sq] using
          hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) (-T)
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

end HeckeGeneral.Analysis
