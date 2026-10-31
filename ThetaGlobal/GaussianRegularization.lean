import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gaussian regularization on a vertical Mellin line

The literal multiplier is `exp (ε * (σ + i t)^2)`.  Its uniform bound is
`exp (σ^2)` for `0 ≤ ε ≤ 1`, and it tends to one as `ε → 0`.  Hence every
absolutely integrable vertical Mellin kernel passes to the unregularized
limit by dominated convergence.  This is independent of any theta identity.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GaussianRegularization

open MeasureTheory Filter
open scoped Topology

def verticalGaussian (ε σ t : ℝ) : ℂ :=
  Complex.exp ((ε : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2)

theorem verticalGaussian_norm (ε σ t : ℝ) :
    ‖verticalGaussian ε σ t‖ = Real.exp (ε * (σ ^ 2 - t ^ 2)) := by
  rw [verticalGaussian, Complex.norm_exp]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem verticalGaussian_norm_le {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (σ t : ℝ) :
    ‖verticalGaussian ε σ t‖ ≤ Real.exp (σ ^ 2) := by
  rw [verticalGaussian_norm]
  apply Real.exp_le_exp.mpr
  calc
    ε * (σ ^ 2 - t ^ 2) ≤ ε * σ ^ 2 :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hε₀
    _ ≤ 1 * σ ^ 2 := mul_le_mul_of_nonneg_right hε₁ (sq_nonneg _)
    _ = σ ^ 2 := one_mul _

theorem verticalGaussian_continuous (ε σ : ℝ) :
    Continuous (verticalGaussian ε σ) := by
  unfold verticalGaussian
  fun_prop

theorem verticalGaussian_tendsto {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (σ t : ℝ) :
    Tendsto (fun n => verticalGaussian (ε n) σ t) atTop (𝓝 1) := by
  have hr := ((Complex.continuous_ofReal.tendsto 0).comp hε).mul_const
    (((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2)
  have he := Complex.continuous_exp.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, verticalGaussian, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero] using he

theorem regularized_integrable (g : ℝ → ℂ) (hg : Integrable g)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (σ : ℝ) :
    Integrable (fun t => g t * verticalGaussian ε σ t) := by
  apply Integrable.mono' (hg.norm.const_mul (Real.exp (σ ^ 2)))
    (hg.aestronglyMeasurable.mul (verticalGaussian_continuous ε σ).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖g t * verticalGaussian ε σ t‖ ≤ Real.exp (σ ^ 2) * ‖g t‖
  rw [norm_mul]
  calc
    ‖g t‖ * ‖verticalGaussian ε σ t‖ ≤ ‖g t‖ * Real.exp (σ ^ 2) :=
      mul_le_mul_of_nonneg_left (verticalGaussian_norm_le hε₀ hε₁ σ t) (norm_nonneg _)
    _ = Real.exp (σ ^ 2) * ‖g t‖ := mul_comm _ _

theorem regularized_integral_tendsto (g : ℝ → ℂ) (hg : Integrable g)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (σ : ℝ) :
    Tendsto (fun n => ∫ t, g t * verticalGaussian (ε n) σ t)
      atTop (𝓝 (∫ t, g t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t => Real.exp (σ ^ 2) * ‖g t‖)
  · intro n
    exact (regularized_integrable g hg (hε₀ n) (hε₁ n) σ).aestronglyMeasurable
  · exact hg.norm.const_mul _
  · intro n
    filter_upwards [] with t
    rw [norm_mul]
    calc
      ‖g t‖ * ‖verticalGaussian (ε n) σ t‖ ≤ ‖g t‖ * Real.exp (σ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (verticalGaussian_norm_le (hε₀ n) (hε₁ n) σ t) (norm_nonneg _)
      _ = Real.exp (σ ^ 2) * ‖g t‖ := mul_comm _ _
  · filter_upwards [] with t
    simpa only [mul_one] using
      (tendsto_const_nhds.mul (verticalGaussian_tendsto hε σ t) :
        Tendsto (fun n => g t * verticalGaussian (ε n) σ t) atTop (𝓝 (g t * 1)))

end ThetaGlobal.GaussianRegularization

#print axioms ThetaGlobal.GaussianRegularization.regularized_integral_tendsto
