import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

/-!
# Absolute convolution mass from one weighted moment

The fixed-profile transfer does not need an analytic continuation of the
global Dirichlet series. A single absolutely convergent coefficient majorant
and the corresponding positive/negative power moment of the deconvolver
justify all exchanges. In logarithmic coordinates these are exponential
moments. The estimates retain the sign change on the reflected side.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ConvolutionMass

open MeasureTheory
open scoped BigOperators

variable {I T : Type*} [MeasurableSpace T] {μ : Measure T}

/-- A separable majorant proves both individual integrability and summable
integral norms, the precise hypotheses of absolute integral/series Fubini. -/
theorem absolute_mass_of_separable_majorant
    (f : I → T → ℂ) (b : I → ℝ) (g : T → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hb : Summable b) (hg : Integrable g μ)
    (hbound : ∀ i, ∀ᵐ t ∂μ, ‖f i t‖ ≤ b i * g t) :
    (∀ i, Integrable (f i) μ) ∧
      Summable (fun i => ∫ t, ‖f i t‖ ∂μ) := by
  have hi (i : I) : Integrable (f i) μ :=
    Integrable.mono' (hg.const_mul (b i)) (hf i) (hbound i)
  refine ⟨hi, ?_⟩
  apply (hb.mul_right (∫ t, g t ∂μ)).of_nonneg_of_le
    (fun i => integral_nonneg fun t => norm_nonneg (f i t))
  intro i
  calc
    (∫ t, ‖f i t‖ ∂μ) ≤ ∫ t, b i * g t ∂μ :=
      integral_mono_ae (hi i).norm (hg.const_mul (b i)) (hbound i)
    _ = b i * ∫ t, g t ∂μ := integral_const_mul _ _

/-- Translating the direct profile requires the negative exponential
moment of the deconvolver. -/
theorem direct_log_bound (P J : ℝ → ℂ) (a : ℂ) (x t σ C : ℝ)
    (hP : ‖P (t + x)‖ ≤ C * Real.exp (-σ * (t + x))) :
    ‖J t * (a * P (t + x))‖ ≤
      (‖a‖ * Real.exp (-σ * x)) * (C * (‖J t‖ * Real.exp (-σ * t))) := by
  rw [norm_mul, norm_mul]
  calc
    ‖J t‖ * (‖a‖ * ‖P (t + x)‖) ≤
        ‖J t‖ * (‖a‖ * (C * Real.exp (-σ * (t + x)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hP (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      rw [show -σ * (t + x) = -σ * t + -σ * x by ring, Real.exp_add]
      ring

/-- Reflecting the log variable reverses that sign, so the positive
exponential moment is needed on the reflected side. -/
theorem reflected_log_bound (H J : ℝ → ℂ) (a : ℂ) (x t σ C : ℝ)
    (hH : ‖H (x - t)‖ ≤ C * Real.exp (-σ * (x - t))) :
    ‖J t * (a * H (x - t))‖ ≤
      (‖a‖ * Real.exp (-σ * x)) * (C * (‖J t‖ * Real.exp (σ * t))) := by
  rw [norm_mul, norm_mul]
  calc
    ‖J t‖ * (‖a‖ * ‖H (x - t)‖) ≤
        ‖J t‖ * (‖a‖ * (C * Real.exp (-σ * (x - t)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hH (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      rw [show -σ * (x - t) = -σ * x + σ * t by ring, Real.exp_add]
      ring

theorem direct_convolution_absolute_mass
    (P J : ℝ → ℂ) (a : I → ℂ) (x : I → ℝ) (σ C : ℝ)
    (hP : ∀ y, ‖P y‖ ≤ C * Real.exp (-σ * y))
    (hcoeff : Summable (fun i => ‖a i‖ * Real.exp (-σ * x i)))
    (hmoment : Integrable (fun t => ‖J t‖ * Real.exp (-σ * t)))
    (hmeas : ∀ i, AEStronglyMeasurable (fun t => J t * (a i * P (t + x i)))) :
    (∀ i, Integrable (fun t => J t * (a i * P (t + x i)))) ∧
      Summable (fun i => ∫ t, ‖J t * (a i * P (t + x i))‖) := by
  apply absolute_mass_of_separable_majorant _
    (fun i => ‖a i‖ * Real.exp (-σ * x i))
    (fun t => C * (‖J t‖ * Real.exp (-σ * t))) hmeas hcoeff
    (hmoment.const_mul C)
  intro i
  exact Filter.Eventually.of_forall fun t => direct_log_bound P J (a i) (x i) t σ C (hP _)

theorem reflected_convolution_absolute_mass
    (H : I → ℝ → ℂ) (J : ℝ → ℂ) (a : I → ℂ) (x : I → ℝ) (σ C : ℝ)
    (hH : ∀ i y, ‖H i y‖ ≤ C * Real.exp (-σ * y))
    (hcoeff : Summable (fun i => ‖a i‖ * Real.exp (-σ * x i)))
    (hmoment : Integrable (fun t => ‖J t‖ * Real.exp (σ * t)))
    (hmeas : ∀ i, AEStronglyMeasurable (fun t => J t * (a i * H i (x i - t)))) :
    (∀ i, Integrable (fun t => J t * (a i * H i (x i - t)))) ∧
      Summable (fun i => ∫ t, ‖J t * (a i * H i (x i - t))‖) := by
  apply absolute_mass_of_separable_majorant _
    (fun i => ‖a i‖ * Real.exp (-σ * x i))
    (fun t => C * (‖J t‖ * Real.exp (σ * t))) hmeas hcoeff
    (hmoment.const_mul C)
  intro i
  exact Filter.Eventually.of_forall fun t => reflected_log_bound (H i) J (a i) (x i) t σ C (hH i _)

end ThetaGlobal.ConvolutionMass

#print axioms ThetaGlobal.ConvolutionMass.absolute_mass_of_separable_majorant
#print axioms ThetaGlobal.ConvolutionMass.reflected_convolution_absolute_mass
