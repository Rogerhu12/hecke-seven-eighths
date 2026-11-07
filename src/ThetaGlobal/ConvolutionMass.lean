module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.FieldTheory.Extension
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology

@[expose] public section

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
