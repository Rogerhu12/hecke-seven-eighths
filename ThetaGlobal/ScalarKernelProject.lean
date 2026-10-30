module

public import ThetaGlobal.RegularizedKernelProject
public import ThetaGlobal.ReflectedLimitProject
public import ThetaGlobal.TestMellinLimit

/-!
# Exact compatibility of scalar Mellin convolution with the actual kernel

These identities are definitional algebra plus the positive-real logarithm.
They check both the t -> -t sign in Vhat(-t) and the 1/(2π) normalization.
No Mellin inversion, theta reflection, or scalar convolution identity is
assumed in this project bridge.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.ScalarKernelProject

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (F : FiniteMellinData K S) (θ : HeckeCharacter K)
variable (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)

theorem regularizedReflected_eq_actualKernel (V : SmoothAnnularTest)
    (ε : ℝ) {y : ℝ} (hy : 0 < y) :
    ScalarMellinConvolution.regularizedReflected
      (fun t => mellin V.toFun ((t : ℂ) * Complex.I))
      (fun t => reflectionMultiplier K S F θ u κ ((t : ℂ) * Complex.I))
      ε (Real.log y) =
    RegularizedKernelProject.regularizedKernel F θ u κ V ε 0 y := by
  unfold ScalarMellinConvolution.regularizedReflected
    ScalarMellinConvolution.inverseLine RegularizedKernelProject.regularizedKernel
    VerticalInverseBounds.regularizedInverseLine RegularizedKernelProject.spectral
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_neg, neg_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [TestMellinLimit.powerPhase_zero_eq_phase t hy,
    TestMellinLimit.verticalGaussian_zero_eq]
  ring

theorem inverseReflected_eq_actualKernel (V : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    ScalarMellinConvolution.inverseLine
      (fun t : ℝ => mellin V (((-t : ℝ) : ℂ) * Complex.I) *
        reflectionMultiplier K S F θ u κ ((t : ℂ) * Complex.I))
      (Real.log y) =
    mellinReflectionKernel K S F θ u κ V 0 y := by
  unfold ScalarMellinConvolution.inverseLine mellinReflectionKernel kernelIntegrand
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_neg, neg_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hp := TestMellinLimit.powerPhase_zero_eq_phase t hy
  unfold VerticalInverseBounds.powerPhase at hp
  simp only [Complex.ofReal_zero, zero_add] at hp
  rw [hp]

variable (D : ThetaArithmeticData K S) (d : MarkedDatum K S)

/-- The exact reflected scalar term arising from the deconvolution theorem is
the actual regularized reflected arithmetic term, at its actual frequency. -/
theorem regularizedTerm_eq_scalar (V : SmoothAnnularTest) (ε : ℝ)
    {X : ℝ} (hX : 0 < X) (i : ReflectionIndex K S d) :
    ReflectedLimitProject.term K S D d θ
      (fun κ y => RegularizedKernelProject.regularizedKernel F θ
        (QuotientGroup.mk d.rowUnit) κ V ε 0 y) X i =
    ReflectedArithmetic.reflectedCoefficient K S D d i θ *
      ScalarMellinConvolution.regularizedReflected
        (fun t => mellin V.toFun ((t : ℂ) * Complex.I))
        (fun t => reflectionMultiplier K S F θ
          (QuotientGroup.mk d.rowUnit) (frequencyClass K S D d i) ((t : ℂ) * Complex.I))
        ε (Real.log (ReflectedLimitProject.argument K S d X i)) := by
  unfold ReflectedLimitProject.term
  rw [regularizedReflected_eq_actualKernel K S F θ
    (QuotientGroup.mk d.rowUnit) (frequencyClass K S D d i) V ε
    (ReflectedLimitProject.argument_pos K S d hX i)]

end ThetaGlobal.ScalarKernelProject

