import ThetaGlobal.GaussianStripDecay
import ThetaGlobal.AnnularTransfer
import ThetaGlobal.ScalarGaussianLimits
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The actual finite gamma product supplies the scalar deconvolver

The direct profile has C0 A0^s times a finite product of shifted gamma factors.
This file proves its imaginary-line nonvanishing and the entire reciprocal
using Mathlib's actual reciprocal-Gamma theorem. The only remaining local
growth input is explicitly a polynomial-times-exponential strip bound for
that concrete reciprocal product (the usual reciprocal-Gamma Stirling bound).
GaussianStripDecay proves the resulting deconvolver's strip decay, after
which DeconvolverMoments proves all absolute power moments.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaDeconvolver

open MeasureTheory
open DeconvolverMoments GaussianStripDecay
open scoped Classical BigOperators

/-- For the theta profile the index is the complex place times the two sixth
offsets; shift = (|m_v|+1)/2 ± 1/6 and radial = -τ_v. -/
structure GammaProfile (ι : Type*) where
  C₀ : ℂ
  C₀_ne_zero : C₀ ≠ 0
  A₀ : ℝ
  A₀_pos : 0 < A₀
  shift : ι → ℝ
  shift_pos : ∀ j, 0 < shift j
  radial : ι → ℝ

variable {ι : Type*} [Fintype ι] (p : GammaProfile ι)

def directGamma (s : ℂ) : ℂ :=
  p.C₀ * Complex.exp ((Real.log p.A₀ : ℂ) * s) *
    ∏ j, Complex.Gamma ((p.shift j : ℂ) + s + Complex.I * (p.radial j : ℂ))

/-- Define the entire reciprocal through reciprocal Gamma, never through an
unconverged totalized Mellin integral. -/
def reciprocalGamma (s : ℂ) : ℂ :=
  p.C₀⁻¹ * Complex.exp (-((Real.log p.A₀ : ℂ) * s)) *
    ∏ j, (Complex.Gamma ((p.shift j : ℂ) + s + Complex.I * (p.radial j : ℂ)))⁻¹

theorem directGamma_eq_positive_cpow (s : ℂ) :
    directGamma p s = p.C₀ * (p.A₀ : ℂ) ^ s *
      ∏ j, Complex.Gamma ((p.shift j : ℂ) + s + Complex.I * (p.radial j : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr p.A₀_pos.ne'),
    ← Complex.ofReal_log p.A₀_pos.le]
  rfl

theorem reciprocalGamma_eq_inverse (s : ℂ) :
    reciprocalGamma p s = (directGamma p s)⁻¹ := by
  unfold reciprocalGamma directGamma
  simp only [mul_inv_rev, Finset.prod_inv_distrib, Complex.exp_neg]
  ring

/-- This is proved even at the gamma poles, using the entire reciprocal. -/
theorem reciprocalGamma_entire : Differentiable ℂ (reciprocalGamma p) := by
  apply Differentiable.mul
  · exact (differentiable_const (p.C₀⁻¹)).mul (by fun_prop)
  · apply Differentiable.fun_finsetProd
    intro j _
    exact Complex.differentiable_one_div_Gamma.comp (by fun_prop)

theorem directGamma_imaginary_ne_zero (t : ℝ) :
    directGamma p ((t : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero p.C₀_ne_zero (Complex.exp_ne_zero _))
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply Complex.Gamma_ne_zero_of_re_pos
  simpa using p.shift_pos j

/-- Concrete scalar deconvolution data for every positive regularizer.
The only Gamma estimate assumed is hStirling for the explicit reciprocal
product above. Its entire nature and imaginary nonvanishing are proved. -/
def gammaDeconvolver (Vhat : ℂ → ℂ)
    (hV : Differentiable ℂ Vhat) (hVstrip : BoundedOnVerticalStrips Vhat)
    (hStirling : ExponentialStripGrowth (reciprocalGamma p))
    (ε : ℝ) (hε : 0 < ε) :
    AnnularTransfer.DeconvolverData
      (fun t => directGamma p ((t : ℂ) * Complex.I))
      (fun t => Vhat ((t : ℂ) * Complex.I)) ε where
  spectrum := regularized (fun s => Vhat (-s) * reciprocalGamma p (-s)) ε
  entire := differentiable_regularized
    ((hV.comp differentiable_neg).mul ((reciprocalGamma_entire p).comp differentiable_neg)) ε
  strip_decay := quadraticStripDecay_regularized
    (hVstrip.exponentialGrowth.comp_neg.mul hStirling.comp_neg) hε
  imaginary_line := by
    intro t
    unfold verticalSpectrum regularized
    simp only [Complex.ofReal_zero, zero_add]
    have hneg : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hneg, reciprocalGamma_eq_inverse]
    have hg := ScalarGaussianLimits.gaussian_eq_vertical ε t
    simp only [GaussianRegularization.verticalGaussian, Complex.ofReal_zero, zero_add] at hg
    rw [← hg]
    unfold ScalarMellinConvolution.deconvolutionSpectrum
    rw [div_eq_mul_inv]
    ring

/-- Every dt/t absolute power moment follows from the explicit Gamma profile,
annular Mellin strip bounds, and the local Stirling bound; it is not assumed. -/
theorem gammaDeconvolver_all_power_moments (Vhat : ℂ → ℂ)
    (hV : Differentiable ℂ Vhat) (hVstrip : BoundedOnVerticalStrips Vhat)
    (hStirling : ExponentialStripGrowth (reciprocalGamma p))
    (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    IntegrableOn
      (fun t => ‖multiplicativeInverse
        (gammaDeconvolver p Vhat hV hVstrip hStirling ε hε).spectrum t‖ * t ^ q / t)
      (Set.Ioi 0) :=
  integrable_multiplicative_power_moment
    (gammaDeconvolver p Vhat hV hVstrip hStirling ε hε).entire
    (gammaDeconvolver p Vhat hV hVstrip hStirling ε hε).strip_decay q

end ThetaGlobal.GammaDeconvolver

