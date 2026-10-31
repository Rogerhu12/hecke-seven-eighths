import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.FieldTheory.Extension
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# The two scalar Mellin deconvolution identities, with their signs

We work in logarithmic coordinates `u = log t`, so Lebesgue measure here
is exactly the multiplicative measure `dt/t`.  `positiveSpectrum f τ`
is the Mellin transform at `iτ` of `x ↦ f (log x)`.

The direct profile is translated as `f(u+z)` and the reflected profile as
`h(z-u)`.  They consequently consume the seed Mellin factors at `-iτ` and
`+iτ`, respectively.  All sum/integral interchange in this scalar result is
derived from two ordinary L1 assumptions, with no theta identity premise.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ScalarMellinConvolution

open MeasureTheory
open scoped Topology

def phase (τ u : ℝ) : ℂ := Complex.exp ((τ : ℂ) * Complex.I * (u : ℂ))

theorem norm_phase (τ u : ℝ) : ‖phase τ u‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

theorem continuous_phase : Continuous (fun p : ℝ × ℝ => phase (-p.1) p.2) := by
  unfold phase
  fun_prop

theorem phase_shift (τ z v : ℝ) :
    phase (-τ) (v - z) = phase τ z * phase (-τ) v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_reverse (τ z v : ℝ) :
    phase (-τ) (z - v) = phase (-τ) z * phase τ v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def positiveSpectrum (f : ℝ → ℂ) (τ : ℝ) : ℂ :=
  ∫ u, f u * phase τ u

def inverseLine (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ τ, G τ * phase (-τ) u

theorem integrable_spectral_product {G f : ℝ → ℂ}
    (hG : Integrable G) (hf : Integrable f) :
    Integrable (fun p : ℝ × ℝ => G p.1 * phase (-p.1) p.2 * f p.2)
      (volume.prod volume) := by
  have hprod := hG.mul_prod hf
  apply hprod.mono
  · have hm := hprod.aestronglyMeasurable.mul continuous_phase.aestronglyMeasurable
    convert hm using 1
    funext p
    change G p.1 * phase (-p.1) p.2 * f p.2 = (G p.1 * f p.2) * phase (-p.1) p.2
    ring
  · filter_upwards [] with p
    simp only [norm_mul, norm_phase, mul_one]
    exact le_rfl

/-- The scalar inverse-transform/product interchange; absolute Fubini follows
from `G ∈ L1` and `f ∈ L1` because the phase has norm one. -/
theorem integral_inverse_mul {G f : ℝ → ℂ}
    (hG : Integrable G) (hf : Integrable f) :
    (∫ u, inverseLine G u * f u) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ τ, G τ * positiveSpectrum f (-τ) := by
  have hi (u : ℝ) : inverseLine G u * f u =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ τ, G τ * phase (-τ) u * f u := by
    rw [inverseLine, integral_mul_const]
    ring
  simp_rw [hi]
  rw [integral_const_mul]
  congr 1
  calc
    (∫ u, ∫ τ, G τ * phase (-τ) u * f u) =
        ∫ τ, ∫ u, G τ * phase (-τ) u * f u :=
      integral_integral_swap (integrable_spectral_product hG hf).swap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with τ
      rw [positiveSpectrum, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      ring

theorem positiveSpectrum_translate (f : ℝ → ℂ) (τ z : ℝ) :
    positiveSpectrum (fun u => f (u + z)) (-τ) =
      phase τ z * positiveSpectrum f (-τ) := by
  have hshift := integral_add_right_eq_self
    (fun v : ℝ => f v * phase (-τ) (v - z)) z (μ := volume)
  simp only [add_sub_cancel_right] at hshift
  unfold positiveSpectrum
  rw [hshift, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [phase_shift]
  ring

theorem positiveSpectrum_reverse (f : ℝ → ℂ) (τ z : ℝ) :
    positiveSpectrum (fun u => f (z - u)) (-τ) =
      phase (-τ) z * positiveSpectrum f τ := by
  have hshift := integral_sub_left_eq_self
    (fun v : ℝ => f v * phase (-τ) (z - v)) volume z
  have hcancel (u : ℝ) : z - (z - u) = u := by ring
  simp only [hcancel] at hshift
  unfold positiveSpectrum
  rw [hshift, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [phase_reverse]
  ring

theorem direct_profile_convolution {G f : ℝ → ℂ}
    (hG : Integrable G) (hf : Integrable f) (z : ℝ) :
    (∫ u, inverseLine G u * f (u + z)) =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ τ, G τ * phase τ z * positiveSpectrum f (-τ) := by
  rw [integral_inverse_mul hG (hf.comp_add_right z)]
  simp_rw [positiveSpectrum_translate, mul_assoc]

theorem reverse_profile_convolution {G f : ℝ → ℂ}
    (hG : Integrable G) (hf : Integrable f) (z : ℝ) :
    (∫ u, inverseLine G u * f (z - u)) =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ τ, G τ * phase (-τ) z * positiveSpectrum f τ := by
  rw [integral_inverse_mul hG (hf.comp_sub_left z)]
  simp_rw [positiveSpectrum_reverse, mul_assoc]

def gaussian (ε τ : ℝ) : ℂ := Complex.exp (-(ε : ℂ) * (τ : ℂ) ^ 2)

theorem gaussian_even (ε τ : ℝ) : gaussian ε (-τ) = gaussian ε τ := by
  simp [gaussian]

/-- `M τ` is the direct seed Mellin transform at `iτ`.  Thus the
denominator here is `M(-τ)`, exactly as required by Mellin correlation. -/
def deconvolutionSpectrum (M Vhat : ℝ → ℂ) (ε τ : ℝ) : ℂ :=
  Vhat (-τ) * gaussian ε τ / M (-τ)

def regularizedTest (Vhat : ℝ → ℂ) (ε z : ℝ) : ℂ :=
  inverseLine (fun τ => Vhat τ * gaussian ε τ) z

def regularizedReflected (Vhat R : ℝ → ℂ) (ε z : ℝ) : ℂ :=
  inverseLine (fun τ => Vhat (-τ) * gaussian ε τ * R τ) z

/-- The direct scalar deconvolution formula.  `hM` is a local Mellin pair,
and `hMne` follows from the explicit gamma product on the imaginary axis.
There is no fixed-profile global theta identity among the assumptions. -/
theorem deconvolver_direct (f : ℝ → ℂ) (hf : Integrable f)
    (M Vhat : ℝ → ℂ) (ε : ℝ)
    (hM : ∀ τ, positiveSpectrum f τ = M τ) (hMne : ∀ τ, M τ ≠ 0)
    (hG : Integrable (deconvolutionSpectrum M Vhat ε)) (z : ℝ) :
    (∫ u, inverseLine (deconvolutionSpectrum M Vhat ε) u * f (u + z)) =
      regularizedTest Vhat ε z := by
  rw [direct_profile_convolution hG hf]
  have heq (τ : ℝ) :
      deconvolutionSpectrum M Vhat ε τ * phase τ z * positiveSpectrum f (-τ) =
        Vhat (-τ) * gaussian ε τ * phase τ z := by
    rw [hM]
    unfold deconvolutionSpectrum
    field_simp [hMne (-τ)]
  simp_rw [heq]
  unfold regularizedTest inverseLine
  congr 1
  have hneg := integral_neg_eq_self
    (fun τ : ℝ => Vhat τ * gaussian ε τ * phase (-τ) z) volume
  simpa only [gaussian_even, neg_neg] using hneg

/-- The reflected scalar formula.  `hH` is the explicit local quotient
identity `Hhat(iτ) = M(-iτ) R(iτ)`; it is not a theta reflection identity. -/
theorem deconvolver_reflected (h : ℝ → ℂ) (hh : Integrable h)
    (M Vhat R : ℝ → ℂ) (ε : ℝ)
    (hH : ∀ τ, positiveSpectrum h τ = M (-τ) * R τ)
    (hMne : ∀ τ, M τ ≠ 0)
    (hG : Integrable (deconvolutionSpectrum M Vhat ε)) (z : ℝ) :
    (∫ u, inverseLine (deconvolutionSpectrum M Vhat ε) u * h (z - u)) =
      regularizedReflected Vhat R ε z := by
  rw [reverse_profile_convolution hG hh]
  unfold regularizedReflected inverseLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [hH]
  unfold deconvolutionSpectrum
  field_simp [hMne (-τ)]

end ThetaGlobal.ScalarMellinConvolution
