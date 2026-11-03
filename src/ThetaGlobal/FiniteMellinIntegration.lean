import ThetaGlobal.FiniteShellCoefficients
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Absolute shell integration and finite-place Mellin transforms

The coefficient estimates alone do not justify unfolding an integral: there
could be cancellation inside each shell.  This module applies the same raw
local Whittaker estimates to the absolute values *before* integrating.  It
therefore proves summability of the integrals of the norms, genuine
integrability for the sum of shell measures, and the literal Mellin identity.

The measure identity used by the final theorem is a geometric hypothesis,
independent of the test function and of the Mellin parameter.  A separate
valuation-shell module proves it from invariance of multiplicative Haar.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.FiniteMellinIntegration

open MeasureTheory
open scoped BigOperators
open ThetaGlobal.FiniteShell

variable {Branch X U : Type*} [MeasurableSpace U]

/-- Take absolute values of the local vector and of the unitary mask before
forming a coefficient.  This retains all pointwise support and decay input. -/
def absoluteData (d : LocalShellData Branch X U) : LocalShellData Branch X U where
  q := d.q
  q_gt_one := d.q_gt_one
  radius := d.radius
  shell := d.shell
  shell_radius := d.shell_radius
  value x := (‖d.value x‖ : ℂ)
  multiplier b k u := (‖d.multiplier b k u‖ : ℂ)
  multiplier_norm b k u := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using
      d.multiplier_norm b k u

theorem absoluteData_bounds (d : LocalShellData Branch X U)
    (hd : LocalWhittakerBounds d) : LocalWhittakerBounds (absoluteData d) := by
  constructor
  · obtain ⟨M, hM, hlarge⟩ := hd.large_support
    exact ⟨M, hM, fun x hx => by simpa [absoluteData, hlarge x hx]⟩
  · intro δ hδ hδ'
    obtain ⟨B, hB, hbound⟩ := hd.small_power δ hδ hδ'
    refine ⟨B, hB, fun x hx hx' => ?_⟩
    simpa only [absoluteData, Complex.norm_real, Real.norm_eq_abs, abs_norm] using
      hbound x hx hx'

/-- The new coefficient is precisely the integral of the norm, with no
norm-of-an-integral substitution. -/
theorem absolute_coefficient_spec (d : LocalShellData Branch X U)
    (μ : Measure U) (b : Branch) (k : ℤ) :
    coefficient (absoluteData d) μ b k =
      Complex.ofReal (∫ u, ‖d.multiplier b k u * d.value (d.shell k u)‖ ∂μ) := by
  change (∫ u, (‖d.multiplier b k u‖ : ℂ) *
    (‖d.value (d.shell k u)‖ : ℂ) ∂μ) = _
  simp_rw [← Complex.ofReal_mul, ← norm_mul]
  exact integral_complex_ofReal

/-- Absolute summability is established at the level required by Fubini:
the summands are the integrals of the norms of the shell integrands. -/
theorem summable_integral_norm (d : LocalShellData Branch X U)
    (μ : Measure U) [IsFiniteMeasure μ] (hd : LocalWhittakerBounds d)
    (b : Branch) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Summable (fun k : ℤ => ∫ u,
      ‖(d.multiplier b k u * d.value (d.shell k u)) *
        (d.q : ℂ) ^ (-(k : ℂ) * s)‖ ∂μ) := by
  have h := (shell_mellin_summable (absoluteData d) μ
    (absoluteData_bounds d hd) b s hs).norm
  apply h.congr
  intro k
  rw [norm_mul, absolute_coefficient_spec]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
  simp_rw [norm_mul]
  rw [integral_mul_const]
  rfl

/-- The geometric sum of the pushforwards of unit measure on all valuation
shells.  The corresponding Haar identity has no analytic hypotheses. -/
def shellMeasure [MeasurableSpace X] (d : LocalShellData Branch X U)
    (μ : Measure U) : Measure X :=
  Measure.sum (fun k : ℤ => Measure.map (d.shell k) μ)

/-- Reassembly from genuine unit-shell integrability and raw local estimates.
The identity `hf_shell` just specifies the restriction of the function being
integrated; it asserts neither convergence nor an integral formula. -/
theorem integrable_and_integral_shellMeasure [MeasurableSpace X]
    (d : LocalShellData Branch X U) (μ : Measure U) [IsFiniteMeasure μ]
    (hd : LocalWhittakerBounds d) (hi : ShellIntegrable d μ)
    (hm : ∀ k, AEMeasurable (d.shell k) μ)
    (b : Branch) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re)
    (f : X → ℂ)
    (hf : ∀ k, AEStronglyMeasurable f (Measure.map (d.shell k) μ))
    (hf_shell : ∀ k u, f (d.shell k u) =
      (d.multiplier b k u * d.value (d.shell k u)) *
        (d.q : ℂ) ^ (-(k : ℂ) * s)) :
    Integrable f (shellMeasure d μ) ∧
      (∫ x, f x ∂shellMeasure d μ) =
        ∑' k : ℤ, coefficient d μ b k * (d.q : ℂ) ^ (-(k : ℂ) * s) := by
  have hlocal (k : ℤ) : Integrable f (Measure.map (d.shell k) μ) := by
    apply (integrable_map_measure (hf k) (hm k)).2
    simpa only [Function.comp_def, hf_shell] using
      (hi b k).mul_const ((d.q : ℂ) ^ (-(k : ℂ) * s))
  have habs : Summable (fun k : ℤ =>
      ∫ x, ‖f x‖ ∂Measure.map (d.shell k) μ) := by
    have h := summable_integral_norm d μ hd b s hs
    apply h.congr
    intro k
    rw [integral_map (hm k) (hf k).norm]
    simp only [hf_shell]
  have hall : Integrable f (shellMeasure d μ) := integrable_sum_measure hlocal habs
  refine ⟨hall, ?_⟩
  rw [shellMeasure, integral_sum_measure hall]
  apply tsum_congr
  intro k
  rw [integral_map (hm k) (hf k)]
  simp only [hf_shell, integral_mul_const, coefficient]

/-- Once multiplicative Haar has been geometrically decomposed into its
unit shells, the local Mellin series is its actual integral. -/
theorem integrable_and_integral_of_haar_shells [MeasurableSpace X]
    (d : LocalShellData Branch X U) (μ : Measure U) [IsFiniteMeasure μ]
    (ν : Measure X) (hν : ν = shellMeasure d μ)
    (hd : LocalWhittakerBounds d) (hi : ShellIntegrable d μ)
    (hm : ∀ k, AEMeasurable (d.shell k) μ)
    (b : Branch) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re)
    (f : X → ℂ)
    (hf : ∀ k, AEStronglyMeasurable f (Measure.map (d.shell k) μ))
    (hf_shell : ∀ k u, f (d.shell k u) =
      (d.multiplier b k u * d.value (d.shell k u)) *
        (d.q : ℂ) ^ (-(k : ℂ) * s)) :
    Integrable f ν ∧ (∫ x, f x ∂ν) =
      ∑' k : ℤ, coefficient d μ b k * (d.q : ℂ) ^ (-(k : ℂ) * s) := by
  rw [hν]
  exact integrable_and_integral_shellMeasure d μ hd hi hm b s hs f hf hf_shell

end ThetaGlobal.FiniteMellinIntegration

#print axioms ThetaGlobal.FiniteMellinIntegration.summable_integral_norm
#print axioms ThetaGlobal.FiniteMellinIntegration.integrable_and_integral_shellMeasure
