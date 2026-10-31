import ThetaGlobal.ScalarMellinConvolution
import ThetaGlobal.VerticalInverseBounds
import Mathlib.Analysis.MellinInversion

/-!
# Pointwise recovery of the original test after Gaussian regularization

The inverse integral is identified with Mathlib's Mellin inverse, including
its `1/(2π)` normalization and the sign of the imaginary coordinate.
Mellin inversion and dominated convergence then prove convergence to the
original test at every positive continuity point.  In particular no
almost-everywhere representative is substituted in an ideal sum.

The two integrability assumptions are the ordinary Mellin and vertical
Mellin convergence conditions.  For smooth annular tests they follow from
the existing `ThetaKernel.TestMellin` estimates.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.TestMellinLimit

open MeasureTheory Filter
open scoped Topology

theorem powerPhase_zero_eq_phase (t : ℝ) {y : ℝ} (hy : 0 < y) :
    VerticalInverseBounds.powerPhase 0 y t =
      ScalarMellinConvolution.phase (-t) (Real.log y) := by
  unfold VerticalInverseBounds.powerPhase ScalarMellinConvolution.phase
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),
    ← Complex.ofReal_log hy.le]
  congr 1
  push_cast
  ring

theorem verticalGaussian_zero_eq (ε t : ℝ) :
    GaussianRegularization.verticalGaussian ε 0 t =
      ScalarMellinConvolution.gaussian ε t := by
  unfold GaussianRegularization.verticalGaussian ScalarMellinConvolution.gaussian
  congr 1
  simp only [Complex.ofReal_zero, zero_add, mul_pow, Complex.I_sq]
  ring

theorem inverseLine_eq_mellinInv (F : ℂ → ℂ) (σ y : ℝ) :
    VerticalInverseBounds.inverseLine
      (fun t => F ((σ : ℂ) + (t : ℂ) * Complex.I)) σ y = mellinInv σ F y := by
  unfold VerticalInverseBounds.inverseLine VerticalInverseBounds.powerPhase mellinInv
  simp only [one_div, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => mul_comm _ _

theorem scalar_regularizedTest_eq (F : ℂ → ℂ) (ε : ℝ)
    {y : ℝ} (hy : 0 < y) :
    ScalarMellinConvolution.regularizedTest
      (fun t => F ((t : ℂ) * Complex.I)) ε (Real.log y) =
      VerticalInverseBounds.regularizedInverseLine
        (fun t => F ((t : ℂ) * Complex.I)) ε 0 y := by
  unfold ScalarMellinConvolution.regularizedTest ScalarMellinConvolution.inverseLine
    VerticalInverseBounds.regularizedInverseLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [powerPhase_zero_eq_phase t hy, verticalGaussian_zero_eq]
  ring

/-- Actual pointwise Mellin inversion, before taking the regularized limit. -/
theorem inverseLine_mellin_eq (f : ℝ → ℂ) (σ : ℝ)
    (hf : MellinConvergent f σ) (hF : Complex.VerticalIntegrable (mellin f) σ)
    {y : ℝ} (hy : 0 < y) (hc : ContinuousAt f y) :
    VerticalInverseBounds.inverseLine
      (fun t => mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)) σ y = f y := by
  rw [inverseLine_eq_mellinInv]
  exact mellinInv_mellin_eq σ f hy hf hF hc

/-- The Gaussian-smoothed test converges at every positive point, not
merely almost everywhere.  This is the limit required by discrete theta
and ideal sums. -/
theorem regularized_test_tendsto (f : ℝ → ℂ)
    (hf : MellinConvergent f 0) (hF : Complex.VerticalIntegrable (mellin f) 0)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0))
    {y : ℝ} (hy : 0 < y) (hc : ContinuousAt f y) :
    Tendsto (fun n => ScalarMellinConvolution.regularizedTest
      (fun t => mellin f ((t : ℂ) * Complex.I)) (ε n) (Real.log y))
      atTop (𝓝 (f y)) := by
  have hi : Integrable (fun t : ℝ => mellin f ((t : ℂ) * Complex.I)) := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] using hF
  have h := VerticalInverseBounds.regularizedInverseLine_tendsto
    (fun t => mellin f ((t : ℂ) * Complex.I)) hi ε hε₀ hε₁ hε 0 hy
  have hinv : VerticalInverseBounds.inverseLine
      (fun t => mellin f ((t : ℂ) * Complex.I)) 0 y = f y := by
    simpa only [Complex.ofReal_zero, zero_add] using inverseLine_mellin_eq f 0 hf hF hy hc
  rw [hinv] at h
  exact h.congr (fun n => (scalar_regularizedTest_eq (mellin f) (ε n) hy).symm)

end ThetaGlobal.TestMellinLimit

#print axioms ThetaGlobal.TestMellinLimit.inverseLine_mellin_eq
#print axioms ThetaGlobal.TestMellinLimit.regularized_test_tendsto
