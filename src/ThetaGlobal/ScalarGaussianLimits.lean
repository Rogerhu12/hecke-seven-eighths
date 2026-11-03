import ThetaGlobal.ScalarMellinConvolution
import ThetaGlobal.GaussianRegularization
import Mathlib.Analysis.MellinInversion

/-!
# Pointwise scalar Gaussian limits, including actual Mellin inversion

These are the scalar limit hypotheses needed by AnnularTransfer. They follow
from ordinary L1 vertical spectra and Mathlib's Mellin inversion theorem.
The final direct theorem converges to the actual test value V(exp z), not an
unspecified inverse transform and not merely an almost-everywhere value.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ScalarGaussianLimits

open MeasureTheory Filter
open ThetaGlobal.ScalarMellinConvolution
open scoped Topology

theorem gaussian_eq_vertical (ε t : ℝ) :
    gaussian ε t = GaussianRegularization.verticalGaussian ε 0 t := by
  unfold gaussian GaussianRegularization.verticalGaussian
  congr 1
  simp only [Complex.ofReal_zero, zero_add, mul_pow, Complex.I_sq]
  ring

theorem integrable_phase_product {G : ℝ → ℂ} (hG : Integrable G) (z : ℝ) :
    Integrable (fun t => G t * phase (-t) z) := by
  have hp : Continuous (fun t : ℝ => phase (-t) z) := by
    unfold phase
    fun_prop
  apply hG.norm.mono' (hG.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖G t * phase (-t) z‖ ≤ ‖G t‖
  rw [norm_mul, norm_phase, mul_one]

theorem regularizedTest_tendsto_inverseLine (Vhat : ℝ → ℂ) (hVhat : Integrable Vhat)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℝ) :
    Tendsto (fun n => regularizedTest Vhat (ε n) z)
      atTop (𝓝 (inverseLine Vhat z)) := by
  have h := (GaussianRegularization.regularized_integral_tendsto
    (fun t => Vhat t * phase (-t) z) (integrable_phase_product hVhat z)
    ε hε₀ hε₁ hε 0).const_mul (2 * (Real.pi : ℂ))⁻¹
  have heq (n : ℕ) : regularizedTest Vhat (ε n) z =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t, (Vhat t * phase (-t) z) * GaussianRegularization.verticalGaussian (ε n) 0 t := by
    unfold regularizedTest inverseLine
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [gaussian_eq_vertical]
    ring
  simpa only [heq, inverseLine] using h

theorem regularizedReflected_eq_regularizedTest (Vhat R : ℝ → ℂ) (ε z : ℝ) :
    regularizedReflected Vhat R ε z =
      regularizedTest (fun t => Vhat (-t) * R t) ε z := by
  unfold regularizedReflected regularizedTest inverseLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem regularizedReflected_tendsto (Vhat R : ℝ → ℂ)
    (hF : Integrable (fun t => Vhat (-t) * R t))
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℝ) :
    Tendsto (fun n => regularizedReflected Vhat R (ε n) z)
      atTop (𝓝 (inverseLine (fun t => Vhat (-t) * R t) z)) := by
  simpa only [regularizedReflected_eq_regularizedTest] using
    regularizedTest_tendsto_inverseLine (fun t => Vhat (-t) * R t) hF ε hε₀ hε₁ hε z

/-- Exact compatibility of the log-coordinate inverse line with Mathlib's
Mellin inverse and its normalization 1/(2π). -/
theorem inverseLine_mellin_eq (V : ℝ → ℂ) (z : ℝ) :
    inverseLine (fun t => mellin V ((t : ℂ) * Complex.I)) z =
      mellinInv 0 (mellin V) (Real.exp z) := by
  have hpow (t : ℝ) :
      ((Real.exp z : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) = phase (-t) z := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_pos z).ne'),
      ← Complex.ofReal_log (Real.exp_pos z).le, Real.log_exp]
    unfold phase
    congr 1
    push_cast
    ring
  unfold inverseLine mellinInv
  simp only [Complex.ofReal_zero, zero_add, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat, one_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hpow]
  ring

/-- The actual test is recovered at every positive point whenever its Mellin
integral and vertical transform are L1 and it is continuous at that point.
Smooth annular tests satisfy these scalar analytic hypotheses. -/
theorem regularizedTest_tendsto_actual_test (V : ℝ → ℂ)
    (hV : MellinConvergent V 0)
    (hF : Complex.VerticalIntegrable (mellin V) 0)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℝ)
    (hcont : ContinuousAt V (Real.exp z)) :
    Tendsto (fun n =>
      regularizedTest (fun t => mellin V ((t : ℂ) * Complex.I)) (ε n) z)
      atTop (𝓝 (V (Real.exp z))) := by
  have hspec : Integrable (fun t : ℝ => mellin V ((t : ℂ) * Complex.I)) := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] using hF
  have h := regularizedTest_tendsto_inverseLine
    (fun t => mellin V ((t : ℂ) * Complex.I)) hspec ε hε₀ hε₁ hε z
  rw [inverseLine_mellin_eq,
    mellinInv_mellin_eq 0 V (Real.exp_pos z) hV hF hcont] at h
  exact h

end ThetaGlobal.ScalarGaussianLimits

