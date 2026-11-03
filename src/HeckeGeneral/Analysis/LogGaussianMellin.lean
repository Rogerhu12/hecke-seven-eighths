import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Complex.CauchyIntegral

/-!+# Mellin transform of the actual logarithmic Gaussian

The Gaussian in the detector is `exp (-(log x)^2/4)/(2 sqrt π)`.
We use an equivalent complex square-root normalization and prove the Mellin
integral is absolutely convergent for every complex parameter and equals
`exp (s^2)`. The logarithmic change of variables is proved for arbitrary
complex-valued Mellin integrands before applying the Gaussian integral.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open MeasureTheory Set
open scoped Real

theorem exp_mellin_jacobian (s : ℂ) (u : ℝ) :
    (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (s - 1) = Complex.exp (s * u) := by
  have hn : (Real.exp u : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero u
  conv_lhs => lhs; rw [← Complex.cpow_one (Real.exp u : ℂ)]
  rw [← Complex.cpow_add _ _ hn]
  rw [show (1 : ℂ) + (s - 1) = s by ring, Complex.cpow_def_of_ne_zero hn,
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, mul_comm]

/-- The actual Mellin integral becomes a bilateral Laplace integral on the logarithmic line. -/
theorem mellin_eq_log_integral (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, Complex.exp (s * u) * f (Real.exp u) := by
  unfold mellin
  rw [← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [Complex.real_smul, smul_eq_mul, ← mul_assoc, exp_mellin_jacobian]

theorem mellinConvergent_iff_log_integrable (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun u : ℝ => Complex.exp (s * u) * f (Real.exp u)) := by
  unfold MellinConvergent
  rw [← integrable_comp_exp]
  apply integrable_congr
  filter_upwards [] with u
  rw [Complex.real_smul, smul_eq_mul, ← mul_assoc, exp_mellin_jacobian]

def logGaussianNormalization : ℂ := ((4 * (Real.pi : ℂ)) ^ (1 / 2 : ℂ))⁻¹

theorem logGaussianNormalization_eq_real :
    logGaussianNormalization = ((1 / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
  have hroot : (4 * (Real.pi : ℂ)) ^ (1 / 2 : ℂ) = ((2 * Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [show (4 : ℂ) * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity)]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [logGaussianNormalization, hroot]
  rw [one_div, Complex.ofReal_inv]

/-- The normalized Gaussian as a function of a real logarithmic coordinate. -/
def logarithmicGaussian (u : ℝ) : ℂ :=
  logGaussianNormalization * Complex.exp (-(u : ℂ) ^ 2 / 4)

/-- The original Gaussian profile on the positive multiplicative line. -/
def logGaussianProfile (x : ℝ) : ℂ := logarithmicGaussian (Real.log x)

@[simp] theorem logGaussianProfile_exp (u : ℝ) :
    logGaussianProfile (Real.exp u) = logarithmicGaussian u := by
  simp [logGaussianProfile]

theorem logGaussianNormalization_ne_zero : logGaussianNormalization ≠ 0 := by
  apply inv_ne_zero
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact_mod_cast (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero)

theorem logarithmicGaussian_ne_zero (u : ℝ) : logarithmicGaussian u ≠ 0 :=
  mul_ne_zero logGaussianNormalization_ne_zero (Complex.exp_ne_zero _)

theorem logGaussianProfile_ne_zero (x : ℝ) : logGaussianProfile x ≠ 0 :=
  logarithmicGaussian_ne_zero _

theorem gaussian_laplace_integrand (s : ℂ) (u : ℝ) :
    Complex.exp (s * u) * logarithmicGaussian u =
      logGaussianNormalization * Complex.exp (-(1 / 4 : ℂ) * (u : ℂ) ^ 2 + s * u + 0) := by
  unfold logarithmicGaussian
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem integrable_logarithmicGaussian_laplace (s : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (s * u) * logarithmicGaussian u) := by
  simp_rw [gaussian_laplace_integrand]
  exact (integrable_cexp_quadratic' (b := -(1 / 4 : ℂ)) (by norm_num) s 0).const_mul _

/-- Absolute convergence is established independently of the value of the integral. -/
theorem mellinConvergent_logGaussianProfile (s : ℂ) : MellinConvergent logGaussianProfile s := by
  rw [mellinConvergent_iff_log_integrable]
  simpa only [logGaussianProfile_exp] using integrable_logarithmicGaussian_laplace s

theorem integral_logarithmicGaussian_laplace (s : ℂ) :
    (∫ u : ℝ, Complex.exp (s * u) * logarithmicGaussian u) = Complex.exp (s ^ 2) := by
  simp_rw [gaussian_laplace_integrand]
  rw [integral_const_mul, integral_cexp_quadratic (by norm_num : (-(1 / 4 : ℂ)).re < 0)]
  have hbase : (Real.pi : ℂ) / -(-(1 / 4 : ℂ)) = 4 * (Real.pi : ℂ) := by ring
  have hexp : (0 : ℂ) - s ^ 2 / (4 * -(1 / 4 : ℂ)) = s ^ 2 := by ring
  rw [hbase, hexp]
  unfold logGaussianNormalization
  rw [inv_mul_cancel_left₀]
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact_mod_cast (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero)

/-- The exact Mellin identity used by the detector's Gaussian smoothing. -/
theorem mellin_logGaussianProfile (s : ℂ) : mellin logGaussianProfile s = Complex.exp (s ^ 2) := by
  rw [mellin_eq_log_integral]
  simp only [logGaussianProfile_exp]
  exact integral_logarithmicGaussian_laplace s

theorem hasMellin_logGaussianProfile (s : ℂ) : HasMellin logGaussianProfile s (Complex.exp (s ^ 2)) :=
  ⟨mellinConvergent_logGaussianProfile s, mellin_logGaussianProfile s⟩

/-- The Mellin transform is genuinely entire. -/
theorem analyticAt_mellin_logGaussianProfile (s : ℂ) : AnalyticAt ℂ (mellin logGaussianProfile) s := by
  have he : mellin logGaussianProfile = fun z => Complex.exp (z ^ 2) :=
    funext mellin_logGaussianProfile
  rw [he]
  exact (Complex.differentiable_exp.comp (differentiable_id.pow 2)).analyticAt s

theorem norm_mellin_logGaussianProfile (σ t : ℝ) :
    ‖mellin logGaussianProfile ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      Real.exp (σ ^ 2 - t ^ 2) := by
  rw [mellin_logGaussianProfile, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re]

/-- A vertical real strip has the precise Gaussian majorant required for height integration. -/
theorem norm_mellin_logGaussianProfile_le (B σ t : ℝ) (hB : 0 ≤ B) (hσ : |σ| ≤ B) :
    ‖mellin logGaussianProfile ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.exp (B ^ 2) * Real.exp (-(t ^ 2)) := by
  rw [norm_mellin_logGaussianProfile, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq : σ ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg σ) hB).mpr hσ
  linarith

theorem logGaussianProfile_inverse (x : ℝ) : logGaussianProfile x⁻¹ = logGaussianProfile x := by
  simp [logGaussianProfile, logarithmicGaussian, Real.log_inv]

/-- Scaling a Gaussian profile shifts its Mellin transform by the actual Mellin dilation factor. -/
theorem mellin_logGaussianProfile_scaled {a : ℝ} (ha : 0 < a) (s : ℂ) :
    mellin (fun x => logGaussianProfile (a * x)) s =
      (a : ℂ) ^ (-s) * Complex.exp (s ^ 2) := by
  rw [mellin_comp_mul_left _ _ ha, mellin_logGaussianProfile, smul_eq_mul]

/-- A fixed complex power shifts the Gaussian Mellin parameter exactly. -/
theorem mellin_logGaussianProfile_power (w s : ℂ) :
    mellin (fun x => (x : ℂ) ^ w * logGaussianProfile x) s = Complex.exp ((s + w) ^ 2) := by
  exact (mellin_cpow_smul logGaussianProfile s w).trans (mellin_logGaussianProfile (s + w))

theorem mellinConvergent_logGaussianProfile_power (w s : ℂ) :
    MellinConvergent (fun x => (x : ℂ) ^ w * logGaussianProfile x) s :=
  MellinConvergent.cpow_smul.mpr (mellinConvergent_logGaussianProfile (s + w))

end HeckeGeneral.Analysis
