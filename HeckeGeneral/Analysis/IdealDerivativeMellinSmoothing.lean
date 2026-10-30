import HeckeGeneral.Analysis.HeckeDerivativeSmoothing
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Recovering the genuine ideal series by Mellin transform

The normalized Gaussian smoothing is a function of the positive scale X.
Its Mellin transform at λ with Re(λ)<-1 is the original ideal logarithmic
moment at -λ, multiplied by exp((λ+b)^2). The interchange is justified by
actual L¹ summability: a translated Gaussian integral times the already
proved ideal log-norm majorant. There is no continuation hypothesis.

The norm twist then becomes the expected shift λ -> λ+it after removing
the explicit Gaussian Mellin factor.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField MeasureTheory Filter
open scoped Topology ENNReal

variable (K : Type*) [Field K] [NumberField K]

/-- A genuine L¹ criterion for exchanging countably many complex integrands.
The conclusion includes integrability of the total sum. -/
theorem integrable_complex_tsum_of_summable_integral_norm {ι : Type*} [Countable ι]
    {F : ι → ℝ → ℂ} (hF : ∀ i, Integrable (F i))
    (hsum : Summable (fun i => ∫ u : ℝ, ‖F i u‖)) :
    Integrable (fun u => ∑' i, F i u) := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hF i).aestronglyMeasurable), ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  apply lt_of_le_of_lt (lintegral_mono (fun u => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun i => (hF i).aemeasurable.enorm)]
  have heq (i : ι) : (∫⁻ u : ℝ, ‖F i u‖ₑ) =
      ENNReal.ofReal (∫ u : ℝ, ‖F i u‖) :=
    (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun i => integral_nonneg (fun u => norm_nonneg _)) hsum]
  exact ENNReal.ofReal_lt_top

/-- The scale-dependent ideal smoothing with all actual ideal indices retained. -/
def idealGaussianSmoothing (a : NonzeroIdeal K → ℂ) (k : ℕ) (b X : ℝ) : ℂ :=
  ∑' I, normalizedGaussianIdealTerm K a k b X I

/-- The elementary translated Gaussian kernel appearing in the Mellin integral. -/
def gaussianSmoothingMellinKernel (b : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp ((s + (b : ℂ)) * (u : ℂ)) * logarithmicGaussian u

theorem integrable_gaussianSmoothingMellinKernel (b : ℝ) (s : ℂ) :
    Integrable (gaussianSmoothingMellinKernel b s) :=
  integrable_logarithmicGaussian_laplace (s + (b : ℂ))

theorem integral_gaussianSmoothingMellinKernel (b : ℝ) (s : ℂ) :
    (∫ u : ℝ, gaussianSmoothingMellinKernel b s u) = Complex.exp ((s + (b : ℂ)) ^ 2) :=
  integral_logarithmicGaussian_laplace (s + (b : ℂ))

theorem normalizedGaussianIdealTerm_exp (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b u : ℝ) (I : NonzeroIdeal K) :
    normalizedGaussianIdealTerm K a k b (Real.exp u) I =
      ((-(Real.log (idealNorm K I) : ℂ)) ^ k * a I) *
        (Complex.exp ((b : ℂ) * ((u - Real.log (idealNorm K I) : ℝ) : ℂ)) *
          logarithmicGaussian (u - Real.log (idealNorm K I))) := by
  unfold normalizedGaussianIdealTerm gaussianSmoothedIdealTerm idealGaussianLogRatio
  rw [Real.log_exp]
  unfold logarithmicGaussian
  rw [show ((b * (u - Real.log (idealNorm K I)) -
      (u - Real.log (idealNorm K I)) ^ 2 / 4 : ℝ) : ℂ) =
      (b : ℂ) * ((u - Real.log (idealNorm K I) : ℝ) : ℂ) +
        (-((u - Real.log (idealNorm K I) : ℝ) : ℂ) ^ 2 / 4) by push_cast; ring,
    Complex.exp_add]
  have hc := gaussianVerticalNormalization
  rw [div_eq_mul_inv] at hc ⊢
  rw [← hc]
  ring

/-- Exact factorization of the logarithmic Mellin integrand.
The sign -s is forced by the ideal factor N(I)^s. -/
theorem gaussianIdealMellin_log_integrand (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b : ℝ) (s : ℂ) (u : ℝ) (I : NonzeroIdeal K) :
    Complex.exp (s * (u : ℂ)) * normalizedGaussianIdealTerm K a k b (Real.exp u) I =
      idealLogTerm K a k (-s) I *
        gaussianSmoothingMellinKernel b s (u - Real.log (idealNorm K I)) := by
  rw [normalizedGaussianIdealTerm_exp]
  unfold idealLogTerm dirichletTerm gaussianSmoothingMellinKernel
  rw [neg_neg, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (idealNorm_pos K I).ne'),
    ← Complex.ofReal_log (idealNorm_pos K I).le]
  have heq : Complex.exp (s * (u : ℂ)) *
      Complex.exp ((b : ℂ) * ((u - Real.log (idealNorm K I) : ℝ) : ℂ)) =
      Complex.exp ((Real.log (idealNorm K I) : ℂ) * s) *
        Complex.exp ((s + (b : ℂ)) * ((u - Real.log (idealNorm K I) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ((-(Real.log (idealNorm K I) : ℂ)) ^ k * a I) *
      ((Complex.exp (s * (u : ℂ)) *
        Complex.exp ((b : ℂ) * ((u - Real.log (idealNorm K I) : ℝ) : ℂ))) *
          logarithmicGaussian (u - Real.log (idealNorm K I))) := by ring
    _ = _ := by rw [heq]; ring

theorem integrable_gaussianIdealMellin_log_term (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b : ℝ) (s : ℂ) (I : NonzeroIdeal K) :
    Integrable (fun u : ℝ => Complex.exp (s * (u : ℂ)) *
      normalizedGaussianIdealTerm K a k b (Real.exp u) I) := by
  simp_rw [gaussianIdealMellin_log_integrand]
  simpa only [sub_eq_add_neg] using
    ((integrable_gaussianSmoothingMellinKernel b s).comp_add_right
      (-Real.log (idealNorm K I))).const_mul (idealLogTerm K a k (-s) I)

theorem integral_norm_gaussianIdealMellin_log_term (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b : ℝ) (s : ℂ) (I : NonzeroIdeal K) :
    (∫ u : ℝ, ‖Complex.exp (s * (u : ℂ)) *
      normalizedGaussianIdealTerm K a k b (Real.exp u) I‖) =
    ‖idealLogTerm K a k (-s) I‖ *
      (∫ u : ℝ, ‖gaussianSmoothingMellinKernel b s u‖) := by
  simp_rw [gaussianIdealMellin_log_integrand, norm_mul]
  rw [integral_const_mul]
  congr 1
  simpa only [sub_eq_add_neg] using integral_add_right_eq_self
    (fun u : ℝ => ‖gaussianSmoothingMellinKernel b s u‖) (-Real.log (idealNorm K I))

theorem summable_integral_norm_gaussianIdealMellin_log_term (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {s : ℂ} (hs : s.re < -1) :
    Summable (fun I => ∫ u : ℝ, ‖Complex.exp (s * (u : ℂ)) *
      normalizedGaussianIdealTerm K a k b (Real.exp u) I‖) := by
  simp_rw [integral_norm_gaussianIdealMellin_log_term]
  exact (absolutelySummable_idealLogTerm K a ha k (by simp only [Complex.neg_re]; linarith)).mul_right _

/-- Genuine absolute convergence of the full Mellin integral, proved before evaluation. -/
theorem mellinConvergent_idealGaussianSmoothing (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {s : ℂ} (hs : s.re < -1) :
    MellinConvergent (idealGaussianSmoothing K a k b) s := by
  rw [mellinConvergent_iff_log_integrable]
  have h := integrable_complex_tsum_of_summable_integral_norm
    (integrable_gaussianIdealMellin_log_term K a k b s)
    (summable_integral_norm_gaussianIdealMellin_log_term K a ha k b hs)
  simpa only [idealGaussianSmoothing, tsum_mul_left] using h

theorem integral_gaussianIdealMellin_log_term (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b : ℝ) (s : ℂ) (I : NonzeroIdeal K) :
    (∫ u : ℝ, Complex.exp (s * (u : ℂ)) *
      normalizedGaussianIdealTerm K a k b (Real.exp u) I) =
      idealLogTerm K a k (-s) I * Complex.exp ((s + (b : ℂ)) ^ 2) := by
  simp_rw [gaussianIdealMellin_log_integrand]
  rw [integral_const_mul]
  have hshift : (∫ u : ℝ, gaussianSmoothingMellinKernel b s (u - Real.log (idealNorm K I))) =
      ∫ u : ℝ, gaussianSmoothingMellinKernel b s u := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self
      (gaussianSmoothingMellinKernel b s) (-Real.log (idealNorm K I))
  rw [hshift, integral_gaussianSmoothingMellinKernel]

/-- Evaluation of the actual Mellin integral, in its genuine convergence region. -/
theorem mellin_idealGaussianSmoothing (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {s : ℂ} (hs : s.re < -1) :
    mellin (idealGaussianSmoothing K a k b) s =
      Complex.exp ((s + (b : ℂ)) ^ 2) * idealLogSeries K a k (-s) := by
  rw [mellin_eq_log_integral]
  have h := hasSum_integral_of_summable_integral_norm
    (integrable_gaussianIdealMellin_log_term K a k b s)
    (summable_integral_norm_gaussianIdealMellin_log_term K a ha k b hs)
  have htarget : (∫ u : ℝ, ∑' I, Complex.exp (s * (u : ℂ)) *
      normalizedGaussianIdealTerm K a k b (Real.exp u) I) =
      ∫ u : ℝ, Complex.exp (s * (u : ℂ)) * idealGaussianSmoothing K a k b (Real.exp u) := by
    simp only [idealGaussianSmoothing, tsum_mul_left]
  rw [htarget] at h
  simp_rw [integral_gaussianIdealMellin_log_term] at h
  rw [← h.tsum_eq, tsum_mul_right, idealLogSeries, mul_comm]

theorem hasMellin_idealGaussianSmoothing (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {s : ℂ} (hs : s.re < -1) :
    HasMellin (idealGaussianSmoothing K a k b) s
      (Complex.exp ((s + (b : ℂ)) ^ 2) * idealLogSeries K a k (-s)) :=
  ⟨mellinConvergent_idealGaussianSmoothing K a ha k b hs,
    mellin_idealGaussianSmoothing K a ha k b hs⟩

/-- The recovered Hecke function is the actual convergent ideal series. -/
theorem hasMellin_heckeGaussianSmoothedSeries
    (χ : HeckeGeneral.Characters.HeckeCharacter K) (k : ℕ) (b : ℝ)
    {s : ℂ} (hs : s.re < -1) :
    HasMellin (heckeGaussianSmoothedSeries K χ k b) s
      (Complex.exp ((s + (b : ℂ)) ^ 2) * heckeDerivativeSeries K χ k (-s)) :=
  hasMellin_idealGaussianSmoothing K _ (norm_heckeIdealCoefficient_le_one K χ) k b hs

theorem recoveredGaussianMellin_heckeDerivative
    (χ : HeckeGeneral.Characters.HeckeCharacter K) (k : ℕ) (b : ℝ)
    {s : ℂ} (hs : s.re < -1) :
    mellin (heckeGaussianSmoothedSeries K χ k b) s /
      Complex.exp ((s + (b : ℂ)) ^ 2) = heckeDerivativeSeries K χ k (-s) := by
  rw [(hasMellin_heckeGaussianSmoothedSeries K χ k b hs).2]
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

/-- After removing the explicit Gaussian multiplier, norm twisting shifts λ by +it. -/
theorem recoveredGaussianMellin_normTwist
    (χ : HeckeGeneral.Characters.HeckeCharacter K) (k : ℕ) (b t : ℝ)
    {s : ℂ} (hs : s.re < -1) :
    mellin (heckeGaussianSmoothedSeries K (χ * HeckeGeneral.Characters.heckeNormTwist K t) k b) s /
      Complex.exp ((s + (b : ℂ)) ^ 2) =
    mellin (heckeGaussianSmoothedSeries K χ k b) (s + (t : ℂ) * Complex.I) /
      Complex.exp (((s + (t : ℂ) * Complex.I) + (b : ℂ)) ^ 2) := by
  rw [recoveredGaussianMellin_heckeDerivative K _ k b hs,
    recoveredGaussianMellin_heckeDerivative K χ k b (by simpa using hs),
    heckeDerivativeSeries_normTwist]
  congr 1
  ring

end HeckeGeneral.Analysis
