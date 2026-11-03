import HeckeGeneral.Analysis.IdealDerivativeSmoothing
import HeckeGeneral.Analysis.GaussianContour

/-!
# Gaussian Mellin inversion for genuine ideal sums

We evaluate the vertical Gaussian integral directly using the proved complex
Gaussian integral. The result is a rapidly decreasing weight in log norm.
All logarithmic moments of the actual ideal sum admit the resulting smoothing
formula, with no analytic continuation. The convergent contour expression is
independent of its real part as long as that real part is greater than one.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open MeasureTheory NumberField
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

theorem gaussianContour_laplace_quadratic (a σ u t : ℝ) :
    gaussianContourFactor a (idealVerticalPoint σ t) *
      Complex.exp (idealVerticalPoint σ t * (u : ℂ)) =
    Complex.exp ((-1 : ℂ) * (t : ℂ) ^ 2 +
      (((2 * (σ - a) + u : ℝ) : ℂ) * Complex.I) * (t : ℂ) +
        (((σ - a) ^ 2 + σ * u : ℝ) : ℂ)) := by
  unfold gaussianContourFactor idealVerticalPoint
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

theorem integrable_gaussianContour_laplace (a σ u : ℝ) :
    Integrable (fun t : ℝ => gaussianContourFactor a (idealVerticalPoint σ t) *
      Complex.exp (idealVerticalPoint σ t * (u : ℂ))) := by
  simp_rw [gaussianContour_laplace_quadratic]
  exact integrable_cexp_quadratic' (b := (-1 : ℂ)) (by norm_num) _ _

/-- Exact Gaussian inversion, valid at every vertical line for this elementary kernel. -/
theorem integral_gaussianContour_laplace (a σ u : ℝ) :
    (∫ t : ℝ, gaussianContourFactor a (idealVerticalPoint σ t) *
      Complex.exp (idealVerticalPoint σ t * (u : ℂ))) =
    (Real.sqrt Real.pi : ℂ) * Complex.exp ((a * u - u ^ 2 / 4 : ℝ) : ℂ) := by
  simp_rw [gaussianContour_laplace_quadratic]
  rw [integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num)]
  have hroot : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt Real.pi : ℂ) := by
    norm_num only [neg_neg, div_one]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow Real.pi_pos.le]
    congr 1
    rw [← Real.sqrt_eq_rpow]
  rw [hroot]
  congr 1
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The logarithmic ratio of the Mellin scale to an actual ideal norm. -/
def idealGaussianLogRatio (X : ℝ) (I : NonzeroIdeal K) : ℝ :=
  Real.log X - Real.log (idealNorm K I)

/-- An actual log-norm smoothing coefficient, with its k-th signed moment. -/
def gaussianSmoothedIdealTerm (a : NonzeroIdeal K → ℂ) (k : ℕ)
    (b X : ℝ) (I : NonzeroIdeal K) : ℂ :=
  ((-(Real.log (idealNorm K I) : ℂ)) ^ k * a I) *
    ((Real.sqrt Real.pi : ℂ) *
      Complex.exp ((b * idealGaussianLogRatio K X I -
        idealGaussianLogRatio K X I ^ 2 / 4 : ℝ) : ℂ))

def gaussianSmoothedIdealSeries (a : NonzeroIdeal K → ℂ) (k : ℕ) (b X : ℝ) : ℂ :=
  ∑' I, gaussianSmoothedIdealTerm K a k b X I

theorem gaussianContour_idealLogTerm_integrand (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b σ t : ℝ) {X : ℝ} (hX : 0 < X) (I : NonzeroIdeal K) :
    (gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        idealLogTerm K a k (idealVerticalPoint σ t) I =
    ((-(Real.log (idealNorm K I) : ℂ)) ^ k * a I) *
      (gaussianContourFactor b (idealVerticalPoint σ t) *
        Complex.exp (idealVerticalPoint σ t * (idealGaussianLogRatio K X I : ℂ))) := by
  simp only [idealLogTerm, dirichletTerm, idealGaussianLogRatio]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (idealNorm_pos K I).ne'),
    ← Complex.ofReal_log hX.le, ← Complex.ofReal_log (idealNorm_pos K I).le]
  have hexp : Complex.exp ((Real.log X : ℂ) * idealVerticalPoint σ t) *
      Complex.exp ((Real.log (idealNorm K I) : ℂ) * -idealVerticalPoint σ t) =
      Complex.exp (idealVerticalPoint σ t * (↑(Real.log X) - ↑(Real.log (idealNorm K I)))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  calc
    _ = ((-(Real.log (idealNorm K I) : ℂ)) ^ k * a I) *
        (gaussianContourFactor b (idealVerticalPoint σ t) *
          (Complex.exp ((Real.log X : ℂ) * idealVerticalPoint σ t) *
            Complex.exp ((Real.log (idealNorm K I) : ℂ) * -idealVerticalPoint σ t))) := by ring
    _ = _ := by rw [hexp]

theorem integral_gaussianContour_idealLogTerm (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b σ : ℝ) {X : ℝ} (hX : 0 < X) (I : NonzeroIdeal K) :
    (∫ t : ℝ, (gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        idealLogTerm K a k (idealVerticalPoint σ t) I) =
      gaussianSmoothedIdealTerm K a k b X I := by
  simp_rw [gaussianContour_idealLogTerm_integrand K a k b σ _ hX I]
  rw [integral_const_mul, integral_gaussianContour_laplace]
  rfl

theorem integrable_gaussianContour_scaled (b σ : ℝ) {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) :=
  integrable_kernel_mul_vertical_cpow (integrable_vertical_gaussianContourFactor b σ) hX σ

theorem integrable_gaussianContour_idealLogSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {σ X : ℝ}
    (hσ : 1 < σ) (hX : 0 < X) :
    Integrable (fun t : ℝ => (gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        idealLogSeries K a k (idealVerticalPoint σ t)) :=
  integrable_kernel_mul_idealLogSeries K a ha k hσ (integrable_gaussianContour_scaled b σ hX)

/-- Absolute convergence of the actual ideal smoothing sum, for all real center parameters. -/
theorem absolutelySummable_gaussianSmoothedIdealTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {X : ℝ} (hX : 0 < X) :
    Summable (fun I => ‖gaussianSmoothedIdealTerm K a k b X I‖) := by
  apply Summable.of_nonneg_of_le (fun I => norm_nonneg _)
    (fun I => ?_)
    (summable_integral_norm_kernel_mul_idealLogTerm K a ha k
      (σ := 2) (by norm_num) (integrable_gaussianContour_scaled b 2 hX))
  rw [← integral_gaussianContour_idealLogTerm K a k b 2 hX I]
  exact norm_integral_le_integral_norm _

theorem hasSum_gaussianSmoothedIdealTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {σ X : ℝ}
    (hσ : 1 < σ) (hX : 0 < X) :
    HasSum (gaussianSmoothedIdealTerm K a k b X)
      (∫ t : ℝ, (gaussianContourFactor b (idealVerticalPoint σ t) *
        (X : ℂ) ^ idealVerticalPoint σ t) *
          idealLogSeries K a k (idealVerticalPoint σ t)) := by
  have h := hasSum_integral_kernel_mul_idealLogTerm K a ha k hσ
    (integrable_gaussianContour_scaled b σ hX)
  simpa only [integral_gaussianContour_idealLogTerm K a k b σ hX] using h

theorem integral_gaussianContour_idealLogSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {σ X : ℝ}
    (hσ : 1 < σ) (hX : 0 < X) :
    (∫ t : ℝ, (gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        idealLogSeries K a k (idealVerticalPoint σ t)) =
      gaussianSmoothedIdealSeries K a k b X :=
  (hasSum_gaussianSmoothedIdealTerm K a ha k b hσ hX).tsum_eq.symm

/-- Equality of convergent right-half-plane contours, without a continuation hypothesis. -/
theorem gaussianContour_idealLogSeries_independent (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {σ τ X : ℝ}
    (hσ : 1 < σ) (hτ : 1 < τ) (hX : 0 < X) :
    (∫ t : ℝ, (gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        idealLogSeries K a k (idealVerticalPoint σ t)) =
    (∫ t : ℝ, (gaussianContourFactor b (idealVerticalPoint τ t) *
      (X : ℂ) ^ idealVerticalPoint τ t) *
        idealLogSeries K a k (idealVerticalPoint τ t)) := by
  rw [integral_gaussianContour_idealLogSeries K a ha k b hσ hX,
    integral_gaussianContour_idealLogSeries K a ha k b hτ hX]

end HeckeGeneral.Analysis
