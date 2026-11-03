import HeckeGeneral.Analysis.HeckeDerivative
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral

/-!
# Genuine ideal sums under vertical smoothing integrals

The kernel is an ordinary integrable function on the real line. All ideal
convergence and logarithmic moments come from the proved number-field ideal
counting theorem. In particular, the integral/series exchange does not assume
continuation, an Euler identity, or bounds on a continued L-function.

The statements cover every logarithmic derivative moment, positive Mellin
scales, and the translation in height induced by the actual norm twist.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open MeasureTheory NumberField Ideal
open scoped Topology nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- Finite norm fibers make the actual ideal index countable. -/
instance countable_nonzeroIdeal : Countable (NonzeroIdeal K) := by
  have : Countable (Ideal (𝓞 K)) := by
    apply Set.Countable.of_preimage_singleton (f := absNorm)
    intro n
    exact (Ideal.finite_setOfPred_absNorm_eq n).countable
  infer_instance

/-- Height parametrization of a vertical line. -/
def idealVerticalPoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem idealVerticalPoint_re (σ t : ℝ) :
    (idealVerticalPoint σ t).re = σ := by simp [idealVerticalPoint]

@[simp] theorem idealVerticalPoint_im (σ t : ℝ) :
    (idealVerticalPoint σ t).im = t := by simp [idealVerticalPoint]

theorem continuous_idealVerticalPoint (σ : ℝ) : Continuous (idealVerticalPoint σ) := by
  unfold idealVerticalPoint
  fun_prop

theorem idealVerticalPoint_sub_height (σ t u : ℝ) :
    idealVerticalPoint σ t - (u : ℂ) * Complex.I = idealVerticalPoint σ (t - u) := by
  unfold idealVerticalPoint
  push_cast
  ring

/-- The nonnegative summable majorant for the k-th ideal moment. -/
def idealVerticalMajorant (k : ℕ) (σ : ℝ) (I : NonzeroIdeal K) : ℝ :=
  Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ)

theorem idealVerticalMajorant_nonneg (k : ℕ) (σ : ℝ) (I : NonzeroIdeal K) :
    0 ≤ idealVerticalMajorant K k σ I :=
  mul_nonneg (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k)
    (Real.rpow_nonneg (idealNorm_pos K I).le _)

theorem summable_idealVerticalMajorant (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (idealVerticalMajorant K k σ) := summable_ideal_logPower_rpow K k hσ

theorem norm_idealLogTerm_vertical_le (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (σ t : ℝ) (I : NonzeroIdeal K) :
    ‖idealLogTerm K a k (idealVerticalPoint σ t) I‖ ≤
      idealVerticalMajorant K k σ I := by
  simpa only [idealVerticalPoint_re, idealVerticalMajorant] using
    norm_idealLogTerm_le K a ha k (idealVerticalPoint σ t) I

theorem continuous_idealLogTerm_vertical (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (σ : ℝ) (I : NonzeroIdeal K) :
    Continuous (fun t => idealLogTerm K a k (idealVerticalPoint σ t) I) :=
  (differentiable_idealLogTerm K a k I).continuous.comp (continuous_idealVerticalPoint σ)

theorem integrable_kernel_mul_idealLogTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (σ : ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (I : NonzeroIdeal K) :
    Integrable (fun t => f t * idealLogTerm K a k (idealVerticalPoint σ t) I) :=
  hf.mul_bdd (continuous_idealLogTerm_vertical K a k σ I).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => norm_idealLogTerm_vertical_le K a ha k σ t I))

theorem integral_norm_kernel_mul_idealLogTerm_le (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (σ : ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (I : NonzeroIdeal K) :
    (∫ t : ℝ, ‖f t * idealLogTerm K a k (idealVerticalPoint σ t) I‖) ≤
      (∫ t : ℝ, ‖f t‖) * idealVerticalMajorant K k σ I := by
  rw [← integral_mul_const]
  apply integral_mono (integrable_kernel_mul_idealLogTerm K a ha k σ hf I).norm
    (hf.norm.mul_const _)
  intro t
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_idealLogTerm_vertical_le K a ha k σ t I)
    (norm_nonneg _)

theorem summable_integral_norm_kernel_mul_idealLogTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Summable (fun I => ∫ t : ℝ, ‖f t * idealLogTerm K a k (idealVerticalPoint σ t) I‖) := by
  apply Summable.of_nonneg_of_le
    (fun I => integral_nonneg (fun t => norm_nonneg _))
    (integral_norm_kernel_mul_idealLogTerm_le K a ha k σ hf)
    ((summable_idealVerticalMajorant K k hσ).mul_left (∫ t : ℝ, ‖f t‖))

theorem norm_idealLogSeries_vertical_le (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖idealLogSeries K a k (idealVerticalPoint σ t)‖ ≤
      ∑' I, idealVerticalMajorant K k σ I := by
  apply (norm_tsum_le_tsum_norm
    (absolutelySummable_idealLogTerm K a ha k (by simpa using hσ))).trans
  exact Summable.tsum_le_tsum (norm_idealLogTerm_vertical_le K a ha k σ t)
    (absolutelySummable_idealLogTerm K a ha k (by simpa using hσ))
    (summable_idealVerticalMajorant K k hσ)

theorem continuous_idealLogSeries_vertical (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun t => idealLogSeries K a k (idealVerticalPoint σ t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (analyticAt_idealLogSeries K a ha k (by simpa using hσ)).continuousAt.comp
    (continuous_idealVerticalPoint σ).continuousAt

/-- The integrand on the sum side is genuinely integrable, not a default-zero integral. -/
theorem integrable_kernel_mul_idealLogSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t => f t * idealLogSeries K a k (idealVerticalPoint σ t)) :=
  hf.mul_bdd (continuous_idealLogSeries_vertical K a ha k hσ).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_idealLogSeries_vertical_le K a ha k hσ))

theorem norm_integral_kernel_mul_idealLogSeries_le (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    ‖∫ t : ℝ, f t * idealLogSeries K a k (idealVerticalPoint σ t)‖ ≤
      (∫ t : ℝ, ‖f t‖) * ∑' I, idealVerticalMajorant K k σ I := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono (integrable_kernel_mul_idealLogSeries K a ha k hσ hf).norm
    (hf.norm.mul_const _)
  intro t
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_idealLogSeries_vertical_le K a ha k hσ t)
    (norm_nonneg _)

/-- Exchange of the actual ideal sum and a vertical kernel integral. -/
theorem hasSum_integral_kernel_mul_idealLogTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    HasSum (fun I => ∫ t : ℝ, f t * idealLogTerm K a k (idealVerticalPoint σ t) I)
      (∫ t : ℝ, f t * idealLogSeries K a k (idealVerticalPoint σ t)) := by
  have h := hasSum_integral_of_summable_integral_norm
    (integrable_kernel_mul_idealLogTerm K a ha k σ hf)
    (summable_integral_norm_kernel_mul_idealLogTerm K a ha k hσ hf)
  convert h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    simp only [idealLogSeries, tsum_mul_left])

theorem integral_kernel_mul_idealLogSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ t : ℝ, f t * idealLogSeries K a k (idealVerticalPoint σ t)) =
      ∑' I, ∫ t : ℝ, f t * idealLogTerm K a k (idealVerticalPoint σ t) I :=
  (hasSum_integral_kernel_mul_idealLogTerm K a ha k hσ hf).tsum_eq.symm

/-- Multiplying an integrable kernel by a positive Mellin scale preserves integrability. -/
theorem integrable_kernel_mul_vertical_cpow {f : ℝ → ℂ} (hf : Integrable f)
    {X : ℝ} (hX : 0 < X) (σ : ℝ) :
    Integrable (fun t => f t * (X : ℂ) ^ idealVerticalPoint σ t) := by
  apply hf.mul_bdd
  · exact ((differentiable_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).continuous.comp
      (continuous_idealVerticalPoint σ)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, idealVerticalPoint_re])

/-- The Mellin contour can be exchanged with every logarithmic ideal moment. -/
theorem integral_mellin_kernel_mul_idealLogSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ)
    {f : ℝ → ℂ} (hf : Integrable f) {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ, (f t * (X : ℂ) ^ idealVerticalPoint σ t) *
      idealLogSeries K a k (idealVerticalPoint σ t)) =
      ∑' I, ∫ t : ℝ, (f t * (X : ℂ) ^ idealVerticalPoint σ t) *
        idealLogTerm K a k (idealVerticalPoint σ t) I :=
  integral_kernel_mul_idealLogSeries K a ha k hσ
    (integrable_kernel_mul_vertical_cpow hf hX σ)

/-- The Fourier phase of a single actual ideal on a vertical line. -/
theorem idealDirichletTerm_vertical_exp (a : NonzeroIdeal K → ℂ)
    (σ t : ℝ) (I : NonzeroIdeal K) :
    dirichletTerm (idealNorm K) a (idealVerticalPoint σ t) I =
      (a I * (idealNorm K I : ℂ) ^ (-(σ : ℂ))) *
        Complex.exp (-(t : ℂ) * Complex.I * (Real.log (idealNorm K I) : ℂ)) := by
  unfold dirichletTerm idealVerticalPoint
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (idealNorm_pos K I).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (idealNorm_pos K I).ne'),
    ← Complex.ofReal_log (idealNorm_pos K I).le, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The transform of a vertical kernel at a real logarithmic frequency. -/
def idealSmoothingTransform (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, f t * Complex.exp (-(t : ℂ) * Complex.I * (u : ℂ))

theorem integral_kernel_idealLogTerm_transform (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (σ : ℝ) (f : ℝ → ℂ) (I : NonzeroIdeal K) :
    (∫ t : ℝ, f t * idealLogTerm K a k (idealVerticalPoint σ t) I) =
      ((-(Real.log (idealNorm K I) : ℂ)) ^ k * a I *
        (idealNorm K I : ℂ) ^ (-(σ : ℂ))) *
          idealSmoothingTransform f (Real.log (idealNorm K I)) := by
  simp only [idealLogTerm, idealDirichletTerm_vertical_exp, idealSmoothingTransform]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by ring)

theorem integral_kernel_idealLogSeries_transform (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ t : ℝ, f t * idealLogSeries K a k (idealVerticalPoint σ t)) =
      ∑' I, ((-(Real.log (idealNorm K I) : ℂ)) ^ k * a I *
        (idealNorm K I : ℂ) ^ (-(σ : ℂ))) *
          idealSmoothingTransform f (Real.log (idealNorm K I)) := by
  rw [integral_kernel_mul_idealLogSeries K a ha k hσ hf]
  exact tsum_congr (integral_kernel_idealLogTerm_transform K a k σ f)

/-- A norm twist translates the height and hence the smoothing kernel. -/
theorem integral_kernel_idealLogSeries_normTwist (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (σ u : ℝ) (f : ℝ → ℂ) :
    (∫ t : ℝ, f t * idealLogSeries K
      (normTwistedCoefficients (idealNorm K) a u) k (idealVerticalPoint σ t)) =
      ∫ t : ℝ, f (t + u) * idealLogSeries K a k (idealVerticalPoint σ t) := by
  simp_rw [idealLogSeries_normTwist, idealVerticalPoint_sub_height]
  rw [← integral_add_right_eq_self
    (fun t : ℝ => f t * idealLogSeries K a k (idealVerticalPoint σ (t - u))) u]
  simp only [add_sub_cancel_right]

end HeckeGeneral.Analysis
