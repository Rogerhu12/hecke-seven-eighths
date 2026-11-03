import HeckeGeneral.Analysis.HeckeDerivativeSmoothing
import HeckeGeneral.Analysis.IdealDerivativeLogHigher

/-!
# Genuine prime-power detector smoothing

The actual positive prime powers are injected into the actual ideal index.
This supplies every logarithmic majorant needed to exchange the vertical
integral with the prime-power expansion of L'/L and its higher derivatives.
The signed logarithmic derivative convention is retained explicitly.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain MeasureTheory HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

instance countable_positivePrimePowers : Countable (HeightOneSpectrum (𝓞 K) × ℕ) :=
  (primePowerIdeal_injective K).countable

theorem summable_primePowerVerticalMajorant (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun pn => idealVerticalMajorant K (k + 1) σ (primePowerIdeal K pn)) :=
  (summable_idealVerticalMajorant K (k + 1) hσ).comp_injective (primePowerIdeal_injective K)

theorem norm_primePowerDerivativeTerm_vertical_le
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) (σ t : ℝ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    ‖primePowerDerivativeTerm K a k (idealVerticalPoint σ t) pn‖ ≤
      idealVerticalMajorant K (k + 1) σ (primePowerIdeal K pn) :=
  (norm_primePowerDerivativeTerm_le K a k (idealVerticalPoint σ t) pn).trans
    (norm_idealLogTerm_vertical_le K _ (norm_nonzeroIdealCoefficient_le_one a ha)
      (k + 1) σ t (primePowerIdeal K pn))

theorem integrable_kernel_mul_primePowerDerivativeTerm
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) (σ : ℝ) {f : ℝ → ℂ} (hf : Integrable f)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    Integrable (fun t => f t * primePowerDerivativeTerm K a k (idealVerticalPoint σ t) pn) := by
  apply hf.mul_bdd
  · have hc : Continuous (fun z => primePowerDerivativeTerm K a k z pn) :=
      Differentiable.continuous (fun z =>
        (hasDerivAt_primePowerDerivativeTerm K a k pn z).differentiableAt)
    exact (hc.comp (continuous_idealVerticalPoint σ)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t =>
      norm_primePowerDerivativeTerm_vertical_le K a ha k σ t pn)

theorem integral_norm_kernel_mul_primePowerDerivativeTerm_le
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) (σ : ℝ) {f : ℝ → ℂ} (hf : Integrable f)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    (∫ t : ℝ, ‖f t * primePowerDerivativeTerm K a k (idealVerticalPoint σ t) pn‖) ≤
      (∫ t : ℝ, ‖f t‖) * idealVerticalMajorant K (k + 1) σ (primePowerIdeal K pn) := by
  rw [← integral_mul_const]
  apply integral_mono (integrable_kernel_mul_primePowerDerivativeTerm K a ha k σ hf pn).norm
    (hf.norm.mul_const _)
  intro t
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_primePowerDerivativeTerm_vertical_le K a ha k σ t pn)
    (norm_nonneg _)

theorem summable_integral_norm_kernel_mul_primePowerDerivativeTerm
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) {σ : ℝ} (hσ : 1 < σ) {f : ℝ → ℂ} (hf : Integrable f) :
    Summable (fun pn => ∫ t : ℝ,
      ‖f t * primePowerDerivativeTerm K a k (idealVerticalPoint σ t) pn‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_kernel_mul_primePowerDerivativeTerm_le K a ha k σ hf)
    ((summable_primePowerVerticalMajorant K k hσ).mul_left _)

theorem norm_primePowerDerivativeSeries_vertical_le
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖primePowerDerivativeSeries K a k (idealVerticalPoint σ t)‖ ≤
      ∑' pn, idealVerticalMajorant K (k + 1) σ (primePowerIdeal K pn) := by
  apply (norm_tsum_le_tsum_norm
    (absolutelySummable_primePowerDerivativeTerm K a ha k (by simpa using hσ))).trans
  exact Summable.tsum_le_tsum (norm_primePowerDerivativeTerm_vertical_le K a ha k σ t)
    (absolutelySummable_primePowerDerivativeTerm K a ha k (by simpa using hσ))
    (summable_primePowerVerticalMajorant K k hσ)

theorem continuous_primePowerDerivativeSeries_vertical
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun t => primePowerDerivativeSeries K a k (idealVerticalPoint σ t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_primePowerDerivativeSeries K a ha k
    (by simpa using hσ)).continuousAt.comp (continuous_idealVerticalPoint σ).continuousAt

theorem integrable_kernel_mul_primePowerDerivativeSeries
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) {σ : ℝ} (hσ : 1 < σ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t => f t * primePowerDerivativeSeries K a k (idealVerticalPoint σ t)) :=
  hf.mul_bdd (continuous_primePowerDerivativeSeries_vertical K a ha k hσ).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_primePowerDerivativeSeries_vertical_le K a ha k hσ))

theorem hasSum_integral_kernel_mul_primePowerDerivativeTerm
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) {σ : ℝ} (hσ : 1 < σ) {f : ℝ → ℂ} (hf : Integrable f) :
    HasSum (fun pn => ∫ t : ℝ,
      f t * primePowerDerivativeTerm K a k (idealVerticalPoint σ t) pn)
        (∫ t : ℝ, f t * primePowerDerivativeSeries K a k (idealVerticalPoint σ t)) := by
  have h := hasSum_integral_of_summable_integral_norm
    (integrable_kernel_mul_primePowerDerivativeTerm K a ha k σ hf)
    (summable_integral_norm_kernel_mul_primePowerDerivativeTerm K a ha k hσ hf)
  convert h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    simp only [primePowerDerivativeSeries, tsum_mul_left])

/-- Normalized Gaussian weight of a positive prime power in a logarithmic derivative. -/
def gaussianSmoothedPrimePowerDerivativeTerm (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (k : ℕ) (b X : ℝ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  ((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
    normalizedGaussianIdealTerm K (nonzeroIdealCoefficient a) (k + 1) b X (primePowerIdeal K pn)

theorem gaussianSmoothedPrimePowerDerivativeTerm_profile
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (k : ℕ) (b : ℝ)
    {X : ℝ} (hX : 0 < X) (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    gaussianSmoothedPrimePowerDerivativeTerm K a k b X pn =
      ((pn.2 + 1 : ℕ) : ℂ) ^ k *
        (-(Real.log (Ideal.absNorm pn.1.asIdeal : ℝ) : ℂ)) ^ (k + 1) *
        a pn.1 ^ (pn.2 + 1) *
        ((X / (Ideal.absNorm pn.1.asIdeal : ℝ) ^ (pn.2 + 1) : ℝ) : ℂ) ^ (b : ℂ) *
          logGaussianProfile (X / (Ideal.absNorm pn.1.asIdeal : ℝ) ^ (pn.2 + 1)) := by
  have hm : ((pn.2 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero pn.2
  unfold gaussianSmoothedPrimePowerDerivativeTerm
  rw [normalizedGaussianIdealTerm_profile K _ (k + 1) b hX,
    log_idealNorm_primePowerIdeal, idealNorm_primePowerIdeal]
  simp only [nonzeroIdealCoefficient, primePowerIdeal_val, idealCoefficient_prime_pow,
    Complex.ofReal_mul, Complex.ofReal_natCast, neg_mul_eq_mul_neg, mul_pow]
  rw [pow_succ]
  field_simp

theorem integral_gaussianContour_primePowerDerivativeTerm
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (k : ℕ) (b σ : ℝ)
    {X : ℝ} (hX : 0 < X) (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    (∫ t : ℝ, ((gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        primePowerDerivativeTerm K a k (idealVerticalPoint σ t) pn) /
          (2 * (Real.pi : ℂ))) = gaussianSmoothedPrimePowerDerivativeTerm K a k b X pn := by
  simp only [primePowerDerivativeTerm]
  rw [integral_div]
  have heq : (fun t : ℝ => (gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
      (((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
        idealLogTerm K (nonzeroIdealCoefficient a) (k + 1)
          (idealVerticalPoint σ t) (primePowerIdeal K pn))) =
      (fun t : ℝ => ((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
        ((gaussianContourFactor b (idealVerticalPoint σ t) *
          (X : ℂ) ^ idealVerticalPoint σ t) *
            idealLogTerm K (nonzeroIdealCoefficient a) (k + 1)
              (idealVerticalPoint σ t) (primePowerIdeal K pn))) := by funext t; ring
  rw [heq, integral_const_mul, integral_gaussianContour_idealLogTerm K _ (k + 1) b σ hX]
  unfold gaussianSmoothedPrimePowerDerivativeTerm normalizedGaussianIdealTerm
  ring

/-- Absolute convergence of the smoothed actual prime-power expansion for all real centers. -/
theorem absolutelySummable_gaussianSmoothedPrimePowerDerivativeTerm
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) (b : ℝ) {X : ℝ} (hX : 0 < X) :
    Summable (fun pn => ‖gaussianSmoothedPrimePowerDerivativeTerm K a k b X pn‖) := by
  have habs := (absolutelySummable_normalizedGaussianIdealTerm K _
    (norm_nonzeroIdealCoefficient_le_one a ha) (k + 1) b hX).comp_injective
      (primePowerIdeal_injective K)
  apply Summable.of_nonneg_of_le (fun pn => norm_nonneg _) ?_ habs
  intro pn
  dsimp only [Function.comp_def]
  have hm : ‖((pn.2 + 1 : ℕ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast Nat.succ_pos pn.2
  rw [gaussianSmoothedPrimePowerDerivativeTerm, norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (norm_nonneg _)

/-- The actual logarithmic detector integrand is genuinely integrable. -/
theorem integrable_gaussianContour_iteratedDeriv_heckeLogDerivative
    (χ : HeckeCharacter K) (k : ℕ) (b : ℝ) {σ X : ℝ}
    (hσ : 1 < σ) (hX : 0 < X) :
    Integrable (fun t : ℝ => ((gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        iteratedDeriv k (heckeLogDerivative K χ) (idealVerticalPoint σ t)) /
          (2 * (Real.pi : ℂ))) := by
  have hderiv (t : ℝ) : iteratedDeriv k (heckeLogDerivative K χ) (idealVerticalPoint σ t) =
      primePowerDerivativeSeries K (primeCoefficient K χ) k (idealVerticalPoint σ t) :=
    iteratedDeriv_heckeLogDerivative K χ k (by simpa using hσ)
  simp_rw [hderiv]
  exact (integrable_kernel_mul_primePowerDerivativeSeries K (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) k hσ
      (integrable_gaussianContour_scaled b σ hX)).div_const _

/-- The full normalized detector identity for the actual Hecke logarithmic derivative. -/
theorem integral_gaussianContour_iteratedDeriv_heckeLogDerivative
    (χ : HeckeCharacter K) (k : ℕ) (b : ℝ) {σ X : ℝ}
    (hσ : 1 < σ) (hX : 0 < X) :
    (∫ t : ℝ, ((gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        iteratedDeriv k (heckeLogDerivative K χ) (idealVerticalPoint σ t)) /
          (2 * (Real.pi : ℂ))) =
      ∑' pn, gaussianSmoothedPrimePowerDerivativeTerm K (primeCoefficient K χ) k b X pn := by
  have hderiv (t : ℝ) : iteratedDeriv k (heckeLogDerivative K χ) (idealVerticalPoint σ t) =
      primePowerDerivativeSeries K (primeCoefficient K χ) k (idealVerticalPoint σ t) :=
    iteratedDeriv_heckeLogDerivative K χ k (by simpa using hσ)
  simp_rw [hderiv]
  rw [integral_div]
  have h := (hasSum_integral_kernel_mul_primePowerDerivativeTerm K (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) k hσ (integrable_gaussianContour_scaled b σ hX)).div_const
      (2 * (Real.pi : ℂ))
  have hterms (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
      (∫ t : ℝ, (gaussianContourFactor b (idealVerticalPoint σ t) *
        (X : ℂ) ^ idealVerticalPoint σ t) *
          primePowerDerivativeTerm K (primeCoefficient K χ) k (idealVerticalPoint σ t) pn) /
            (2 * (Real.pi : ℂ)) =
      gaussianSmoothedPrimePowerDerivativeTerm K (primeCoefficient K χ) k b X pn := by
    rw [← integral_div]
    exact integral_gaussianContour_primePowerDerivativeTerm K _ k b σ hX pn
  simp_rw [hterms] at h
  exact h.tsum_eq.symm

end HeckeGeneral.Analysis
