import HeckeGeneral.Analysis.IdealDerivativeGaussianSmoothing
import HeckeGeneral.Analysis.HeckeConjugation

/-!
# Normalized detector smoothing for actual Hecke characters

The 1/(2π) vertical integral has exactly the manuscript's logarithmic Gaussian
profile, including its 1/(2√π) normalization. The coefficients are the genuine
local-character ideal coefficients. This construction has an absolutely
convergent ideal sum and exact norm-twist and inverse-character symmetries.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField MeasureTheory HeckeGeneral.Characters
open scoped Topology ComplexConjugate

variable (K : Type*) [Field K] [NumberField K]

theorem gaussianVerticalNormalization :
    (Real.sqrt Real.pi : ℂ) / (2 * (Real.pi : ℂ)) = logGaussianNormalization := by
  rw [logGaussianNormalization_eq_real]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrt : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have heq : Real.sqrt Real.pi / (2 * Real.pi) = 1 / (2 * Real.sqrt Real.pi) := by
    field_simp
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  exact_mod_cast heq

def normalizedGaussianIdealTerm (a : NonzeroIdeal K → ℂ) (k : ℕ)
    (b X : ℝ) (I : NonzeroIdeal K) : ℂ :=
  gaussianSmoothedIdealTerm K a k b X I / (2 * (Real.pi : ℂ))

theorem normalizedGaussianIdealTerm_profile (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b : ℝ) {X : ℝ} (hX : 0 < X) (I : NonzeroIdeal K) :
    normalizedGaussianIdealTerm K a k b X I =
      ((-(Real.log (idealNorm K I) : ℂ)) ^ k * a I) *
        ((X / idealNorm K I : ℝ) : ℂ) ^ (b : ℂ) *
          logGaussianProfile (X / idealNorm K I) := by
  have hratio : 0 < X / idealNorm K I := div_pos hX (idealNorm_pos K I)
  have hlog : Real.log (X / idealNorm K I) = idealGaussianLogRatio K X I := by
    exact Real.log_div hX.ne' (idealNorm_pos K I).ne'
  unfold normalizedGaussianIdealTerm gaussianSmoothedIdealTerm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio.ne'),
    ← Complex.ofReal_log hratio.le]
  simp only [logGaussianProfile, logarithmicGaussian, hlog]
  rw [show ((b * idealGaussianLogRatio K X I - idealGaussianLogRatio K X I ^ 2 / 4 : ℝ) : ℂ) =
      (idealGaussianLogRatio K X I : ℂ) * (b : ℂ) +
        (-(idealGaussianLogRatio K X I : ℂ) ^ 2 / 4) by push_cast; ring,
    Complex.exp_add]
  have hc := gaussianVerticalNormalization
  rw [div_eq_mul_inv] at hc ⊢
  rw [← hc]
  ring

theorem absolutelySummable_normalizedGaussianIdealTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (b : ℝ) {X : ℝ} (hX : 0 < X) :
    Summable (fun I => ‖normalizedGaussianIdealTerm K a k b X I‖) := by
  simp only [normalizedGaussianIdealTerm, norm_div]
  exact (absolutelySummable_gaussianSmoothedIdealTerm K a ha k b hX).div_const _

def heckeGaussianSmoothedSeries (χ : HeckeCharacter K) (k : ℕ) (b X : ℝ) : ℂ :=
  ∑' I, normalizedGaussianIdealTerm K (heckeIdealCoefficient K χ) k b X I

/-- The normalized detector contour equals the actual, absolutely convergent ideal sum. -/
theorem integral_gaussianContour_iteratedDeriv_heckeLSeries (χ : HeckeCharacter K)
    (k : ℕ) (b : ℝ) {σ X : ℝ} (hσ : 1 < σ) (hX : 0 < X) :
    (∫ t : ℝ, ((gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        iteratedDeriv k (heckeLSeries K χ) (idealVerticalPoint σ t)) /
          (2 * (Real.pi : ℂ))) = heckeGaussianSmoothedSeries K χ k b X := by
  have hderiv (t : ℝ) : iteratedDeriv k (heckeLSeries K χ) (idealVerticalPoint σ t) =
      heckeDerivativeSeries K χ k (idealVerticalPoint σ t) :=
    iteratedDeriv_heckeLSeries K χ k (by simpa using hσ)
  simp_rw [hderiv]
  rw [integral_div]
  change (∫ t : ℝ, (gaussianContourFactor b (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        idealLogSeries K (heckeIdealCoefficient K χ) k (idealVerticalPoint σ t)) /
          (2 * (Real.pi : ℂ)) = _
  rw [integral_gaussianContour_idealLogSeries K _
    (norm_heckeIdealCoefficient_le_one K χ) k b hσ hX]
  simp only [gaussianSmoothedIdealSeries, heckeGaussianSmoothedSeries,
    normalizedGaussianIdealTerm, tsum_div_const]

theorem hasSum_heckeGaussianSmoothedSeries (χ : HeckeCharacter K) (k : ℕ)
    (b : ℝ) {X : ℝ} (hX : 0 < X) :
    HasSum (normalizedGaussianIdealTerm K (heckeIdealCoefficient K χ) k b X)
      (heckeGaussianSmoothedSeries K χ k b X) :=
  (absolutelySummable_normalizedGaussianIdealTerm K _
    (norm_heckeIdealCoefficient_le_one K χ) k b hX).of_norm.hasSum

/-- The paper's exact normalized log-Gaussian weight on actual integral ideals. -/
theorem heckeGaussianSmoothedSeries_eq_profile_sum (χ : HeckeCharacter K) (k : ℕ)
    (b : ℝ) {X : ℝ} (hX : 0 < X) :
    heckeGaussianSmoothedSeries K χ k b X =
      ∑' I, ((-(Real.log (idealNorm K I) : ℂ)) ^ k * heckeIdealCoefficient K χ I) *
        ((X / idealNorm K I : ℝ) : ℂ) ^ (b : ℂ) *
          logGaussianProfile (X / idealNorm K I) :=
  tsum_congr (normalizedGaussianIdealTerm_profile K _ k b hX)

theorem gaussianSmoothedIdealTerm_conjugate (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b X : ℝ) (I : NonzeroIdeal K) :
    gaussianSmoothedIdealTerm K (fun J => conj (a J)) k b X I =
      conj (gaussianSmoothedIdealTerm K a k b X I) := by
  simp only [gaussianSmoothedIdealTerm, map_mul, map_pow, map_neg,
    Complex.conj_ofReal, ← Complex.exp_conj]

theorem normalizedGaussianIdealTerm_conjugate (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b X : ℝ) (I : NonzeroIdeal K) :
    normalizedGaussianIdealTerm K (fun J => conj (a J)) k b X I =
      conj (normalizedGaussianIdealTerm K a k b X I) := by
  simp only [normalizedGaussianIdealTerm, gaussianSmoothedIdealTerm_conjugate,
    map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]

theorem heckeGaussianSmoothedSeries_inv (χ : HeckeCharacter K) (k : ℕ) (b X : ℝ) :
    heckeGaussianSmoothedSeries K χ⁻¹ k b X = conj (heckeGaussianSmoothedSeries K χ k b X) := by
  unfold heckeGaussianSmoothedSeries
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro I
  rw [show heckeIdealCoefficient K χ⁻¹ = fun J => conj (heckeIdealCoefficient K χ J)
    from funext (heckeIdealCoefficient_inv K χ)]
  exact normalizedGaussianIdealTerm_conjugate K _ k b X I

theorem normalizedGaussianIdealTerm_normTwist (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b X u : ℝ) (I : NonzeroIdeal K) :
    normalizedGaussianIdealTerm K (normTwistedCoefficients (idealNorm K) a u) k b X I =
      normalizedGaussianIdealTerm K a k b X I *
        (idealNorm K I : ℂ) ^ ((u : ℂ) * Complex.I) := by
  simp only [normalizedGaussianIdealTerm, gaussianSmoothedIdealTerm, normTwistedCoefficients]
  ring

theorem norm_normalizedGaussianIdealTerm_normTwist (a : NonzeroIdeal K → ℂ)
    (k : ℕ) (b X u : ℝ) (I : NonzeroIdeal K) :
    ‖normalizedGaussianIdealTerm K (normTwistedCoefficients (idealNorm K) a u) k b X I‖ =
      ‖normalizedGaussianIdealTerm K a k b X I‖ := by
  rw [normalizedGaussianIdealTerm_normTwist, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (idealNorm_pos K I)]
  simp

/-- Twisting the actual character supplies exactly the ideal-norm Fourier phase. -/
theorem heckeGaussianSmoothedSeries_normTwist (χ : HeckeCharacter K)
    (k : ℕ) (b X u : ℝ) :
    heckeGaussianSmoothedSeries K (χ * heckeNormTwist K u) k b X =
      ∑' I, normalizedGaussianIdealTerm K (heckeIdealCoefficient K χ) k b X I *
        (idealNorm K I : ℂ) ^ ((u : ℂ) * Complex.I) := by
  unfold heckeGaussianSmoothedSeries
  rw [show heckeIdealCoefficient K (χ * heckeNormTwist K u) =
      normTwistedCoefficients (idealNorm K) (heckeIdealCoefficient K χ) u
    from funext (heckeIdealCoefficient_normTwist K χ u)]
  exact tsum_congr (normalizedGaussianIdealTerm_normTwist K _ k b X u)

end HeckeGeneral.Analysis
