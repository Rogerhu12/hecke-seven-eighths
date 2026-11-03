import HeckeGeneral.Analysis.IdealDerivativeEulerLog

/-!
# Higher logarithmic derivatives and actual prime powers

The k-th logarithmic derivative uses the positive prime power p^m with
weight m^k(-log Np)^(k+1). We represent this as the (k+1)-st ideal log
moment at p^m divided by m. Since m≥1, its norm is bounded by that ideal
moment. This proves absolute convergence and justifies every subsequent
termwise derivative without introducing an analytic convergence hypothesis.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters Filter
open scoped Topology Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- The signed prime-power term for the k-th derivative of L'/L. -/
def primePowerDerivativeTerm (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (k : ℕ) (s : ℂ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  ((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
    idealLogTerm K (nonzeroIdealCoefficient a) (k + 1) s (primePowerIdeal K pn)

def primePowerDerivativeSeries (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (k : ℕ) (s : ℂ) : ℂ := ∑' pn, primePowerDerivativeTerm K a k s pn

/-- The representation agrees exactly with the conventional prime-power weight. -/
theorem primePowerDerivativeTerm_eq (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (k : ℕ) (s : ℂ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    primePowerDerivativeTerm K a k s pn =
      ((pn.2 + 1 : ℕ) : ℂ) ^ k *
        (-(Real.log (Ideal.absNorm pn.1.asIdeal : ℝ) : ℂ)) ^ (k + 1) *
        primeIdealRatio K a s pn.1 ^ (pn.2 + 1) := by
  have hm : ((pn.2 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero pn.2
  unfold primePowerDerivativeTerm idealLogTerm
  rw [log_idealNorm_primePowerIdeal, Complex.ofReal_mul, Complex.ofReal_natCast,
    primePower_dirichletTerm, neg_mul_eq_mul_neg, mul_pow]
  rw [pow_succ]
  field_simp

theorem norm_primePowerDerivativeTerm_le (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (k : ℕ) (s : ℂ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    ‖primePowerDerivativeTerm K a k s pn‖ ≤
      ‖idealLogTerm K (nonzeroIdealCoefficient a) (k + 1) s (primePowerIdeal K pn)‖ := by
  have hm : ‖((pn.2 + 1 : ℕ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast Nat.succ_pos pn.2
  rw [primePowerDerivativeTerm, norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (norm_nonneg _)

theorem absolutelySummable_primePowerDerivativeTerm
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pn => ‖primePowerDerivativeTerm K a k s pn‖) := by
  have hmajor := (absolutelySummable_idealLogTerm K (nonzeroIdealCoefficient a)
    (norm_nonzeroIdealCoefficient_le_one a ha) (k + 1) hs).comp_injective
      (primePowerIdeal_injective K)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_primePowerDerivativeTerm_le K a k s) hmajor

theorem hasDerivAt_primePowerDerivativeTerm (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (k : ℕ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) (s : ℂ) :
    HasDerivAt (fun z => primePowerDerivativeTerm K a k z pn)
      (primePowerDerivativeTerm K a (k + 1) s pn) s :=
  (hasDerivAt_idealLogTerm K (nonzeroIdealCoefficient a) (k + 1)
    (primePowerIdeal K pn) s).const_mul ((pn.2 + 1 : ℕ) : ℂ)⁻¹

/-- Monotonicity in the real part retains the actual coefficient norm. -/
theorem norm_idealLogTerm_mono_realPart (a : NonzeroIdeal K → ℂ) (k : ℕ)
    {s z : ℂ} (hsz : s.re ≤ z.re) (I : NonzeroIdeal K) :
    ‖idealLogTerm K a k z I‖ ≤ ‖idealLogTerm K a k s I‖ := by
  rw [norm_idealLogTerm, norm_idealLogTerm]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_idealNorm K I) (neg_le_neg hsz))
      (norm_nonneg _))
    (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k)

theorem hasDerivAt_primePowerDerivativeSeries
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (primePowerDerivativeSeries K a k)
      (primePowerDerivativeSeries K a (k + 1) s) s := by
  let σ : ℝ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  have hopen : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmajor : Summable (fun pn : HeightOneSpectrum (𝓞 K) × ℕ =>
      ‖idealLogTerm K (nonzeroIdealCoefficient a) (k + 1) (σ : ℂ) (primePowerIdeal K pn)‖) :=
    (absolutelySummable_idealLogTerm K (nonzeroIdealCoefficient a)
      (norm_nonzeroIdealCoefficient_le_one a ha) (k + 1) (by simpa using hσ)).comp_injective
        (primePowerIdeal_injective K)
  have hterm (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
      DifferentiableOn ℂ (fun z => primePowerDerivativeTerm K a k z pn)
        {z : ℂ | σ < z.re} :=
    fun z _ => (hasDerivAt_primePowerDerivativeTerm K a k pn z).differentiableAt.differentiableWithinAt
  have hbound (pn : HeightOneSpectrum (𝓞 K) × ℕ) (z : ℂ) (hz : σ < z.re) :
      ‖primePowerDerivativeTerm K a k z pn‖ ≤
        ‖idealLogTerm K (nonzeroIdealCoefficient a) (k + 1) (σ : ℂ) (primePowerIdeal K pn)‖ :=
    (norm_primePowerDerivativeTerm_le K a k z pn).trans
      (norm_idealLogTerm_mono_realPart K _ (k + 1) (by simpa using hz.le) _)
  have hsum := Complex.hasSum_deriv_of_summable_norm hmajor hterm hopen hbound hsσ
  simp_rw [(hasDerivAt_primePowerDerivativeTerm K a k _ _).deriv] at hsum
  exact ((Complex.differentiableOn_tsum_of_summable_norm hmajor hterm hopen hbound).differentiableAt
    (hopen.mem_nhds hsσ)).hasDerivAt.congr_deriv hsum.tsum_eq.symm

@[simp] theorem primePowerDerivativeSeries_zero
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) :
    primePowerDerivativeSeries K a 0 s = -primePowerLogSeries K a 1 s := by
  unfold primePowerDerivativeSeries primePowerLogSeries
  rw [← tsum_neg]
  apply tsum_congr
  intro pn
  rw [primePowerDerivativeTerm_eq]
  simp only [zero_add, pow_zero, pow_one, one_mul, primePowerLogTerm, neg_mul]

/-- All higher derivatives of the Euler logarithm have their absolutely convergent expansion. -/
theorem iteratedDeriv_primeIdealLogSeries
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv (k + 1) (primeIdealLogSeries K a) s = primePowerDerivativeSeries K a k s := by
  induction k generalizing s with
  | zero =>
    rw [zero_add, iteratedDeriv_one, (hasDerivAt_primeIdealLogSeries K a ha hs).deriv,
      primePowerDerivativeSeries_zero]
  | succ k ih =>
    have heq : iteratedDeriv (k + 1) (primeIdealLogSeries K a) =ᶠ[𝓝 s]
        primePowerDerivativeSeries K a k := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
        with z hz
      exact ih hz
    rw [iteratedDeriv_succ, heq.deriv_eq,
      (hasDerivAt_primePowerDerivativeSeries K a ha k hs).deriv]

/-- The actual Hecke logarithmic derivative and all of its higher derivatives. -/
theorem iteratedDeriv_heckeLogDerivative (χ : HeckeCharacter K) (k : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (heckeLogDerivative K χ) s =
      primePowerDerivativeSeries K (primeCoefficient K χ) k s := by
  induction k generalizing s with
  | zero =>
    rw [iteratedDeriv_zero, heckeLogDerivative_eq_primePowerSeries K χ hs,
      primePowerDerivativeSeries_zero]
  | succ k ih =>
    have heq : iteratedDeriv k (heckeLogDerivative K χ) =ᶠ[𝓝 s]
        primePowerDerivativeSeries K (primeCoefficient K χ) k := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
        with z hz
      exact ih hz
    rw [iteratedDeriv_succ, heq.deriv_eq,
      (hasDerivAt_primePowerDerivativeSeries K (primeCoefficient K χ)
        (norm_primeCoefficient_le_one K χ) k hs).deriv]

end HeckeGeneral.Analysis
