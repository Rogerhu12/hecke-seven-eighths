import HeckeGeneral.Analysis.IdealDerivativePrimePowers
import HeckeGeneral.Analysis.IdealEulerIdentity
import HeckeGeneral.Analysis.HeckeDerivative
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The logarithmic derivative as the actual prime-power series

We differentiate the convergent sum of local Euler logarithms, using a
summable uniform majorant on smaller right half-planes. The already proved
Euler identity identifies its exponential with the ideal series. This proves
the logarithmic derivative identity, with absolute convergence of the double
prime-power sum established independently from ideal norm counting.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters Filter
open scoped Topology Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

theorem norm_primeIdealRatio_le_rpow (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {σ : ℝ} {s : ℂ} (hσ : σ ≤ s.re)
    (p : HeightOneSpectrum (𝓞 K)) :
    ‖primeIdealRatio K a s p‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) := by
  have h := norm_idealLogTerm_le_on_halfPlane K (nonzeroIdealCoefficient a)
    (norm_nonzeroIdealCoefficient_le_one a ha) 0 hσ (primeNonzeroIdeal K p)
  rw [idealLogTerm_zero, ← idealEulerWeight_nonzero] at h
  change ‖idealEulerWeight K a s p.asIdeal‖ ≤
    Real.log (Ideal.absNorm p.asIdeal : ℝ) ^ 0 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) at h
  rw [idealEulerWeight_prime] at h
  simpa only [pow_zero, one_mul] using h

theorem norm_primeIdealRatio_le_half (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (p : HeightOneSpectrum (𝓞 K)) : ‖primeIdealRatio K a s p‖ ≤ 1 / 2 := by
  have hq : (2 : ℝ) ≤ Ideal.absNorm p.asIdeal := by
    exact_mod_cast one_lt_primeIdeal_absNorm K p
  calc
    _ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-(1 : ℝ)) :=
      norm_primeIdealRatio_le_rpow K a ha hs.le p
    _ = (Ideal.absNorm p.asIdeal : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq

theorem summable_primeIdeal_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ)) := by
  have h := (summable_nonzeroIdeal_norm_rpow K hσ).comp_injective
    (primeNonzeroIdeal_injective K)
  exact h

def primeIdealLogTerm (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (p : HeightOneSpectrum (𝓞 K)) : ℂ := -Complex.log (1 - primeIdealRatio K a s p)

def primeIdealLogSeries (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑' p, primeIdealLogTerm K a s p

theorem norm_primeIdealLogTerm_le (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re)
    (p : HeightOneSpectrum (𝓞 K)) :
    ‖primeIdealLogTerm K a s p‖ ≤ (3 / 2) * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) := by
  have hr := norm_primeIdealRatio_le_half K a ha (lt_of_lt_of_le hσ hs) p
  have hlog := Complex.norm_log_one_add_half_le_self (by simpa using hr :
    ‖-primeIdealRatio K a s p‖ ≤ 1 / 2)
  have hlog' : ‖Complex.log (1 - primeIdealRatio K a s p)‖ ≤
      (3 / 2) * ‖primeIdealRatio K a s p‖ := by
    simpa only [norm_neg, sub_eq_add_neg] using hlog
  unfold primeIdealLogTerm
  rw [norm_neg]
  exact hlog'.trans
    (mul_le_mul_of_nonneg_left (norm_primeIdealRatio_le_rpow K a ha hs p) (by norm_num))

theorem hasDerivAt_primeIdealRatio (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (p : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    HasDerivAt (fun z => primeIdealRatio K a z p)
      (-(Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℂ) * primeIdealRatio K a s p) s := by
  have hq : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p)).ne'
  have hbase := (hasDerivAt_neg' s).const_cpow (Or.inl hq)
  apply (hbase.const_mul (a p)).congr_deriv
  rw [← Complex.natCast_log]
  unfold primeIdealRatio
  ring

theorem hasDerivAt_primeIdealLogTerm (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (p : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun z => primeIdealLogTerm K a z p)
      (-((Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℂ) *
        primeIdealRatio K a s p / (1 - primeIdealRatio K a s p))) s := by
  have hslit : 1 - primeIdealRatio K a s p ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (by simpa only [norm_neg] using norm_primeIdealRatio_lt_one K a ha hs p :
        ‖-primeIdealRatio K a s p‖ < 1)
  have h := ((hasDerivAt_primeIdealRatio K a p s).const_sub 1).clog hslit
  apply h.neg.congr_deriv
  ring

theorem differentiableOn_primeIdealLogSeries_above
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (primeIdealLogSeries K a) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((summable_primeIdeal_norm_rpow K hσ).mul_left (3 / 2))
    (fun p z hz => (hasDerivAt_primeIdealLogTerm K a ha p
      (lt_trans hσ hz)).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)
  exact fun p z hz => norm_primeIdealLogTerm_le K a ha hσ (le_of_lt hz) p

/-- The derivative of the convergent Euler logarithm is the negative prime-power sum. -/
theorem hasDerivAt_primeIdealLogSeries (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (primeIdealLogSeries K a) (-primePowerLogSeries K a 1 s) s := by
  let σ : ℝ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  have hopen : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsum := Complex.hasSum_deriv_of_summable_norm
    ((summable_primeIdeal_norm_rpow K hσ).mul_left (3 / 2))
    (fun p z hz => (hasDerivAt_primeIdealLogTerm K a ha p
      (lt_trans hσ hz)).differentiableAt.differentiableWithinAt)
    hopen (fun p z hz => norm_primeIdealLogTerm_le K a ha hσ (le_of_lt hz) p) hsσ
  simp_rw [(hasDerivAt_primeIdealLogTerm K a ha _ hs).deriv] at hsum
  have htarget := (hasSum_primePowerLog_localValues K a ha 1 hs).neg
  simp only [pow_one] at htarget
  exact ((differentiableOn_primeIdealLogSeries_above K a ha hσ).differentiableAt
    (hopen.mem_nhds hsσ)).hasDerivAt.congr_deriv (hsum.unique htarget)

/-- Derivative of the genuine ideal series obtained from its proved Euler identity. -/
theorem hasDerivAt_idealDirichletSeries_euler (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (idealDirichletSeries K (nonzeroIdealCoefficient a))
      (idealDirichletSeries K (nonzeroIdealCoefficient a) s *
        (-primePowerLogSeries K a 1 s)) s := by
  have hexp := (hasDerivAt_primeIdealLogSeries K a ha hs).cexp
  have heq : idealDirichletSeries K (nonzeroIdealCoefficient a) =ᶠ[𝓝 s]
      (fun z => Complex.exp (primeIdealLogSeries K a z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact idealDirichletSeries_eq_primeIdealEulerValue K a ha hz
  have hvalue : Complex.exp (primeIdealLogSeries K a s) =
      idealDirichletSeries K (nonzeroIdealCoefficient a) s :=
    (idealDirichletSeries_eq_primeIdealEulerValue K a ha hs).symm
  exact (hexp.congr_of_eventuallyEq heq).congr_deriv (by rw [hvalue])

theorem idealDirichletSeries_logDerivative_eq_primePowerSeries
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    deriv (idealDirichletSeries K (nonzeroIdealCoefficient a)) s /
      idealDirichletSeries K (nonzeroIdealCoefficient a) s = -primePowerLogSeries K a 1 s := by
  rw [(hasDerivAt_idealDirichletSeries_euler K a ha hs).deriv]
  exact mul_div_cancel_left₀ _ (idealDirichletSeries_ne_zero K a ha hs)

/-- The actual Hecke logarithmic derivative has the convergent prime-power expansion. -/
theorem heckeLogDerivative_eq_primePowerSeries (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLogDerivative K χ s = -primePowerLogSeries K (primeCoefficient K χ) 1 s :=
  idealDirichletSeries_logDerivative_eq_primePowerSeries K (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) hs

end HeckeGeneral.Analysis
