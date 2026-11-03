import HeckeGeneral.Analysis.IdealLogWeights
import HeckeGeneral.Analysis.IdealEulerProduct
import HeckeGeneral.Arithmetic.IdealFactorization

/-!
# Absolutely convergent logarithmic prime-power sums

The prime powers are embedded injectively into actual nonzero integral ideals.
The exponent is n+1: including exponent zero separately for every prime would
incorrectly count the unit ideal infinitely many times. Summability comes from
the already proved ideal logarithmic majorant, rather than a new hypothesis.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Topology Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- The actual positive prime power corresponding to a prime and a natural index. -/
def primePowerIdeal (pn : HeightOneSpectrum (𝓞 K) × ℕ) : NonzeroIdeal K :=
  idealOfPrimeExponents (Finsupp.single pn.1 (pn.2 + 1))

@[simp] theorem primePowerIdeal_val (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    (primePowerIdeal K pn).val = pn.1.asIdeal ^ (pn.2 + 1) :=
  idealOfPrimeExponents_single pn.1 (pn.2 + 1)

/-- Distinct primes or distinct positive exponents give distinct integral ideals. -/
theorem primePowerIdeal_injective : Function.Injective (primePowerIdeal K) := by
  intro x y h
  have he := congrArg primeExponents h
  simp only [primePowerIdeal, primeExponents_idealOfPrimeExponents_single] at he
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp he with ⟨hp, hn⟩ | ⟨hz, _⟩
  · exact Prod.ext hp (Nat.add_right_cancel hn)
  · exact (Nat.succ_ne_zero x.2 hz).elim

theorem idealNorm_primePowerIdeal (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    idealNorm K (primePowerIdeal K pn) = (Ideal.absNorm pn.1.asIdeal : ℝ) ^ (pn.2 + 1) := by
  simp only [idealNorm, primePowerIdeal_val, map_pow, Nat.cast_pow]

theorem log_idealNorm_primePowerIdeal (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    Real.log (idealNorm K (primePowerIdeal K pn)) =
      (pn.2 + 1 : ℕ) * Real.log (Ideal.absNorm pn.1.asIdeal : ℝ) := by
  rw [idealNorm_primePowerIdeal, Real.log_pow]

theorem prime_log_nonneg (p : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Real.log (Ideal.absNorm p.asIdeal : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast (one_lt_primeIdeal_absNorm K p).le

theorem prime_log_le_log_primePower (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    Real.log (Ideal.absNorm pn.1.asIdeal : ℝ) ≤
      Real.log (idealNorm K (primePowerIdeal K pn)) := by
  rw [log_idealNorm_primePowerIdeal]
  have hn : (1 : ℝ) ≤ (pn.2 + 1 : ℕ) := by exact_mod_cast Nat.succ_pos pn.2
  nlinarith [prime_log_nonneg K pn.1]

/-- The unsigned logarithmic prime-power term used in logarithmic derivative expansions. -/
def primePowerLogTerm (a : HeightOneSpectrum (𝓞 K) → ℂ) (k : ℕ) (s : ℂ)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  (Real.log (Ideal.absNorm pn.1.asIdeal : ℝ) : ℂ) ^ k *
    primeIdealRatio K a s pn.1 ^ (pn.2 + 1)

def primePowerLogSeries (a : HeightOneSpectrum (𝓞 K) → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' pn, primePowerLogTerm K a k s pn

theorem primePower_dirichletTerm (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    dirichletTerm (idealNorm K) (nonzeroIdealCoefficient a) s (primePowerIdeal K pn) =
      primeIdealRatio K a s pn.1 ^ (pn.2 + 1) := by
  rw [← idealEulerWeight_nonzero, primePowerIdeal_val, idealEulerWeight_prime_pow]

/-- The prime-power logarithm is bounded by the logarithm of the full ideal norm. -/
theorem norm_primePowerLogTerm_le_idealLogTerm
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (k : ℕ) (s : ℂ)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    ‖primePowerLogTerm K a k s pn‖ ≤
      ‖idealLogTerm K (nonzeroIdealCoefficient a) k s (primePowerIdeal K pn)‖ := by
  unfold primePowerLogTerm
  rw [← primePower_dirichletTerm K a s pn, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (prime_log_nonneg K pn.1)]
  calc
    _ ≤ Real.log (idealNorm K (primePowerIdeal K pn)) ^ k *
        ‖dirichletTerm (idealNorm K) (nonzeroIdealCoefficient a) s (primePowerIdeal K pn)‖ :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (prime_log_nonneg K pn.1) (prime_log_le_log_primePower K pn) k)
        (norm_nonneg _)
    _ = _ := by
      rw [norm_idealLogTerm,
        norm_dirichletTerm (idealNorm K) (nonzeroIdealCoefficient a) s
          (primePowerIdeal K pn) (idealNorm_pos K (primePowerIdeal K pn))]

/-- Absolute summability over all actual primes and all positive powers. -/
theorem absolutelySummable_primePowerLogTerm (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pn => ‖primePowerLogTerm K a k s pn‖) := by
  have hmajor := (absolutelySummable_idealLogTerm K (nonzeroIdealCoefficient a)
    (norm_nonzeroIdealCoefficient_le_one a ha) k hs).comp_injective (primePowerIdeal_injective K)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_primePowerLogTerm_le_idealLogTerm K a k s) hmajor

/-- Each local positive-power sum has its actual geometric value. -/
theorem hasSum_primePowerLogTerm_local (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re)
    (p : HeightOneSpectrum (𝓞 K)) :
    HasSum (fun n : ℕ => primePowerLogTerm K a k s (p, n))
      ((Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℂ) ^ k *
        primeIdealRatio K a s p / (1 - primeIdealRatio K a s p)) := by
  have hgeo := (hasSum_geometric_of_norm_lt_one
    (norm_primeIdealRatio_lt_one K a ha hs p)).mul_left
      ((Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℂ) ^ k * primeIdealRatio K a s p)
  simpa only [primePowerLogTerm, pow_succ, mul_assoc, mul_comm, mul_left_comm,
    div_eq_mul_inv] using hgeo

/-- The prime-power double sum can be collapsed to a convergent sum over primes. -/
theorem hasSum_primePowerLog_localValues (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p => (Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℂ) ^ k *
      primeIdealRatio K a s p / (1 - primeIdealRatio K a s p))
      (primePowerLogSeries K a k s) :=
  (absolutelySummable_primePowerLogTerm K a ha k hs).of_norm.hasSum.prod_fiberwise
    (hasSum_primePowerLogTerm_local K a ha k hs)

theorem primePowerLogSeries_eq_prime_sum (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    primePowerLogSeries K a k s =
      ∑' p, (Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℂ) ^ k *
        primeIdealRatio K a s p / (1 - primeIdealRatio K a s p) :=
  (hasSum_primePowerLog_localValues K a ha k hs).tsum_eq.symm

end HeckeGeneral.Analysis
