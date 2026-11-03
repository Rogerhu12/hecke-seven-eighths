import HeckeGeneral.Arithmetic.IdealCoefficients
import HeckeGeneral.Analysis.IdealDirichlet
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Finite Euler expansions and convergence of the actual prime-ideal product

The indices below are height-one prime ideals of the ring of integers, not
natural-number primes. Finite products are expanded into coefficients at
actual products of prime ideal powers. Bounded prime coefficients give
absolute convergence of the ideal series and convergence to a nonzero value
of the prime-ideal product on `Re s > 1`.

The identification with the ideal series is proved in `IdealEulerIdentity`
by passage from finite prime-supported sums to all ideals. That argument is
separate from the local factors here; Mathlib's existing Euler-product
identity is specific to the natural numbers.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped BigOperators nonZeroDivisors Topology Classical

variable (K : Type*) [Field K] [NumberField K]

/-- The actual Dirichlet weight, extended to all integral ideals. -/
def idealEulerWeight (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (I : Ideal (𝓞 K)) : ℂ :=
  idealCoefficient a I * (Ideal.absNorm I : ℂ) ^ (-s)

theorem idealEulerWeight_one (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) :
    idealEulerWeight K a s 1 = 1 := by
  unfold idealEulerWeight
  rw [idealCoefficient_one, map_one]
  simp

theorem idealEulerWeight_mul (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (I J : Ideal (𝓞 K)) :
    idealEulerWeight K a s (I * J) =
      idealEulerWeight K a s I * idealEulerWeight K a s J := by
  simp only [idealEulerWeight, idealCoefficient_mul, map_mul, Nat.cast_mul]
  rw [Complex.natCast_mul_natCast_cpow]
  ring

/-- Multiplicativity uses actual ideal multiplication and actual absolute norm. -/
def idealEulerWeightHom (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) :
    Ideal (𝓞 K) →* ℂ where
  toFun := idealEulerWeight K a s
  map_one' := idealEulerWeight_one K a s
  map_mul' := idealEulerWeight_mul K a s

def primeIdealRatio (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  a p * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s)

theorem idealEulerWeight_prime (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (p : HeightOneSpectrum (𝓞 K)) :
    idealEulerWeight K a s p.asIdeal = primeIdealRatio K a s p := by
  simp [idealEulerWeight, primeIdealRatio]

theorem idealEulerWeight_prime_pow (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (p : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    idealEulerWeight K a s (p.asIdeal ^ n) = primeIdealRatio K a s p ^ n := by
  change idealEulerWeightHom K a s (p.asIdeal ^ n) = _
  rw [map_pow]
  exact congrArg (fun z : ℂ => z ^ n) (idealEulerWeight_prime K a s p)

def primeNonzeroIdeal (p : HeightOneSpectrum (𝓞 K)) : NonzeroIdeal K :=
  ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩

omit [NumberField K] in
theorem primeNonzeroIdeal_injective : Function.Injective (primeNonzeroIdeal K) := by
  intro p q h
  exact HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h)

theorem idealEulerWeight_nonzero (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (I : NonzeroIdeal K) :
    idealEulerWeight K a s I.val =
      dirichletTerm (idealNorm K) (nonzeroIdealCoefficient a) s I := by
  simp [idealEulerWeight, dirichletTerm, idealNorm, nonzeroIdealCoefficient]

/-- A finite prime set with exponents in `Fin n` gives a genuine finite
Euler expansion, including the coefficient at every resulting integral ideal. -/
theorem finite_idealEuler_expansion (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (∏ p : S, ∑ e : Fin n, primeIdealRatio K a s p.val ^ e.val) =
      ∑ e : S → Fin n,
        idealEulerWeight K a s (∏ p : S, p.val.asIdeal ^ (e p).val) := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro e _
  change _ = idealEulerWeightHom K a s _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p _
  exact (idealEulerWeight_prime_pow K a s p.val (e p).val).symm

theorem one_lt_primeIdeal_absNorm (p : HeightOneSpectrum (𝓞 K)) :
    1 < Ideal.absNorm p.asIdeal := by
  have hp := Ideal.absNorm_pos_of_nonZeroDivisors (primeNonzeroIdeal K p)
  have hn : Ideal.absNorm p.asIdeal ≠ 1 := by
    intro hn
    exact p.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp hn)
  exact lt_of_le_of_ne (Nat.succ_le_iff.mpr hp) hn.symm

theorem norm_primeIdealRatio_lt_one (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (p : HeightOneSpectrum (𝓞 K)) : ‖primeIdealRatio K a s p‖ < 1 := by
  have hq : (1 : ℝ) < Ideal.absNorm p.asIdeal := by
    exact_mod_cast one_lt_primeIdeal_absNorm K p
  have hqpos : (0 : ℝ) < Ideal.absNorm p.asIdeal := lt_trans zero_lt_one hq
  have hcast : (Ideal.absNorm p.asIdeal : ℂ) = ((Ideal.absNorm p.asIdeal : ℝ) : ℂ) := by
    simp
  rw [primeIdealRatio, norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
  simp only [Complex.neg_re]
  calc
    ‖a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-s.re) ≤
        1 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (ha p) (Real.rpow_nonneg hqpos.le _)
    _ < 1 := by
      rw [one_mul]
      exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)

theorem primeIdealFactor_denominator_ne_zero (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (p : HeightOneSpectrum (𝓞 K)) : 1 - primeIdealRatio K a s p ≠ 0 := by
  intro h
  have heq := sub_eq_zero.mp h
  have hn := norm_primeIdealRatio_lt_one K a ha hs p
  rw [← heq, norm_one] at hn
  exact (lt_irrefl 1 hn)

/-- The local series is genuinely convergent; it sums the actual prime-ideal
powers with their Dirichlet weights. -/
theorem hasSum_primeIdeal_powers (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (p : HeightOneSpectrum (𝓞 K)) :
    HasSum (fun n : ℕ => idealEulerWeight K a s (p.asIdeal ^ n))
      (1 - primeIdealRatio K a s p)⁻¹ := by
  simpa only [idealEulerWeight_prime_pow] using
    hasSum_geometric_of_norm_lt_one (norm_primeIdealRatio_lt_one K a ha hs p)

theorem finite_primeIdeal_local_series (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∏ p ∈ S, ∑' n : ℕ, idealEulerWeight K a s (p.asIdeal ^ n)) =
      ∏ p ∈ S, (1 - primeIdealRatio K a s p)⁻¹ := by
  apply Finset.prod_congr rfl
  intro p _
  exact (hasSum_primeIdeal_powers K a ha hs p).tsum_eq

theorem finite_primeIdeal_factors_ne_zero (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∏ p ∈ S, (1 - primeIdealRatio K a s p)⁻¹) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p _ =>
    inv_ne_zero (primeIdealFactor_denominator_ne_zero K a ha hs p))

theorem absolutelySummable_idealEulerWeight (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : NonzeroIdeal K => ‖idealEulerWeight K a s I.val‖) := by
  simpa only [idealEulerWeight_nonzero] using
    absolutelySummable_idealDirichlet K (nonzeroIdealCoefficient a)
      (norm_nonzeroIdealCoefficient_le_one a ha) hs

set_option maxHeartbeats 800000 in
theorem absolutelySummable_primeIdealRatio (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p => ‖primeIdealRatio K a s p‖) := by
  have h : Summable ((fun I : NonzeroIdeal K => ‖idealEulerWeight K a s I.val‖) ∘
      primeNonzeroIdeal K) :=
    (absolutelySummable_idealEulerWeight K a ha hs).comp_injective
      (primeNonzeroIdeal_injective K)
  apply h.congr
  intro p
  exact congrArg norm (idealEulerWeight_prime K a s p)

/-- An explicit value of the convergent prime-ideal product. Its equality
with the ideal Dirichlet series is proved in `IdealEulerIdentity`. -/
def primeIdealEulerValue (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (∑' p, -Complex.log (1 - primeIdealRatio K a s p))

theorem hasProd_primeIdeal_factors (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p => (1 - primeIdealRatio K a s p)⁻¹)
      (primeIdealEulerValue K a s) := by
  have hsum := (absolutelySummable_primeIdealRatio K a ha hs).of_norm
  have hlog := Complex.summable_log_one_add_of_summable hsum.neg
  have hlog' : Summable (fun p => -Complex.log (1 - primeIdealRatio K a s p)) := by
    simpa only [sub_eq_add_neg] using hlog.neg
  apply hlog'.hasSum.cexp.congr
  intro S
  apply Finset.prod_congr rfl
  intro p _
  simp only [Function.comp_apply, Complex.exp_neg,
    Complex.exp_log (primeIdealFactor_denominator_ne_zero K a ha hs p)]

theorem primeIdealEulerValue_ne_zero (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) :
    primeIdealEulerValue K a s ≠ 0 := Complex.exp_ne_zero _

theorem tprod_primeIdeal_factors_ne_zero (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∏' p, (1 - primeIdealRatio K a s p)⁻¹) ≠ 0 := by
  rw [(hasProd_primeIdeal_factors K a ha hs).tprod_eq]
  exact primeIdealEulerValue_ne_zero K a s

end HeckeGeneral.Analysis
