import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

/-!
# The arithmetic part of the detector over an arbitrary number field

The cutoff coefficient is an explicit sum over the squarefree divisors of an
actual ideal, represented by subsets of its actual prime support. All
coefficients are the genuine unique-factorization Moebius coefficients.
There is no assumption that elements have unique factorization.

This file proves the cancellation below the truncation scale and the exact
terminal-defect identity. Analytic smallness of the two error terms is not
asserted here. The construction accommodates multiplicative weights with
ramified zeros.
-/

noncomputable section
namespace ExpansionDetector.IdealCutoff

open UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- Finite support of the actual prime ideal factorization. -/
def primeSupport (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (normalizedFactors I).toFinset

lemma support_prime {I P : Ideal (𝓞 K)} (hP : P ∈ primeSupport I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma support_product_ne_zero {I : Ideal (𝓞 K)} {A : Finset (Ideal (𝓞 K))}
    (hA : A ⊆ primeSupport I) : (∏ P ∈ A, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ hP => (support_prime (hA hP)).ne_zero)

lemma factors_support_product {I : Ideal (𝓞 K)} {A : Finset (Ideal (𝓞 K))}
    (hA : A ⊆ primeSupport I) : normalizedFactors (∏ P ∈ A, P) = A.val := by
  have hp : ∀ P ∈ A.val, Prime P := fun P hP => support_prime (hA hP)
  simpa using normalizedFactors_prod_of_prime hp

lemma squarefree_support_product {I : Ideal (𝓞 K)} {A : Finset (Ideal (𝓞 K))}
    (hA : A ⊆ primeSupport I) : Squarefree (∏ P ∈ A, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hA)).mpr
  rw [factors_support_product hA]
  exact A.nodup

lemma support_product_dvd {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    {A : Finset (Ideal (𝓞 K))} (hA : A ⊆ primeSupport I) : (∏ P ∈ A, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors
    (support_product_ne_zero hA) hI).mpr
  rw [factors_support_product hA]
  apply (Multiset.le_iff_subset A.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hA hP)

lemma moebius_support_product {I : Ideal (𝓞 K)} {A : Finset (Ideal (𝓞 K))}
    (hA : A ⊆ primeSupport I) :
    (moebius (∏ P ∈ A, P) : ℂ) = (-1 : ℂ) ^ A.card := by
  rw [(squarefree_support_product hA).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hA]
  simp

lemma primeSupport_empty_iff (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    primeSupport I = ∅ ↔ I = 1 := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := Multiset.toFinset_eq_empty.mp h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    exact hp.symm
  · rintro rfl
    simp [primeSupport, ← Ideal.one_eq_top]

lemma sum_subset_sign {α : Type*} (T : Finset α) :
    (∑ A ∈ T.powerset, (-1 : ℂ) ^ A.card) = if T = ∅ then 1 else 0 := by
  have h : ((∑ A ∈ T.powerset, (-1 : ℤ) ^ A.card : ℤ) : ℂ) =
      ((if T = ∅ then 1 else 0 : ℤ) : ℂ) := by
    rw [Finset.sum_powerset_neg_one_pow_card]
  push_cast at h
  exact h

/-- Squarefree divisor parametrization of the truncated Moebius convolution. -/
def coefficient (V : ℝ → ℂ) (D : ℝ) (I : Ideal (𝓞 K)) : ℂ :=
  if I = 0 then 0 else
    ∑ A ∈ (primeSupport I).powerset,
      (moebius (∏ P ∈ A, P) : ℂ) *
        V ((Ideal.absNorm (∏ P ∈ A, P) : ℝ) / D)

@[simp] lemma coefficient_zero (V : ℝ → ℂ) (D : ℝ) :
    coefficient V D (0 : Ideal (𝓞 K)) = 0 := by simp [coefficient]

lemma divisor_norm_le {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    {A : Finset (Ideal (𝓞 K))} (hA : A ⊆ primeSupport I) :
    Ideal.absNorm (∏ P ∈ A, P) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (support_product_dvd hI hA))

lemma two_le_norm_of_prime {P : Ideal (𝓞 K)} (hP : Prime P) :
    2 ≤ Ideal.absNorm P := by
  have hp : 0 < Ideal.absNorm P :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
  have hn : Ideal.absNorm P ≠ 1 := by
    intro he
    have htop := Ideal.absNorm_eq_one_iff.mp he
    exact hP.ne_one (by simpa only [← Ideal.one_eq_top] using htop)
  omega

/-- A deliberately crude divisor estimate, sufficient because the smooth
scale is U^20. It is proved for actual ideal factorizations. -/
lemma support_card_pow_le_norm (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    2 ^ (primeSupport I).card ≤ Ideal.absNorm I := by
  calc
    _ = ∏ P ∈ primeSupport I, (2 : ℕ) := by simp
    _ ≤ ∏ P ∈ primeSupport I, Ideal.absNorm P :=
      Finset.prod_le_prod (fun P hP => two_le_norm_of_prime (support_prime hP))
    _ = Ideal.absNorm (∏ P ∈ primeSupport I, P) := (map_prod Ideal.absNorm _ _).symm
    _ ≤ Ideal.absNorm I := divisor_norm_le hI (fun _ h => h)

/-- The explicit truncated convolution has size at most the ideal norm;
no divisor asymptotic is needed for the exponential tail. -/
theorem norm_coefficient_le_norm (V : ℝ → ℂ) (D : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) (I : Ideal (𝓞 K)) :
    ‖coefficient V D I‖ ≤ (Ideal.absNorm I : ℝ) := by
  by_cases hI : I = 0
  · simp [hI, coefficient]
  rw [coefficient, if_neg hI]
  calc
    _ ≤ ∑ A ∈ (primeSupport I).powerset,
        ‖(moebius (∏ P ∈ A, P) : ℂ) *
          V ((Ideal.absNorm (∏ P ∈ A, P) : ℝ) / D)‖ := norm_sum_le _ _
    _ ≤ ∑ A ∈ (primeSupport I).powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      rw [moebius_support_product (Finset.mem_powerset.mp hA), norm_mul]
      simpa using hV ((Ideal.absNorm (∏ P ∈ A, P) : ℝ) / D)
    _ = ((2 : ℕ) ^ (primeSupport I).card : ℝ) := by simp
    _ ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast support_card_pow_le_norm I hI

/-- The smoothed inverse agrees with the exact convolution at every ideal
below D. This includes the unit ideal and the zero ideal conventions. -/
theorem coefficient_small (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (I : Ideal (𝓞 K)) (hI : (Ideal.absNorm I : ℝ) ≤ D) :
    coefficient V D I = if I = 1 then 1 else 0 := by
  by_cases hI0 : I = 0
  · simp [hI0, coefficient]
  rw [coefficient, if_neg hI0]
  calc
    _ = ∑ A ∈ (primeSupport I).powerset, (-1 : ℂ) ^ A.card := by
      apply Finset.sum_congr rfl
      intro A hA
      have hsub := Finset.mem_powerset.mp hA
      rw [moebius_support_product hsub,
        hV _ (div_nonneg (by positivity) hD.le) ((div_le_one hD).mpr ?_), mul_one]
      exact (by exact_mod_cast divisor_norm_le hI0 hsub :
        (Ideal.absNorm (∏ P ∈ A, P) : ℝ) ≤ Ideal.absNorm I).trans hI
    _ = if I = 1 then 1 else 0 := by
      rw [sum_subset_sign]
      simp only [primeSupport_empty_iff I hI0]

/-- Deleting the initial range removes exactly the unit coefficient. -/
theorem coefficient_tail (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (I : Ideal (𝓞 K)) :
    coefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      coefficient V D I - if I = 1 then 1 else 0 := by
  have hD0 : 0 < D := by linarith
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ D
  · rw [coefficient_small V D hD0 hV I hI]
    by_cases hI1 : I = 1
    · subst I
      simp only [map_one, Nat.cast_one, mul_one, if_true, one_mul, sub_self]
      rw [hV _ (by positivity) ((div_le_one hD0).mpr hD), sub_self]
    · simp only [if_neg hI1, zero_mul, sub_zero]
  · have hv : V (2 * (Ideal.absNorm I : ℝ) / D) = 0 := by
      apply hVzero
      apply (le_div_iff₀ hD0).mpr
      linarith [lt_of_not_ge hI]
    have hI1 : I ≠ 1 := by
      intro hh
      subst I
      simp only [map_one, Nat.cast_one] at hI
      linarith
    rw [hv, sub_zero, mul_one, if_neg hI1, sub_zero]

/-- `w` may be an actual Hecke ideal weight with ramified zero extensions. -/
def smoothedTerm (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ)
    (D : ℝ) (kernel : ℕ → ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  coefficient V D I * w I * kernel (Ideal.absNorm I)

def terminalTerm (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ)
    (D H : ℝ) (kernel : ℕ → ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  smoothedTerm w V D kernel I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) *
    T ((Ideal.absNorm I : ℝ) / H)

def terminalRemainder (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ)
    (D H : ℝ) (kernel : ℕ → ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  smoothedTerm w V D kernel I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) *
    (1 - T ((Ideal.absNorm I : ℝ) / H))

theorem smoothedTerm_tail (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ)
    (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (kernel : ℕ → ℂ) (I : Ideal (𝓞 K)) :
    smoothedTerm w V D kernel I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      smoothedTerm w V D kernel I - if I = 1 then kernel 1 else 0 := by
  have h := coefficient_tail V D hD hV hVzero I
  unfold smoothedTerm
  calc
    _ = (coefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) *
        w I * kernel (Ideal.absNorm I) := by ring
    _ = _ := by
      rw [h]
      by_cases hI : I = 1
      · subst I
        simp only [if_true, map_one, mul_one]
        ring
      · simp only [if_neg hI, sub_zero]

/-- An exact finite identity: the source polynomial is the smoothed
convolution, minus the unit term, minus the terminal tail. -/
theorem finite_terminal_identity (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ)
    (D H : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (kernel : ℕ → ℂ) (S : Finset (Ideal (𝓞 K))) (hS : 1 ∈ S) :
    (∑ I ∈ S, terminalTerm w V T D H kernel I) =
      (∑ I ∈ S, smoothedTerm w V D kernel I) - kernel 1 -
        ∑ I ∈ S, terminalRemainder w V T D H kernel I := by
  have hterm (I : Ideal (𝓞 K)) :
      terminalTerm w V T D H kernel I =
        smoothedTerm w V D kernel I - (if I = 1 then kernel 1 else 0) -
          terminalRemainder w V T D H kernel I := by
    have h := smoothedTerm_tail w V D hD hV hVzero kernel I
    unfold terminalTerm terminalRemainder
    rw [← h]
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos hS]

/-- The missing analytic input is exposed as two SMALL ERRORS, not as an
already constructed witness. Every polynomial in the conclusion is explicit. -/
theorem finite_terminal_lower (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ)
    (D H : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (kernel : ℕ → ℂ) (S : Finset (Ideal (𝓞 K))) (hS : 1 ∈ S)
    (ε₁ ε₂ c : ℝ)
    (hunit : c + ε₁ + ε₂ ≤ ‖kernel 1‖)
    (hcontour : ‖∑ I ∈ S, smoothedTerm w V D kernel I‖ ≤ ε₁)
    (htail : ‖∑ I ∈ S, terminalRemainder w V T D H kernel I‖ ≤ ε₂) :
    c ≤ ‖∑ I ∈ S, terminalTerm w V T D H kernel I‖ := by
  have hi := finite_terminal_identity w V T D H hD hV hVzero kernel S hS
  have he : kernel 1 = (∑ I ∈ S, smoothedTerm w V D kernel I) -
      (∑ I ∈ S, terminalRemainder w V T D H kernel I) -
        (∑ I ∈ S, terminalTerm w V T D H kernel I) := by rw [hi]; ring
  have hn := norm_sub_le
    ((∑ I ∈ S, smoothedTerm w V D kernel I) -
      ∑ I ∈ S, terminalRemainder w V T D H kernel I)
    (∑ I ∈ S, terminalTerm w V T D H kernel I)
  rw [← he] at hn
  have hn' := norm_sub_le (∑ I ∈ S, smoothedTerm w V D kernel I)
    (∑ I ∈ S, terminalRemainder w V T D H kernel I)
  linarith

end ExpansionDetector.IdealCutoff
