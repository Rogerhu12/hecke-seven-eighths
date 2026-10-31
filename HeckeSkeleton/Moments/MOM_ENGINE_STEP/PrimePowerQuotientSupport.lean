import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierValuationSupport
import HeckePort.Moments.Descent.Quotients

/-!
# Exact plain quotients after an amplification valuation allocation

An exact valuation n forces p^n to divide the original plain ideal.
The quotient has valuation zero, proved from normalized-factor counts.
The complete paired error polynomial is therefore reindexed on two
genuine quotient supports and the actual live prime slots, retaining
the same whole coefficient on the reconstructed original tuple.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace HeckeSkeleton.Moments.EngineStep.PrimePowerQuotientSupport

open HeckePort.Moments AmplifierValuationSupport
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]

theorem prime_power_dvd_of_count (p : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hc : (normalizedFactors I).count p.asIdeal = n) : p.asIdeal ^ n ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors
    (pow_ne_zero n p.ne_bot) hI).mpr
  rw [p.irreducible.normalizedFactors_pow, normalize_eq]
  exact Multiset.le_count_iff_replicate_le.mp hc.ge

theorem count_prime_power_mul (p : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (J : Ideal (𝓞 K)) (hJ : J ≠ 0) :
    (normalizedFactors (p.asIdeal ^ n * J)).count p.asIdeal =
      n + (normalizedFactors J).count p.asIdeal := by
  rw [normalizedFactors_mul (pow_ne_zero n p.ne_bot) hJ, Multiset.count_add,
    p.irreducible.normalizedFactors_pow, normalize_eq]
  simp

def primitiveQuotient (p : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (S : Finset (Ideal (𝓞 K))) : Finset (Ideal (𝓞 K)) :=
  (quotientSupport (p.asIdeal ^ n) S).filter
    (fun J => (normalizedFactors J).count p.asIdeal = 0)

theorem quotient_exact_eq_filter (p : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ I ∈ S, I ≠ 0) :
    quotientSupport (p.asIdeal ^ n)
      (S.filter (fun I => (normalizedFactors I).count p.asIdeal = n)) =
      primitiveQuotient p n S := by
  ext J
  simp only [primitiveQuotient, mem_quotientSupport _ _ (pow_ne_zero n p.ne_bot),
    Finset.mem_filter]
  by_cases hm : p.asIdeal ^ n * J ∈ S
  · have hJ : J ≠ 0 := (mul_ne_zero_iff.mp (hS _ hm)).2
    rw [count_prime_power_mul p n J hJ]
    simp only [hm, true_and]
    omega
  · simp only [hm, false_and]

theorem sum_exact_quotients (p : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ I ∈ S, I ≠ 0) (C : Ideal (𝓞 K) → ℂ) :
    (∑ I ∈ S with (normalizedFactors I).count p.asIdeal = n, C I) =
      ∑ J ∈ primitiveQuotient p n S, C (p.asIdeal ^ n * J) := by
  have hf :
      (S.filter (fun I => (normalizedFactors I).count p.asIdeal = n)).filter
        (fun I => p.asIdeal ^ n ∣ I) =
      S.filter (fun I => (normalizedFactors I).count p.asIdeal = n) := by
    apply Finset.filter_eq_self.mpr
    intro I hI
    exact prime_power_dvd_of_count p n I (hS I (Finset.mem_filter.mp hI).1)
      (Finset.mem_filter.mp hI).2
  calc
    _ = ∑ I ∈ S.filter (fun I => (normalizedFactors I).count p.asIdeal = n)
        with p.asIdeal ^ n ∣ I, C I := by rw [hf]
    _ = ∑ J ∈ quotientSupport (p.asIdeal ^ n)
        (S.filter (fun I => (normalizedFactors I).count p.asIdeal = n)),
        C (p.asIdeal ^ n * J) := sum_quotientSupport _ _ _
    _ = _ := by rw [quotient_exact_eq_filter p n S hS]

theorem paired_exact_plain_quotients {P : Type*} {k : ℕ}
    (p : HeightOneSpectrum (𝓞 K)) (n₁ n₂ : ℕ)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset P)
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ J ∈ S₂, J ≠ 0)
    (C : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → P) → ℂ) :
    (∑ x ∈ childCartesianColumns
      (S₁.filter (fun I => (normalizedFactors I).count p.asIdeal = n₁))
      (S₂.filter (fun J => (normalizedFactors J).count p.asIdeal = n₂)) S, C x) =
      ∑ y ∈ childCartesianColumns (primitiveQuotient p n₁ S₁)
        (primitiveQuotient p n₂ S₂) S,
        C ((p.asIdeal ^ n₁ * y.1.1, p.asIdeal ^ n₂ * y.1.2), y.2) := by
  simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.sum_product]
  rw [sum_exact_quotients p n₁ S₁ hS₁]
  apply Finset.sum_congr rfl
  intro I _
  rw [sum_exact_quotients p n₂ S₂ hS₂]

theorem actual_error_polynomial_quotient_subsupport {k : ℕ}
    (p : HeightOneSpectrum (𝓞 K)) (n : Fin (k + 2) → ℕ)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ J ∈ S₂, J ≠ 0)
    (frozen : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)))
    (hfrozen : frozen ∈ pairedColumns p n S₁ S₂ S id id)
    (C : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ x ∈ pairedColumns p n S₁ S₂ S id id, C x) =
      ∑ y ∈ childCartesianColumns
        (primitiveQuotient p (n 0) S₁)
        (primitiveQuotient p (n (Fin.succ 0)) S₂)
        (fun j => (S (selectedSlotIndex (liveSlots n) j)).erase p),
        C ((p.asIdeal ^ n 0 * y.1.1, p.asIdeal ^ n (Fin.succ 0) * y.1.2),
          SlotRestriction.extend (liveSlots n) (fun _ => p) y.2) := by
  rw [actual_error_polynomial_subsupport p n S₁ S₂ S id id frozen hfrozen C]
  exact paired_exact_plain_quotients p (n 0) (n (Fin.succ 0)) S₁ S₂
    (fun j => (S (selectedSlotIndex (liveSlots n) j)).erase p) hS₁ hS₂
    (fun y => C (y.1, SlotRestriction.extend (liveSlots n) (fun _ => p) y.2))

end HeckeSkeleton.Moments.EngineStep.PrimePowerQuotientSupport

#print axioms HeckeSkeleton.Moments.EngineStep.PrimePowerQuotientSupport.sum_exact_quotients
#print axioms HeckeSkeleton.Moments.EngineStep.PrimePowerQuotientSupport.actual_error_polynomial_quotient_subsupport
