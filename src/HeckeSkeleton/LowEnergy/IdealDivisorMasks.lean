import HeckeSkeleton.LowEnergy.SquarefreeFibers
import HeckeSkeleton.LowEnergy.KeepOriginalRow
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius

/-!
# Actual finite ideal divisors and exact squarefree moving masks

The divisor finset is defined from Mathlib's finite ideal norm ball.  Its
membership criterion and the complete inclusion-exclusion identity are
proved here, so this module has no dependency on the missing upstream
`DedekindZetaZeroFree` divisor package.  The coefficients are Mathlib's actual ideal Moebius function.  The finite
cancellation is proved from the prime-support powerset, and its norm bound
is derived directly from the definition.
-/

namespace HeckeSkeleton.LowEnergy.IdealDivisorMasks

open NumberField Ideal UniqueFactorizationMonoid
open HeckeSkeleton.LowEnergy KeepOriginalRow
open scoped NumberField Classical BigOperators
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def divisors (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).toFinset.filter
    (fun J => J ∣ I)

theorem mem_divisors (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    J ∈ divisors I ↔ J ∣ I := by
  simp only [divisors, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · exact And.right
  · intro hJI
    refine ⟨?_, hJI⟩
    exact Nat.le_of_dvd
      (Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)))
      (map_dvd Ideal.absNorm hJI)

def sign (I : Ideal (𝓞 K)) : ℂ := (moebius I : ℂ)

theorem sign_norm (I : Ideal (𝓞 K)) : ‖sign I‖ ≤ 1 := by
  unfold sign UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

theorem squarefree_support_product {I : Ideal (𝓞 K)}
    {s : Finset (Ideal (𝓞 K))} (hs : s ⊆ idealPrimeSupport K I) :
    Squarefree (∏ P ∈ s, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (ideal_support_product_ne_zero K hs)).mpr
  rw [ideal_factors_support_product K hs]
  exact s.nodup

theorem support_product_injective {I : Ideal (𝓞 K)}
    {s t : Finset (Ideal (𝓞 K))}
    (hs : s ⊆ idealPrimeSupport K I) (ht : t ⊆ idealPrimeSupport K I)
    (he : (∏ P ∈ s, P) = ∏ P ∈ t, P) : s = t := by
  have hf := congrArg normalizedFactors he
  rw [ideal_factors_support_product K hs, ideal_factors_support_product K ht] at hf
  exact Finset.val_inj.mp hf

theorem sign_support_product {I : Ideal (𝓞 K)}
    {s : Finset (Ideal (𝓞 K))} (hs : s ⊆ idealPrimeSupport K I) :
    sign (∏ P ∈ s, P) = (-1 : ℂ) ^ s.card := by
  rw [sign, (squarefree_support_product hs).moebius_eq, factors_eq_normalizedFactors,
    ideal_factors_support_product K hs]
  simp

theorem squarefree_divisors_eq_image (I : Ideal (𝓞 K)) (hI : Squarefree I) :
    divisors I = (idealPrimeSupport K I).powerset.image (fun s => ∏ P ∈ s, P) := by
  ext J
  rw [mem_divisors I J hI.ne_zero]
  simp only [Finset.mem_image, Finset.mem_powerset]
  constructor
  · intro hJI
    have hJ := Squarefree.squarefree_of_dvd hJI hI
    exact ⟨idealPrimeSupport K J,
      idealPrimeSupport_mono_of_dvd K hI.ne_zero hJ.ne_zero hJI,
      squarefree_ideal_support_product K hJ⟩
  · rintro ⟨s, hs, rfl⟩
    exact ideal_support_product_dvd K hI.ne_zero hs

theorem support_empty_iff (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    idealPrimeSupport K I = ∅ ↔ I = ⊤ := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := Multiset.toFinset_eq_empty.mp h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    simpa only [Ideal.one_eq_top] using hp.symm
  · intro h
    subst I
    simp [idealPrimeSupport, ← Ideal.one_eq_top]

theorem sum_subset_sign {α : Type*} (s : Finset α) :
    (∑ t ∈ s.powerset, (-1 : ℂ) ^ t.card) = if s = ∅ then 1 else 0 := by
  have h : ((∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card : ℤ) : ℂ) =
      ((if s = ∅ then 1 else 0 : ℤ) : ℂ) := by
    rw [Finset.sum_powerset_neg_one_pow_card]
  push_cast at h
  exact h

theorem sum_sign_divisors (I : Ideal (𝓞 K)) (hI : Squarefree I) :
    (∑ J ∈ divisors I, sign J) = if I = ⊤ then 1 else 0 := by
  rw [squarefree_divisors_eq_image I hI, Finset.sum_image]
  · have he : (∑ s ∈ (idealPrimeSupport K I).powerset, sign (∏ P ∈ s, P)) =
        ∑ s ∈ (idealPrimeSupport K I).powerset, (-1 : ℂ) ^ s.card := by
      apply Finset.sum_congr rfl
      intro s hs
      exact sign_support_product (Finset.mem_powerset.mp hs)
    rw [he, sum_subset_sign]
    simp only [support_empty_iff I hI.ne_zero]
  · intro s hs t ht he
    exact support_product_injective (Finset.mem_powerset.mp hs)
      (Finset.mem_powerset.mp ht) he

/-- Both sides are actual ideal coprimality; no quotient model is used. -/
theorem coprime_mask_expansion (k n : Ideal (𝓞 K)) (hk : Squarefree k) :
    mask k n = ∑ D ∈ divisors k, if D ∣ n then sign D else 0 := by
  let g : Ideal (𝓞 K) := k ⊔ n
  have hgs : Squarefree g := Squarefree.squarefree_of_dvd
    (show g ∣ k from Ideal.dvd_iff_le.mpr le_sup_left) hk
  have he : (divisors k).filter (fun D => D ∣ n) = divisors g := by
    ext D
    simp only [Finset.mem_filter, mem_divisors k D hk.ne_zero,
      mem_divisors g D hgs.ne_zero, Ideal.dvd_iff_le, g, sup_le_iff]
  rw [← Finset.sum_filter, he, sum_sign_divisors g hgs]
  simp only [mask, Ideal.isCoprime_iff_sup_eq, g]

#print axioms coprime_mask_expansion

end
end HeckeSkeleton.LowEnergy.IdealDivisorMasks
