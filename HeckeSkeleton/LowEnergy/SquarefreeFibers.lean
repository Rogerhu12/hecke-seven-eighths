import HeckeSkeleton.LowEnergy.IdealMass
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Data.Finset.Powerset

/-!
# Actual ideal product fibers with a uniform small-power cost

Only squarefree product targets are needed by the quadratic and cubic
sieves. Their fibers inject into the squarefree ideal divisors. We prove
the required divisor bound directly from finite prime support and finiteness
of the small-norm ideals. No divisor-bound axiom, prime ideal theorem, or
unproved project declaration is imported.

The basic prime-support identities are adapted from the supplied file
`HeckePort/CenteredMoment/IdealMobius.lean`.
-/

namespace HeckeSkeleton.LowEnergy

open NumberField Ideal UniqueFactorizationMonoid
open scoped BigOperators NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def idealPrimeSupport (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (normalizedFactors I).toFinset

theorem idealPrimeSupport_prime {I P : Ideal (𝓞 K)}
    (hP : P ∈ idealPrimeSupport K I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem ideal_support_product_ne_zero {I : Ideal (𝓞 K)}
    {s : Finset (Ideal (𝓞 K))} (hs : s ⊆ idealPrimeSupport K I) :
    (∏ P ∈ s, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ hP => (idealPrimeSupport_prime K (hs hP)).ne_zero)

theorem ideal_factors_support_product {I : Ideal (𝓞 K)}
    {s : Finset (Ideal (𝓞 K))} (hs : s ⊆ idealPrimeSupport K I) :
    normalizedFactors (∏ P ∈ s, P) = s.val := by
  have hp : ∀ P ∈ s.val, Prime P := fun P hP => idealPrimeSupport_prime K (hs hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem ideal_support_product_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    {s : Finset (Ideal (𝓞 K))} (hs : s ⊆ idealPrimeSupport K I) :
    (∏ P ∈ s, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors
    (ideal_support_product_ne_zero K hs) hI).mpr
  rw [ideal_factors_support_product K hs]
  apply (Multiset.le_iff_subset s.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hs hP)

theorem idealPrimeSupport_mono_of_dvd {I J : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hJI : J ∣ I) :
    idealPrimeSupport K J ⊆ idealPrimeSupport K I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_ideal_support_product {I : Ideal (𝓞 K)} (hI : Squarefree I) :
    (∏ P ∈ idealPrimeSupport K I, P) = I := by
  have hn : (normalizedFactors I).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  have hv : (idealPrimeSupport K I).val = normalizedFactors I := by
    simpa only [idealPrimeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (idealPrimeSupport K I).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors I).prod := by rw [hv]
    _ = I := Ideal.prod_normalizedFactors_eq_self hI.ne_zero

theorem norm_ideal_support_product_le {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (∏ P ∈ idealPrimeSupport K I, (Ideal.absNorm P : ℝ)) ≤ (Ideal.absNorm I : ℝ) := by
  have hn : Ideal.absNorm (∏ P ∈ idealPrimeSupport K I, P) ≤ Ideal.absNorm I :=
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)))
      (map_dvd Ideal.absNorm (ideal_support_product_dvd K hI (Finset.Subset.refl _)))
  have hcast := (Nat.cast_le (α := ℝ)).mpr hn
  simpa only [map_prod, Nat.cast_prod] using hcast

/-- Finite prime support has the required uniform subpower cardinality.
This controls squarefree divisors even when the ambient ideal is not
squarefree. -/
theorem two_pow_idealPrimeSupport_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      (2 : ℝ) ^ (idealPrimeSupport K I).card ≤ C * (Ideal.absNorm I : ℝ) ^ eps := by
  classical
  let cutoff : ℕ := Nat.ceil ((2 : ℝ) ^ (1 / eps))
  let bad : Finset (Ideal (𝓞 K)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) cutoff).toFinset
  have hbad (P : Ideal (𝓞 K)) : P ∈ bad ↔ Ideal.absNorm P ≤ cutoff := by
    exact Set.Finite.mem_toFinset _
  refine ⟨(2 : ℝ) ^ bad.card, one_le_pow₀ (by norm_num), ?_⟩
  intro I hI
  have hlarge (P : Ideal (𝓞 K)) (hP : P ∉ bad) :
      2 ≤ (Ideal.absNorm P : ℝ) ^ eps := by
    have hnat : cutoff < Ideal.absNorm P := Nat.lt_of_not_ge (fun h => hP ((hbad P).mpr h))
    have hbase : (2 : ℝ) ^ (1 / eps) ≤ (Ideal.absNorm P : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hnat.le)
    have heq : ((2 : ℝ) ^ (1 / eps)) ^ eps = 2 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have he : (1 / eps) * eps = 1 := by field_simp [ne_of_gt heps]
      rw [he, Real.rpow_one]
    exact heq ▸ Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hbase heps.le
  have hterm (P : Ideal (𝓞 K)) (hP : P ∈ idealPrimeSupport K I) :
      (2 : ℝ) ≤ (if P ∈ bad then 2 else 1) * (Ideal.absNorm P : ℝ) ^ eps := by
    by_cases hPb : P ∈ bad
    · rw [if_pos hPb]
      have hn := Real.one_le_rpow
        (one_le_ideal_norm K P (idealPrimeSupport_prime K hP).ne_zero) heps.le
      linarith
    · rw [if_neg hPb, one_mul]
      exact hlarge P hPb
  have hbadprod :
      (∏ P ∈ idealPrimeSupport K I, if P ∈ bad then (2 : ℝ) else 1) ≤
        (2 : ℝ) ^ bad.card := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    apply Finset.card_le_card
    intro P hP
    exact (Finset.mem_filter.mp hP).2
  have hnorm :
      (∏ P ∈ idealPrimeSupport K I, (Ideal.absNorm P : ℝ)) ^ eps ≤
        (Ideal.absNorm I : ℝ) ^ eps :=
    Real.rpow_le_rpow (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      (norm_ideal_support_product_le K hI) heps.le
  calc
    _ = ∏ _P ∈ idealPrimeSupport K I, (2 : ℝ) := by simp
    _ ≤ ∏ P ∈ idealPrimeSupport K I,
        (if P ∈ bad then (2 : ℝ) else 1) * (Ideal.absNorm P : ℝ) ^ eps := by
      exact Finset.prod_le_prod₀ (fun _ _ => by norm_num) hterm
    _ = (∏ P ∈ idealPrimeSupport K I, if P ∈ bad then (2 : ℝ) else 1) *
        (∏ P ∈ idealPrimeSupport K I, (Ideal.absNorm P : ℝ)) ^ eps := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
    _ ≤ _ := mul_le_mul hbadprod hnorm (Real.rpow_nonneg
      (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) _) (by positivity)

/-- Every finite set of squarefree divisors has at most `2^omega(I)` elements. -/
theorem squarefree_divisor_finset_card_le
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (s : Finset (Ideal (𝓞 K)))
    (hs : ∀ J ∈ s, Squarefree J ∧ J ∣ I) :
    s.card ≤ 2 ^ (idealPrimeSupport K I).card := by
  classical
  have hcard : s.card ≤ (idealPrimeSupport K I).powerset.card := by
    apply Finset.card_le_card_of_injOn (idealPrimeSupport K)
    · intro J hJ
      exact Finset.mem_powerset.mpr
        (idealPrimeSupport_mono_of_dvd K hI (hs J hJ).1.ne_zero (hs J hJ).2)
    · intro J hJ L hL hJL
      rw [← squarefree_ideal_support_product K (hs J hJ).1,
        ← squarefree_ideal_support_product K (hs L hL).1, hJL]
  simpa only [Finset.card_powerset] using hcard

/-- Uniform small-power cardinality for finite squarefree-divisor sets. -/
theorem squarefree_divisor_finset_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (I : Ideal (𝓞 K)) (s : Finset (Ideal (𝓞 K))),
      I ≠ ⊥ → (∀ J ∈ s, Squarefree J ∧ J ∣ I) →
      (s.card : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ eps := by
  obtain ⟨C, hC, hb⟩ := two_pow_idealPrimeSupport_small_power K eps heps
  refine ⟨C, hC, ?_⟩
  intro I s hI hs
  have hc : (s.card : ℝ) ≤ (2 : ℝ) ^ (idealPrimeSupport K I).card := by
    exact_mod_cast squarefree_divisor_finset_card_le K I hI s hs
  exact hc.trans (hb I hI)

/-- The first component injects each ideal product fiber into divisors of
its nonzero squarefree product. This is applicable separately to `m*h` and
`c*m`; it does not identify those two fiber maps. -/
theorem ideal_product_fiber_card_le
    (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (I : Ideal (𝓞 K)) (hI : Squarefree I) :
    (pairs.filter (fun x => x.1 * x.2 = I)).card ≤
      2 ^ (idealPrimeSupport K I).card := by
  classical
  let fiber := pairs.filter (fun x => x.1 * x.2 = I)
  have hnonzero (x : Ideal (𝓞 K) × Ideal (𝓞 K)) (hx : x ∈ fiber) : x.1 ≠ 0 := by
    have he := (Finset.mem_filter.mp hx).2
    have hp : x.1 * x.2 ≠ 0 := by rw [he]; exact hI.ne_zero
    exact (mul_ne_zero_iff.mp hp).1
  have hinj : Set.InjOn (fun x : Ideal (𝓞 K) × Ideal (𝓞 K) => x.1) fiber := by
    intro x hx y hy hxy
    change x.1 = y.1 at hxy
    have he : x.1 * x.2 = y.1 * y.2 :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    apply Prod.ext hxy
    rw [← hxy] at he
    exact mul_left_cancel₀ (hnonzero x hx) he
  have himage : (fiber.image Prod.fst).card = fiber.card := Finset.card_image_iff.mpr hinj
  rw [← himage]
  apply squarefree_divisor_finset_card_le K I hI.ne_zero
  intro J hJ
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hJ
  have hd : x.1 ∣ I := ⟨x.2, (Finset.mem_filter.mp hx).2.symm⟩
  exact ⟨Squarefree.squarefree_of_dvd hd hI, hd⟩

theorem ideal_product_fibers_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (I : Ideal (𝓞 K)),
      Squarefree I → (Ideal.absNorm I : ℝ) ≤ X →
      ((pairs.filter (fun x => x.1 * x.2 = I)).card : ℝ) ≤ C * X ^ eps := by
  obtain ⟨C, hC, hb⟩ := two_pow_idealPrimeSupport_small_power K eps heps
  refine ⟨C, hC, ?_⟩
  intro X hX pairs I hI hcut
  have hc : ((pairs.filter (fun x => x.1 * x.2 = I)).card : ℝ) ≤
      (2 : ℝ) ^ (idealPrimeSupport K I).card := by
    exact_mod_cast ideal_product_fiber_card_le K pairs I hI
  exact hc.trans ((hb I hI.ne_zero).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hcut heps.le) (zero_le_one.trans hC)))

#print axioms two_pow_idealPrimeSupport_small_power
#print axioms squarefree_divisor_finset_small_power
#print axioms ideal_product_fibers_small_power

end
end HeckeSkeleton.LowEnergy
