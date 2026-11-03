import HeckeGeneral.Arithmetic.SIntegerResidue
import HeckeGeneral.Arithmetic.IdealFactorization

/-! Removing exactly the S-prime factors gives the ordinary contraction of
an extended ideal. This uses ideal unique factorization and actual localization. -/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

def outsideSPrimeExponents (I : (Ideal (𝓞 K))⁰) : HeightOneSpectrum (𝓞 K) →₀ ℕ :=
  (primeExponents I).filter (fun v => v ∉ S)

def outsideSIdeal (I : (Ideal (𝓞 K))⁰) : (Ideal (𝓞 K))⁰ :=
  idealOfPrimeExponents (outsideSPrimeExponents K S I)

/-- Every prime inverted in the actual S-integer ring extends to the unit ideal. -/
theorem map_sInteger_prime_eq_top (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    v.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) = ⊤ := by
  letI := sInteger_isLocalizationAway_finiteDenominator K S
  have hdiv : primePowerGenerator K v ∣ finiteSIntegerDenominator K S := by
    unfold finiteSIntegerDenominator
    exact Finset.dvd_prod_of_mem _ ((Set.toFinite S).mem_toFinset.mpr hv)
  have hu : IsUnit (algebraMap (𝓞 K) (S.integer K) (primePowerGenerator K v)) :=
    isUnit_of_dvd_unit ((algebraMap (𝓞 K) (S.integer K)).map_dvd hdiv)
      (IsLocalization.Away.algebraMap_isUnit
        (S := S.integer K) (finiteSIntegerDenominator K S))
  apply Ideal.eq_top_of_isUnit_mem _ ?_ hu
  exact Ideal.mem_map_of_mem _ ((primePowerGenerator_mem_prime_iff K v v).mpr rfl)

/-- Filtering out the S-prime powers leaves the extended ideal unchanged. -/
theorem map_idealOfPrimeExponents_filter_outside
    (e : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    (idealOfPrimeExponents (e.filter (fun v => v ∉ S))).val.map
      (algebraMap (𝓞 K) (S.integer K)) =
    (idealOfPrimeExponents e).val.map (algebraMap (𝓞 K) (S.integer K)) := by
  induction e using Finsupp.induction with
  | zero => simp [Finsupp.filter_zero]
  | @single_add p n e hp hn ih =>
    rw [Finsupp.filter_add, idealOfPrimeExponents_add, idealOfPrimeExponents_add]
    simp only [Submonoid.coe_mul, Ideal.map_mul, ih]
    by_cases hps : p ∈ S
    · simp [hps, idealOfPrimeExponents_single,
        Ideal.map_pow, map_sInteger_prime_eq_top K S p hps, Ideal.one_eq_top,
        Ideal.map_top, Ideal.top_pow]
    · simp [hps, idealOfPrimeExponents_single]

theorem map_outsideSIdeal (I : (Ideal (𝓞 K))⁰) :
    (outsideSIdeal K S I).val.map (algebraMap (𝓞 K) (S.integer K)) =
      I.val.map (algebraMap (𝓞 K) (S.integer K)) := by
  unfold outsideSIdeal outsideSPrimeExponents
  rw [map_idealOfPrimeExponents_filter_outside, idealOfPrimeExponents_primeExponents]

/-- Every retained prime power is coprime to each S-prime. -/
theorem outsideSIdeal_coprime (I : (Ideal (𝓞 K))⁰) :
    ∀ v ∈ S, (outsideSIdeal K S I).val ⊔ v.asIdeal = ⊤ := by
  intro v hv
  unfold outsideSIdeal idealOfPrimeExponents
  change (∏ p ∈ (outsideSPrimeExponents K S I).support,
    p.asIdeal ^ (outsideSPrimeExponents K S I) p) ⊔ v.asIdeal = ⊤
  apply Ideal.prod_sup_eq_top
  intro p hp
  have hpS : p ∉ S := by
    by_contra h
    have hz : outsideSPrimeExponents K S I p = 0 := by
      simp [outsideSPrimeExponents, Finsupp.filter_apply, h]
    exact (Finsupp.mem_support_iff.mp hp) hz
  have hpv : p ≠ v := fun he => hpS (he.symm ▸ hv)
  simpa only [pow_one] using
    (p.isCoprime_pow_of_ne v hpv ((outsideSPrimeExponents K S I) p) 1).sup_eq

/-- Coprimality makes extension and contraction inverse, witnessed by the
actual injective residue-ring equivalence. -/
theorem under_map_coprime_sIntegerIdeal (J : Ideal (𝓞 K))
    (hJ : ∀ v ∈ S, J ⊔ v.asIdeal = ⊤) :
    (J.map (algebraMap (𝓞 K) (S.integer K))).under (𝓞 K) = J := by
  let e := sIntegerResidueEquiv K S J hJ
  ext a
  change algebraMap (𝓞 K) (S.integer K) a ∈ J.map (algebraMap (𝓞 K) (S.integer K)) ↔ a ∈ J
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  change e (Ideal.Quotient.mk J a) = 0 ↔ Ideal.Quotient.mk J a = 0
  rw [← map_zero e]
  exact e.injective.eq_iff

theorem under_map_outsideSIdeal (I : (Ideal (𝓞 K))⁰) :
    ((outsideSIdeal K S I).val.map (algebraMap (𝓞 K) (S.integer K))).under (𝓞 K) =
      (outsideSIdeal K S I).val :=
  under_map_coprime_sIntegerIdeal K S _ (outsideSIdeal_coprime K S I)

/-- The ordinary contraction is obtained by deleting exactly the inverted
prime factors, rather than choosing a new principal generator. -/
theorem under_map_ideal_eq_outsideSIdeal (I : (Ideal (𝓞 K))⁰) :
    (I.val.map (algebraMap (𝓞 K) (S.integer K))).under (𝓞 K) =
      (outsideSIdeal K S I).val := by
  rw [← map_outsideSIdeal K S I]
  exact under_map_outsideSIdeal K S I

end HeckeGeneral.Arithmetic
