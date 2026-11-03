import HeckeGeneral.Characters.SIntegerSexticCharacter
import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.Ideal

/-! Actual finite-prime product on S-integers and its finite
quotient function. This is not a MulChar on the S-integer ring. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)

def sIntegerSexticIdealEvaluation (a : S.integer K) : ℂ := by
  letI : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  exact ∏ p : idealPrimeDivisors K I,
    sIntegerSexticEvaluation K S p.val (hS p.val p.property)
      ζ hζ σ (h6 p.val p.property) a ^ idealPrimeMultiplicity K p.val I

include hS in
theorem sexticIdeal_coprime_S : ∀ v ∈ S, I ⊔ v.asIdeal = ⊤ := by
  intro v hv
  by_contra hne
  have heq : v.asIdeal = I ⊔ v.asIdeal := v.isMaximal.eq_of_le hne le_sup_right
  have hle : I ≤ v.asIdeal := by rw [heq]; exact le_sup_left
  exact hS v (Ideal.dvd_iff_le.mpr hle) hv

include hI hS in
theorem finite_sIntegerSexticIdealQuotient :
    Finite (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) :=
  finite_sIntegerResidue K S I hI (sexticIdeal_coprime_S K S I hS)

def sexticIdealPrimeQuotientMap (p : idealPrimeDivisors K I) :
    (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) →+*
      (𝓞 K ⧸ p.val.asIdeal) :=
  (sIntegerResidueEquiv K S p.val.asIdeal
    (sIntegerSexticResidue_coprime K S p.val (hS p.val p.property))).symm.toRingHom.comp
    (Ideal.quotientMap
      (p.val.asIdeal.map (algebraMap (𝓞 K) (S.integer K)))
      (RingHom.id (S.integer K)) (by
        simpa only [Ideal.comap_id] using
          Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K))
            (Ideal.dvd_iff_le.mp p.property)))

theorem sexticIdealPrimeQuotientMap_mk (p : idealPrimeDivisors K I)
    (a : S.integer K) :
    sexticIdealPrimeQuotientMap K S I hS p
      (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K))) a) =
        sIntegerSexticResidueMap K S p.val (hS p.val p.property) a := by
  simp only [sexticIdealPrimeQuotientMap, RingHom.comp_apply,
    Ideal.quotientMap_mk, RingHom.id_apply]
  rfl

def sIntegerSexticIdealQuotientFunction
    (q : S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) : ℂ := by
  letI : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  exact ∏ p : idealPrimeDivisors K I,
    sexticResidueCharacter K ζ hζ σ p.val (h6 p.val p.property)
      (sexticIdealPrimeQuotientMap K S I hS p q) ^ idealPrimeMultiplicity K p.val I

@[simp] theorem sIntegerSexticIdealQuotientFunction_mk (a : S.integer K) :
    sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6
      (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K))) a) =
        sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a := by
  simp only [sIntegerSexticIdealQuotientFunction, sIntegerSexticIdealEvaluation,
    sexticIdealPrimeQuotientMap_mk, sIntegerSexticEvaluation]

theorem sIntegerSexticIdealEvaluation_mul (a b : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 (a * b) =
      sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a *
        sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 b := by
  simp only [sIntegerSexticIdealEvaluation, sIntegerSexticEvaluation_mul,
    mul_pow, Finset.prod_mul_distrib]

@[simp] theorem sIntegerSexticIdealEvaluation_one :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 1 = 1 := by
  simp only [sIntegerSexticIdealEvaluation, sIntegerSexticEvaluation, map_one,
    one_pow, Finset.prod_const_one]

theorem sIntegerSexticIdealEvaluation_mul_sixth_power_unit (u : S.unit K)
    (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
        ((S.unitEquivUnitsInteger K u).val ^ 6 * a) =
      sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a := by
  simp only [sIntegerSexticIdealEvaluation,
    sIntegerSexticEvaluation_mul_sixth_power_unit]

theorem sIntegerSexticIdealEvaluation_sixth_power_unit (u : S.unit K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
      ((S.unitEquivUnitsInteger K u).val ^ 6) = 1 := by
  simpa only [mul_one, sIntegerSexticIdealEvaluation_one] using
    sIntegerSexticIdealEvaluation_mul_sixth_power_unit K S ζ hζ σ I hI hS h6 u 1

theorem sIntegerSexticIdealEvaluation_literal_invariant
    (Γ : Subgroup (S.unit K))
    (hΓ : Γ ≤ (powMonoidHom 6 : S.unit K →* S.unit K).range)
    (γ : Γ) (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
        ((S.unitEquivUnitsInteger K γ.val).val * a) =
      sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a := by
  letI : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  unfold sIntegerSexticIdealEvaluation
  apply Finset.prod_congr rfl
  intro p _
  rw [sIntegerSexticEvaluation_literal_invariant K S p.val
    (hS p.val p.property) ζ hζ σ (h6 p.val p.property) Γ hΓ γ a]

private theorem norm_sIntegerSexticEvaluation_le_one
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hp6 : (6 : 𝓞 K) ∉ p.asIdeal) (a : S.integer K) :
    ‖sIntegerSexticEvaluation K S p hpS ζ hζ σ hp6 a‖ ≤ 1 := by
  unfold sIntegerSexticEvaluation
  by_cases h : sIntegerSexticResidueMap K S p hpS a = 0
  · rw [h, sexticResidueCharacter_zero, norm_zero]; norm_num
  · exact le_of_eq (sexticResidueCharacter_norm K ζ hζ σ p hp6 _ h)

theorem norm_sIntegerSexticIdealEvaluation_le_one (a : S.integer K) :
    ‖sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a‖ ≤ 1 := by
  letI : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  unfold sIntegerSexticIdealEvaluation
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro p _; exact norm_nonneg _
  · intro p _
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _)
      (norm_sIntegerSexticEvaluation_le_one K S ζ hζ σ p.val
        (hS p.val p.property) (h6 p.val p.property) a)

include hI in
private theorem sexticIdealPrimeMultiplicity_pos
    (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I) :
    0 < idealPrimeMultiplicity K p I := by
  unfold idealPrimeMultiplicity
  exact Nat.pos_of_ne_zero ((Associates.count_ne_zero_iff_dvd hI p.irreducible).mpr hp)

theorem sIntegerSexticIdealEvaluation_eq_zero_of_badPrime
    (a : S.integer K) (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I)
    (ha : sIntegerSexticResidueMap K S p (hS p hp) a = 0) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a = 0 := by
  letI : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  unfold sIntegerSexticIdealEvaluation
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨p, hp⟩ : idealPrimeDivisors K I))
  have he : sIntegerSexticEvaluation K S p (hS p hp) ζ hζ σ (h6 p hp) a = 0 := by
    unfold sIntegerSexticEvaluation
    rw [ha, sexticResidueCharacter_zero]
  rw [he, zero_pow (Nat.ne_of_gt (sexticIdealPrimeMultiplicity_pos K I hI p hp))]

/-- Every factor has norm one when the numerator is a unit at all prime
 divisors of the denominator. This includes the empty product for the unit ideal. -/
theorem norm_sIntegerSexticIdealEvaluation_eq_one
    (a : S.integer K)
    (ha : ∀ p : HeightOneSpectrum (𝓞 K), ∀ hp : p.asIdeal ∣ I,
      sIntegerSexticResidueMap K S p (hS p hp) a ≠ 0) :
    ‖sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a‖ = 1 := by
  letI : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  unfold sIntegerSexticIdealEvaluation
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro p _
  rw [norm_pow]
  have hn : ‖sIntegerSexticEvaluation K S p.val (hS p.val p.property)
      ζ hζ σ (h6 p.val p.property) a‖ = 1 := by
    unfold sIntegerSexticEvaluation
    exact sexticResidueCharacter_norm K ζ hζ σ p.val (h6 p.val p.property)
      _ (ha p.val p.property)
  rw [hn, one_pow]

/-- The literal zero set is exactly the union of the bad-prime residue
kernels. Multiplicities divisible by six do not remove a bad prime. -/
theorem sIntegerSexticIdealEvaluation_eq_zero_iff
    (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a = 0 ↔
      ∃ p : HeightOneSpectrum (𝓞 K), ∃ hp : p.asIdeal ∣ I,
        sIntegerSexticResidueMap K S p (hS p hp) a = 0 := by
  constructor
  · intro hz
    by_contra hbad
    have hgood : ∀ p : HeightOneSpectrum (𝓞 K), ∀ hp : p.asIdeal ∣ I,
        sIntegerSexticResidueMap K S p (hS p hp) a ≠ 0 := by
      intro p hp ha
      exact hbad ⟨p, hp, ha⟩
    have hn := norm_sIntegerSexticIdealEvaluation_eq_one K S ζ hζ σ I hI hS h6 a hgood
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  · rintro ⟨p, hp, ha⟩
    exact sIntegerSexticIdealEvaluation_eq_zero_of_badPrime K S ζ hζ σ I hI hS h6 a p hp ha

/-- The unit ideal gives an empty product, even at the zero argument. -/
theorem sIntegerSexticIdealEvaluation_top
    (hStop : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ (⊤ : Ideal (𝓞 K)) → p ∉ S)
    (h6top : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ (⊤ : Ideal (𝓞 K)) →
      (6 : 𝓞 K) ∉ p.asIdeal) (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ ⊤ top_ne_bot hStop h6top a = 1 := by
  have hempty : IsEmpty (idealPrimeDivisors K (⊤ : Ideal (𝓞 K))) := by
    refine ⟨fun p => p.val.isPrime.ne_top ?_⟩
    exact top_le_iff.mp (Ideal.dvd_iff_le.mp p.property)
  letI := hempty
  simp only [sIntegerSexticIdealEvaluation, Finset.univ_eq_empty, Finset.prod_empty]

end HeckeGeneral.Characters
