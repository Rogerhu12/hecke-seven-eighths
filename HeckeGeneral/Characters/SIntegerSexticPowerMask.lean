import HeckeGeneral.Characters.SIntegerSexticIdealEvaluation
import HeckeGeneral.Arithmetic.SIntegerModulus
import HeckeGeneral.Arithmetic.SIntegerIdealSaturation

/-!
The actual sixth-power mask for every S-integer numerator.  This uses the
existing prime-residue evaluation, including its zero extension.  It does
not extend a moving character to a Hecke character and does not assume a
moment estimate.  The numerator need not be an S-unit, or even nonzero.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- Any numerator which is nonzero at this exterior prime has sixth-power
evaluation one, even if it is a nonunit of the S-integer ring. -/
theorem sIntegerSexticEvaluation_sixth_power_of_residue_ne_zero
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hp6 : (6 : 𝓞 K) ∉ p.asIdeal) (a : S.integer K)
    (ha : sIntegerSexticResidueMap K S p hpS a ≠ 0) :
    sIntegerSexticEvaluation K S p hpS ζ hζ σ hp6 (a ^ 6) = 1 := by
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _
  unfold sIntegerSexticEvaluation sexticResidueCharacter
  rw [map_pow]
  exact Arithmetic.FiniteFieldSexticCharacter.character_sixth_power_of_ne_zero
    _ _ _ _ _ _ _ ha

variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)

/-- The genuine ideal product equals one when no denominator prime is bad. -/
theorem sIntegerSexticIdealEvaluation_sixth_power_of_no_badPrime
    (a : S.integer K)
    (ha : ∀ p : HeightOneSpectrum (𝓞 K), ∀ hp : p.asIdeal ∣ I,
      sIntegerSexticResidueMap K S p (hS p hp) a ≠ 0) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 (a ^ 6) = 1 := by
  letI : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  unfold sIntegerSexticIdealEvaluation
  apply Finset.prod_eq_one
  intro p _hp
  rw [sIntegerSexticEvaluation_sixth_power_of_residue_ne_zero K S ζ hζ σ
    p.val (hS p.val p.property) (h6 p.val p.property) a (ha p.val p.property), one_pow]

/-- Exact zero/one mask, with every actual denominator prime retained.
No squarefreeness of I or condition on its multiplicities is required. -/
theorem sIntegerSexticIdealEvaluation_sixth_power_mask
    (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 (a ^ 6) =
      if ∀ p : HeightOneSpectrum (𝓞 K), ∀ hp : p.asIdeal ∣ I,
        sIntegerSexticResidueMap K S p (hS p hp) a ≠ 0 then 1 else 0 := by
  by_cases ha : ∀ p : HeightOneSpectrum (𝓞 K), ∀ hp : p.asIdeal ∣ I,
    sIntegerSexticResidueMap K S p (hS p hp) a ≠ 0
  · rw [if_pos ha]
    exact sIntegerSexticIdealEvaluation_sixth_power_of_no_badPrime
      K S ζ hζ σ I hI hS h6 a ha
  · rw [if_neg ha]
    simp only [not_forall, not_not] at ha
    obtain ⟨p, hp, hpa⟩ := ha
    apply sIntegerSexticIdealEvaluation_eq_zero_of_badPrime
      K S ζ hζ σ I hI hS h6 (a ^ 6) p hp
    rw [map_pow, hpa]
    norm_num

/-- The actual exterior residue map has the expected localized prime kernel. -/
theorem sIntegerSexticResidueMap_eq_zero_iff_mem_map
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S) (a : S.integer K) :
    sIntegerSexticResidueMap K S p hpS a = 0 ↔
      a ∈ p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) := by
  let e := sIntegerResidueEquiv K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p hpS)
  change e.symm (Ideal.Quotient.mk
    (p.asIdeal.map (algebraMap (𝓞 K) (S.integer K))) a) = 0 ↔ _
  rw [← map_zero e.symm, e.symm.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Prime divisibility of the actual contraction is exactly bad reduction. -/
theorem sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S) (a : S.integer K) :
    sIntegerSexticResidueMap K S p hpS a = 0 ↔
      p.asIdeal ∣ sIntegerModulusContraction K S a := by
  rw [sIntegerSexticResidueMap_eq_zero_iff_mem_map K S p hpS a]
  constructor
  · intro ha
    apply Ideal.dvd_iff_le.mpr
    calc
      sIntegerModulusContraction K S a ≤
          (p.asIdeal.map (algebraMap (𝓞 K) (S.integer K))).under (𝓞 K) :=
        Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr ha)
      _ = p.asIdeal := under_map_coprime_sIntegerIdeal K S p.asIdeal
        (sIntegerSexticResidue_coprime K S p hpS)
  · intro ha
    have hle := Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K))
      (Ideal.dvd_iff_le.mp ha)
    rw [map_sIntegerModulusContraction K S a] at hle
    exact hle (Ideal.subset_span (Set.mem_singleton a))

include hI in
/-- No bad denominator prime is equivalent to ordinary ideal coprimality. -/
theorem sIntegerSextic_no_badPrime_iff_coprime_contraction
    (a : S.integer K) :
    (∀ p : HeightOneSpectrum (𝓞 K), ∀ hp : p.asIdeal ∣ I,
      sIntegerSexticResidueMap K S p (hS p hp) a ≠ 0) ↔
        IsCoprime I (sIntegerModulusContraction K S a) := by
  constructor
  · intro ha
    apply Ideal.coprime_of_no_prime_ge
    intro P hIP hAP hP
    have hP0 : P ≠ ⊥ := by
      intro hz
      exact hI (le_bot_iff.mp (hz ▸ hIP))
    let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP, hP0⟩
    have hp : p.asIdeal ∣ I := Ideal.dvd_iff_le.mpr hIP
    exact ha p hp ((sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction
      K S p (hS p hp) a).mpr (Ideal.dvd_iff_le.mpr hAP))
  · intro ha p hp hpa
    have hAP := Ideal.dvd_iff_le.mp
      ((sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction
        K S p (hS p hp) a).mp hpa)
    have htop : (⊤ : Ideal (𝓞 K)) ≤ p.asIdeal := by
      rw [← ha.sup_eq]
      exact sup_le (Ideal.dvd_iff_le.mp hp) hAP
    exact p.isPrime.ne_top (top_le_iff.mp htop)

/-- The sixth-power amplification coefficient is the literal coprimality
indicator, including at nonunit numerators and at the unit denominator. -/
theorem sIntegerSexticIdealEvaluation_sixth_power_coprime_mask
    (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 (a ^ 6) =
      if IsCoprime I (sIntegerModulusContraction K S a) then 1 else 0 := by
  rw [sIntegerSexticIdealEvaluation_sixth_power_mask K S ζ hζ σ I hI hS h6 a,
    sIntegerSextic_no_badPrime_iff_coprime_contraction K S I hI hS a]

end HeckeGeneral.Characters
