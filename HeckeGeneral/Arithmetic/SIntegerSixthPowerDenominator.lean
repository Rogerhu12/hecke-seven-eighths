import HeckeGeneral.Arithmetic.SIntegerFiniteLocalization
import HeckeGeneral.Characters.SIntegerSexticIdealEvaluation

/-!
Clearing denominators inside the original sixth-power Kummer class.

The actual valuation-defined S-integer ring is localized away from the
explicit finiteSIntegerDenominator, with exactly the original finite S.
If a*m=d is the localization presentation, then m^5*d=m^6*a. The image
of m is a genuine unit of the same S-integer ring, hence corresponds to
an actual S-unit. This avoids changing S and avoids merely clearing a
denominator by an arbitrary unit.

The integral representative and sixth-power S-unit are chosen once before
the ideal and residue-symbol data. The final theorem consequently retains
every literal zero-extended ideal evaluation at once.

This supplies integral representatives for the actual row-character
construction; it does not construct the global character itself.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- A nonzero integral representative in the same sixth-power S-unit
class. Both the ring of S-integers and the S-unit group use the given S. -/
theorem exists_integer_sixthPower_sUnit_representative
    (a : S.integer K) (ha : a ≠ 0) :
    ∃ b : 𝓞 K, ∃ hb : b ≠ 0, ∃ u : S.unit K,
      algebraMap (𝓞 K) (S.integer K) b =
        (S.unitEquivUnitsInteger K u).val ^ 6 * a := by
  letI := sInteger_isLocalizationAway_finiteDenominator K S
  obtain ⟨⟨d, m⟩, hm⟩ :=
    IsLocalization.surj (Submonoid.powers (finiteSIntegerDenominator K S)) a
  obtain ⟨v, hv⟩ := IsLocalization.map_units (S.integer K) m
  rw [← hv] at hm
  let b : 𝓞 K := m.val ^ 5 * d
  have hbImage : algebraMap (𝓞 K) (S.integer K) b = v.val ^ 6 * a := by
    dsimp only [b]
    rw [map_mul, map_pow, ← hm, ← hv]
    ring
  have hb : b ≠ 0 := by
    intro hzero
    have h := hbImage
    rw [hzero, map_zero] at h
    exact (mul_ne_zero (pow_ne_zero 6 v.ne_zero) ha) h.symm
  refine ⟨b, hb, (S.unitEquivUnitsInteger K).symm v, ?_⟩
  rw [MulEquiv.apply_symm_apply]
  exact hbImage

end HeckeGeneral.Arithmetic

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- A literal sixth-power-unit representation preserves the existing
actual ideal evaluation, including its noncoprimality zeros. -/
theorem sIntegerSexticIdealEvaluation_integer_sixthPower_sUnit_representative
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
    (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)
    (a : S.integer K) (b : 𝓞 K) (u : S.unit K)
    (hrep : algebraMap (𝓞 K) (S.integer K) b =
      (S.unitEquivUnitsInteger K u).val ^ 6 * a) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
        (algebraMap (𝓞 K) (S.integer K) b) =
      sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a := by
  rw [hrep]
  exact sIntegerSexticIdealEvaluation_mul_sixth_power_unit
    K S ζ hζ σ I hI hS h6 u a

/-- The same integral b works simultaneously for every exterior ideal
avoiding 6 and every residue-symbol choice. Those data occur after b,u. -/
theorem exists_integer_sixthPower_sUnit_representative_with_evaluation
    (a : S.integer K) (ha : a ≠ 0) :
    ∃ b : 𝓞 K, ∃ hb : b ≠ 0, ∃ u : S.unit K,
      algebraMap (𝓞 K) (S.integer K) b =
          (S.unitEquivUnitsInteger K u).val ^ 6 * a ∧
      ∀ (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
        (I : Ideal (𝓞 K)) (hI : I ≠ 0)
        (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
        (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal),
        sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
            (algebraMap (𝓞 K) (S.integer K) b) =
          sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a := by
  obtain ⟨b, hb, u, hrep⟩ := exists_integer_sixthPower_sUnit_representative K S a ha
  refine ⟨b, hb, u, hrep, ?_⟩
  intro ζ hζ σ I hI hS h6
  exact sIntegerSexticIdealEvaluation_integer_sixthPower_sUnit_representative
    K S ζ hζ σ I hI hS h6 a b u hrep

end HeckeGeneral.Characters
