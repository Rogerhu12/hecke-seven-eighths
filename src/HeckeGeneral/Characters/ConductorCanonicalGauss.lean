import HeckeGeneral.Characters.LocalCanonicalAdditive
import HeckeGeneral.Characters.ConductorGaussFrequency

/-! The standard local trace/different normalizations on the genuine global conductor quotient.
The proved local normalization units are assembled by CRT; their phase correction remains explicit. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

local instance canonicalLocalResidueFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n) := Fintype.ofFinite _

local instance canonicalConductorQuotientFintype (χ : HeckeCharacter K) :
    Fintype (𝓞 K ⧸ (finiteConductor K χ).val) :=
  Fintype.ofEquiv (GlobalConductorResidueRing K χ) (conductorResidueCRT K χ).symm.toEquiv

def canonicalConductorAdditiveUnit (χ : HeckeCharacter K) :
    (𝓞 K ⧸ (finiteConductor K χ).val)ˣ :=
  (conductorResidueUnitsCRT K χ).symm (fun v : conductorPlaces K χ =>
    localCanonicalAdditiveUnit K v.val (localConductorExponent K χ v.val))

theorem canonicalConductorAdditiveUnit_CRT (χ : HeckeCharacter K)
    (v : conductorPlaces K χ) :
    conductorResidueCRT K χ (canonicalConductorAdditiveUnit K χ).val v =
      (localCanonicalAdditiveUnit K v.val (localConductorExponent K χ v.val)).val :=
  congrFun (conductorResidueCRT_unit_symm K χ _) v

/-- The character is identified below with the product of scaled standard trace characters. -/
def canonicalConductorAddCharacter (χ : HeckeCharacter K) :
    AddChar (𝓞 K ⧸ (finiteConductor K χ).val) ℂ :=
  (conductorPrimitiveAddCharacter K χ).mulShift (canonicalConductorAdditiveUnit K χ).val

theorem canonicalConductorAddCharacter_CRT (χ : HeckeCharacter K)
    (x : 𝓞 K ⧸ (finiteConductor K χ).val) :
    canonicalConductorAddCharacter K χ x =
      ∏ v : conductorPlaces K χ,
        localCanonicalAddCharacter K v.val (localConductorExponent K χ v.val)
          (conductorResidueCRT K χ x v) := by
  rw [canonicalConductorAddCharacter, AddChar.mulShift_apply,
    conductorPrimitiveAddCharacter_apply, map_mul]
  apply Finset.prod_congr rfl
  intro v _
  change (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val)
    (conductorResidueCRT K χ (canonicalConductorAdditiveUnit K χ).val v *
      conductorResidueCRT K χ x v) : ℂ) = _
  rw [canonicalConductorAdditiveUnit_CRT]
  have h := congrArg
    (fun η : AddChar (LocalResidueRing K v.val (localConductorExponent K χ v.val)) Circle =>
      (η (conductorResidueCRT K χ x v) : ℂ))
    (localCanonicalAdditiveUnit_shift K v.val (localConductorExponent K χ v.val))
  exact h

theorem canonicalConductorAddCharacter_isPrimitive (χ : HeckeCharacter K) :
    (canonicalConductorAddCharacter K χ).IsPrimitive := by
  intro a ha he
  have hna : (canonicalConductorAdditiveUnit K χ).val * a ≠ 0 :=
    fun h => ha ((canonicalConductorAdditiveUnit K χ).mul_right_eq_zero.mp h)
  apply conductorPrimitiveAddCharacter_isPrimitive K χ hna
  simpa only [canonicalConductorAddCharacter, AddChar.mulShift_mulShift] using he

theorem canonicalConductorAddCharacter_norm (χ : HeckeCharacter K)
    (x : 𝓞 K ⧸ (finiteConductor K χ).val) : ‖canonicalConductorAddCharacter K χ x‖ = 1 :=
  conductorPrimitiveAddCharacter_norm K χ _

/-- Mathlib's Gauss sum for the actual Hecke conductor and standard trace-normalized pairing. -/
def canonicalConductorGauss (χ : HeckeCharacter K) : ℂ :=
  gaussSum (conductorMulCharacter K χ) (canonicalConductorAddCharacter K χ)

theorem canonicalConductorGauss_normalization (χ : HeckeCharacter K) :
    canonicalConductorGauss K χ =
      (conductorUnitCharacter K χ (canonicalConductorAdditiveUnit K χ) : ℂ)⁻¹ * conductorGauss K χ := by
  change gaussSum _ ((conductorPrimitiveAddCharacter K χ).mulShift
    (canonicalConductorAdditiveUnit K χ).val) = _
  rw [← conductorGaussFrequency_eq_gaussSum, conductorGaussFrequency_unit]

theorem canonicalConductorGauss_factorization (χ : HeckeCharacter K) :
    canonicalConductorGauss K χ =
      ∏ v : conductorPlaces K χ, canonicalConductorResidueGauss K v.val χ := by
  change gaussSum _ ((conductorPrimitiveAddCharacter K χ).mulShift
    (canonicalConductorAdditiveUnit K χ).val) = _
  rw [← conductorGaussFrequency_eq_gaussSum, conductorGaussFrequency_factorization]
  apply Finset.prod_congr rfl
  intro v _
  rw [canonicalConductorAdditiveUnit_CRT]
  change localResidueGauss K v.val _ _
    ((localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val)).mulShift
      (localCanonicalAdditiveUnit K v.val (localConductorExponent K χ v.val)).val) = _
  rw [localCanonicalAdditiveUnit_shift]
  rfl

theorem canonicalConductorGauss_norm_sq (χ : HeckeCharacter K) :
    ‖canonicalConductorGauss K χ‖ ^ 2 = (Ideal.absNorm (finiteConductor K χ).val : ℝ) := by
  rw [canonicalConductorGauss_normalization, norm_mul, norm_inv, Circle.norm_coe,
    inv_one, one_mul, conductorGauss_norm_sq]

theorem canonicalConductorGauss_norm (χ : HeckeCharacter K) :
    ‖canonicalConductorGauss K χ‖ = Real.sqrt (Ideal.absNorm (finiteConductor K χ).val : ℝ) := by
  rw [← canonicalConductorGauss_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem canonicalConductorGauss_ne_zero (χ : HeckeCharacter K) : canonicalConductorGauss K χ ≠ 0 := by
  rw [canonicalConductorGauss_normalization]
  exact mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _)) (conductorGauss_ne_zero K χ)

end HeckeGeneral.Characters
