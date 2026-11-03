import HeckeGeneral.Characters.ConductorCRT
import HeckeGeneral.Characters.LocalPrimitiveFourier
import HeckeGeneral.Arithmetic.ProductResidueFourier

/-! The actual finite-conductor Gauss sum, transported through completed-local CRT.
The additive character is constructed by finite duality at each prime-power factor.
It is not identified with a canonical trace/inverse-different normalization here. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

local instance conductorLocalResidueFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n) := Fintype.ofFinite _

local instance conductorLocalUnitsFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n)ˣ := Fintype.ofFinite _

local instance conductorQuotientFintype (χ : HeckeCharacter K) :
    Fintype (𝓞 K ⧸ (finiteConductor K χ).val) :=
  Fintype.ofEquiv (GlobalConductorResidueRing K χ) (conductorResidueCRT K χ).symm.toEquiv

local instance conductorQuotientUnitsFintype (χ : HeckeCharacter K) :
    Fintype (𝓞 K ⧸ (finiteConductor K χ).val)ˣ := Fintype.ofFinite _

/-- The constructed primitive completed-local character with complex values. -/
def localComplexPrimitiveAddCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    AddChar (LocalResidueRing K v n) ℂ :=
  Circle.coeHom.compAddChar (localPrimitiveAddCharacter K v n)

@[simp] theorem localComplexPrimitiveAddCharacter_apply (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (a : LocalResidueRing K v n) :
    localComplexPrimitiveAddCharacter K v n a = (localPrimitiveAddCharacter K v n a : ℂ) := rfl

theorem localComplexPrimitiveAddCharacter_isPrimitive (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) : (localComplexPrimitiveAddCharacter K v n).IsPrimitive :=
  (localPrimitiveAddCharacter_isPrimitive K v n).compMulHom_of_isPrimitive Circle.coe_injective

/-- The product pairing on all prime-power factors of the actual conductor. -/
def productConductorPrimitiveAddCharacter (χ : HeckeCharacter K) :
    AddChar (GlobalConductorResidueRing K χ) ℂ :=
  productCharacter (fun v : conductorPlaces K χ =>
    localComplexPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val))

theorem productConductorPrimitiveAddCharacter_isPrimitive (χ : HeckeCharacter K) :
    (productConductorPrimitiveAddCharacter K χ).IsPrimitive :=
  productCharacter_isPrimitive _ (fun v => localComplexPrimitiveAddCharacter_isPrimitive K v.val _)

/-- A primitive additive character on the genuine global conductor quotient. -/
def conductorPrimitiveAddCharacter (χ : HeckeCharacter K) :
    AddChar (𝓞 K ⧸ (finiteConductor K χ).val) ℂ :=
  transportCharacter (conductorResidueCRT K χ) (productConductorPrimitiveAddCharacter K χ)

@[simp] theorem conductorPrimitiveAddCharacter_apply (χ : HeckeCharacter K)
    (a : 𝓞 K ⧸ (finiteConductor K χ).val) :
    conductorPrimitiveAddCharacter K χ a =
      ∏ v : conductorPlaces K χ,
        (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val)
          (conductorResidueCRT K χ a v) : ℂ) := rfl

theorem conductorPrimitiveAddCharacter_isPrimitive (χ : HeckeCharacter K) :
    (conductorPrimitiveAddCharacter K χ).IsPrimitive :=
  transportCharacter_isPrimitive _ _ (productConductorPrimitiveAddCharacter_isPrimitive K χ)

theorem conductorPrimitiveAddCharacter_norm (χ : HeckeCharacter K)
    (a : 𝓞 K ⧸ (finiteConductor K χ).val) :
    ‖conductorPrimitiveAddCharacter K χ a‖ = 1 := by
  rw [conductorPrimitiveAddCharacter_apply, norm_prod]
  simp only [Circle.norm_coe, Finset.prod_const_one]

/-- The Gauss sum uses the actual conductor unit character, including depth zero. -/
def conductorGauss (χ : HeckeCharacter K) : ℂ :=
  ∑ u : (𝓞 K ⧸ (finiteConductor K χ).val)ˣ,
    (conductorUnitCharacter K χ u : ℂ) * conductorPrimitiveAddCharacter K χ u.val

/-- The unit sum agrees with Mathlib's ring sum for the actual extension by zero. -/
theorem conductorGauss_eq_gaussSum (χ : HeckeCharacter K) :
    conductorGauss K χ = gaussSum (conductorMulCharacter K χ) (conductorPrimitiveAddCharacter K χ) := by
  unfold conductorGauss gaussSum
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro a ha
    have hau : ¬ IsUnit a := fun ⟨u, hu⟩ => ha ⟨u, hu⟩
    rw [conductorMulCharacter_nonunit K χ a hau, zero_mul]
  · intro u
    rw [conductorMulCharacter_unit]

theorem conductorGauss_factorization (χ : HeckeCharacter K) :
    conductorGauss K χ =
      ∏ v : conductorPlaces K χ, primitiveConductorResidueGauss K v.val χ := by
  unfold conductorGauss
  have hs := (conductorResidueUnitsCRT K χ).symm.toEquiv.sum_comp
    (fun u : (𝓞 K ⧸ (finiteConductor K χ).val)ˣ =>
      (conductorUnitCharacter K χ u : ℂ) * conductorPrimitiveAddCharacter K χ u.val)
  rw [← hs]
  change (∑ y : GlobalConductorResidueUnits K χ,
    (conductorUnitCharacter K χ ((conductorResidueUnitsCRT K χ).symm y) : ℂ) *
      conductorPrimitiveAddCharacter K χ ((conductorResidueUnitsCRT K χ).symm y).val) = _
  have he (y : GlobalConductorResidueUnits K χ) :
      (conductorUnitCharacter K χ ((conductorResidueUnitsCRT K χ).symm y) : ℂ) *
        conductorPrimitiveAddCharacter K χ ((conductorResidueUnitsCRT K χ).symm y).val =
      ∏ v : conductorPlaces K χ,
        (conductorResidueCharacter K v.val χ (y v) : ℂ) *
          (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val) (y v).val : ℂ) := by
    rw [conductorUnitCharacter_CRT, conductorPrimitiveAddCharacter_apply]
    have hcrt : conductorResidueCRT K χ ((conductorResidueUnitsCRT K χ).symm y).val =
        fun v => (y v).val := by
      have hu : Units.map (conductorResidueCRT K χ).toMonoidHom
          ((conductorResidueUnitsCRT K χ).symm y) = MulEquiv.piUnits.symm y := by
        apply MulEquiv.piUnits.injective
        exact (conductorResidueUnitsCRT K χ).apply_symm_apply y
      exact congrArg Units.val hu
    rw [hcrt]
    change Circle.coeHom (∏ v : conductorPlaces K χ, conductorResidueCharacter K v.val χ (y v)) *
      (∏ v : conductorPlaces K χ,
        (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val) (y v).val : ℂ)) = _
    rw [map_prod]
    change (∏ v : conductorPlaces K χ, (conductorResidueCharacter K v.val χ (y v) : ℂ)) * _ = _
    rw [Finset.prod_mul_distrib]
  simp_rw [he]
  exact (Fintype.prod_sum (fun v : conductorPlaces K χ => fun u =>
    (conductorResidueCharacter K v.val χ u : ℂ) *
      (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val) u.val : ℂ))).symm

theorem conductorQuotient_card (χ : HeckeCharacter K) :
    Nat.card (𝓞 K ⧸ (finiteConductor K χ).val) =
      ∏ v : conductorPlaces K χ, residueCard K v.val ^ localConductorExponent K χ v.val := by
  rw [Nat.card_congr (conductorResidueCRT K χ).toEquiv, Nat.card_pi]
  simp_rw [natCard_localResidueRing]

theorem conductorGauss_norm_sq (χ : HeckeCharacter K) :
    ‖conductorGauss K χ‖ ^ 2 = (Ideal.absNorm (finiteConductor K χ).val : ℝ) := by
  rw [conductorGauss_factorization, norm_prod, ← Finset.prod_pow]
  change (∏ v : conductorPlaces K χ,
    ‖localResidueGauss K v.val (localConductorExponent K χ v.val)
      (conductorResidueCharacter K v.val χ)
      (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val))‖ ^ 2) = _
  simp_rw [localPrimitiveGauss_norm_sq K _ _ _ (conductorResidueCharacter_isPrimitive K _ χ)]
  have hc : Ideal.absNorm (finiteConductor K χ).val =
      ∏ v : conductorPlaces K χ, Nat.card (LocalResidueRing K v.val (localConductorExponent K χ v.val)) := by
    change Nat.card (𝓞 K ⧸ (finiteConductor K χ).val) = _
    rw [Nat.card_congr (conductorResidueCRT K χ).toEquiv, Nat.card_pi]
  exact_mod_cast hc.symm

theorem conductorGauss_ne_zero (χ : HeckeCharacter K) : conductorGauss K χ ≠ 0 := by
  rw [conductorGauss_factorization]
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => primitiveConductorResidueGauss_ne_zero K v.val χ)

theorem conductorGauss_norm (χ : HeckeCharacter K) :
    ‖conductorGauss K χ‖ = Real.sqrt (Ideal.absNorm (finiteConductor K χ).val : ℝ) := by
  rw [← conductorGauss_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end HeckeGeneral.Characters
