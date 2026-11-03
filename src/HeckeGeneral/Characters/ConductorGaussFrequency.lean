import HeckeGeneral.Characters.ConductorGauss

/-! Exact unit support of the finite Fourier transform at the actual Hecke conductor. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

local instance frequencyLocalResidueFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n) := Fintype.ofFinite _

local instance frequencyLocalUnitsFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n)ˣ := Fintype.ofFinite _

local instance frequencyConductorQuotientFintype (χ : HeckeCharacter K) :
    Fintype (𝓞 K ⧸ (finiteConductor K χ).val) :=
  Fintype.ofEquiv (GlobalConductorResidueRing K χ) (conductorResidueCRT K χ).symm.toEquiv

local instance frequencyConductorUnitsFintype (χ : HeckeCharacter K) :
    Fintype (𝓞 K ⧸ (finiteConductor K χ).val)ˣ := Fintype.ofFinite _

theorem conductorResidueCRT_unit_symm (χ : HeckeCharacter K)
    (y : GlobalConductorResidueUnits K χ) :
    conductorResidueCRT K χ ((conductorResidueUnitsCRT K χ).symm y).val =
      fun v => (y v).val := by
  have hu : Units.map (conductorResidueCRT K χ).toMonoidHom
      ((conductorResidueUnitsCRT K χ).symm y) = MulEquiv.piUnits.symm y := by
    apply MulEquiv.piUnits.injective
    exact (conductorResidueUnitsCRT K χ).apply_symm_apply y
  exact congrArg Units.val hu

def conductorGaussFrequency (χ : HeckeCharacter K)
    (b : 𝓞 K ⧸ (finiteConductor K χ).val) : ℂ :=
  ∑ u : (𝓞 K ⧸ (finiteConductor K χ).val)ˣ,
    (conductorUnitCharacter K χ u : ℂ) * conductorPrimitiveAddCharacter K χ (b * u.val)

theorem conductorGaussFrequency_eq_gaussSum (χ : HeckeCharacter K)
    (b : 𝓞 K ⧸ (finiteConductor K χ).val) :
    conductorGaussFrequency K χ b =
      gaussSum (conductorMulCharacter K χ) ((conductorPrimitiveAddCharacter K χ).mulShift b) := by
  unfold conductorGaussFrequency gaussSum
  simp only [AddChar.mulShift_apply]
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro a ha
    have hau : ¬ IsUnit a := fun ⟨u, hu⟩ => ha ⟨u, hu⟩
    rw [conductorMulCharacter_nonunit K χ a hau, zero_mul]
  · intro u
    rw [conductorMulCharacter_unit]

theorem conductorGaussFrequency_factorization (χ : HeckeCharacter K)
    (b : 𝓞 K ⧸ (finiteConductor K χ).val) :
    conductorGaussFrequency K χ b =
      ∏ v : conductorPlaces K χ,
        localResidueGaussFrequency K v.val (localConductorExponent K χ v.val)
          (conductorResidueCharacter K v.val χ)
          (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val))
          (conductorResidueCRT K χ b v) := by
  unfold conductorGaussFrequency
  rw [← (conductorResidueUnitsCRT K χ).symm.toEquiv.sum_comp]
  change (∑ y : GlobalConductorResidueUnits K χ,
    (conductorUnitCharacter K χ ((conductorResidueUnitsCRT K χ).symm y) : ℂ) *
      conductorPrimitiveAddCharacter K χ (b * ((conductorResidueUnitsCRT K χ).symm y).val)) = _
  have he (y : GlobalConductorResidueUnits K χ) :
      (conductorUnitCharacter K χ ((conductorResidueUnitsCRT K χ).symm y) : ℂ) *
        conductorPrimitiveAddCharacter K χ (b * ((conductorResidueUnitsCRT K χ).symm y).val) =
      ∏ v : conductorPlaces K χ,
        (conductorResidueCharacter K v.val χ (y v) : ℂ) *
          (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val)
            (conductorResidueCRT K χ b v * (y v).val) : ℂ) := by
    rw [conductorUnitCharacter_CRT, conductorPrimitiveAddCharacter_apply, map_mul,
      conductorResidueCRT_unit_symm]
    change Circle.coeHom (∏ v : conductorPlaces K χ, conductorResidueCharacter K v.val χ (y v)) *
      (∏ v : conductorPlaces K χ,
        (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val)
          (conductorResidueCRT K χ b v * (y v).val) : ℂ)) = _
    rw [map_prod]
    change (∏ v : conductorPlaces K χ, (conductorResidueCharacter K v.val χ (y v) : ℂ)) * _ = _
    rw [Finset.prod_mul_distrib]
  simp_rw [he]
  exact (Fintype.prod_sum (fun v : conductorPlaces K χ => fun u =>
    (conductorResidueCharacter K v.val χ u : ℂ) *
      (localPrimitiveAddCharacter K v.val (localConductorExponent K χ v.val)
        (conductorResidueCRT K χ b v * u.val) : ℂ))).symm

theorem conductorGaussFrequency_nonunit (χ : HeckeCharacter K)
    (b : 𝓞 K ⧸ (finiteConductor K χ).val) (hb : ¬ IsUnit b) :
    conductorGaussFrequency K χ b = 0 := by
  have hcrt : ¬ IsUnit (conductorResidueCRT K χ b) := by
    intro h
    exact hb (by simpa using h.map (conductorResidueCRT K χ).symm.toRingHom)
  rw [Pi.isUnit_iff] at hcrt
  push Not at hcrt
  obtain ⟨v, hv⟩ := hcrt
  rw [conductorGaussFrequency_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  exact conductorResidueGaussFrequency_nonunit K v.val χ _ _ hv

theorem conductorGaussFrequency_unit (χ : HeckeCharacter K)
    (u : (𝓞 K ⧸ (finiteConductor K χ).val)ˣ) :
    conductorGaussFrequency K χ u.val = (conductorUnitCharacter K χ u : ℂ)⁻¹ * conductorGauss K χ := by
  rw [conductorGaussFrequency_eq_gaussSum, gaussSum_mulShift_eq, ← conductorGauss_eq_gaussSum]
  congr 1
  rw [MulChar.inv_apply_eq_inv, conductorMulCharacter_unit, Ring.inverse_eq_inv]

theorem conductorGaussFrequency_ne_zero_iff (χ : HeckeCharacter K)
    (b : 𝓞 K ⧸ (finiteConductor K χ).val) :
    conductorGaussFrequency K χ b ≠ 0 ↔ IsUnit b := by
  constructor
  · intro h
    by_contra hb
    exact h (conductorGaussFrequency_nonunit K χ b hb)
  · rintro ⟨u, rfl⟩
    rw [conductorGaussFrequency_unit]
    exact mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _)) (conductorGauss_ne_zero K χ)

theorem conductorGaussFrequency_support (χ : HeckeCharacter K) :
    Function.support (conductorGaussFrequency K χ) =
      {b : 𝓞 K ⧸ (finiteConductor K χ).val | IsUnit b} := by
  ext b
  exact conductorGaussFrequency_ne_zero_iff K χ b

end HeckeGeneral.Characters
