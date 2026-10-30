import HeckeGeneral.Characters.GlobalIntegralCharacter
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.NumberTheory.MulChar.Basic

/-! The finite conductor character on the actual global integer residue ring. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev GlobalConductorResidueRing (χ : HeckeCharacter K) :=
  ∀ v : conductorPlaces K χ, LocalResidueRing K v.val (localConductorExponent K χ v.val)

theorem conductor_primePower_product (χ : HeckeCharacter K) :
    (∏ v : conductorPlaces K χ, v.val.asIdeal ^ localConductorExponent K χ v.val) =
      (finiteConductor K χ).val := by
  change (∏ v : (conductorExponents K χ).support, v.val.asIdeal ^ (conductorExponents K χ) v.val) =
    (conductorExponents K χ).prod (fun v n => v.asIdeal ^ n)
  exact Finset.prod_coe_sort (conductorExponents K χ).support
    (fun v => v.asIdeal ^ (conductorExponents K χ) v)

def conductorGlobalPrimePowerCRT (χ : HeckeCharacter K) :
    (𝓞 K ⧸ (finiteConductor K χ).val) ≃+*
      ∀ v : conductorPlaces K χ, 𝓞 K ⧸ v.val.asIdeal ^ localConductorExponent K χ v.val :=
  HeightOneSpectrum.quotientEquivPiOfProdEq (ι := conductorPlaces K χ)
    (finiteConductor K χ).val (fun v : conductorPlaces K χ => v.val)
    (fun v : conductorPlaces K χ => localConductorExponent K χ v.val)
    (fun _ _ h => Subtype.val_injective.ne h) (conductor_primePower_product K χ)

/-- CRT together with the proved identification of global and completed local residues. -/
def conductorResidueCRT (χ : HeckeCharacter K) :
    (𝓞 K ⧸ (finiteConductor K χ).val) ≃+* GlobalConductorResidueRing K χ :=
  (conductorGlobalPrimePowerCRT K χ).trans
    (RingEquiv.piCongrRight fun v => localResidueRingEquivGlobal K v.val _)

theorem localResidueRingEquivGlobal_mk (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (r : 𝓞 K) :
    localResidueRingEquivGlobal K v n (Ideal.Quotient.mk _ r) = globalToLocalResidue K v n r := by
  rfl

theorem conductorResidueCRT_mk (χ : HeckeCharacter K) (r : 𝓞 K)
    (v : conductorPlaces K χ) :
    conductorResidueCRT K χ (Ideal.Quotient.mk _ r) v =
      globalToLocalResidue K v.val (localConductorExponent K χ v.val) r := by
  rfl

def conductorResidueUnitsCRT (χ : HeckeCharacter K) :
    (𝓞 K ⧸ (finiteConductor K χ).val)ˣ ≃* GlobalConductorResidueUnits K χ :=
  (Units.mapEquiv (conductorResidueCRT K χ).toMulEquiv).trans MulEquiv.piUnits

/-- The finite residue unit character belonging to the actual Hecke character. -/
def conductorUnitCharacter (χ : HeckeCharacter K) :
    (𝓞 K ⧸ (finiteConductor K χ).val)ˣ →* Circle :=
  (globalConductorResidueCharacter K χ).comp (conductorResidueUnitsCRT K χ).toMonoidHom

theorem conductorUnitCharacter_CRT (χ : HeckeCharacter K)
    (y : GlobalConductorResidueUnits K χ) :
    conductorUnitCharacter K χ ((conductorResidueUnitsCRT K χ).symm y) =
      globalConductorResidueCharacter K χ y := by
  simp [conductorUnitCharacter]

theorem conductorUnitCharacter_integral (χ : HeckeCharacter K) (u : GlobalIntegralUnits K) :
    conductorUnitCharacter K χ
      ((conductorResidueUnitsCRT K χ).symm (globalConductorReduction K χ u)) =
      globalIntegralComponent K χ u := by
  rw [conductorUnitCharacter_CRT, globalConductorResidueCharacter_reduction]

/-- Extension by zero on nonunits, as the standard multiplicative residue character. -/
def conductorMulCharacter (χ : HeckeCharacter K) :
    MulChar (𝓞 K ⧸ (finiteConductor K χ).val) ℂ :=
  MulChar.ofUnitHom (Circle.toUnits.comp (conductorUnitCharacter K χ))

@[simp] theorem conductorMulCharacter_unit (χ : HeckeCharacter K)
    (u : (𝓞 K ⧸ (finiteConductor K χ).val)ˣ) :
    conductorMulCharacter K χ u = (conductorUnitCharacter K χ u : ℂ) := by
  rw [conductorMulCharacter, MulChar.ofUnitHom_coe]
  rfl

theorem conductorMulCharacter_nonunit (χ : HeckeCharacter K)
    (r : 𝓞 K ⧸ (finiteConductor K χ).val) (hr : ¬ IsUnit r) :
    conductorMulCharacter K χ r = 0 := (conductorMulCharacter K χ).map_nonunit hr

theorem conductorMulCharacter_unit_norm (χ : HeckeCharacter K)
    (u : (𝓞 K ⧸ (finiteConductor K χ).val)ˣ) :
    ‖conductorMulCharacter K χ u‖ = 1 := by
  rw [conductorMulCharacter_unit]
  exact Circle.norm_coe _

theorem conductorMulCharacter_norm_le_one (χ : HeckeCharacter K)
    (r : 𝓞 K ⧸ (finiteConductor K χ).val) : ‖conductorMulCharacter K χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    rw [conductorMulCharacter_unit_norm]
  · rw [conductorMulCharacter_nonunit K χ r hr, norm_zero]
    exact zero_le_one

theorem conductorMulCharacter_integral (χ : HeckeCharacter K) (u : GlobalIntegralUnits K) :
    conductorMulCharacter K χ
      ((conductorResidueUnitsCRT K χ).symm (globalConductorReduction K χ u)) =
      (globalIntegralComponent K χ u : ℂ) := by
  rw [conductorMulCharacter_unit, conductorUnitCharacter_integral]

theorem conductorUnitCharacter_range_eq (χ : HeckeCharacter K) :
    Set.range (conductorUnitCharacter K χ) = Set.range (globalIntegralComponent K χ) := by
  rw [globalIntegralComponent_range_eq]
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨conductorResidueUnitsCRT K χ u, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(conductorResidueUnitsCRT K χ).symm y, conductorUnitCharacter_CRT K χ y⟩

theorem finite_conductorUnitCharacter_range (χ : HeckeCharacter K) :
    (Set.range (conductorUnitCharacter K χ)).Finite := by
  rw [conductorUnitCharacter_range_eq]
  exact finite_globalIntegralComponent_range K χ

theorem conductorUnitCharacter_pow_card (χ : HeckeCharacter K)
    (u : (𝓞 K ⧸ (finiteConductor K χ).val)ˣ) :
    conductorUnitCharacter K χ u ^ Nat.card (GlobalConductorResidueUnits K χ) = 1 := by
  change globalConductorResidueCharacter K χ (conductorResidueUnitsCRT K χ u) ^ _ = 1
  rw [← map_pow, pow_card_eq_one', map_one]

end HeckeGeneral.Characters
