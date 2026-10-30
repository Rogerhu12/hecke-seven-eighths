import RowCharacterGlobalUniqueness
import HeckeGeneral.Analysis.PhysicalProbeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Characters.RowUniquenessDraft
open HeckeGeneral.Analysis HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton.Global
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S)

theorem isCoprime_primeIdeal_of_not_dvd
    (p : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hp : ¬p.asIdeal ∣ I) : IsCoprime p.asIdeal I := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hnot
  have he : p.asIdeal = p.asIdeal ⊔ I := p.isMaximal.eq_of_le hnot le_sup_left
  apply hp
  apply Ideal.dvd_iff_le.mpr
  rw [he]
  exact le_sup_right

/-- The actual calibration on one exterior prime ideal compares arbitrary
supplied row characters, not only a chosen canonical constructor. -/
theorem rowCharacterInput_primeCoefficient_eq_away
    (R₁ R₂ : RowCharacterInput K S P) (u : FrequencyRow K S)
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hpu : ¬p.asIdeal ∣ u.ideal.val.val) :
    primeCoefficient K (R₁.character u) p = primeCoefficient K (R₂.character u) p := by
  let I := exteriorPrimeIdeal K S ⟨p, hpS⟩
  have hcop : IsCoprime I.val.val u.ideal.val.val :=
    isCoprime_primeIdeal_of_not_dvd K p u.ideal.val.val hpu
  have h₁ := R₁.coefficient_calibration u I
  have h₂ := R₂.coefficient_calibration u I
  rw [if_pos hcop] at h₁ h₂
  have h := h₁.trans h₂.symm
  change idealCoefficient (primeCoefficient K (R₁.character u)) p.asIdeal =
    idealCoefficient (primeCoefficient K (R₂.character u)) p.asIdeal at h
  simpa only [idealCoefficient_prime] using h

/-- The original finite-order/calibration fields force uniqueness of
every actual row character, including rows supported at the unit ideal. -/
theorem rowCharacterInput_character_unique
    (R₁ R₂ : RowCharacterInput K S P) (u : FrequencyRow K S) :
    R₁.character u = R₂.character u := by
  classical
  have hS : S.Finite := Set.toFinite S
  have hu : (idealPrimeDivisors K u.ideal.val.val).Finite :=
    idealPrimeDivisors_finite K u.ideal.val.val (nonZeroDivisors.coe_ne_zero u.ideal.val)
  let B := hS.toFinset ∪ hu.toFinset
  apply finiteOrder_heckeCharacter_eq_of_primeCoefficient_eq_away K
    (R₁.character u) (R₂.character u) (R₁.finite_order u) (R₂.finite_order u) B
  intro p hp
  have hpS : p ∉ S := by
    intro h
    exact hp (Finset.mem_union_left _ (hS.mem_toFinset.mpr h))
  have hpu : ¬p.asIdeal ∣ u.ideal.val.val := by
    intro h
    have hm : p ∈ idealPrimeDivisors K u.ideal.val.val := h
    exact hp (Finset.mem_union_right _ (hu.mem_toFinset.mpr hm))
  exact rowCharacterInput_primeCoefficient_eq_away K S P R₁ R₂ u p hpS hpu

theorem rowCharacterInput_character_fun_unique (R₁ R₂ : RowCharacterInput K S P) :
    R₁.character = R₂.character :=
  funext (rowCharacterInput_character_unique K S P R₁ R₂)

end HeckeGeneral.ThetaSkeleton.Physical
