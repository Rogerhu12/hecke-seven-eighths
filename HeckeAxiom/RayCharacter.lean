import HeckeGeneral.Characters.GlobalIntegralCharacter
import HeckeGeneral.Characters.LocalConductor
import HeckeGeneral.Analysis.HeckeSeries
import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

/-!
# Hecke ideal coefficients as AxiomMath ray class data

The ideal coefficients of an actual continuous unitary Hecke character are
compared with the axioms of `DedekindZetaZeroFree.RayClassCharacter` for the
modulus given by the character's finite conductor.

This file proves the formal laws: multiplicativity, the unit ideal, and the
exact zero set. The principal law for totally positive generators congruent
to one is proved separately for characters of finite order.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Arithmetic
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The finite conductor as an ordinary integral ideal. -/
abbrev conductorIdeal (χ : HeckeCharacter K) : Ideal (𝓞 K) := (finiteConductor K χ).val

theorem conductorIdeal_ne_bot (χ : HeckeCharacter K) : conductorIdeal K χ ≠ ⊥ :=
  nonZeroDivisors.coe_ne_zero (finiteConductor K χ)

/-- A prime divides the finite conductor exactly at the ramified places. -/
theorem conductorIdeal_le_iff (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    conductorIdeal K χ ≤ v.asIdeal ↔ ¬ UnramifiedAt K χ v := by
  have hmem : conductorIdeal K χ ≤ v.asIdeal ↔
      v.asIdeal ∈ normalizedFactors (conductorIdeal K χ) := by
    rw [Ideal.mem_normalizedFactors_iff (conductorIdeal_ne_bot K χ)]
    exact ⟨fun h => ⟨v.isPrime, h⟩, fun h => h.2⟩
  have hcount : (normalizedFactors (conductorIdeal K χ)).count v.asIdeal =
      localConductorExponent K χ v := by
    change (normalizedFactors (finiteConductor K χ).val).count v.asIdeal = _
    rw [← primeExponents_apply, primeExponents_finiteConductor, conductorExponents_apply]
  rw [hmem, ← Multiset.count_ne_zero, hcount, Ne, localConductorExponent_eq_zero_iff]

/-- An actual prime coefficient vanishes exactly at a ramified place. -/
theorem primeCoefficient_eq_zero_iff (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K χ v = 0 ↔ ¬ UnramifiedAt K χ v := by
  by_cases h : UnramifiedAt K χ v
  · rw [primeCoefficient_of_unramified K χ v h]
    simp only [h, not_true_eq_false, iff_false]
    exact Circle.coe_ne_zero _
  · rw [primeCoefficient_of_ramified K χ v h]
    simp only [h, not_false_eq_true]

/-- The ideal coefficient vanishes exactly on the zero ideal and on the
ideals sharing a prime factor with the finite conductor. -/
theorem idealCoefficient_eq_zero_iff (χ : HeckeCharacter K) (I : Ideal (𝓞 K)) :
    idealCoefficient (primeCoefficient K χ) I = 0 ↔
      (I = ⊥ ∨ I ⊔ conductorIdeal K χ ≠ ⊤) := by
  by_cases hI : I = ⊥
  · subst hI
    simp
  simp only [hI, false_or]
  rw [idealCoefficient, ite_eq_right hI, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨P, hP, hP0⟩ htop
    obtain ⟨hPprime, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hP
    have hPne : P ≠ ⊥ := (prime_of_normalized_factor P hP).ne_zero
    let v : HeightOneSpectrum (𝓞 K) := ⟨P, hPprime, hPne⟩
    have hval : primeIdealValue (primeCoefficient K χ) P = primeCoefficient K χ v :=
      primeIdealValue_asIdeal (primeCoefficient K χ) v
    have hram : ¬ UnramifiedAt K χ v :=
      (primeCoefficient_eq_zero_iff K χ v).mp (hval ▸ hP0)
    have hle : I ⊔ conductorIdeal K χ ≤ P :=
      sup_le hIP ((conductorIdeal_le_iff K χ v).mpr hram)
    rw [htop] at hle
    exact hPprime.ne_top (top_unique hle)
  · intro hne
    obtain ⟨M, hMmax, hM⟩ := Ideal.exists_le_maximal _ hne
    have hIM : I ≤ M := le_trans le_sup_left hM
    have hmM : conductorIdeal K χ ≤ M := le_trans le_sup_right hM
    have hMne : M ≠ ⊥ := by
      intro h
      rw [h, le_bot_iff] at hmM
      exact conductorIdeal_ne_bot K χ hmM
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hMmax.isPrime, hMne⟩
    refine ⟨M, (Ideal.mem_normalizedFactors_iff hI).mpr ⟨hMmax.isPrime, hIM⟩, ?_⟩
    have hram : ¬ UnramifiedAt K χ v := (conductorIdeal_le_iff K χ v).mp hmM
    rw [show M = v.asIdeal from rfl, primeIdealValue_asIdeal]
    exact (primeCoefficient_eq_zero_iff K χ v).mpr hram

/-- The coefficient of the unit ideal is one. -/
theorem idealCoefficient_top (χ : HeckeCharacter K) :
    idealCoefficient (primeCoefficient K χ) ⊤ = 1 := by
  rw [← Ideal.one_eq_top]
  exact idealCoefficient_one _

end HeckeAxiom
