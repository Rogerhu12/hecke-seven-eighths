import RowCharacterCanonicalUniqueness
import ArithmeticFrequencyRowFaithfulness

/-!
Transport of actual Kummer principal-row detection to the original supplied
RowCharacterInput. Canonical equality is proved by global uniqueness and is
not an extra premise. The only arithmetic condition is the original
AllowedGeneratorInput for the same P.arithmetic and the same S.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S)

/-- Triviality of an arbitrary original supplied row character forces the
actual principal row, including its original sixth-unit sector. -/
theorem principalFrequencyRow_of_rowCharacterInput_eq_one
    (R : RowCharacterInput K S P)
    (hAllowed : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (hu : R.character u = 1) :
    principalFrequencyRow K S u := by
  apply principalFrequencyRow_of_arithmeticRowCharacter_eq_one K S P hAllowed u
  rw [← rowCharacterInput_character_eq_arithmetic K S P R u]
  exact hu

/-- Global HB-POLE scope for the original row input: every nonprincipal
row is excluded from every pure norm twist, without a size cutoff. -/
theorem rowCharacterInput_ne_normTwist_of_not_principal
    (R : RowCharacterInput K S P)
    (hAllowed : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (hu : ¬ principalFrequencyRow K S u) (t : ℝ) :
    R.character u ≠ heckeNormTwist K t := by
  rw [rowCharacterInput_character_eq_arithmetic K S P R u]
  exact arithmeticRowCharacter_ne_normTwist_of_not_principal K S P hAllowed u hu t

end HeckeGeneral.ThetaSkeleton.Physical
