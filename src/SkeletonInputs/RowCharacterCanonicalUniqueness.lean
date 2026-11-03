import RowCharacterInputUniqueness
import ArithmeticRowCharacterInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S)

/-- Applies to the supplied input itself; it does not replace that input
or assume a canonical-character identification. -/
theorem rowCharacterInput_character_eq_arithmetic
    (R : RowCharacterInput K S P) (u : FrequencyRow K S) :
    R.character u = arithmeticRowCharacter K S P u := by
  exact rowCharacterInput_character_unique K S P R (arithmeticRowCharacterInput K S P) u

theorem rowCharacterInput_character_fun_eq_arithmetic
    (R : RowCharacterInput K S P) :
    R.character = arithmeticRowCharacter K S P :=
  funext (rowCharacterInput_character_eq_arithmetic K S P R)

end HeckeGeneral.ThetaSkeleton.Physical
