import CubicSieve.InitialGeneric
import CubicSieve.PrimitiveCharactersCoefficients

/-! The unconditional initial cubic sieve exponent for the actual exterior kernel.
Primitivity, coefficient calibration, separation, finite local types and conductor
bounds are supplied by proved constructions, not assumptions of this endpoint. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Initial

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical NumberField

variable (K : Type) [Field K] [NumberField K]

theorem hasCubicExponent_two_finset
    (Sf : Finset (HeightOneSpectrum (𝓞 K)))
    (D : ThetaArithmeticData K (Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hD : AllowedGeneratorInput K (Sf : Set (HeightOneSpectrum (𝓞 K))) D) :
    Bootstrap.HasCubicExponent
      (ExteriorSieve.B K (Sf : Set (HeightOneSpectrum (𝓞 K))) D) 2 := by
  let S : Set (HeightOneSpectrum (𝓞 K)) := Sf
  obtain ⟨C, hC, hcond⟩ := CubicConductors.exists_fixed_conductor_norm_bound K S
  apply InitialGeneric.exponent_two_of_model K Sf D hD
    (PrimitiveCharacters.primitiveCharacter K S D)
    (PrimitiveCharacters.totallyComplex K S D)
    (PrimitiveCharacters.primitiveCharacter_cube K S D)
    (PrimitiveCharacters.primitiveCharacter_exterior_coefficient K S D)
    (PrimitiveCharacters.primitiveCharacter_distinct K S D) C hC
  intro J hJ
  rw [PrimitiveCharacters.primitiveCharacter_conductor]
  exact hcond D J hJ

theorem hasCubicExponent_two
    (S : Set (HeightOneSpectrum (𝓞 K))) [instS : Fintype S]
    (D : ThetaArithmeticData K S) (hD : AllowedGeneratorInput K S D) :
    Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) 2 := by
  obtain ⟨Sf, rfl⟩ := (Set.toFinite S).exists_finset_coe
  have heq : instS = FinsetCoe.fintype Sf := Subsingleton.elim _ _
  cases heq
  exact hasCubicExponent_two_finset K Sf D hD

end CubicSieve.Initial
