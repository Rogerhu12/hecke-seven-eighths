import HeckeSkeleton.Moments.MOM_INV_STEP.UnitGaussTransport
import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitiveFourier

/-!
# Sixth-unit transport of the actual primitive Gauss packet

The generic principal-quotient unit transport is instantiated with the
proved multiplicative primitive coefficient. No finite Gauss identity is
supplied by the input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.UnitGaussTransport

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton
open PrincipalGaussCRT
open scoped Classical BigOperators

open ActualFiniteSource PrimitivePoissonSource PrimitiveFourier

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K Sset)

/-- The multiplicative hom already proved for the actual primitive packet. -/
def primitiveCharacter (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : PrincipalQuotient K S D B t →* ℂ where
  toFun := primitiveCoefficient K S D B t
  map_one' := primitiveCoefficient_one K S D B t
  map_mul' := primitiveCoefficient_mul K S D B t

theorem principalGauss_primitiveCharacter (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    principalGauss K Sset D.different_outside (primitiveModulus K S D B t)
        (primitiveModulus_ne_zero K S D B t) (primitiveCharacter K S D B t) =
      primitiveGauss K S D B t := by
  rw [primitiveGauss_eq_sum]
  rfl

/-- The allowed-generator sixth-power discrepancy leaves the actual
primitive Gauss sum unchanged. This is a literal finite-sum identity. -/
theorem primitiveGauss_sixth_unit_generator (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (u : (Sset).unit K) :
    let v := ((Sset).unitEquivUnitsInteger K u) ^ 6
    principalGauss K Sset D.different_outside (v.val * primitiveModulus K S D B t)
      (mul_ne_zero v.ne_zero (primitiveModulus_ne_zero K S D B t))
      (unitCharacter (primitiveModulus K S D B t) v (primitiveCharacter K S D B t)) =
      primitiveGauss K S D B t := by
  dsimp only
  rw [principalGauss_unit_of_value_one]
  · exact principalGauss_primitiveCharacter K S D B t
  · change primitiveCoefficient K S D B t
      (Ideal.Quotient.mk _ ((((Sset).unitEquivUnitsInteger K u) ^ 6).val)) = 1
    simpa only [Units.val_pow_eq_pow_val] using
      primitiveCoefficient_sixth_unit K S D B t u


end HeckeSkeleton.Moments.MOM_INV_STEP.UnitGaussTransport
