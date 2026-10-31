import HeckeSkeleton.HighBinSupport.ActualGaussData
import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# The actual twelfth root fixes the prime Gauss sign

The root is reduced from the given number field after proving its
integrality. Its sixth power is -1 in every exterior residue field, so
the sextic residue character takes value 1 at -1. This supplies the
negative-frequency sign and the exact G₁G₅ = Np identity without adding
either as an arithmetic hypothesis.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualEuler

open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance signPrimeResidueField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance signPrimeResidueFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

/-- Reduction of the actual twelfth root realizes -1 as a sixth power. -/
theorem exists_residue_sixth_root_neg_one (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) : ∃ ξ : 𝓞 K ⧸ p.val.asIdeal, ξ ^ 6 = -1 := by
  let ξ : 𝓞 K := ⟨D.root12, D.primitive12.isIntegral (by norm_num)⟩
  have htwo : IsPrimitiveRoot (D.root12 ^ 6) 2 := by
    simpa using D.primitive12.pow_div_gcd 6 (by norm_num)
  have hξ : ξ ^ 6 = (-1 : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    simpa only [map_pow, map_neg, map_one] using htwo.eq_neg_one_of_two_right
  refine ⟨Ideal.Quotient.mk p.val.asIdeal ξ, ?_⟩
  rw [← map_pow, hξ, map_neg, map_one]

/-- The sign in the actual negative-frequency Gauss sum is one. -/
theorem thetaPrimeCharacter_neg_one (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) : thetaPrimeCharacter K S D p (-1) = 1 := by
  obtain ⟨ξ, hξ⟩ := exists_residue_sixth_root_neg_one K S D p
  apply HighBin.ActualGaussPhases.neg_one_eq_one (thetaPrimeCharacter K S D p) _ ξ hξ
  simpa only [thetaPrimeCharacter_order K S D p] using
    pow_orderOf_eq_one (thetaPrimeCharacter K S D p)

/-- Both Gauss sums use the actual prime generator's principal phase. -/
theorem primeGauss_one_mul_five (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S D p)
        (primeAddCharacter K S D p) 1 *
      HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S D p)
        (primeAddCharacter K S D p) 5 = (p.val.asIdeal.absNorm : ℂ) := by
  simpa only [card_primeIdealResidueField] using
    HighBin.ActualGaussPhases.gaussFamily_one_mul_five
      (thetaPrimeCharacter K S D p) (thetaPrimeCharacter_order K S D p)
      (primeAddCharacter K S D p) (primeAddCharacter_isPrimitive K S D p)
      (thetaPrimeCharacter_neg_one K S D p)

#print axioms thetaPrimeCharacter_neg_one
#print axioms primeGauss_one_mul_five

end HeckeSkeleton.HighBinActualEuler
