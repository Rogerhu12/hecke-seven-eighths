import HeckeGeneral.Analysis.ThetaPrimeGaussNorm
import HeckeSkeleton.HighBinSupport.ActualPrimePowerSymbols
import HeckeSkeleton.HighBinSupport.ActualGaussPhases

/-!
# Actual prime Gauss data without the arithmetic row-character construction

These definitions and proofs are the original prime-level Gauss portion
of `ActualEulerData`, moved without changing their names or types. They
use the actual residue equivalence, actual principal additive character,
and actual whole-ideal symbol. Their consumers can therefore check the
prime-power Fourier and finite-Poisson calculations before importing the
Artin/Kummer construction of arithmetic row characters.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualEuler

open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinActualGenerators
open HeckeSkeleton.HighBinActualSymbols
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance primeResidueField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance primeResidueFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

/-- The literal prime-level additive character, transferred across the
proved residue equivalence; this is not an arbitrary trace character. -/
def primeAddCharacter (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    AddChar (𝓞 K ⧸ p.val.asIdeal) ℂ :=
  transportCharacter (thetaPrimeResidueEquiv K S p)
    (thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p))

theorem primeAddCharacter_isPrimitive (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) : (primeAddCharacter K S D p).IsPrimitive :=
  transportCharacter_isPrimitive _ _
    (thetaPrincipalAddCharacter_isPrimitive K S D (exteriorPrimeIdeal K S p))

theorem thetaPrimeCharacter_order (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    orderOf (thetaPrimeCharacter K S D p) = 6 :=
  sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property)

/-- The whole-ideal quotient symbol specializes to the prescribed prime
residue character. This identifies the actual finite sum before applying
any Gauss norm or orthogonality theorem. -/
theorem primeQuotientSymbol_equiv (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (x : 𝓞 K ⧸ p.val.asIdeal) :
    symbolOnQuotient K S D (exteriorPrimeIdeal K S p) (thetaPrimeResidueEquiv K S p x) =
      thetaPrimeCharacter K S D p x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [thetaPrimeResidueEquiv, sIntegerResidueEquiv_mk,
    symbolOnQuotient, sIntegerSexticIdealQuotientFunction_mk]
  change idealSymbol K S D (exteriorPrimeIdeal K S p)
    (algebraMap (𝓞 K) (S.integer K) a) = _
  rw [idealSymbol_eq_idealCoefficient]
  change idealCoefficient (primeValue K S D (algebraMap (𝓞 K) (S.integer K) a))
    p.val.asIdeal = _
  rw [idealCoefficient_prime, primeValue, dif_pos p.property,
    sIntegerSexticEvaluation_algebraMap]
  rfl

/-- Every positive prime-level Gauss coefficient used in the finite table
is the repository's actual `thetaGamma`, with precisely its square-root
normalization. The exponent-zero unit mask is deliberately excluded. -/
theorem normalizedFamily_eq_thetaGamma (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (j : ℕ) (hj : j ≠ 0) :
    HighBin.ActualGaussPhases.normalizedFamily (thetaPrimeCharacter K S D p)
      (primeAddCharacter K S D p) j =
        thetaGamma K S D (exteriorPrimeIdeal K S p) j := by
  let Q := ThetaQuotient K S (exteriorPrimeIdeal K S p)
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S p.val.asIdeal
    p.val.ne_bot (exteriorPrimeIdeal K S p).property
  letI : Fintype Q := Fintype.ofFinite _
  let e : (𝓞 K ⧸ p.val.asIdeal) ≃+* Q := thetaPrimeResidueEquiv K S p
  have hsum :
      (∑ x : Q, symbolOnQuotient K S D (exteriorPrimeIdeal K S p) x ^ j *
        thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p) x) =
      gaussSum (thetaPrimeCharacter K S D p ^ j) (primeAddCharacter K S D p) := by
    calc
      _ = ∑ x : 𝓞 K ⧸ p.val.asIdeal,
          symbolOnQuotient K S D (exteriorPrimeIdeal K S p) (e x) ^ j *
            thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p) (e x) :=
        (e.toEquiv.sum_comp _).symm
      _ = _ := by
        unfold gaussSum
        apply Finset.sum_congr rfl
        intro x _
        rw [primeQuotientSymbol_equiv, MulChar.pow_apply' _ hj]
        rfl
  unfold HighBin.ActualGaussPhases.normalizedFamily
    HighBin.FiniteResidueFourier.normalizedGauss
  change gaussSum (thetaPrimeCharacter K S D p ^ j) (primeAddCharacter K S D p) /
      (Real.sqrt (Fintype.card (𝓞 K ⧸ p.val.asIdeal)) : ℂ) =
    (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
      ∑ x : Q, symbolOnQuotient K S D (exteriorPrimeIdeal K S p) x ^ j *
        thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p) x
  rw [hsum, card_primeIdealResidueField]
  ring

end HeckeSkeleton.HighBinActualEuler
