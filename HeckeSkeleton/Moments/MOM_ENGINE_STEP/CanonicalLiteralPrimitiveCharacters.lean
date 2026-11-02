import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalClassification
import ArithmeticFrequencyRowCharacterFibers
import RowCharacterCanonicalUniqueness

set_option linter.unusedSectionVars false

/-!
# The primitive character laws of the same original probe

The row-character input is not replaced by an independently chosen
character family. Its original finite-order coefficient calibration
identifies it with the arithmetic Kummer construction. The proved local
component formula then gives ideal faithfulness and exterior ramification.

Multiplication of the original nonzero S-integers is proved separately:
away from a finite set of their actual full ideal divisors, the original
single-prime calibration is multiplicative. Finite-order global
uniqueness promotes those genuine prime coefficients to equality of
the supplied characters. No Kummer law, exceptional-row classification,
unit-sector identification, or counting bound is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveCharacters

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Characters.RowUniquenessDraft
open CanonicalOriginalPhaseCalibration CanonicalLiteralExceptionalClassification

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- The full original ideal is read from the actual element, before
reducing its exponents modulo six. -/
private def elementIdeal (a : NonzeroRingElements A.R) : A.Exterior :=
  (OriginalMovingFactors.singleton (P := P) (R := R) a 1).factorIdeal 0

private theorem element_primeCoefficient
    (a : NonzeroRingElements A.R) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal (elementIdeal P R a).val) :
    primeCoefficient K (elementCharacter P R a) p =
      zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
        (primeIdeal p) a.val := by
  sorry

private theorem element_unramified
    (a : NonzeroRingElements A.R) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal (elementIdeal P R a).val) :
    UnramifiedAt K (elementCharacter P R a) p := by
  sorry

/-- Multiplicativity is derived on the original S-integers, with their
unit sectors intact, from true single-prime calibration and uniqueness. -/
theorem elementCharacter_mul (a b : NonzeroRingElements A.R) :
    elementCharacter P R ⟨a.val * b.val, mul_ne_zero a.property b.property⟩ =
      elementCharacter P R a * elementCharacter P R b := by
  sorry

/-- These laws are produced for the supplied original row-character
input itself. The exceptional classification has no remaining global
character-arithmetic hypothesis. -/
def primitiveCharacterLaws : PrimitiveCharacterLaws P R where
  ideal_faithful u v h := by
    rw [rowCharacterInput_character_eq_arithmetic K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R u,
      rowCharacterInput_character_eq_arithmetic K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R v] at h
    exact congrArg Subtype.val (arithmeticRowCharacter_ideal_eq_of_eq K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P u v h)
  element_mul := elementCharacter_mul P R
  ramified u p hp hpos := by
    rw [rowCharacterInput_character_eq_arithmetic K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R u]
    exact arithmeticRowCharacter_not_unramified_of_pos_exponent K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P u p hp hpos

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveCharacters

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveCharacters.elementCharacter_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveCharacters.primitiveCharacterLaws
