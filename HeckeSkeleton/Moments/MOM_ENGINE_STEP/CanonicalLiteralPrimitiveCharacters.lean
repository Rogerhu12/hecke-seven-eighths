import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalClassification
import ArithmeticFrequencyRowCharacterFibers
import RowCharacterCanonicalUniqueness

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
  let D := OriginalMovingFactors.singleton (P := P) (R := R) a 1
  have h := D.factor_evaluation_of_coprime 0 (primeIdeal p)
    (outside_prime P p hp) hcop
  simpa only [coefficient_prime] using h.symm

private theorem element_unramified
    (a : NonzeroRingElements A.R) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal (elementIdeal P R a).val) :
    UnramifiedAt K (elementCharacter P R a) p :=
  (OriginalMovingFactors.singleton (P := P) (R := R) a 1).
    factorCharacter_unramified 0 p hp hcop

/-- Multiplicativity is derived on the original S-integers, with their
unit sectors intact, from true single-prime calibration and uniqueness. -/
theorem elementCharacter_mul (a b : NonzeroRingElements A.R) :
    elementCharacter P R ⟨a.val * b.val, mul_ne_zero a.property b.property⟩ =
      elementCharacter P R a * elementCharacter P R b := by
  let ab : NonzeroRingElements A.R :=
    ⟨a.val * b.val, mul_ne_zero a.property b.property⟩
  have ha := idealPrimeDivisors_finite K (elementIdeal P R a).val
    (elementIdeal P R a).property.1
  have hb := idealPrimeDivisors_finite K (elementIdeal P R b).val
    (elementIdeal P R b).property.1
  have hab := idealPrimeDivisors_finite K (elementIdeal P R ab).val
    (elementIdeal P R ab).property.1
  let bad := A.Sf ∪ (ha.toFinset ∪ (hb.toFinset ∪ hab.toFinset))
  apply finiteOrder_heckeCharacter_eq_of_primeCoefficient_eq_away K
    (elementCharacter P R ab) (elementCharacter P R a * elementCharacter P R b)
    (R.finite_order _) ((R.finite_order _).mul (R.finite_order _)) bad
  intro p hp
  have hpS : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) := by
    intro h
    exact hp (Finset.mem_union_left _ h)
  have hpa : ¬p.asIdeal ∣ (elementIdeal P R a).val := by
    intro h
    have hm : p ∈ idealPrimeDivisors K (elementIdeal P R a).val := h
    exact hp (Finset.mem_union_right _
      (Finset.mem_union_left _ (ha.mem_toFinset.mpr hm)))
  have hpb : ¬p.asIdeal ∣ (elementIdeal P R b).val := by
    intro h
    have hm : p ∈ idealPrimeDivisors K (elementIdeal P R b).val := h
    exact hp (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_left _ (hb.mem_toFinset.mpr hm))))
  have hpab : ¬p.asIdeal ∣ (elementIdeal P R ab).val := by
    intro h
    have hm : p ∈ idealPrimeDivisors K (elementIdeal P R ab).val := h
    exact hp (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_right _ (hab.mem_toFinset.mpr hm))))
  have hca := isCoprime_primeIdeal_of_not_dvd K p _ hpa
  have hcb := isCoprime_primeIdeal_of_not_dvd K p _ hpb
  have hcab := isCoprime_primeIdeal_of_not_dvd K p _ hpab
  rw [primeCoefficient_mul_right_unramified K _ _ p
      (element_unramified P R b p hpS hcb),
    element_primeCoefficient P R ab p hpS hcab,
    element_primeCoefficient P R a p hpS hca,
    element_primeCoefficient P R b p hpS hcb]
  exact zeroExtendedSexticIdealEvaluation_original_mul P (primeIdeal p) a.val b.val

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
