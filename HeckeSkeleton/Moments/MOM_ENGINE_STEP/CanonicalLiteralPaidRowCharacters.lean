import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowCharacters

set_option linter.unusedSectionVars false

/-!
# The same ordinary rows after removing an amplifier sixth power

The character attached to an original moving element is computed from
its actual sixth-power-free frequency row, including its unit sector.
Multiplication by a nonzero sixth power preserves that row.  The proof
uses the original orbit relation and uniqueness of the physical
frequency-row/amplifier decomposition; no character extensionality or
unmasked coefficient identity is assumed.

The pool factors of multiplicity one, six and seven therefore have the
same complete Hecke characters as their reduced active factors.  Their
zero-extended ideal evaluations still have the different masks proved
in `CanonicalLiteralPassivePhases`.  This distinction lets the new paid
source retain the original ordinary-row predicate exactly.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

section ActualRows

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

private def sixthDilation (a : NonzeroRingElements (S.integer K))
    (q : ActualSIntegerOrbit K S) : ActualSIntegerOrbit K S :=
  sIntegerOrbitDilation K S (sixthPowerSUnitSubgroup K S)
    ⟨a.val ^ 6, pow_ne_zero 6 a.property⟩ q

/-- Associated generators have identical sixth-power actions on the
actual quotient, even though the generators themselves need not agree. -/
private theorem sixthDilation_eq_of_span
    (a b : NonzeroRingElements (S.integer K))
    (hspan : Ideal.span ({a.val} : Set (S.integer K)) =
      Ideal.span ({b.val} : Set (S.integer K)))
    (q : ActualSIntegerOrbit K S) :
    sixthDilation K S a q = sixthDilation K S b q := by
  sorry

private theorem sixthDilation_comp
    (a b : NonzeroRingElements (S.integer K)) (q : ActualSIntegerOrbit K S) :
    sixthDilation K S a (sixthDilation K S b q) =
      sixthDilation K S (sIntegerNonzeroMul K S a b) q := by
  sorry

variable (P : ProbeData K S)

private theorem simultaneousAmplifier_comp (q : ActualSIntegerOrbit K S)
    (I J : HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S) :
    actualSimultaneousAmplifier K S P.arithmetic
        (actualSimultaneousAmplifier K S P.arithmetic q I) J =
      actualSimultaneousAmplifier K S P.arithmetic q (exteriorMul K S J I) := by
  sorry

/-- The actual physical base row used in `OriginalMovingFactors`.
Its unit sector comes from the original orbit equivalence. -/
def frequencyBase (q : ActualSIntegerOrbit K S) : FrequencyRow K S :=
  let x := (exteriorIdealSectorsEquivActualOrbits K S P).symm q
  decomposedFrequencyRow K S x.1 x.2

private def frequencyAmplifier (q : ActualSIntegerOrbit K S) :
    HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S :=
  exteriorSixthPowerAmplifierPart S
    ((exteriorIdealSectorsEquivActualOrbits K S P).symm q).1

private theorem frequencyBase_spec (q : ActualSIntegerOrbit K S) :
    actualSimultaneousAmplifier K S P.arithmetic
        (frequencyRowOrbit K S P (frequencyBase K S P q))
        (frequencyAmplifier K S P q) = q := by
  sorry

theorem frequencyBase_simultaneousAmplifier (q : ActualSIntegerOrbit K S)
    (I : HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S) :
    frequencyBase K S P (actualSimultaneousAmplifier K S P.arithmetic q I) =
      frequencyBase K S P q := by
  sorry

/-- The sixth power can use any actual nonzero generator.  Its
principal ideal supplies the amplifier, and the unit discrepancy is
removed in the original sixth-unit quotient. -/
theorem frequencyBase_sixth_mul
    (a b : NonzeroRingElements (S.integer K)) :
    frequencyBase K S P (Quotient.mk _
      (⟨a.val ^ 6 * b.val, mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ :
        NonzeroRingElements (S.integer K))) =
      frequencyBase K S P (Quotient.mk _ b) := by
  sorry

end ActualRows

open LocalFiniteSums CanonicalLiteralPhaseCalibration CanonicalLiteralPaidCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- A complete Hecke-character identity, obtained by equality of the
actual inputs to the original row-character function. -/
theorem singleton_character_sixth_mul (a b : NonzeroRingElements A.R) (e : ℤ) :
    (OriginalMovingFactors.singleton (P := P) (R := R)
      ⟨a.val ^ 6 * b.val, mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ e).character =
      (OriginalMovingFactors.singleton (P := P) (R := R) b e).character := by
  sorry

/-- The original one/six/seven pool factor and the reduced active
factor have the same character, while their deletion masks stay separate. -/
theorem poolMoving_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity)) :
    (F.poolMoving P R).character =
      (CanonicalLiteralPassivePhases.activeMoving P R C p e).character := by
  sorry

theorem moving_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) :
    (F.moving P R oldMoving).character =
      ((reducedPhases F C p e).moving P R oldMoving).character := by
  sorry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem appended_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool) :
    ((F.moving P R oldMoving).appendSecondFactor C primes m n pattern).character =
      (((reducedPhases F C p e).moving P R oldMoving).appendSecondFactor
        C primes m n pattern).character := by
  sorry

theorem rowCharacter_eq (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (primes : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C primes m n
        pattern ν u =
      CanonicalLiteralAllocatedData.rowCharacter P R (reducedPhases F C p e)
        oldMoving correction C primes m n pattern ν u := by
  sorry

theorem literalCharacter_eq {H : Type*} (S : ActualSecondCorrelationRows A σ H ι)
    (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (h : H) :
    S.literalCharacter C P R F oldMoving correction pattern ν h =
      S.literalCharacter C P R (reducedPhases F C p e) oldMoving correction pattern ν h := by
  sorry

/-- The original ordinary filter is unchanged before any passive
allocation or normalized child is selected. -/
theorem ordinary_iff {H : Type*} (S : ActualSecondCorrelationRows A σ H ι)
    (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (theta : Finset (HeckeCharacter K)) (h : H) :
    S.literalCharacter C P R F oldMoving correction pattern ν h ∉ theta ↔
      S.literalCharacter C P R (reducedPhases F C p e) oldMoving correction pattern ν h ∉ theta := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.frequencyBase_sixth_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.singleton_character_sixth_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.poolMoving_character
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.appended_character
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.literalCharacter_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.ordinary_iff
