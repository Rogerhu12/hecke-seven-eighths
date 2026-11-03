import HeckeGeneral.Analysis.SIntegerSixthPowerDecomposition

/-!
Literal coefficient calibration on complete-ideal rows in a fixed unit
sector. The common mask is fixed-S/6 deletion together with coprimality
to the COMPLETE row ideal. No admissibility or moment estimate is claimed.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- This is the original exceptional and complete-row coprimality mask. -/
def decomposedIdealRowMask (I : ExteriorIdeal K S) (J : NonzeroIdeal K) : ℂ :=
  if sexticIdealOutsideS K S J ∧ IsCoprime J.val I.val.val then 1 else 0

theorem actualOrbitSexticEvaluation_frequencyRow (u : FrequencyRow K S)
    (J : ExteriorIdeal K S) :
    actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
      P.arithmetic.embedding J.val (frequencyRowOrbit K S P u) =
      idealSymbol K S P.arithmetic J (frequencyRowElement K S P u) := by
  have hgood : sexticIdealOutsideS K S J.val := by
    intro p hp
    exact ⟨J.property p hp, P.arithmetic.away_six p (J.property p hp)⟩
  rw [frequencyRowOrbit, actualOrbitSexticEvaluation_mk]
  unfold zeroExtendedSexticIdealEvaluation
  rw [dite_eq_left hgood]
  rfl

theorem actualOrbitSexticEvaluation_decomposed_character
    (x : ExteriorIdeal K S × SixthUnitClasses K S) (J : NonzeroIdeal K) :
    actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding J (decomposedIdealSectorOrbit K S P x) =
      heckeIdealCoefficient K (R.character (decomposedFrequencyRow K S x.1 x.2)) J *
        decomposedIdealRowMask K S x.1 J := by
  by_cases hgood : sexticIdealOutsideS K S J
  · let J' : ExteriorIdeal K S := ⟨J, fun p hp => (hgood p hp).1⟩
    have hcal := R.coefficient_calibration (decomposedFrequencyRow K S x.1 x.2) J'
    rw [← actualOrbitSexticEvaluation_frequencyRow K S P] at hcal
    rw [actualOrbitSexticEvaluation_decomposedIdealSector, ← hcal]
    have hfactor : x.1.val.val =
        (sixthPowerFreePart x.1.val).val * (sixthPowerAmplifierPart x.1.val).val ^ 6 :=
      congrArg Subtype.val (sixthPowerFreePart_mul_amplifier_sixth x.1.val).symm
    have hcop : IsCoprime J.val x.1.val.val ↔
        IsCoprime J.val (sixthPowerFreePart x.1.val).val ∧
          IsCoprime J.val (sixthPowerAmplifierPart x.1.val).val := by
      rw [hfactor, IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 6)]
    change (if IsCoprime J.val (sixthPowerFreePart x.1.val).val then _ else 0) * _ = _
    by_cases hb : IsCoprime J.val (sixthPowerFreePart x.1.val).val <;>
      by_cases ha : IsCoprime J.val (sixthPowerAmplifierPart x.1.val).val <;>
      simp [J', decomposedIdealRowMask, hgood, hcop, hb, ha]
  · rw [← actualOrbitSexticEvaluation_out]
    simp [zeroExtendedSexticIdealEvaluation_eq_zero K S P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding J _ hgood,
      decomposedIdealRowMask, hgood]

/-- The inverse power preserves every zero of the same complete-row mask. -/
theorem actualOrbitSexticEvaluation_decomposed_inverse
    (x : ExteriorIdeal K S × SixthUnitClasses K S) (J : NonzeroIdeal K) :
    actualOrbitSexticEvaluation K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding J (decomposedIdealSectorOrbit K S P x) ^ (-1 : ℤ) =
      heckeIdealCoefficient K (R.character (decomposedFrequencyRow K S x.1 x.2)) J ^ (-1 : ℤ) *
        decomposedIdealRowMask K S x.1 J := by
  rw [actualOrbitSexticEvaluation_decomposed_character K S P R]
  by_cases h : sexticIdealOutsideS K S J ∧ IsCoprime J.val x.1.val.val <;>
    simp [decomposedIdealRowMask, h]

/-- Literal finite inverse polynomial for any test, with all original zeros. -/
theorem sIntegerSexticInverseIdealPolynomial_decomposed_character
    (η : HeckeCharacter K) (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (F : Finset (NonzeroIdeal K)) (D : ℝ) (W : ℝ → ℂ) :
    sIntegerSexticInverseIdealPolynomial K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding η F (decomposedIdealSectorOrbit K S P x).out.val D W =
      (Real.sqrt D : ℂ)⁻¹ * ∑ J ∈ F,
        (UniqueFactorizationMonoid.moebius J.val : ℂ) * heckeIdealCoefficient K η J *
        heckeIdealCoefficient K (R.character (decomposedFrequencyRow K S x.1 x.2)) J ^ (-1 : ℤ) *
        W (idealNorm K J / D) * decomposedIdealRowMask K S x.1 J := by
  unfold sIntegerSexticInverseIdealPolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  unfold sIntegerSexticInverseIdealTerm
  rw [actualOrbitSexticEvaluation_out,
    actualOrbitSexticEvaluation_decomposed_inverse K S P R]
  ring

/-- The actual dyadic Mellin family is a specialization of the same identity. -/
theorem actualSIntegerInversePolynomial_decomposed_character
    (η : HeckeCharacter K) (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (D : ℝ) (s : ℂ) :
    actualSIntegerInversePolynomial K S P.arithmetic.root6 P.arithmetic.primitive6
        P.arithmetic.embedding η (decomposedIdealSectorOrbit K S P x) D s =
      (Real.sqrt D : ℂ)⁻¹ * ∑ J ∈ dyadicIdealSupport K D,
        (UniqueFactorizationMonoid.moebius J.val : ℂ) * heckeIdealCoefficient K η J *
        heckeIdealCoefficient K (R.character (decomposedFrequencyRow K S x.1 x.2)) J ^ (-1 : ℤ) *
        dyadicMellinWeight s (idealNorm K J / D) * decomposedIdealRowMask K S x.1 J := by
  rw [← actualSIntegerInversePolynomial_out]
  exact sIntegerSexticInverseIdealPolynomial_decomposed_character K S P R η x _ D _

end HeckeGeneral.ThetaSkeleton.Physical
