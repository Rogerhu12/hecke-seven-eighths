import HeckeSkeleton.LowFrozenCube.ExteriorData

/-!
# Literal phase correspondence with the marked reflected coefficient

The ordinary-prime interaction products use the original
`primeEvaluation` and `localWeylExponent`.  The mixed phase becomes the
two actual `idealSymbol` factors in `reflectedTerm`, with both collision
masks retained.  The numerator product uses the proved sixth-unit
invariance of the allowed section, rather than a strict generator identity.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowFrozenCube.Exterior

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowHybrid
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S) (hD : AllowedGeneratorInput K S D)

theorem symbol_generator_product (I J L : ExteriorIdeal K S) :
    ExteriorSymbol.symbolHom K S D hD I (J * L) =
      idealSymbol K S D I (D.generator J * D.generator L) := by
  rw [map_mul]
  change sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding
      I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => D.away_six p (I.property p hp)) (D.generator J) *
    sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding
      I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => D.away_six p (I.property p hp)) (D.generator L) = _
  exact (sIntegerSexticIdealEvaluation_mul K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) (D.generator J) (D.generator L)).symm

namespace Data

theorem negativeOrdinaryInteraction_eq (f : Data K S) (a I : ExteriorIdeal K S) :
    negativeOrdinaryInteraction f.ordinary (f.toFrozen K S D hD).ordinarySymbol
      (fun p => (f.digit p).val)
      (PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) a) I =
      ∏ p ∈ f.ordinary, primeEvaluation K S D p (D.generator I) ^
        (-(2 * localWeylExponent (f.digit p) (primeExponents a.val p.val) : ℤ)) := by
  unfold negativeOrdinaryInteraction
  apply Finset.prod_congr rfl
  intro p _
  rw [ordinarySymbol_eq]
  congr 1
  simp only [ExteriorArithmetic.valuation_coords, localPhaseDigit, localWeylExponent]

theorem positiveOrdinaryInteraction_eq (f : Data K S) (a I : ExteriorIdeal K S) :
    positiveOrdinaryInteraction f.ordinary (f.toFrozen K S D hD).ordinarySymbol
      (fun p => (f.digit p).val)
      (PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) a) I =
      ∏ p ∈ f.ordinary, primeEvaluation K S D p (D.generator I) ^
        localWeylExponent (f.digit p) (primeExponents a.val p.val) := by
  unfold positiveOrdinaryInteraction
  apply Finset.prod_congr rfl
  intro p _
  rw [ordinarySymbol_eq]
  rfl

/-- The two mixed characters are precisely the quadratic and inverse
cubic characters used by the original `reflectedTerm`. -/
theorem mixedPhase_eq_actual (f : Data K S) (d P c n : ExteriorIdeal K S) :
    (f.toFrozen K S D hD).mixedPhase d P c n =
      (if IsCoprime P.val.val d.val.val then (1 : ℂ) else 0) *
        (idealSymbol K S D d (D.generator c * D.generator n) ^ 3 *
          idealSymbol K S D P (D.generator c) ^ (-2 : ℤ) *
          (if IsCoprime P.val.val n.val.val then (1 : ℂ) else 0)) := by
  rw [FrozenReduction.Data.mixedPhase_eq]
  have hn := symbol_zpow_neg_two (f.toFrozen K S D hD).symbol
    (PrimeCoordinates.Coprime (f.toFrozen K S D hD).coords)
    (f.toFrozen K S D hD).sixth P c
  rw [← hn]
  change (if PrimeCoordinates.Coprime (ExteriorArithmetic.coords K S) P d
      then (1 : ℂ) else 0) *
    ((ExteriorSymbol.symbolHom K S D hD d (c * n)) ^ 3 *
      idealSymbol K S D P (D.generator c) ^ (-2 : ℤ) *
      (if PrimeCoordinates.Coprime (ExteriorArithmetic.coords K S) P n
        then (1 : ℂ) else 0)) = _
  rw [ExteriorArithmetic.coords_coprime_iff, ExteriorArithmetic.coords_coprime_iff,
    symbol_generator_product]

theorem mixedPhase_eq_actual_of_coprime (f : Data K S)
    (d P c n : ExteriorIdeal K S)
    (hPd : IsCoprime P.val.val d.val.val) (hPn : IsCoprime P.val.val n.val.val) :
    (f.toFrozen K S D hD).mixedPhase d P c n =
      idealSymbol K S D d (D.generator c * D.generator n) ^ 3 *
        idealSymbol K S D P (D.generator c) ^ (-2 : ℤ) := by
  rw [mixedPhase_eq_actual, if_pos hPd, if_pos hPn, one_mul, mul_one]

end Data

#print axioms symbol_generator_product
#print axioms Data.negativeOrdinaryInteraction_eq
#print axioms Data.mixedPhase_eq_actual

end HeckeSkeleton.LowFrozenCube.Exterior
