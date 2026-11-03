import HeckeGeneral.Analysis.TInputPrincipal
import HeckeGeneral.Arithmetic.SIntegerTripleReindex
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Literal sixth-unit invariance of the physical probe

UNCOMPILED candidate; static source inspection only.
All reindexings below are bijections within a single sum. No interchange
of infinite sums, summability hypothesis, or global theta reflection is used.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem idealSymbol_mul_sixth_unit (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (u : S.unit K) (a : S.integer K) :
    idealSymbol K S D I ((S.unitEquivUnitsInteger K u).val ^ 6 * a) =
      idealSymbol K S D I a :=
  sIntegerSexticIdealEvaluation_mul_sixth_power_unit K S D.root6 D.primitive6
    D.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) u a

theorem completedThetaSum_mul_sixth_unit (D : ThetaArithmeticData K S)
    (θ : HeckeCharacter K) (u : S.unit K) (a : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ) :
    completedThetaSum K S D θ ((S.unitEquivUnitsInteger K u).val ^ 6 * a) r Q V X =
      completedThetaSum K S D θ a r Q V X := by
  apply tsum_congr
  intro cn
  simp only [completedTerm, idealSymbol_mul_sixth_unit]

/-- Finite quotient multiplication by the actual sixth power of a global
S-unit changes neither the residue weight nor the Gauss frequency sum. -/
theorem probeGauss_mul_sixth_unit (P : ProbeData K S) (I : ExteriorIdeal K S)
    (u : S.unit K) (k : S.integer K) :
    probeGauss K S P I ((S.unitEquivUnitsInteger K u).val ^ 6 * k) =
      probeGauss K S P I k := by
  letI : Finite (ThetaQuotient K S I) :=
    finite_sIntegerSexticIdealQuotient K S I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  let χ := sIntegerSexticIdealQuotientFunction K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => P.arithmetic.away_six p (I.property p hp))
  let v : (ThetaQuotient K S I)ˣ :=
    Units.map (Ideal.Quotient.mk
      (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))).toMonoidHom
      ((S.unitEquivUnitsInteger K u) ^ 6)
  have hv : (v : ThetaQuotient K S I) =
      Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u).val ^ 6) := by
    simp only [v, Units.coe_map, Units.val_pow_eq_pow_val]
    rfl
  have hχ : ∀ d : ThetaQuotient K S I, χ ((v : ThetaQuotient K S I) * d) = χ d := by
    intro d
    refine Quotient.inductionOn' d ?_
    intro a
    change χ ((v : ThetaQuotient K S I) * Ideal.Quotient.mk _ a) =
      χ (Ideal.Quotient.mk _ a)
    rw [hv, ← map_mul]
    exact (sIntegerSexticIdealQuotientFunction_mk K S P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => P.arithmetic.away_six p (I.property p hp)) _).trans
        ((idealSymbol_mul_sixth_unit K S P.arithmetic I u a).trans
          (sIntegerSexticIdealQuotientFunction_mk K S P.arithmetic.root6
            P.arithmetic.primitive6 P.arithmetic.embedding I.val.val
            (nonZeroDivisors.coe_ne_zero I.val) I.property
            (fun p hp => P.arithmetic.away_six p (I.property p hp)) a).symm)
  change (∑ d : ThetaQuotient K S I, χ d * thetaPrincipalAddCharacter K S P.arithmetic I
      (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u).val ^ 6 * k) * d)) =
    ∑ d : ThetaQuotient K S I, χ d * thetaPrincipalAddCharacter K S P.arithmetic I
      (Ideal.Quotient.mk _ k * d)
  apply Fintype.sum_equiv v.mulLeft
  intro d
  change χ d * thetaPrincipalAddCharacter K S P.arithmetic I
      (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u).val ^ 6 * k) * d) =
    χ ((v : ThetaQuotient K S I) * d) * thetaPrincipalAddCharacter K S P.arithmetic I
      (Ideal.Quotient.mk _ k * ((v : ThetaQuotient K S I) * d))
  rw [hχ]
  apply congrArg (fun x => χ d * thetaPrincipalAddCharacter K S P.arithmetic I x)
  rw [hv, map_mul]
  ring

/-- The actual nonzero S-integer index permutation, retaining all elements. -/
def probeSixthUnitIndexEquiv (u : S.unit K) :
    NonzeroRingElements (S.integer K) ≃ NonzeroRingElements (S.integer K) :=
  sIntegerTranslateEquiv K S ⊤ ⟨u ^ 6, Subgroup.mem_top _⟩

@[simp] theorem probeSixthUnitIndexEquiv_val (u : S.unit K)
    (m : NonzeroRingElements (S.integer K)) :
    (probeSixthUnitIndexEquiv K S u m).val =
      (S.unitEquivUnitsInteger K u).val ^ 6 * m.val := by
  change (S.unitEquivUnitsInteger K (u ^ 6)).val * m.val = _
  rw [map_pow, Units.val_pow_eq_pow_val]

theorem probeSixthUnitIndexEquiv_diagonal (u : S.unit K)
    (m : NonzeroRingElements (S.integer K)) :
    sLocalNonzeroIntegerDiagonal K S (probeSixthUnitIndexEquiv K S u m) =
      sLocalDiagonal K S (u ^ 6) * sLocalNonzeroIntegerDiagonal K S m :=
  sLocalNonzeroIntegerDiagonal_translate K S ⊤ ⟨u ^ 6, Subgroup.mem_top _⟩ m

theorem probeRowTerm_sixth_unit_covariance (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Z : ℝ) (u : S.unit K)
    (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S)
    (m : NonzeroRingElements (S.integer K)) :
    probeRowTerm K S P ψ Q X Z (sLocalNormOneDiagonal K S (u ^ 6) * t) I
        (probeSixthUnitIndexEquiv K S u m) =
      probeRowTerm K S P ψ Q X Z t I m := by
  unfold probeRowTerm
  split_ifs with h
  · simp only [probeSixthUnitIndexEquiv_val]
    rw [show -((S.unitEquivUnitsInteger K u).val ^ 6 * m.val) =
        (S.unitEquivUnitsInteger K u).val ^ 6 * (-m.val) by rw [mul_neg],
      probeGauss_mul_sixth_unit, completedThetaSum_mul_sixth_unit,
      probeSixthUnitIndexEquiv_diagonal]
    have hd : (((sLocalNormOneDiagonal K S (u ^ 6) * t : sLocalNormOneGroup K S) :
        sLocalMultiplicativeGroup K S)) = sLocalDiagonal K S (u ^ 6) *
          (t : sLocalMultiplicativeGroup K S) := rfl
    rw [hd]
    have harg : (sLocalDiagonal K S (u ^ 6) * sLocalNonzeroIntegerDiagonal K S m) /
        ((sLocalDiagonal K S (u ^ 6) * (t : sLocalMultiplicativeGroup K S)) *
          sLocalNormSection K S ⟨exteriorNorm K S I * X, h⟩) =
        sLocalNonzeroIntegerDiagonal K S m /
          ((t : sLocalMultiplicativeGroup K S) *
            sLocalNormSection K S ⟨exteriorNorm K S I * X, h⟩) := by
      simp only [mul_assoc, mul_div_mul_left_eq_div]
    rw [harg]
  · rfl

/-- Exact original field, including all its positive-parameter quantifiers.
No absolute convergence is needed for bijective single-sum reindexing. -/
theorem probeIntegralInput_sixth_unit_invariant (P : ProbeData K S) (ψ : HeckeCharacter K) :
    ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
      0 < X → 0 < Y → 0 < Z → ∀ (u : S.unit K) (t : sLocalNormOneGroup K S),
        probeIntegrand K S P ψ Q X Y Z (sLocalNormOneDiagonal K S (u ^ 6) * t) =
          probeIntegrand K S P ψ Q X Y Z t := by
  intro Q X Y Z _hX _hY _hZ u t
  apply tsum_congr
  intro I
  unfold probeDenominatorTerm
  congr 1
  calc
    (∑' m, probeRowTerm K S P ψ Q X Z
        (sLocalNormOneDiagonal K S (u ^ 6) * t) I m) =
      ∑' m, probeRowTerm K S P ψ Q X Z
        (sLocalNormOneDiagonal K S (u ^ 6) * t) I
          (probeSixthUnitIndexEquiv K S u m) :=
      ((probeSixthUnitIndexEquiv K S u).tsum_eq _).symm
    _ = _ := tsum_congr fun m => probeRowTerm_sixth_unit_covariance K S P ψ Q X Z u t I m

end HeckeGeneral.ThetaSkeleton.Physical
