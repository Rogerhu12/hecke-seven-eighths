import HeckeGeneral.Analysis.ActualSIntegerSimultaneousAmplifier
import HeckeGeneral.Analysis.ActualSIntegerScaleDerivative
import HeckeGeneral.Characters.SIntegerSexticPowerMask

/-! Exact common amplifier deletion on actual quotient rows.
Multiplication by generator(A)^6 preserves the original row evaluation
and deletes precisely the denominator ideals meeting A. Existing zeros
from the base row and the fixed S/6 deletion remain zeros. This does not
replace an actual row coefficient by an invented Hecke character. -/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- The literal fixed-S/6 zero-extended symbol descends to every original
sixth-power S-unit sector. -/
def actualOrbitSexticEvaluation (I : NonzeroIdeal K) (q : ActualSIntegerOrbit K S) : ℂ :=
  Quotient.liftOn q (fun a => zeroExtendedSexticIdealEvaluation K S ζ hζ σ I a.val) (by
    intro a b hab
    obtain ⟨γ, hγ⟩ :=
      (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S) a b).mp hab
    have heq : (S.unitEquivUnitsInteger K γ.val).val * b.val = a.val := Subtype.ext hγ
    rw [← heq]
    exact zeroExtendedSexticIdealEvaluation_sixthSubgroup_invariant K S ζ hζ σ I γ b.val)

@[simp] theorem actualOrbitSexticEvaluation_mk
    (I : NonzeroIdeal K) (a : NonzeroRingElements (S.integer K)) :
    actualOrbitSexticEvaluation K S ζ hζ σ I (Quotient.mk _ a) =
      zeroExtendedSexticIdealEvaluation K S ζ hζ σ I a.val := rfl

theorem actualOrbitSexticEvaluation_out (I : NonzeroIdeal K) (q : ActualSIntegerOrbit K S) :
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ I q.out.val =
      actualOrbitSexticEvaluation K S ζ hζ σ I q := by
  simpa only [actualOrbitSexticEvaluation_mk] using
    congrArg (actualOrbitSexticEvaluation K S ζ hζ σ I) (Quotient.out_eq q)

variable (τ : ThetaArithmeticData K S)

theorem zeroExtendedSexticIdealEvaluation_thetaGenerator_sixth_mul
    (I : NonzeroIdeal K) (A : ExteriorIdeal K S) (u : S.integer K) :
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ I (τ.generator A ^ 6 * u) =
      if IsCoprime I.val A.val.val then
        zeroExtendedSexticIdealEvaluation K S ζ hζ σ I u else 0 := by
  by_cases hI : sexticIdealOutsideS K S I
  · simp only [zeroExtendedSexticIdealEvaluation, dite_eq_left hI]
    rw [sIntegerSexticIdealEvaluation_mul,
      sIntegerSexticIdealEvaluation_sixth_power_coprime_mask,
      contraction_thetaGenerator K S τ A]
    by_cases hc : IsCoprime I.val A.val.val <;> simp [hc]
  · simp [zeroExtendedSexticIdealEvaluation_eq_zero K S ζ hζ σ I _ hI]

theorem actualOrbitSexticEvaluation_simultaneousAmplifier
    (I : NonzeroIdeal K) (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S) :
    actualOrbitSexticEvaluation K S ζ hζ σ I (actualSimultaneousAmplifier K S τ q A) =
      if IsCoprime I.val A.val.val then actualOrbitSexticEvaluation K S ζ hζ σ I q else 0 := by
  refine Quotient.inductionOn q ?_
  intro a
  change zeroExtendedSexticIdealEvaluation K S ζ hζ σ I (τ.generator A ^ 6 * a.val) = _
  exact zeroExtendedSexticIdealEvaluation_thetaGenerator_sixth_mul K S ζ hζ σ τ I A a.val

theorem actualOrbitSexticEvaluation_simultaneousAmplifier_product
    (I : NonzeroIdeal K) (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S) :
    actualOrbitSexticEvaluation K S ζ hζ σ I (actualSimultaneousAmplifier K S τ q A) =
      actualOrbitSexticEvaluation K S ζ hζ σ I q *
        (if IsCoprime I.val A.val.val then 1 else 0) := by
  rw [actualOrbitSexticEvaluation_simultaneousAmplifier]
  by_cases hc : IsCoprime I.val A.val.val <;> simp [hc]

/-- Scale-independent coefficient identity, including zeros of the base
row and of either fixed exceptional deletion. -/
theorem actualInverseIdealCoefficient_simultaneousAmplifier
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S)
    (A : ExteriorIdeal K S) (I : NonzeroIdeal K) :
    actualInverseIdealCoefficient K S ζ hζ σ η
        (actualSimultaneousAmplifier K S τ q A).out.val I =
      if IsCoprime I.val A.val.val then
        actualInverseIdealCoefficient K S ζ hζ σ η q.out.val I else 0 := by
  simp only [actualInverseIdealCoefficient, actualOrbitSexticEvaluation_out]
  rw [actualOrbitSexticEvaluation_simultaneousAmplifier]
  by_cases hc : IsCoprime I.val A.val.val <;> simp [hc]

/-- The amplified finite sum is exactly the base row with the common
A-deletion. There is deliberately no unmasked polynomial equality. -/
theorem sIntegerInverseIdealPolynomial_simultaneousAmplifier
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S)
    (F : Finset (NonzeroIdeal K)) (D : ℝ) (W : ℝ → ℂ) :
    sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η F
        (actualSimultaneousAmplifier K S τ q A).out.val D W =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
        (F.filter (fun I => IsCoprime I.val A.val.val)) q.out.val D W := by
  unfold sIntegerSexticInverseIdealPolynomial
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I _
  change actualInverseIdealCoefficient K S ζ hζ σ η
      (actualSimultaneousAmplifier K S τ q A).out.val I * W (idealNorm K I / D) =
    if IsCoprime I.val A.val.val then
      actualInverseIdealCoefficient K S ζ hζ σ η q.out.val I * W (idealNorm K I / D) else 0
  rw [actualInverseIdealCoefficient_simultaneousAmplifier]
  by_cases hc : IsCoprime I.val A.val.val <;> simp [hc]

theorem actualSIntegerInversePolynomial_simultaneousAmplifier
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S)
    (D : ℝ) (s : ℂ) :
    actualSIntegerInversePolynomial K S ζ hζ σ η
        (actualSimultaneousAmplifier K S τ q A) D s =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
        ((dyadicIdealSupport K D).filter (fun I => IsCoprime I.val A.val.val))
        q.out.val D (dyadicMellinWeight s) := by
  rw [← actualSIntegerInversePolynomial_out]
  exact sIntegerInverseIdealPolynomial_simultaneousAmplifier K S ζ hζ σ τ η q A
    (dyadicIdealSupport K D) D (dyadicMellinWeight s)

theorem actualFiniteInverseLogPolynomial_simultaneousAmplifier
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S)
    (F : Finset (NonzeroIdeal K)) (W : ℝ → ℂ) (t : ℝ) :
    actualFiniteInverseLogPolynomial K S ζ hζ σ η F
        (actualSimultaneousAmplifier K S τ q A).out.val W t =
      actualFiniteInverseLogPolynomial K S ζ hζ σ η
        (F.filter (fun I => IsCoprime I.val A.val.val)) q.out.val W t := by
  rw [actualFiniteInverseLogPolynomial_eq, actualFiniteInverseLogPolynomial_eq]
  exact sIntegerInverseIdealPolynomial_simultaneousAmplifier K S ζ hζ σ τ η q A F
    (Real.exp t) W

end HeckeGeneral.Analysis.ActualSIntegerMoments
