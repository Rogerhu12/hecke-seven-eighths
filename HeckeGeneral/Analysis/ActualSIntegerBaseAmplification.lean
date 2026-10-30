import HeckeGeneral.Analysis.SIntegerSexticBaseMellinAmplification

/-! Arbitrary-base amplification on the actual sixth-power S-unit quotient.
The common amplifier deletion and all base-row zeros remain literal.
The quotient may lie in any original unit sector. -/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (τ : ThetaArithmeticData K S)

theorem dyadicMellin_thetaGenerator_mul_eq_simultaneousAmplifier
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S)
    (D : ℝ) (s : ℂ) :
    dyadicSexticMellinInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η
        (τ.generator A ^ 6 * q.out.val) D s =
      actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η
        (actualSimultaneousAmplifier K S τ q A) D s := by
  let u : NonzeroRingElements (S.integer K) :=
    ⟨τ.generator A ^ 6 * q.out.val, mul_ne_zero (pow_ne_zero 6 (τ.generator_ne_zero A))
      q.out.property⟩
  have he : Quotient.mk _ u = actualSimultaneousAmplifier K S τ q A := by
    change actualSimultaneousAmplifier K S τ (Quotient.mk _ q.out) A =
      actualSimultaneousAmplifier K S τ q A
    exact congrArg (fun v => actualSimultaneousAmplifier K S τ v A) (Quotient.out_eq q)
  change dyadicSexticMellinInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η u.val D s = _
  rw [dyadicSexticMellinInversePolynomial_eq_orbit, he]

/-- The exact quotient-row identity used by simultaneous amplification. -/
theorem actualSIntegerInversePolynomial_base_amplification
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S)
    {D : ℝ} (hD : 0 < D) (s : ℂ) :
    actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η q D s =
      ∑ T ∈ (dyadicDividingPrimes K S (τ.generator A) D).powerset,
        sexticBaseAmplifierCoefficient K S τ.root6 τ.primitive6 τ.embedding η q.out.val T *
          actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η
            (actualSimultaneousAmplifier K S τ q A)
            (D / idealNorm K (squarefreeIdeal K T)) s := by
  rw [← actualSIntegerInversePolynomial_out]
  change dyadicSexticMellinInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η
    q.out.val D s = _
  rw [dyadicSexticMellinInversePolynomial_base_amplification K S τ.root6 τ.primitive6
    τ.embedding η q.out.val (τ.generator A) hD s]
  apply Finset.sum_congr rfl
  intro T _
  rw [dyadicMellin_thetaGenerator_mul_eq_simultaneousAmplifier]

/-- Cauchy uses only the original Hecke/Moebius divisor mass. Its constant
does not depend on the base row, and no base coprimality is assumed. -/
theorem actualSIntegerInversePolynomial_base_sq_le
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (A : ExteriorIdeal K S)
    {D W B : ℝ} (hD : 0 < D) (s : ℂ) (hB : 0 ≤ B)
    (hmass : ∑ T ∈ (dyadicDividingPrimes K S (τ.generator A) D).powerset,
      ‖sexticAmplifierCoefficient K η T‖ ≤ W)
    (hrow : ∀ T ∈ (dyadicDividingPrimes K S (τ.generator A) D).powerset,
      ‖actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η
        (actualSimultaneousAmplifier K S τ q A)
        (D / idealNorm K (squarefreeIdeal K T)) s‖ ^ 2 ≤ B) :
    ‖actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η q D s‖ ^ 2
      ≤ W ^ 2 * B := by
  rw [← actualSIntegerInversePolynomial_out]
  apply dyadicSexticMellinInversePolynomial_base_sq_le K S τ.root6 τ.primitive6 τ.embedding
    η q.out.val (τ.generator A) hD s hB hmass
  intro T hT
  rw [dyadicMellin_thetaGenerator_mul_eq_simultaneousAmplifier]
  exact hrow T hT

end HeckeGeneral.Analysis.ActualSIntegerMoments
