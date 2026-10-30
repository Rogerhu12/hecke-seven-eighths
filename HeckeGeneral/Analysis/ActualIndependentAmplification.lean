import HeckeGeneral.Analysis.ActualSIntegerBaseAmplification
import HeckeGeneral.Analysis.ActualSimultaneousMajorants
import HeckeGeneral.Analysis.ActualSIntegerAmplificationBound

/-! Sum the actual arbitrary-base amplification over every selected
sixth-power-free row. The exact simultaneous embedding avoids an extra
base-row count. Only the displayed scale majorant remains analytic input;
there is no assumed moment estimate or hidden row-character extension. -/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (τ : ThetaArithmeticData K S)

theorem actualIndependent_amplification_to_orbit_majorant {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : HeckeCharacter K)
      (R : Finset (ActualSixthPowerFreeOrbit K S)) (F : Finset (ExteriorIdeal K S))
      (U P H D : ℝ) (s : ℂ) (B : ActualSIntegerOrbit K S → ℝ),
      1 ≤ P → U * P ^ 6 ≤ H → 0 < D →
      (∀ q ∈ R, actualSIntegerOrbitNorm K S q.val ≤ U) →
      (∀ A ∈ F, idealNorm K A.val ≤ P) →
      (∀ q, 0 ≤ B q) →
      (∀ q, actualSIntegerOrbitNorm K S q ≤ H → ∀ r : ℝ,
        0 < r → r ≤ D →
        ‖actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η q r s‖ ^ 2
          ≤ B q) →
      (F.card : ℝ) * ∑ q ∈ R,
        ‖actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η q.val D s‖ ^ 2
        ≤ C * P ^ (2 * δ) * ∑ q : ActualBoundedSIntegerOrbits K S H, B q.val := by
  obtain ⟨C, hC, hmass⟩ := sexticAmplifierCoefficient_mass_small_power K hδ
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro η R F U P H D s B hP hPH hD hR hF hB hrow
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have heach (q : ActualSixthPowerFreeOrbit K S) (hq : q ∈ R)
      (A : ExteriorIdeal K S) (hA : A ∈ F) :
      ‖actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η q.val D s‖ ^ 2
        ≤ (C * P ^ δ) ^ 2 * B (actualSimultaneousAmplifier K S τ q.val A) := by
    apply actualSIntegerInversePolynomial_base_sq_le K S τ η q.val A hD s (hB _)
    · exact (hmass η A.val _ (dyadicDividingPrimes_thetaGenerator_subset K S τ A D)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (idealNorm_pos K A.val).le (hF A hA) hδ.le) hC.le)
    · intro T _
      exact hrow (actualSimultaneousAmplifier K S τ q.val A)
        ((actualSimultaneousAmplifier_norm_le K S τ q.val A (hR q hq) (hF A hA)).trans hPH)
        (D / idealNorm K (squarefreeIdeal K T))
        (div_pos hD (idealNorm_pos K _)) (div_le_self hD.le (one_le_idealNorm K _))
  have hsum := Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (heach q hq))
  have hsum' : (F.card : ℝ) * ∑ q ∈ R,
      ‖actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η q.val D s‖ ^ 2
      ≤ (C * P ^ δ) ^ 2 * ∑ q ∈ R, ∑ A ∈ F,
        B (actualSimultaneousAmplifier K S τ q.val A) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum] using hsum
  have hpow : (C * P ^ δ) ^ 2 = C ^ 2 * P ^ (2 * δ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hP0 δ 2]
    congr 1
    ring
  calc
    _ ≤ (C * P ^ δ) ^ 2 * ∑ q ∈ R, ∑ A ∈ F,
        B (actualSimultaneousAmplifier K S τ q.val A) := hsum'
    _ ≤ (C * P ^ δ) ^ 2 * ∑ q : ActualBoundedSIntegerOrbits K S H, B q.val :=
      mul_le_mul_of_nonneg_left
        (sum_simultaneous_majorants_le_bounded_orbits K S τ R F hR hF hPH B hB)
        (sq_nonneg _)
    _ = _ := by rw [hpow]

end HeckeGeneral.Analysis.ActualSIntegerMoments
