import HeckeGeneral.Analysis.ActualIndependentOrbitEnergy
import HeckeGeneral.Analysis.WitnessRowCount
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.WitnessCalibration

/-!
# Independent amplification with a complete-row scale-supremum seed

The seed explicitly controls every complete quotient row, including sixth
powers, with a common majorant over the divisor scales.  This is the input
used by the arithmetic amplifier in the repository.  A moment over only
sixth-power-free rows, or unrelated fixed-scale profiles, does not supply
that input.

The resulting witness estimate is uniform over the whole bounded length
interval: its preliminary losses and constant are chosen before `U` and `r`.
-/

noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton
open scoped BigOperators Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (τ : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- A correctly quantified replacement for the arithmetic core of
`MI-I-AMPLIFIED-WITNESS-CALIBRATION`, on the actual ideal orbit polynomial.
The complete-row scale-supremum seed is an explicit dependency of the
canonical inverse induction. -/
theorem actual_witness_energy
    {R loss : ℝ} (hR : 0 ≤ R) (hloss : 0 < loss)
    (T : Set ℂ) (hT : IsCompact T) (χ : HeckeCharacter K)
    (hMI : ActualTargetZeroSlotScaleSupInput K (S : Set (HeightOneSpectrum (𝓞 K)))
      τ.root6 τ.primitive6 τ.embedding χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U r : ℝ, 1 ≤ U → 0 ≤ r → r ≤ R →
      ∀ F : Finset (ActualSixthPowerFreeOrbit K (S : Set (HeightOneSpectrum (𝓞 K)))),
        (∀ q ∈ F, actualSIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) q.val ≤ U) →
        ∀ s ∈ T,
          (∑ q ∈ F,
            ‖actualSIntegerInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
              τ.root6 τ.primitive6 τ.embedding χ q.val (U ^ r) s‖ ^ 2) ≤
            C * U ^ (amplifiedInverseExponent r + loss) := by
  obtain ⟨a, ε, ha, hε, hallocate⟩ := exists_witness_loss_allocation hR hloss
  obtain ⟨C, hC, hamp⟩ := actualTargetScaleSup_independentOrbitEnergy K S τ
    ha hε T hT χ hMI
  refine ⟨C, hC, ?_⟩
  intro U r hU hr hrR F hF s hs
  have hD : 1 ≤ U ^ r := Real.one_le_rpow hU hr
  have he := hamp U (U ^ r) hU hD F hF s hs
  calc
    _ ≤ C * (max U (U ^ (1 / 6 : ℝ) * (U ^ r) ^ (5 * (1 + a) / 6)) *
        (U * U ^ r) ^ ε) := by simpa only [mul_assoc] using he
    _ ≤ _ := mul_le_mul_of_nonneg_left (hallocate U r hU hr hrR) hC.le

end HeckeSkeleton.Moments.UniformAmplify
