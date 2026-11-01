import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalRowScalar
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalOriginalLabel

/-!
# Exact exceptional normalization with the original annulus cost

The actual Gauss scales remain unchanged. A fixed cost in their lower
window is transferred to the scalar bound by an explicit square-root
identity. The original row amplitude, common envelope, orbital radius,
common radical and child width all remain those of the same row mass.

The final scalar lemma is an internal algebraic composition used after
the actual source factory has proved its magnitude estimate. It does
not supply a new analytic assumption for the engine theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis HeckePort.Moments
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsPrincipalIdealRing A.R]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {kCommonLeft kCommonRight : ℕ}

namespace ActualSecondRowMass

/-- A fixed annulus cost multiplies the old relative row budget once.
The scaled auxiliary real number only proves the algebraic comparison;
the returned expression still contains the original two Gauss scales. -/
theorem original_rowFactor_budget_with_centralCost
    (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    (Z : ℝ) (hZ : 1 < Z)
    (a₀ q wo w boundary krow g ell NL NR parentWidth remaining g₂ t₂ error
      centralCost : ℝ)
    (hcost : 0 < centralCost)
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hcentral : Z ^ a₀ ≤ centralCost * (Real.sqrt NL * Real.sqrt NR))
    (hwindow : g₂ - t₂ ≤
      idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
        idealLogLength Z W.unitIdeal.val + error)
    (hremaining : a₀ + q + w + boundary + wo + ell + error - parentWidth ≤ remaining) :
    (W.originalRowAmplitude * Z ^ (g₂ - t₂) / (Real.sqrt NL * Real.sqrt NR)) *
        Z ^ (secondCommonChildWidth Z a₀ q wo krow g
            W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
          secondCommonChildAllowance Z w boundary ell W.leftIdeal W.rightIdeal) / Z ^ parentWidth ≤
      centralCost * (W.commonEnvelope * orbitalFieldFactor F) * Z ^ remaining /
        (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hsqrt : Real.sqrt (centralCost ^ 2 * NL) = centralCost * Real.sqrt NL := by
    rw [Real.sqrt_mul (sq_nonneg centralCost), Real.sqrt_sq hcost.le]
  have hcentral' : Z ^ a₀ ≤ Real.sqrt (centralCost ^ 2 * NL) * Real.sqrt NR := by
    simpa only [hsqrt, mul_assoc] using hcentral
  have hden : Real.sqrt NL * Real.sqrt NR ≠ 0 := by
    intro he
    rw [he, mul_zero] at hcentral
    exact (not_le_of_gt (Real.rpow_pos_of_pos hz a₀)) hcentral
  have hNL : Real.sqrt NL ≠ 0 := left_ne_zero_of_mul hden
  have hNR : Real.sqrt NR ≠ 0 := right_ne_zero_of_mul hden
  have hp : Z ^ parentWidth ≠ 0 := (Real.rpow_pos_of_pos hz _).ne'
  have hb := W.original_rowFactor_budget_relative_allowance Z hZ
    a₀ q wo w boundary krow g ell (centralCost ^ 2 * NL) NR
    parentWidth remaining g₂ t₂ error hrow hcentral' hwindow hremaining
  have hm := mul_le_mul_of_nonneg_left hb hcost.le
  rw [hsqrt] at hm
  convert hm using 1
  · field_simp [hcost.ne', hden, hNL, hNR, hp]
    <;> ring
  · ring

end ActualSecondRowMass

namespace CanonicalExceptionalPaidNormalization

/-- Compose a proved source estimate with the same relative row
budget. The physical cutoff cost is already part of `margin`, while
the fixed Gauss annulus cost is already part of `envelope`. -/
theorem relative_of_magnitude
    (Z magnitude rowFactor envelope radical coefficient childWidth actualWidth parentWidth
      remaining widthError margin divisorLower : ℝ)
    (hZ : 1 ≤ Z) (hcoefficient : 0 ≤ coefficient)
    (henvelope : 0 ≤ envelope) (hradical : 0 ≤ radical)
    (hsource : Z ^ (-childWidth) * magnitude ≤
      rowFactor * coefficient * Z ^ (margin - divisorLower))
    (hrow : rowFactor * Z ^ actualWidth / Z ^ parentWidth ≤
      envelope * Z ^ remaining / radical)
    (hwidth : childWidth - actualWidth ≤ widthError) :
    magnitude / Z ^ parentWidth ≤
      envelope * coefficient * Z ^ (remaining + widthError + margin) /
        radical * Z ^ (-divisorLower) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hpowc : Z ^ childWidth ≠ 0 := (Real.rpow_pos_of_pos hz _).ne'
  have hpowp : Z ^ parentWidth ≠ 0 := (Real.rpow_pos_of_pos hz _).ne'
  have hscale := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsource (Real.rpow_nonneg hz.le childWidth))
    (Real.rpow_nonneg hz.le parentWidth)
  have hrecover : Z ^ childWidth * (Z ^ (-childWidth) * magnitude) / Z ^ parentWidth =
      magnitude / Z ^ parentWidth := by
    rw [Real.rpow_neg hz.le]
    field_simp [hpowc, hpowp] <;> ring
  rw [hrecover] at hscale
  have hsplit : Z ^ childWidth = Z ^ actualWidth * Z ^ (childWidth - actualWidth) := by
    rw [← Real.rpow_add hz]
    congr 1
    ring
  calc
    _ ≤ Z ^ childWidth * (rowFactor * coefficient * Z ^ (margin - divisorLower)) /
        Z ^ parentWidth := hscale
    _ = (rowFactor * Z ^ actualWidth / Z ^ parentWidth) * coefficient *
        Z ^ ((childWidth - actualWidth) + (margin - divisorLower)) := by
      rw [hsplit, Real.rpow_add hz]
      ring
    _ ≤ (envelope * Z ^ remaining / radical) * coefficient *
        Z ^ (widthError + (margin - divisorLower)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hrow hcoefficient)
        (Real.rpow_le_rpow_of_exponent_le hZ (add_le_add hwidth le_rfl))
        (Real.rpow_nonneg hz.le _)
        (mul_nonneg
          (div_nonneg (mul_nonneg henvelope (Real.rpow_nonneg hz.le _)) hradical)
          hcoefficient)
    _ = _ := by
      simp only [Real.rpow_add hz, Real.rpow_sub hz, Real.rpow_neg hz.le]
      ring

end CanonicalExceptionalPaidNormalization
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.original_rowFactor_budget_with_centralCost
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidNormalization.relative_of_magnitude
