import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMassBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllowanceCancellation

/-!
# Original row amplitudes and the exceptional common-support scalar

The actual frozen common factors prove the row amplitude.  Original
dyadic gcd/unit windows pay an explicit error.  The genuine radius,
the two original Gauss scales and the original first allowance then
leave the second common-radical density. No capacity allocation cost
or inverse second-divisor norm occurs here; the exceptional divisor
factor is paid by its separate original dyadic window.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {kLeft kRight : ℕ} (W : ActualSecondRowMass R C kLeft kRight)

def originalRowAmplitude : ℝ :=
  ‖secondOrbitalScalar (K := F) (S := A.Sf) W.radius W.mask‖ *
    W.commonEnvelope / W.commonDenominator

theorem originalRowAmplitude_nonneg : 0 ≤ W.originalRowAmplitude :=
  div_nonneg (mul_nonneg (norm_nonneg _) W.commonEnvelope_nonneg) W.commonDenominator_nonneg

theorem rowBound_eq_originalRowAmplitude :
    W.rowBound = W.originalRowAmplitude * W.correlationBound := rfl

/-- This input to the exceptional row theorem is computed from the
original row profile and each original frozen atom. -/
theorem original_row_weight_bound (h : H) (hh : h ∈ R.rows) :
    ‖R.weight h‖ ≤ W.originalRowAmplitude := by
  have hl := W.leftAtoms.norm_le C h hh
  have hr := W.rightAtoms.norm_le C h hh
  rw [W.left_ideal] at hl
  rw [W.right_ideal] at hr
  have h₀ := mul_le_mul_of_nonneg_left (W.profile_bound h hh)
    (norm_nonneg (secondOrbitalScalar (K := F) (S := A.Sf) W.radius W.mask))
  have h₁ := mul_le_mul h₀ hl (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) W.profileBound_nonneg)
  have h₂ := mul_le_mul h₁ hr (norm_nonneg _)
    (mul_nonneg (mul_nonneg (norm_nonneg _) W.profileBound_nonneg)
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  calc
    _ = ‖secondOrbitalScalar (K := F) (S := A.Sf) W.radius W.mask‖ *
        ‖W.rowProfile h‖ * ‖W.leftAtoms.value h‖ * ‖W.rightAtoms.value h‖ := by
      rw [W.weight_eq h hh]
      simp only [norm_mul, norm_star]
    _ ≤ _ := h₂
    _ = W.originalRowAmplitude := by
      unfold originalRowAmplitude commonEnvelope commonDenominator leftIdeal rightIdeal
      ring

theorem correlationBound_eq_rpow (Z : ℝ) (hZ : 1 < Z) :
    W.correlationBound =
      Z ^ (idealLogLength Z (gcd W.leftIdeal W.rightIdeal) - idealLogLength Z W.unitIdeal.val) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hD : W.leftIdeal ≠ 0 := (primePowerProduct R.primes R.leftMultiplicity).property.1
  rw [Real.rpow_sub hz,
    rpow_idealLogLength Z hZ _ (gcd_ne_zero_of_left hD),
    rpow_idealLogLength Z hZ _ W.unitIdeal.property.1]
  rfl

/-- A dyadic upper gcd exponent and lower unit exponent are compared
with the actual ideal norms, with their explicit original bin error. -/
theorem original_rowFactor_dyadic_le
    (Z : ℝ) (hZ : 1 < Z) (g₂ t₂ error NL NR : ℝ)
    (hwindow : g₂ - t₂ ≤
      idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
        idealLogLength Z W.unitIdeal.val + error) :
    W.originalRowAmplitude * Z ^ (g₂ - t₂) / (Real.sqrt NL * Real.sqrt NR) ≤
      (W.rowBound / (Real.sqrt NL * Real.sqrt NR)) * Z ^ error := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc : Z ^ (g₂ - t₂) ≤ W.correlationBound * Z ^ error := by
    rw [W.correlationBound_eq_rpow Z hZ, ← Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hwindow
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc W.originalRowAmplitude_nonneg)
    (mul_nonneg (Real.sqrt_nonneg NL) (Real.sqrt_nonneg NR))
  apply h.trans_eq
  rw [W.rowBound_eq_originalRowAmplitude]
  ring

/-- Both original Gauss normalizers and the real row radius cancel
against the width/allowance before the same first normalization.
The output contains no second-divisor factor. -/
theorem original_rowFactor_budget_relative_allowance
    (Z : ℝ) (hZ : 1 < Z)
    (a₀ q wo w boundary krow g ell NL NR parentWidth remaining g₂ t₂ error : ℝ)
    (hrow : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (hwindow : g₂ - t₂ ≤
      idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
        idealLogLength Z W.unitIdeal.val + error)
    (hremaining : a₀ + q + w + boundary + wo + ell + error - parentWidth ≤ remaining) :
    (W.originalRowAmplitude * Z ^ (g₂ - t₂) / (Real.sqrt NL * Real.sqrt NR)) *
        Z ^ (secondCommonChildWidth Z a₀ q wo krow g
            W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
          secondCommonChildAllowance Z w boundary ell W.leftIdeal W.rightIdeal) / Z ^ parentWidth ≤
      (W.commonEnvelope * orbitalFieldFactor F) * Z ^ remaining /
        (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc := W.original_rowFactor_dyadic_le Z hZ g₂ t₂ error NL NR hwindow
  have hb := W.normalized_row_budget Z hZ a₀ q wo w boundary krow g ell NL NR hrow hcentral
  have hc' := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hz.le
      (secondCommonChildWidth Z a₀ q wo krow g
          W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
        secondCommonChildAllowance Z w boundary ell W.leftIdeal W.rightIdeal)))
    (Real.rpow_nonneg hz.le parentWidth)
  have hb' := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le error)) (Real.rpow_nonneg hz.le parentWidth)
  have hbudget :
      (W.originalRowAmplitude * Z ^ (g₂ - t₂) / (Real.sqrt NL * Real.sqrt NR)) *
          Z ^ (secondCommonChildWidth Z a₀ q wo krow g
              W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
            secondCommonChildAllowance Z w boundary ell W.leftIdeal W.rightIdeal) / Z ^ parentWidth ≤
        (W.commonEnvelope *
          (orbitalFieldFactor F * Z ^ (a₀ + q + w + boundary) * Z ^ wo * Z ^ ell /
            (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ))) *
          Z ^ error / Z ^ parentWidth := by
    apply hc'.trans
    convert hb' using 1 <;> ring
  have he : Z ^ (a₀ + q + w + boundary) * Z ^ wo * Z ^ ell * Z ^ error / Z ^ parentWidth =
      Z ^ (a₀ + q + w + boundary + wo + ell + error - parentWidth) := by
    rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_sub hz]
  apply hbudget.trans
  calc
    _ = (W.commonEnvelope * orbitalFieldFactor F) *
        (Z ^ (a₀ + q + w + boundary) * Z ^ wo * Z ^ ell * Z ^ error / Z ^ parentWidth) /
          (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ) := by ring
    _ = _ := by rw [he]
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hremaining)
        (mul_nonneg W.commonEnvelope_nonneg (orbitalFieldFactor_nonneg F))) (Nat.cast_nonneg _)

end HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.original_row_weight_bound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.original_rowFactor_budget_relative_allowance
