import ActualSexticOriginalChartMean
import ActualRCorrectionSixthUnit
import ActualResidualSixthUnit

/-!
UNCOMPILED / native 0. The original raw coefficient, actual ALL-S Hilbert
correction and stipulated residual extension are invariant under the two
independent sixth-unit column actions at the SAME divisor and frequency.
Every shared-prime zero is retained. This supplies only the arithmetic
part of a two-column unit-partition identity, not the analytic identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ActualOriginalChartSixthUnitDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualRCorrectionSixthUnitDraft ActualResidualSixthUnitDraft

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "Γ" => MonoidHom.range (powMonoidHom 6 : S.unit K →* S.unit K)

private theorem divisorColumn_translate_right (u : Γ) (d m : NZ) :
    divisorColumn K S d (sIntegerOrbitTranslate K S Γ u m) =
      sIntegerOrbitTranslate K S Γ u (divisorColumn K S d m) := by
  apply Subtype.ext
  change d.val * ((S.unitEquivUnitsInteger K u.val).val * m.val) =
    (S.unitEquivUnitsInteger K u.val).val * (d.val * m.val)
  ring

/-- Denominator unit invariance leaves the original frequency and its
negative second numerator unchanged. No character value is cancelled. -/
private theorem rawCoefficient_fixed_frequency (u v : Γ) (a b k : NZ) :
    sIntegerSexticRawCoefficient K S ζ hζ σ hS6
        (sIntegerOrbitTranslate K S Γ u a) (sIntegerOrbitTranslate K S Γ v b) k =
      sIntegerSexticRawCoefficient K S ζ hζ σ hS6 a b k := by
  simp only [sIntegerSexticRawCoefficient, sIntegerOrbitTranslate,
    sIntegerSexticSymbol_denominator_invariant]

/-- The exact original coefficient is unchanged by independent sixth-unit
column translations; c, k and d are fixed and no coprimality is required. -/
theorem originalChartCoefficient_sixthPower_columns
    (c k d m₁ m₂ : NZ) (u v : Γ) :
    originalChartCoefficient K S ζ hζ σ hS6 c k d
        (sIntegerOrbitTranslate K S Γ u m₁) (sIntegerOrbitTranslate K S Γ v m₂) =
      originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂ := by
  have hres := actualResidualExtension_sixthPower_columns K S ζ hζ σ
    (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
    (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)
    (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k)
    hS6 d.val k.val m₁.val m₂.val u v
  unfold originalChartCoefficient
  rw [divisorColumn_translate_right K S u d m₁,
    divisorColumn_translate_right K S v d m₂,
    rawCoefficient_fixed_frequency K S ζ hζ σ hS6,
    sIntegerSexticRCorrection_sixthPower_translate K S ζ hζ σ]
  exact congrArg (fun z : ℂ =>
    (sIntegerSexticRawCoefficient K S ζ hζ σ hS6
        (divisorColumn K S d m₁) (divisorColumn K S d m₂) k *
      sIntegerSexticRCorrection K S ζ hζ σ
        (divisorColumn K S d m₁) (divisorColumn K S d m₂)) * z) hres

end HeckeGeneral.Characters.ActualOriginalChartSixthUnitDraft
