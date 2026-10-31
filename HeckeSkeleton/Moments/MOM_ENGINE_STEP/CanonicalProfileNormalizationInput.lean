import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileNormalizationInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedMomentProfiles

/-!
# The concrete profile operation used by the actual capacity producer

The public normalization operation proves its homogeneity directly from
the literal finite polynomials.  This module supplies that operation to
the earlier raw Schwartz-window and capacity interfaces.  No homogeneity
law or admissibility assertion remains an external input when this
canonical instance is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Scaling by `c` is the concrete normalization with positive radius
`c⁻¹`.  Every arithmetic carrier, coefficient and formal length is
preserved by the literal record update. -/
def canonicalProfileNormalizationInput : ProfileNormalizationInput K ω ψ where
  scaleData d c hc := normalizedMomentProfiles d c⁻¹ (inv_pos.mpr hc)
  slotCount _ _ _ := rfl
  slotEquiv _ _ _ := Equiv.refl _
  slotLength _ _ _ _ := rfl
  totalLength _ _ _ := rfl
  fitsMesh _ _ _ _ := Iff.rfl
  rows _ _ _ := rfl
  allowedRow _ _ _ := rfl
  commonMask _ _ _ := rfl
  rowCharacter _ _ _ := rfl
  theta _ _ _ := rfl
  direction _ _ _ := rfl
  inverseBackground _ _ _ := rfl
  plainBackground _ _ _ := rfl
  slotCoefficient _ _ _ _ := rfl
  inverse_support _ _ _ := rfl
  plain₁_support _ _ _ := rfl
  plain₂_support _ _ _ := rfl
  prime_support _ _ _ _ := rfl
  inverse_profile d c hc u t y := by
    change (((c⁻¹)⁻¹ : ℝ) : ℂ) * d.inverseTest.profile u t y = _
    rw [inv_inv]
  plain₁_profile d c hc u t y := by
    change (((c⁻¹)⁻¹ : ℝ) : ℂ) * d.plainTest₁.profile u t y = _
    rw [inv_inv]
  plain₂_profile d c hc u t y := by
    change (((c⁻¹)⁻¹ : ℝ) : ℂ) * d.plainTest₂.profile u t y = _
    rw [inv_inv]
  prime_profile d c hc i t y := by
    change (((c⁻¹)⁻¹ : ℝ) : ℂ) * (d.geometry.slots i).profile t y = _
    rw [inv_inv]
  energy_scale d p c hc Z t := by
    simpa only [inv_inv] using
      pairedEnergy_normalizedMomentProfiles d p c⁻¹ (inv_pos.mpr hc) Z t

/-- The generic normalization is exactly the new concrete constructor,
including its individual profile representatives. -/
theorem canonicalProfileNormalizationInput_normalize
    (d : MomentData K ω ψ) (A : ℝ) (hA : 0 < A) :
    canonicalProfileNormalizationInput.normalizeData d A hA =
      normalizedMomentProfiles d A hA := by
  simp only [ProfileNormalizationInput.normalizeData,
    canonicalProfileNormalizationInput, inv_inv]

/-- The original fixed Schwartz-window conclusion is now available for
the concrete normalized child without a supplied scaling theorem. -/
theorem normalizedMomentProfiles_in_fixed_window
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {s : Finset (ℕ × ℕ)} {d : MomentData K ω ψ} {A : ℝ}
    (hA : 0 < A) (w : RawProfileWindow rowDomain heightDomain window s d A) :
    InFixedProfileWindow rowDomain heightDomain window s
      (normalizedMomentProfiles d A hA) := by
  simpa only [canonicalProfileNormalizationInput_normalize] using
    (canonicalProfileNormalizationInput (K := K) (ω := ω) (ψ := ψ)).
      normalized_in_fixed_window hA w

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.canonicalProfileNormalizationInput
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalProfileNormalizationInput_normalize
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedMomentProfiles_in_fixed_window
