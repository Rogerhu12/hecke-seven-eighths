import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSignedProfileBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalChildFourierControl

set_option linter.unusedSectionVars false

/-!
# The signed original profiles control the same Fourier children

The actual two-stage Gauss compensation leaves the signed exponent
`j * δ - 1` and a scale-one logarithmic atom. Its bounded positive
prefactor costs at most the square root of the fixed original annulus.
That cost remains explicit in the actual normalization amplitude.

The existing capacity children and their exact radii are retained.
Their finite Fourier controls are produced from the original profile
updates, and both actual kernel bounds come from the fixed continuous
linear maps. The resulting mass profile has no moving scale, common
ideal or Fourier offset in its constant. No transformed amplitude or
completed profile-control bound is supplied.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

/-- All costs of the original signed profile and its actual clipping,
including the bounded Gauss prefactor, are fixed before the source. -/
def signedClippedAmplitudeConstant
    (a B : ℝ) (ha : 0 < a) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (directionBound : ℝ) : ℝ :=
  clippingCoefficient B orders *
    signedAmplitudeConstant (Set.Icc a B) isCompact_Icc (positiveAnnulus a B ha)
      orders δ R cap directionBound * Real.sqrt B

theorem signedClippedAmplitudeConstant_nonneg
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (directionBound : ℝ) (hD : 0 ≤ directionBound) :
    0 ≤ signedClippedAmplitudeConstant a B ha orders δ R cap directionBound := by
  sorry

namespace OriginalLogProfiles

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (D : OriginalLogProfiles K ω ψ (WithLp 2 (U × E)))

/-- The actual amplitude uses the original seminorm multiplied by
the fixed Gauss prefactor. The signed power is paid on the original
positive compact support, independently of every phase offset. -/
theorem signed_amplitude_bound
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (orders : Finset (ℕ × ℕ))
    (δ : ℝ) (R cap : ℕ) (directionBound P : ℝ)
    (hD : 0 ≤ directionBound) (hP : 0 ≤ P)
    (hcount : D.original.geometry.slotCount ≤ cap)
    (hexponent : ∀ i, (D.atom i).exponent ∈ shiftedExponentPalette δ R)
    (hdirection : ∀ i, ‖(D.atom i).direction‖ ≤ directionBound)
    (hscale : ∀ i, (D.atom i).scale = 1) :
    D.amplitude a B ha orders (Real.sqrt B * P) ≤
      signedClippedAmplitudeConstant a B ha orders δ R cap directionBound * P := by
  sorry

end OriginalLogProfiles

section SameFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [MeasurableSpace (WithLp 2 (ℝ × ℝ))] [BorelSpace (WithLp 2 (ℝ × ℝ))]

/-- The original signed atoms and the two fixed kernel maps produce
all profile fields for the already selected family. Radius degrees
are fixed by `orders` before the separate kernel targets are supplied.

For a bounded child, `left.original` and `right.original` are the
literal positive-scalar updates of its frozen original profiles. Their
original seminorm bounds are `sqrt B * P`, and the radius below is the
same one used by `clippedPolynomialWindow` and `chosen_profile_windows`.
The only family identities are its actual data, height, kernels and
radius definitions; no seminorm bound for a moving child is an input.
-/
theorem exists_signed_family_profile_controls
    (orders : Finset (ℕ × ℕ)) (R cap : ℕ)
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (δ directionBound τ : ℝ) (hD : 0 ≤ directionBound) (hτ : 0 ≤ τ)
    (T₁ T₂ : 𝓢(W, ℂ) →L[ℝ] 𝓢(ℝ, ℂ))
    (target₁ target₂ : Finset (ℕ × ℕ)) :
    ∃ source : Finset (ℕ × ℕ), ∃ Cprofile : ℝ, 1 ≤ Cprofile ∧
      ∀ {Λ : Type*} (Z P : ℝ), 1 ≤ Z → 1 ≤ P →
      ∀ (family : ActualNormalizedPairFamily A σ (WithLp 2 (ℝ × ℝ)) Λ ω ψ Z)
        (labels : Finset Λ)
        (left right : Λ → OriginalLogProfiles K ω ψ (WithLp 2 (ℝ × ℝ)))
        (leftTime rightTime : Λ → ℝ),
      (∀ b ξ, (family.leftCalibration b).data ξ = (left b).moving ξ) →
      (∀ b ξ, (family.rightCalibration b).data ξ = (right b).moving ξ) →
      (∀ b ξ, (family.leftCalibration b).height ξ = leftTime b) →
      (∀ b ξ, (family.rightCalibration b).height ξ = rightTime b) →
      ∀ (φ₁ φ₂ : Λ → 𝓢(W, ℂ)) (F₁ F₂ : Λ → 𝓢(ℝ, ℂ)) (outer : Λ → ℝ),
      (∀ b ∈ labels, F₁ b = T₁ (φ₁ b)) →
      (∀ b ∈ labels, F₂ b = T₂ (φ₂ b)) →
      (∀ b ∈ labels, source.sup (schwartzSeminormFamily ℝ W ℂ) (φ₁ b) ≤ P) →
      (∀ b ∈ labels, source.sup (schwartzSeminormFamily ℝ W ℂ) (φ₂ b) ≤ P) →
      (∀ b ∈ labels, 0 ≤ outer b) →
      (∀ b ∈ labels, (left b).original.geometry.slotCount ≤ cap) →
      (∀ b ∈ labels, (right b).original.geometry.slotCount ≤ cap) →
      (∀ b ∈ labels, ∀ i, ((left b).atom i).exponent ∈ shiftedExponentPalette δ R) →
      (∀ b ∈ labels, ∀ i, ((right b).atom i).exponent ∈ shiftedExponentPalette δ R) →
      (∀ b ∈ labels, ∀ i, ‖((left b).atom i).direction‖ ≤ directionBound) →
      (∀ b ∈ labels, ∀ i, ‖((right b).atom i).direction‖ ≤ directionBound) →
      (∀ b ∈ labels, ∀ i, ((left b).atom i).scale = 1) →
      (∀ b ∈ labels, ∀ i, ((right b).atom i).scale = 1) →
      (∀ b ∈ labels, ∀ z, (family.leftCapacity b).radius (WithLp.toLp 2 z) =
        polynomialProfileRadius ((left b).amplitude a B ha orders (Real.sqrt B * P))
          (orders.sup Prod.snd) (orders.sup Prod.snd) z) →
      (∀ b ∈ labels, ∀ z, (family.rightCapacity b).radius (WithLp.toLp 2 z) =
        polynomialProfileRadius ((right b).amplitude a B ha orders (Real.sqrt B * P))
          (orders.sup Prod.snd) (orders.sup Prod.snd) z) →
      ∃ atoms : family.FourierAtomControl labels
        (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd),
        InternalMassAssembly.ProfileWindows family labels F₁ F₂ outer
          (fun b => (left b).amplitude a B ha orders (Real.sqrt B * P))
          (fun b => (right b).amplitude a B ha orders (Real.sqrt B * P)) (Cprofile * P * Z ^ τ)
          cap (orders.sup Prod.snd) (orders.sup Prod.snd)
          (orders.sup Prod.snd) (orders.sup Prod.snd) 1 1 1 1 target₁ target₂ := by
  sorry

end SameFamily
end HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.OriginalLogProfiles.signed_amplitude_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.exists_signed_family_profile_controls
