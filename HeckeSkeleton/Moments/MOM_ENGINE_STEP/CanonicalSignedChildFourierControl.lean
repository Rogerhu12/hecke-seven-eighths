import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSignedProfileBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalChildFourierControl

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
    0 ≤ signedClippedAmplitudeConstant a B ha orders δ R cap directionBound :=
  mul_nonneg
    (mul_nonneg (zero_le_one.trans (clippingCoefficient_one_le B hB orders))
      (zero_le_one.trans (signedAmplitudeConstant_one_le (Set.Icc a B) isCompact_Icc
        (positiveAnnulus a B ha) orders δ R cap directionBound hD)))
    (Real.sqrt_nonneg B)

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
  exact clippedProfileAmplitude_le_shifted a B ha hB orders δ R cap
    directionBound (Real.sqrt B) P hD (Real.sqrt_nonneg B) hP
    D.original D.left D.right D.slot hcount
    (hexponent .left) (hexponent .right) (fun i => hexponent (.prime i))
    (hdirection .left) (hdirection .right) (fun i => hdirection (.prime i))
    (hscale .left) (hscale .right) (fun i => hscale (.prime i))

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
  obtain ⟨source, Ckernel, hCkernel, hkernel⟩ :=
    fixedKernelPair_source_bounds T₁ T₂ target₁ target₂
  let Cclip := signedClippedAmplitudeConstant a B ha orders δ R cap directionBound
  have hCclip : 0 ≤ Cclip :=
    signedClippedAmplitudeConstant_nonneg a B ha hB orders δ R cap directionBound hD
  let Cprofile := 1 + Cclip + Ckernel
  have hCprofile : 1 ≤ Cprofile := by dsimp only [Cprofile]; linarith
  have hclip_le : Cclip ≤ Cprofile := by dsimp only [Cprofile]; linarith
  have hkernel_le : Ckernel ≤ Cprofile := by dsimp only [Cprofile]; linarith
  refine ⟨source, Cprofile, hCprofile, ?_⟩
  intro Λ Z P hZ hP family labels left right leftTime rightTime
    hleftData hrightData hleftTime hrightTime φ₁ φ₂ F₁ F₂ outer
    hF₁ hF₂ hφ₁ hφ₂ houter hleftCount hrightCount hleftExp hrightExp
    hleftDirection hrightDirection hleftScale hrightScale hleftRadius hrightRadius
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hscaledP : 0 ≤ Real.sqrt B * P := mul_nonneg (Real.sqrt_nonneg B) hP0
  have hprofile0 : 0 ≤ Cprofile := zero_le_one.trans hCprofile
  have hpower : 1 ≤ Z ^ τ := Real.one_le_rpow hZ hτ
  have hleftNonneg (b : Λ) : 0 ≤ (left b).amplitude a B ha orders (Real.sqrt B * P) :=
    (left b).amplitude_nonneg a B ha hB orders hscaledP
  have hrightNonneg (b : Λ) : 0 ≤ (right b).amplitude a B ha orders (Real.sqrt B * P) :=
    (right b).amplitude_nonneg a B ha hB orders hscaledP
  let atoms := familyFourierControl family labels left right leftTime rightTime
    hleftData hrightData hleftTime hrightTime
    (fun b => (left b).amplitude a B ha orders (Real.sqrt B * P))
    (fun b => (right b).amplitude a B ha orders (Real.sqrt B * P))
    (fun b _ => hleftNonneg b) (fun b _ => hrightNonneg b)
    (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd)
    hleftRadius hrightRadius
  have hclipComparison : Cclip * P ≤ Cprofile * P * Z ^ τ :=
    (mul_le_mul_of_nonneg_right hclip_le hP0).trans
      (le_mul_of_one_le_right (mul_nonneg hprofile0 hP0) hpower)
  have hkernelComparison : Ckernel * P ≤ Cprofile * P * Z ^ τ :=
    (mul_le_mul_of_nonneg_right hkernel_le hP0).trans
      (le_mul_of_one_le_right (mul_nonneg hprofile0 hP0) hpower)
  refine ⟨atoms,
    { outer_nonneg := houter
      left_radius_nonneg := fun b _ => hleftNonneg b
      right_radius_nonneg := fun b _ => hrightNonneg b
      left_slots := ?_
      right_slots := ?_
      left_radius := hleftRadius
      right_radius := hrightRadius
      left_radius_power := ?_
      right_radius_power := ?_
      first_kernel_power := ?_
      second_kernel_power := ?_ }⟩
  · intro b hb
    rw [(left b).source_count (family.leftCalibration b) (hleftData b)]
    exact hleftCount b hb
  · intro b hb
    rw [(right b).source_count (family.rightCalibration b) (hrightData b)]
    exact hrightCount b hb
  · intro b hb
    rw [pow_one]
    exact ((left b).signed_amplitude_bound a B ha hB orders δ R cap directionBound P
      hD hP0 (hleftCount b hb) (hleftExp b hb)
      (hleftDirection b hb) (hleftScale b hb)).trans hclipComparison
  · intro b hb
    rw [pow_one]
    exact ((right b).signed_amplitude_bound a B ha hB orders δ R cap directionBound P
      hD hP0 (hrightCount b hb) (hrightExp b hb)
      (hrightDirection b hb) (hrightScale b hb)).trans hclipComparison
  · intro b hb
    rw [pow_one, hF₁ b hb]
    exact ((hkernel (φ₁ b)).1.trans
      (mul_le_mul_of_nonneg_left (hφ₁ b hb) (zero_le_one.trans hCkernel))).trans hkernelComparison
  · intro b hb
    rw [pow_one, hF₂ b hb]
    exact ((hkernel (φ₂ b)).2.trans
      (mul_le_mul_of_nonneg_left (hφ₂ b hb) (zero_le_one.trans hCkernel))).trans hkernelComparison

end SameFamily
end HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.OriginalLogProfiles.signed_amplitude_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.exists_signed_family_profile_controls
