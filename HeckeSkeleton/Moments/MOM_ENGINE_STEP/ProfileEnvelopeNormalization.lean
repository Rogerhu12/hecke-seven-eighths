import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedSlotRemoval
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PolynomialProfileEnvelope

/-!
# Normalized actual children in the original positive Fourier kernel

The actual child data are divided by explicit positive profile radii.
Their exact pair amplitude is absorbed in the original product Fourier
measure.  Raw profile seminorm bounds produce unit-ball children, while
the original finite summands give integrability under the weighted
measure.  No moment estimate or bound for a final child is an input.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}
variable {V E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup E]

def normalizedFourierChild (D : V × E → MomentData K ω ψ)
    (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ) (z : V × E) : MomentData K ω ψ :=
  normalizedMomentProfiles (D z) (polynomialProfileRadius B J₁ J₂ z)
    (polynomialProfileRadius_pos B hB J₁ J₂ z)

theorem normalizedFourierChild_unit_ball (D : V × E → MomentData K ω ψ)
    (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ) (t : V × E → ℝ)
    (orders : Finset (ℕ × ℝ))
    (hideal : ∀ z, ∀ q ∈ orders,
      ∀ W ∈ [(D z).inverseTest, (D z).plainTest₁, (D z).plainTest₂], ∀ u,
        testSeminorm (W.profile u (t z)) q.1 q.2 ≤
          B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂))
    (hprime : ∀ z, ∀ q ∈ orders, ∀ i,
      testSeminorm (((D z).geometry.slots i).profile (t z)) q.1 q.2 ≤
        B * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    ∀ z, MomentProfileUnitBall (normalizedFourierChild D B hB J₁ J₂ z) (t z) orders := by
  intro z
  apply normalizedMomentProfiles_unit_ball
  · intro q hq W hW u
    exact (hideal z q hq W hW u).trans (by unfold polynomialProfileRadius; linarith)
  · intro q hq i
    exact (hprime z q hq i).trans (by unfold polynomialProfileRadius; linarith)

/-- Normalization alters no arithmetic data, and the parameters can
remain fixed before the two continuous variables. -/
theorem normalizedFourierChild_invariants (D : V × E → MomentData K ω ψ)
    (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ) (z : V × E) :
    (normalizedFourierChild D B hB J₁ J₂ z).rows = (D z).rows ∧
    (normalizedFourierChild D B hB J₁ J₂ z).allowedRow = (D z).allowedRow ∧
    (normalizedFourierChild D B hB J₁ J₂ z).commonMask = (D z).commonMask ∧
    (normalizedFourierChild D B hB J₁ J₂ z).rowCharacter = (D z).rowCharacter ∧
    (normalizedFourierChild D B hB J₁ J₂ z).theta = (D z).theta ∧
    (normalizedFourierChild D B hB J₁ J₂ z).slotCoefficient = (D z).slotCoefficient ∧
    (normalizedFourierChild D B hB J₁ J₂ z).geometry.slotCount = (D z).geometry.slotCount ∧
    (normalizedFourierChild D B hB J₁ J₂ z).geometry.totalLength =
      (D z).geometry.totalLength :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Each extracted factor is the square root of the precise energy
homogeneity degree.  It appears in the common kernel exactly once. -/
theorem normalizedFourierChild_cauchy_identity
    (D₁ D₂ : V × E → MomentData K ω ψ) (k₁ k₂ : ℕ)
    (hc₁ : ∀ z, (D₁ z).geometry.slotCount = k₁)
    (hc₂ : ∀ z, (D₂ z).geometry.slotCount = k₂)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (a₁ a₂ : RealParameters)
    (Z : ℝ) (t₁ t₂ : V × E → ℝ) (z : V × E) :
    Real.sqrt (normalizedPairedEnergy (D₁ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy (D₂ z) a₂ Z (t₂ z)) =
    pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂ z *
      (Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₁ B₁ hB₁ J₁₁ J₁₂ z) a₁ Z (t₁ z)) *
       Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₂ B₂ hB₂ J₂₁ J₂₂ z) a₂ Z (t₂ z))) := by
  rw [sqrt_normalizedPairedEnergy_profile_factor (D₁ z) a₁
    (polynomialProfileRadius B₁ J₁₁ J₁₂ z)
    (polynomialProfileRadius_pos B₁ hB₁ J₁₁ J₁₂ z) Z (t₁ z),
    sqrt_normalizedPairedEnergy_profile_factor (D₂ z) a₂
      (polynomialProfileRadius B₂ J₂₁ J₂₂ z)
      (polynomialProfileRadius_pos B₂ hB₂ J₂₁ J₂₂ z) Z (t₂ z), hc₁ z, hc₂ z]
  dsimp only [normalizedFourierChild, pairedProfileEnvelope]
  ring

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem normalizedFourierChild_cauchy_integral
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (D₁ D₂ : V × E → MomentData K ω ψ) (k₁ k₂ : ℕ)
    (hc₁ : ∀ z, (D₁ z).geometry.slotCount = k₁)
    (hc₂ : ∀ z, (D₂ z).geometry.slotCount = k₂)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (a₁ a₂ : RealParameters)
    (Z : ℝ) (t₁ t₂ : V × E → ℝ) :
    (∫ z, Real.sqrt (normalizedPairedEnergy (D₁ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy (D₂ z) a₂ Z (t₂ z)) ∂nestedFourierMeasure F₁ F₂) =
    ∫ z, Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₁ B₁ hB₁ J₁₁ J₁₂ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₂ B₂ hB₂ J₂₁ J₂₂ z) a₂ Z (t₂ z))
      ∂weightedNestedFourierMeasure F₁ F₂
        (pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂) := by
  rw [weightedNestedFourierMeasure_integral F₁ F₂ _
    (pairedProfileEnvelope_continuous B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂).measurable
    (pairedProfileEnvelope_nonneg B₁ B₂ hB₁ hB₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z =>
    normalizedFourierChild_cauchy_identity D₁ D₂ k₁ k₂ hc₁ hc₂ B₁ B₂ hB₁ hB₂
      J₁₁ J₁₂ J₂₁ J₂₂ a₁ a₂ Z t₁ t₂ z

/-- After normalization precedes deletion, the envelope degree is the
original live-slot count, while the integrand is the final retained
child.  This transports that exact envelope without reinterpreting its
degree as the smaller retained slot count. -/
theorem normalized_pre_removal_cauchy_integral
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (D₁ D₂ : V × E → MomentData K ω ψ) (sourceSlots₁ sourceSlots₂ : ℕ)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (a₁ a₂ : RealParameters)
    (Z : ℝ) (t₁ t₂ : V × E → ℝ) :
    (∫ z, pairedProfileEnvelope B₁ B₂ sourceSlots₁ sourceSlots₂ J₁₁ J₁₂ J₂₁ J₂₂ z *
      (Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₁ B₁ hB₁ J₁₁ J₁₂ z) a₁ Z (t₁ z)) *
       Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₂ B₂ hB₂ J₂₁ J₂₂ z) a₂ Z (t₂ z)))
      ∂nestedFourierMeasure F₁ F₂) =
    ∫ z, Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₁ B₁ hB₁ J₁₁ J₁₂ z) a₁ Z (t₁ z)) *
      Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₂ B₂ hB₂ J₂₁ J₂₂ z) a₂ Z (t₂ z))
      ∂weightedNestedFourierMeasure F₁ F₂
        (pairedProfileEnvelope B₁ B₂ sourceSlots₁ sourceSlots₂ J₁₁ J₁₂ J₂₁ J₂₂) := by
  symm
  exact weightedNestedFourierMeasure_integral F₁ F₂ _
    (pairedProfileEnvelope_continuous B₁ B₂ sourceSlots₁ sourceSlots₂
      J₁₁ J₁₂ J₂₁ J₂₂).measurable
    (pairedProfileEnvelope_nonneg B₁ B₂ hB₁ hB₂ sourceSlots₁ sourceSlots₂
      J₁₁ J₁₂ J₂₁ J₂₂) _

/-- The unnormalized child is controlled only through its individual
original finite summands.  Dividing all profiles by a radius at least one
preserves integrability for the already weighted common measure. -/
theorem normalizedFourierChild_integrable
    {D : V × E → MomentData K ω ψ} {k : ℕ}
    {hc : ∀ z, (D z).geometry.slotCount = k}
    {a : RealParameters} {Z : ℝ} {t : V × E → ℝ}
    (cal : ActualFiniteFamilyControl D k hc a Z t)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B : ℝ) (hB : 0 ≤ B) (J₁ J₂ : ℕ)
    (envelope : V × E → ℝ) (hmeas : Measurable envelope)
    (hnonneg : ∀ z, 0 ≤ envelope z) (C : ℝ) (hC : 0 ≤ C) (L₁ L₂ : ℕ)
    (hbound : ∀ z, envelope z ≤ C * ((1 + ‖z.1‖) ^ L₁ * (1 + ‖z.2‖) ^ L₂)) :
    Integrable (fun z => normalizedPairedEnergy
      (normalizedFourierChild D B hB J₁ J₂ z) a Z (t z))
      (weightedNestedFourierMeasure F₁ F₂ envelope) := by
  exact normalized_profile_family_integrable _ D k hc
    (polynomialProfileRadius B J₁ J₂) (polynomialProfileRadius_pos B hB J₁ J₂)
    (polynomialProfileRadius_one_le B hB J₁ J₂)
    (polynomialProfileRadius_continuous B J₁ J₂).measurable a Z t
    (actual_weighted_nested_normalized_integrable cal F₁ F₂ envelope hmeas hnonneg
      C hC L₁ L₂ hbound)

/-- Both normalized children and their Cauchy product are integrable
under precisely the same absorbed-envelope measure. -/
theorem normalizedFourierChild_pair_integrable_for_counts
    {D₁ D₂ : V × E → MomentData K ω ψ} {k₁ k₂ : ℕ}
    {hc₁ : ∀ z, (D₁ z).geometry.slotCount = k₁}
    {hc₂ : ∀ z, (D₂ z).geometry.slotCount = k₂}
    {a₁ a₂ : RealParameters} {Z : ℝ} (hZ : 0 < Z) {t₁ t₂ : V × E → ℝ}
    (cal₁ : ActualFiniteFamilyControl D₁ k₁ hc₁ a₁ Z t₁)
    (cal₂ : ActualFiniteFamilyControl D₂ k₂ hc₂ a₂ Z t₂)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (J₁₁ J₁₂ J₂₁ J₂₂ sourceSlots₁ sourceSlots₂ : ℕ) :
    let μ := weightedNestedFourierMeasure F₁ F₂
      (pairedProfileEnvelope B₁ B₂ sourceSlots₁ sourceSlots₂ J₁₁ J₁₂ J₂₁ J₂₂)
    let f₁ := fun z => normalizedPairedEnergy
      (normalizedFourierChild D₁ B₁ hB₁ J₁₁ J₁₂ z) a₁ Z (t₁ z)
    let f₂ := fun z => normalizedPairedEnergy
      (normalizedFourierChild D₂ B₂ hB₂ J₂₁ J₂₂ z) a₂ Z (t₂ z)
    Integrable f₁ μ ∧ Integrable f₂ μ ∧
      Integrable (fun z => Real.sqrt (f₁ z) * Real.sqrt (f₂ z)) μ := by
  dsimp only
  have hm := (pairedProfileEnvelope_continuous (V := V) (E := E) B₁ B₂ sourceSlots₁ sourceSlots₂
    J₁₁ J₁₂ J₂₁ J₂₂).measurable
  have hn := pairedProfileEnvelope_nonneg (V := V) (E := E) B₁ B₂ hB₁ hB₂ sourceSlots₁ sourceSlots₂
    J₁₁ J₁₂ J₂₁ J₂₂
  have hC := pairedProfileEnvelope_constant_nonneg B₁ B₂ hB₁ hB₂ sourceSlots₁ sourceSlots₂
  have hb := pairedProfileEnvelope_bound (V := V) (E := E) B₁ B₂ hB₁ hB₂ sourceSlots₁ sourceSlots₂
    J₁₁ J₁₂ J₂₁ J₂₂
  have hi₁ := normalizedFourierChild_integrable cal₁ F₁ F₂ B₁ hB₁ J₁₁ J₁₂
    _ hm hn _ hC _ _ hb
  have hi₂ := normalizedFourierChild_integrable cal₂ F₁ F₂ B₂ hB₂ J₂₁ J₂₂
    _ hm hn _ hC _ _ hb
  refine ⟨hi₁, hi₂, ?_⟩
  have hmeas := (Real.continuous_sqrt.comp_aestronglyMeasurable hi₁.aestronglyMeasurable).mul
    (Real.continuous_sqrt.comp_aestronglyMeasurable hi₂.aestronglyMeasurable)
  apply ((hi₁.add hi₂).div_const 2).mono' hmeas
  exact Filter.Eventually.of_forall fun z => by
    have hl := normalizedPairedEnergy_nonneg
      (normalizedFourierChild D₁ B₁ hB₁ J₁₁ J₁₂ z) a₁ Z (t₁ z) hZ
    have hr := normalizedPairedEnergy_nonneg
      (normalizedFourierChild D₂ B₂ hB₂ J₂₁ J₂₂ z) a₂ Z (t₂ z) hZ
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    nlinarith [Real.sq_sqrt hl, Real.sq_sqrt hr, sq_nonneg
      (Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₁ B₁ hB₁ J₁₁ J₁₂ z) a₁ Z (t₁ z)) -
       Real.sqrt (normalizedPairedEnergy
        (normalizedFourierChild D₂ B₂ hB₂ J₂₁ J₂₂ z) a₂ Z (t₂ z)))]

theorem normalizedFourierChild_pair_integrable
    {D₁ D₂ : V × E → MomentData K ω ψ} {k₁ k₂ : ℕ}
    {hc₁ : ∀ z, (D₁ z).geometry.slotCount = k₁}
    {hc₂ : ∀ z, (D₂ z).geometry.slotCount = k₂}
    {a₁ a₂ : RealParameters} {Z : ℝ} (hZ : 0 < Z) {t₁ t₂ : V × E → ℝ}
    (cal₁ : ActualFiniteFamilyControl D₁ k₁ hc₁ a₁ Z t₁)
    (cal₂ : ActualFiniteFamilyControl D₂ k₂ hc₂ a₂ Z t₂)
    (F₁ : 𝓢(V, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) :
    let μ := weightedNestedFourierMeasure F₁ F₂
      (pairedProfileEnvelope B₁ B₂ k₁ k₂ J₁₁ J₁₂ J₂₁ J₂₂)
    let f₁ := fun z => normalizedPairedEnergy
      (normalizedFourierChild D₁ B₁ hB₁ J₁₁ J₁₂ z) a₁ Z (t₁ z)
    let f₂ := fun z => normalizedPairedEnergy
      (normalizedFourierChild D₂ B₂ hB₂ J₂₁ J₂₂ z) a₂ Z (t₂ z)
    Integrable f₁ μ ∧ Integrable f₂ μ ∧
      Integrable (fun z => Real.sqrt (f₁ z) * Real.sqrt (f₂ z)) μ :=
  normalizedFourierChild_pair_integrable_for_counts hZ cal₁ cal₂ F₁ F₂
    B₁ B₂ hB₁ hB₂ J₁₁ J₁₂ J₂₁ J₂₂ k₁ k₂

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.normalizedFourierChild_unit_ball
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedFourierChild_cauchy_integral
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_pre_removal_cauchy_integral
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedFourierChild_pair_integrable_for_counts
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedFourierChild_pair_integrable
