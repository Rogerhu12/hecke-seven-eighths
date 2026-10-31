import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityChildIntegrability

/-!
# The actual capacity kernel has the original weighted Fourier mass

The source dictionary uses the Hilbert product of the two continuous
parameters.  Its measure is the canonical image of their original
product Fourier measure.  The exact normalization density is retained,
and its mass is controlled by fixed original Schwartz seminorms chosen
before any source, allocation, radius or child.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ} {ω ψ : HeckeCharacter F}
variable {U E HL HR : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {k l : ℕ}

section ActualKernel

variable {sL : ActualAllocatedSource A (WithLp 2 (U × E)) HL k}
variable {sR : ActualAllocatedSource A (WithLp 2 (U × E)) HR l}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {GL : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}
variable (B₁ B₂ : ℝ) (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
variable (hleftRadius : ∀ z, GL.radius (WithLp.toLp 2 z) = polynomialProfileRadius B₁ J₁₁ J₁₂ z)
variable (hrightRadius : ∀ z, GR.radius (WithLp.toLp 2 z) = polynomialProfileRadius B₂ J₂₁ J₂₂ z)

include hleftRadius hrightRadius

theorem normalizedCapacityPairEnvelope_hilbert_eq (ξ : WithLp 2 (U × E)) :
    normalizedCapacityPairEnvelope GL GR ξ =
      pairedProfileEnvelope B₁ B₂ sL.allocation.keep.card sR.allocation.keep.card
        J₁₁ J₁₂ J₂₁ J₂₂ (WithLp.ofLp ξ) := by
  have hl : GL.radius ξ = polynomialProfileRadius B₁ J₁₁ J₁₂ (WithLp.ofLp ξ) := by
    simpa only [WithLp.toLp_ofLp] using hleftRadius (WithLp.ofLp ξ)
  have hr : GR.radius ξ = polynomialProfileRadius B₂ J₂₁ J₂₂ (WithLp.ofLp ξ) := by
    simpa only [WithLp.toLp_ofLp] using hrightRadius (WithLp.ofLp ξ)
  simp only [normalizedCapacityPairEnvelope, pairedProfileEnvelope, hl, hr]

theorem normalizedCapacityPairEnvelope_hilbert_measurable :
    Measurable (normalizedCapacityPairEnvelope GL GR) := by
  have heq : normalizedCapacityPairEnvelope GL GR = fun ξ =>
      pairedProfileEnvelope B₁ B₂ sL.allocation.keep.card sR.allocation.keep.card
        J₁₁ J₁₂ J₂₁ J₂₂ (WithLp.ofLp ξ) :=
    funext (normalizedCapacityPairEnvelope_hilbert_eq B₁ B₂ J₁₁ J₁₂ J₂₁ J₂₂
      hleftRadius hrightRadius)
  rw [heq]
  exact ((pairedProfileEnvelope_continuous B₁ B₂ sL.allocation.keep.card
    sR.allocation.keep.card J₁₁ J₁₂ J₂₁ J₂₂).comp
      (WithLp.prod_continuous_ofLp 2 U E)).measurable

/-- The actual kernel mass contains its original scalar exactly once
and the exact profile envelope under the two original Fourier measures. -/
theorem normalizedCapacityPairKernel_nested_mass_eq
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (left : GL.Child) (right : GR.Child) (originalLeft originalRight : ℂ)
    (Z parentWidth : ℝ) (hZ : 0 < Z) :
    (normalizedCapacityPairKernel (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂))
      left right originalLeft originalRight Z parentWidth).real Set.univ =
      normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth *
        (weightedNestedFourierMeasure F₁ F₂
          (pairedProfileEnvelope B₁ B₂ sL.allocation.keep.card sR.allocation.keep.card
            J₁₁ J₁₂ J₂₁ J₂₂)).real Set.univ := by
  rw [normalizedCapacityPairKernel_mass _ _ _ _ _ _ _ hZ
    (normalizedCapacityPairEnvelope_hilbert_measurable B₁ B₂ J₁₁ J₁₂ J₂₁ J₂₂
      hleftRadius hrightRadius).aestronglyMeasurable]
  rw [(WithLp.homeomorphProd 2 U E).symm.measurableEmbedding.integral_map]
  rw [weightedNestedFourierMeasure_mass_eq F₁ F₂ _
    (pairedProfileEnvelope_continuous B₁ B₂ sL.allocation.keep.card
      sR.allocation.keep.card J₁₁ J₁₂ J₂₁ J₂₂).measurable
    (pairedProfileEnvelope_nonneg B₁ B₂ hB₁ hB₂ sL.allocation.keep.card
      sR.allocation.keep.card J₁₁ J₁₂ J₂₁ J₂₂)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [normalizedCapacityPairEnvelope, pairedProfileEnvelope, hleftRadius, hrightRadius]

theorem normalizedCapacityPairKernel_nested_finite
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (left : GL.Child) (right : GR.Child) (originalLeft originalRight : ℂ)
    (Z parentWidth : ℝ) :
    IsFiniteMeasure (normalizedCapacityPairKernel
      (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂))
      left right originalLeft originalRight Z parentWidth) := by
  apply normalizedCapacityPairKernel_finite
  apply (integrable_mapped_nested_fourier_iff F₁ F₂ _).mpr
  have hi := actual_profile_envelope_integrable F₁ F₂
    (pairedProfileEnvelope B₁ B₂ sL.allocation.keep.card sR.allocation.keep.card
      J₁₁ J₁₂ J₂₁ J₂₂)
    (pairedProfileEnvelope_continuous B₁ B₂ sL.allocation.keep.card
      sR.allocation.keep.card J₁₁ J₁₂ J₂₁ J₂₂).measurable
    (pairedProfileEnvelope_nonneg B₁ B₂ hB₁ hB₂ sL.allocation.keep.card
      sR.allocation.keep.card J₁₁ J₁₂ J₂₁ J₂₂)
    (pairedProfileEnvelopeConstant B₁ B₂ sL.allocation.keep.card sR.allocation.keep.card)
    (pairedProfileEnvelopeOrder sL.allocation.keep.card sR.allocation.keep.card J₁₁ J₂₁)
    (pairedProfileEnvelopeOrder sL.allocation.keep.card sR.allocation.keep.card J₁₂ J₂₂)
    (pairedProfileEnvelope_bound B₁ B₂ hB₁ hB₂ sL.allocation.keep.card
      sR.allocation.keep.card J₁₁ J₁₂ J₂₁ J₂₂)
  simpa only [normalizedCapacityPairEnvelope, pairedProfileEnvelope, hleftRadius, hrightRadius]
    using hi

end ActualKernel

/-- An original finite arithmetic label weight stays outside the same
profile density and is charged exactly once. -/
theorem normalizedCapacityPairKernel_smul_measure
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    {sL : ActualAllocatedSource A V HL k} {sR : ActualAllocatedSource A V HR l}
    {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
    {GL : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}
    (μ : Measure V) (c : ℝ≥0∞) (left : GL.Child) (right : GR.Child)
    (originalLeft originalRight : ℂ) (Z parentWidth : ℝ) :
    normalizedCapacityPairKernel (c • μ) left right originalLeft originalRight Z parentWidth =
      c • normalizedCapacityPairKernel μ left right originalLeft originalRight Z parentWidth := by
  simp only [normalizedCapacityPairKernel, withDensity_smul_measure, smul_smul, mul_comm]

/-- The fixed seminorms precede every actual source and capacity choice.
Only the upper bound uses the fixed cap; the density keeps the exact
two pre-removal live-slot exponents. -/
theorem normalized_capacity_nested_kernel_uniform_mass
    (cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) :
    ∃ s₁ s₂ : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
    ∀ {HL HR : Type*} {k l : ℕ},
    ∀ (sL : ActualAllocatedSource A (WithLp 2 (U × E)) HL k)
      (sR : ActualAllocatedSource A (WithLp 2 (U × E)) HR l)
      (DL : sL.Calibration (σ := σ) ω ψ) (DR : sR.Calibration (σ := σ) ω ψ)
      (GL : DL.NormalizedCapacityData) (GR : DR.NormalizedCapacityData),
      sL.allocation.keep.card ≤ cap → sR.allocation.keep.card ≤ cap →
      (∀ z, GL.radius (WithLp.toLp 2 z) = polynomialProfileRadius B₁ J₁₁ J₁₂ z) →
      (∀ z, GR.radius (WithLp.toLp 2 z) = polynomialProfileRadius B₂ J₂₁ J₂₂ z) →
    ∀ (left : GL.Child) (right : GR.Child) (originalLeft originalRight : ℂ)
      (Z parentWidth : ℝ), 0 < Z →
      IsFiniteMeasure (normalizedCapacityPairKernel
        (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂))
        left right originalLeft originalRight Z parentWidth) ∧
      (normalizedCapacityPairKernel (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂))
        left right originalLeft originalRight Z parentWidth).real Set.univ ≤
        normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth *
          pairedProfileEnvelopeConstant B₁ B₂ cap cap * C *
            s₁.sup (schwartzSeminormFamily ℝ U ℂ) F₁ *
              s₂.sup (schwartzSeminormFamily ℝ E ℂ) F₂ := by
  obtain ⟨s₁, s₂, C, hC, hmass⟩ := normalized_profile_kernel_uniform_mass_up_to
    (V := U) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂
  refine ⟨s₁, s₂, C, hC, ?_⟩
  intro F₁ F₂ B₁ B₂ hB₁ hB₂ HL HR k l sL sR DL DR GL GR hcapL hcapR hleftRadius hrightRadius
    left right originalLeft originalRight Z parentWidth hZ
  refine ⟨normalizedCapacityPairKernel_nested_finite B₁ B₂ J₁₁ J₁₂ J₂₁ J₂₂
    hleftRadius hrightRadius F₁ F₂ hB₁ hB₂ left right originalLeft originalRight Z parentWidth, ?_⟩
  rw [normalizedCapacityPairKernel_nested_mass_eq B₁ B₂ J₁₁ J₁₂ J₂₁ J₂₂
    hleftRadius hrightRadius F₁ F₂ hB₁ hB₂ left right originalLeft originalRight Z parentWidth hZ]
  exact (mul_le_mul_of_nonneg_left
    (hmass F₁ F₂ B₁ B₂ hB₁ hB₂ sL.allocation.keep.card sR.allocation.keep.card hcapL hcapR).2
    (normalizedCapacityPairWeight_nonneg left right originalLeft originalRight Z parentWidth hZ)).trans_eq
      (by ring)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.normalizedCapacityPairKernel_nested_mass_eq
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_capacity_nested_kernel_uniform_mass
