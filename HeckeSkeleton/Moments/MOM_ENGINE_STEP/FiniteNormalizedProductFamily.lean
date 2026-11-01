import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFiniteKernelMass

/-!
# A finite family of actual normalized leaves under its original kernels

The outer index is the actual live-source leaf, and the inner index can
be its four ordinary rectangles. The construction preserves each
source, calibration, fixed capacity input and arithmetic normalizer.

All source and child convergence requirements are discharged here.
Source convergence comes from its literal finite coefficient arrays;
child convergence comes from the original finite single-atom windows.
The positive kernels are the same kernels used by the uniform mass
theorem, with each original outer scalar included once.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}

namespace ActualNormalizedPairFamily

section Combine

variable {V J Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Z : ℝ}

/-- This keeps the original finite leaf index and its rectangle index.
It introduces no extra source or choices depending on frequency. -/
def combine (families : J → ActualNormalizedPairFamily A σ V Λ ω ψ Z) :
    ActualNormalizedPairFamily A σ V (J × Λ) ω ψ Z where
  LeftRow b := (families b.1).LeftRow b.2
  RightRow b := (families b.1).RightRow b.2
  leftSlots b := (families b.1).leftSlots b.2
  rightSlots b := (families b.1).rightSlots b.2
  leftSource b := (families b.1).leftSource b.2
  rightSource b := (families b.1).rightSource b.2
  leftCalibration b := (families b.1).leftCalibration b.2
  rightCalibration b := (families b.1).rightCalibration b.2
  leftCapacity b := (families b.1).leftCapacity b.2
  rightCapacity b := (families b.1).rightCapacity b.2
  left_base b := (families b.1).left_base b.2
  right_base b := (families b.1).right_base b.2
  leftNormalizer b := (families b.1).leftNormalizer b.2
  rightNormalizer b := (families b.1).rightNormalizer b.2

theorem combine_sourcePair
    (families : J → ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (parentWidth : ℝ) (b : J × Λ) (ξ : V) :
    (combine families).sourcePair parentWidth b ξ =
      (families b.1).sourcePair parentWidth b.2 ξ := rfl

end Combine

section Product

variable {U E Λ : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)

/-- The actual finite source energies are bounded continuous functions,
so their Cauchy product is integrable under the original two measures. -/
theorem sourcePair_nested_integrable (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (parentWidth : ℝ) (b : Λ) :
    Integrable (fun z : U × E => family.sourcePair parentWidth b (WithLp.toLp 2 z))
      (nestedFourierMeasure F₁ F₂) := by
  let μ := nestedFourierMeasure F₁ F₂
  letI : IsFiniteMeasure μ := nestedFourierMeasure_finite F₁ F₂
  let L : U × E → ℝ := fun z => ‖family.leftNormalizer b‖ ^ 2 *
    (family.leftSource b).energy (σ := σ) (WithLp.toLp 2 z)
  let R : U × E → ℝ := fun z => ‖family.rightNormalizer b‖ ^ 2 *
    (family.rightSource b).energy (σ := σ) (WithLp.toLp 2 z)
  have hl : Integrable L μ :=
    ((family.leftSource b).nestedEnergy_integrable (σ := σ) μ).const_mul _
  have hr : Integrable R μ :=
    ((family.rightSource b).nestedEnergy_integrable (σ := σ) μ).const_mul _
  have hl0 (z : U × E) : 0 ≤ L z :=
    mul_nonneg (sq_nonneg _) ((family.leftSource b).energy_nonneg (σ := σ) _)
  have hr0 (z : U × E) : 0 ≤ R z :=
    mul_nonneg (sq_nonneg _) ((family.rightSource b).energy_nonneg (σ := σ) _)
  have hi : Integrable (fun z => Real.sqrt (L z) * Real.sqrt (R z)) μ := by
    apply ((hl.add hr).div_const 2).mono'
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hl.aestronglyMeasurable).mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable hr.aestronglyMeasurable))
    exact Filter.Eventually.of_forall fun z => by
      change ‖Real.sqrt (L z) * Real.sqrt (R z)‖ ≤ (L z + R z) / 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      nlinarith [Real.sq_sqrt (hl0 z), Real.sq_sqrt (hr0 z),
        sq_nonneg (Real.sqrt (L z) - Real.sqrt (R z))]
  exact hi.div_const (Z ^ parentWidth)

variable (labels : Finset Λ)

/-- Both measured child energies are integrable under the literal
family kernel. The original finite scalar may vanish. -/
theorem kernel_children_integrable_of_atoms
    (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ)
    (parentWidth : ℝ) (hZ : 0 < Z) (b : family.active labels)
    (calL : ActualFiniteFamilyControl
      (fun z => (family.leftChild labels b).rawData (WithLp.toLp 2 z))
      (family.leftChild labels b).retainedCount
      (fun z => (family.leftChild labels b).raw_count (WithLp.toLp 2 z))
      (family.leftParameters labels b) Z
      (fun z => (family.leftCalibration b.val).height (WithLp.toLp 2 z)))
    (calR : ActualFiniteFamilyControl
      (fun z => (family.rightChild labels b).rawData (WithLp.toLp 2 z))
      (family.rightChild labels b).retainedCount
      (fun z => (family.rightChild labels b).raw_count (WithLp.toLp 2 z))
      (family.rightParameters labels b) Z
      (fun z => (family.rightCalibration b.val).height (WithLp.toLp 2 z)))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (hleftRadius : ∀ z, (family.leftCapacity b.val).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius B₁ J₁₁ J₁₂ z)
    (hrightRadius : ∀ z, (family.rightCapacity b.val).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius B₂ J₂₁ J₂₂ z) :
    Integrable (fun ξ => normalizedPairedEnergy
      (family.leftData labels b ξ) (family.leftParameters labels b) Z 0)
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b) ∧
    Integrable (fun ξ => normalizedPairedEnergy
      (family.rightData labels b ξ) (family.rightParameters labels b) Z 0)
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b) := by
  let base := Measure.map (WithLp.toLp 2) (nestedFourierMeasure (F₁ b.val) (F₂ b.val))
  have hm : Measurable (family.envelope labels b) :=
    normalizedCapacityPairEnvelope_hilbert_measurable B₁ B₂ J₁₁ J₁₂ J₂₁ J₂₂
      hleftRadius hrightRadius
  have hn : ∀ ξ, 0 ≤ family.envelope labels b ξ :=
    normalizedCapacityPairEnvelope_nonneg
  have hi := normalized_capacity_children_nested_actual_integrable
    (family.leftChild labels b) (family.rightChild labels b) Z hZ calL calR
    (F₁ b.val) (F₂ b.val) B₁ B₂ hB₁ hB₂ J₁₁ J₁₂ J₂₁ J₂₂
    hleftRadius hrightRadius
  have hmprod : Measurable
      (fun z : U × E => family.envelope labels b (WithLp.toLp 2 z)) :=
    hm.comp (WithLp.homeomorphProd 2 U E).symm.continuous.measurable
  have transfer (f : WithLp 2 (U × E) → ℝ)
      (hf : Integrable (fun z => f (WithLp.toLp 2 z))
        ((nestedFourierMeasure (F₁ b.val) (F₂ b.val)).withDensity
          (fun z => ENNReal.ofReal (family.envelope labels b (WithLp.toLp 2 z))))) :
      Integrable f (base.withDensity (fun ξ => ENNReal.ofReal (family.envelope labels b ξ))) := by
    apply (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    have hp := (integrable_withDensity_iff_integrable_smul' hmprod.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hf
    have hp' : Integrable
        (fun z => family.envelope labels b (WithLp.toLp 2 z) * f (WithLp.toLp 2 z))
        (nestedFourierMeasure (F₁ b.val) (F₂ b.val)) := by
      simpa only [ENNReal.toReal_ofReal (hn _), smul_eq_mul] using hp
    have hv := (integrable_mapped_nested_fourier_iff (F₁ b.val) (F₂ b.val)
      (fun ξ => family.envelope labels b ξ * f ξ)).mpr hp'
    simpa only [ENNReal.toReal_ofReal (hn _), smul_eq_mul] using hv
  have hl : Integrable (fun ξ => normalizedPairedEnergy
      (family.leftData labels b ξ) (family.leftParameters labels b) Z 0)
      (base.withDensity (fun ξ => ENNReal.ofReal (family.envelope labels b ξ))) := by
    apply transfer
    simpa only [leftData, leftParameters, envelope,
      ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozenData,
      normalizedPairedEnergy_frozenMomentProfiles] using hi.1
  have hr : Integrable (fun ξ => normalizedPairedEnergy
      (family.rightData labels b ξ) (family.rightParameters labels b) Z 0)
      (base.withDensity (fun ξ => ENNReal.ofReal (family.envelope labels b ξ))) := by
    apply transfer
    simpa only [rightData, rightParameters, envelope,
      ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozenData,
      normalizedPairedEnergy_frozenMomentProfiles] using hi.2.1
  rw [family.kernel_actualNestedLabelMeasure labels F₁ F₂ outer parentWidth b]
  exact ⟨(hl.smul_measure ENNReal.ofReal_ne_top).smul_measure ENNReal.ofReal_ne_top,
    (hr.smul_measure ENNReal.ofReal_ne_top).smul_measure ENNReal.ofReal_ne_top⟩

/-- The finite actual source integral reaches the same finite kernels
used in the mass theorem. Every integrability premise is proved from
the raw atom controls and individual polynomial profile radii. -/
theorem finite_integral_of_atoms
    (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ)
    (parentWidth : ℝ) (hZ : 0 < Z) (houter : ∀ b ∈ labels, 0 ≤ outer b)
    (calL : ∀ b : family.active labels, ActualFiniteFamilyControl
      (fun z => (family.leftChild labels b).rawData (WithLp.toLp 2 z))
      (family.leftChild labels b).retainedCount
      (fun z => (family.leftChild labels b).raw_count (WithLp.toLp 2 z))
      (family.leftParameters labels b) Z
      (fun z => (family.leftCalibration b.val).height (WithLp.toLp 2 z)))
    (calR : ∀ b : family.active labels, ActualFiniteFamilyControl
      (fun z => (family.rightChild labels b).rawData (WithLp.toLp 2 z))
      (family.rightChild labels b).retainedCount
      (fun z => (family.rightChild labels b).raw_count (WithLp.toLp 2 z))
      (family.rightParameters labels b) Z
      (fun z => (family.rightCalibration b.val).height (WithLp.toLp 2 z)))
    (B₁ B₂ : Λ → ℝ) (hB₁ : ∀ b ∈ labels, 0 ≤ B₁ b) (hB₂ : ∀ b ∈ labels, 0 ≤ B₂ b)
    (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (hleftRadius : ∀ b ∈ labels, ∀ z, (family.leftCapacity b).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (B₁ b) J₁₁ J₁₂ z)
    (hrightRadius : ∀ b ∈ labels, ∀ z, (family.rightCapacity b).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (B₂ b) J₂₁ J₂₂ z) :
    (∑ b ∈ labels, outer b *
      ∫ z : U × E, family.sourcePair parentWidth b (WithLp.toLp 2 z)
        ∂nestedFourierMeasure (F₁ b) (F₂ b)) ≤
      ∑ b : family.active labels,
        ∫ ξ, family.childPair labels b ξ
          ∂family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b := by
  have hb (b : family.active labels) : b.val ∈ labels := (Finset.mem_filter.mp b.property).1
  have hprofile (b : family.active labels) : Measurable (family.envelope labels b) :=
    normalizedCapacityPairEnvelope_hilbert_measurable (B₁ b.val) (B₂ b.val)
      J₁₁ J₁₂ J₂₁ J₂₂ (hleftRadius b.val (hb b)) (hrightRadius b.val (hb b))
  have hsource (b : Λ) (_ : b ∈ labels) :
      Integrable (family.sourcePair parentWidth b) (actualNestedLabelMeasure F₁ F₂ outer b) :=
    ((integrable_mapped_nested_fourier_iff (F₁ b) (F₂ b) _).mpr
      (family.sourcePair_nested_integrable (F₁ b) (F₂ b) parentWidth b)).smul_measure
        ENNReal.ofReal_ne_top
  have hchild (b : family.active labels) :
      Integrable (fun ξ => family.envelope labels b ξ * family.childPair labels b ξ)
        (actualNestedLabelMeasure F₁ F₂ outer b.val) := by
    have hraw := normalized_capacity_pair_nested_actual_integrable
      (family.leftChild labels b) (family.rightChild labels b) Z hZ (calL b) (calR b)
      (F₁ b.val) (F₂ b.val) (B₁ b.val) (B₂ b.val) (hB₁ b.val (hb b)) (hB₂ b.val (hb b))
      J₁₁ J₁₂ J₂₁ J₂₂ (hleftRadius b.val (hb b)) (hrightRadius b.val (hb b))
    exact ((integrable_mapped_nested_fourier_iff (F₁ b.val) (F₂ b.val) _).mpr hraw).smul_measure
      ENNReal.ofReal_ne_top
  have h := family.finite_integral labels (actualNestedLabelMeasure F₁ F₂ outer)
    parentWidth hZ hprofile hsource hchild
  have he : (∑ b ∈ labels, ∫ ξ, family.sourcePair parentWidth b ξ
      ∂actualNestedLabelMeasure F₁ F₂ outer b) =
      ∑ b ∈ labels, outer b *
        ∫ z : U × E, family.sourcePair parentWidth b (WithLp.toLp 2 z)
          ∂nestedFourierMeasure (F₁ b) (F₂ b) := by
    apply Finset.sum_congr rfl
    intro b hbl
    rw [actualNestedLabelMeasure, integral_smul_measure,
      ENNReal.toReal_ofReal (houter b hbl), smul_eq_mul]
    congr 1
    exact (WithLp.homeomorphProd 2 U E).symm.measurableEmbedding.integral_map _
  rw [he] at h
  exact h

end Product

end ActualNormalizedPairFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.combine
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sourcePair_nested_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.kernel_children_integrable_of_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.finite_integral_of_atoms

