import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedProductFamily

/-!
# Original atom controls used by the complete finite source producer

This record packages only the finite summand controls and the exact
single-profile radii. Its methods prove convergence and the finite
source-to-child integral inequality under the same positive kernels.
No aggregate energy inequality or kernel mass bound is a field.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {U E Λ : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {Z : ℝ}

namespace ActualNormalizedPairFamily

variable (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
variable (labels : Finset Λ) (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)

/-- The scalar profile amplitudes may depend on the original finite
label. The polynomial orders are fixed before those moving labels. -/
structure FourierAtomControl where
  left : ∀ b : family.active labels, ActualFiniteFamilyControl
    (fun z => (family.leftChild labels b).rawData (WithLp.toLp 2 z))
    (family.leftChild labels b).retainedCount
    (fun z => (family.leftChild labels b).raw_count (WithLp.toLp 2 z))
    (family.leftParameters labels b) Z
    (fun z => (family.leftCalibration b.val).height (WithLp.toLp 2 z))
  right : ∀ b : family.active labels, ActualFiniteFamilyControl
    (fun z => (family.rightChild labels b).rawData (WithLp.toLp 2 z))
    (family.rightChild labels b).retainedCount
    (fun z => (family.rightChild labels b).raw_count (WithLp.toLp 2 z))
    (family.rightParameters labels b) Z
    (fun z => (family.rightCalibration b.val).height (WithLp.toLp 2 z))
  leftAmplitude : Λ → ℝ
  rightAmplitude : Λ → ℝ
  left_nonneg : ∀ b ∈ labels, 0 ≤ leftAmplitude b
  right_nonneg : ∀ b ∈ labels, 0 ≤ rightAmplitude b
  left_radius : ∀ b ∈ labels, ∀ z,
    (family.leftCapacity b).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (leftAmplitude b) J₁₁ J₁₂ z
  right_radius : ∀ b ∈ labels, ∀ z,
    (family.rightCapacity b).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (rightAmplitude b) J₂₁ J₂₂ z

namespace FourierAtomControl

variable {family labels J₁₁ J₁₂ J₂₁ J₂₂}
variable (atoms : family.FourierAtomControl labels J₁₁ J₁₂ J₂₁ J₂₂)

include atoms in
theorem source_integral
    (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ)
    (parentWidth : ℝ) (hZ : 0 < Z) (houter : ∀ b ∈ labels, 0 ≤ outer b) :
    (∑ b ∈ labels, outer b *
      ∫ z : U × E, family.sourcePair parentWidth b (WithLp.toLp 2 z)
        ∂nestedFourierMeasure (F₁ b) (F₂ b)) ≤
      ∑ b : family.active labels,
        ∫ ξ, family.childPair labels b ξ
          ∂family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b :=
  family.finite_integral_of_atoms labels F₁ F₂ outer parentWidth hZ houter
    atoms.left atoms.right atoms.leftAmplitude atoms.rightAmplitude
    atoms.left_nonneg atoms.right_nonneg J₁₁ J₁₂ J₂₁ J₂₂
    atoms.left_radius atoms.right_radius

include atoms in
theorem children_integrable
    (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ)
    (parentWidth : ℝ) (hZ : 0 < Z) (b : family.active labels) :
    Integrable (fun ξ => normalizedPairedEnergy
      (family.leftData labels b ξ) (family.leftParameters labels b) Z 0)
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b) ∧
    Integrable (fun ξ => normalizedPairedEnergy
      (family.rightData labels b ξ) (family.rightParameters labels b) Z 0)
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b) :=
  family.kernel_children_integrable_of_atoms labels F₁ F₂ outer parentWidth hZ b
    (atoms.left b) (atoms.right b) (atoms.leftAmplitude b.val) (atoms.rightAmplitude b.val)
    (atoms.left_nonneg b.val (Finset.mem_filter.mp b.property).1)
    (atoms.right_nonneg b.val (Finset.mem_filter.mp b.property).1)
    J₁₁ J₁₂ J₂₁ J₂₂ (atoms.left_radius b.val (Finset.mem_filter.mp b.property).1)
    (atoms.right_radius b.val (Finset.mem_filter.mp b.property).1)

end FourierAtomControl
end ActualNormalizedPairFamily

/-- This last convergence consequence uses the same numerical child
energies. No measurability of the type of moment models is needed. -/
theorem actual_normalized_pair_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (left right : Ω → MomentData K ω ψ)
    (a b : RealParameters) (t u : Ω → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hl : Integrable (fun ξ => normalizedPairedEnergy (left ξ) a Z (t ξ)) μ)
    (hr : Integrable (fun ξ => normalizedPairedEnergy (right ξ) b Z (u ξ)) μ) :
    Integrable (fun ξ =>
      Real.sqrt (normalizedPairedEnergy (left ξ) a Z (t ξ)) *
        Real.sqrt (normalizedPairedEnergy (right ξ) b Z (u ξ))) μ := by
  apply ((hl.add hr).div_const 2).mono'
    ((Real.continuous_sqrt.comp_aestronglyMeasurable hl.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hr.aestronglyMeasurable))
  exact Filter.Eventually.of_forall fun ξ => by
    let L := normalizedPairedEnergy (left ξ) a Z (t ξ)
    let R := normalizedPairedEnergy (right ξ) b Z (u ξ)
    have hL : 0 ≤ L := normalizedPairedEnergy_nonneg (left ξ) a Z (t ξ) hZ
    have hR : 0 ≤ R := normalizedPairedEnergy_nonneg (right ξ) b Z (u ξ) hZ
    change ‖Real.sqrt L * Real.sqrt R‖ ≤ (L + R) / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    nlinarith [Real.sq_sqrt hL, Real.sq_sqrt hR, sq_nonneg (Real.sqrt L - Real.sqrt R)]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.FourierAtomControl.source_integral
#print axioms HeckeSkeleton.Moments.EngineStep.actual_normalized_pair_integrable
