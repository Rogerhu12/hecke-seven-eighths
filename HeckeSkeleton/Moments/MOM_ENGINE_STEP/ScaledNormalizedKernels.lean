import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyAtoms

/-!
# Original outer factors on the same normalized kernels

The first-source normalization, finite source fibre and pool coefficient
multiply a stored leaf's outer weight. They act on its already chosen
kernel by scalar multiplication of the measure. All children, profile
densities, removals and both original Fourier kernels remain the same.
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
variable (labels : Finset Λ)
variable (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ)
variable (parentWidth factor : ℝ) (hfactor : 0 ≤ factor)

include hfactor

/-- This is the literal original outer scalar, paid once in the measure. -/
theorem kernel_outer_mul (b : family.active labels) :
    family.kernel labels (actualNestedLabelMeasure F₁ F₂ (fun i => factor * outer i))
        parentWidth b =
      ENNReal.ofReal factor •
        family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b := by
  rw [family.kernel_actualNestedLabelMeasure, family.kernel_actualNestedLabelMeasure,
    ENNReal.ofReal_mul hfactor, smul_smul]

theorem kernel_outer_mul_integral (b : family.active labels)
    (f : WithLp 2 (U × E) → ℝ) :
    (∫ ξ, f ξ
      ∂family.kernel labels (actualNestedLabelMeasure F₁ F₂ (fun i => factor * outer i))
        parentWidth b) =
      factor * ∫ ξ, f ξ
        ∂family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b := by
  rw [family.kernel_outer_mul labels F₁ F₂ outer parentWidth factor hfactor,
    integral_smul_measure, ENNReal.toReal_ofReal hfactor, smul_eq_mul]

theorem kernel_outer_mul_mass (b : family.active labels) :
    (family.kernel labels (actualNestedLabelMeasure F₁ F₂ (fun i => factor * outer i))
      parentWidth b).real Set.univ =
      factor * (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer)
        parentWidth b).real Set.univ := by
  rw [family.kernel_outer_mul labels F₁ F₂ outer parentWidth factor hfactor]
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hfactor]

theorem kernel_outer_mul_integrable (b : family.active labels)
    (f : WithLp 2 (U × E) → ℝ)
    (hf : Integrable f
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) :
    Integrable f
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ (fun i => factor * outer i))
        parentWidth b) := by
  rw [family.kernel_outer_mul labels F₁ F₂ outer parentWidth factor hfactor]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem kernel_outer_mul_finite (b : family.active labels)
    [IsFiniteMeasure
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)] :
    IsFiniteMeasure
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ (fun i => factor * outer i))
        parentWidth b) := by
  rw [family.kernel_outer_mul labels F₁ F₂ outer parentWidth factor hfactor]
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem sum_child_integral_outer_mul :
    (∑ b : family.active labels,
      ∫ ξ, family.childPair labels b ξ
        ∂family.kernel labels (actualNestedLabelMeasure F₁ F₂ (fun i => factor * outer i))
          parentWidth b) =
      factor * ∑ b : family.active labels,
        ∫ ξ, family.childPair labels b ξ
          ∂family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b := by
  simp only [family.kernel_outer_mul_integral labels F₁ F₂ outer parentWidth factor hfactor,
    Finset.mul_sum]

theorem sum_kernel_mass_outer_mul :
    (∑ b : family.active labels,
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ (fun i => factor * outer i))
        parentWidth b).real Set.univ) =
      factor * ∑ b : family.active labels,
        (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer)
          parentWidth b).real Set.univ := by
  simp only [family.kernel_outer_mul_mass labels F₁ F₂ outer parentWidth factor hfactor,
    Finset.mul_sum]

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.kernel_outer_mul
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.kernel_outer_mul_integral
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.kernel_outer_mul_mass
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.kernel_outer_mul_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.kernel_outer_mul_finite
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sum_child_integral_outer_mul
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sum_kernel_mass_outer_mul
