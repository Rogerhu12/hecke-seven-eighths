import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedFamily

/-!
# The same kernels under dependent finite reindexing

The active sigma family uses each component's original measure and
the exact normalized children already chosen in that component.
Kernel mass and child integrals therefore commute with the finite
dependent sum. Finiteness and integrability also pass along these
same projections, without any new choice or numerical estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

namespace ActualNormalizedPairFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V J : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V]
variable {Λ : J → Type*} {Z : ℝ}
variable (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)
variable (outer : Finset J) (labels : ∀ j, Finset (Λ j))
variable (μ : ∀ j, Λ j → Measure V) (parentWidth : ℝ)

/-- The mass is the exact dependent sum of the original component
kernel masses, including their original measures. -/
theorem sum_sigmaCombine_kernel_mass :
    (∑ b : (sigmaCombine families).active (outer.sigma labels),
      ((sigmaCombine families).kernel (outer.sigma labels)
        (fun p => μ p.1 p.2) parentWidth b).real Set.univ) =
      ∑ j : outer, ∑ b : (families j.val).active (labels j.val),
        ((families j.val).kernel (labels j.val) (μ j.val) parentWidth b).real Set.univ := by
  rw [sum_sigmaCombine_active families outer labels]
  rfl

/-- No integral is replaced by a bound: this is the same integrand
under the same kernel at every original active label. -/
theorem sum_sigmaCombine_child_integral :
    (∑ b : (sigmaCombine families).active (outer.sigma labels),
      ∫ ξ, (sigmaCombine families).childPair (outer.sigma labels) b ξ
        ∂(sigmaCombine families).kernel (outer.sigma labels)
          (fun p => μ p.1 p.2) parentWidth b) =
      ∑ j : outer, ∑ b : (families j.val).active (labels j.val),
        ∫ ξ, (families j.val).childPair (labels j.val) b ξ
          ∂(families j.val).kernel (labels j.val) (μ j.val) parentWidth b := by
  rw [sum_sigmaCombine_active families outer labels]
  rfl

/-- The combined kernel at a label is its original component kernel. -/
theorem sigmaCombine_kernel_finite
    (hfinite : ∀ j : outer, ∀ b : (families j.val).active (labels j.val),
      IsFiniteMeasure ((families j.val).kernel (labels j.val) (μ j.val) parentWidth b))
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    IsFiniteMeasure ((sigmaCombine families).kernel (outer.sigma labels)
      (fun p => μ p.1 p.2) parentWidth b) :=
  hfinite (sigmaActiveOuter families outer labels b) (sigmaActiveInner families outer labels b)

theorem sigmaCombine_childPair_integrable
    (hcomponents : ∀ j : outer, ∀ b : (families j.val).active (labels j.val),
      Integrable ((families j.val).childPair (labels j.val) b)
        ((families j.val).kernel (labels j.val) (μ j.val) parentWidth b))
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    Integrable ((sigmaCombine families).childPair (outer.sigma labels) b)
      ((sigmaCombine families).kernel (outer.sigma labels)
        (fun p => μ p.1 p.2) parentWidth b) :=
  hcomponents (sigmaActiveOuter families outer labels b) (sigmaActiveInner families outer labels b)

/-- Both actual normalized energies retain their original data,
parameters and evaluation at zero under the sigma reindexing. -/
theorem sigmaCombine_children_integrable
    (hcomponents : ∀ j : outer, ∀ b : (families j.val).active (labels j.val),
      Integrable (fun ξ => normalizedPairedEnergy
        ((families j.val).leftData (labels j.val) b ξ)
        ((families j.val).leftParameters (labels j.val) b) Z 0)
        ((families j.val).kernel (labels j.val) (μ j.val) parentWidth b) ∧
      Integrable (fun ξ => normalizedPairedEnergy
        ((families j.val).rightData (labels j.val) b ξ)
        ((families j.val).rightParameters (labels j.val) b) Z 0)
        ((families j.val).kernel (labels j.val) (μ j.val) parentWidth b))
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    Integrable (fun ξ => normalizedPairedEnergy
      ((sigmaCombine families).leftData (outer.sigma labels) b ξ)
      ((sigmaCombine families).leftParameters (outer.sigma labels) b) Z 0)
      ((sigmaCombine families).kernel (outer.sigma labels)
        (fun p => μ p.1 p.2) parentWidth b) ∧
    Integrable (fun ξ => normalizedPairedEnergy
      ((sigmaCombine families).rightData (outer.sigma labels) b ξ)
      ((sigmaCombine families).rightParameters (outer.sigma labels) b) Z 0)
      ((sigmaCombine families).kernel (outer.sigma labels)
        (fun p => μ p.1 p.2) parentWidth b) :=
  hcomponents (sigmaActiveOuter families outer labels b) (sigmaActiveInner families outer labels b)

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sum_sigmaCombine_kernel_mass
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sum_sigmaCombine_child_integral
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_kernel_finite
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_childPair_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_children_integrable
