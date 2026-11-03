import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf

/-!
# Zero original row weights on a literal hybrid leaf

An individual zero row weight kills its original row product before
either Fourier integration.  Both kernels, both complete columns and
the original outer scalar are unchanged.  This low-level module does
not depend on exceptional numerical calibration or terminal budgets.
-/

noncomputable section
open scoped Classical BigOperators NumberField
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {H U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U E)

theorem exceptionalIntegrand_eq_zero_of_rowWeight_zero
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = 0) (z : U × E) :
    B.exceptionalIntegrand z = 0 := by
  unfold exceptionalIntegrand jointColumnPairMagnitude
  apply Finset.sum_eq_zero
  intro h hh
  rw [hweight h (Finset.mem_filter.mp hh).1, norm_zero, zero_mul, zero_mul]

theorem exceptionalCost_eq_zero_of_rowWeight_zero
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = 0) : B.exceptionalCost = 0 := by
  simp only [exceptionalCost, B.exceptionalIntegrand_eq_zero_of_rowWeight_zero hweight,
    integral_zero, mul_zero]

end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.exceptionalCost_eq_zero_of_rowWeight_zero
