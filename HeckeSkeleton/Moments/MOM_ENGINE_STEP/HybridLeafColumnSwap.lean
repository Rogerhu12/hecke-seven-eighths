import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf

/-!
# Either actual column may pay the centered exceptional saving

The exceptional magnitude is symmetric in its two complete Fourier
polynomials. A literal hybrid leaf uses a conjugated right coefficient
and a negative first location. Its column exchange therefore conjugates
both stored coefficients and negates both first locations, while keeping
the second locations, row weights, exceptional predicate, outer scalar
and the two Fourier kernels. This exchanges the two actual polynomials
at the same two Fourier parameters.

The resulting exceptional and ordinary costs are exactly the original
costs. This is a symmetry of a terminal estimate, and makes no new choice
of normalized children or of their removed slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

section Magnitude

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Exchange the complete column polynomials without changing any row
or its weight. The coefficients themselves are not split. -/
theorem jointColumnPairMagnitude_swap_columns {H ι κ : Type*}
    (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (weight : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) (ξ : V) :
    jointColumnPairMagnitude rows left right weight c d x y ξ =
      jointColumnPairMagnitude rows right left weight d c y x ξ := by
  unfold jointColumnPairMagnitude
  apply Finset.sum_congr rfl
  intro h _
  ring

end Magnitude

variable {K : Type} [Field K] [NumberField K]
variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U V)

/-- The complete correlation conjugates when its two original moduli
are exchanged and its frequency is negated. Both positive integrands
depend on its norm, so this operation retains their literal values. -/
def conjugateRowWeights : ActualHybridLeaf K H U V :=
  { B with rowWeight := fun h => star (B.rowWeight h) }

@[simp] theorem conjugateRowWeights_exceptionalIntegrand (z : U × V) :
    B.conjugateRowWeights.exceptionalIntegrand z = B.exceptionalIntegrand z := by
  simp only [exceptionalIntegrand, conjugateRowWeights, jointColumnPairMagnitude, norm_star]
  apply Finset.sum_congr
  · ext h
    simp only [Finset.mem_filter]
  · intro h _
    rfl

@[simp] theorem conjugateRowWeights_ordinaryIntegrand (z : U × V) :
    B.conjugateRowWeights.ordinaryIntegrand z = B.ordinaryIntegrand z := by
  simp only [ordinaryIntegrand, conjugateRowWeights, jointColumnEnergy, norm_star]
  apply congrArg₂ (fun a b : ℝ => Real.sqrt a * Real.sqrt b)
  all_goals
    apply Finset.sum_congr
    · ext h
      simp only [Finset.mem_filter]
    · intro h _
      rfl

@[simp] theorem conjugateRowWeights_exceptionalCost :
    B.conjugateRowWeights.exceptionalCost = B.exceptionalCost := by
  change B.weight * (∫ z, B.conjugateRowWeights.exceptionalIntegrand z ∂B.measure) =
    B.weight * (∫ z, B.exceptionalIntegrand z ∂B.measure)
  simp only [conjugateRowWeights_exceptionalIntegrand]

@[simp] theorem conjugateRowWeights_ordinaryCost :
    B.conjugateRowWeights.ordinaryCost = B.ordinaryCost := by
  change B.weight * (∫ z, B.conjugateRowWeights.ordinaryIntegrand z ∂B.measure) =
    B.weight * (∫ z, B.ordinaryIntegrand z ∂B.measure)
  simp only [conjugateRowWeights_ordinaryIntegrand]

/-- Exchange precisely the two polynomials occurring in the actual
hybrid integrands. All original row and measure data are retained. -/
def swapColumns : ActualHybridLeaf K H U V where
  leftSlots := B.rightSlots
  rightSlots := B.leftSlots
  rows := B.rows
  left := B.right
  right := B.left
  firstKernel := B.firstKernel
  secondKernel := B.secondKernel
  weight := B.weight
  weight_nonneg := B.weight_nonneg
  rowWeight := B.rowWeight
  leftCoefficient h i := star (B.rightCoefficient h i)
  rightCoefficient h i := star (B.leftCoefficient h i)
  leftFirst h i := -B.rightFirst h i
  rightFirst h i := -B.leftFirst h i
  leftSecond := B.rightSecond
  rightSecond := B.leftSecond
  exceptional := B.exceptional

@[simp] theorem swapColumns_measure : B.swapColumns.measure = B.measure := rfl

/-- The exact exceptional integrand at the same two actual Fourier
variables; there is no frequency change of variables in the measure. -/
@[simp] theorem swapColumns_exceptionalIntegrand (z : U × V) :
    B.swapColumns.exceptionalIntegrand z = B.exceptionalIntegrand z := by
  simp only [exceptionalIntegrand, swapColumns, star_star, neg_neg]
  exact jointColumnPairMagnitude_swap_columns _ _ _ _ _ _ _ _ _

@[simp] theorem swapColumns_ordinaryIntegrand (z : U × V) :
    B.swapColumns.ordinaryIntegrand z = B.ordinaryIntegrand z := by
  simp only [ordinaryIntegrand, swapColumns, star_star, neg_neg]
  exact mul_comm _ _

@[simp] theorem swapColumns_exceptionalCost :
    B.swapColumns.exceptionalCost = B.exceptionalCost := by
  change B.weight * (∫ z, B.swapColumns.exceptionalIntegrand z ∂B.measure) =
    B.weight * (∫ z, B.exceptionalIntegrand z ∂B.measure)
  simp only [swapColumns_exceptionalIntegrand]

@[simp] theorem swapColumns_ordinaryCost :
    B.swapColumns.ordinaryCost = B.ordinaryCost := by
  change B.weight * (∫ z, B.swapColumns.ordinaryIntegrand z ∂B.measure) =
    B.weight * (∫ z, B.ordinaryIntegrand z ∂B.measure)
  simp only [swapColumns_ordinaryIntegrand]

@[simp] theorem swapColumns_cost : B.swapColumns.cost = B.cost := by
  rw [cost, swapColumns_exceptionalCost, swapColumns_ordinaryCost, cost]

/-- A bound proved using the other original column applies to this
same terminal contribution. This helper does not select output children. -/
theorem exceptionalCost_le_of_swapColumns {bound : ℝ}
    (h : B.swapColumns.exceptionalCost ≤ bound) : B.exceptionalCost ≤ bound := by
  simpa only [swapColumns_exceptionalCost] using h

/-- Combine the literal polynomial exchange with the conjugation of
the actual swapped correlation. This is the source orientation with
negative original frequency, evaluated under the unchanged measures. -/
def swapCorrelationColumns : ActualHybridLeaf K H U V :=
  B.swapColumns.conjugateRowWeights

@[simp] theorem swapCorrelationColumns_exceptionalCost :
    B.swapCorrelationColumns.exceptionalCost = B.exceptionalCost := by
  rw [swapCorrelationColumns, conjugateRowWeights_exceptionalCost,
    swapColumns_exceptionalCost]

@[simp] theorem swapCorrelationColumns_ordinaryCost :
    B.swapCorrelationColumns.ordinaryCost = B.ordinaryCost := by
  rw [swapCorrelationColumns, conjugateRowWeights_ordinaryCost,
    swapColumns_ordinaryCost]

end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.swapColumns_exceptionalIntegrand
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.swapColumns_exceptionalCost
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.swapColumns_ordinaryCost
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.swapCorrelationColumns_exceptionalCost
