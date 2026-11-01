import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantProfileExtraction

/-!
# Move a fixed row scalar into the original leaf's outer weight

The scalar is independent of the original row and of both Fourier
parameters. Moving its norm outside preserves both the exceptional
integral and the ordinary paired integral exactly. All finite columns,
their characters and locations, the exceptional predicate, and both
original kernels remain unchanged. This also applies when the scalar
vanishes, and composes with the original coefficient extraction.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem fixed_row_scalar_energy {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rows : Finset H) (columns : Finset I) (q w : H → ℂ) (a : ℂ)
    (c : H → I → ℂ) (x : H → I → E) (ξ : E)
    (hq : ∀ h ∈ rows, q h = a * w h) :
    jointColumnEnergy rows columns q c x ξ =
      ‖a‖ * jointColumnEnergy rows columns w c x ξ := by
  unfold jointColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [hq h hh, norm_mul]
  ring

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U V)

def withRowWeight (w : H → ℂ) : ActualHybridLeaf K H U V :=
  { B with rowWeight := w }

/-- Put the norm of the actual fixed multiplier into the existing
outer weight. The measure itself still uses the same two kernels. -/
def moveConstantRowWeight (w : H → ℂ) (a : ℂ) : ActualHybridLeaf K H U V :=
  (B.withRowWeight w).scale ‖a‖ (norm_nonneg _)

variable (w : H → ℂ) (a : ℂ)
variable (hrow : ∀ h ∈ B.rows, B.rowWeight h = a * w h)

include hrow in
theorem exceptionalIntegrand_fixedRowScalar (z : U × V) :
    B.exceptionalIntegrand z = ‖a‖ * (B.withRowWeight w).exceptionalIntegrand z := by
  unfold exceptionalIntegrand jointColumnPairMagnitude
  dsimp only [withRowWeight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [hrow h (Finset.mem_filter.mp hh).1]
  simp only [norm_mul]
  ring

include hrow in
theorem ordinaryIntegrand_fixedRowScalar (z : U × V) :
    B.ordinaryIntegrand z = ‖a‖ * (B.withRowWeight w).ordinaryIntegrand z := by
  have hl := fixed_row_scalar_energy
    (B.rows.filter fun h => ¬B.exceptional h) B.left B.rowWeight w a B.leftCoefficient
    (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i))
    (WithLp.toLp 2 z) (fun h hh => hrow h (Finset.mem_filter.mp hh).1)
  have hr := fixed_row_scalar_energy
    (B.rows.filter fun h => ¬B.exceptional h) B.right B.rowWeight w a
    (fun h i => star (B.rightCoefficient h i))
    (fun h i => WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i))
    (WithLp.toLp 2 z) (fun h hh => hrow h (Finset.mem_filter.mp hh).1)
  unfold ordinaryIntegrand
  dsimp only [withRowWeight]
  rw [hl, hr, Real.sqrt_mul (norm_nonneg a), Real.sqrt_mul (norm_nonneg a)]
  calc
    _ = Real.sqrt ‖a‖ ^ 2 *
        (Real.sqrt (jointColumnEnergy (B.rows.filter fun h => ¬B.exceptional h)
          B.left w B.leftCoefficient
          (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i)) (WithLp.toLp 2 z)) *
        Real.sqrt (jointColumnEnergy (B.rows.filter fun h => ¬B.exceptional h)
          B.right w (fun h i => star (B.rightCoefficient h i))
          (fun h i => WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i))
          (WithLp.toLp 2 z))) := by ring
    _ = _ := by
      rw [Real.sq_sqrt (norm_nonneg a)]
      rfl

include hrow in
theorem exceptionalCost_eq_moveConstantRowWeight :
    B.exceptionalCost = (B.moveConstantRowWeight w a).exceptionalCost := by
  change B.weight * (∫ z, B.exceptionalIntegrand z ∂B.measure) =
    (‖a‖ * B.weight) * (∫ z, (B.withRowWeight w).exceptionalIntegrand z ∂B.measure)
  have hi := integral_congr_ae (μ := B.measure) (Filter.Eventually.of_forall
    (B.exceptionalIntegrand_fixedRowScalar w a hrow))
  rw [hi, integral_const_mul]
  ring

include hrow in
theorem ordinaryCost_eq_moveConstantRowWeight :
    B.ordinaryCost = (B.moveConstantRowWeight w a).ordinaryCost := by
  change B.weight * (∫ z, B.ordinaryIntegrand z ∂B.measure) =
    (‖a‖ * B.weight) * (∫ z, (B.withRowWeight w).ordinaryIntegrand z ∂B.measure)
  have hi := integral_congr_ae (μ := B.measure) (Filter.Eventually.of_forall
    (B.ordinaryIntegrand_fixedRowScalar w a hrow))
  rw [hi, integral_const_mul]
  ring

include hrow in
theorem cost_eq_moveConstantRowWeight :
    B.cost = (B.moveConstantRowWeight w a).cost := by
  rw [cost, cost, B.exceptionalCost_eq_moveConstantRowWeight w a hrow,
    B.ordinaryCost_eq_moveConstantRowWeight w a hrow]

namespace ConstantAtomExtraction

variable {B} (X : B.ConstantAtomExtraction)

/-- The residual columns with their actual constant pair paid once in
the original outer scalar, including both original terminal parts. -/
def outerLeaf : ActualHybridLeaf K H U V :=
  X.leaf.moveConstantRowWeight B.rowWeight (X.leftScalar * star X.rightScalar)

private theorem rowWeight_eq_outerScalar (h : H) :
    X.leaf.rowWeight h = (X.leftScalar * star X.rightScalar) * B.rowWeight h := by
  change B.rowWeight h * X.leftScalar * star X.rightScalar = _
  ring

theorem exceptionalCost_eq_outerLeaf : B.exceptionalCost = X.outerLeaf.exceptionalCost :=
  X.exceptionalCost_eq.trans (X.leaf.exceptionalCost_eq_moveConstantRowWeight B.rowWeight
    (X.leftScalar * star X.rightScalar) (fun h _ => X.rowWeight_eq_outerScalar h))

theorem ordinaryCost_eq_outerLeaf : B.ordinaryCost = X.outerLeaf.ordinaryCost :=
  X.ordinaryCost_eq.trans (X.leaf.ordinaryCost_eq_moveConstantRowWeight B.rowWeight
    (X.leftScalar * star X.rightScalar) (fun h _ => X.rowWeight_eq_outerScalar h))

theorem outerLeaf_weight :
    X.outerLeaf.weight = (‖X.leftScalar‖ * ‖X.rightScalar‖) * B.weight := by
  simp only [outerLeaf, moveConstantRowWeight, scale, withRowWeight,
    leaf, withConstantAtoms, norm_mul, norm_star]

@[simp] theorem outerLeaf_firstKernel : X.outerLeaf.firstKernel = B.firstKernel := rfl
@[simp] theorem outerLeaf_secondKernel : X.outerLeaf.secondKernel = B.secondKernel := rfl
@[simp] theorem outerLeaf_rowWeight : X.outerLeaf.rowWeight = B.rowWeight := rfl

end ConstantAtomExtraction
end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.exceptionalCost_eq_moveConstantRowWeight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ordinaryCost_eq_moveConstantRowWeight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ConstantAtomExtraction.exceptionalCost_eq_outerLeaf
