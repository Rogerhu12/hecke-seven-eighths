import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHilbertPhase
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondHybridAllocation

/-!
# One product Fourier measure for the actual hybrid split

The exceptional product of two whole columns and the complementary
paired energy use the same two continuous parameters.  Their genuine
finite columns prove integrability, and exact Fubini combines the
original two Fourier measures.  The first phase in the right column is
conjugated once, hence its first location is negated.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem nested_jointColumnPairMagnitude {H ι κ : Type*}
    (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V) (ξ : U) (η : V) :
    jointColumnPairMagnitude rows left right q
      (fun h i => c h i * jointPhase ξ (x₁ h i))
      (fun h j => d h j * jointPhase ξ (y₁ h j)) x₂ y₂ η =
      jointColumnPairMagnitude rows left right q c d
        (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i))
        (fun h j => WithLp.toLp 2 (y₁ h j, y₂ h j)) (WithLp.toLp 2 (ξ, η)) := by
  simp only [jointColumnPairMagnitude, nested_jointFourierColumn]

theorem nested_joint_magnitude_integrable
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {H ι κ : Type*} (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → WithLp 2 (U × V)) (y : H → κ → WithLp 2 (U × V))
    (μ : Measure (U × V)) [IsFiniteMeasure μ] :
    Integrable (fun z : U × V =>
      jointColumnPairMagnitude rows left right q c d x y (WithLp.toLp 2 z)) μ := by
  have hphase (a : WithLp 2 (U × V)) :
      Measurable (fun z : U × V => jointPhase (WithLp.toLp 2 z) a) := by
    have heq : (fun z : U × V => jointPhase (WithLp.toLp 2 z) a) =
        (fun z : U × V => jointPhase z.1 (WithLp.ofLp a).1 *
          jointPhase z.2 (WithLp.ofLp a).2) := by
      funext z
      exact jointPhase_toLp_pair z.1 (WithLp.ofLp a).1 z.2 (WithLp.ofLp a).2
    rw [heq]
    exact ((continuous_jointPhase (WithLp.ofLp a).1).measurable.comp measurable_fst).mul
      ((continuous_jointPhase (WithLp.ofLp a).2).measurable.comp measurable_snd)
  have hc : Measurable (fun z : U × V =>
      jointColumnPairMagnitude rows left right q c d x y (WithLp.toLp 2 z)) := by
    unfold jointColumnPairMagnitude
    apply Finset.measurable_sum
    intro h _
    apply Measurable.mul
    · apply measurable_const.mul
      apply Measurable.norm
      unfold jointFourierColumn
      apply Finset.measurable_sum
      intro i _
      exact measurable_const.mul (hphase (x h i))
    · apply Measurable.norm
      unfold jointFourierColumn
      apply Finset.measurable_sum
      intro j _
      exact measurable_const.mul (hphase (y h j))
  apply (integrable_const (jointColumnPairMass rows left right q c d)).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    change ‖jointColumnPairMagnitude rows left right q c d x y (WithLp.toLp 2 z)‖ ≤
      jointColumnPairMass rows left right q c d
    rw [Real.norm_eq_abs, abs_of_nonneg
      (jointColumnPairMagnitude_nonneg rows left right q c d x y _)]
    exact jointColumnPairMagnitude_le_mass rows left right q c d x y _

/-- One actual exceptional/ordinary integrand on both Fourier variables.
The right whole coefficient is conjugated once and its first location
is negated, matching the original paired source. -/
def nestedJointHybridIntegrand {H ι κ : Type*}
    (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V)
    (exceptional : H → Prop) (z : U × V) : ℝ :=
  jointColumnPairMagnitude (rows.filter exceptional) left right q c
    (fun h j => star (d h j))
    (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i))
    (fun h j => WithLp.toLp 2 (-y₁ h j, y₂ h j)) (WithLp.toLp 2 z) +
  Real.sqrt (jointColumnEnergy (rows.filter fun h => ¬exceptional h) left q c
    (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i)) (WithLp.toLp 2 z)) *
  Real.sqrt (jointColumnEnergy (rows.filter fun h => ¬exceptional h) right q
    (fun h j => star (d h j))
    (fun h j => WithLp.toLp 2 (-y₁ h j, y₂ h j)) (WithLp.toLp 2 z))

theorem nestedJointHybridIntegrand_nonneg {H ι κ : Type*}
    (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V)
    (exceptional : H → Prop) (z : U × V) :
    0 ≤ nestedJointHybridIntegrand rows left right q c d x₁ x₂ y₁ y₂ exceptional z :=
  add_nonneg (jointColumnPairMagnitude_nonneg _ _ _ _ _ _ _ _ _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem nested_joint_hybrid_integrable
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {H ι κ : Type*} (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V)
    (exceptional : H → Prop) (μ : Measure (U × V)) [IsFiniteMeasure μ] :
    Integrable (nestedJointHybridIntegrand rows left right q c d x₁ x₂ y₁ y₂ exceptional) μ :=
  (nested_joint_magnitude_integrable (rows.filter exceptional) left right q c
    (fun h j => star (d h j))
    (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i))
    (fun h j => WithLp.toLp 2 (-y₁ h j, y₂ h j)) μ).add
      (nested_joint_cauchy_integrable (rows.filter fun h => ¬exceptional h) left right q c
        (fun h j => star (d h j))
        (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i))
        (fun h j => WithLp.toLp 2 (-y₁ h j, y₂ h j)) μ)

variable [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The inner actual hybrid kernel is exactly the integral of the same
two-frequency integrand; no Cauchy operation is moved across the row
partition. -/
theorem joint_hybrid_first_phase_integral {H ι κ : Type*}
    (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V)
    (exceptional : H → Prop) (F : SchwartzMap V ℂ) (ξ : U) :
    jointHybridKernelCost F rows left right q
      (fun h i => c h i * jointPhase ξ (x₁ h i))
      (fun h j => d h j * jointPhase ξ (y₁ h j)) x₂ y₂ exceptional =
      ∫ η, nestedJointHybridIntegrand rows left right q c d
        x₁ x₂ y₁ y₂ exceptional (ξ, η) ∂actualFourierMeasure F := by
  rw [actualFourierMeasure_integral_eq]
  unfold jointHybridKernelCost nestedJointHybridIntegrand
  have hs :
      (fun h j => star (d h j * jointPhase ξ (y₁ h j))) =
        (fun h j => star (d h j) * jointPhase ξ (-y₁ h j)) := by
    funext h j
    rw [star_mul', jointPhase_neg]
  rw [hs]
  simp only [nested_jointColumnPairMagnitude, nested_jointColumnEnergy]

theorem iterated_joint_hybrid_integrable {H ι κ : Type*}
    (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V)
    (exceptional : H → Prop)
    (F₁ : SchwartzMap U ℂ) (F₂ : SchwartzMap V ℂ) :
    Integrable (fun ξ => jointHybridKernelCost F₂ rows left right q
      (fun h i => c h i * jointPhase ξ (x₁ h i))
      (fun h j => d h j * jointPhase ξ (y₁ h j)) x₂ y₂ exceptional)
      (actualFourierMeasure F₁) := by
  letI := actualFourierMeasure_finite F₁
  letI := actualFourierMeasure_finite F₂
  letI := nestedFourierMeasure_finite F₁ F₂
  have hi := (nested_joint_hybrid_integrable rows left right q c d x₁ x₂ y₁ y₂
    exceptional (nestedFourierMeasure F₁ F₂)).integral_prod_left
  convert hi using 1
  funext ξ
  exact joint_hybrid_first_phase_integral rows left right q c d
    x₁ x₂ y₁ y₂ exceptional F₂ ξ

/-- The genuine first integral of the pre-Cauchy hybrid source is one
positive product-measure integral, with the same actual exception test
and the same complete coefficients throughout. -/
theorem nested_joint_hybrid_fubini {H ι κ : Type*}
    (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V)
    (exceptional : H → Prop)
    (F₁ : SchwartzMap U ℂ) (F₂ : SchwartzMap V ℂ) :
    (∫ ξ, jointHybridKernelCost F₂ rows left right q
      (fun h i => c h i * jointPhase ξ (x₁ h i))
      (fun h j => d h j * jointPhase ξ (y₁ h j)) x₂ y₂ exceptional
      ∂actualFourierMeasure F₁) =
      ∫ z, nestedJointHybridIntegrand rows left right q c d x₁ x₂ y₁ y₂ exceptional z
        ∂nestedFourierMeasure F₁ F₂ := by
  letI := nestedFourierMeasure_finite F₁ F₂
  rw [nestedFourierMeasure_integral_iterated F₁ F₂ _
    (nested_joint_hybrid_integrable rows left right q c d x₁ x₂ y₁ y₂ exceptional _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ =>
    joint_hybrid_first_phase_integral rows left right q c d x₁ x₂ y₁ y₂ exceptional F₂ ξ

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.nested_joint_hybrid_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.iterated_joint_hybrid_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.nested_joint_hybrid_fubini
