import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedCapacityProvider
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WeightedNestedFourierMeasure
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstWeightedReduction
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Both continuous phases in one actual child family

The ordinary product carries the original product Fourier measure. The
child term dictionaries use the genuine Hilbert product `WithLp 2`.
Composing the child family with `toLp` identifies their parameters and
combines the two original phases exactly. No inner product is assigned
to the ordinary maximum product norm, and no Haar normalization is
changed. In particular a single capacity choice is made before both
continuous variables, rather than separately at each first frequency.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform

namespace HeckeSkeleton.Moments.EngineStep

open NumberField MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem jointPhase_toLp_pair (ξ x : U) (η y : V) :
    jointPhase (WithLp.toLp 2 (ξ, η)) (WithLp.toLp 2 (x, y)) =
      jointPhase ξ x * jointPhase η y := by
  simp only [jointPhase, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
    AddChar.map_add_eq_mul, Circle.coe_mul]

/-- The first phase stays in its whole original coefficient until it
is combined with the second phase. -/
theorem nested_jointFourierColumn {ι : Type*}
    (columns : Finset ι) (c : ι → ℂ) (x : ι → U) (y : ι → V) (ξ : U) (η : V) :
    jointFourierColumn columns (fun i => c i * jointPhase ξ (x i)) y η =
      jointFourierColumn columns c (fun i => WithLp.toLp 2 (x i, y i))
        (WithLp.toLp 2 (ξ, η)) := by
  simp only [jointFourierColumn, jointPhase_toLp_pair, mul_assoc]

theorem nested_jointColumnEnergy {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : H → ι → ℂ) (x : H → ι → U) (y : H → ι → V) (ξ : U) (η : V) :
    jointColumnEnergy rows columns q
      (fun h i => c h i * jointPhase ξ (x h i)) y η =
      jointColumnEnergy rows columns q c (fun h i => WithLp.toLp 2 (x h i, y h i))
        (WithLp.toLp 2 (ξ, η)) := by
  simp only [jointColumnEnergy, nested_jointFourierColumn]

private theorem measurable_jointColumnEnergy_toLp
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {H ι : Type*} (rows : Finset H) (columns : Finset ι)
    (q : H → ℂ) (c : H → ι → ℂ) (x : H → ι → WithLp 2 (U × V)) :
    Measurable (fun z : U × V =>
      jointColumnEnergy rows columns q c x (WithLp.toLp 2 z)) := by
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
  unfold jointColumnEnergy jointFourierColumn
  apply Finset.measurable_sum
  intro h _
  apply measurable_const.mul
  apply Measurable.pow_const
  apply Measurable.norm
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (hphase (x h i))

/-- The finite joint energy is measurable for the original product
sigma-algebra, using the two coordinate phases. -/
theorem measurable_nested_jointColumnEnergy
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {H ι : Type*} (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : H → ι → ℂ) (x : H → ι → WithLp 2 (U × V)) :
    Measurable (fun z : U × V =>
      jointColumnEnergy rows columns q c x (WithLp.toLp 2 z)) :=
  measurable_jointColumnEnergy_toLp rows columns q c x

/-- Convergence of the actual two-frequency finite source follows from
its fixed coefficient arrays. This estimate is used only for Fubini. -/
theorem nested_joint_cauchy_integrable
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {H ι κ : Type*} (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → WithLp 2 (U × V)) (y : H → κ → WithLp 2 (U × V))
    (μ : Measure (U × V)) [IsFiniteMeasure μ] :
    Integrable (fun z : U × V =>
      Real.sqrt (jointColumnEnergy rows left q c x (WithLp.toLp 2 z)) *
        Real.sqrt (jointColumnEnergy rows right q d y (WithLp.toLp 2 z))) μ := by
  have hc := measurable_jointColumnEnergy_toLp rows left q c x
  have hd := measurable_jointColumnEnergy_toLp rows right q d y
  apply (integrable_const
    (Real.sqrt (jointColumnMass rows left q c) *
      Real.sqrt (jointColumnMass rows right q d))).mono'
    (hc.sqrt.mul hd.sqrt).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    change ‖Real.sqrt (jointColumnEnergy rows left q c x (WithLp.toLp 2 z)) *
        Real.sqrt (jointColumnEnergy rows right q d y (WithLp.toLp 2 z))‖ ≤
      Real.sqrt (jointColumnMass rows left q c) *
        Real.sqrt (jointColumnMass rows right q d)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul
      (Real.sqrt_le_sqrt (jointColumnEnergy_le_mass rows left q c x _))
      (Real.sqrt_le_sqrt (jointColumnEnergy_le_mass rows right q d y _))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

variable [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The genuine iterated first/second Fourier integrals are one integral
of the same whole columns. Both parameter locations were fixed earlier. -/
theorem nested_joint_cauchy_fubini
    {H ι κ : Type*} (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V)
    (F₁ : SchwartzMap U ℂ) (F₂ : SchwartzMap V ℂ) :
    (∫ ξ, (∫ η, ‖(𝓕 F₂) η‖ *
      (Real.sqrt (jointColumnEnergy rows left q
        (fun h i => c h i * jointPhase ξ (x₁ h i)) x₂ η) *
       Real.sqrt (jointColumnEnergy rows right q
        (fun h j => d h j * jointPhase ξ (y₁ h j)) y₂ η)))
      ∂actualFourierMeasure F₁) =
    ∫ z, Real.sqrt (jointColumnEnergy rows left q c
        (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i)) (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right q d
        (fun h j => WithLp.toLp 2 (y₁ h j, y₂ h j)) (WithLp.toLp 2 z))
      ∂nestedFourierMeasure F₁ F₂ := by
  letI := nestedFourierMeasure_finite F₁ F₂
  rw [nestedFourierMeasure_integral_iterated F₁ F₂ _
    (nested_joint_cauchy_integrable rows left right q c d _ _ _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    rw [actualFourierMeasure_integral_eq]
    simp only [nested_jointColumnEnergy]

theorem iterated_joint_cauchy_integrable
    {H ι κ : Type*} (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x₁ : H → ι → U) (x₂ : H → ι → V)
    (y₁ : H → κ → U) (y₂ : H → κ → V)
    (F₁ : SchwartzMap U ℂ) (F₂ : SchwartzMap V ℂ) :
    Integrable (fun ξ => ∫ η, ‖(𝓕 F₂) η‖ *
      (Real.sqrt (jointColumnEnergy rows left q
        (fun h i => c h i * jointPhase ξ (x₁ h i)) x₂ η) *
       Real.sqrt (jointColumnEnergy rows right q
        (fun h j => d h j * jointPhase ξ (y₁ h j)) y₂ η)))
      (actualFourierMeasure F₁) := by
  letI := actualFourierMeasure_finite F₁
  letI := actualFourierMeasure_finite F₂
  letI := nestedFourierMeasure_finite F₁ F₂
  have hi := (nested_joint_cauchy_integrable rows left right q c d
    (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i))
    (fun h j => WithLp.toLp 2 (y₁ h j, y₂ h j)) (nestedFourierMeasure F₁ F₂)).integral_prod_left
  convert hi using 1
  funext ξ
  dsimp only
  rw [actualFourierMeasure_integral_eq]
  simp only [nested_jointColumnEnergy]

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {H : Type*} {k : ℕ} {ω ψ : HeckeCharacter F}

namespace ActualAllocatedSource

variable (s : ActualAllocatedSource A (WithLp 2 (U × V)) H k)

def nestedEnergy (z : U × V) : ℝ := s.energy (σ := σ) (WithLp.toLp 2 z)

theorem nestedEnergy_nonneg (z : U × V) : 0 ≤ s.nestedEnergy (σ := σ) z :=
  s.energy_nonneg (σ := σ) (WithLp.toLp 2 z)

theorem nestedEnergy_zero_iff :
    (∀ z : U × V, s.nestedEnergy (σ := σ) z = 0) ↔
      ∀ z : WithLp 2 (U × V), s.energy (σ := σ) z = 0 := by
  constructor
  · intro h z
    simpa only [nestedEnergy, WithLp.toLp_ofLp] using h (WithLp.ofLp z)
  · intro h z
    exact h (WithLp.toLp 2 z)

namespace Calibration

variable {s} (D : s.Calibration (σ := σ) ω ψ)

def nestedData (z : U × V) : MomentData F ω ψ := D.data (WithLp.toLp 2 z)

def nestedHeight (z : U × V) : ℝ := D.height (WithLp.toLp 2 z)

theorem nested_energy_le (z : U × V) :
    s.nestedEnergy (σ := σ) z ≤
      D.mass * pairedEnergy (D.nestedData z) D.parameters s.base (D.nestedHeight z) :=
  D.energy_le (WithLp.toLp 2 z)

theorem nested_energy_le_clipped (z : U × V) :
    s.nestedEnergy (σ := σ) z ≤
      D.mass * pairedEnergy (D.clippedData (WithLp.toLp 2 z))
        D.clippedParameters s.base (D.nestedHeight z) :=
  D.energy_le_clipped (WithLp.toLp 2 z)

end Calibration

/-- This finite-polynomial bound is used only for convergence under
the already controlled positive measure, never as a recursive mass
estimate. All source coefficients and both locations precede z. -/
theorem nestedEnergy_integrable (μ : Measure (U × V)) [IsFiniteMeasure μ] :
    Integrable (s.nestedEnergy (σ := σ)) μ := by
  let c := fun h => rawSourceCoefficient (σ := σ) (s.characters h)
    (s.extractedFactor h) (s.row h).element s.scale₁ s.scale₂ s.base s.length
    (s.leftWeight h) (s.rightWeight h) (s.slotWeight h)
  let x := fun h => rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)
  have hc : Continuous (s.nestedEnergy (σ := σ)) :=
    (continuous_jointColumnEnergy s.rows s.allocation.columns s.weight c x).comp
      (WithLp.prod_continuous_toLp 2 U V)
  apply (integrable_const (jointColumnMass s.rows s.allocation.columns s.weight c)).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (s.nestedEnergy_nonneg (σ := σ) z)]
    exact jointColumnEnergy_le_mass s.rows s.allocation.columns s.weight c x
      (WithLp.toLp 2 z)

end ActualAllocatedSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.nested_jointColumnEnergy
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.nestedEnergy_integrable
