import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedSecondClassProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CenteredAllocatedChildren

/-!
# The whole centered second kernel on one already fixed row class

The subtraction remains inside each complete column until the row class
has been fixed. Finite weighted L2 Minkowski then gives the four ordinary
rectangle pairs on that same class and under the same positive measure.
The exceptional-class endpoint is not invoked here and must retain its
whole centered difference.

All finite exchanges are justified by the actual finite columns.
-/

noncomputable section
open scoped Classical BigOperators NumberField
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H α β : Type*}
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

local notation "W" => WithLp 2 (U × V)

theorem kernelDivisorCoefficient_sub
    (I : α → Ideal (𝓞 K)) (L : Ideal (𝓞 K)) (c d phase : α → ℂ)
    (χ : α → H → ℂ) (h : H) (i : α) :
    kernelDivisorCoefficient I L (fun i => c i - d i) phase χ h i =
      kernelDivisorCoefficient I L c phase χ h i -
        kernelDivisorCoefficient I L d phase χ h i := by
  unfold kernelDivisorCoefficient
  split_ifs <;> ring

/-- A paired finite column estimate, with the same complete row weight
in all four resulting rectangles. -/
theorem joint_centered_cauchy_measure_bound
    (μ : Measure (U × V)) [IsFiniteMeasure μ]
    (rows : Finset H) (left : Finset α) (right : Finset β)
    (q : H → ℂ) (c₀ c₁ : H → α → ℂ) (d₀ d₁ : H → β → ℂ)
    (x : H → α → W) (y : H → β → W) :
    (∫ z, Real.sqrt (jointColumnEnergy rows left q (fun h i => c₀ h i - c₁ h i) x
        (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right q (fun h j => d₀ h j - d₁ h j) y
        (WithLp.toLp 2 z)) ∂μ) ≤
    (∫ z, Real.sqrt (jointColumnEnergy rows left q c₀ x (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right q d₀ y (WithLp.toLp 2 z)) ∂μ) +
    (∫ z, Real.sqrt (jointColumnEnergy rows left q c₀ x (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right q d₁ y (WithLp.toLp 2 z)) ∂μ) +
    (∫ z, Real.sqrt (jointColumnEnergy rows left q c₁ x (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right q d₀ y (WithLp.toLp 2 z)) ∂μ) +
    (∫ z, Real.sqrt (jointColumnEnergy rows left q c₁ x (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right q d₁ y (WithLp.toLp 2 z)) ∂μ) := by
  let E := fun (c : H → α → ℂ) (d : H → β → ℂ) (z : U × V) =>
    Real.sqrt (jointColumnEnergy rows left q c x (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right q d y (WithLp.toLp 2 z))
  have hi (c : H → α → ℂ) (d : H → β → ℂ) : Integrable (E c d) μ :=
    nested_joint_cauchy_integrable rows left right q c d x y μ
  have hb :
      (∫ z, E (fun h i => c₀ h i - c₁ h i) (fun h j => d₀ h j - d₁ h j) z ∂μ) ≤
      ∫ z, E c₀ d₀ z + E c₀ d₁ z + E c₁ d₀ z + E c₁ d₁ z ∂μ := by
    apply integral_mono (hi _ _)
      ((((hi c₀ d₀).add (hi c₀ d₁)).add (hi c₁ d₀)).add (hi c₁ d₁))
    intro z
    have hl := sqrt_joint_energy_sub rows left q c₀ c₁ x (WithLp.toLp 2 z)
    have hr := sqrt_joint_energy_sub rows right q d₀ d₁ y (WithLp.toLp 2 z)
    apply (mul_le_mul hl hr (Real.sqrt_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).trans_eq
    dsimp only [E]
    ring
  rw [integral_add (((hi c₀ d₀).add (hi c₀ d₁)).add (hi c₁ d₀)) (hi c₁ d₁),
    integral_add ((hi c₀ d₀).add (hi c₀ d₁)) (hi c₁ d₀),
    integral_add (hi c₀ d₀) (hi c₀ d₁)] at hb
  exact hb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- This inequality is used only after the actual finite exceptional
classification has separated the original complex source rows. It
does not mix a center of one class with a rectangle of another class. -/
theorem actual_measured_centered_kernel_bound
    (R : ActualSecondCorrelationRows A σ H ι)
    (μ : Measure (U × V)) [IsFiniteMeasure μ]
    (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray) (phaseTable : Ray × Ray → Circle)
    (c₀ c₁ : α → ℂ) (d₀ d₁ : β → ℂ)
    (x : H → α → W) (y : H → β → W) :
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable
      (fun i => c₀ i - c₁ i) (fun j => d₀ j - d₁ j) x y ≤
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c₀ d₀ x y +
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c₀ d₁ x y +
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c₁ d₀ x y +
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c₁ d₁ x y := by
  unfold actualMeasuredSecondKernelCost
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro L _
  simp only [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro χ _
  simp only [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [kernelDivisorCoefficient_sub, star_sub]
  exact joint_centered_cauchy_measure_bound μ R.rows left right
    (fun h => R.weight h * R.correlation h)
    (kernelDivisorCoefficient (fun i => (IA i).val) L c₀
      (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
      (fun i h => σ (A.sexticResidue (IA i) (R.frequency h))))
    (kernelDivisorCoefficient (fun i => (IA i).val) L c₁
      (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
      (fun i h => σ (A.sexticResidue (IA i) (R.frequency h))))
    (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L d₀
      (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
      (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j))
    (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L d₁
      (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
      (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j)) x y


theorem actual_measured_kernel_congr_coefficients
    (R : ActualSecondCorrelationRows A σ H ι)
    (μ : Measure (U × V)) (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray) (phaseTable : Ray × Ray → Circle)
    (c c' : α → ℂ) (f f' : β → ℂ)
    (x : H → α → W) (y : H → β → W)
    (hc : ∀ i ∈ left, c i = c' i) (hf : ∀ j ∈ right, f j = f' j) :
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c f x y =
      actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c' f' x y := by
  have he {J : Type*} (columns : Finset J) (a b : H → J → ℂ)
      (location : H → J → W) (ξ : W)
      (hab : ∀ h ∈ R.rows, ∀ i ∈ columns, a h i = b h i) :
      jointColumnEnergy R.rows columns (fun h => R.weight h * R.correlation h) a location ξ =
        jointColumnEnergy R.rows columns (fun h => R.weight h * R.correlation h) b location ξ := by
    unfold jointColumnEnergy
    apply Finset.sum_congr rfl
    intro h hh
    have hp : jointFourierColumn columns (a h) (location h) ξ =
        jointFourierColumn columns (b h) (location h) ξ := by
      unfold jointFourierColumn
      exact Finset.sum_congr rfl fun i hi => by rw [hab h hh i hi]
    rw [hp]
  unfold actualMeasuredSecondKernelCost
  apply Finset.sum_congr rfl
  intro L _
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    congr 1
    · congr 1
      apply he
      intro h _ i hi
      simp only [kernelDivisorCoefficient, hc i hi]
    · congr 1
      apply he
      intro h _ j hj
      simp only [kernelDivisorCoefficient, hf j hj]

/-- The actual original coefficients need agree with the two
rectangles only at individual retained columns. Neither a whole
polynomial identity nor an energy comparison is an input. -/
theorem actual_measured_centered_kernel_bound_of_terms
    (R : ActualSecondCorrelationRows A σ H ι)
    (μ : Measure (U × V)) [IsFiniteMeasure μ]
    (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray) (phaseTable : Ray × Ray → Circle)
    (c c₀ c₁ : α → ℂ) (f d₀ d₁ : β → ℂ)
    (x : H → α → W) (y : H → β → W)
    (hc : ∀ i ∈ left, c i = c₀ i - c₁ i)
    (hf : ∀ j ∈ right, f j = d₀ j - d₁ j) :
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c f x y ≤
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c₀ d₀ x y +
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c₀ d₁ x y +
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c₁ d₀ x y +
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c₁ d₁ x y := by
  rw [actual_measured_kernel_congr_coefficients Ray R μ left right IA IB rayLeft rayRight
    phaseTable c (fun i => c₀ i - c₁ i) f (fun j => d₀ j - d₁ j) x y hc hf]
  exact actual_measured_centered_kernel_bound Ray R μ left right IA IB rayLeft rayRight
    phaseTable c₀ c₁ d₀ d₁ x y


end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_measured_centered_kernel_bound

