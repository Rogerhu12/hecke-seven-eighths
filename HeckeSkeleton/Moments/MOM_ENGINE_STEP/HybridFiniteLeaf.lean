import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHybridResidual

/-!
# Literal finite hybrid leaves of the two actual Fourier transforms

A leaf stores the original finite rows, both complete coefficient
functions, the two fixed kernels, and the two locations on each side.
Its exceptional and ordinary terms use the same positive product
Fourier measure.  Fubini is proved from these finite polynomials.

The allocation label below is the actual divisor, phase character and
two whole-occurrence allocations.  No total-cost identity is a field.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum UniqueFactorizationMonoid
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- All data are literal source data.  The right coefficient has not
yet been conjugated; conjugation occurs once in the paired integrand. -/
structure ActualHybridLeaf (K : Type) [Field K] [NumberField K]
    (H U V : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  leftSlots : ℕ
  rightSlots : ℕ
  rows : Finset H
  left : Finset (AllocationColumn K leftSlots)
  right : Finset (AllocationColumn K rightSlots)
  firstKernel : SchwartzMap U ℂ
  secondKernel : SchwartzMap V ℂ
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  rowWeight : H → ℂ
  leftCoefficient : H → AllocationColumn K leftSlots → ℂ
  rightCoefficient : H → AllocationColumn K rightSlots → ℂ
  leftFirst : H → AllocationColumn K leftSlots → U
  rightFirst : H → AllocationColumn K rightSlots → U
  leftSecond : H → AllocationColumn K leftSlots → V
  rightSecond : H → AllocationColumn K rightSlots → V
  exceptional : H → Prop

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U V)

def measure : Measure (U × V) :=
  nestedFourierMeasure B.firstKernel B.secondKernel

def exceptionalIntegrand (z : U × V) : ℝ :=
  jointColumnPairMagnitude (B.rows.filter B.exceptional) B.left B.right
    B.rowWeight B.leftCoefficient (fun h j => star (B.rightCoefficient h j))
    (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i))
    (fun h j => WithLp.toLp 2 (-B.rightFirst h j, B.rightSecond h j))
    (WithLp.toLp 2 z)

def ordinaryIntegrand (z : U × V) : ℝ :=
  Real.sqrt (jointColumnEnergy (B.rows.filter fun h => ¬B.exceptional h) B.left
    B.rowWeight B.leftCoefficient
    (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i))
    (WithLp.toLp 2 z)) *
  Real.sqrt (jointColumnEnergy (B.rows.filter fun h => ¬B.exceptional h) B.right
    B.rowWeight (fun h j => star (B.rightCoefficient h j))
    (fun h j => WithLp.toLp 2 (-B.rightFirst h j, B.rightSecond h j))
    (WithLp.toLp 2 z))

def exceptionalCost : ℝ := B.weight * ∫ z, B.exceptionalIntegrand z ∂B.measure

def ordinaryCost : ℝ := B.weight * ∫ z, B.ordinaryIntegrand z ∂B.measure

def cost : ℝ := B.exceptionalCost + B.ordinaryCost

def firstPhaseCost (ξ : U) : ℝ :=
  B.weight * jointHybridKernelCost B.secondKernel B.rows B.left B.right B.rowWeight
    (fun h i => B.leftCoefficient h i * jointPhase ξ (B.leftFirst h i))
    (fun h j => B.rightCoefficient h j * jointPhase ξ (B.rightFirst h j))
    B.leftSecond B.rightSecond B.exceptional

theorem exceptionalIntegrand_nonneg (z : U × V) : 0 ≤ B.exceptionalIntegrand z :=
  jointColumnPairMagnitude_nonneg _ _ _ _ _ _ _ _ _

theorem ordinaryIntegrand_nonneg (z : U × V) : 0 ≤ B.ordinaryIntegrand z :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem exceptionalIntegrand_integrable :
    Integrable B.exceptionalIntegrand B.measure := by
  letI : IsFiniteMeasure B.measure := nestedFourierMeasure_finite B.firstKernel B.secondKernel
  exact nested_joint_magnitude_integrable _ _ _ _ _ _ _ _ _

theorem ordinaryIntegrand_integrable :
    Integrable B.ordinaryIntegrand B.measure := by
  letI : IsFiniteMeasure B.measure := nestedFourierMeasure_finite B.firstKernel B.secondKernel
  exact nested_joint_cauchy_integrable _ _ _ _ _ _ _ _ _

theorem exceptionalCost_nonneg : 0 ≤ B.exceptionalCost :=
  mul_nonneg B.weight_nonneg (integral_nonneg B.exceptionalIntegrand_nonneg)

theorem ordinaryCost_nonneg : 0 ≤ B.ordinaryCost :=
  mul_nonneg B.weight_nonneg (integral_nonneg B.ordinaryIntegrand_nonneg)

theorem cost_nonneg : 0 ≤ B.cost :=
  add_nonneg B.exceptionalCost_nonneg B.ordinaryCost_nonneg

theorem cost_eq_zero_of_weight_eq_zero (hB : B.weight = 0) : B.cost = 0 := by
  simp only [cost, exceptionalCost, ordinaryCost, hB, zero_mul, add_zero]

theorem exceptionalCost_eq_zero_of_weight_eq_zero (hB : B.weight = 0) :
    B.exceptionalCost = 0 := by
  simp only [exceptionalCost, hB, zero_mul]

theorem ordinaryCost_eq_zero_of_weight_eq_zero (hB : B.weight = 0) :
    B.ordinaryCost = 0 := by
  simp only [ordinaryCost, hB, zero_mul]

theorem firstPhaseCost_integrable :
    Integrable B.firstPhaseCost (actualFourierMeasure B.firstKernel) :=
  (iterated_joint_hybrid_integrable B.rows B.left B.right B.rowWeight
    B.leftCoefficient B.rightCoefficient B.leftFirst B.leftSecond
    B.rightFirst B.rightSecond B.exceptional B.firstKernel B.secondKernel).const_mul B.weight

/-- Exact separation of terminal exceptional products and ordinary
paired energies under the single genuine nested Fourier measure. -/
theorem cost_eq_integral :
    B.cost = B.weight * ∫ z,
      nestedJointHybridIntegrand B.rows B.left B.right B.rowWeight
        B.leftCoefficient B.rightCoefficient B.leftFirst B.leftSecond
        B.rightFirst B.rightSecond B.exceptional z ∂B.measure := by
  change B.weight * (∫ z, B.exceptionalIntegrand z ∂B.measure) +
      B.weight * (∫ z, B.ordinaryIntegrand z ∂B.measure) =
    B.weight * ∫ z, B.exceptionalIntegrand z + B.ordinaryIntegrand z ∂B.measure
  rw [integral_add B.exceptionalIntegrand_integrable B.ordinaryIntegrand_integrable,
    mul_add]

/-- This is derived from the stored finite polynomials and actual
Fubini; it is not an input to a source family. -/
theorem integral_firstPhaseCost :
    (∫ ξ, B.firstPhaseCost ξ ∂actualFourierMeasure B.firstKernel) = B.cost := by
  unfold firstPhaseCost
  rw [integral_const_mul, nested_joint_hybrid_fubini]
  exact B.cost_eq_integral.symm

def scale (a : ℝ) (ha : 0 ≤ a) : ActualHybridLeaf K H U V :=
  { B with weight := a * B.weight, weight_nonneg := mul_nonneg ha B.weight_nonneg }

@[simp] theorem scale_firstPhaseCost (a : ℝ) (ha : 0 ≤ a) (ξ : U) :
    (B.scale a ha).firstPhaseCost ξ = a * B.firstPhaseCost ξ := by
  dsimp only [firstPhaseCost, scale]
  ring

@[simp] theorem scale_exceptionalCost (a : ℝ) (ha : 0 ≤ a) :
    (B.scale a ha).exceptionalCost = a * B.exceptionalCost := by
  dsimp only [exceptionalCost, exceptionalIntegrand, measure, scale]
  ring

@[simp] theorem scale_ordinaryCost (a : ℝ) (ha : 0 ≤ a) :
    (B.scale a ha).ordinaryCost = a * B.ordinaryCost := by
  dsimp only [ordinaryCost, ordinaryIntegrand, measure, scale]
  ring

@[simp] theorem scale_cost (a : ℝ) (ha : 0 ≤ a) :
    (B.scale a ha).cost = a * B.cost := by
  rw [cost, scale_exceptionalCost, scale_ordinaryCost, cost, mul_add]

end ActualHybridLeaf

variable {k l : ℕ} {γ : Type*} [Fintype γ]

/-- The exact finite divisor/character/two-allocation labels. -/
abbrev HybridAllocationLabel
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (rightIdeals : AllocationColumn K l → Ideal (𝓞 K)) (k : ℕ) (γ : Type*) :=
  Σ D : divisorPool (childCartesianColumns T₁ T₂ T) rightIdeals,
    γ × AllocationMass.idealAllocations D.val (k + 2) ×
      AllocationMass.idealAllocations D.val (l + 2)

def fullCorrelationHybridLeaf
    (F₁ : SchwartzMap U ℂ) (F₂ : SchwartzMap V ℂ) (rows : Finset H)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (rightIdeals : AllocationColumn K l → Ideal (𝓞 K))
    (q : H → ℂ) (phaseCoefficient : γ → ℂ)
    (c : γ → H → AllocationColumn K k → ℂ)
    (d : γ → H → AllocationColumn K l → ℂ)
    (x₁ : H → AllocationColumn K k → U) (x₂ : H → AllocationColumn K k → V)
    (y₁ : H → AllocationColumn K l → U) (y₂ : H → AllocationColumn K l → V)
    (exceptional : ∀ D : Ideal (𝓞 K), γ →
      (primeSupport D → Finset (Fin (k + 2))) →
      (primeSupport D → Finset (Fin (l + 2))) → H → Prop)
    (b : HybridAllocationLabel T₁ T₂ T rightIdeals k γ) : ActualHybridLeaf K H U V where
  leftSlots := k
  rightSlots := l
  rows := rows
  left := pairedAllocatedColumns b.1.val b.2.2.1.val S₁ S₂ S id id HeightOneSpectrum.asIdeal
  right := pairedAllocatedColumns b.1.val b.2.2.2.val T₁ T₂ T id id HeightOneSpectrum.asIdeal
  firstKernel := F₁
  secondKernel := F₂
  weight := ‖(moebius b.1.val : ℂ)‖ * ‖phaseCoefficient b.2.1‖
  weight_nonneg := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rowWeight := q
  leftCoefficient := c b.2.1
  rightCoefficient := d b.2.1
  leftFirst := x₁
  rightFirst := y₁
  leftSecond := x₂
  rightSecond := y₂
  exceptional := exceptional b.1.val b.2.1 b.2.2.1.val b.2.2.2.val

/-- The original complete hybrid cost is literally the finite sum of
its divisor/character/allocation leaves at the first Fourier variable. -/
theorem fullCorrelationHybridCost_eq_leaf_sum
    (F₁ : SchwartzMap U ℂ) (F₂ : SchwartzMap V ℂ) (rows : Finset H)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (rightIdeals : AllocationColumn K l → Ideal (𝓞 K))
    (q : H → ℂ) (phaseCoefficient : γ → ℂ)
    (c : γ → H → AllocationColumn K k → ℂ)
    (d : γ → H → AllocationColumn K l → ℂ)
    (x₁ : H → AllocationColumn K k → U) (x₂ : H → AllocationColumn K k → V)
    (y₁ : H → AllocationColumn K l → U) (y₂ : H → AllocationColumn K l → V)
    (exceptional : ∀ D : Ideal (𝓞 K), γ →
      (primeSupport D → Finset (Fin (k + 2))) →
      (primeSupport D → Finset (Fin (l + 2))) → H → Prop) (ξ : U) :
    fullCorrelationHybridCost F₂ rows S₁ S₂ S T₁ T₂ T rightIdeals q phaseCoefficient
      (fun χ h i => c χ h i * jointPhase ξ (x₁ h i))
      (fun χ h j => d χ h j * jointPhase ξ (y₁ h j)) x₂ y₂ exceptional =
      ∑ b : HybridAllocationLabel T₁ T₂ T rightIdeals k γ,
        (fullCorrelationHybridLeaf F₁ F₂ rows S₁ S₂ S T₁ T₂ T rightIdeals
          q phaseCoefficient c d x₁ x₂ y₁ y₂ exceptional b).firstPhaseCost ξ := by
  unfold fullCorrelationHybridCost
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, fullCorrelationHybridLeaf,
    ActualHybridLeaf.firstPhaseCost]
  simp only [Finset.mul_sum, mul_assoc]
  refine (Finset.sum_coe_sort
    (divisorPool (childCartesianColumns T₁ T₂ T) rightIdeals) _).symm.trans ?_
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro χ _
  refine (Finset.sum_coe_sort
    (AllocationMass.idealAllocations D.val (k + 2)) _).symm.trans ?_
  apply Finset.sum_congr rfl
  intro a _
  exact (Finset.sum_coe_sort
    (AllocationMass.idealAllocations D.val (l + 2)) _).symm

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.integral_firstPhaseCost
#print axioms HeckeSkeleton.Moments.EngineStep.fullCorrelationHybridCost_eq_leaf_sum

