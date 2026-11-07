module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveExpansion
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationKernel

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Residual expansion under the unchanged finite row measure

The exact divisor and occurrence expansion is inserted before either
square norm. Weighted finite Minkowski then separates the same labels,
with their actual signs. Both sides retain their independent allocations
and the original joint Fourier parameter; no cardinality factor enters.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation

open EngineStep NumberField
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {H V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ}

theorem joint_residual_expansion (B : Carrier K k) (mask : Ideal (𝓞 K))
    (hmask : mask ≠ 0) (c : AllocationColumn K k → ℂ)
    (x : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn ((carrierColumns B).filter
      (fun i => IsCoprime mask (columnIdeal i))) c x ξ =
      ∑ a : labels B mask, sign a.val *
        jointFourierColumn (columns B a.val) c x ξ :=
  residual_mobius_labels B mask hmask (fun i => c i * jointPhase ξ (x i))

/-- A constant complex factor costs its exact norm outside the square
root, including the zero factor and the empty original row set. -/
theorem sqrt_row_energy_scalar (rows : Finset H) (q f : H → ℂ) (z : ℂ) :
    Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖z * f h‖ ^ 2) =
      ‖z‖ * Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2) := by
  have he : (∑ h ∈ rows, ‖q h‖ * ‖z * f h‖ ^ 2) =
      ‖z‖ ^ 2 * ∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [norm_mul, mul_pow]
    ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The retained passive labels are separated inside the original
finite square norm. Their signs are not replaced by a label count. -/
theorem sqrt_residual_energy_le (B : Carrier K k) (mask : Ideal (𝓞 K))
    (hmask : mask ≠ 0) (rows : Finset H) (q : H → ℂ)
    (c : H → AllocationColumn K k → ℂ)
    (x : H → AllocationColumn K k → V) (ξ : V) :
    Real.sqrt (jointColumnEnergy rows ((carrierColumns B).filter
      (fun i => IsCoprime mask (columnIdeal i))) q c x ξ) ≤
      ∑ a : labels B mask, ‖sign a.val‖ *
        Real.sqrt (jointColumnEnergy rows (columns B a.val) q c x ξ) := by
  unfold jointColumnEnergy
  simp_rw [joint_residual_expansion B mask hmask]
  refine (sqrt_row_energy_sum rows Finset.univ q
    (fun (a : labels B mask) h => sign a.val *
      jointFourierColumn (columns B a.val) (c h) (x h) ξ)).trans_eq ?_
  apply Finset.sum_congr rfl
  intro a _
  exact sqrt_row_energy_scalar rows q
    (fun h => jointFourierColumn (columns B a.val) (c h) (x h) ξ) (sign a.val)

variable {l : ℕ}

/-- The left and right divisor labels are independent. Their exact
product weight is paid once under the common Fourier parameter. -/
theorem paired_residual_energy_le
    (B : Carrier K k) (D : Carrier K l) (leftMask rightMask : Ideal (𝓞 K))
    (hleft : leftMask ≠ 0) (hright : rightMask ≠ 0)
    (rows : Finset H) (q : H → ℂ)
    (c : H → AllocationColumn K k → ℂ)
    (d : H → AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V)
    (y : H → AllocationColumn K l → V) (ξ : V) :
    Real.sqrt (jointColumnEnergy rows ((carrierColumns B).filter
      (fun i => IsCoprime leftMask (columnIdeal i))) q c x ξ) *
      Real.sqrt (jointColumnEnergy rows ((carrierColumns D).filter
        (fun i => IsCoprime rightMask (columnIdeal i))) q d y ξ) ≤
      ∑ a : labels B leftMask, ∑ b : labels D rightMask,
        (‖sign a.val‖ * ‖sign b.val‖) *
          (Real.sqrt (jointColumnEnergy rows (columns B a.val) q c x ξ) *
            Real.sqrt (jointColumnEnergy rows (columns D b.val) q d y ξ)) := by
  have hL := sqrt_residual_energy_le B leftMask hleft rows q c x ξ
  have hR := sqrt_residual_energy_le D rightMask hright rows q d y ξ
  calc
    _ ≤ (∑ a : labels B leftMask, ‖sign a.val‖ *
          Real.sqrt (jointColumnEnergy rows (columns B a.val) q c x ξ)) *
        (∑ b : labels D rightMask, ‖sign b.val‖ *
          Real.sqrt (jointColumnEnergy rows (columns D b.val) q d y ξ)) :=
      mul_le_mul hL hR (Real.sqrt_nonneg _)
        (Finset.sum_nonneg fun a _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation.joint_residual_expansion
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation.sqrt_residual_energy_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation.paired_residual_energy_le
