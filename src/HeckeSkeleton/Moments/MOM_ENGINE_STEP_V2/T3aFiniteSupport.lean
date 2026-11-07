module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernelExceptionalSplit

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Exact finite support and retained-row reindexing -/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep

namespace T3a

section Finite

variable {H I J V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Delete precisely the rows with zero weight or an identically zero
whole column. Cancellation inside a nonzero whole column is preserved. -/
theorem pairMagnitude_eq_supported
    (rows : Finset H) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (a : H → I → ℂ) (b : H → J → ℂ)
    (x : H → I → V) (y : H → J → V) (ξ : V) :
    jointColumnPairMagnitude rows left right q a b x y ξ =
      jointColumnPairMagnitude
        (rows.filter (fun h => q h ≠ 0 ∧
          (∃ i ∈ left, a h i ≠ 0) ∧ (∃ j ∈ right, b h j ≠ 0)))
        left right q a b x y ξ := by
  unfold jointColumnPairMagnitude
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro h hh hnot
  have hnot' : ¬ (q h ≠ 0 ∧
      (∃ i ∈ left, a h i ≠ 0) ∧ (∃ j ∈ right, b h j ≠ 0)) := by
    intro hp
    exact hnot (Finset.mem_filter.mpr ⟨hh, hp⟩)
  by_cases hq : q h = 0
  · simp only [hq, norm_zero, zero_mul]
  by_cases ha : ∃ i ∈ left, a h i ≠ 0
  · have hb : ∀ j ∈ right, b h j = 0 := by
      intro j hj
      by_contra hb
      exact hnot' ⟨hq, ha, j, hj, hb⟩
    have hz : jointFourierColumn right (b h) (y h) ξ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hb j hj, zero_mul]
    simp only [hz, norm_zero, mul_zero]
  · have hb : ∀ i ∈ left, a h i = 0 := by
      intro i hi
      by_contra hb
      exact ha ⟨i, hi, hb⟩
    have hz : jointFourierColumn left (a h) (x h) ξ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hb i hi, zero_mul]
    simp only [hz, norm_zero, mul_zero, zero_mul]

/-- Passing to the subtype of a retained row set is an exact finite
reindexing, before either Fourier integration. -/
theorem pairMagnitude_subtype_filter
    (rows : Finset H) (P : H → Prop) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (a : H → I → ℂ) (b : H → J → ℂ)
    (x : H → I → V) (y : H → J → V) (ξ : V) :
    jointColumnPairMagnitude (rows.filter P) left right q a b x y ξ =
      jointColumnPairMagnitude
        ((Finset.univ : Finset rows).filter (fun h => P h.val)) left right
        (fun h => q h.val) (fun h => a h.val) (fun h => b h.val)
        (fun h => x h.val) (fun h => y h.val) ξ := by
  simp only [jointColumnPairMagnitude, Finset.sum_filter]
  exact (Finset.sum_coe_sort rows (fun h =>
    if P h then ‖q h‖ * ‖jointFourierColumn left (a h) (x h) ξ‖ *
      ‖jointFourierColumn right (b h) (y h) ξ‖ else 0)).symm

end Finite

end T3a

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.pairMagnitude_eq_supported
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.pairMagnitude_subtype_filter
