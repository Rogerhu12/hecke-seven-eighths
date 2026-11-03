import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RowIntegralKernel
import Mathlib.MeasureTheory.Measure.Real

/-!
# One positive measure for the actual finite branches

The branch label is a numerical discrete label (dyadic index and one of
two fixed contour lines), not an arithmetic row or a polynomial model.
Its product with the original frequency space is fixed before the node.
The finite sum of pushforwards retains every original branch measure.

Only numerical functions on this space are integrated.  The injection of
one branch is a measurable embedding, so neither integral transport nor
the almost-everywhere geometric assertions require a measurable space
on the family of polynomial models.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory
open scoped BigOperators Classical

universe u v
variable {B : Type u} [MeasurableSpace B] [MeasurableSingletonClass B]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- The genuine injection of a fixed numerical branch. -/
theorem measurableEmbedding_finiteBranch (b : B) :
    MeasurableEmbedding (fun ξ : Ω => (b, ξ)) := by
  refine ⟨?_, measurable_prodMk_left, ?_⟩
  · intro ξ η h
    exact congrArg Prod.snd h
  · intro s hs
    have himage : (fun ξ : Ω => (b, ξ)) '' s = {b} ×ˢ s := by
      ext x
      rcases x with ⟨k, η⟩
      simp only [Set.mem_image, Prod.mk.injEq, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ξ, hξ, hleft, hright⟩
        exact ⟨hleft.symm, hright ▸ hξ⟩
      · rintro ⟨hleft, hright⟩
        exact ⟨η, hright, hleft.symm, rfl⟩
    rw [himage]
    exact (MeasurableSet.singleton b).prod hs

/-- All finite branches share one fixed parameter space. -/
def finiteBranchMeasure (branches : Finset B) (μ : B → Measure Ω) : Measure (B × Ω) :=
  ∑ b ∈ branches, (μ b).map (fun ξ => (b, ξ))

theorem finiteBranchMeasure_finite (branches : Finset B) (μ : B → Measure Ω)
    [∀ b, IsFiniteMeasure (μ b)] : IsFiniteMeasure (finiteBranchMeasure branches μ) := by
  unfold finiteBranchMeasure
  infer_instance

/-- This formula holds for arbitrary sets, as each branch injection is
a measurable embedding.  It will also transport nonmeasurable predicates. -/
theorem finiteBranchMeasure_apply (branches : Finset B) (μ : B → Measure Ω)
    (s : Set (B × Ω)) :
    finiteBranchMeasure branches μ s =
      ∑ b ∈ branches, μ b ((fun ξ => (b, ξ)) ⁻¹' s) := by
  induction branches using Finset.induction_on with
  | empty => simp [finiteBranchMeasure]
  | @insert b bs hb ih =>
    simp only [finiteBranchMeasure, Finset.sum_insert hb, Measure.add_apply,
      (measurableEmbedding_finiteBranch b).map_apply]
    exact congrArg (fun t => μ b ((fun ξ => (b, ξ)) ⁻¹' s) + t) ih

theorem finiteBranchMeasure_integrable (branches : Finset B) (μ : B → Measure Ω)
    (value : B × Ω → ℝ)
    (hi : ∀ b ∈ branches, Integrable (fun ξ => value (b, ξ)) (μ b)) :
    Integrable value (finiteBranchMeasure branches μ) := by
  apply integrable_finsetSum_measure.mpr
  intro b hb
  exact (measurableEmbedding_finiteBranch b).integrable_map_iff.mpr (hi b hb)

/-- Exact transport of the original finite sum of numerical integrals. -/
theorem integral_finiteBranchMeasure (branches : Finset B) (μ : B → Measure Ω)
    (value : B × Ω → ℝ)
    (hi : ∀ b ∈ branches, Integrable (fun ξ => value (b, ξ)) (μ b)) :
    (∫ x, value x ∂finiteBranchMeasure branches μ) =
      ∑ b ∈ branches, ∫ ξ, value (b, ξ) ∂μ b := by
  rw [finiteBranchMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro b _hb
    exact (measurableEmbedding_finiteBranch b).integral_map value
  · intro b hb
    exact (measurableEmbedding_finiteBranch b).integrable_map_iff.mpr (hi b hb)

/-- Complete mass is additive; no branch or row is discarded. -/
theorem finiteBranchMeasure_mass (branches : Finset B) (μ : B → Measure Ω)
    [∀ b, IsFiniteMeasure (μ b)] :
    (finiteBranchMeasure branches μ).real Set.univ =
      ∑ b ∈ branches, (μ b).real Set.univ := by
  letI := finiteBranchMeasure_finite branches μ
  calc
    _ = ∫ _x : B × Ω, (1 : ℝ) ∂finiteBranchMeasure branches μ := by simp
    _ = ∑ b ∈ branches, ∫ _ξ : Ω, (1 : ℝ) ∂μ b :=
      integral_finiteBranchMeasure branches μ (fun _ => 1) (fun _ _ => integrable_const 1)
    _ = _ := by simp

/-- Actual child geometry can be transported without imposing any
measurability assumption on the predicate or the child map. -/
theorem ae_finiteBranchMeasure (branches : Finset B) (μ : B → Measure Ω)
    {p : B × Ω → Prop} (hp : ∀ b ∈ branches, ∀ᵐ ξ ∂μ b, p (b, ξ)) :
    ∀ᵐ x ∂finiteBranchMeasure branches μ, p x := by
  apply ae_iff.mpr
  rw [finiteBranchMeasure_apply]
  apply Finset.sum_eq_zero
  intro b hb
  exact ae_iff.mp (hp b hb)

end HeckeSkeleton.Moments.EngineInduction
