module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-! # Exact finite aggregation of old rows and fixed spectral branches -/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstFiniteAggregation

open scoped Classical BigOperators

variable {F Z I E J R : Type*}
variable [Fintype F] [Fintype Z] [Fintype I] [Fintype E] [Fintype J]
variable [CommSemiring R]

theorem reorder_rows (f : F → Z → I → E → J → R) :
    (∑ x : F, ∑ z : Z, ∑ i : I, ∑ e : E, ∑ j : J, f x z i e j) =
      ∑ i : I, ∑ e : E, ∑ j : J, ∑ x : F, ∑ z : Z, f x z i e j := by
  have h : (∑ x : F × Z, ∑ y : I × (E × J), f x.1 x.2 y.1 y.2.1 y.2.2) =
      ∑ y : I × (E × J), ∑ x : F × Z, f x.1 x.2 y.1 y.2.1 y.2.2 :=
    Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h

/-- The original common label weight is not replaced by a different
weight at each frequency. All rows with a selected center are collected
together, while the actual branch scalar is extracted exactly. -/
theorem collect_rows (assignment : Z → E → I) (c : I → E → J → R)
    (w : F → R) (v : I → E → J → F → Z → R) :
    (∑ x : F, ∑ z : Z, w x *
      (∑ i : I, ∑ e : E, if assignment z e = i then
        ∑ j : J, c i e j * v i e j x z else 0)) =
      ∑ i : I, ∑ e : E, ∑ j : J, c i e j *
        ∑ x : F, ∑ z : Z, if assignment z e = i then w x * v i e j x z else 0 := by
  calc
    _ = ∑ x : F, ∑ z : Z, ∑ i : I, ∑ e : E, ∑ j : J,
        if assignment z e = i then c i e j * (w x * v i e j x z) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      by_cases ha : assignment z e = i
      · simp only [if_pos ha, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      · simp only [if_neg ha, mul_zero, Finset.sum_const_zero]
    _ = ∑ i : I, ∑ e : E, ∑ j : J, ∑ x : F, ∑ z : Z,
        if assignment z e = i then c i e j * (w x * v i e j x z) else 0 :=
      reorder_rows _
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      by_cases ha : assignment z e = i <;> simp only [ha, if_true, if_false, mul_zero]

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstFiniteAggregation

end
