import HeckeSkeleton.LowHybrid.Counting

/-!
# Positivity is already forced by linear norm counting

The zero cutoff excludes every element of norm zero. On a nonempty type,
the singleton count also forces the counting constant to be positive.
These are consequences of the counting premise, not additional inputs.
-/

namespace HeckeSkeleton.LowHybrid

noncomputable section

theorem linear_norm_counting_norm_one_le
    {I : Type*} (q : I → ℕ) (C : ℝ) (hcount : LinearNormCounting q C) :
    ∀ i : I, 1 ≤ q i := by
  classical
  intro i
  by_contra hnot
  have hz : q i = 0 := by omega
  have hb := hcount 0 {i} (by
    intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact le_of_eq hz)
  norm_num at hb

theorem linear_norm_counting_constant_pos_of_element
    {I : Type*} (q : I → ℕ) (C : ℝ) (hcount : LinearNormCounting q C) (i : I) :
    0 < C := by
  classical
  have hb := hcount (q i) {i} (by
    intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact le_rfl)
  have hb' : (1 : ℝ) ≤ C * (q i : ℝ) := by simpa only [Finset.card_singleton, Nat.cast_one] using hb
  by_contra hnot
  have hC : C ≤ 0 := le_of_not_gt hnot
  have hprod : C * (q i : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hC (Nat.cast_nonneg _)
  linarith

theorem linear_norm_counting_constant_pos
    {I : Type*} [Nonempty I] (q : I → ℕ) (C : ℝ) (hcount : LinearNormCounting q C) :
    0 < C :=
  linear_norm_counting_constant_pos_of_element q C hcount (Classical.choice ‹Nonempty I›)

#print axioms linear_norm_counting_norm_one_le
#print axioms linear_norm_counting_constant_pos

end
end HeckeSkeleton.LowHybrid
