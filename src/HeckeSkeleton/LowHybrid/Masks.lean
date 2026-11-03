import HeckeSkeleton.LowHybrid.Assembly
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact Mobius masks on finite prime supports

A squarefree ideal is represented by its finite prime support. The Mobius
coefficient of a divisor support d is (-1)^card(d). The mask identity is
proved from Mathlib's alternating powerset sum, not assumed.

The coefficient F(k,P) stays at its original column throughout the exact
expansion. The passage from ExteriorIdeal divisors to prime-support subsets
is a separate arithmetic instantiation.

The complex powerset sum is the direct cast of
Finset.sum_powerset_neg_one_pow_card, also used by the supplied project
HeckePort/CenteredMoment/IdealMobius.lean.
-/

namespace HeckeSkeleton.LowHybrid
open scoped BigOperators
noncomputable section

/-- The complex alternating sum over all subsets of a finite support. -/
theorem complex_support_mobius_sum {Prime : Type*} [DecidableEq Prime]
    (support : Finset Prime) :
    (∑ d ∈ support.powerset, (-1 : ℂ) ^ d.card) =
      if support = ∅ then 1 else 0 := by
  have h :
      ((∑ d ∈ support.powerset, (-1 : ℤ) ^ d.card : ℤ) : ℂ) =
        ((if support = ∅ then 1 else 0 : ℤ) : ℂ) := by
    rw [Finset.sum_powerset_neg_one_pow_card]
  push_cast at h
  exact h

/-- Every squarefree-support Mobius coefficient has norm one. -/
theorem norm_support_mobius {Prime : Type*} (d : Finset Prime) :
    ‖(-1 : ℂ) ^ d.card‖ = 1 := by
  simp

/-- Exact coprimality mask from all common-prime subset contributions. -/
theorem support_coprime_mask_eq_mobius_sum {Prime : Type*} [DecidableEq Prime]
    (columnSupport rowSupport : Finset Prime) :
    (if Disjoint columnSupport rowSupport then (1 : ℂ) else 0) =
      ∑ d ∈ (columnSupport ∩ rowSupport).powerset, (-1 : ℂ) ^ d.card := by
  rw [complex_support_mobius_sum]
  simp only [Finset.disjoint_iff_inter_eq_empty]

/-- Common divisor supports are row divisor supports contained in the column. -/
theorem row_powerset_filter_eq_common_powerset
    {Prime : Type*} [DecidableEq Prime]
    (columnSupport rowSupport : Finset Prime) :
    rowSupport.powerset.filter (fun d => d ⊆ columnSupport) =
      (columnSupport ∩ rowSupport).powerset := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  exact and_comm

/-- Expand the entire mask over the actual row divisor set.
No residual coprimality mask can be reinserted after this identity. -/
theorem support_coprime_mask_eq_row_divisor_sum
    {Prime : Type*} [DecidableEq Prime]
    (columnSupport rowSupport : Finset Prime) :
    (if Disjoint columnSupport rowSupport then (1 : ℂ) else 0) =
      ∑ d ∈ rowSupport.powerset,
        if d ⊆ columnSupport then (-1 : ℂ) ^ d.card else 0 := by
  rw [← Finset.sum_filter,
    row_powerset_filter_eq_common_powerset columnSupport rowSupport]
  exact support_coprime_mask_eq_mobius_sum columnSupport rowSupport

/-- Exact finite sum exchange for one row. F retains its original column. -/
theorem support_mask_column_expansion
    {Prime P : Type*} [DecidableEq Prime]
    (columns : Finset P) (columnSupport : P → Finset Prime)
    (rowSupport : Finset Prime) (F : P → ℂ) :
    (∑ p ∈ columns,
      (if Disjoint (columnSupport p) rowSupport then (1 : ℂ) else 0) * F p) =
      ∑ d ∈ rowSupport.powerset, (-1 : ℂ) ^ d.card *
        ∑ p ∈ columns with d ⊆ columnSupport p, F p := by
  classical
  calc
    _ = ∑ p ∈ columns, ∑ d ∈ rowSupport.powerset,
        (if d ⊆ columnSupport p then (-1 : ℂ) ^ d.card else 0) * F p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [support_coprime_mask_eq_row_divisor_sum, Finset.sum_mul]
    _ = ∑ d ∈ rowSupport.powerset, ∑ p ∈ columns,
        (if d ⊆ columnSupport p then (-1 : ℂ) ^ d.card else 0) * F p :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp

/-- Exact family expansion with arbitrary dependence on the original row
and original column. No coefficient independence is asserted here. -/
theorem support_mask_row_expansion
    {Prime K P : Type*} [DecidableEq Prime]
    (columns : Finset P) (rowSupport : K → Finset Prime)
    (columnSupport : P → Finset Prime) (F : K → P → ℂ) (k : K) :
    (∑ p ∈ columns,
      (if Disjoint (columnSupport p) (rowSupport k) then (1 : ℂ) else 0) * F k p) =
      ∑ d ∈ (rowSupport k).powerset, (-1 : ℂ) ^ d.card *
        ∑ p ∈ columns with d ⊆ columnSupport p, F k p :=
  support_mask_column_expansion columns columnSupport (rowSupport k) (F k)

/-- Cauchy costs the divisor count of the individual row. -/
theorem support_mask_row_energy_local_count
    {Prime K P : Type*} [DecidableEq Prime]
    (rows : Finset K) (columns : Finset P)
    (rowSupport : K → Finset Prime) (columnSupport : P → Finset Prime)
    (F : K → P → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ columns,
      (if Disjoint (columnSupport p) (rowSupport k) then (1 : ℂ) else 0) * F k p‖ ^ 2) ≤
      ∑ k ∈ rows, (((rowSupport k).powerset).card : ℝ) *
        ∑ d ∈ (rowSupport k).powerset,
          ‖∑ p ∈ columns with d ⊆ columnSupport p, F k p‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro k hk
  rw [support_mask_row_expansion columns rowSupport columnSupport F k]
  exact bounded_coefficient_sum_sq ((rowSupport k).powerset)
    (fun d => (-1 : ℂ) ^ d.card)
    (fun d => ∑ p ∈ columns with d ⊆ columnSupport p, F k p)
    (fun d hd => le_of_eq (norm_support_mobius d))

/-- Uniform row-local divisor Cauchy for either complete moving mask. -/
theorem support_mask_row_energy
    {Prime K P : Type*} [DecidableEq Prime]
    (rows : Finset K) (columns : Finset P)
    (rowSupport : K → Finset Prime) (columnSupport : P → Finset Prime)
    (F : K → P → ℂ) (Delta : ℝ)
    (hcard : ∀ k ∈ rows, (((rowSupport k).powerset).card : ℝ) ≤ Delta) :
    (∑ k ∈ rows, ‖∑ p ∈ columns,
      (if Disjoint (columnSupport p) (rowSupport k) then (1 : ℂ) else 0) * F k p‖ ^ 2) ≤
      Delta * ∑ k ∈ rows, ∑ d ∈ (rowSupport k).powerset,
        ‖∑ p ∈ columns with d ⊆ columnSupport p, F k p‖ ^ 2 := by
  classical
  calc
    _ = ∑ k ∈ rows,
        ‖∑ d ∈ (rowSupport k).powerset, (-1 : ℂ) ^ d.card *
          (∑ p ∈ columns with d ⊆ columnSupport p, F k p)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [support_mask_row_expansion columns rowSupport columnSupport F k]
    _ ≤ _ := row_local_cauchy rows (fun k => (rowSupport k).powerset)
      (fun _ d => (-1 : ℂ) ^ d.card)
      (fun k d => ∑ p ∈ columns with d ⊆ columnSupport p, F k p)
      Delta (fun _ _ d _ => le_of_eq (norm_support_mobius d)) hcard

#print axioms complex_support_mobius_sum
#print axioms norm_support_mobius
#print axioms support_coprime_mask_eq_mobius_sum
#print axioms row_powerset_filter_eq_common_powerset
#print axioms support_coprime_mask_eq_row_divisor_sum
#print axioms support_mask_column_expansion
#print axioms support_mask_row_expansion
#print axioms support_mask_row_energy_local_count
#print axioms support_mask_row_energy

end
end HeckeSkeleton.LowHybrid

