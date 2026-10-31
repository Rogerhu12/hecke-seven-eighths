import Expansion.BufferedSelection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod

/-!
Convert existence of a buffered bin into an actual disjoint fixed-row
partition.  Wide buffered bins by themselves are only a cover.  This file
retains a single fixed choice for each row before any contour integration.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion
open scoped Classical BigOperators

abbrev BufferedIndex (lo hi e : ℝ) (n : ℕ) :=
  Fin (n + 1) × Fin (⌊(hi - lo) / e⌋₊ + 1)

def BufferedIndex.center {lo hi e : ℝ} {n : ℕ}
    (label : BufferedIndex lo hi e n) : ℝ := lo + e * label.2.val

def ValidBufferedIndex (M : ℕ → ℝ) (lo hi e : ℝ) (n : ℕ)
    (label : BufferedIndex lo hi e n) : Prop :=
  lo ≤ label.center ∧ label.center ≤ hi ∧
  label.center ≤ M label.1.val ∧ M label.1.val < label.center + e ∧
    M (label.1.val + 1) < label.center + 2 * e

theorem exists_validBufferedIndex (M : ℕ → ℝ) {lo hi e : ℝ}
    (he : 0 < e) (n : ℕ)
    (hrange : ∀ i ≤ n + 1, lo ≤ M i ∧ M i ≤ hi)
    (hwidth : hi - lo ≤ (n + 1 : ℕ) * e) :
    ∃ label : BufferedIndex lo hi e n, ValidBufferedIndex M lo hi e n label := by
  obtain ⟨i, k, hi, hk, hlo, hhi, hcur, hcur', hnext⟩ :=
    exists_buffered_grid M he n hrange hwidth
  refine ⟨(⟨i, by omega⟩, ⟨k, by omega⟩), ?_⟩
  exact ⟨hlo, hhi, hcur, hcur', hnext⟩

def chooseBufferedIndex (M : ℕ → ℝ) {lo hi e : ℝ}
    (he : 0 < e) (n : ℕ)
    (hrange : ∀ i ≤ n + 1, lo ≤ M i ∧ M i ≤ hi)
    (hwidth : hi - lo ≤ (n + 1 : ℕ) * e) : BufferedIndex lo hi e n :=
  Classical.choose (exists_validBufferedIndex M he n hrange hwidth)

theorem chooseBufferedIndex_spec (M : ℕ → ℝ) {lo hi e : ℝ}
    (he : 0 < e) (n : ℕ)
    (hrange : ∀ i ≤ n + 1, lo ≤ M i ∧ M i ≤ hi)
    (hwidth : hi - lo ≤ (n + 1 : ℕ) * e) :
    ValidBufferedIndex M lo hi e n (chooseBufferedIndex M he n hrange hwidth) :=
  Classical.choose_spec (exists_validBufferedIndex M he n hrange hwidth)

@[simp] theorem card_bufferedIndex (lo hi e : ℝ) (n : ℕ) :
    Fintype.card (BufferedIndex lo hi e n) =
      (n + 1) * (⌊(hi - lo) / e⌋₊ + 1) := by
  simp only [BufferedIndex, Fintype.card_prod, Fintype.card_fin]

variable {Row Label : Type*} [Fintype Label]

def selectedRows (rows : Finset Row) (select : Row → Label) (label : Label) : Finset Row :=
  rows.filter fun u => select u = label

theorem selectedRows_subset (rows : Finset Row) (select : Row → Label) (label : Label) :
    selectedRows rows select label ⊆ rows := Finset.filter_subset _ _

theorem mem_selectedRows (rows : Finset Row) (select : Row → Label)
    (label : Label) (u : Row) :
    u ∈ selectedRows rows select label ↔ u ∈ rows ∧ select u = label := by
  simp only [selectedRows, Finset.mem_filter]

theorem selectedRows_cover (rows : Finset Row) (select : Row → Label) :
    ∀ u ∈ rows, ∃ label, u ∈ selectedRows rows select label := by
  intro u hu
  exact ⟨select u, (mem_selectedRows rows select (select u) u).mpr ⟨hu, rfl⟩⟩

theorem selectedRows_disjoint (rows : Finset Row) (select : Row → Label)
    {label label' : Label} (h : label ≠ label') :
    Disjoint (selectedRows rows select label) (selectedRows rows select label') := by
  apply Finset.disjoint_left.mpr
  intro u hu hu'
  exact h (((mem_selectedRows rows select label u).mp hu).2.symm.trans
    ((mem_selectedRows rows select label' u).mp hu').2)

/-- The fixed selected bins, unlike the wide cover, reconstruct the row sum
with coefficient exactly one. -/
theorem sum_selectedRows (rows : Finset Row) (select : Row → Label) (value : Row → ℂ) :
    (∑ label, ∑ u ∈ selectedRows rows select label, value u) =
      ∑ u ∈ rows, value u := by
  simp only [selectedRows, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  simp

/-- Every selected fixed bin retains any property satisfied by its chosen
wide bin; the later analytic estimates can therefore use that wide-bin bound. -/
theorem selectedRows_valid (rows : Finset Row) (select : Row → Label)
    (good : Row → Label → Prop)
    (hselect : ∀ u ∈ rows, good u (select u)) (label : Label) :
    ∀ u ∈ selectedRows rows select label, good u label := by
  intro u hu
  obtain ⟨hur, heq⟩ := (mem_selectedRows rows select label u).mp hu
  simpa only [← heq] using hselect u hur

end Expansion
