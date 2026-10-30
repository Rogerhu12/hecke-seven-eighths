import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination

/-!
Whole-slot selection for prime amplitudes (Q 15116--15134).

Slots have positive lengths `w i` and amplitudes `0 ≤ g i ≤ gmax`, with
length-weighted mean `q`.  For a requested length `0 ≤ z ≤ ∑ w`, some set of
positive-amplitude slots has total length at most `z` and gain at least
`q z - gmax * wmax`: fill greedily by decreasing amplitude and drop the one
possibly fractional slot.  This is pure combinatorics; no analytic input.
-/

namespace HeckeGeneral.Analysis

open scoped BigOperators

/-- Strong-induction form of `exists_slot_selection`: take a slot of maximal
amplitude and recurse on the remaining slots with the remaining length. -/
private theorem exists_slot_selection_aux {ι : Type*} [DecidableEq ι] (w g : ι → ℝ)
    {gmax wmax : ℝ} (hgmax : 0 ≤ gmax) (hwmax0 : 0 ≤ wmax) (s : Finset ι) :
    ∀ q z : ℝ, (∀ i ∈ s, 0 < w i) → (∀ i ∈ s, 0 ≤ g i) → (∀ i ∈ s, g i ≤ gmax) →
      (∀ i ∈ s, w i ≤ wmax) → q * ∑ i ∈ s, w i = ∑ i ∈ s, w i * g i →
      0 ≤ z → z ≤ ∑ i ∈ s, w i →
      ∃ I ⊆ s, (∀ i ∈ I, 0 < g i) ∧ ∑ i ∈ I, w i ≤ z ∧
        q * z - gmax * wmax ≤ ∑ i ∈ I, w i * g i := by
  induction s using Finset.strongInduction with
  | H s ih =>
    intro q z hw hg0 hg hwmax hq hz0 hzW
    have hloss : 0 ≤ gmax * wmax := mul_nonneg hgmax hwmax0
    -- The empty selection works as soon as `q * z ≤ gmax * wmax`.
    have hempty : q * z ≤ gmax * wmax →
        ∃ I ⊆ s, (∀ i ∈ I, 0 < g i) ∧ ∑ i ∈ I, w i ≤ z ∧
          q * z - gmax * wmax ≤ ∑ i ∈ I, w i * g i := by
      intro h
      refine ⟨∅, Finset.empty_subset _, by simp, by simpa using hz0, ?_⟩
      rw [Finset.sum_empty]
      linarith
    rcases s.eq_empty_or_nonempty with hs | hs
    · apply hempty
      subst hs
      rw [Finset.sum_empty] at hzW
      have hz : z = 0 := le_antisymm hzW hz0
      rw [hz, mul_zero]
      exact hloss
    obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image g hs
    have hW : 0 < ∑ i ∈ s, w i := Finset.sum_pos hw hs
    have hSle : ∑ i ∈ s, w i * g i ≤ (∑ i ∈ s, w i) * g i₀ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hmax i hi) (hw i hi).le
    -- The mean is at most the maximal amplitude.
    have hqg : q ≤ g i₀ := by
      by_contra hcon
      have := mul_lt_mul_of_pos_left (not_le.mp hcon) hW
      linarith
    by_cases hz : z < w i₀
    · -- The request is shorter than the top slot: select nothing.
      apply hempty
      have h1 : q * z ≤ g i₀ * z := mul_le_mul_of_nonneg_right hqg hz0
      have h2 : g i₀ * z ≤ g i₀ * w i₀ := mul_le_mul_of_nonneg_left hz.le (hg0 i₀ hi₀)
      have h3 : g i₀ * w i₀ ≤ gmax * wmax :=
        mul_le_mul (hg i₀ hi₀) (hwmax i₀ hi₀) (hw i₀ hi₀).le hgmax
      linarith
    replace hz : w i₀ ≤ z := not_lt.mp hz
    by_cases hgpos : 0 < g i₀
    swap
    · -- All amplitudes vanish: select nothing.
      apply hempty
      have h1 : q * z ≤ 0 * z :=
        mul_le_mul_of_nonneg_right (hqg.trans (not_lt.mp hgpos)) hz0
      linarith
    -- Take the top slot `i₀` and recurse on the remaining slots.
    have hmem : ∀ {i}, i ∈ s.erase i₀ → i ∈ s := fun h => Finset.mem_of_mem_erase h
    have hWsplit : ∑ i ∈ s, w i = w i₀ + ∑ i ∈ s.erase i₀, w i :=
      (Finset.add_sum_erase s w hi₀).symm
    have hSsplit : ∑ i ∈ s, w i * g i = w i₀ * g i₀ + ∑ i ∈ s.erase i₀, w i * g i :=
      (Finset.add_sum_erase s (fun i => w i * g i) hi₀).symm
    have hW'0 : 0 ≤ ∑ i ∈ s.erase i₀, w i :=
      Finset.sum_nonneg fun i hi => (hw i (hmem hi)).le
    have hS'le : ∑ i ∈ s.erase i₀, w i * g i ≤ (∑ i ∈ s.erase i₀, w i) * g i₀ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hmax i (hmem hi)) (hw i (hmem hi)).le
    have hS'0 : 0 ≤ ∑ i ∈ s.erase i₀, w i * g i :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hw i (hmem hi)).le (hg0 i (hmem hi))
    obtain ⟨q', hq'def⟩ : ∃ q' : ℝ,
        q' = (∑ i ∈ s.erase i₀, w i * g i) / ∑ i ∈ s.erase i₀, w i := ⟨_, rfl⟩
    have hq' : q' * ∑ i ∈ s.erase i₀, w i = ∑ i ∈ s.erase i₀, w i * g i := by
      rcases hW'0.lt_or_eq with hpos | hzero
      · rw [hq'def]
        exact div_mul_cancel₀ _ hpos.ne'
      · have h0 : ∑ i ∈ s.erase i₀, w i * g i ≤ 0 := by
          have h := hS'le
          rw [← hzero, zero_mul] at h
          exact h
        rw [← hzero, mul_zero]
        linarith
    have hq'g : q' ≤ g i₀ := by
      rcases hW'0.lt_or_eq with hpos | hzero
      · rw [hq'def, div_le_iff₀ hpos]
        linarith
      · rw [hq'def, ← hzero, div_zero]
        exact hg0 i₀ hi₀
    obtain ⟨I', hI's, hI'g, hI'w, hI'gain⟩ :=
      ih (s.erase i₀) (Finset.erase_ssubset hi₀) q' (z - w i₀)
        (fun i hi => hw i (hmem hi)) (fun i hi => hg0 i (hmem hi))
        (fun i hi => hg i (hmem hi)) (fun i hi => hwmax i (hmem hi)) hq'
        (by linarith) (by linarith)
    have hnot : i₀ ∉ I' := fun h => Finset.notMem_erase i₀ s (hI's h)
    refine ⟨insert i₀ I', Finset.insert_subset hi₀ (hI's.trans (Finset.erase_subset i₀ s)),
      ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with h | h
      · rw [h]
        exact hgpos
      · exact hI'g i h
    · rw [Finset.sum_insert hnot]
      linarith
    · rw [Finset.sum_insert hnot]
      -- Removing the top slot does not lower the mean gain per unit length:
      -- `W (q z - (w₀ g₀ + q' (z - w₀))) = w₀ (g₀ - q') (z - W) ≤ 0`.
      have hqW : q * ∑ i ∈ s, w i = w i₀ * g i₀ + q' * ∑ i ∈ s.erase i₀, w i := by
        rw [hq, hSsplit, hq']
      have key : (∑ i ∈ s, w i) * (q * z - (w i₀ * g i₀ + q' * (z - w i₀))) =
          w i₀ * (g i₀ - q') * (z - ∑ i ∈ s, w i) := by
        linear_combination z * hqW - q' * z * hWsplit
      have hneg : w i₀ * (g i₀ - q') * (z - ∑ i ∈ s, w i) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw i₀ hi₀).le (sub_nonneg.mpr hq'g))
          (by linarith)
      have hkey : q * z - (w i₀ * g i₀ + q' * (z - w i₀)) ≤ 0 := by
        by_contra hcon
        have := mul_pos hW (not_le.mp hcon)
        linarith
      linarith

/-- Greedy whole-slot selection with an explicit one-slot rounding loss. -/
theorem exists_slot_selection {ι : Type*} [DecidableEq ι] (s : Finset ι) (w g : ι → ℝ)
    {q gmax wmax z : ℝ}
    (hw : ∀ i ∈ s, 0 < w i) (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg : ∀ i ∈ s, g i ≤ gmax)
    (hwmax : ∀ i ∈ s, w i ≤ wmax) (hgmax : 0 ≤ gmax) (hwmax0 : 0 ≤ wmax)
    (hq : q * ∑ i ∈ s, w i = ∑ i ∈ s, w i * g i)
    (hz0 : 0 ≤ z) (hzW : z ≤ ∑ i ∈ s, w i) :
    ∃ I ⊆ s, (∀ i ∈ I, 0 < g i) ∧ ∑ i ∈ I, w i ≤ z ∧
      q * z - gmax * wmax ≤ ∑ i ∈ I, w i * g i :=
  exists_slot_selection_aux w g hgmax hwmax0 s q z hw hg0 hg hwmax hq hz0 hzW

end HeckeGeneral.Analysis
