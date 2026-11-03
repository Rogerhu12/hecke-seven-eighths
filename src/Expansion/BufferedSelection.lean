import Expansion.MeromorphicZeros
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity

/-!
The finite buffered-bin argument, with no assumptions about the arithmetic
field.  The selected-zero height and the next, upper-zero height are distinct.
This module constructs the indices; a preselected bin is not an input.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion
open scoped Classical

theorem exists_small_increment (M : ℕ → ℝ) (lo hi e : ℝ) (n : ℕ)
    (hlo : lo ≤ M 0) (hhi : M (n + 1) ≤ hi)
    (hwidth : hi - lo ≤ (n + 1 : ℕ) * e) :
    ∃ i : ℕ, i ≤ n ∧ M (i + 1) ≤ M i + e := by
  by_contra hn
  have hstep : ∀ i ≤ n, M i + e < M (i + 1) := by
    intro i hi
    exact lt_of_not_ge (fun h => hn ⟨i, hi, h⟩)
  have hgrow : ∀ k : ℕ, k ≤ n + 1 → lo + k * e ≤ M k := by
    intro k
    induction k with
    | zero => simpa using hlo
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hnext := hstep k (by omega)
      push_cast
      linarith
  have hprev := hgrow n (by omega)
  have hlast := hstep n le_rfl
  push_cast at hwidth
  nlinarith

/-- One finite grid works for every possible sequence of maxima. -/
theorem exists_buffered_grid (M : ℕ → ℝ) {lo hi e : ℝ}
    (he : 0 < e) (n : ℕ)
    (hrange : ∀ i ≤ n + 1, lo ≤ M i ∧ M i ≤ hi)
    (hwidth : hi - lo ≤ (n + 1 : ℕ) * e) :
    ∃ i k : ℕ, i ≤ n ∧ k ≤ ⌊(hi - lo) / e⌋₊ ∧
      let a := lo + e * k
      lo ≤ a ∧ a ≤ hi ∧ a ≤ M i ∧ M i < a + e ∧
        M (i + 1) < a + 2 * e := by
  obtain ⟨i, hi, hstep⟩ := exists_small_increment M lo hi e n
    (hrange 0 (by omega)).1 (hrange (n + 1) le_rfl).2 hwidth
  have hMi := hrange i (by omega)
  let k : ℕ := ⌊(M i - lo) / e⌋₊
  have hquot : 0 ≤ (M i - lo) / e := div_nonneg (sub_nonneg.mpr hMi.1) he.le
  have hklo : (k : ℝ) ≤ (M i - lo) / e := Nat.floor_le hquot
  have hkhi : (M i - lo) / e < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hleft : lo + e * k ≤ M i := by
    have h := (le_div_iff₀ he).mp hklo
    nlinarith
  have hright : M i < lo + e * k + e := by
    have h := (div_lt_iff₀ he).mp hkhi
    nlinarith
  refine ⟨i, k, hi, ?_, ?_⟩
  · exact Nat.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right hMi.2 lo) he.le)
  · dsimp
    exact ⟨le_add_of_nonneg_right (mul_nonneg he.le (Nat.cast_nonneg _)),
      hleft.trans hMi.2, hleft, hright, by linarith⟩

variable {ι : Type*} [Fintype ι]

/-- A genuine zero is selected in the current-height rectangle whenever the
chosen bin lies above the floor.  Every zero at the next height lies below
the buffer.  A common boundary `B` may equal one. -/
theorem MeromorphicFamily.exists_buffered_zero_bin (F : MeromorphicFamily ι)
    {lo B e T : ℝ} (hloB : lo ≤ B) (hB : B ≤ 1) (he : 0 < e)
    (n : ℕ) (hwidth : B - lo ≤ (n + 1 : ℕ) * e)
    (hboundary : ∀ j s, lo ≤ s.re → s.re ≤ 1 →
      0 < meromorphicOrderAt (F.function j) s → s.re ≤ B) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n + 1 ∧ k ≤ ⌊(B - lo) / e⌋₊ ∧
      let a := lo + e * k
      lo ≤ a ∧ a ≤ B ∧
      (lo < a → ∃ j s, 0 < meromorphicOrderAt (F.function j) s ∧
        a ≤ s.re ∧ s.re < a + e ∧ |s.im| ≤ 3 * i * T) ∧
      (∀ j s, lo ≤ s.re → s.re ≤ 1 →
        |s.im| ≤ 3 * (i + 1 : ℕ) * T →
        0 < meromorphicOrderAt (F.function j) s → s.re < a + 2 * e) := by
  let M : ℕ → ℝ := fun j => F.maximum lo 1 (3 * (j + 1 : ℕ) * T)
  have hrange : ∀ j ≤ n + 1, lo ≤ M j ∧ M j ≤ B := by
    intro j _
    refine ⟨(F.maximum_bounds (hloB.trans hB) _).1, ?_⟩
    exact F.maximum_le_boundary hloB (fun i s hs hs' _ hz => hboundary i s hs hs' hz)
  obtain ⟨i, k, hi, hk, ha0, haB, hcur, hcur', hnext⟩ :=
    exists_buffered_grid M he n hrange hwidth
  refine ⟨i + 1, k, by omega, by omega, hk, ha0, haB, ?_, ?_⟩
  · intro ha
    obtain ⟨j, s, hz, ht, hs, _, _⟩ :=
      F.maximum_attained (lt_of_lt_of_le ha hcur)
    exact ⟨j, s, hz, by simpa only [hs] using hcur,
      by simpa only [hs] using hcur', ht⟩
  · intro j s hlo hhi ht hz
    exact (F.zero_re_le_maximum hlo hhi ht hz).trans_lt hnext

/-- Finite real choices can be fixed uniformly before all height parameters. -/
theorem explicit_buffered_width {lo B e : ℝ} (he : 0 < e) :
    B - lo ≤ (⌈(B - lo) / e⌉₊ + 1 : ℕ) * e := by
  have h := Nat.le_ceil ((B - lo) / e)
  have h' : (B - lo) / e ≤ (⌈(B - lo) / e⌉₊ + 1 : ℕ) := by
    exact h.trans (by push_cast; linarith)
  exact (div_le_iff₀ he).mp h'

end Expansion
