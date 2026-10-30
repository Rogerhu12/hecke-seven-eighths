import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The common real-zero boundary of an entire family

`zeros i` is an arbitrary set of real parts of zeros of the family member `i`.
No arithmetic or analytic assertion about Hecke L-functions is made here.
The baseline and clipping agree with `eq-common-B` in the source manuscript.
In particular, `familySupremum` always ranges over the entire index type.
-/

namespace HeckeGeneral.Analysis

noncomputable section

variable {ι : Type*}

/-- The common set of zero real parts, with the manuscript's baseline and clipping. -/
def familyZeroSet (zeros : ι → Set ℝ) : Set ℝ :=
  {r | r = 1 / 2 ∨ ∃ i, r ∈ zeros i ∧ 1 / 2 ≤ r ∧ r ≤ 1}

/-- The supremum is over the entire family, never over one selected member. -/
def familySupremum (zeros : ι → Set ℝ) : ℝ := sSup (familyZeroSet zeros)

theorem baseline_mem_familyZeroSet (zeros : ι → Set ℝ) :
    (1 / 2 : ℝ) ∈ familyZeroSet zeros := Or.inl rfl

theorem familyZeroSet_nonempty (zeros : ι → Set ℝ) :
    (familyZeroSet zeros).Nonempty := ⟨1 / 2, baseline_mem_familyZeroSet zeros⟩

theorem familyZeroSet_bddAbove (zeros : ι → Set ℝ) :
    BddAbove (familyZeroSet zeros) := by
  refine ⟨1, ?_⟩
  intro r hr
  rcases hr with hr | ⟨i, hi, hlo, hhi⟩
  · rw [hr]
    norm_num
  · exact hhi

theorem baseline_le_familySupremum (zeros : ι → Set ℝ) :
    (1 / 2 : ℝ) ≤ familySupremum zeros :=
  le_csSup (familyZeroSet_bddAbove zeros) (baseline_mem_familyZeroSet zeros)

theorem zero_le_familySupremum (zeros : ι → Set ℝ) {i : ι} {r : ℝ}
    (hr : r ∈ zeros i) (hlo : 1 / 2 ≤ r) (hhi : r ≤ 1) :
    r ≤ familySupremum zeros :=
  le_csSup (familyZeroSet_bddAbove zeros) (Or.inr ⟨i, hr, hlo, hhi⟩)

theorem familySupremum_le_of_common_bound (zeros : ι → Set ℝ) {b : ℝ}
    (hbaseline : 1 / 2 ≤ b)
    (hbound : ∀ i r, r ∈ zeros i → 1 / 2 ≤ r → r ≤ 1 → r ≤ b) :
    familySupremum zeros ≤ b := by
  apply csSup_le (familyZeroSet_nonempty zeros)
  intro r hr
  rcases hr with hr | ⟨i, hi, hlo, hhi⟩
  · simpa only [hr] using hbaseline
  · exact hbound i r hi hlo hhi

/-- This parameter is the analytic seed conclusion, not its analytic proof. -/
def SeedBound (zeros : ι → Set ℝ) : Prop :=
  ∀ i r, r ∈ zeros i → r ≤ 11 / 12

theorem familySupremum_le_seed (zeros : ι → Set ℝ) (hseed : SeedBound zeros) :
    familySupremum zeros ≤ 11 / 12 := by
  apply familySupremum_le_of_common_bound zeros (by norm_num)
  intro i r hr _ _
  exact hseed i r hr

/-- An approximate supremum witness belongs to some member of the same family. -/
theorem exists_family_zero_above (zeros : ι → Set ℝ) {a : ℝ}
    (hbaseline : 1 / 2 ≤ a) (ha : a < familySupremum zeros) :
    ∃ i r, r ∈ zeros i ∧ 1 / 2 ≤ r ∧ r ≤ 1 ∧ a < r := by
  classical
  by_contra hnone
  have hbound : familySupremum zeros ≤ a := by
    apply familySupremum_le_of_common_bound zeros hbaseline
    intro i r hr hlo hhi
    exact le_of_not_gt (fun har => hnone ⟨i, r, hr, hlo, hhi, har⟩)
  exact (not_le_of_gt ha) hbound

end

end HeckeGeneral.Analysis
