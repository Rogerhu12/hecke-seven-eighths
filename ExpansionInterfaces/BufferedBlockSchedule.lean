import ExpansionInterfaces.DyadicShells
import ExpansionInterfaces.BufferedHeights
import Expansion.SelectedBufferedRows
import Mathlib.Data.Fintype.BigOperators

/-!
# The actual finite shell and buffered-index schedule

This bridges the explicit shell count to the buffered indices constructed
by `Expansion.SelectedBufferedRows`.  Its row sets are always clipped by
one global retained set.  In particular, the final dyadic shell cannot
reintroduce rows above the global large-row cutoff.
-/

noncomputable section
namespace ExpansionInterfaces
open scoped Classical BigOperators

/-- Definitionally the arithmetic adapter's `RowBufferIndex`. -/
abbrev BufferedChoices (B e : ℝ) :=
  Expansion.BufferedIndex (51 / 100) B e (Nat.ceil ((B - 51 / 100) / e))

abbrev BufferedBlockSchedule (Z lower upper B e : ℝ) :=
  RetainedBlockSchedule (BufferedChoices B e) Z lower upper

theorem card_bufferedBlockSchedule (Z lower upper B e : ℝ) :
    Fintype.card (BufferedBlockSchedule Z lower upper B e) =
      shellCount Z lower upper *
        ((Nat.ceil ((B - 51 / 100) / e) + 1) *
          (Nat.floor ((B - 51 / 100) / e) + 1)) := by
  rw [card_retainedBlockSchedule]
  rw [Expansion.card_bufferedIndex]

/-- The exact EX-BLOCK-COUNT form, with no factor involving T. -/
theorem bufferedBlockSchedule_subpower {Z lower upper B e η : ℝ}
    (hZ : 1 ≤ Z) (hlu : lower ≤ upper) (hη : 0 < η) :
    (Fintype.card (BufferedBlockSchedule Z lower upper B e) : ℝ) ≤
      ((((Nat.ceil ((B - 51 / 100) / e) + 1) *
          (Nat.floor ((B - 51 / 100) / e) + 1) : ℕ) : ℝ) *
        (2 + ((upper - lower) / Real.log 2) / η)) * Z ^ η := by
  simpa only [BufferedBlockSchedule, BufferedChoices, Expansion.card_bufferedIndex] using
    retainedBlockSchedule_subpower (BufferedChoices B e) hZ hlu hη

/-- Every index, including one whose row set is empty, has a legal bin center. -/
theorem bufferedChoices_center_bounds {B e : ℝ} (hB : (51 / 100 : ℝ) ≤ B)
    (he : 0 < e) (b : BufferedChoices B e) :
    51 / 100 ≤ b.center ∧ b.center ≤ B := by
  have hquot : 0 ≤ (B - 51 / 100) / e := div_nonneg (sub_nonneg.mpr hB) he.le
  have hk : b.2.val ≤ Nat.floor ((B - 51 / 100) / e) := by
    have hlt := b.2.isLt
    omega
  have hkcast : (b.2.val : ℝ) ≤ (Nat.floor ((B - 51 / 100) / e) : ℝ) := by
    exact_mod_cast hk
  have hkr : (b.2.val : ℝ) ≤ (B - 51 / 100) / e :=
    hkcast.trans (Nat.floor_le hquot)
  have hmul := (le_div_iff₀ he).mp hkr
  have hnonneg : 0 ≤ e * (b.2.val : ℝ) := mul_nonneg he.le (Nat.cast_nonneg _)
  unfold Expansion.BufferedIndex.center
  constructor <;> nlinarith

theorem bufferedChoices_height_bounds {B e T : ℝ} (hT : 0 ≤ T)
    (b : BufferedChoices B e) :
    let N := Nat.ceil ((B - 51 / 100) / e) + 1
    let i := b.1.val + 1
    0 ≤ selectedHeight i T ∧ 0 ≤ upperHeight i T ∧ 0 ≤ contourHeight T ∧
      selectedHeight i T ≤ 3 * (N + 1 : ℝ) * (1 + T) ∧
      upperHeight i T ≤ 3 * (N + 1 : ℝ) * (1 + T) ∧
      contourHeight T ≤ 3 * (N + 1 : ℝ) * (1 + T) := by
  apply buffered_heights_bound _ _ ?_ T hT
  have hlt := b.1.isLt
  omega

variable {Row : Type*}

/-- The global range is applied before dyadic or buffered selection. -/
def globalRetainedRows (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper : ℝ) : Finset Row :=
  rows.filter fun u => Z ^ lower < norm u ∧ norm u ≤ Z ^ upper

def clippedShellRows (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper : ℝ) (j : Fin (shellCount Z lower upper)) : Finset Row :=
  (globalRetainedRows rows norm Z lower upper).filter fun u =>
    Z ^ shellExponent Z lower j.val < norm u ∧
      norm u ≤ 2 * Z ^ shellExponent Z lower j.val

theorem clippedShellRows_subset_global (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper : ℝ) (j : Fin (shellCount Z lower upper)) :
    clippedShellRows rows norm Z lower upper j ⊆
      globalRetainedRows rows norm Z lower upper := Finset.filter_subset _ _

theorem clippedShellRows_norm_bounds (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper : ℝ) (j : Fin (shellCount Z lower upper))
    {u : Row} (hu : u ∈ clippedShellRows rows norm Z lower upper j) :
    Z ^ shellExponent Z lower j.val < norm u ∧
      norm u ≤ 2 * Z ^ shellExponent Z lower j.val ∧ norm u ≤ Z ^ upper := by
  obtain ⟨hg, hlo, hhi⟩ := Finset.mem_filter.mp hu
  exact ⟨hlo, hhi, (Finset.mem_filter.mp hg).2.2⟩

theorem shellIndex_unique {Z lower r : ℝ} (hZ : 1 < Z) {i j : ℕ}
    (hi : Z ^ shellExponent Z lower i < r ∧ r ≤ 2 * Z ^ shellExponent Z lower i)
    (hj : Z ^ shellExponent Z lower j < r ∧ r ≤ 2 * Z ^ shellExponent Z lower j) :
    i = j := by
  apply dyadicShell_unique (Real.rpow_pos_of_pos (by linarith : 0 < Z) lower)
  · simpa only [shellExponent_identity hZ, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hi
  · simpa only [shellExponent_identity hZ, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hj

/-- The final shell is clipped; the exact sum stops at Z^upper. -/
theorem sum_clippedShellRows (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper : ℝ) (hZ : 1 < Z) (value : Row → ℂ) :
    (∑ j : Fin (shellCount Z lower upper),
      ∑ u ∈ clippedShellRows rows norm Z lower upper j, value u) =
      ∑ u ∈ globalRetainedRows rows norm Z lower upper, value u := by
  simp only [clippedShellRows, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  have hur := (Finset.mem_filter.mp hu).2
  let j₀ := actualShellIndex Z lower upper (norm u) hZ hur.1 hur.2
  have hj₀ : Z ^ shellExponent Z lower j₀.val < norm u ∧
      norm u ≤ 2 * Z ^ shellExponent Z lower j₀.val :=
    (actualShellIndex_spec Z lower upper (norm u) hZ hur.1 hur.2).2.2
  have htest : ∀ j : Fin (shellCount Z lower upper),
      (Z ^ shellExponent Z lower j.val < norm u ∧
        norm u ≤ 2 * Z ^ shellExponent Z lower j.val) ↔ j = j₀ := by
    intro j
    constructor
    · intro hj
      exact Fin.ext (shellIndex_unique hZ hj hj₀)
    · intro hj
      simpa only [hj] using hj₀
  simp_rw [htest]
  simp

def clippedBufferedRows (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper B e : ℝ) (select : Row → BufferedChoices B e)
    (b : BufferedBlockSchedule Z lower upper B e) : Finset Row :=
  Expansion.selectedRows (clippedShellRows rows norm Z lower upper b.1) select b.2

theorem clippedBufferedRows_subset_global (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper B e : ℝ) (select : Row → BufferedChoices B e)
    (b : BufferedBlockSchedule Z lower upper B e) :
    clippedBufferedRows rows norm Z lower upper B e select b ⊆
      globalRetainedRows rows norm Z lower upper :=
  (Expansion.selectedRows_subset _ _ _).trans
    (clippedShellRows_subset_global rows norm Z lower upper b.1)

theorem sum_clippedBufferedRows (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper B e : ℝ) (hZ : 1 < Z) (select : Row → BufferedChoices B e)
    (value : Row → ℂ) :
    (∑ b : BufferedBlockSchedule Z lower upper B e,
      ∑ u ∈ clippedBufferedRows rows norm Z lower upper B e select b, value u) =
      ∑ u ∈ globalRetainedRows rows norm Z lower upper, value u := by
  unfold clippedBufferedRows
  rw [Fintype.sum_prod_type]
  simp_rw [Expansion.sum_selectedRows]
  exact sum_clippedShellRows rows norm Z lower upper hZ value

theorem clippedBufferedRows_disjoint (rows : Finset Row) (norm : Row → ℝ)
    (Z lower upper B e : ℝ) (hZ : 1 < Z) (select : Row → BufferedChoices B e)
    {b b' : BufferedBlockSchedule Z lower upper B e} (hne : b ≠ b') :
    Disjoint (clippedBufferedRows rows norm Z lower upper B e select b)
      (clippedBufferedRows rows norm Z lower upper B e select b') := by
  apply Finset.disjoint_left.mpr
  intro u hu hu'
  obtain ⟨hs, hb⟩ := (Expansion.mem_selectedRows _ _ b.2 u).mp hu
  obtain ⟨hs', hb'⟩ := (Expansion.mem_selectedRows _ _ b'.2 u).mp hu'
  have hi : b.1 = b'.1 := Fin.ext
    (shellIndex_unique hZ (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp hs').2)
  exact hne (Prod.ext hi (hb.symm.trans hb'))

end ExpansionInterfaces

#print axioms ExpansionInterfaces.bufferedBlockSchedule_subpower
#print axioms ExpansionInterfaces.sum_clippedBufferedRows
#print axioms ExpansionInterfaces.clippedBufferedRows_disjoint
