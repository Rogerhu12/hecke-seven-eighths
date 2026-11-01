import HeckeSkeleton.HighBinSupport.DyadicShells
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The finite dyadic schedule is attached to literal source rows.  A row at
an exact dyadic endpoint belongs to the preceding shell.  The source set
is retained as a mask, so the final shell never adds rows beyond the
original upper cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinVerified.Dyadic

open scoped BigOperators

variable {Row : Type*} [DecidableEq Row]

/-- A deterministic dyadic fiber of a fixed finite source set. -/
def shellFiber (norm : Row → ℝ) (R : Finset Row) (Z lower upper : ℝ)
    (j : Fin (shellCount Z lower upper)) : Finset Row :=
  R.filter fun u => dyadicIndex (norm u / Z ^ lower) = j.val

theorem shellFiber_subset (norm : Row → ℝ) (R : Finset Row) (Z lower upper : ℝ)
    (j : Fin (shellCount Z lower upper)) : shellFiber norm R Z lower upper j ⊆ R :=
  Finset.filter_subset _ _

theorem shellFiber_disjoint (norm : Row → ℝ) (R : Finset Row) (Z lower upper : ℝ)
    {i j : Fin (shellCount Z lower upper)} (hij : i ≠ j) :
    Disjoint (shellFiber norm R Z lower upper i) (shellFiber norm R Z lower upper j) := by
  apply Finset.disjoint_left.mpr
  intro u hi hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact hij (Fin.ext (hi'.symm.trans hj'))

theorem shellFiber_covers (norm : Row → ℝ) (R : Finset Row) {Z lower upper : ℝ}
    (hZ : 1 < Z)
    (hR : ∀ u ∈ R, Z ^ lower < norm u ∧ norm u ≤ Z ^ upper)
    (u : Row) (hu : u ∈ R) :
    ∃ j : Fin (shellCount Z lower upper), u ∈ shellFiber norm R Z lower upper j := by
  let j := actualShellIndex Z lower upper (norm u) hZ (hR u hu).1 (hR u hu).2
  exact ⟨j, Finset.mem_filter.mpr ⟨hu, rfl⟩⟩

theorem shellFiber_bounds (norm : Row → ℝ) (R : Finset Row) {Z lower upper : ℝ}
    (hZ : 1 < Z)
    (hR : ∀ u ∈ R, Z ^ lower < norm u ∧ norm u ≤ Z ^ upper)
    (j : Fin (shellCount Z lower upper)) (u : Row)
    (hu : u ∈ shellFiber norm R Z lower upper j) :
    Z ^ shellExponent Z lower j.val < norm u ∧
      norm u ≤ 2 * Z ^ shellExponent Z lower j.val := by
  obtain ⟨huR, hindex⟩ := Finset.mem_filter.mp hu
  have hspec := actualShellIndex_spec Z lower upper (norm u) hZ
    (hR u huR).1 (hR u huR).2
  change _ ∧ _ ∧ Z ^ shellExponent Z lower (dyadicIndex (norm u / Z ^ lower)) < norm u ∧
    norm u ≤ 2 * Z ^ shellExponent Z lower (dyadicIndex (norm u / Z ^ lower)) at hspec
  rw [hindex] at hspec
  exact hspec.2.2

/-- For source rows within the cutoffs, the deterministic fiber is
exactly the masked annulus, including both endpoint conventions. -/
theorem shellFiber_eq_annulus (norm : Row → ℝ) (R : Finset Row) {Z lower upper : ℝ}
    (hZ : 1 < Z)
    (hR : ∀ u ∈ R, Z ^ lower < norm u ∧ norm u ≤ Z ^ upper)
    (j : Fin (shellCount Z lower upper)) :
    shellFiber norm R Z lower upper j = R.filter fun u =>
      Z ^ shellExponent Z lower j.val < norm u ∧
        norm u ≤ 2 * Z ^ shellExponent Z lower j.val := by
  ext u
  constructor
  · intro hu
    exact Finset.mem_filter.mpr ⟨shellFiber_subset norm R Z lower upper j hu,
      shellFiber_bounds norm R hZ hR j u hu⟩
  · intro hu
    obtain ⟨huR, hlo, hhi⟩ := Finset.mem_filter.mp hu
    apply Finset.mem_filter.mpr
    refine ⟨huR, ?_⟩
    have hbase : 0 < Z ^ lower := Real.rpow_pos_of_pos (by linarith) _
    have hactual := dyadicShell_bounds hbase (hR u huR).1
    have hj : Z ^ lower * (2 : ℝ) ^ j.val < norm u ∧
        norm u ≤ Z ^ lower * (2 : ℝ) ^ (j.val + 1) := by
      rw [shellExponent_identity hZ] at hlo hhi
      refine ⟨hlo, ?_⟩
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hhi
    exact dyadicShell_unique hbase hactual hj

/-- The genuine shell sum contains every source row exactly once. -/
theorem sum_shellFiber {M : Type*} [AddCommMonoid M]
    (norm : Row → ℝ) (R : Finset Row) {Z lower upper : ℝ} (hZ : 1 < Z)
    (hR : ∀ u ∈ R, Z ^ lower < norm u ∧ norm u ≤ Z ^ upper)
    (f : Row → M) :
    (∑ j : Fin (shellCount Z lower upper),
      ∑ u ∈ shellFiber norm R Z lower upper j, f u) = ∑ u ∈ R, f u := by
  simp only [shellFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  let j := actualShellIndex Z lower upper (norm u) hZ (hR u hu).1 (hR u hu).2
  have hindex : ∀ k : Fin (shellCount Z lower upper),
      dyadicIndex (norm u / Z ^ lower) = k.val ↔ k = j := by
    intro k
    constructor
    · intro h
      apply Fin.ext
      exact h.symm
    · intro h
      subst k
      rfl
  simp only [hindex, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end HighBinVerified.Dyadic
