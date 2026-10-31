import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Zero-extended sextic phase separation

These identities are the five cross-couplings in the proof of the
separated marked expansion.  They explicitly include the zero case;
nonzero character values are sixth roots of unity.  In particular the
row--mark and mark--cube interactions give coprimality masks, rather
than being cancelled to `1` at a zero of the residue symbol.

The file uses only Mathlib.  Instantiation with the project's actual
sextic residue evaluations requires their sixth-root/zero theorem and
the allowed-generator reciprocity theorem.
-/

noncomputable section
open scoped BigOperators Classical

namespace ThetaGlobal.GlobalPhases

variable {R : Type*} [Field R]

/-- The precise range condition of a sextic character extended by zero. -/
def SexticValue (z : R) : Prop := z = 0 ∨ z ^ 6 = 1

/-- The unit/coprimality mask represented by a zero-extended character. -/
def nonzeroMask (z : R) : R := if z = 0 then 0 else 1

theorem sextic_nonzero {z : R} (h : z ^ 6 = 1) : z ≠ 0 := by
  intro hz
  simpa [hz] using h

theorem sextic_zpow_six_periodic {z : R} (h : z ^ 6 = 1) (n : ℤ) :
    z ^ (n + 6) = z ^ n := by
  rw [zpow_add₀ (sextic_nonzero h), show z ^ (6 : ℤ) = 1 by simpa using h,
    mul_one]

theorem sextic_neg_four_eq_two {z : R} (h : z ^ 6 = 1) :
    z ^ (-4 : ℤ) = z ^ 2 := by
  have hp := sextic_zpow_six_periodic h (-4)
  norm_num at hp ⊢
  exact hp.symm

theorem sextic_neg_two_eq_four {z : R} (h : z ^ 6 = 1) :
    z ^ (-2 : ℤ) = z ^ 4 := by
  have hp := sextic_zpow_six_periodic h (-2)
  norm_num at hp ⊢
  exact hp.symm

/-- Row--squarefree-column interaction. -/
theorem row_column_coupling {z : R} (hz : SexticValue z) :
    z * z ^ (-4 : ℤ) = z ^ 3 := by
  rcases hz with rfl | h6
  · simp
  · rw [sextic_neg_four_eq_two h6]
    ring

/-- Row--active-mark interaction, with its zero extension retained. -/
theorem row_mark_coupling {z : R} (hz : SexticValue z) :
    z ^ (-2 : ℤ) * z ^ (-4 : ℤ) = nonzeroMask z := by
  rcases hz with rfl | h6
  · simp [nonzeroMask]
  · rw [sextic_neg_two_eq_four h6, sextic_neg_four_eq_two h6]
    rw [nonzeroMask, if_neg (sextic_nonzero h6)]
    calc
      z ^ 4 * z ^ 2 = z ^ 6 := by ring
      _ = 1 := h6

/-- Active-mark--squarefree-column interaction. -/
theorem mark_column_coupling {z : R} (hz : SexticValue z) :
    z ^ 2 * z ^ (-4 : ℤ) = z ^ (-2 : ℤ) := by
  rcases hz with rfl | h6
  · simp
  · rw [sextic_neg_four_eq_two h6, sextic_neg_two_eq_four h6]
    ring

/-- The cube variable meets an active mark only through this mask. -/
theorem mark_cube_coupling {z : R} (hz : SexticValue z) :
    z ^ 6 = nonzeroMask z := by
  rcases hz with rfl | h6
  · simp [nonzeroMask]
  · simp [nonzeroMask, sextic_nonzero h6, h6]

/-- Reciprocity can be substituted before the row--column simplification. -/
theorem reciprocal_row_column_coupling {x y : R}
    (hx : SexticValue x) (hreciprocity : x = y) :
    x * y ^ (-4 : ℤ) = x ^ 3 := by
  rw [← hreciprocity]
  exact row_column_coupling hx

/-- Simultaneous separation of all the moving kinds.  The variables are
the reciprocal pairings `(d,c)`, `(d,P)`, `(P,c)`, `(d,n)`, `(P,n)`.
There is no cancellation by a possibly zero residue symbol. -/
theorem separated_moving_couplings (dc dP Pc dn Pn : R)
    (hdc : SexticValue dc) (hdP : SexticValue dP)
    (hPc : SexticValue Pc) (hPn : SexticValue Pn) :
    (dc * dc ^ (-4 : ℤ)) * (dP ^ (-2 : ℤ) * dP ^ (-4 : ℤ)) *
        (Pc ^ 2 * Pc ^ (-4 : ℤ)) * dn ^ 3 * Pn ^ 6 =
      (dc * dn) ^ 3 * Pc ^ (-2 : ℤ) * nonzeroMask dP * nonzeroMask Pn := by
  rw [row_column_coupling hdc, row_mark_coupling hdP,
    mark_column_coupling hPc, mark_cube_coupling hPn]
  ring

/-- The same phase reduction after multiplying over any finite prime set. -/
theorem prod_row_column_coupling {P : Type*} (s : Finset P)
    (z : P → R) (hz : ∀ p ∈ s, SexticValue (z p)) :
    (∏ p ∈ s, z p * z p ^ (-4 : ℤ)) = (∏ p ∈ s, z p) ^ 3 := by
  calc
    _ = ∏ p ∈ s, z p ^ 3 := by
      apply Finset.prod_congr rfl
      intro p hp
      exact row_column_coupling (hz p hp)
    _ = _ := Finset.prod_pow s 3 z

end ThetaGlobal.GlobalPhases
