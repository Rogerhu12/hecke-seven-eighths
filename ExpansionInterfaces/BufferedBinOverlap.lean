import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Buffered inequalities alone do not give a partition

This is an abstract numerical witness, not an assertion that any particular
Hecke L-function has a zero at 7/10.  It proves that the displayed selected-
zero and upper-zero inequalities permit more than one center for the same
row.  A separate deterministic assignment is therefore needed when all raw
buffered bins are enumerated in an exact physical decomposition.
-/

noncomputable section
namespace ExpansionInterfaces

/-- The real-part inequalities for one selected zero and one upper bound. -/
def BufferedRealCondition (beta center width : ℝ) : Prop :=
  center ≤ beta ∧ beta ≤ center + 2 * width

/-- Adjacent centers both accept the same real part; no analytic input is used. -/
theorem adjacent_buffer_centers (beta width : ℝ) (hw : 0 ≤ width) :
    BufferedRealCondition beta (beta - width) width ∧
      BufferedRealCondition beta beta width := by
  unfold BufferedRealCondition
  constructor <;> constructor <;> linarith

/-- This numerical choice respects the small-width scale of the skeleton. -/
theorem numerical_buffer_overlap :
    let e : ℝ := 1 / 200000
    let beta : ℝ := 7 / 10
    0 < e ∧ e ≤ min (1 / 1000 : ℝ) (1 / 1000 : ℝ) / 100 ∧
      51 / 100 < beta - e ∧ beta ≤ 9 / 10 ∧
      beta - e ≠ beta ∧
      BufferedRealCondition beta (beta - e) e ∧
      BufferedRealCondition beta beta e := by
  norm_num [BufferedRealCondition]

/-- A zero of imaginary part zero also fits every positive buffered height. -/
theorem zero_imaginary_part_fits (i : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    |(0 : ℝ)| ≤ 3 * i * T ∧ |(0 : ℝ)| ≤ 3 * (i + 1) * T := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  simp only [abs_zero]
  constructor <;> positivity

end ExpansionInterfaces
