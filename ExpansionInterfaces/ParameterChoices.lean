import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Actual numeric choices for the small bin width and shell allowance.
They supply the numeric fields of a future ActualHighPresentation and ensure
its shell upper bound is also the one required by BlockSource. -/

noncomputable section
namespace ExpansionInterfaces

def binWidth (lamA lamB : ℝ) : ℝ := min lamA lamB / 200

def shellAllowance (lamA : ℝ) : ℝ := min lamA (1 / 96)

theorem binWidth_spec {lamA lamB : ℝ} (ha : 0 < lamA) (hb : 0 < lamB) :
    0 < binWidth lamA lamB ∧ binWidth lamA lamB ≤ min lamA lamB / 100 := by
  have hh := lt_min ha hb
  unfold binWidth
  constructor <;> linarith

theorem shellAllowance_spec {lamA : ℝ} (ha : 0 < lamA) :
    0 < shellAllowance lamA ∧ shellAllowance lamA < 1 / 48 ∧
      shellAllowance lamA ≤ lamA := by
  unfold shellAllowance
  refine ⟨lt_min ha (by norm_num), ?_, min_le_left _ _⟩
  exact (min_le_right _ _).trans_lt (by norm_num)

theorem shell_upper_for_BlockSource {lamA shell : ℝ}
    (h : shell ≤ 13 / 16 + shellAllowance lamA) :
    shell ≤ 13 / 16 + lamA := by
  apply h.trans
  unfold shellAllowance
  linarith [min_le_left lamA (1 / 96 : ℝ)]

theorem revised_shell_lower_implies_legacy {shell : ℝ}
    (h : 1 / 16 ≤ shell) : 1 / 100 ≤ shell := by linarith

end ExpansionInterfaces
