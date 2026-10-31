module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# A strict-region estimate needs cross-scale structure to amplify

This elementary energy vanishes in every strict region but violates the
independent amplifier bound already at a = ε = U = 1.  In a moment family,
the missing structure is provided by the actual common polynomial and its
complete-row scale-supremum estimate, not by a bound on unrelated scales.
-/

@[expose] public section
noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

def diagonalCutoffEnergy (U D : ℝ) : ℝ := if D ≤ U then 0 else D ^ 4

theorem diagonalCutoffEnergy_strict {a U D : ℝ}
    (ha : 0 < a) (hU : 1 ≤ U) (hD : D ≤ U ^ (1 / (1 + a))) :
    diagonalCutoffEnergy U D = 0 := by
  have hexp : 1 / (1 + a) ≤ 1 :=
    (div_le_one (by linarith : 0 < 1 + a)).mpr (by linarith)
  have hu : U ^ (1 / (1 + a)) ≤ U := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hexp
  exact if_pos (hD.trans hu)

/-- Any prescribed constant fails for the independent-scale central
factor at a = ε = U = 1. -/
theorem diagonalCutoffEnergy_violates_amplification (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 1 ≤ D ∧
      C * max 1 (D ^ (5 / 3 : ℝ)) * D < diagonalCutoffEnergy 1 D := by
  let D := max 2 (C + 1)
  have hD2 : 2 ≤ D := le_max_left _ _
  have hDC : C < D := lt_of_lt_of_le (by linarith : C < C + 1) (le_max_right _ _)
  have hD1 : 1 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hmax : max 1 (D ^ (5 / 3 : ℝ)) ≤ D ^ 2 := by
    apply max_le
    · nlinarith
    · simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num : (5 / 3 : ℝ) ≤ 2)
  refine ⟨D, hD1, ?_⟩
  have hnD : ¬D ≤ 1 := by linarith
  rw [diagonalCutoffEnergy, if_neg hnD]
  calc
    _ ≤ C * D ^ 2 * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC) hDpos.le
    _ = C * D ^ 3 := by ring
    _ < D * D ^ 3 := mul_lt_mul_of_pos_right hDC (pow_pos hDpos _)
    _ = D ^ 4 := by ring

end HeckeSkeleton.Moments.UniformAmplify
