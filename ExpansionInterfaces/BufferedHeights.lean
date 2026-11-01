import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Numerical height control for the actual buffered choices 3*i*T,
3*(i+1)*T, and T.  This proves the height bound after the finite integer
schedule is fixed; it does not construct an analytic detector. -/

noncomputable section
namespace ExpansionInterfaces

def selectedHeight (i : ℕ) (T : ℝ) : ℝ := 3 * i * T

def upperHeight (i : ℕ) (T : ℝ) : ℝ := 3 * (i + 1) * T

def contourHeight (T : ℝ) : ℝ := T

theorem buffered_heights_bound (N i : ℕ) (hi : i ≤ N) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ selectedHeight i T ∧ 0 ≤ upperHeight i T ∧ 0 ≤ contourHeight T ∧
    selectedHeight i T ≤ 3 * (N + 1 : ℝ) * (1 + T) ∧
    upperHeight i T ≤ 3 * (N + 1 : ℝ) * (1 + T) ∧
    contourHeight T ≤ 3 * (N + 1 : ℝ) * (1 + T) := by
  have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hi' hT
  unfold selectedHeight upperHeight contourHeight
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem buffered_heights_separated (i : ℕ) (T : ℝ) :
    upperHeight i T - selectedHeight i T = 3 * T := by
  unfold upperHeight selectedHeight
  ring

/-- Changing from the external height to any of the buffered heights changes
only the scalar constant, while preserving the already fixed height degree. -/
theorem height_degree_absorption {C T h A : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hA : 0 ≤ A) (hh : |h| ≤ C * (1 + T)) :
    (1 + |h|) ^ A ≤ (1 + C) ^ A * (1 + T) ^ A := by
  have hbase : 1 + |h| ≤ (1 + C) * (1 + T) := by nlinarith
  calc
    (1 + |h|) ^ A ≤ ((1 + C) * (1 + T)) ^ A :=
      Real.rpow_le_rpow (by positivity) hbase hA
    _ = (1 + C) ^ A * (1 + T) ^ A :=
      Real.mul_rpow (by positivity) (by positivity)

end ExpansionInterfaces
