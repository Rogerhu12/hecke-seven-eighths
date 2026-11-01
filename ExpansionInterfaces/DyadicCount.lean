import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit counts for dyadic length labels

The schedule is constructed as a finite type; its size estimate is proved
for every `Z >= 1`.  The missing detector theorem must show that its lengths
are represented by this schedule.  No such analytic coverage is assumed or
claimed by these purely numerical counting lemmas.
-/

noncomputable section
namespace ExpansionInterfaces

/-- Two spare positions cover natural floor/ceiling endpoint conventions. -/
def dyadicCount (c Z : ℝ) : ℕ := Nat.floor (c * Real.log Z) + 2

theorem dyadicCount_le {c Z η : ℝ} (hc : 0 ≤ c) (hZ : 1 ≤ Z) (hη : 0 < η) :
    (dyadicCount c Z : ℝ) ≤ (2 + c / η) * Z ^ η := by
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hfl := Nat.floor_le (mul_nonneg hc hlog)
  have hl := Real.log_le_rpow_div (by linarith : 0 ≤ Z) hη
  have hp : 1 ≤ Z ^ η := Real.one_le_rpow hZ hη.le
  have hcount : (dyadicCount c Z : ℝ) ≤ c * Real.log Z + 2 := by
    unfold dyadicCount
    push_cast
    linarith
  calc
    (dyadicCount c Z : ℝ) ≤ c * Real.log Z + 2 := hcount
    _ ≤ c * (Z ^ η / η) + 2 := by linarith [mul_le_mul_of_nonneg_left hl hc]
    _ ≤ c * (Z ^ η / η) + 2 * Z ^ η := by linarith
    _ = (2 + c / η) * Z ^ η := by ring

theorem dyadicCount_square_le {c Z η : ℝ}
    (hc : 0 ≤ c) (hZ : 1 ≤ Z) (hη : 0 < η) :
    (dyadicCount c Z : ℝ) ^ 2 ≤ (2 + 2 * c / η) ^ 2 * Z ^ η := by
  have hhalf : 0 < η / 2 := by linarith
  have hn := dyadicCount_le hc hZ hhalf
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (dyadicCount c Z)) hn 2
  have hexp : (Z ^ (η / 2)) ^ 2 = Z ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Z)]
    congr 1
    norm_num
  have hconst : 2 + c / (η / 2) = 2 + 2 * c / η := by ring
  simpa only [mul_pow, hexp, hconst] using hsq

/-- Fixed character presentations and two independently chosen dyadic lengths. -/
abbrev DyadicWitnessLabels (presentations : ℕ) (c Z : ℝ) :=
  Fin presentations × (Fin (dyadicCount c Z) × Fin (dyadicCount c Z))

theorem card_dyadicWitnessLabels (presentations : ℕ) (c Z : ℝ) :
    Fintype.card (DyadicWitnessLabels presentations c Z) =
      presentations * dyadicCount c Z ^ 2 := by
  simp [DyadicWitnessLabels, pow_two]

theorem dyadicWitnessLabels_subpower (presentations : ℕ) {c Z η : ℝ}
    (hc : 0 ≤ c) (hZ : 1 ≤ Z) (hη : 0 < η) :
    (Fintype.card (DyadicWitnessLabels presentations c Z) : ℝ) ≤
      presentations * (2 + 2 * c / η) ^ 2 * Z ^ η := by
  rw [card_dyadicWitnessLabels]
  push_cast
  have hh := mul_le_mul_of_nonneg_left (dyadicCount_square_le hc hZ hη)
    (Nat.cast_nonneg presentations : (0 : ℝ) ≤ presentations)
  simpa only [mul_assoc] using hh

end ExpansionInterfaces
