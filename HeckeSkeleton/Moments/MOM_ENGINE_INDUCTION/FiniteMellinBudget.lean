import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedProfileControl

/-!
# A common scalar for the finite strict source boxes

Only finitely many numerical boxes and backward profile orders occur.
Their scalar constants can therefore be fixed together before a source
height, node or Fourier variable is supplied. The unchanged common
source profile budget pays the outer Mellin mass with one height degree.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HeckeSkeleton.Moments.EngineInduction

/-- A positive bound for a finite list of real constants. -/
def finiteStrictConstant (N : ℕ) (coefficient : ℕ → ℝ) : ℝ :=
  1 + ∑ rank ∈ Finset.range (N + 1), max 0 (coefficient rank)

theorem finiteStrictConstant_pos (N : ℕ) (coefficient : ℕ → ℝ) :
    0 < finiteStrictConstant N coefficient := by
  have hsum : 0 ≤ ∑ rank ∈ Finset.range (N + 1), max 0 (coefficient rank) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  unfold finiteStrictConstant
  linarith

theorem le_finiteStrictConstant (N : ℕ) (coefficient : ℕ → ℝ)
    (rank : ℕ) (hrank : rank ≤ N) :
    coefficient rank ≤ finiteStrictConstant N coefficient := by
  have hterm : max 0 (coefficient rank) ≤
      ∑ r ∈ Finset.range (N + 1), max 0 (coefficient r) :=
    Finset.single_le_sum (fun _ _ => le_max_left _ _)
      (Finset.mem_range.mpr (by omega))
  unfold finiteStrictConstant
  linarith [le_max_right (0 : ℝ) (coefficient rank)]

/-- The complete outer Mellin coefficient uses the same fixed height
degree at every finite rank. Its input inequalities concern only scalar
constants already produced before the moving source. -/
theorem finiteMellin_profile_budget
    {N rank cap : ℕ} {mass : ℕ → ℝ} {engine Cp Hp T : ℝ}
    (hrank : rank ≤ N) (hmass : 0 ≤ mass rank) (hengine : 0 ≤ engine)
    (hCp : 0 ≤ Cp) (hHp : 0 ≤ Hp) (hT : 0 ≤ T) :
    mass rank * profileFamilyBudget Cp Hp T ^ (2 * (cap + 2)) * engine ≤
      (finiteStrictConstant N mass * (1 + Cp) ^ (2 * (cap + 2)) * engine) *
        (1 + T) ^ (Hp * (2 * (cap + 2) : ℕ)) := by
  rw [profileFamilyBudget_pow Cp Hp hT]
  have hconstant := le_finiteStrictConstant N mass rank hrank
  have hpow : 0 ≤ (1 + Cp) ^ (2 * (cap + 2)) := pow_nonneg (by linarith) _
  have hheight : 0 ≤ (1 + T) ^ (Hp * (2 * (cap + 2) : ℕ)) :=
    Real.rpow_nonneg (by linarith) _
  calc
    _ = (mass rank * (1 + Cp) ^ (2 * (cap + 2)) * engine) *
      (1 + T) ^ (Hp * (2 * (cap + 2) : ℕ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant hpow) hengine) hheight

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.finiteStrictConstant_pos
#print axioms HeckeSkeleton.Moments.EngineInduction.finiteMellin_profile_budget
