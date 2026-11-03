import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
Elementary ledger inequalities in the revised canonical reductions.
These prove arithmetic consequences of explicitly supplied length data.
They do not construct common supports, a Poisson child, or an amplifier pool.
-/
set_option autoImplicit false

namespace HeckeSkeleton.HardLedger

/-- A real-variable form of the local common-support inequality. For integral
multiplicities `i ≥ j ≥ 1`, the non-six-divisible case has `r = 1` and
`i ≥ 2`; the equal multiplicity `(1,1)` has `r = 0`. The hypotheses here
state exactly the weaker data needed for this numerical estimate. -/
theorem common_support_local
    (i j r : ℝ) (hij : j ≤ i) (hj : 1 ≤ j)
    (hr : r = 0 ∨ r = 1) (hr_one : r = 1 → 2 ≤ i) :
    max (3 * i - 5 * j - r) 0 / 6 ≤ i + j - 2 - r := by
  by_cases hsign : 3 * i - 5 * j - r ≤ 0
  · rw [max_eq_right hsign]
    rcases hr with hr | hr
    · nlinarith
    · have hi := hr_one hr
      nlinarith
  · have hnonneg : 0 ≤ 3 * i - 5 * j - r := le_of_lt (lt_of_not_ge hsign)
    rw [max_eq_left hnonneg]
    rcases hr with hr | hr
    · nlinarith
    · have hi := hr_one hr
      nlinarith

/-- At the first whole-slot prefix crossing the capacity deficit, the
previous prefix is still below it and the last slot has length at most the
mesh. Removing this prefix repairs capacity; its squared prime cost fits
the child allowance plus one mesh overshoot. Existence of such a prefix,
or the alternative in which all slots disappear, is a separate task. -/
theorem greedy_prefix_capacity_and_cost
    (κ previous last mesh F Δ err : ℝ)
    (hκ : 0 ≤ κ) (hlast : last ≤ mesh)
    (hprevious : 6 * κ * previous ≤ F)
    (hcrossing : F ≤ 6 * κ * (previous + last))
    (hdefect : F ≤ 6 * Δ + err) :
    F - 6 * κ * (previous + last) ≤ 0 ∧
      κ * (previous + last) ≤ Δ + err / 6 + κ * mesh := by
  have hovershoot : 0 ≤ κ * (mesh - last) :=
    mul_nonneg hκ (sub_nonneg.mpr hlast)
  constructor <;> nlinarith

/-- Consume an already established greedy-prefix bound. The factor six
in the capacity defect cancels the factor six in the squared prime cost;
it does not leave a factor depending on `κ` in front of the allowance. -/
theorem greedy_cost_from_defect
    (κ removed mesh F Δ err : ℝ)
    (hdefect : F ≤ 6 * Δ + err)
    (hcost : κ * removed ≤ F / 6 + κ * mesh) :
    κ * removed ≤ Δ + err / 6 + κ * mesh := by
  linarith

/-- A nonterminal inverse child has an actual width drop of at least
`3*d0/2` once its annular error is bounded by `d0/16`. The source geometry
must still supply the hypothesis relating the parent and child widths. -/
theorem inverse_child_width_drop
    (M childM V ell d0 η : ℝ)
    (hwidth : d0 ≤ V + ell) (herror : η ≤ d0 / 16)
    (hchild : 2 * (V + ell) - 8 * η ≤ M - childM) :
    3 * d0 / 2 ≤ M - childM := by
  linarith

end HeckeSkeleton.HardLedger
