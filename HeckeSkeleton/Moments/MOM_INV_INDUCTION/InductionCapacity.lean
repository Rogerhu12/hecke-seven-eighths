import HeckeSkeleton.Moments.MOM_INV_INDUCTION.InductionGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Capacity parameters for marked and independent inverse moments

The marked source has `m = 1` and margin `2 * lamA`.  The independent
unmarked source has `z = 0` and `D ≤ U ^ (1 / (1 + a))`.  This file
converts the latter condition to the literal logarithmic exponent,
including the boundary `U = 1`, without dividing by a vanishing logarithm.

The final gluing lemma records the bounded-scale estimate needed to turn
an eventual analytic estimate into a statement for every `U ≥ 1`.
-/

set_option autoImplicit false

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open HeckePort.Moments

/-- The source inverse capacity is exactly the marked-margin predicate. -/
theorem capacity_marked_margins {r z lam : ℝ}
    (h₁ : r + 2 * z ≤ 1 - 2 * lam)
    (h₂ : 2 * r + 8 * z ≤ 3 - 2 * lam) :
    MarkedMargins 1 r z (2 * lam) := by
  exact ⟨h₁, by simpa using h₂⟩

/-- A fixed strict independent-scale gap gives a fixed positive margin. -/
theorem unmarked_margin_pos {a : ℝ} (ha : 0 < a) :
    0 < a / (1 + a) := div_pos ha (by linarith)

theorem unmarked_length_margins {a r : ℝ} (ha : 0 < a)
    (hr : r ≤ 1 / (1 + a)) :
    MarkedMargins 1 r 0 (a / (1 + a)) := by
  have hd : 0 < 1 + a := by linarith
  have hc := unmarked_margin_pos ha
  have hid : a / (1 + a) + 1 / (1 + a) = 1 := by
    rw [← add_div]
    simpa only [add_comm a 1] using div_self hd.ne'
  constructor <;> linarith

/-- At the only degenerate logarithmic base, the independent column
scale is forced to equal one. -/
theorem independent_scale_at_one {a D : ℝ}
    (hD : 1 ≤ D) (hcap : D ≤ (1 : ℝ) ^ (1 / (1 + a))) : D = 1 := by
  exact le_antisymm (by simpa using hcap) hD

/-- Above the unit base, the real logarithmic exponent recovers the
column scale exactly and preserves the strict upper length bound. -/
theorem independent_scale_above_one {a U D : ℝ}
    (hU : 1 < U) (hD : 1 ≤ D)
    (hcap : D ≤ U ^ (1 / (1 + a))) :
    0 ≤ Real.logb U D ∧ Real.logb U D ≤ 1 / (1 + a) ∧
      U ^ Real.logb U D = D := by
  have hu : 0 < U := zero_lt_one.trans hU
  have hd : 0 < D := zero_lt_one.trans_le hD
  have hlog := Real.logb_le_logb_of_le hU hd hcap
  rw [Real.logb_rpow hu (ne_of_gt hU)] at hlog
  exact ⟨Real.logb_nonneg hU hD, hlog,
    Real.rpow_logb hu (ne_of_gt hU) hd⟩

/-- The independent source scales have a genuine nonnegative logarithmic
parameter and the same positive marked margin, uniformly including `U=1`.
The relation `U ^ r = D` is part of the conclusion. -/
theorem independent_scale_parameters {a U D : ℝ}
    (ha : 0 < a) (hU : 1 ≤ U) (hD : 1 ≤ D)
    (hcap : D ≤ U ^ (1 / (1 + a))) :
    0 ≤ Real.logb U D ∧ Real.logb U D ≤ 1 / (1 + a) ∧
      U ^ Real.logb U D = D ∧
      MarkedMargins 1 (Real.logb U D) 0 (a / (1 + a)) := by
  by_cases hUeq : U = 1
  · have hD1 : D = 1 := independent_scale_at_one hD (by simpa [hUeq] using hcap)
    have hr : Real.logb U D = 0 := by simp [hUeq, hD1]
    have hcap0 : (0 : ℝ) ≤ 1 / (1 + a) := by positivity
    refine ⟨by simpa [hr], by simpa [hr] using hcap0, ?_, ?_⟩
    · simp [hUeq, hD1]
    · simpa [hr] using unmarked_length_margins ha hcap0
  · have hUgt : 1 < U := lt_of_le_of_ne hU (Ne.symm hUeq)
    obtain ⟨hr0, hru, heq⟩ := independent_scale_above_one hUgt hD hcap
    exact ⟨hr0, hru, heq, unmarked_length_margins ha hru⟩

/-- Explicit existential form used when constructing a literal initial
canonical node from independent scales. -/
theorem exists_independent_scale_parameter {a U D : ℝ}
    (ha : 0 < a) (hU : 1 ≤ U) (hD : 1 ≤ D)
    (hcap : D ≤ U ^ (1 / (1 + a))) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / (1 + a) ∧ U ^ r = D ∧
      MarkedMargins 1 r 0 (a / (1 + a)) :=
  ⟨Real.logb U D, independent_scale_parameters ha hU hD hcap⟩

/-- An eventual estimate supplies no information on the bounded scale
interval.  Given that separate estimate, one common constant covers all
scales, in the quantifier order needed by `StrictUnmarkedMomentBound`. -/
theorem all_scales_of_bounded_and_eventual (E R : ℝ → ℝ)
    (U₀ C₀ C₁ : ℝ)
    (hR : ∀ U : ℝ, 1 ≤ U → 0 ≤ R U)
    (hsmall : ∀ U : ℝ, 1 ≤ U → U < U₀ → E U ≤ C₀ * R U)
    (hlarge : ∀ U : ℝ, 1 ≤ U → U₀ ≤ U → E U ≤ C₁ * R U) :
    ∀ U : ℝ, 1 ≤ U → E U ≤ max C₀ C₁ * R U := by
  intro U hU
  rcases lt_or_ge U U₀ with h | h
  · exact (hsmall U hU h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hR U hU))
  · exact (hlarge U hU h).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hR U hU))

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
