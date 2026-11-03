import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BranchedIntegralRecursion

/-!
# Scalar consumption of genuine local reductions

A fixed local positive kernel can be integrated after the induction
hypothesis is applied to its actual earlier children. For an additional
outer parameter, this scalar conclusion can itself be integrated in a
separately constructed measure. No measurability of a family of inner
kernels, measurable model space, or bind of those kernels is needed.

The abstract recurrence lemma below is used only after the concrete
geometric cases have proved its scalar premise. It does not provide an
alternative analytic input contract or assume a final moment estimate.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory
open scoped BigOperators Classical

universe u v

/-- Apply a constant induction bound to the genuine children of one
fixed local output, on that output's original positive kernels. -/
theorem BranchedIntegralAt.bound_of_children
    {X : Type u} {Ω : Type v} {bands : ℕ} [MeasurableSpace Ω]
    {value : X → ℝ} {schedule : X → State bands} {x : X}
    (step : BranchedIntegralAt (Ω := Ω) value schedule x)
    {terminal mass D : ℝ} (hD : 0 ≤ D)
    (hterminal : step.remainder ≤ terminal)
    (hmass : (∑ b, (step.kernel b).real Set.univ) ≤ mass)
    (hchildren : ∀ y, (schedule y).Earlier (schedule x) → value y ≤ D) :
    value x ≤ terminal + mass * D := by
  have hbranch (b : Fin step.branches) :
      ((∫ ξ, value (step.left b ξ) ∂step.kernel b) +
        ∫ ξ, value (step.right b ξ) ∂step.kernel b) / 2 ≤
          (step.kernel b).real Set.univ * D := by
    letI : IsFiniteMeasure (step.kernel b) := step.finite b
    have hl := integral_mono_ae (step.left_integrable b) (integrable_const D)
      ((step.left_earlier b).mono fun ξ hξ => hchildren _ hξ)
    have hr := integral_mono_ae (step.right_integrable b) (integrable_const D)
      ((step.right_earlier b).mono fun ξ hξ => hchildren _ hξ)
    simp only [integral_const, smul_eq_mul] at hl hr
    linarith
  calc
    value x ≤ step.remainder +
        ∑ b, ((∫ ξ, value (step.left b ξ) ∂step.kernel b) +
          ∫ ξ, value (step.right b ξ) ∂step.kernel b) / 2 := step.estimate
    _ ≤ terminal + ∑ b, (step.kernel b).real Set.univ * D :=
      add_le_add hterminal (Finset.sum_le_sum fun b _ => hbranch b)
    _ = terminal + (∑ b, (step.kernel b).real Set.univ) * D := by
      rw [Finset.sum_mul]
    _ ≤ terminal + mass * D :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hmass hD)

/-- Strong induction on the same finite geometric rank, after the
actual local cases have been consumed as scalar inequalities. -/
theorem scalarRecursion_bound {X : Type u} {bands : ℕ}
    (value : X → ℝ) (schedule : X → State bands)
    (terminal mass : ℝ) (ht : 0 ≤ terminal) (hm : 0 ≤ mass)
    (hstep : ∀ x D, 0 ≤ D →
      (∀ y, (schedule y).Earlier (schedule x) → value y ≤ D) →
      value x ≤ terminal + mass * D) :
    ∀ x, value x ≤ terminal * (1 + mass) ^ ((schedule x).rank + 1) := by
  have hone : 1 ≤ 1 + mass := by linarith
  have hmain : ∀ rank : ℕ, ∀ x, (schedule x).rank = rank →
      value x ≤ terminal * (1 + mass) ^ (rank + 1) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro x hx
      have hD : 0 ≤ terminal * (1 + mass) ^ rank := by positivity
      have hchildren (y : X) (hy : (schedule y).Earlier (schedule x)) :
          value y ≤ terminal * (1 + mass) ^ rank := by
        have hrank : (schedule y).rank < rank := by
          rw [← hx]
          exact State.earlier_rank_lt hy
        exact (ih _ hrank y rfl).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hone (Nat.succ_le_of_lt hrank)) ht)
      have hpower : 1 ≤ (1 + mass) ^ rank := one_le_pow₀ hone
      calc
        value x ≤ terminal + mass * (terminal * (1 + mass) ^ rank) :=
          hstep x _ hD hchildren
        _ ≤ terminal * (1 + mass) ^ rank + mass * (terminal * (1 + mass) ^ rank) :=
          add_le_add
            (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower ht) le_rfl
        _ = terminal * (1 + mass) ^ (rank + 1) := by rw [pow_succ]; ring
  intro x
  exact hmain _ x rfl

/-- The terminal exponent is charged once and the edge exponent only
once per genuine rank decrease, exactly as for the kernel recurrence. -/
theorem scalarRecursion_power_bound {X : Type u} {bands : ℕ}
    (value : X → ℝ) (schedule : X → State bands) (C U T H β δ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hstep : ∀ x D, 0 ≤ D →
      (∀ y, (schedule y).Earlier (schedule x) → value y ≤ D) →
      value x ≤ C * (1 + T) ^ H * U ^ β + C * (1 + T) ^ H * U ^ δ * D) :
    ∀ x, value x ≤
      (C * (1 + C) ^ (6 * (bands + 1))) *
        U ^ (β + (6 * (bands + 1) : ℕ) * δ) *
        (1 + T) ^ (H * ((6 * (bands + 1) : ℕ) + 1)) := by
  intro x
  have hheight : 1 ≤ (1 + T) ^ H := Real.one_le_rpow (by linarith) hH
  have ht : 0 ≤ C * (1 + T) ^ H * U ^ β := by positivity
  have hm : 0 ≤ C * (1 + T) ^ H * U ^ δ := by positivity
  have hlocal := scalarRecursion_bound value schedule
    (C * (1 + T) ^ H * U ^ β) (C * (1 + T) ^ H * U ^ δ) ht hm hstep x
  have hfinite := hlocal.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith)
      (Nat.succ_le_of_lt (schedule x).rank_lt_bound)) ht)
  apply hfinite.trans
  convert propagated_majorant C U ((1 + T) ^ H) β δ (6 * (bands + 1))
    hC hU hheight hδ using 1
  rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 1 + T)]
  norm_num

end HeckeSkeleton.Moments.EngineInduction
