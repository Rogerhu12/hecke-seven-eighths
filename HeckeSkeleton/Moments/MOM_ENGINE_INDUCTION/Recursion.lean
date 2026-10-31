import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Quantitative closure of the finite fourth-moment recursion

A local step is a finite nonnegative weighted inequality, with a separate
terminal remainder.  Children are required to be earlier in the actual
three-component order of §4.8.  There is no completed moment estimate in
the interface.

The weight mass includes the complete normalized outer counting measure,
the common-support factors, the one prime-pool density, and the whole-slot
removal cost.  They must be included once in the parent's local reduction.
This module then proves termination and propagates the constants, height
degree and local power loss.  The number of child labels may vary with
the scale: only the total weight mass is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace HeckeSkeleton.Moments.EngineInduction

universe u

/-- A single finite reduction, at fixed scales and profiles.  The actual
polynomial specialization is in `Interface.lean`. -/
structure LocalStep {X : Type u} {bands : ℕ}
    (value : X → ℝ) (schedule : X → State bands) where
  children : X → Finset X
  weight : X → X → ℝ
  remainder : X → ℝ
  weight_nonneg : ∀ x y, y ∈ children x → 0 ≤ weight x y
  earlier : ∀ x y, y ∈ children x → (schedule y).Earlier (schedule x)
  estimate : ∀ x, value x ≤ remainder x + ∑ y ∈ children x, weight x y * value y

namespace LocalStep

variable {X : Type u} {bands : ℕ} {value : X → ℝ} {schedule : X → State bands}

/-- The terminal remainder is charged once.  Each recursive edge consumes
only its own weight mass; no bound on the number of labels is required. -/
theorem bound (step : LocalStep value schedule) (terminal mass : ℝ)
    (ht : 0 ≤ terminal) (hm : 0 ≤ mass)
    (hterminal : ∀ x, step.remainder x ≤ terminal)
    (hmass : ∀ x, (∑ y ∈ step.children x, step.weight x y) ≤ mass) :
    ∀ x, value x ≤ terminal * (1 + mass) ^ ((schedule x).rank + 1) := by
  have hone : 1 ≤ 1 + mass := by linarith
  have hmain : ∀ n : ℕ, ∀ x, (schedule x).rank = n →
      value x ≤ terminal * (1 + mass) ^ (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      have hchild : ∀ y ∈ step.children x,
          value y ≤ terminal * (1 + mass) ^ n := by
        intro y hy
        have hylt : (schedule y).rank < n := by
          rw [← hx]
          exact State.earlier_rank_lt (step.earlier x y hy)
        exact (ih _ hylt y rfl).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hone (Nat.succ_le_of_lt hylt)) ht)
      have hpower : 1 ≤ (1 + mass) ^ n := one_le_pow₀ hone
      have hnonneg : 0 ≤ terminal * (1 + mass) ^ n :=
        mul_nonneg ht (pow_nonneg (by linarith) _)
      calc
        value x ≤ step.remainder x +
            ∑ y ∈ step.children x, step.weight x y * value y := step.estimate x
        _ ≤ terminal +
            ∑ y ∈ step.children x, step.weight x y * (terminal * (1 + mass) ^ n) :=
          add_le_add (hterminal x) (Finset.sum_le_sum fun y hy =>
            mul_le_mul_of_nonneg_left (hchild y hy) (step.weight_nonneg x y hy))
        _ = terminal + (∑ y ∈ step.children x, step.weight x y) *
            (terminal * (1 + mass) ^ n) := by rw [Finset.sum_mul]
        _ ≤ terminal + mass * (terminal * (1 + mass) ^ n) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right (hmass x) hnonneg)
        _ ≤ terminal * (1 + mass) ^ n + mass * (terminal * (1 + mass) ^ n) :=
          add_le_add
            (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower ht) le_rfl
        _ = terminal * (1 + mass) ^ (n + 1) := by rw [pow_succ]; ring
  intro x
  exact hmain _ x rfl

/-- A common exponent for every source index and every recursively
generated label. -/
theorem uniform_rank_bound (step : LocalStep value schedule)
    (terminal mass : ℝ) (ht : 0 ≤ terminal) (hm : 0 ≤ mass)
    (hterminal : ∀ x, step.remainder x ≤ terminal)
    (hmass : ∀ x, (∑ y ∈ step.children x, step.weight x y) ≤ mass) :
    ∀ x, value x ≤ terminal * (1 + mass) ^ (4 * (bands + 1)) := by
  intro x
  exact (step.bound terminal mass ht hm hterminal hmass x).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith) (Nat.succ_le_of_lt (schedule x).rank_lt_bound)) ht)

end LocalStep

/-- The simple algebra behind finite propagation.  The coarse terminal
loss `β` appears once; only the local edge loss `δ` is multiplied by depth. -/
theorem propagated_majorant (C U H β δ : ℝ) (N : ℕ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hH : 1 ≤ H) (hδ : 0 ≤ δ) :
    C * H * U ^ β * (1 + C * H * U ^ δ) ^ N ≤
      (C * (1 + C) ^ N) * U ^ (β + (N : ℝ) * δ) * H ^ (N + 1) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hUd : 1 ≤ U ^ δ := Real.one_le_rpow hU hδ
  have hfactor : 1 + C * H * U ^ δ ≤ (1 + C) * H * U ^ δ := by
    nlinarith [mul_le_mul hH hUd (by norm_num : (0 : ℝ) ≤ 1) hH0]
  have hleft : 0 ≤ 1 + C * H * U ^ δ := by positivity
  have hpow : (U ^ δ) ^ N = U ^ ((N : ℝ) * δ) := by
    rw [mul_comm (N : ℝ) δ, Real.rpow_mul_natCast hU0.le]
  calc
    _ ≤ C * H * U ^ β * ((1 + C) * H * U ^ δ) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hleft hfactor N) (by positivity)
    _ = (C * (1 + C) ^ N) * U ^ (β + (N : ℝ) * δ) * H ^ (N + 1) := by
      rw [Real.rpow_add hU0, mul_pow, mul_pow, hpow]
      rw [pow_succ]
      ring

/-- A uniform polynomial-height conclusion from the local terminal and
weight estimates.  It is independent of the number of finite labels. -/
theorem localStep_power_bound {X : Type u} {bands : ℕ}
    {value : X → ℝ} {schedule : X → State bands}
    (step : LocalStep value schedule) (C U T H β δ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hterminal : ∀ x, step.remainder x ≤ C * (1 + T) ^ H * U ^ β)
    (hmass : ∀ x, (∑ y ∈ step.children x, step.weight x y) ≤
      C * (1 + T) ^ H * U ^ δ) :
    ∀ x, value x ≤
      (C * (1 + C) ^ (4 * (bands + 1))) *
        U ^ (β + (4 * (bands + 1) : ℕ) * δ) *
        (1 + T) ^ (H * ((4 * (bands + 1) : ℕ) + 1)) := by
  intro x
  have hp : 1 ≤ (1 + T) ^ H := Real.one_le_rpow (by linarith) hH
  have h₁ := step.uniform_rank_bound
    (C * (1 + T) ^ H * U ^ β) (C * (1 + T) ^ H * U ^ δ)
    (by positivity) (by positivity) hterminal hmass x
  apply h₁.trans
  convert propagated_majorant C U ((1 + T) ^ H) β δ (4 * (bands + 1))
    hC hU hp hδ using 1
  rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 1 + T)]
  norm_num

end HeckeSkeleton.Moments.EngineInduction
