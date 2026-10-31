import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Recursion
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Quantitative recursion with a positive measure of earlier children

The common Fourier kernel produces a continuous frequency integral.  This
module retains that integral: the child measure is a genuine positive
finite measure, and almost every child is earlier in the same finite-rank
order as the discrete engine.  The complete scalar weight is absorbed in
this measure, whose total mass must be estimated by the analytic producer.

The value function is unchanged.  In the polynomial specialization it is
the actual normalized energy of each node, including its complete centered
coefficient.  No finite set of representative frequencies or assumed final
energy bound is introduced.  Integrability is an explicit local obligation,
so the totalized Bochner integral cannot silently discard a divergent term.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace HeckeSkeleton.Moments.EngineInduction

universe u

/-- A local reduction with an actual positive measure on child states. -/
structure IntegralStep {X : Type u} {bands : ℕ} [MeasurableSpace X]
    (value : X → ℝ) (schedule : X → State bands) where
  childrenMeasure : X → Measure X
  finite : ∀ x, IsFiniteMeasure (childrenMeasure x)
  remainder : X → ℝ
  integrable : ∀ x, Integrable value (childrenMeasure x)
  earlier : ∀ x, ∀ᵐ y ∂(childrenMeasure x), (schedule y).Earlier (schedule x)
  estimate : ∀ x, value x ≤ remainder x + ∫ y, value y ∂(childrenMeasure x)

namespace IntegralStep

variable {X : Type u} {bands : ℕ} [MeasurableSpace X]
variable {value : X → ℝ} {schedule : X → State bands}

/-- The total positive child mass, including the full common kernel weight. -/
def mass (step : IntegralStep value schedule) (x : X) : ℝ :=
  (step.childrenMeasure x).real Set.univ

theorem mass_nonneg (step : IntegralStep value schedule) (x : X) :
    0 ≤ step.mass x := measureReal_nonneg

/-- The terminal remainder is charged once, exactly as in the finite-sum
recursion.  Almost-everywhere strict descent is sufficient. -/
theorem bound (step : IntegralStep value schedule) (terminal mass : ℝ)
    (ht : 0 ≤ terminal) (hm : 0 ≤ mass)
    (hterminal : ∀ x, step.remainder x ≤ terminal)
    (hmass : ∀ x, step.mass x ≤ mass) :
    ∀ x, value x ≤ terminal * (1 + mass) ^ ((schedule x).rank + 1) := by
  have hone : 1 ≤ 1 + mass := by linarith
  have hmain : ∀ n : ℕ, ∀ x, (schedule x).rank = n →
      value x ≤ terminal * (1 + mass) ^ (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      letI : IsFiniteMeasure (step.childrenMeasure x) := step.finite x
      have hchild : ∀ᵐ y ∂(step.childrenMeasure x),
          value y ≤ terminal * (1 + mass) ^ n :=
        (step.earlier x).mono fun y hy => by
          have hylt : (schedule y).rank < n := by
            rw [← hx]
            exact State.earlier_rank_lt hy
          exact (ih _ hylt y rfl).trans
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hone (Nat.succ_le_of_lt hylt)) ht)
      have hpower : 1 ≤ (1 + mass) ^ n := one_le_pow₀ hone
      have hnonneg : 0 ≤ terminal * (1 + mass) ^ n :=
        mul_nonneg ht (pow_nonneg (by linarith) _)
      calc
        value x ≤ step.remainder x + ∫ y, value y ∂(step.childrenMeasure x) :=
          step.estimate x
        _ ≤ terminal + ∫ _y : X, terminal * (1 + mass) ^ n ∂(step.childrenMeasure x) :=
          add_le_add (hterminal x)
            (integral_mono_ae (step.integrable x) (integrable_const _) hchild)
        _ = terminal + step.mass x * (terminal * (1 + mass) ^ n) := by
          simp only [integral_const, smul_eq_mul, IntegralStep.mass]
        _ ≤ terminal + mass * (terminal * (1 + mass) ^ n) :=
          add_le_add_left (mul_le_mul_of_nonneg_right (hmass x) hnonneg) _
        _ ≤ terminal * (1 + mass) ^ n + mass * (terminal * (1 + mass) ^ n) :=
          add_le_add
            (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower ht) le_rfl
        _ = terminal * (1 + mass) ^ (n + 1) := by rw [pow_succ]; ring
  intro x
  exact hmain _ x rfl

/-- One finite exponent controls the entire continuous family of states. -/
theorem uniform_rank_bound (step : IntegralStep value schedule)
    (terminal mass : ℝ) (ht : 0 ≤ terminal) (hm : 0 ≤ mass)
    (hterminal : ∀ x, step.remainder x ≤ terminal)
    (hmass : ∀ x, step.mass x ≤ mass) :
    ∀ x, value x ≤ terminal * (1 + mass) ^ (4 * (bands + 1)) := by
  intro x
  exact (step.bound terminal mass ht hm hterminal hmass x).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith) (Nat.succ_le_of_lt (schedule x).rank_lt_bound)) ht)

end IntegralStep

/-- Continuous Fourier children propagate the same constants, height
degree and local exponent loss as the discrete recursion. -/
theorem integralStep_power_bound {X : Type u} {bands : ℕ} [MeasurableSpace X]
    {value : X → ℝ} {schedule : X → State bands}
    (step : IntegralStep value schedule) (C U T H β δ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hterminal : ∀ x, step.remainder x ≤ C * (1 + T) ^ H * U ^ β)
    (hmass : ∀ x, step.mass x ≤ C * (1 + T) ^ H * U ^ δ) :
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
