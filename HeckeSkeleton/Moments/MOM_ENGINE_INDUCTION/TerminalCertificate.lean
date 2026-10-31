import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Terminal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Terminal certificates from the raw local ledgers

The two-transform step supplies finite terminal components, their original
nonnegative coefficients, and the appropriate local ledger for each
component.  This module proves the common terminal exponent and sums the
components.  In particular, the exceptional saving and the final terminal
bound are deductions, not fields of the single-step input.

The coefficient-mass hypotheses are the analytic inputs: the genuine row
classification and sixth-power fibers, the whole centered cancellation,
diagonal coefficients and common frequency tails must supply them before
this arithmetic certificate is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace HeckeSkeleton.Moments.EngineInduction

/-- The coarse loss in the order prescribed by the end of §4.8. -/
def terminalBudget (ρ padding σ boundary : ℝ) : ℝ :=
  ρ + padding + ρ / 6 + 3 * σ + 5 * σ / 3 + boundary

theorem terminalBudget_nonneg {ρ padding σ boundary : ℝ}
    (hρ : 0 ≤ ρ) (hp : 0 ≤ padding) (hσ : 0 ≤ σ) (hb : 0 ≤ boundary) :
    0 ≤ terminalBudget ρ padding σ boundary := by
  unfold terminalBudget
  positivity

/-- A raw terminal exponent, classified by its actual role in the
two-transform expansion.  Centered coefficients retain the formal lower
scale until the common residue cancellation has been used. -/
inductive TerminalLedger (ρ padding σ boundary : ℝ) : ℝ → Prop where
  | base {e : ℝ}
      (hexponent : e ≤ ρ + padding + ρ / 6) :
      TerminalLedger ρ padding σ boundary e
  | uncentered {e A M F₁ F₂ c w b₂ : ℝ}
      (hexponent : e ≤ A - 5 * M / 6 - F₁ - F₂)
      (hcore : A ≤ 5 * M / 6)
      (hc : 0 ≤ c) (hw : 0 ≤ w) (hb₂ : 0 ≤ b₂)
      (hF₁ : 2 * (c + w) / 3 - 3 * σ - boundary ≤ F₁)
      (hF₂ : 2 * b₂ / 3 ≤ F₂) :
      TerminalLedger ρ padding σ boundary e
  | centeredPositive {e A M F₁ F₂ c w c₂ d₂ : ℝ}
      (hexponent : e ≤ A - 5 * M / 6 - F₁ - F₂ -
        max (M / 4 - (c + w + min c₂ d₂)) 0)
      (hcapacity : A ≤ M)
      (hF₁ : 2 * (c + w) / 3 - 3 * σ - boundary ≤ F₁)
      (hF₂ : 2 * ((c₂ + d₂) / 2) / 3 ≤ F₂) :
      TerminalLedger ρ padding σ boundary e
  | centeredZero {e A M F₁ F₂ c w c₂ d₂ : ℝ}
      (hexponent : e ≤ A - 5 * M / 6 - F₁ - F₂ -
        max (M / 4 - (c + w + min c₂ d₂)) 0)
      (hpadded : A ≤ M + padding)
      (hF₁ : 2 * (c + w) / 3 - 3 * σ - boundary ≤ F₁)
      (hF₂ : 2 * ((c₂ + d₂) / 2) / 3 ≤ F₂) :
      TerminalLedger ρ padding σ boundary e
  | diagonal {e : ℝ}
      (hexponent : e ≤ 5 * σ / 3 + padding + boundary) :
      TerminalLedger ρ padding σ boundary e
  | tail {e : ℝ} (hexponent : e ≤ 0) :
      TerminalLedger ρ padding σ boundary e

namespace TerminalLedger

/-- All terminal alternatives fit the same coarse budget.  The centered
cases use the divisor-saving optimization proved in `Terminal.lean`. -/
theorem exponent_le {ρ padding σ boundary e : ℝ}
    (ledger : TerminalLedger ρ padding σ boundary e)
    (hρ : 0 ≤ ρ) (hp : 0 ≤ padding) (hσ : 0 ≤ σ) (hb : 0 ≤ boundary) :
    e ≤ terminalBudget ρ padding σ boundary := by
  cases ledger with
  | base he =>
      unfold terminalBudget
      linarith
  | uncentered he hcore hc hw hb₂ hF₁ hF₂ =>
      have h := uncentered_exceptional_excess_le hcore hc hw hb₂ hF₁ hF₂
      unfold terminalBudget
      linarith
  | @centeredPositive _ A M _ _ _ _ _ _ he hcapacity hF₁ hF₂ =>
      have h := centered_exceptional_terminal (A := A) (M := M) hF₁ hF₂
      have hm : max (A - M) 0 = 0 := max_eq_right (sub_nonpos.mpr hcapacity)
      rw [hm] at h
      unfold terminalBudget
      linarith
  | @centeredZero _ A M _ _ _ _ _ _ he hpadded hF₁ hF₂ =>
      have h := centered_exceptional_terminal (A := A) (M := M) hF₁ hF₂
      have hm : max (A - M) 0 ≤ padding := max_le (by linarith) hp
      unfold terminalBudget
      linarith
  | diagonal he =>
      unfold terminalBudget
      linarith
  | tail he =>
      exact he.trans (terminalBudget_nonneg hρ hp hσ hb)

end TerminalLedger

universe u

/-- The finite genuine terminal sum after the common arithmetic and
analytic inputs have been recorded.  There is no final remainder bound
among the fields: it is proved below from these raw components. -/
structure TerminalComponents
    (residual U T C H ρ padding σ boundary : ℝ) where
  Label : Type u
  terms : Finset Label
  coefficient : Label → ℝ
  exponent : Label → ℝ
  coefficient_nonneg : ∀ j ∈ terms, 0 ≤ coefficient j
  estimate : residual ≤ ∑ j ∈ terms, coefficient j * U ^ exponent j
  mass : (∑ j ∈ terms, coefficient j) ≤ C * (1 + T) ^ H
  ledger : ∀ j ∈ terms, TerminalLedger ρ padding σ boundary (exponent j)

namespace TerminalComponents

/-- Close the terminal sum with any exponent above the explicit coarse
budget.  The original finite coefficient mass is charged exactly once. -/
theorem bound {residual U T C H ρ padding σ boundary β : ℝ}
    (components : TerminalComponents.{u} residual U T C H ρ padding σ boundary)
    (hU : 1 ≤ U)
    (hρ : 0 ≤ ρ) (hp : 0 ≤ padding) (hσ : 0 ≤ σ) (hb : 0 ≤ boundary)
    (hbudget : terminalBudget ρ padding σ boundary ≤ β) :
    residual ≤ C * (1 + T) ^ H * U ^ β := by
  calc
    residual ≤ ∑ j ∈ components.terms,
        components.coefficient j * U ^ components.exponent j := components.estimate
    _ ≤ ∑ j ∈ components.terms, components.coefficient j * U ^ β := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU
          (((components.ledger j hj).exponent_le hρ hp hσ hb).trans hbudget))
        (components.coefficient_nonneg j hj)
    _ = (∑ j ∈ components.terms, components.coefficient j) * U ^ β := by
      rw [Finset.sum_mul]
    _ ≤ C * (1 + T) ^ H * U ^ β :=
      mul_le_mul_of_nonneg_right components.mass
        (Real.rpow_nonneg (zero_le_one.trans hU) _)

end TerminalComponents

end HeckeSkeleton.Moments.EngineInduction
