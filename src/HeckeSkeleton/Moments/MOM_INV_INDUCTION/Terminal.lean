import HeckeSkeleton.Moments.MOM_INV_INDUCTION.InductionGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Terminal energy estimates and the label normalization

The three reflected terminal exponents are bounded in `InductionGeometry`.
This file consumes the corresponding explicit energy inequalities.  Its
constants are common to every squarefree label and surviving mark subset.
The outside factor `Z ^ (-V)` cancels the label mass exactly once; the
label's prescribed small-power loss remains in the result.

The hypotheses below are terminal block estimates, not a derivation from
the fixed physical `CompletedMarkedEnergy` statement.  The transport from
that statement to arbitrary canonical terminals is discussed separately in
`STATEMENT_AUDIT.md`.
-/

set_option autoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open scoped BigOperators

/-- Three terminal branches with a common exponent bound cost a factor of
three, uniformly in all the data indexing those branches. -/
theorem terminal_three_powers_le {Z C E e₁ e₂ e₃ p : ℝ}
    (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (h₁ : e₁ ≤ p) (h₂ : e₂ ≤ p) (h₃ : e₃ ≤ p)
    (hE : E ≤ C * (Z ^ e₁ + Z ^ e₂ + Z ^ e₃)) :
    E ≤ (3 * C) * Z ^ p := by
  have hpow₁ := Real.rpow_le_rpow_of_exponent_le hZ h₁
  have hpow₂ := Real.rpow_le_rpow_of_exponent_le hZ h₂
  have hpow₃ := Real.rpow_le_rpow_of_exponent_le hZ h₃
  calc
    E ≤ C * (Z ^ e₁ + Z ^ e₂ + Z ^ e₃) := hE
    _ ≤ C * (3 * Z ^ p) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = (3 * C) * Z ^ p := by ring

/-- The reflected row branch and the two column branches all retain the
fixed saving `c / 4`, including their localization and tail losses. -/
theorem terminal_energy_le {Z C E F M cnode c d η τ π : ℝ}
    (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hc : 0 < c) (hM : 0 ≤ M) (hnode : c / 2 ≤ cnode)
    (hd : d ≤ c / 200) (hη : η ≤ c / 1000)
    (hτ : τ ≤ c / 1000) (hπ : π ≤ c / 1000)
    (hE : E ≤ C *
      (Z ^ (F - cnode + 5 * η / 3 + π) +
       Z ^ (F - 2 * cnode + 5 * d + 17 * η / 3 + τ + π) +
       Z ^ (F - M / 4 - 3 * cnode / 4 + 5 * d / 2 +
         19 * η / 6 + τ / 2 + π))) :
    E ≤ (3 * C) * Z ^ (F - c / 4) := by
  obtain ⟨h₁, h₂, h₃⟩ := terminal_ledger_saving
    (F := F) hc hM hnode hd hη hτ hπ
  exact terminal_three_powers_le hZ hC h₁ h₂ h₃ hE

/-- The actual positive label measure is summed once.  Its main power
`Z ^ V` cancels the outside normalization, retaining only its loss `δ`. -/
theorem normalized_label_energy_le {ι : Type*} (labels : Finset ι)
    (weight energy : ι → ℝ) {Z V δ C L p : ℝ}
    (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hweight : ∀ f ∈ labels, 0 ≤ weight f)
    (hmass : ∑ f ∈ labels, weight f ≤ L * Z ^ (V + δ))
    (henergy : ∀ f ∈ labels, energy f ≤ C * Z ^ p) :
    Z ^ (-V) * (∑ f ∈ labels, weight f * energy f) ≤
      (C * L) * Z ^ (p + δ) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hp : 0 ≤ C * Z ^ p := mul_nonneg hC (Real.rpow_nonneg hz.le _)
  calc
    Z ^ (-V) * (∑ f ∈ labels, weight f * energy f) ≤
        Z ^ (-V) * (∑ f ∈ labels, weight f * (C * Z ^ p)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hz.le _)
      exact Finset.sum_le_sum (fun f hf =>
        mul_le_mul_of_nonneg_left (henergy f hf) (hweight f hf))
    _ = Z ^ (-V) * ((∑ f ∈ labels, weight f) * (C * Z ^ p)) := by
      rw [Finset.sum_mul]
    _ ≤ Z ^ (-V) * ((L * Z ^ (V + δ)) * (C * Z ^ p)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass hp)
        (Real.rpow_nonneg hz.le _)
    _ = (C * L) * (Z ^ (-V) * Z ^ (V + δ) * Z ^ p) := by ring
    _ = (C * L) * Z ^ (p + δ) := by
      rw [← Real.rpow_add hz, ← Real.rpow_add hz]
      congr 2
      ring

/-- Canonical terminal estimate after the squarefree-label measure.  The
same reflected constant is used for every label, and the label's divisor
mass is charged exactly once. -/
theorem terminal_normalized_label_energy_le {ι : Type*} (labels : Finset ι)
    (weight energy : ι → ℝ) {Z V δ C L F M cnode c d η τ π : ℝ}
    (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hweight : ∀ f ∈ labels, 0 ≤ weight f)
    (hmass : ∑ f ∈ labels, weight f ≤ L * Z ^ (V + δ))
    (hc : 0 < c) (hM : 0 ≤ M) (hnode : c / 2 ≤ cnode)
    (hd : d ≤ c / 200) (hη : η ≤ c / 1000)
    (hτ : τ ≤ c / 1000) (hπ : π ≤ c / 1000)
    (henergy : ∀ f ∈ labels, energy f ≤ C *
      (Z ^ (F - cnode + 5 * η / 3 + π) +
       Z ^ (F - 2 * cnode + 5 * d + 17 * η / 3 + τ + π) +
       Z ^ (F - M / 4 - 3 * cnode / 4 + 5 * d / 2 +
         19 * η / 6 + τ / 2 + π))) :
    Z ^ (-V) * (∑ f ∈ labels, weight f * energy f) ≤
      (3 * C * L) * Z ^ (F - c / 4 + δ) := by
  exact normalized_label_energy_le labels weight energy hZ (by positivity)
    hweight hmass (fun f hf => terminal_energy_le hZ hC hc hM hnode hd hη hτ hπ
      (henergy f hf))

/-- Absorbing a small label loss preserves a fixed terminal saving. -/
theorem terminal_label_saving {ι : Type*} (labels : Finset ι)
    (weight energy : ι → ℝ) {Z V δ C L F c : ℝ}
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : δ ≤ c / 8)
    (henergy : Z ^ (-V) * (∑ f ∈ labels, weight f * energy f) ≤
      (3 * C * L) * Z ^ (F - c / 4 + δ)) :
    Z ^ (-V) * (∑ f ∈ labels, weight f * energy f) ≤
      (3 * C * L) * Z ^ (F - c / 8) := by
  apply henergy.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
