import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quantitative numerical consumption of the explicit finite-height
Mellin bounds. These lemmas do not assert a Hecke estimate; that estimate
is supplied by the actual deleted-continuation adapters. Constants and
tail order are chosen before the varying exponent, length, and value. -/

noncomputable section
namespace ExpansionDetector.PowerBudget

theorem exists_const_mul_rpow_absorbed (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ x : ℝ,
      C * U ^ x ≤ U ^ (x + η) := by
  let B : ℝ := max C 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right C 1)
  let U₀ : ℝ := max 2 (B ^ (1 / η))
  refine ⟨U₀, le_max_left _ _, ?_⟩
  intro U hU x
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    ((le_max_left _ _).trans hU)
  have hroot : B ^ (1 / η) ≤ U := (le_max_right _ _).trans hU
  have hpower : B ≤ U ^ η := by
    calc
      B = (B ^ (1 / η)) ^ η := by
        rw [← Real.rpow_mul hB.le, one_div_mul_cancel hη.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB.le _) hroot hη.le
  calc
    C * U ^ x ≤ U ^ η * U ^ x :=
      mul_le_mul_of_nonneg_right ((le_max_left C 1).trans hpower) (Real.rpow_nonneg hUpos.le _)
    _ = U ^ (x + η) := by rw [← Real.rpow_add hUpos]; congr 1; ring

/-- One uniform cutoff absorbs a fixed constant and both finite-height
tails, then squares the normalized polynomial. The reference exponent is
allowed to be negative, as it is on long reflected plain blocks. -/
theorem exists_absorb_contour_remainder_square (C η : ℝ)
    (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ x : ℝ, -30 ≤ x → ∀ P : ℂ,
      ‖P‖ ≤ C * (U ^ (x + η / 4) + U ^ (-100 : ℝ) + U ^ (-100 : ℝ)) →
      ‖P‖ ^ 2 ≤ U ^ (2 * x + η) := by
  obtain ⟨U₀, hU₀, habsorb⟩ := exists_const_mul_rpow_absorbed (3 * C) (η / 4)
    (by positivity) (by positivity)
  refine ⟨U₀, hU₀, ?_⟩
  intro U hU x hx P hP
  have hUone : 1 ≤ U := by linarith [hU₀.trans hU]
  have hUpos : 0 < U := zero_lt_one.trans_le hUone
  have htail : U ^ (-100 : ℝ) ≤ U ^ (x + η / 4) :=
    Real.rpow_le_rpow_of_exponent_le hUone (by linarith)
  have hnorm : ‖P‖ ≤ U ^ (x + η / 2) := by
    calc
      _ ≤ C * (U ^ (x + η / 4) + U ^ (-100 : ℝ) + U ^ (-100 : ℝ)) := hP
      _ ≤ (3 * C) * U ^ (x + η / 4) := by nlinarith
      _ ≤ U ^ ((x + η / 4) + η / 4) := habsorb U hU (x + η / 4)
      _ = _ := by congr 1; ring
  calc
    ‖P‖ ^ 2 ≤ (U ^ (x + η / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = U ^ ((x + η / 2) * (2 : ℕ)) := (Real.rpow_mul_natCast hUpos.le _ 2).symm
    _ = U ^ (2 * x + η) := by congr 1; ring

theorem normalize_left_monomial (X B β σ : ℝ) (hX : 0 < X) :
    X ^ (β - 1 / 2) * (B * X ^ (σ - β)) = B * X ^ (σ - 1 / 2) := by
  have hp : X ^ (β - 1 / 2) * X ^ (σ - β) = X ^ (σ - 1 / 2) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  calc
    _ = B * (X ^ (β - 1 / 2) * X ^ (σ - β)) := by ring
    _ = _ := by rw [hp]

theorem normalize_initial_monomial (X B β : ℝ) (hX : 0 < X) :
    X ^ (β - 1 / 2) * (B * X ^ (2 - β)) = B * X ^ (3 / 2 : ℝ) := by
  simpa only [show (2 - 1 / 2 : ℝ) = 3 / 2 by norm_num] using
    normalize_left_monomial X B β 2 hX

/-- The tail order is chosen before any row or length. It absorbs both
the buffered cost and the coarse reflected rectangle cost. -/
theorem exists_uniform_contour_order (τ L b κ : ℝ) (hτ : 0 < τ) :
    ∃ N : ℕ, 3 / 2 * L + max b κ + 100 ≤ τ * N := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((3 / 2 * L + max b κ + 100) / τ)
  refine ⟨N, ?_⟩
  have h := mul_le_mul_of_nonneg_left hN hτ.le
  simpa only [mul_div_cancel₀ _ hτ.ne'] using h

/-- Explicit exponent allocation for the three actual analytic estimates.
`b` is the buffered value/inverse cost; `κ` is used only on horizontal sides. -/
theorem contour_exponent_budget
    (a r L e ε θ τ η k : ℝ) (N : ℕ)
    (hr : 0 ≤ r) (hrL : r ≤ L) (he : 0 ≤ e) (hk : 0 ≤ k) (hθ : 0 ≤ θ)
    (hforward : 6 * e * L + 2 * ε + k * ε * θ ≤ η / 4)
    (hreflected : 12 * e + 2 * ε + k * θ * (1 + ε) ≤ η / 4)
    (htail : 3 / 2 * L + max (2 * ε + k * ε * θ) (3 / 4 + ε + k * θ) + 100 ≤ τ * N) :
    (a - 1 / 2 + 6 * e) * r + (2 * ε + k * ε * θ) ≤
      (2 * a - 1) * r / 2 + η / 4 ∧
    (a - 1 / 2) * (1 - r) + 12 * e - 6 * e * r + 2 * ε + k * θ * (1 + ε) ≤
      (2 * a - 1) * (1 - r) / 2 + η / 4 ∧
    3 / 2 * r + (2 * ε + k * ε * θ) - τ * N ≤ -100 ∧
    3 / 2 * r + (3 / 4 + ε + k * θ) - τ * N ≤ -100 := by
  have hlength := mul_le_mul_of_nonneg_left hrL (show 0 ≤ 6 * e by positivity)
  have hleft := le_max_left (2 * ε + k * ε * θ) (3 / 4 + ε + k * θ)
  have hright := le_max_right (2 * ε + k * ε * θ) (3 / 4 + ε + k * θ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith [mul_nonneg he hr]
  · linarith
  · linarith

theorem min_power_upper {U δ m η x : ℝ} (hU : 1 ≤ U) (hδ : 0 ≤ δ)
    (hforward : x ≤ U ^ (δ * m + η))
    (hreflected : x ≤ U ^ (δ * (1 - m) + η)) :
    x ≤ U ^ (δ * min m (1 - m) + η) := by
  rcases le_total m (1 - m) with hm | hm
  · simpa only [min_eq_left hm] using hforward
  · simpa only [min_eq_right hm] using hreflected

end ExpansionDetector.PowerBudget
