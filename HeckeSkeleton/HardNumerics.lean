import HeckeGeneral.Analysis.EndpointClosure
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Exact numerical reductions at research frontiers. These do not assert
the buffered L-ratio, Poisson recursions, or actual mask realization. -/
set_option autoImplicit false
namespace HeckeSkeleton.HardNumerics
open HeckeGeneral.Analysis

/-- The raw monomial, conductor cost, full-slot normalization and row count
produce the original moderate exponent without a delta<=5/6 restriction. -/
theorem high_row_scale_identity (d δ q R : ℝ) :
    (17 / 48 : ℝ) * (1 / 2 - 17 / 50) +
      ((1 + δ) / 2 + 17 / 50 - 1) - (23 / 48 : ℝ) * ((1 + δ) / 2) -
      d * (17 / 50) + d * δ / 2 +
      (1 / 6 : ℝ) * (17 / 50 - 1 / 2) + q / 6 + d * R =
        3 / 16 + moderateExponent d δ q R := by
  unfold moderateExponent
  ring

/-- Omitting only the full-slot normalizing power costs exactly 2/75. -/
theorem omitted_slot_normalization_cost (d δ q R : ℝ) :
    (17 / 48 : ℝ) * (1 / 2 - 17 / 50) +
      ((1 + δ) / 2 + 17 / 50 - 1) - (23 / 48 : ℝ) * ((1 + δ) / 2) -
      d * (17 / 50) + d * δ / 2 + q / 6 + d * R =
        3 / 16 + moderateExponent d δ q R + 2 / 75 := by
  unfold moderateExponent
  ring

/-- The comparison node retains a strict positive capacity margin all the
way to kappa=1. Actual child lengths still have to satisfy hcomparison. -/
theorem paired_comparison_capacity_margin
    (M κ z A Acomp ξ : ℝ) (hz : 0 ≤ z) (hκ : 3 / 4 ≤ κ)
    (hlarge : 5 * M / 6 < A) (hcapacity : A + (6 * κ - 1) * z ≤ M)
    (hcomparison : Acomp ≤ 3 * M / 2 - A + 2 * z + ξ) :
    M / 14 - ξ < 5 * M / 6 - Acomp ∧
      M / 14 - ξ < M - (Acomp + (6 * κ - 1) * z) := by
  have hprod : 0 ≤ (κ - 3 / 4) * z := mul_nonneg (by linarith) hz
  constructor <;> nlinarith

theorem paired_comparison_endpoint_margin
    (M z A Acomp ξ : ℝ) (hlarge : 5 * M / 6 < A)
    (hcapacity : A + 5 * z ≤ M)
    (hcomparison : Acomp ≤ 3 * M / 2 - A + 2 * z + ξ) :
    M / 10 - ξ < M - (Acomp + 5 * z) := by
  linarith

end HeckeSkeleton.HardNumerics
