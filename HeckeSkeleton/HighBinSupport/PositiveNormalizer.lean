import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-! Cancellation of a finite positive normalizer, including a zero sum.
This is used for a coarse boundary estimate and requires no lower bound
for the number of primes in the window. -/

noncomputable section
namespace HighBinBoundary.PositiveNormalizer

open scoped BigOperators

/-- A positive finite normalizer absorbs the identical majorant mass.
Lean's literal division convention also covers an empty or zero mass. -/
theorem norm_sum_div_nonneg_sum_le {ι : Type*} (F : Finset ι)
    (a : ι → ℝ) (x : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ i ∈ F, 0 ≤ a i) (hx : ∀ i ∈ F, ‖x i‖ ≤ M * a i) :
    ‖(∑ i ∈ F, x i) / ((∑ i ∈ F, a i : ℝ) : ℂ)‖ ≤ M := by
  have hsum : 0 ≤ ∑ i ∈ F, a i := Finset.sum_nonneg ha
  by_cases hz : ∑ i ∈ F, a i = 0
  · simp [hz, hM]
  · have hp : 0 < ∑ i ∈ F, a i := lt_of_le_of_ne hsum (Ne.symm hz)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum]
    apply (div_le_iff₀ hp).mpr
    calc
      ‖∑ i ∈ F, x i‖ ≤ ∑ i ∈ F, ‖x i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ F, M * a i := Finset.sum_le_sum hx
      _ = M * ∑ i ∈ F, a i := (Finset.mul_sum _ _ _).symm

/-- An external scalar can be retained exactly, without a nonzero premise. -/
theorem norm_sum_div_scaled_nonneg_sum_le {ι : Type*} (F : Finset ι)
    (a : ι → ℝ) (x : ι → ℂ) (c : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ i ∈ F, 0 ≤ a i) (hx : ∀ i ∈ F, ‖x i‖ ≤ M * a i) :
    ‖(∑ i ∈ F, x i) / (c * ((∑ i ∈ F, a i : ℝ) : ℂ))‖ ≤ ‖c⁻¹‖ * M := by
  have h := norm_sum_div_nonneg_sum_le F a x M hM ha hx
  rw [mul_comm c, div_mul_eq_div_div, norm_div]
  calc
    _ ≤ M / ‖c‖ := div_le_div_of_nonneg_right h (norm_nonneg _)
    _ = ‖c⁻¹‖ * M := by rw [norm_inv, div_eq_mul_inv, mul_comm]

/-- The coarse loss of undoing q^(-5/6) in every genuine slot is Z^(1/6).
The slot number is fixed before the external tail order. -/
theorem prime_normalizer_coarse_cost (J : ℕ) (hJ : 0 < J)
    (Z : ℝ) (hZ : 0 < Z) :
    Z ^ (1 / 36 : ℝ) *
      (2 * Z ^ ((1 / 6 : ℝ) / (J : ℝ))) ^ ((5 / 6 : ℝ) * (J : ℝ)) =
      2 ^ ((5 / 6 : ℝ) * (J : ℝ)) * Z ^ (1 / 6 : ℝ) := by
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have he : ((1 / 6 : ℝ) / (J : ℝ)) * ((5 / 6 : ℝ) * (J : ℝ)) = 5 / 36 := by
    field_simp [hJ0] <;> ring
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hZ.le _),
    ← Real.rpow_mul hZ.le, he]
  calc
    _ = 2 ^ ((5 / 6 : ℝ) * (J : ℝ)) * (Z ^ (1 / 36 : ℝ) * Z ^ (5 / 36 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hZ]; norm_num

#print axioms norm_sum_div_nonneg_sum_le
#print axioms norm_sum_div_scaled_nonneg_sum_le
#print axioms prime_normalizer_coarse_cost

end HighBinBoundary.PositiveNormalizer
