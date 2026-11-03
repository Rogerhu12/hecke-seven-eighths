import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum

/-!
# Orthogonality for the optional positive-valuation branch

The ordinary zeroth digit is constant on residue units.  At positive
valuation its additive phase is one.  The remaining character is the
fourth power of an exact-order-six character, whose sum is zero.

These lemmas use only finite character algebra.  The project adapter
derives the exact order from the actual specified-root residue character.
-/

noncomputable section
open scoped BigOperators

namespace ThetaGlobal.GlobalCharacterSums

variable {R C : Type*} [CommMonoid R] [CommRing C] [IsDomain C]

/-- Orthogonality over the unit group, with no zero-extension convention
hidden in the index of summation. -/
theorem sum_units_eq_zero_of_ne_one [Fintype Rˣ]
    (χ : MulChar R C) (hχ : χ ≠ 1) :
    (∑ x : Rˣ, χ (x : R)) = 0 := by
  obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp hχ
  apply eq_zero_of_mul_eq_self_left hb
  calc
    χ (b : R) * ∑ x : Rˣ, χ (x : R) =
        ∑ x : Rˣ, χ ((b * x : Rˣ) : R) := by
      simp only [Finset.mul_sum, Units.val_mul, map_mul]
    _ = ∑ x : Rˣ, χ (x : R) :=
      Equiv.sum_comp (Equiv.mulLeft b) (fun x : Rˣ => χ (x : R))

theorem fourth_power_ne_one_of_order_six (χ : MulChar R C)
    (hχ : orderOf χ = 6) : χ ^ 4 ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hχ] at hd
  norm_num at hd

theorem sum_fourth_power_units_eq_zero [Fintype Rˣ]
    (χ : MulChar R C) (hχ : orderOf χ = 6) :
    (∑ x : Rˣ, χ (x : R) ^ 4) = 0 := by
  simpa only [MulChar.pow_apply_coe] using
    sum_units_eq_zero_of_ne_one (χ ^ 4) (fourth_power_ne_one_of_order_six χ hχ)

/-- This is the literal positive-valuation zeroth-row exterior sum. -/
theorem ordinary_zero_digit_positive_sum [Fintype Rˣ]
    (χ : MulChar R C) (hχ : orderOf χ = 6) (qinv spherical : C) :
    spherical * (∑ x : Rˣ, (-qinv) * χ (x : R) ^ 4) = 0 := by
  rw [← Finset.mul_sum, sum_fourth_power_units_eq_zero χ hχ, mul_zero, mul_zero]

end ThetaGlobal.GlobalCharacterSums
