import ThetaGlobal.GlobalCharacterSums
import Mathlib.Tactic.Ring

/-!
# The actual nonzero support of the ordinary positive-valuation digit

At positive valuation the additive phase is one.  The remaining
character sum vanishes for every nonzero ordinary digit except j=4.
In particular a moving-row digit j=1 has only valuation e=0.
This is finite character algebra, independent of theta reflection.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalDigitSupport

open scoped BigOperators

variable {k : Type*} [Field k] [Fintype k] [Fintype kˣ]

theorem character_sixth_power (χ : MulChar k ℂ) (hχ : orderOf χ = 6) (x : kˣ) :
    χ (x : k) ^ 6 = 1 := by
  have h := congrArg (fun c : MulChar k ℂ => c (x : k)) (pow_orderOf_eq_one χ)
  simpa only [hχ, MulChar.pow_apply_coe, MulChar.one_apply_coe] using h

theorem inverse_digit_times_fourth (χ : MulChar k ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) (x : kˣ) :
    χ (x : k) ^ (-(j.val : ℤ)) * χ (x : k) ^ 4 = χ (x : k) ^ (10 - j.val) := by
  have h6 := character_sixth_power χ hχ x
  have hx : χ (x : k) ≠ 0 := by
    intro hz
    exact zero_ne_one (by
      simpa only [hz, zero_pow (by decide : (6 : ℕ) ≠ 0)] using h6)
  rw [zpow_neg, zpow_natCast, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero j.val hx)]
  rw [← pow_add, Nat.add_sub_of_le (by omega : j.val ≤ 10)]
  calc
    χ (x : k) ^ 4 = χ (x : k) ^ 6 * χ (x : k) ^ 4 := by rw [h6, one_mul]
    _ = χ (x : k) ^ 10 := by rw [← pow_add]

theorem positive_digit_character_ne_one (χ : MulChar k ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) (hj : j.val ≠ 4) : χ ^ (10 - j.val) ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hχ] at hd
  have hjlt := j.isLt
  omega

theorem ordinary_positive_digit_sum_zero (χ : MulChar k ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) (hj : j.val ≠ 4) (tauInv spherical : ℂ) :
    spherical * (∑ x : kˣ,
      tauInv * χ (x : k) ^ (-(j.val : ℤ)) * χ (x : k) ^ 4) = 0 := by
  have hs : (∑ x : kˣ, χ (x : k) ^ (10 - j.val)) = 0 := by
    simpa only [MulChar.pow_apply_coe] using
      GlobalCharacterSums.sum_units_eq_zero_of_ne_one (χ ^ (10 - j.val))
        (positive_digit_character_ne_one χ hχ j hj)
  calc
    _ = spherical * (tauInv * ∑ x : kˣ, χ (x : k) ^ (10 - j.val)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_assoc, inverse_digit_times_fourth χ hχ]
    _ = 0 := by rw [hs, mul_zero, mul_zero]

end ThetaGlobal.GlobalDigitSupport

#print axioms ThetaGlobal.GlobalDigitSupport.ordinary_positive_digit_sum_zero
