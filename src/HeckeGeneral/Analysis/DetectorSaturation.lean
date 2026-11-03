import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite numerical consumption of Q 4498--4547: a product spike and the
pointwise bounds force individual saturation and short plain length.
M and S may be values of the ACTUAL zero-extended polynomials. No nonzero
coefficient is substituted for a ramified zero, and neither witness
existence nor source-profile admissibility is asserted by this module.
-/

noncomputable section
namespace HeckeGeneral.Analysis

private theorem rpow_lower_of_product_upper {U a b x y : ℝ}
    (hU : 0 < U) (ha : 0 ≤ a) (hprod : U ^ x ≤ a * b) (hb : b ≤ U ^ y) :
    U ^ (x - y) ≤ a := by
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU y)).mp
  calc
    U ^ (x - y) * U ^ y = U ^ x := by
      rw [← Real.rpow_add hU]
      congr 1
      ring
    _ ≤ a * b := hprod
    _ ≤ a * U ^ y := mul_le_mul_of_nonneg_left hb ha

/-- The individual lower bounds use the same actual values as the product
spike. No division by M or S and no nonzero assumption on them is needed. -/
theorem detector_individual_saturation {U δ r m ε : ℝ} {M S : ℂ}
    (hU : 1 < U) (hδ : 0 ≤ δ)
    (hspike : U ^ (δ * (r + m) - ε) ≤ ‖M * S‖ ^ 2)
    (hM : ‖M‖ ^ 2 ≤ U ^ (δ * r + ε))
    (hS : ‖S‖ ^ 2 ≤ U ^ (δ * min m (1 - m) + ε)) :
    U ^ (δ * r - 2 * ε) ≤ ‖M‖ ^ 2 ∧
      U ^ (δ * m - 2 * ε) ≤ ‖S‖ ^ 2 := by
  have hUpos : 0 < U := lt_trans zero_lt_one hU
  have hp : U ^ (δ * (r + m) - ε) ≤ ‖M‖ ^ 2 * ‖S‖ ^ 2 := by
    simpa only [norm_mul, mul_pow] using hspike
  have hSweak : ‖S‖ ^ 2 ≤ U ^ (δ * m + ε) :=
    hS.trans (Real.rpow_le_rpow_of_exponent_le hU.le (by
      have hmul := mul_le_mul_of_nonneg_left (min_le_left m (1 - m)) hδ
      linarith))
  have hMl := rpow_lower_of_product_upper hUpos (sq_nonneg ‖M‖) hp hSweak
  have hSl := rpow_lower_of_product_upper hUpos (sq_nonneg ‖S‖)
    (by simpa only [mul_comm] using hp) hM
  constructor
  · convert hMl using 1
    congr 1
    ring
  · convert hSl using 1
    congr 1
    ring

/-- Delta >= 1/50 converts the exponent loss 3*epsilon into the explicit
length loss 75*epsilon. The min upper bound is used before any count. -/
theorem detector_plain_length_le {U δ r m ε : ℝ} {M S : ℂ}
    (hU : 1 < U) (hδ : 1 / 50 ≤ δ) (hε : 0 ≤ ε)
    (hspike : U ^ (δ * (r + m) - ε) ≤ ‖M * S‖ ^ 2)
    (hM : ‖M‖ ^ 2 ≤ U ^ (δ * r + ε))
    (hS : ‖S‖ ^ 2 ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε := by
  have hUpos : 0 < U := lt_trans zero_lt_one hU
  have hp : U ^ (δ * (r + m) - ε) ≤ ‖M‖ ^ 2 * ‖S‖ ^ 2 := by
    simpa only [norm_mul, mul_pow] using hspike
  have hpow : U ^ (δ * (r + m) - ε) ≤
      U ^ ((δ * r + ε) + (δ * min m (1 - m) + ε)) := by
    rw [Real.rpow_add hUpos]
    exact hp.trans (mul_le_mul hM hS (sq_nonneg ‖S‖)
      (Real.rpow_nonneg hUpos.le _))
  have hexp := (Real.rpow_le_rpow_left_iff hU).mp hpow
  by_cases hm : m ≤ 1 / 2
  · linarith
  · have hmin : min m (1 - m) = 1 - m := min_eq_right (by linarith)
    rw [hmin] at hexp
    have hcost : (1 / 50 : ℝ) * (2 * m - 1) ≤ δ * (2 * m - 1) :=
      mul_le_mul_of_nonneg_right hδ (by linarith)
    nlinarith

/-- The simultaneous conclusion used AFTER actual detector construction. -/
theorem detector_saturation_with_length {U δ r m ε t η : ℝ} {M S : ℂ}
    (hU : 1 < U) (hδ : 1 / 50 ≤ δ) (hε : 0 ≤ ε)
    (hspike : U ^ (δ * (r + m) - ε) ≤ ‖M * S‖ ^ 2)
    (hM : ‖M‖ ^ 2 ≤ U ^ (δ * r + ε))
    (hS : ‖S‖ ^ 2 ≤ U ^ (δ * min m (1 - m) + ε))
    (hlength : t - η ≤ r + m) :
    U ^ (δ * r - 2 * ε) ≤ ‖M‖ ^ 2 ∧
      U ^ (δ * m - 2 * ε) ≤ ‖S‖ ^ 2 ∧
      m ≤ 1 / 2 + 75 * ε ∧ r ≥ t - 1 / 2 - 75 * ε - η := by
  obtain ⟨hMl, hSl⟩ := detector_individual_saturation hU (by linarith) hspike hM hS
  have hm := detector_plain_length_le hU hδ hε hspike hM hS
  exact ⟨hMl, hSl, hm, by linarith⟩

end HeckeGeneral.Analysis
