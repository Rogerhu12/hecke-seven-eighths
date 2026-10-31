import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial bounds between two exponential weights

The constants in these elementary estimates precede the point and the
function value.  The actual orbital construction uses them with two
positive Mellin weights on either side of a fixed small tilt.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep.ExponentialTilt

/-- A polynomial is bounded by a fixed exponential, with an explicit
constant depending only on its degree and the positive decay rate. -/
theorem pow_mul_exp_neg_le (k : ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-a * x) ≤ (k.factorial : ℝ) / a ^ k := by
  have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (a * x) (mul_nonneg ha.le hx) k)
  apply (le_div_iff₀ (pow_pos ha k)).mpr
  calc
    (x ^ k * Real.exp (-a * x)) * a ^ k =
        (a * x) ^ k * Real.exp (-(a * x)) := by
      rw [mul_pow, show -a * x = -(a * x) by ring]
      ring
    _ ≤ (Real.exp (a * x) * (k.factorial : ℝ)) * Real.exp (-(a * x)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (k.factorial : ℝ) *
        (Real.exp (a * x) * Real.exp (-(a * x))) := by ring
    _ = (k.factorial : ℝ) := by rw [← Real.exp_add]; simp

/-- Two exponential weights surrounding the tilt dominate every
polynomial weight, on the complete real axis. -/
theorem polynomial_weight_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) {a δ B : ℝ} (ha : 0 < a) (t : ℝ) (v : F)
    (hminus : Real.exp ((δ - a) * t) * ‖v‖ ≤ B)
    (hplus : Real.exp ((δ + a) * t) * ‖v‖ ≤ B) :
    ‖t‖ ^ k * ‖Real.exp (δ * t) • v‖ ≤
      ((k.factorial : ℝ) / a ^ k) * B := by
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hconstant : 0 ≤ (k.factorial : ℝ) / a ^ k := by positivity
  by_cases ht : 0 ≤ t
  · rw [Real.norm_of_nonneg ht]
    have he : Real.exp (δ * t) =
        Real.exp (-a * t) * Real.exp ((δ + a) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    calc
      t ^ k * (Real.exp (-a * t) * Real.exp ((δ + a) * t) * ‖v‖) =
          (t ^ k * Real.exp (-a * t)) *
            (Real.exp ((δ + a) * t) * ‖v‖) := by ring
      _ ≤ ((k.factorial : ℝ) / a ^ k) * B :=
        mul_le_mul (pow_mul_exp_neg_le k ha ht) hplus
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hconstant
  · have ht' : t ≤ 0 := (not_le.mp ht).le
    rw [Real.norm_of_nonpos ht']
    have he : Real.exp (δ * t) =
        Real.exp (-a * (-t)) * Real.exp ((δ - a) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    calc
      (-t) ^ k * (Real.exp (-a * (-t)) * Real.exp ((δ - a) * t) * ‖v‖) =
          ((-t) ^ k * Real.exp (-a * (-t))) *
            (Real.exp ((δ - a) * t) * ‖v‖) := by ring
      _ ≤ ((k.factorial : ℝ) / a ^ k) * B :=
        mul_le_mul (pow_mul_exp_neg_le k ha (neg_nonneg.mpr ht')) hminus
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hconstant

end HeckeSkeleton.Moments.EngineStep.ExponentialTilt

#print axioms HeckeSkeleton.Moments.EngineStep.ExponentialTilt.polynomial_weight_le
