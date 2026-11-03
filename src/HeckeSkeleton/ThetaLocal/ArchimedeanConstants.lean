import HeckeSkeleton.ThetaLocal.ArchimedeanMellin

/-!
# Normalizations for the single-complex-place Mellin pair

This file records the nonvanishing and absolute values of all fixed factors.
The normalized reflected profile is obtained from the genuine Bessel profile
by a constant of absolute value one.  It is not defined by its Mellin transform.
-/

noncomputable section

namespace HeckeSkeleton.ThetaLocal

open Complex

theorem archWeight_neg (m : ℤ) : archWeight (-m) = archWeight m := by
  simp [archWeight]

theorem archReflectedConstant_ne_zero (c : ℝ) (hc : 0 < c) (m : ℤ) (τ : ℝ) :
    archReflectedConstant c m τ ≠ 0 :=
  archDirectConstant_ne_zero c hc m (-τ)

theorem archDirectConstant_norm (c : ℝ) (hc : 0 < c) (m : ℤ) (τ : ℝ) :
    ‖archDirectConstant c m τ‖ =
      (1 / 2 : ℝ) * (archScale c) ^ archWeight m := by
  unfold archDirectConstant
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (archScale_pos c hc),
    archExponent_re]
  norm_num

theorem archReflectedConstant_norm (c : ℝ) (hc : 0 < c) (m : ℤ) (τ : ℝ) :
    ‖archReflectedConstant c m τ‖ =
      (1 / 2 : ℝ) * (archScale c) ^ archWeight m :=
  archDirectConstant_norm c hc m (-τ)

/-- The same open strip works for every angular weight, including zero. -/
theorem arch_reflected_mellin_common_strip (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ : ℝ) (s : ℂ)
    (hleft : -(1 / 3 : ℝ) < s.re) (hright : s.re < (1 / 3 : ℝ)) :
    mellin (archReflectedProfile c m τ) s =
      mellin (archDirectProfile c m τ) (-s) *
        (archScale c : ℂ) ^ (2 * s) * archReflectionPhase c τ *
        (archGammaPair (archExponent m (-τ) + s) /
          archGammaPair (archExponent m τ + (-s))) := by
  have hm := archWeight_ge_half m
  exact arch_reflected_mellin c hc m τ s (by linarith) (by linarith)

#print axioms archDirectConstant_norm
#print axioms archReflectedConstant_ne_zero
#print axioms arch_reflected_mellin_common_strip

end HeckeSkeleton.ThetaLocal
