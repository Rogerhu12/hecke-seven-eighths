import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniformity estimates for prime-slot cancellation

These elementary real inequalities handle logarithmic losses, the capacity
constraint, and a choice of contour buffer.  The height exponent is fixed at
one before the positive height parameter is chosen; the multiplicative
constant may depend on that parameter.

This file does not assume or prove a prime-sum estimate, a zero-free region,
or the project-specific `paired_primes_below_one` theorem.
-/

namespace PrimeCancellationUniformity

/-- An explicit constant absorbing a fixed logarithmic power. -/
noncomputable def logAbsorptionConstant (N : ℕ) (τ : ℝ) : ℝ :=
  (N.factorial : ℝ) * Real.exp τ / τ ^ N

theorem logAbsorptionConstant_pos (N : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    0 < logAbsorptionConstant N τ := by
  have hfact : 0 < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  exact div_pos (mul_pos hfact (Real.exp_pos τ)) (pow_pos hτ N)

/-- The N-th term of the exponential series gives a uniform bound for every
`V ≥ 1`, with an explicit constant. -/
theorem one_add_log_pow_le_rpow (N : ℕ) {τ V : ℝ}
    (hτ : 0 < τ) (hV : 1 ≤ V) :
    (1 + Real.log V) ^ N ≤ logAbsorptionConstant N τ * V ^ τ := by
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hlog : 0 ≤ 1 + Real.log V := add_nonneg zero_le_one (Real.log_nonneg hV)
  have hfact : 0 < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hterm := Real.pow_div_factorial_le_exp (τ * (1 + Real.log V))
    (mul_nonneg hτ.le hlog) N
  have hterm' :
      (τ * (1 + Real.log V)) ^ N ≤
        Real.exp (τ * (1 + Real.log V)) * (N.factorial : ℝ) :=
    (div_le_iff₀ hfact).mp hterm
  rw [mul_pow] at hterm'
  have hdiv :
      (1 + Real.log V) ^ N ≤
        (Real.exp (τ * (1 + Real.log V)) * (N.factorial : ℝ)) / τ ^ N := by
    apply (le_div_iff₀ (pow_pos hτ N)).mpr
    simpa only [mul_comm] using hterm'
  have hexp : Real.exp (τ * (1 + Real.log V)) = Real.exp τ * V ^ τ := by
    rw [Real.rpow_def_of_pos hVpos]
    rw [show τ * (1 + Real.log V) = τ + Real.log V * τ by ring, Real.exp_add]
  calc
    (1 + Real.log V) ^ N ≤
        (Real.exp (τ * (1 + Real.log V)) * (N.factorial : ℝ)) / τ ^ N := hdiv
    _ = logAbsorptionConstant N τ * V ^ τ := by
      rw [hexp]
      unfold logAbsorptionConstant
      ring

/-- A convenient version matching a height factor `1 + V ^ τ`. -/
theorem one_add_log_pow_le_height (N : ℕ) {τ V : ℝ}
    (hτ : 0 < τ) (hV : 1 ≤ V) :
    (1 + Real.log V) ^ N ≤ logAbsorptionConstant N τ * (1 + V ^ τ) := by
  refine (one_add_log_pow_le_rpow N hτ hV).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith : V ^ τ ≤ 1 + V ^ τ)
    (logAbsorptionConstant_pos N hτ).le

/-- The constant is chosen after the positive height parameter, as permitted
by `UniformMomentBound`. -/
theorem exists_log_absorption_constant (N : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : ℝ, 1 ≤ V →
      (1 + Real.log V) ^ N ≤ C * (1 + V ^ τ) := by
  refine ⟨logAbsorptionConstant N τ, (logAbsorptionConstant_pos N hτ).le, ?_⟩
  intro V hV
  exact one_add_log_pow_le_height N hτ hV

/-- A single height exponent, namely one, works for every finite logarithmic
power and every positive height parameter. -/
theorem logarithmic_losses_admit_fixed_height_exponent :
    ∃ A : ℝ, A = 1 ∧ 0 ≤ A ∧
      ∀ (N : ℕ) (τ : ℝ), 0 < τ →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ V : ℝ, 1 ≤ V →
          (1 + Real.log V) ^ N ≤ C * (1 + V ^ τ) ^ A := by
  refine ⟨1, rfl, zero_le_one, ?_⟩
  intro N τ hτ
  obtain ⟨C, hC, hbound⟩ := exists_log_absorption_constant N τ hτ
  refine ⟨C, hC, ?_⟩
  intro V hV
  simpa only [Real.rpow_one] using hbound V hV

/-- In the parameter range `κ ≥ 3/4`, the capacity constraint gives a uniform
upper bound for the total selected length. -/
theorem selected_length_le_two_ninths {plain z κ : ℝ}
    (hplain : 0 ≤ plain) (hz : 0 ≤ z) (hκ : (3 : ℝ) / 4 ≤ κ)
    (hcapacity : 2 * plain + 6 * κ * z ≤ 1) :
    z ≤ (2 : ℝ) / 9 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hκ) hz]

/-- A positive contour buffer with a fixed upper bound and a prescribed
total exponent loss. -/
noncomputable def contourBuffer (lam L : ℝ) : ℝ :=
  min (1 / 4) (lam / (2 * max 1 L))

theorem contourBuffer_pos {lam L : ℝ} (hlam : 0 < lam) :
    0 < contourBuffer lam L := by
  have hmax : 0 < max (1 : ℝ) L := lt_of_lt_of_le zero_lt_one (le_max_left 1 L)
  unfold contourBuffer
  exact lt_min (by norm_num) (div_pos hlam (mul_pos (by norm_num) hmax))

theorem contourBuffer_le_quarter (lam L : ℝ) :
    contourBuffer lam L ≤ (1 : ℝ) / 4 :=
  min_le_left _ _

/-- Only an upper bound on total length is needed.  In particular, no
positive lower bound for an individual slot length is used here. -/
theorem contourBuffer_total_loss {lam L z : ℝ} (hlam : 0 < lam) (hzL : z ≤ L) :
    2 * contourBuffer lam L * z ≤ lam := by
  have hmax : 0 < max (1 : ℝ) L := lt_of_lt_of_le zero_lt_one (le_max_left 1 L)
  have hden : 0 < 2 * max (1 : ℝ) L := mul_pos (by norm_num) hmax
  have hbuffer : contourBuffer lam L ≤ lam / (2 * max (1 : ℝ) L) := min_le_right _ _
  have hmul : contourBuffer lam L * (2 * max (1 : ℝ) L) ≤ lam :=
    (le_div_iff₀ hden).mp hbuffer
  have hzmax : z ≤ max (1 : ℝ) L := hzL.trans (le_max_right 1 L)
  calc
    2 * contourBuffer lam L * z ≤ 2 * contourBuffer lam L * max (1 : ℝ) L :=
      mul_le_mul_of_nonneg_left hzmax
        (mul_nonneg (by norm_num) (contourBuffer_pos hlam).le)
    _ ≤ lam := by nlinarith [hmul]

#print axioms logAbsorptionConstant_pos
#print axioms one_add_log_pow_le_rpow
#print axioms one_add_log_pow_le_height
#print axioms exists_log_absorption_constant
#print axioms logarithmic_losses_admit_fixed_height_exponent
#print axioms selected_length_le_two_ninths
#print axioms contourBuffer_pos
#print axioms contourBuffer_le_quarter
#print axioms contourBuffer_total_loss

end PrimeCancellationUniformity
