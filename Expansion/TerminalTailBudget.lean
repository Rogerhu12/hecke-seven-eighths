import Expansion.DyadicSupport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A uniform numerical budget for the actual terminal Fourier tail

The terminal norm cutoff is `H = U^21`, and the retained Fourier radius is
`U^theta / (8*pi+8)`.  The actual ideal coefficient mass costs at most
`81 CZ^2 U^84`; the two dyadic choices cost at most a fixed multiple of
`U^2`.  Choosing the Fourier moment order before all varying scales with
`theta * N >= 87` therefore leaves one inverse power of `U`.

The cutoff is explicit and is chosen after the Fourier-moment constant.
No detector spike, polynomial upper bound, or asymptotic conclusion is a
hypothesis of this numerical step.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Dyadic

/-- A fixed, positive linear envelope for the number of terminal dyadic
scales. Its dependence is entirely numerical. -/
def terminalDyadicCountConstant : ℝ :=
  21 / Real.log 2 + Real.log 3 / Real.log 2 + 2

theorem terminalDyadicCountConstant_pos : 0 < terminalDyadicCountConstant := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hthree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold terminalDyadicCountConstant
  positivity

/-- The literal ceiling-defined count has a uniform linear envelope. The
stronger logarithmic bound is `dyadicCap_terminal_le`. -/
theorem terminal_dyadic_count_le {U : ℝ} (hU : 1 ≤ U) :
    ((dyadicCap (3 * U ^ (21 : ℕ)) + 1 : ℕ) : ℝ) ≤
      terminalDyadicCountConstant * U := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogthree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hcap := dyadicCap_terminal_le hU
  rw [Real.rpow_ofNat] at hcap
  have hlog := Real.log_le_self (zero_le_one.trans hU)
  have hfirst := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 21 / Real.log 2 by positivity)
  have hlast := mul_le_mul_of_nonneg_left hU
    (show 0 ≤ Real.log 3 / Real.log 2 + 2 by positivity)
  push_cast
  unfold terminalDyadicCountConstant
  nlinarith

/-- Every terminal dyadic scale is at most 6H. Consequently its complete
smooth annular support lies below 12H; an ambient ideal set with that norm
cap contains the full polynomial required by Mellin inversion. -/
theorem two_pow_terminal_dyadicCap_le {H : ℝ} (hH : 1 ≤ H) :
    (2 : ℝ) ^ dyadicCap (3 * H) ≤ 6 * H := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquot : 0 ≤ Real.log (3 * H) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
  have hceil := (Nat.ceil_lt_add_one hquot).le
  have hmul := mul_le_mul_of_nonneg_right hceil hlog2.le
  have hcancel : (Real.log (3 * H) / Real.log 2 + 1) * Real.log 2 =
      Real.log (3 * H) + Real.log 2 := by field_simp [hlog2.ne']
  rw [hcancel] at hmul
  have hlog : Real.log (3 * H) + Real.log 2 = Real.log (6 * H) := by
    rw [← Real.log_mul (by positivity : (3 * H : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [hlog] at hmul
  exact (Real.pow_le_iff_le_log (by norm_num : (0 : ℝ) < 2) (by positivity)).mpr hmul

/-- The coefficient of the final inverse-power tail. -/
def terminalFourierTailConstant (CZ Corder : ℝ) (N : ℕ) : ℝ :=
  terminalDyadicCountConstant ^ 2 * 81 * CZ ^ 2 *
    (8 * Real.pi + 8) ^ N * Corder

theorem terminalFourierTailConstant_nonneg (CZ Corder : ℝ) (N : ℕ)
    (hCorder : 0 ≤ Corder) : 0 ≤ terminalFourierTailConstant CZ Corder N := by
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold terminalFourierTailConstant
  positivity

/-- An order may be chosen immediately after the positive height exponent,
before the Fourier-moment constant or any arithmetic data are known. -/
theorem exists_terminal_fourier_order (θ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ, (87 : ℝ) ≤ θ * N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (87 / θ)
  refine ⟨N, ?_⟩
  simpa only [mul_comm] using (div_le_iff₀ hθ).mp hN

/-- The complete scalar tail, including both dyadic counts, has one spare
inverse power. The denominator is the actual buffered Fourier radius. -/
theorem terminal_fourier_tail_le_inverse_power
    {U θ CZ Corder : ℝ} {N : ℕ} (hU : 1 ≤ U)
    (hCorder : 0 ≤ Corder) (horder : (87 : ℝ) ≤ θ * N) :
    (((dyadicCap (3 * U ^ (21 : ℕ)) + 1 : ℕ) : ℝ) ^ 2) *
      ((((3 * U ^ (21 : ℕ)) ^ 2 * CZ) ^ 2) /
        (U ^ θ / (8 * Real.pi + 8)) ^ N * Corder) ≤
      terminalFourierTailConstant CZ Corder N * U ^ (-1 : ℝ) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hpi : 0 < Real.pi := Real.pi_pos
  have hbase : 0 < 8 * Real.pi + 8 := by positivity
  have hcount := terminal_dyadic_count_le hU
  have hcountsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
  have hnonneg : 0 ≤
      (((3 * U ^ (21 : ℕ)) ^ 2 * CZ) ^ 2) /
        (U ^ θ / (8 * Real.pi + 8)) ^ N * Corder := by positivity
  apply (mul_le_mul_of_nonneg_right hcountsq hnonneg).trans
  have hpow : (U ^ θ) ^ N = U ^ (θ * N) :=
    (Real.rpow_mul_natCast hUpos.le θ N).symm
  have halgebra :
      (terminalDyadicCountConstant * U) ^ 2 *
        ((((3 * U ^ (21 : ℕ)) ^ 2 * CZ) ^ 2) /
          (U ^ θ / (8 * Real.pi + 8)) ^ N * Corder) =
      terminalFourierTailConstant CZ Corder N * U ^ (86 - θ * N) := by
    rw [div_pow, hpow, div_div_eq_mul_div]
    rw [Real.rpow_sub hUpos]
    rw [Real.rpow_ofNat]
    unfold terminalFourierTailConstant
    ring
  rw [halgebra]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU (by linarith))
    (terminalFourierTailConstant_nonneg CZ Corder N hCorder)

/-- Explicit eventual Fourier-tail absorption. The quantifier order is:
positive height exponent, Fourier order, the two fixed mass constants,
then one cutoff valid for every later scale. -/
theorem exists_terminal_fourier_tail_budget (θ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ, (87 : ℝ) ≤ θ * N ∧
      ∀ CZ Corder : ℝ, 0 ≤ Corder →
      ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        (((dyadicCap (3 * U ^ (21 : ℕ)) + 1 : ℕ) : ℝ) ^ 2) *
          ((((3 * U ^ (21 : ℕ)) ^ 2 * CZ) ^ 2) /
            (U ^ θ / (8 * Real.pi + 8)) ^ N * Corder) ≤ (1 / 8 : ℝ) := by
  obtain ⟨N, hN⟩ := exists_terminal_fourier_order θ hθ
  refine ⟨N, hN, ?_⟩
  intro CZ Corder hCorder
  let C := terminalFourierTailConstant CZ Corder N
  refine ⟨max 2 (8 * C), le_max_left _ _, ?_⟩
  intro U hU
  have hUtwo : 2 ≤ U := (le_max_left _ _).trans hU
  have hUone : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have hlarge : 8 * C ≤ U := (le_max_right _ _).trans hU
  apply (terminal_fourier_tail_le_inverse_power hUone hCorder hN).trans
  change C * U ^ (-1 : ℝ) ≤ 1 / 8
  rw [Real.rpow_neg_one, ← div_eq_mul_inv]
  exact (div_le_iff₀ hUpos).mpr (by linarith)

/-- The same order works after enlarging the ambient ideal norm cutoff.
Only the final constant and threshold change; the dyadic source count and
the power 87 are retained. `scale=18` accommodates the complete support
window used by the repaired actual terminal extraction. -/
theorem exists_terminal_fourier_tail_budget_scaled (θ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ, (87 : ℝ) ≤ θ * N ∧
      ∀ scale CZ Corder : ℝ, 0 ≤ Corder →
      ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        (((dyadicCap (3 * U ^ (21 : ℕ)) + 1 : ℕ) : ℝ) ^ 2) *
          ((((scale * U ^ (21 : ℕ)) ^ 2 * CZ) ^ 2) /
            (U ^ θ / (8 * Real.pi + 8)) ^ N * Corder) ≤ (1 / 8 : ℝ) := by
  obtain ⟨N, hN, hbudget⟩ := exists_terminal_fourier_tail_budget θ hθ
  refine ⟨N, hN, ?_⟩
  intro scale CZ Corder hCorder
  obtain ⟨U₀, hU₀, htail⟩ := hbudget CZ ((scale / 3) ^ 4 * Corder) (by positivity)
  refine ⟨U₀, hU₀, ?_⟩
  intro U hU
  convert htail U hU using 1 <;> ring

end Expansion.Dyadic
