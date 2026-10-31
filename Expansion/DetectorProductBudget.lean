import Expansion.TerminalTailBudget
import ExpansionDetector.MellinPowerBudget

/-!
# From the actual finite-source inequality to a power spike

The literal terminal dyadic count is logarithmic. This file absorbs its
square and the fixed positive Fourier mass into an arbitrarily small
power, uniformly before any row or dyadic pair is selected. It also
records the exact logarithmic lengths of the dyadic scales.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Dyadic

open ExpansionDetector.PowerBudget

theorem terminal_dyadic_count_subpower {U η : ℝ} (hU : 1 ≤ U) (hη : 0 < η) :
    ((dyadicCap (3 * U ^ (21 : ℕ)) + 1 : ℕ) : ℝ) ≤
      ((21 / Real.log 2) / η + Real.log 3 / Real.log 2 + 2) * U ^ η := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogthree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hcap := dyadicCap_terminal_le hU
  rw [Real.rpow_ofNat] at hcap
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hU) hη
  have hp : 1 ≤ U ^ η := Real.one_le_rpow hU hη.le
  have hfirst := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 21 / Real.log 2 by positivity)
  have hlast := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ Real.log 3 / Real.log 2 + 2 by positivity)
  push_cast
  nlinarith

/-- One cutoff absorbs the complete two-scale count and fixed Fourier
mass. The exponent may be arbitrarily small and positive. -/
theorem exists_terminal_count_mass_absorbed (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      8 * C * (((dyadicCap (3 * U ^ (21 : ℕ)) + 1 : ℕ) : ℝ) ^ 2) ≤ U ^ (η / 2) := by
  let A := (21 / Real.log 2) / (η / 8) + Real.log 3 / Real.log 2 + 2
  have hA : 0 ≤ A := by
    have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hthree : 0 < Real.log 3 := Real.log_pos (by norm_num)
    unfold A
    positivity
  obtain ⟨U₀, hU₀, habsorb⟩ := exists_const_mul_rpow_absorbed
    (8 * C * A ^ 2) (η / 4) (by positivity) (by positivity)
  refine ⟨U₀, hU₀, ?_⟩
  intro U hU
  have hUone : 1 ≤ U := by linarith [hU₀.trans hU]
  have hUpos : 0 < U := zero_lt_one.trans_le hUone
  have hcount := terminal_dyadic_count_subpower hUone (show 0 < η / 8 by positivity)
  have hcountsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
  have hp : (U ^ (η / 8)) ^ 2 = U ^ (η / 4) := by
    rw [← Real.rpow_mul_natCast hUpos.le]
    congr 1
    norm_num
    ring
  calc
    _ ≤ 8 * C * (A * U ^ (η / 8)) ^ 2 :=
      mul_le_mul_of_nonneg_left hcountsq (by positivity)
    _ = (8 * C * A ^ 2) * U ^ (η / 4) := by rw [mul_pow, hp]; ring
    _ ≤ U ^ (η / 4 + η / 4) := habsorb U hU (η / 4)
    _ = _ := by congr 1; ring

/-- The bounded-frequency product selected from the terminal source is a
genuine power spike. The only input about its value is the source inequality
already proved by `actual_terminal_product_eventually`; no spike is assumed.
The same cutoff works for every later real part and every dyadic length. -/
theorem exists_terminal_product_power_spike (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ r m a β p : ℝ, 0 ≤ r → 0 ≤ m → a ≤ β → 0 ≤ p →
      (1 / 8 : ℝ) ≤
        (((dyadicCap (3 * U ^ (21 : ℕ)) + 1 : ℕ) : ℝ) ^ 2) * C *
          (U ^ r) ^ (1 / 2 - β) * (U ^ m) ^ (1 / 2 - β) * p →
      U ^ ((2 * a - 1) * (r + m) - η) ≤ p ^ 2 := by
  obtain ⟨U₀, hU₀, hcount⟩ := exists_terminal_count_mass_absorbed C η hC hη
  refine ⟨U₀, hU₀, ?_⟩
  intro U hU r m a β p hr hm ha hp hsource
  have hUone : 1 ≤ U := by linarith [hU₀.trans hU]
  have hUpos : 0 < U := zero_lt_one.trans_le hUone
  let c : ℝ := (((dyadicCap (3 * U ^ (21 : ℕ)) + 1 : ℕ) : ℝ) ^ 2)
  have hsource' : (1 : ℝ) ≤
      (8 * C * c) * ((U ^ r) ^ (1 / 2 - β) * (U ^ m) ^ (1 / 2 - β) * p) := by
    dsimp only [c]
    nlinarith
  have hlarge := hsource'.trans (mul_le_mul_of_nonneg_right (hcount U hU)
    (show 0 ≤ (U ^ r) ^ (1 / 2 - β) * (U ^ m) ^ (1 / 2 - β) * p by positivity))
  have hpowers : U ^ (η / 2) *
      ((U ^ r) ^ (1 / 2 - β) * (U ^ m) ^ (1 / 2 - β) * p) =
      U ^ (η / 2 + (1 / 2 - β) * (r + m)) * p := by
    rw [← Real.rpow_mul hUpos.le, ← Real.rpow_mul hUpos.le]
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hUpos, ← Real.rpow_add hUpos]
    congr 2
    ring
  rw [hpowers] at hlarge
  have hlower : U ^ ((β - 1 / 2) * (r + m) - η / 2) ≤ p := by
    apply (mul_le_mul_iff_right₀
      (Real.rpow_pos_of_pos hUpos (η / 2 + (1 / 2 - β) * (r + m)))).mp
    calc
      _ = 1 := by
        rw [← Real.rpow_add hUpos]
        convert Real.rpow_zero U using 1 <;> ring
      _ ≤ p * U ^ (η / 2 + (1 / 2 - β) * (r + m)) := by
        simpa only [mul_comm] using hlarge
  have hsquare := pow_le_pow_left₀
    (Real.rpow_nonneg hUpos.le ((β - 1 / 2) * (r + m) - η / 2)) hlower 2
  have hsqpower : (U ^ ((β - 1 / 2) * (r + m) - η / 2)) ^ 2 =
      U ^ ((2 * β - 1) * (r + m) - η) := by
    rw [← Real.rpow_mul_natCast hUpos.le]
    congr 1
    norm_num
    ring
  rw [hsqpower] at hsquare
  have hab := mul_le_mul_of_nonneg_right ha (show 0 ≤ r + m by linarith)
  exact (Real.rpow_le_rpow_of_exponent_le hUone (by nlinarith)).trans hsquare

/-- The exact real length of one integer-indexed dyadic scale. -/
def dyadicLength (U : ℝ) (j : ℕ) : ℝ := Real.log ((2 : ℝ) ^ j) / Real.log U

theorem dyadicLength_nonneg {U : ℝ} (hU : 1 < U) (j : ℕ) :
    0 ≤ dyadicLength U j := by
  exact div_nonneg (Real.log_nonneg (one_le_pow₀ (by norm_num))) (Real.log_pos hU).le

theorem rpow_dyadicLength {U : ℝ} (hU : 1 < U) (j : ℕ) :
    U ^ dyadicLength U j = (2 : ℝ) ^ j := by
  have hUpos : 0 < U := zero_lt_one.trans hU
  have hlog : Real.log U ≠ 0 := (Real.log_pos hU).ne'
  rw [Real.rpow_def_of_pos hUpos]
  unfold dyadicLength
  rw [mul_div_cancel₀ _ hlog]
  exact Real.exp_log (by positivity)

/-- At U >= 6, every terminal dyadic scale has length at most 22.
This is the same range used by the uniform actual contour budget. -/
theorem terminal_dyadicLength_le {U : ℝ} (hU : 6 ≤ U) {j : ℕ}
    (hj : j ≤ dyadicCap (3 * U ^ (21 : ℕ))) : dyadicLength U j ≤ 22 := by
  have hUone : 1 < U := by linarith
  have hUpos : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos hUone
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 + Real.log 2 ≤ Real.log U := by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num only [show (3 * 2 : ℝ) = 6 by norm_num]
    exact Real.log_le_log (by norm_num) hU
  have hcap := dyadicCap_terminal_le hUone.le
  rw [Real.rpow_ofNat] at hcap
  have hj' : (j : ℝ) ≤ (dyadicCap (3 * U ^ (21 : ℕ)) : ℝ) := by exact_mod_cast hj
  have hlen : (j : ℝ) * Real.log 2 ≤ 22 * Real.log U := by
    have hh := mul_le_mul_of_nonneg_right (hj'.trans hcap) hlog2.le
    have heq : ((21 / Real.log 2) * Real.log U +
        (Real.log 3 / Real.log 2 + 1)) * Real.log 2 =
          21 * Real.log U + Real.log 3 + Real.log 2 := by field_simp [hlog2.ne']; ring
    rw [heq] at hh
    linarith
  unfold dyadicLength
  rw [Real.log_pow]
  exact (div_le_iff₀ hlogU).mpr hlen

end Expansion.Dyadic
