import ExpansionDetector.GammaDecay
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-! Explicit exponential terminal-tail estimates. The arbitrary polynomial
order is chosen before the external scale. Only a convergent norm-zeta sum
at exponent two is needed for an ideal-indexed application. -/
noncomputable section
namespace ExpansionDetector.Analytic
open scoped BigOperators Classical

lemma exp_neg_div_le_factorial (q Y : ℝ) (hq : 0 < q) (hY : 0 < Y) (n : ℕ) :
    Real.exp (-q / Y) ≤ (n.factorial : ℝ) * Y ^ n / q ^ n := by
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (q / Y) (div_nonneg hq.le hY.le) n)
  have hprod : (q / Y) ^ n * Real.exp (-(q / Y)) ≤ (n.factorial : ℝ) := by
    calc
      _ ≤ (Real.exp (q / Y) * (n.factorial : ℝ)) * Real.exp (-(q / Y)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
      _ = _ := by rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hprod' : q ^ n * Real.exp (-q / Y) ≤ (n.factorial : ℝ) * Y ^ n := by
    apply (div_le_iff₀ (pow_pos hY n)).mp
    simpa only [div_pow, div_mul_eq_mul_div, neg_div] using hprod
  apply (le_div_iff₀ (pow_pos hq n)).mpr
  simpa only [mul_comm] using hprod'

/-- When q >= H, exponential decay supplies an arbitrary inverse power
of H in addition to the summable q^-2 majorant. -/
theorem q_mul_exp_tail (q Y H : ℝ) (hq : 0 < q) (hY : 0 < Y)
    (hH : 0 < H) (hHq : H ≤ q) (n : ℕ) :
    q * Real.exp (-q / Y) ≤
      ((n + 3).factorial : ℝ) * Y ^ (n + 3) / H ^ n * (q ^ 2)⁻¹ := by
  have he := exp_neg_div_le_factorial q Y hq hY (n + 3)
  have hinv : (q ^ n)⁻¹ ≤ (H ^ n)⁻¹ :=
    inv_le_inv₀ (pow_pos hq n) (pow_pos hH n) |>.mpr
      (pow_le_pow_left₀ hH.le hHq n)
  calc
    _ ≤ q * (((n + 3).factorial : ℝ) * Y ^ (n + 3) / q ^ (n + 3)) :=
      mul_le_mul_of_nonneg_left he hq.le
    _ = ((n + 3).factorial : ℝ) * Y ^ (n + 3) * (q ^ n)⁻¹ * (q ^ 2)⁻¹ := by
      rw [show n + 3 = n + 2 + 1 by omega, pow_add q (n + 2) 1, pow_one,
        pow_add q n 2]
      field_simp
      <;> ring
    _ ≤ ((n + 3).factorial : ℝ) * Y ^ (n + 3) * (H ^ n)⁻¹ * (q ^ 2)⁻¹ := by
      gcongr
    _ = _ := by rw [div_eq_mul_inv]

/-- General countable-index terminal remainder bound. In the ideal
application `N` is the genuine ideal norm and `a` the genuine truncated
Moebius convolution, whose norm bound is proved in IdealCutoff. -/
theorem exponential_terminal_tsum_bound {ι : Type*} [Countable ι]
    (N : ι → ℝ) (a r : ι → ℂ) (s : ℂ) (Y H : ℝ) (n : ℕ)
    (hN : ∀ i, 1 ≤ N i) (ha : ∀ i, ‖a i‖ ≤ N i)
    (hr : ∀ i, ‖r i‖ ≤ 1) (hrzero : ∀ i, N i ≤ H → r i = 0)
    (hs : 0 ≤ s.re) (hY : 0 < Y) (hH : 0 < H)
    (hzeta : Summable (fun i => (N i) ^ (-2 : ℝ))) :
    Summable (fun i => a i * (N i : ℂ) ^ (-s) * (Real.exp (-N i / Y) : ℂ) * r i) ∧
      ‖∑' i, a i * (N i : ℂ) ^ (-s) * (Real.exp (-N i / Y) : ℂ) * r i‖ ≤
        (((n + 3).factorial : ℝ) * Y ^ (n + 3) / H ^ n) *
          ∑' i, (N i) ^ (-2 : ℝ) := by
  let C : ℝ := ((n + 3).factorial : ℝ) * Y ^ (n + 3) / H ^ n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let F : ι → ℂ := fun i =>
    a i * (N i : ℂ) ^ (-s) * (Real.exp (-N i / Y) : ℂ) * r i
  have hb (i : ι) : ‖F i‖ ≤ C * N i ^ (-2 : ℝ) := by
    by_cases hsmall : N i ≤ H
    · simp only [F, hrzero i hsmall, mul_zero, norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans (hN i)) _)
    have hNi : 0 < N i := zero_lt_one.trans_le (hN i)
    have hp : ‖(N i : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNi, Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (hN i) (neg_nonpos.mpr hs)
    calc
      _ = ‖a i‖ * ‖(N i : ℂ) ^ (-s)‖ * Real.exp (-N i / Y) * ‖r i‖ := by
        simp only [F, norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      _ ≤ N i * 1 * Real.exp (-N i / Y) * 1 := by
        apply mul_le_mul _ (hr i) (norm_nonneg _) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul (ha i) hp (norm_nonneg _) hNi.le
      _ = N i * Real.exp (-N i / Y) := by ring
      _ ≤ C * ((N i) ^ 2)⁻¹ := q_mul_exp_tail (N i) Y H hNi hY hH (lt_of_not_ge hsmall).le n
      _ = C * (N i) ^ (-2 : ℝ) := by rw [Real.rpow_neg hNi.le, Real.rpow_two]
  have hsumNorm : Summable (fun i => ‖F i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hzeta.mul_left C)
  refine ⟨hsumNorm.of_norm, ?_⟩
  calc
    ‖∑' i, F i‖ ≤ ∑' i, ‖F i‖ := norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' i, C * N i ^ (-2 : ℝ) := hsumNorm.tsum_le_tsum hb (hzeta.mul_left C)
    _ = C * ∑' i, N i ^ (-2 : ℝ) := tsum_mul_left

end ExpansionDetector.Analytic
