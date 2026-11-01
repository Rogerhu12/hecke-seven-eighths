import ExpansionDetector.ExponentialTail

noncomputable section
namespace ExpansionDetector.Analytic

/-- The exact initial-line absolute majorant also proves summability of the
exponentially smoothed coefficients themselves. -/
theorem exponential_smoothed_series_summable {ι : Type*}
    (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i) (s : ℂ)
    (Y : ℝ) (hY : 0 < Y)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + 2)))) :
    Summable (fun i => c i * (N i : ℂ) ^ (-s) * (Real.exp (-N i / Y) : ℂ)) := by
  have hb (i : ι) :
      ‖c i * (N i : ℂ) ^ (-s) * (Real.exp (-N i / Y) : ℂ)‖ ≤
        (2 * Y ^ 2) * (‖c i‖ * N i ^ (-(s.re + 2))) := by
    have he := exp_neg_div_le_factorial (N i) Y (hN i) hY 2
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.reduceMul, Nat.cast_ofNat] at he
    have hp : N i ^ (-s.re) * ((N i) ^ 2)⁻¹ = N i ^ (-(s.re + 2)) := by
      rw [← Real.rpow_two, ← Real.rpow_neg (hN i).le, ← Real.rpow_add (hN i)]
      congr 1
      ring
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos (hN i), Complex.neg_re]
    calc
      _ ≤ (‖c i‖ * N i ^ (-s.re)) * (2 * Y ^ 2 / (N i) ^ 2) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hN i).le _))
      _ = (2 * Y ^ 2) * (‖c i‖ * (N i ^ (-s.re) * ((N i) ^ 2)⁻¹)) := by
        rw [div_eq_mul_inv]
        ring
      _ = _ := by rw [hp]
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    (hsum.mul_left (2 * Y ^ 2))).of_norm

end ExpansionDetector.Analytic
